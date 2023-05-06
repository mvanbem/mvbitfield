use proc_macro2::Span;
use syn::{Error, Result};

use crate::ast::Field;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackDir {
    LsbFirst,
    MsbFirst,
}

struct SizedField {
    field: Field,
    width: usize,
}

pub struct PackedField {
    pub field: Field,
    pub offset: usize,
    pub width: usize,
    pub width_span: Span,
}

pub fn pack<I: Iterator<Item = Field> + ExactSizeIterator>(
    pack_dir: Option<PackDir>,
    struct_error_span: Span,
    struct_width: usize,
    fields: impl IntoIterator<IntoIter = I>,
) -> Result<Vec<PackedField>> {
    let fields = fields.into_iter();
    let pack_dir = match pack_dir {
        Some(pack_dir) => pack_dir,
        None if fields.len() < 2 => {
            // Doesn't matter, just pick one.
            PackDir::LsbFirst
        }
        None => {
            return Err(Error::new(
                struct_error_span,
                "a packing direction attribute is required (`#[lsb_first]` or `#[msb_first]`)",
            ))
        }
    };

    let mut fields_before_flexible = Vec::new();
    let mut flexible_field = None;
    let mut fields_after_flexible = Vec::new();

    // Initial pass: Collect placeholders into each list of fields in the order
    // they will be packed. Verify there are zero or one flexible fields.
    for field in fields {
        match field.width()? {
            Some(width) => {
                let dst = if flexible_field.is_none() {
                    &mut fields_before_flexible
                } else {
                    &mut fields_after_flexible
                };
                dst.push(SizedField {
                    field,
                    width: width as usize,
                });
            }
            None => {
                if flexible_field.is_some() {
                    return Err(Error::new(
                        field.name_span(),
                        "only up to one flexible field is permitted",
                    ));
                } else {
                    flexible_field = Some(field);
                }
            }
        }
    }

    // Compute available bits after considering all sized fields.
    let mut available = struct_width;
    for &SizedField { ref field, width } in fields_before_flexible
        .iter()
        .chain(fields_after_flexible.iter())
    {
        if let Some(new_available) = available.checked_sub(width) {
            available = new_available;
        } else {
            return Err(Error::new(
                field.name_span(),
                format!("field overflows containing struct; {available} bit(s) available"),
            ));
        }
    }

    // Size the flexible field, if present.
    let flexible_field = match flexible_field {
        Some(field) if available > 0 => Some(SizedField {
            field,
            width: available,
        }),
        Some(field) => {
            return Err(Error::new(
                field.name_span(),
                format!("no bits available for flexible field"),
            ))
        }
        None if available == 0 => None,
        None => {
            return Err(Error::new(
                struct_error_span,
                format!(
                    "there are {available} unassigned bit(s); consider specifying an anonymous \
                        flexible field `..` if this is intended",
                ),
            ))
        }
    };

    // The fields are known to fit and are all sized. Pack them.
    let mut lsb_offset = match pack_dir {
        PackDir::LsbFirst => 0,
        PackDir::MsbFirst => struct_width,
    };
    let mut packed = Vec::new();
    for SizedField { field, width } in fields_before_flexible
        .into_iter()
        .chain(flexible_field.into_iter())
        .chain(fields_after_flexible.into_iter())
    {
        let width_span = field.width_span();
        packed.push(PackedField {
            field,
            offset: match pack_dir {
                PackDir::LsbFirst => {
                    let this_lsb_offset = lsb_offset;
                    lsb_offset += width;
                    this_lsb_offset
                }
                PackDir::MsbFirst => {
                    lsb_offset -= width;
                    lsb_offset
                }
            },
            width,
            width_span,
        });
    }
    Ok(packed)
}
