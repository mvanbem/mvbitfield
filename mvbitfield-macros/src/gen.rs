use proc_macro2::{Literal, Span, TokenStream};
use quote::{format_ident, quote, quote_spanned, ToTokens};
use syn::spanned::Spanned;
use syn::{Error, Path, Result};

use crate::ast::{self, AccessorType, Input};
use crate::pack::{pack, PackDir, PackedBitfield};

struct Config {
    crate_path: Path,
}

struct BitintTypeInfo {
    bitint_type: TokenStream,
    primitive_type: TokenStream,
}

impl BitintTypeInfo {
    fn with_accessor_type(self, accessor_type: AccessorType) -> AccessorTypeInfo {
        match accessor_type {
            AccessorType::Overridden { as_token, type_ } => match type_ {
                type_ => AccessorTypeInfo {
                    error_span: as_token.span().join(type_.span()).unwrap_or(type_.span()),
                    accessor_type: type_.into_token_stream(),
                    bitint_type: self.bitint_type,
                    primitive_type: self.primitive_type,
                },
            },
            AccessorType::Default => AccessorTypeInfo {
                error_span: self.bitint_type.span(),
                accessor_type: self.bitint_type.clone().into(),
                bitint_type: self.bitint_type,
                primitive_type: self.primitive_type,
            },
        }
    }
}

struct AccessorTypeInfo {
    error_span: Span,
    accessor_type: TokenStream,
    bitint_type: TokenStream,
    primitive_type: TokenStream,
}

impl Config {
    /// Names the bitint and primitive types for the given width.
    ///
    /// This will match the associated types on `mvbitfield::Accessor`, but are
    /// resolved before the macro's output to provide clearer rustdoc and editor
    /// metadata.
    fn type_info_for_width(&self, width: usize, span: Span) -> Result<BitintTypeInfo> {
        if !(1..=128).contains(&width) {
            return Err(Error::new(
                span,
                "widths must be at least 1 and at most 128",
            ));
        }

        let crate_path = &self.crate_path;
        let bitint_name = format_ident!("U{width}", span = span);
        let bitint_type = quote_spanned! {span=> #crate_path::bitint::#bitint_name };

        let primitive_width = width.next_power_of_two().max(8);
        let primitive_name = format_ident!("u{}", primitive_width, span = span);
        let primitive_type = quote_spanned! {span=> #primitive_name };

        Ok(BitintTypeInfo {
            bitint_type,
            primitive_type,
        })
    }
}

pub fn bitfield_impl(input: Input) -> TokenStream {
    let cfg = Config {
        crate_path: input.crate_path,
    };
    let results: Vec<_> = input
        .structs
        .into_iter()
        .map(|struct_| generate_struct(&cfg, struct_))
        .collect();
    quote! { #(#results)* }
}

fn generate_struct(cfg: &Config, input: ast::Struct) -> TokenStream {
    let cloned_name = input.name.clone();
    match generate_struct_impl(cfg, input) {
        Ok(result) => result,
        Err(e) => {
            let compile_error = e.into_compile_error();
            quote! {
                #compile_error
                struct #cloned_name {}
            }
        }
    }
}

fn generate_struct_impl(cfg: &Config, input: ast::Struct) -> Result<TokenStream> {
    let mut pack_dir = None;
    let mut other_attrs = Vec::new();

    for attr in input.attrs {
        match attr.path() {
            path if path.is_ident("lsb_first") => {
                attr.meta.require_path_only()?;
                if pack_dir.is_some() {
                    return Err(Error::new(
                        attr.span(),
                        "multiple packing direction attributes are not allowed",
                    ));
                }
                pack_dir = Some(PackDir::LsbFirst);
            }
            path if path.is_ident("msb_first") => {
                attr.meta.require_path_only()?;
                if pack_dir.is_some() {
                    return Err(Error::new(
                        attr.span(),
                        "multiple packing direction attributes are not allowed",
                    ));
                }
                pack_dir = Some(PackDir::MsbFirst);
            }
            _ => other_attrs.push(attr),
        }
    }

    let name = input.name;
    let struct_width = input.width.base10_parse()?;
    let BitintTypeInfo {
        primitive_type: struct_primitive_type,
        bitint_type: struct_bitint_type,
    } = cfg.type_info_for_width(struct_width, input.width.span())?;

    let crate_path = &cfg.crate_path;

    let (from_primitive_method, from_primitive_impl) =
        if [8, 16, 32, 64, 128].contains(&struct_width) {
            let from_primitive_method = quote! {
                /// Creates a bitfield struct value from a primitive value.
                ///
                /// This zero-cost conversion is a convenience alias for
                /// converting through the `bitint` type.
                #[inline(always)]
                #[must_use]
                pub const fn from_primitive(value: #struct_primitive_type) -> Self {
                    Self::from_bitint(#struct_bitint_type::from_primitive(value))
                }
            };
            let from_primitive_impl = quote! {
                impl ::core::convert::From<#struct_primitive_type> for #name {
                    #[inline(always)]
                    fn from(value: #struct_primitive_type) -> Self {
                        Self::from_primitive(value)
                    }
                }
            };
            (from_primitive_method, from_primitive_impl)
        } else {
            let from_primitive_method = TokenStream::new();
            let from_primitive_impl = quote! {
                impl ::core::convert::TryFrom<#struct_primitive_type> for #name {
                    type Error = #crate_path::bitint::RangeError;

                    #[inline(always)]
                    fn try_from(value: #struct_primitive_type) -> Result<Self, Self::Error> {
                        Ok(Self::from_bitint(
                            ::core::convert::TryFrom::try_from(value)?
                        ))
                    }
                }
            };
            (from_primitive_method, from_primitive_impl)
        };

    // Collect bitfield items.
    let mut bitfield_items = Vec::new();
    for bitfield in pack(pack_dir, name.span(), struct_width, input.bitfields)? {
        match generate_accessors(cfg, &struct_primitive_type, bitfield) {
            Ok(Some(tokens)) => bitfield_items.push(tokens),
            Ok(None) => (),
            Err(e) => bitfield_items.push(e.into_compile_error()),
        }
    }

    // Emit the struct and impl block.
    let visibility = input.visibility;
    Ok(quote! {
        #[derive(
            ::core::clone::Clone,
            ::core::marker::Copy,
            ::core::fmt::Debug,
            ::core::cmp::PartialEq,
            ::core::cmp::Eq,
            ::core::hash::Hash,
        )]
        #[repr(transparent)]
        #(#other_attrs)*
        #visibility struct #name {
            value: #struct_bitint_type,
        }

        #[allow(dead_code)]
        impl #name {
            /// Creates a bitfield struct value from a `bitint` value.
            ///
            /// This is a zero-cost conversion.
            #[inline(always)]
            #[must_use]
            pub const fn from_bitint(value: #struct_bitint_type) -> Self {
                Self { value }
            }

            #from_primitive_method

            /// Converts the value to a `bitint`.
            ///
            /// This is a zero-cost conversion.
            #[inline(always)]
            #[must_use]
            pub const fn to_bitint(self) -> #struct_bitint_type {
                self.value
            }

            /// Converts the value to the primitive type.
            ///
            /// The result is in range for the bitint type, as determined by
            /// [`UBitint::is_in_range`].
            ///
            /// This zero-cost conversion is a convenience alias for converting
            /// through the `bitint` type.
            #[inline(always)]
            #[must_use]
            pub const fn to_primitive(self) -> #struct_primitive_type {
                self.to_bitint().to_primitive()
            }

            #(#bitfield_items)*
        }

        impl ::core::convert::From<#struct_bitint_type> for #name {
            #[inline(always)]
            fn from(value: #struct_bitint_type) -> Self {
                Self::from_bitint(value)
            }
        }

        impl ::core::convert::From<#name> for #struct_bitint_type {
            #[inline(always)]
            fn from(value: #name) -> Self {
                value.to_bitint()
            }
        }

        #from_primitive_impl

        impl ::core::convert::From<#name> for #struct_primitive_type {
            #[inline(always)]
            fn from(value: #name) -> Self {
                value.to_primitive()
            }
        }

        impl #crate_path::BitfieldStruct for #name {
            type Bitint = #struct_bitint_type;

            const ZERO: Self = Self { value: #crate_path::bitint::UBitint::ZERO };
        }
    })
}

fn generate_accessors(
    cfg: &Config,
    struct_primitive_type: &TokenStream,
    bitfield: PackedBitfield,
) -> Result<Option<TokenStream>> {
    // Reserved fields do not generate any code.
    let name = bitfield.bitfield.name_to_string();
    if name.starts_with('_') {
        return Ok(None);
    }

    let visibility = &bitfield.bitfield.visibility;
    let name = bitfield.bitfield.name_to_string();
    let name_span = bitfield.bitfield.name_span();
    let AccessorTypeInfo {
        error_span: s,
        accessor_type,
        bitint_type: accessor_bitint_type,
        primitive_type: accessor_primitive_type,
    } = cfg
        .type_info_for_width(bitfield.width, bitfield.width_span)?
        .with_accessor_type(bitfield.bitfield.accessor_type());

    let shift = Literal::usize_unsuffixed(bitfield.offset);
    let offset_mask = {
        let mut literal = Literal::u128_unsuffixed(
            if bitfield.width == 128 {
                u128::MAX
            } else {
                (1 << bitfield.width) - 1
            } << bitfield.offset,
        );
        literal.set_span(bitfield.width_span);
        literal
    };

    let get_method_name = format_ident!("{}", &name, span = name_span);
    let with_method_name = format_ident!("with_{}", &name, span = name_span);
    let map_method_name = format_ident!("map_{}", &name, span = name_span);
    let replace_method_name = format_ident!("replace_{}", &name, span = name_span);
    let set_method_name = format_ident!("set_{}", &name, span = name_span);
    let update_method_name = format_ident!("update_{}", &name, span = name_span);

    let get_method = {
        let doc = format!("Extracts the `{}` bitfield.", name);
        quote_spanned! {s=>
            #[doc = #doc]
            #[inline(always)]
            #[must_use]
            #visibility fn #get_method_name(self) -> #accessor_type {
                ::core::convert::Into::into(#accessor_bitint_type::new_masked(
                    (self.to_primitive() >> #shift) as #accessor_primitive_type,
                ))
            }
        }
    };

    let with_method = {
        let doc = format!("Creates a new value with the given `{}` bitfield.", name);
        quote_spanned! {s=>
            #[doc = #doc]
            #[inline(always)]
            #[must_use]
            #visibility fn #with_method_name(self, value: #accessor_type) -> Self {
                let field: #accessor_bitint_type = ::core::convert::Into::into(value);
                let field = field.to_primitive() as #struct_primitive_type;
                // // This is a redundant operation but it helps the compiler emit the `rlwimi`
                // // instruction on PowerPC.
                // #[cfg(target_arch = "powerpc")]
                // let field = field & offset_mask;

                let struct_value = self.to_primitive();
                let new_value = (struct_value & !#offset_mask) | (field << #shift);
                // SAFETY: Both operands have only in-range bits set, so the result will, too.
                unsafe { Self::new_unchecked(new_value) }
            }
        }
    };

    let map_method: TokenStream = {
        let doc = format!(
            "Creates a new value by mapping the `{}` bitfield to a new one.",
            name,
        );
        quote! {
            #[doc = #doc]
            #[inline(always)]
            #[must_use]
            #visibility fn #map_method_name(
                self,
                f: impl ::core::ops::FnOnce(#accessor_type) -> #accessor_type,
            ) -> Self {
                self.#with_method_name(f(self.#get_method_name()))
            }
        }
    };

    let set_method: TokenStream = {
        let doc = format!("Sets the `{}` bitfield.", name);
        quote! {
            #[doc = #doc]
            #[inline(always)]
            #visibility fn #set_method_name(&mut self, value: #accessor_type) {
                *self = self.#with_method_name(value);
            }
        }
    };

    let replace_method = {
        let doc = format!(
            "Replaces the `{}` bitfield and returns the old value.",
            name,
        );
        quote! {
            #[doc = #doc]
            #[inline(always)]
            #visibility fn #replace_method_name(
                &mut self,
                value: #accessor_type,
            ) -> #accessor_type {
                let old_value = self.#get_method_name();
                self.#set_method_name(value);
                old_value
            }
        }
    };

    let update_method = {
        let doc = format!(
            "Updates the `{}` bitfield using a function and returns the old value.",
            name
        );
        quote! {
            #[doc = #doc]
            #[inline(always)]
            #visibility fn #update_method_name(
                &mut self,
                f: impl ::core::ops::FnOnce(#accessor_type) -> #accessor_type,
            ) -> #accessor_type {
                self.#replace_method_name(f(self.#get_method_name()))
            }
        }
    };

    Ok(Some(quote! {
        #get_method
        #with_method
        #map_method
        #set_method
        #replace_method
        #update_method
    }))
}
