use std::collections::BTreeMap;

use proc_macro2::{Literal, Span, TokenStream};
use quote::{format_ident, quote, quote_spanned, ToTokens};
use syn::spanned::Spanned;
use syn::{Attribute, Error, Path, Result, Visibility};

use crate::ast::{self, FieldAccessorType, Input};
use crate::pack::{pack, PackDir, PackedField};

struct Config {
    crate_path: Path,
}

struct BitintTypeInfo {
    bitint_type: TokenStream,
    bitint_name: String,
    primitive_type: TokenStream,
    primitive_name: String,
}

impl BitintTypeInfo {
    fn with_accessor_type(self, accessor_type: FieldAccessorType) -> AccessorTypeInfo {
        match accessor_type {
            FieldAccessorType::Overridden { as_token, type_ } => AccessorTypeInfo {
                error_span: as_token.span().join(type_.span()).unwrap_or(type_.span()),
                accessor_type: type_.into_token_stream(),
                bitint_type: self.bitint_type,
                primitive_type: self.primitive_type,
            },
            FieldAccessorType::Default => AccessorTypeInfo {
                error_span: self.bitint_type.span(),
                accessor_type: self.bitint_type.clone(),
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
            bitint_name: bitint_name.to_string(),
            primitive_type,
            primitive_name: primitive_name.to_string(),
        })
    }
}

pub fn bitfield_impl(input: Input) -> TokenStream {
    let cfg = Config {
        crate_path: input.crate_path,
    };
    let items: Vec<_> = input
        .items
        .into_iter()
        .map(|item| generate_item(&cfg, item))
        .collect();
    quote! { #(#items)* }
}

fn generate_item(cfg: &Config, item: ast::Item) -> TokenStream {
    match item.kind {
        ast::ItemKind::Struct(struct_) => {
            generate_struct(cfg, item.attrs, item.visibility, struct_)
        }
        ast::ItemKind::Enum(enum_) => generate_enum(cfg, item.attrs, item.visibility, enum_),
    }
}

fn generate_struct(
    cfg: &Config,
    attrs: Vec<Attribute>,
    visibility: Visibility,
    input: ast::Struct,
) -> TokenStream {
    let cloned_name = input.name.clone();
    match generate_struct_impl(cfg, attrs, visibility, input) {
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

fn generate_struct_impl(
    cfg: &Config,
    attrs: Vec<Attribute>,
    visibility: Visibility,
    input: ast::Struct,
) -> Result<TokenStream> {
    let mut pack_dir = None;
    let mut other_attrs = Vec::new();

    for attr in attrs {
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
        primitive_name: struct_primitive_name,
        bitint_type: struct_bitint_type,
        bitint_name: struct_bitint_name,
    } = cfg.type_info_for_width(struct_width, input.width.span())?;

    let crate_path = &cfg.crate_path;

    let doc = format!(
        "\n\nThis type is a generated bitfield struct. The `bitint` type is `{struct_bitint_name}` \
            and the primitive type is [`{struct_primitive_name}`].",
    );

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

    // Collect field items.
    let mut field_items = Vec::new();
    for field in pack(pack_dir, name.span(), struct_width, input.fields)? {
        match generate_accessors(cfg, &struct_primitive_type, field) {
            Ok(Some(tokens)) => field_items.push(tokens),
            Ok(None) => (),
            Err(e) => field_items.push(e.into_compile_error()),
        }
    }

    // Emit the struct and impl block.
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
        #[doc = #doc]
        #visibility struct #name {
            value: #struct_bitint_type,
        }

        #[allow(dead_code)]
        impl #name {
            /// The type's zero value.
            pub const ZERO: Self = Self { value: #struct_bitint_type::ZERO };

            /// Returns the type's zero value.
            ///
            /// This method is a `const` variant of
            /// [`BitfieldStruct::zero`](::mvbitfield::BitfieldStruct::zero).
            #[inline(always)]
            #[must_use]
            pub const fn zero() -> Self {
                Self::ZERO
            }

            /// Creates a bitfield struct value from a primitive value if it is
            /// in range for the `bitint` type.
            ///
            /// This method is a `const` variant of
            /// [`BitfieldStruct::new`](::mvbitfield::BitfieldStruct::new).
            #[inline(always)]
            #[must_use]
            pub const fn new(value: #struct_primitive_type) -> Option<Self> {
                match #struct_bitint_type::new(value) {
                    Some(value) => Some(Self::from_bitint(value)),
                    None => None,
                }
            }

            /// Creates a bitfield struct value by masking off the upper bits of
            /// a primitive value.
            ///
            /// This method is a `const` variant of
            /// [`BitfieldStruct::new_masked`](::mvbitfield::BitfieldStruct::new_masked).
            #[inline(always)]
            #[must_use]
            pub const fn new_masked(value: #struct_primitive_type) -> Self {
                Self::from_bitint(#struct_bitint_type::new_masked(value))
            }

            /// Creates a bitfield struct value from a primitive value without
            /// checking whether it is in range for the `bitint` type.
            ///
            /// This method is a `const` variant of
            /// [`BitfieldStruct::new_unchecked`](::mvbitfield::BitfieldStruct::new_unchecked).
            ///
            /// # Safety
            ///
            /// The value must be in range for the `bitint` type, as determined
            /// by [`UBitint::is_in_range`](::bitint::UBitint::is_in_range).
            #[inline(always)]
            #[must_use]
            pub const unsafe fn new_unchecked(value: #struct_primitive_type) -> Self {
                Self::from_bitint(#struct_bitint_type::new_unchecked(value))
            }

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

            #(#field_items)*
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

            type Primitive = #struct_primitive_type;

            const ZERO: Self = Self::ZERO;

            #[inline(always)]
            fn new(value: #struct_primitive_type) -> Option<Self> {
                Self::new(value)
            }

            #[inline(always)]
            fn new_masked(value: #struct_primitive_type) -> Self {
                Self::new_masked(value)
            }

            #[inline(always)]
            unsafe fn new_unchecked(value: #struct_primitive_type) -> Self {
                Self::new_unchecked(value)
            }
        }
    })
}

fn generate_accessors(
    cfg: &Config,
    struct_primitive_type: &TokenStream,
    field: PackedField,
) -> Result<Option<TokenStream>> {
    // Reserved fields do not generate any code.
    let name = field.field.name_to_string();
    if name.starts_with('_') {
        return Ok(None);
    }

    let crate_path = &cfg.crate_path;
    let visibility = &field.field.visibility;
    let name = field.field.name_to_string();
    let name_span = field.field.name_span();
    let AccessorTypeInfo {
        error_span: s,
        accessor_type,
        bitint_type: accessor_bitint_type,
        primitive_type: accessor_primitive_type,
    } = cfg
        .type_info_for_width(field.width, field.width_span)?
        .with_accessor_type(field.field.accessor_type());

    let shift = Literal::usize_unsuffixed(field.offset);
    let offset_mask = {
        let mut literal = Literal::u128_unsuffixed(
            if field.width == 128 {
                u128::MAX
            } else {
                (1 << field.width) - 1
            } << field.offset,
        );
        literal.set_span(field.width_span);
        literal
    };

    let get_method_name = format_ident!("{}", &name, span = name_span);
    let with_method_name = format_ident!("with_{}", &name, span = name_span);
    let map_method_name = format_ident!("map_{}", &name, span = name_span);
    let replace_method_name = format_ident!("replace_{}", &name, span = name_span);
    let set_method_name = format_ident!("set_{}", &name, span = name_span);
    let update_method_name = format_ident!("update_{}", &name, span = name_span);

    let get_method = {
        let doc = format!("Extracts the `{}` field.", name);
        quote_spanned! {s=>
            #[doc = #doc]
            #[inline(always)]
            #[must_use]
            #visibility fn #get_method_name(self) -> #accessor_type {
                #[allow(clippy::unnecessary_cast)]
                ::core::convert::Into::into(#accessor_bitint_type::new_masked(
                    (self.to_primitive() >> #shift) as #accessor_primitive_type,
                ))
            }
        }
    };

    let with_method = {
        let doc = format!("Creates a new value with the given `{}` field.", name);
        quote_spanned! {s=>
            #[doc = #doc]
            #[inline(always)]
            #[must_use]
            #visibility fn #with_method_name(self, value: #accessor_type) -> Self {
                let field: #accessor_bitint_type = ::core::convert::Into::into(value);
                #[allow(clippy::unnecessary_cast)]
                let field = field.to_primitive() as #struct_primitive_type;
                // // This is a redundant operation but it helps the compiler emit the `rlwimi`
                // // instruction on PowerPC.
                // #[cfg(target_arch = "powerpc")]
                // let field = field & offset_mask;

                let struct_value = self.to_primitive();
                let new_value = (struct_value & !#offset_mask) | (field << #shift);
                // SAFETY: Both operands have only in-range bits set, so the result will, too.
                unsafe { #crate_path::BitfieldStruct::new_unchecked(new_value) }
            }
        }
    };

    let map_method: TokenStream = {
        let doc = format!(
            "Creates a new value by mapping the `{}` field to a new one.",
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
        let doc = format!("Sets the `{}` field.", name);
        quote! {
            #[doc = #doc]
            #[inline(always)]
            #visibility fn #set_method_name(&mut self, value: #accessor_type) {
                *self = self.#with_method_name(value);
            }
        }
    };

    let replace_method = {
        let doc = format!("Replaces the `{}` field and returns the old value.", name,);
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
            "Updates the `{}` field using a function and returns the old value.",
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

fn generate_enum(
    cfg: &Config,
    attrs: Vec<Attribute>,
    visibility: Visibility,
    input: ast::Enum,
) -> TokenStream {
    let cloned_name = input.name.clone();
    match generate_enum_impl(cfg, attrs, visibility, input) {
        Ok(result) => result,
        Err(e) => {
            let compile_error = e.into_compile_error();
            quote! {
                #compile_error
                enum #cloned_name {}
            }
        }
    }
}

fn generate_enum_impl(
    cfg: &Config,
    attrs: Vec<Attribute>,
    visibility: Visibility,
    input: ast::Enum,
) -> Result<TokenStream> {
    let name = input.name;
    let enum_width = input.width.base10_parse()?;
    let BitintTypeInfo {
        primitive_type: enum_primitive_type,
        bitint_type: enum_bitint_type,
        ..
    } = cfg.type_info_for_width(enum_width, input.width.span())?;
    let max: usize = (1 << enum_width) - 1;

    // Gather declared variants.
    let mut variants_by_discriminant = BTreeMap::new();
    let mut next_discriminant: usize = 0;
    let mut dot_dot_span = None;
    for variant in input.variants {
        match variant {
            ast::Variant::Regular { name, discriminant } => {
                if let Some(dot_dot_span) = dot_dot_span {
                    return Err(Error::new(
                        dot_dot_span,
                        "regular variants may not follow a `..` variant",
                    ));
                }

                match discriminant {
                    Some(ast::Discriminant { literal, .. }) => {
                        next_discriminant = literal.base10_parse()?;
                        if next_discriminant > max {
                            return Err(Error::new(
                                name.span().join(literal.span()).unwrap_or(literal.span()),
                                format!("discriminant out of range for U{enum_width}"),
                            ));
                        }
                    }
                    None => {
                        if next_discriminant > max {
                            return Err(Error::new(
                                name.span(),
                                format!("discriminant out of range for U{enum_width}"),
                            ));
                        }
                    }
                }

                let s = name.span();
                let discriminant: Literal = {
                    let mut literal = Literal::usize_unsuffixed(next_discriminant);
                    literal.set_span(s);
                    literal
                };
                variants_by_discriminant.insert(
                    next_discriminant,
                    quote_spanned!(s=> #name = #discriminant,),
                );
                next_discriminant += 1;
            }
            ast::Variant::DotDot { dot_dot_token } => {
                if dot_dot_span.is_some() {
                    return Err(Error::new(
                        dot_dot_token.span(),
                        "only up to one `..` variant is permitted",
                    ));
                }
                dot_dot_span = Some(dot_dot_token.span());
            }
        }
    }

    // Enforce that all discriminants are used.
    if let Some(dot_dot_span) = dot_dot_span {
        for discriminant in 0..=max {
            variants_by_discriminant
                .entry(discriminant)
                .or_insert_with(|| {
                    let variant = format_ident!("Unused{discriminant}", span = dot_dot_span);
                    let discriminant_literal: Literal = {
                        let mut literal = Literal::usize_unsuffixed(discriminant);
                        literal.set_span(dot_dot_span);
                        literal
                    };
                    quote_spanned!(dot_dot_span=> #variant = #discriminant_literal)
                });
        }
    } else if variants_by_discriminant.len() != 1 << enum_width {
        return Err(Error::new(
            name.span(),
            "unused discriminants; consider specifying a `..` variant",
        ));
    }
    let variants = Vec::from_iter(variants_by_discriminant.into_values());

    Ok(quote! {
        #[derive(Clone, Copy, Debug, Eq)]
        #[repr(#enum_primitive_type)]
        #(#attrs)*
        #visibility enum #name {
            #(#variants)*
        }

        impl #name {
            pub fn new(value: #enum_primitive_type) -> Option<Self> {
                match #enum_bitint_type::new(value) {
                    Some(value) => Some(Self::from_bitint(value)),
                    None => None,
                }
            }

            #[inline(always)]
            #[must_use]
            pub fn from_bitint(value: #enum_bitint_type) -> Self {
                // SAFETY: Self is a field-less enum with a primitive
                // representation, so its layout is the same as the
                // discriminant.
                //
                // In addition, the set of valid discriminants is the same as
                // the set of valid primitive values for the bitint type.
                unsafe { ::core::mem::transmute(value.to_primitive()) }
            }

            #[inline(always)]
            #[must_use]
            pub fn to_bitint(self) -> #enum_bitint_type {
                // SAFETY: Self is a field-less enum with a primitive
                // representation, so its layout is the same as the
                // discriminant.
                //
                // In addition, the set of valid discriminants is the same as
                // the set of valid primitive values for the bitint type.
                unsafe { ::core::mem::transmute(self) }
            }

            #[inline(always)]
            #[must_use]
            pub fn to_primitive(self) -> #enum_primitive_type {
                self.to_bitint().to_primitive()
            }
        }

        impl ::core::cmp::PartialEq for #name {
            #[inline(always)]
            fn eq(&self, rhs: &Self) -> bool {
                ::core::cmp::PartialEq::eq(&self.to_bitint(), &rhs.to_bitint())
            }
        }

        impl ::core::hash::Hash for #name {
            fn hash<H: ::core::hash::Hasher>(&self, state: &mut H) {
                ::core::hash::Hash::hash(&self.to_bitint(), state);
            }
        }

        impl ::core::convert::From<#enum_bitint_type> for #name {
            #[inline(always)]
            fn from(value: #enum_bitint_type) -> Self {
                Self::from_bitint(value)
            }
        }

        impl ::core::convert::From<#name> for #enum_bitint_type {
            #[inline(always)]
            fn from(value: #name) -> Self {
                value.to_bitint()
            }
        }
    })
}
