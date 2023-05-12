use std::iter::{empty, once};

use proc_macro2::Span;
use syn::parse::discouraged::Speculative;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{
    braced, parenthesized, token, Attribute, Ident, LitInt, Path, Result, Token, Type, Visibility,
};

pub struct Input {
    _paren_token: token::Paren,
    pub crate_path: Path,
    _comma_token: Token![,],
    pub items: Vec<Item>,
}

impl Parse for Input {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        Ok(Input {
            _paren_token: parenthesized!(content in input),
            crate_path: content.parse()?,
            _comma_token: content.parse()?,
            items: {
                let mut items = Vec::new();
                while !content.is_empty() {
                    items.push(content.parse()?);
                }
                items
            },
        })
    }
}

pub struct Item {
    pub attrs: Vec<Attribute>,
    pub visibility: Visibility,
    pub kind: ItemKind,
}

pub enum ItemKind {
    Struct(Struct),
    Enum(Enum),
}

impl Parse for Item {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            attrs: input.call(Attribute::parse_outer)?,
            visibility: input.parse()?,
            kind: {
                let lookahead = input.lookahead1();
                if lookahead.peek(Token![struct]) {
                    Ok(ItemKind::Struct(input.parse()?))
                } else if lookahead.peek(Token![enum]) {
                    Ok(ItemKind::Enum(input.parse()?))
                } else {
                    Err(lookahead.error())
                }
            }?,
        })
    }
}

pub struct Struct {
    _struct_token: Token![struct],
    pub name: Ident,
    _colon_token: Token![:],
    pub width: LitInt,
    _brace_token: token::Brace,
    pub fields: Punctuated<Field, Token![,]>,
}

impl Parse for Struct {
    fn parse(input: ParseStream) -> Result<Self> {
        let body;
        Ok(Self {
            _struct_token: input.parse()?,
            name: input.parse()?,
            _colon_token: input.parse()?,
            width: input.parse()?,
            _brace_token: braced!(body in input),
            fields: body.parse_terminated(Field::parse, Token![,])?,
        })
    }
}

pub struct Field {
    pub attrs: Vec<Attribute>,
    pub visibility: Visibility,
    kind: FieldKind,
}

enum FieldKind {
    Regular {
        name: FieldName,
        _colon_token: Token![:],
        width: FieldWidth,
        accessor_type: FieldAccessorType,
    },
    DotDot {
        dot_dot_token: Token![..],
    },
}

impl Field {
    pub fn name_to_string(&self) -> String {
        match &self.kind {
            FieldKind::Regular {
                name: FieldName::Ident(ident),
                ..
            } => ident.to_string(),
            _ => "_".to_string(),
        }
    }

    pub fn name_span(&self) -> Span {
        match &self.kind {
            FieldKind::Regular { name, .. } => match name {
                FieldName::Ident(ident) => ident.span(),
                FieldName::Placeholder(underscore) => underscore.span(),
            },
            FieldKind::DotDot { dot_dot_token } => dot_dot_token.span(),
        }
    }

    pub fn width(&self) -> Result<Option<u8>> {
        match &self.kind {
            FieldKind::Regular {
                width: FieldWidth::LitInt(lit_int),
                ..
            } => Ok(Some(lit_int.base10_parse()?)),
            _ => Ok(None),
        }
    }

    pub fn width_span(&self) -> Span {
        match &self.kind {
            FieldKind::Regular { width, .. } => match width {
                FieldWidth::LitInt(lit_int) => lit_int.span(),
                FieldWidth::Placeholder(underscore) => underscore.span(),
            },
            FieldKind::DotDot { dot_dot_token } => dot_dot_token.span(),
        }
    }

    pub fn accessor_type(&self) -> FieldAccessorType {
        match &self.kind {
            FieldKind::Regular { accessor_type, .. } => accessor_type.clone(),
            FieldKind::DotDot { .. } => FieldAccessorType::Default,
        }
    }
}

impl Parse for Field {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            attrs: input.call(Attribute::parse_outer)?,
            visibility: input.parse()?,
            kind: {
                let lookahead = input.lookahead1();
                if lookahead.peek(Token![..]) {
                    Ok(FieldKind::DotDot {
                        dot_dot_token: input.parse()?,
                    })
                } else if lookahead.peek(Ident) | lookahead.peek(Token![_]) {
                    Ok(FieldKind::Regular {
                        name: input.parse()?,
                        _colon_token: input.parse()?,
                        width: input.parse()?,
                        accessor_type: input.parse()?,
                    })
                } else {
                    Err(lookahead.error())
                }
            }?,
        })
    }
}

pub enum FieldName {
    Ident(Ident),
    Placeholder(Token![_]),
}

impl Parse for FieldName {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();
        if lookahead.peek(Ident) {
            input.parse().map(Self::Ident)
        } else if lookahead.peek(Token![_]) {
            input.parse().map(Self::Placeholder)
        } else {
            Err(lookahead.error())
        }
    }
}

pub enum FieldWidth {
    LitInt(LitInt),
    Placeholder(Token![_]),
}

impl Parse for FieldWidth {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();
        if lookahead.peek(LitInt) {
            input.parse().map(Self::LitInt)
        } else if lookahead.peek(Token![_]) {
            input.parse().map(Self::Placeholder)
        } else {
            Err(lookahead.error())
        }
    }
}

#[derive(Clone)]
pub enum FieldAccessorType {
    Overridden { as_token: Token![as], type_: Type },
    Default,
}

impl Parse for FieldAccessorType {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Token![as]) {
            Ok(FieldAccessorType::Overridden {
                as_token: input.parse()?,
                type_: input.parse()?,
            })
        } else {
            Ok(FieldAccessorType::Default)
        }
    }
}

pub struct Enum {
    _enum_token: Token![enum],
    pub name: Ident,
    _colon_token: Token![:],
    pub width: LitInt,
    _brace_token: token::Brace,
    pub elements: Option<EnumElements>,
}

impl Enum {
    pub fn variants(&self) -> Box<dyn Iterator<Item = &Variant> + '_> {
        match &self.elements {
            Some(EnumElements::Variants { variants, .. }) => Box::new(
                once(&variants.first).chain(variants.rest.iter().map(|(_comma, variant)| variant)),
            ),
            _ => Box::new(empty()),
        }
    }

    pub fn dot_dot_token(&self) -> Option<&Token![..]> {
        match &self.elements {
            Some(EnumElements::Variants { dot_dot_token, .. }) => dot_dot_token.as_ref(),
            Some(EnumElements::DotDot { dot_dot_token }) => Some(dot_dot_token),
            None => None,
        }
    }
}

impl Parse for Enum {
    fn parse(input: ParseStream) -> Result<Self> {
        let body;
        Ok(Self {
            _enum_token: input.parse()?,
            name: input.parse()?,
            _colon_token: input.parse()?,
            width: input.parse()?,
            _brace_token: braced!(body in input),
            elements: if body.is_empty() {
                None
            } else {
                let elements = body.parse()?;
                if !body.is_empty() {
                    panic!("unexpected trailing tokens. is this possible?");
                }
                Some(elements)
            },
        })
    }
}

pub enum EnumElements {
    Variants {
        variants: Variants,
        _trailing_comma: Option<Token![,]>,
        dot_dot_token: Option<Token![..]>,
    },
    DotDot {
        dot_dot_token: Token![..],
    },
}

impl Parse for EnumElements {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Token![..]) {
            Ok(Self::DotDot {
                dot_dot_token: input.parse()?,
            })
        } else {
            let variants = input.parse()?;
            let mut _trailing_comma = None;
            let mut dot_dot_token = None;
            if input.peek(Token![,]) {
                _trailing_comma = Some(input.parse()?);
                if input.peek(Token![..]) {
                    dot_dot_token = Some(input.parse()?);
                }
            }
            Ok(Self::Variants {
                variants,
                _trailing_comma,
                dot_dot_token,
            })
        }
    }
}

pub struct Variants {
    pub first: Variant,
    pub rest: Vec<(Token![,], Variant)>,
}

impl Parse for Variants {
    fn parse(input: ParseStream) -> Result<Self> {
        fn parse_rest_element(input: ParseStream) -> Result<(Token![,], Variant)> {
            Ok((input.parse()?, input.parse()?))
        }

        fn try_parse_rest_element(input: ParseStream) -> Option<(Token![,], Variant)> {
            let fork = input.fork();
            match parse_rest_element(&fork) {
                Ok(pair) => {
                    input.advance_to(&fork);
                    Some(pair)
                }
                Err(_) => None,
            }
        }

        Ok(Self {
            first: input.parse()?,
            rest: std::iter::from_fn(|| try_parse_rest_element(input)).collect(),
        })
    }
}

pub struct Variant {
    pub attrs: Vec<Attribute>,
    pub name: Ident,
    pub discriminant: Option<Discriminant>,
}

impl Parse for Variant {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            attrs: input.call(Attribute::parse_outer)?,
            name: input.parse()?,
            discriminant: {
                if input.peek(Token![=]) {
                    Some(input.parse()?)
                } else {
                    None
                }
            },
        })
    }
}

pub struct Discriminant {
    _eq_token: Token![=],
    pub literal: LitInt,
}

impl Parse for Discriminant {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            _eq_token: input.parse()?,
            literal: input.parse()?,
        })
    }
}

#[cfg(test)]
mod tests {
    use quote::quote;

    use super::*;

    #[test]
    fn struct_empty() {
        let input = quote! { struct Foo: 32 {} };
        let Item {
            attrs,
            visibility,
            kind:
                ItemKind::Struct(Struct {
                    name,
                    width,
                    fields,
                    ..
                }),
        } = syn::parse2(input).unwrap() else { panic!() };
        assert!(attrs.is_empty());
        assert_eq!(quote! { #visibility }.to_string(), "");
        assert_eq!(quote! { #name }.to_string(), "Foo");
        assert_eq!(width.base10_digits(), "32");
        assert_eq!(fields.len(), 0);
    }

    #[test]
    fn struct_everything() {
        let input = quote! {
            /// this has a doc comment
            pub(crate) struct Bar: 5 {
                field: 1
            }
        };
        let Item {
            attrs,
            visibility,
            kind:
                ItemKind::Struct(Struct {
                    name,
                    width,
                    fields,
                    ..
                }),
        } = syn::parse2(input).unwrap() else { panic!() };
        assert_eq!(attrs.len(), 1);
        let attr = &attrs[0];
        assert_eq!(
            quote! { #attr }.to_string(),
            "# [doc = r\" this has a doc comment\"]",
        );
        assert_eq!(quote! { #visibility }.to_string(), "pub (crate)");
        assert_eq!(name.to_string(), "Bar");
        assert_eq!(width.base10_digits(), "5");
        assert_eq!(fields.len(), 1);
    }

    #[test]
    fn field_default() {
        let input = quote! { my_field: 5 };
        let Field {
            attrs,
            visibility: Visibility::Inherited,
            kind: FieldKind::Regular {
                name: FieldName::Ident(name),
                width: FieldWidth::LitInt(width),
                accessor_type: FieldAccessorType::Default,
                ..
            },
        } = syn::parse2(input).unwrap() else { panic!() };
        assert!(attrs.is_empty());
        assert_eq!(name.to_string(), "my_field");
        assert_eq!(width.to_string(), "5");
    }

    #[test]
    fn field_everything() {
        let input = quote! { pub(crate) my_field: 5 as path::to::Bar };
        let Field {
            attrs,
            visibility,
            kind: FieldKind::Regular {
                name: FieldName::Ident(name),
                width: FieldWidth::LitInt(width),
                accessor_type:
                    FieldAccessorType::Overridden {
                        type_: accessor_type,
                        ..
                    },
                ..
            },
        } = syn::parse2(input).unwrap() else { panic!() };
        assert!(attrs.is_empty());
        assert_eq!(quote! { #visibility }.to_string(), "pub (crate)");
        assert_eq!(name.to_string(), "my_field");
        assert_eq!(width.to_string(), "5");
        assert_eq!(quote! { #accessor_type }.to_string(), "path :: to :: Bar");
    }

    #[test]
    fn field_flexible() {
        let input = quote! { .. };
        assert!(matches!(
            syn::parse2(input).unwrap(),
            Field {
                kind: FieldKind::DotDot { .. },
                ..
            },
        ));
    }
}
