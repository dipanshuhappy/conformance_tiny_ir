//! Sugar → IR. The checker never sees these attrs; it only sees Schema.

use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::parse::Parser;
use syn::punctuated::Punctuated;
use syn::{
    parse_macro_input, Attribute, Data, DeriveInput, Expr, ExprLit, Fields, FnArg, ImplItem,
    ImplItemFn, ItemFn, ItemImpl, Lit, Meta, Signature, Token, Type,
};

/// `#[derive(Schema)]` + field attrs generate `fn conformance_schema() -> Schema`.
#[proc_macro_derive(Schema, attributes(enum_, required_if, field, pos, len, shape))]
pub fn derive_schema(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let schema_name = name.to_string();

    let Data::Struct(data) = &input.data else {
        return syn::Error::new_spanned(&input, "Schema derive only on structs")
            .to_compile_error()
            .into();
    };
    let Fields::Named(fields) = &data.fields else {
        return syn::Error::new_spanned(&input, "Schema derive needs named fields")
            .to_compile_error()
            .into();
    };

    let mut field_tokens = Vec::new();
    for f in &fields.named {
        let fname = f.ident.as_ref().unwrap().to_string();
        let mut props = Vec::new();
        for attr in &f.attrs {
            if attr.path().is_ident("enum_") {
                match parse_string_list(attr) {
                    Ok(list) => {
                        let lits = list.iter().map(|s| quote! { #s });
                        props.push(quote! {
                            ::conformance_lang::one_of(&[#(#lits),*])
                        });
                    }
                    Err(e) => return e.to_compile_error().into(),
                }
            } else if attr.path().is_ident("required_if") {
                match parse_required_if_pred(attr) {
                    Ok(pred) => props.push(quote! {
                        ::conformance_lang::when(#pred, ::conformance_lang::defined())
                    }),
                    Err(e) => return e.to_compile_error().into(),
                }
            } else if attr.path().is_ident("shape") {
                match parse_shape(attr) {
                    Ok(form) => props.push(quote! {
                        ::conformance_lang::shape(::conformance_lang::Form::#form)
                    }),
                    Err(e) => return e.to_compile_error().into(),
                }
            } else if attr.path().is_ident("pos") {
                match parse_usize(attr) {
                    Ok(n) => props.push(quote! { ::conformance_lang::at(#n) }),
                    Err(e) => return e.to_compile_error().into(),
                }
            } else if attr.path().is_ident("len") {
                match parse_usize(attr) {
                    Ok(n) => props.push(quote! { ::conformance_lang::width(#n) }),
                    Err(e) => return e.to_compile_error().into(),
                }
            }
        }
        let locator_name = field_locator(&f.attrs).unwrap_or_else(|| fname.clone());
        field_tokens.push(quote! {
            ::conformance_lang::Field {
                name: #fname.into(),
                locator: ::conformance_lang::Locator::Path(#locator_name.into()),
                invariants: vec![#(#props),*],
                wire: None,
            }
        });
    }

    TokenStream::from(quote! {
        impl #name {
            pub fn conformance_schema() -> ::conformance_lang::Schema {
                ::conformance_lang::Schema {
                    name: #schema_name.into(),
                    width: None,
                    fields: vec![#(#field_tokens),*],
                }
            }
        }
    })
}

/// Unfold this transition in a generated `#[test]`.
///
/// Put it on a **free function** or on the **`impl` block**. Rustc will not
/// collect `#[test]` on an impl method — that placement is a compile error
/// with a pointer here.
///
/// The test `include_str!`s this file, so callees in the same file are followed.
#[proc_macro_attribute]
pub fn transition(_args: TokenStream, item: TokenStream) -> TokenStream {
    if let Ok(f) = syn::parse::<ItemFn>(item.clone()) {
        return expand_item_fn(f);
    }
    if let Ok(im) = syn::parse::<ItemImpl>(item.clone()) {
        return expand_item_impl(im);
    }
    if let Ok(m) = syn::parse::<ImplItemFn>(item) {
        return expand_impl_method(m);
    }
    syn::Error::new(
        proc_macro2::Span::call_site(),
        "#[conformance::transition] on a free fn or an `impl` block",
    )
    .to_compile_error()
    .into()
}

fn expand_item_fn(f: ItemFn) -> TokenStream {
    let name = f.sig.ident.to_string();
    match schema_ty_from_sig(&f.sig, None).and_then(|ty| {
        transition_test(&ty, std::slice::from_ref(&name)).map(|test| (f.clone(), test))
    }) {
        Ok((f, test)) => quote! { #f #test }.into(),
        Err(e) => {
            let err = e.to_compile_error();
            quote! { #f #err }.into()
        }
    }
}

fn expand_item_impl(im: ItemImpl) -> TokenStream {
    let ty = peel_refs((*im.self_ty).clone());
    let ty_name = type_last_ident(&ty);
    let names: Vec<String> = im
        .items
        .iter()
        .filter_map(|it| {
            let ImplItem::Fn(m) = it else { return None };
            if is_transition_sig(&m.sig, ty_name.as_deref()) {
                Some(m.sig.ident.to_string())
            } else {
                None
            }
        })
        .collect();
    if names.is_empty() {
        let err = syn::Error::new_spanned(
            &im.self_ty,
            "#[conformance::transition] impl: no method with `self` or a schema-typed param",
        )
        .to_compile_error();
        return quote! { #im #err }.into();
    }
    match transition_test(&ty, &names) {
        Ok(test) => quote! { #im #test }.into(),
        Err(e) => {
            let err = e.to_compile_error();
            quote! { #im #err }.into()
        }
    }
}

fn expand_impl_method(m: ImplItemFn) -> TokenStream {
    let err = syn::Error::new_spanned(
        &m.sig.ident,
        "#[conformance::transition] cannot sit on an impl method \
         (`#[test]` is only a free function). Put it on the `impl` block, or on a free fn.",
    )
    .to_compile_error();
    quote! { #m #err }.into()
}

fn transition_test(schema_ty: &Type, fn_names: &[String]) -> syn::Result<proc_macro2::TokenStream> {
    let test_ident = if fn_names.len() == 1 {
        format_ident!("conformance_transition_{}", fn_names[0])
    } else {
        let ty = type_last_ident(schema_ty).unwrap_or_else(|| "impl".into());
        format_ident!("conformance_transition_{}", ty)
    };
    let src_path = proc_macro::Span::call_site().local_file().ok_or_else(|| {
        syn::Error::new(
            proc_macro2::Span::call_site(),
            "#[conformance::transition] needs a real source file",
        )
    })?;
    let src_path = if src_path.is_absolute() {
        src_path
    } else {
        std::env::current_dir().unwrap_or_default().join(&src_path)
    };
    let src_path = src_path.canonicalize().unwrap_or(src_path);
    let src_path = src_path.to_str().ok_or_else(|| {
        syn::Error::new(
            proc_macro2::Span::call_site(),
            "#[conformance::transition] source path is not UTF-8",
        )
    })?;
    Ok(quote! {
        #[cfg(test)]
        #[test]
        fn #test_ident() {
            let src = include_str!(#src_path);
            let schema = <#schema_ty>::conformance_schema();
            #(
            {
                let name = #fn_names;
                let report = match ::conformance_lang::eval_unfold_named(&schema, src, name) {
                    Ok(r) => r,
                    Err(e) => panic!("unfold `{name}`: {e}"),
                };
                assert!(
                    report.ok(),
                    "#[conformance::transition] `{name}` failed:\n{}",
                    report.fail_summary()
                );
            }
            )*
        }
    })
}

fn schema_ty_from_sig(sig: &Signature, impl_ty: Option<&Type>) -> syn::Result<Type> {
    match sig.inputs.first() {
        Some(FnArg::Receiver(_)) => impl_ty.cloned().ok_or_else(|| {
            syn::Error::new_spanned(
                &sig.ident,
                "#[conformance::transition] on `self`: put the attr on the `impl` block",
            )
        }),
        Some(FnArg::Typed(pt)) => Ok(peel_refs((*pt.ty).clone())),
        None => Err(syn::Error::new_spanned(
            &sig.ident,
            "#[conformance::transition] needs a param of the Schema type",
        )),
    }
}

fn is_transition_sig(sig: &Signature, impl_ty_name: Option<&str>) -> bool {
    for input in &sig.inputs {
        match input {
            FnArg::Receiver(_) => return true,
            FnArg::Typed(pt) => {
                let ty = peel_refs((*pt.ty).clone());
                let last = type_last_ident(&ty);
                if last.as_deref() == Some("Self") {
                    return true;
                }
                if impl_ty_name.is_some() && last.as_deref() == impl_ty_name {
                    return true;
                }
                if impl_ty_name.is_none() {
                    return true;
                }
            }
        }
    }
    false
}

fn peel_refs(mut ty: Type) -> Type {
    loop {
        ty = match ty {
            Type::Reference(r) => *r.elem,
            Type::Paren(p) => *p.elem,
            other => return other,
        };
    }
}

fn type_last_ident(ty: &Type) -> Option<String> {
    match ty {
        Type::Path(p) => p.path.segments.last().map(|s| s.ident.to_string()),
        Type::Reference(r) => type_last_ident(&r.elem),
        Type::Paren(p) => type_last_ident(&p.elem),
        _ => None,
    }
}

fn field_locator(attrs: &[Attribute]) -> Option<String> {
    for attr in attrs {
        if attr.path().is_ident("field") {
            if let Meta::List(list) = &attr.meta {
                if let Ok(Lit::Str(s)) = syn::parse2::<Lit>(list.tokens.clone()) {
                    return Some(s.value());
                }
            }
        }
    }
    None
}

fn parse_string_list(attr: &Attribute) -> syn::Result<Vec<String>> {
    let Meta::List(list) = &attr.meta else {
        return Err(syn::Error::new_spanned(attr, "expected #[enum_(...)]"));
    };
    let parser = Punctuated::<Lit, Token![,]>::parse_terminated;
    let lits = parser.parse2(list.tokens.clone())?;
    let mut out = Vec::new();
    for lit in lits {
        let Lit::Str(s) = lit else {
            return Err(syn::Error::new_spanned(lit, "expected string literals"));
        };
        out.push(s.value());
    }
    Ok(out)
}

fn parse_required_if_pred(attr: &Attribute) -> syn::Result<proc_macro2::TokenStream> {
    let Meta::List(list) = &attr.meta else {
        return Err(syn::Error::new_spanned(
            attr,
            "expected #[required_if(...)]",
        ));
    };
    let parser = Punctuated::<Expr, Token![,]>::parse_terminated;
    let exprs = parser.parse2(list.tokens.clone())?;
    if exprs.is_empty() {
        return Err(syn::Error::new_spanned(
            &list.tokens,
            "expected kind = \"hi\"",
        ));
    }
    let mut preds = Vec::new();
    for expr in &exprs {
        preds.push(pred_from_assign(expr)?);
    }
    if preds.len() == 1 {
        Ok(preds.pop().unwrap())
    } else {
        Ok(quote! { ::conformance_lang::Predicate::And(vec![#(#preds),*]) })
    }
}

fn pred_from_assign(expr: &Expr) -> syn::Result<proc_macro2::TokenStream> {
    let Expr::Assign(assign) = expr else {
        return Err(syn::Error::new_spanned(expr, "expected kind = \"hi\""));
    };
    let field = match &*assign.left {
        Expr::Path(p) => p
            .path
            .get_ident()
            .ok_or_else(|| syn::Error::new_spanned(&assign.left, "expected field name"))?
            .to_string(),
        _ => return Err(syn::Error::new_spanned(&assign.left, "expected field name")),
    };
    match &*assign.right {
        Expr::Lit(ExprLit {
            lit: Lit::Str(s), ..
        }) => {
            let lit = s.value();
            Ok(quote! {
                ::conformance_lang::Predicate::Eq {
                    field: #field.into(),
                    lit: #lit.into(),
                }
            })
        }
        Expr::Array(arr) => {
            let mut lits = Vec::new();
            for el in &arr.elems {
                let Expr::Lit(ExprLit {
                    lit: Lit::Str(s), ..
                }) = el
                else {
                    return Err(syn::Error::new_spanned(el, "expected string literals"));
                };
                lits.push(s.value());
            }
            Ok(quote! {
                ::conformance_lang::Predicate::In {
                    field: #field.into(),
                    lits: vec![#(#lits.into()),*],
                }
            })
        }
        _ => Err(syn::Error::new_spanned(
            &assign.right,
            "expected string literal or [\"a\", \"b\"]",
        )),
    }
}

fn parse_shape(attr: &Attribute) -> syn::Result<syn::Ident> {
    let Meta::List(list) = &attr.meta else {
        return Err(syn::Error::new_spanned(
            attr,
            "expected #[shape(scalar|array)]",
        ));
    };
    let ident: syn::Ident = syn::parse2(list.tokens.clone())?;
    let form = match ident.to_string().as_str() {
        "scalar" => "Scalar",
        "array" => "Array",
        _ => {
            return Err(syn::Error::new_spanned(ident, "expected scalar or array"));
        }
    };
    Ok(syn::Ident::new(form, ident.span()))
}

fn parse_usize(attr: &Attribute) -> syn::Result<usize> {
    let Meta::List(list) = &attr.meta else {
        return Err(syn::Error::new_spanned(
            attr,
            "expected #[pos(n)] / #[len(n)]",
        ));
    };
    let lit: Lit = syn::parse2(list.tokens.clone())?;
    match lit {
        Lit::Int(i) => i.base10_parse(),
        other => Err(syn::Error::new_spanned(other, "expected integer")),
    }
}
