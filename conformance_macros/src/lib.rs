//! Sugar → IR. The checker never sees these attrs; it only sees Schema.
//!
//! `#[derive(Schema)]` Unfolds `{crate}/src` at **expand time** and
//! `compile_error!`s on Fail. Not a `#[test]`.

use std::path::{Path, PathBuf};

use conformance_lang::{
    absent, at, defined, eval_crate, eval_unfold_named, one_of, or_absent, pred_eq, pred_in,
    pred_not, rewrite, shape, when, width, Field, Form, Invariant, Locator, Predicate, Schema,
};
use proc_macro::TokenStream;
use quote::quote;
use syn::parse::{ParseStream, Parser};
use syn::punctuated::Punctuated;
use syn::{
    parse_macro_input, Attribute, Data, DeriveInput, Expr, ExprLit, Fields, FieldsNamed, FnArg,
    Ident, ImplItem, ImplItemFn, Item, ItemFn, ItemImpl, Lit, LitStr, Meta, Signature, Token, Type,
};

/// `#[derive(Schema)]` + field attrs generate `fn conformance_schema() -> Schema`.
#[proc_macro_derive(
    Schema,
    attributes(enum_, required_if, field, pos, len, shape, when, refine, nested, leaf)
)]
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
    let mut rewrite_tokens = Vec::new();
    for f in &fields.named {
        let fname = f.ident.as_ref().unwrap().to_string();
        let mut props = Vec::new();
        let leaf = f.attrs.iter().any(|a| a.path().is_ident("leaf"));
        let mut nested_explicit = false;
        for attr in &f.attrs {
            if attr.path().is_ident("when") {
                match parse_when_attr(attr, &fname) {
                    Ok(WhenSugar::Rewrite { pred, then }) => {
                        let pred_ts = quote_pred(&pred);
                        let then_ts = quote_inv(&then);
                        rewrite_tokens.push(quote! {
                            ::conformance_lang::rewrite(#fname, #pred_ts, #then_ts)
                        });
                    }
                    Ok(WhenSugar::Photo { pred, then }) => {
                        let pred_ts = quote_pred(&pred);
                        let then_ts = quote_inv(&then);
                        if is_option_ty(&f.ty) {
                            props.push(quote! {
                                ::conformance_lang::when(#pred_ts, ::conformance_lang::or_absent(#then_ts))
                            });
                        } else {
                            props.push(quote! {
                                ::conformance_lang::when(#pred_ts, #then_ts)
                            });
                        }
                    }
                    Err(e) => return e.to_compile_error().into(),
                }
            } else if attr.path().is_ident("enum_") {
                match parse_string_list(attr) {
                    Ok(list) => {
                        let lits = list.iter().map(|s| quote! { #s });
                        let one = quote! { ::conformance_lang::one_of(&[#(#lits),*]) };
                        if is_option_ty(&f.ty) {
                            props.push(quote! { ::conformance_lang::or_absent(#one) });
                        } else {
                            props.push(one);
                        }
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
            } else if attr.path().is_ident("nested") {
                nested_explicit = true;
                props.push(quote_nested(&f.ty));
            } else if attr.path().is_ident("leaf") {
                // opt out of default nested walk
            } else if attr.path().is_ident("refine") {
                match parse_refine_attr(attr) {
                    Ok(sugar) => {
                        let a = lift_refine_ty(&f.ty);
                        let built = match sugar {
                            RefineSugar::Path(path) => quote! { #path() },
                            RefineSugar::Inline(closure) => {
                                if type_last_ident(&lift_inner_ty(&f.ty)).as_deref()
                                    == Some("String")
                                {
                                    quote! { ::conformance_lang::refine(#closure) }
                                } else {
                                    quote! { ::conformance_lang::refine_on::<#a>(#closure) }
                                }
                            }
                        };
                        let erased = quote! {{
                            let __r: ::conformance_lang::Refine<#a> = #built;
                            ::conformance_lang::Invariant::from(__r)
                        }};
                        if is_option_ty(&f.ty) {
                            props.push(quote! { ::conformance_lang::or_absent(#erased) });
                        } else {
                            props.push(erased);
                        }
                    }
                    Err(e) => return e.to_compile_error().into(),
                }
            }
        }
        if !leaf && !nested_explicit && should_nest(&f.ty) {
            props.push(quote_nested(&f.ty));
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

    let ir = match schema_from_fields(&schema_name, fields) {
        Ok(s) => s,
        Err(e) => return e.to_compile_error().into(),
    };
    let (watch, fail) = crate_compile_check(&ir);

    TokenStream::from(quote! {
        impl #name {
            pub fn conformance_schema() -> ::conformance_lang::Schema {
                ::conformance_lang::Schema {
                    name: #schema_name.into(),
                    width: None,
                    fields: vec![#(#field_tokens),*],
                    rewrites: vec![#(#rewrite_tokens),*],
                }
            }
        }
        #watch
        #fail
    })
}

/// Unfold this transition at **expand time**. Fail is `compile_error!`.
///
/// Put it on a free function, an `impl` block, or a method.
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

/// Mute this fn as a **site**. Message is required (why it is allowed).
/// Follow from other sites still enters the body.
#[proc_macro_attribute]
pub fn except(args: TokenStream, item: TokenStream) -> TokenStream {
    match parse_except_message(args) {
        Ok(_) => item,
        Err(e) => {
            let err = e.to_compile_error();
            let item: proc_macro2::TokenStream = item.into();
            quote! { #item #err }.into()
        }
    }
}

fn parse_except_message(args: TokenStream) -> syn::Result<String> {
    let lit: Lit = syn::parse(args)?;
    let Lit::Str(s) = lit else {
        return Err(syn::Error::new_spanned(
            lit,
            "#[except(\"why\")] needs a string",
        ));
    };
    let v = s.value();
    if v.trim().is_empty() {
        return Err(syn::Error::new_spanned(
            s,
            "#[except(\"why\")] needs a non-empty reason",
        ));
    }
    Ok(v)
}

fn expand_item_fn(f: ItemFn) -> TokenStream {
    let name = f.sig.ident.to_string();
    match schema_ty_from_sig(&f.sig, None).and_then(|ty| file_compile_check(&ty, &[name])) {
        Ok((watch, fail)) => quote! { #f #watch #fail }.into(),
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
    match file_compile_check(&ty, &names) {
        Ok((watch, fail)) => quote! { #im #watch #fail }.into(),
        Err(e) => {
            let err = e.to_compile_error();
            quote! { #im #err }.into()
        }
    }
}

fn expand_impl_method(m: ImplItemFn) -> TokenStream {
    let name = m.sig.ident.to_string();
    match method_compile_check(&name) {
        Ok((watch, fail)) => splice_into_method(m, quote! { #watch #fail }),
        Err(e) => splice_into_method(m, e.to_compile_error()),
    }
}

fn splice_into_method(mut m: ImplItemFn, extra: proc_macro2::TokenStream) -> TokenStream {
    let body = m.block;
    m.block = syn::parse_quote! {{
        #extra
        #body
    }};
    quote! { #m }.into()
}

fn crate_compile_check(schema: &Schema) -> (proc_macro2::TokenStream, proc_macro2::TokenStream) {
    let Some(root) = crate_root() else {
        return (
            quote! {},
            quote! { compile_error!("conformance: cannot find crate root"); },
        );
    };
    let src = root.join("src");
    let watch = watch_rs(&src);
    let fail = match eval_crate(schema, &root) {
        Ok(report) if report.ok() => quote! {},
        Ok(report) => {
            let msg = format!("conformance `{}`:\n{}", schema.name, report.fail_summary());
            quote! { compile_error!(#msg); }
        }
        Err(e) => {
            let msg = format!("conformance `{}`: {e}", schema.name);
            quote! { compile_error!(#msg); }
        }
    };
    (watch, fail)
}

fn file_compile_check(
    schema_ty: &Type,
    fn_names: &[String],
) -> syn::Result<(proc_macro2::TokenStream, proc_macro2::TokenStream)> {
    let path = source_path()?;
    let src = std::fs::read_to_string(&path).map_err(|e| {
        syn::Error::new(
            proc_macro2::Span::call_site(),
            format!("{}: {e}", path.display()),
        )
    })?;
    let type_name = type_last_ident(schema_ty).ok_or_else(|| {
        syn::Error::new(
            proc_macro2::Span::call_site(),
            "#[conformance::transition] needs a named Schema type",
        )
    })?;
    let file: syn::File = syn::parse_str(&src)
        .map_err(|e| syn::Error::new(proc_macro2::Span::call_site(), e.to_string()))?;
    let schema = schema_in_file(&file, &type_name)?;
    let watch = watch_one(&path);
    let mut fail = quote! {};
    for name in fn_names {
        match eval_unfold_named(&schema, &src, name) {
            Ok(report) if report.ok() => {}
            Ok(report) => {
                let msg = format!("conformance `{name}`:\n{}", report.fail_summary());
                fail = quote! { #fail compile_error!(#msg); };
            }
            Err(e) => {
                let msg = format!("conformance `{name}`: {e}");
                fail = quote! { #fail compile_error!(#msg); };
            }
        }
    }
    Ok((watch, fail))
}

fn method_compile_check(
    fn_name: &str,
) -> syn::Result<(proc_macro2::TokenStream, proc_macro2::TokenStream)> {
    let path = source_path()?;
    let src = std::fs::read_to_string(&path).map_err(|e| {
        syn::Error::new(
            proc_macro2::Span::call_site(),
            format!("{}: {e}", path.display()),
        )
    })?;
    let file: syn::File = syn::parse_str(&src)
        .map_err(|e| syn::Error::new(proc_macro2::Span::call_site(), e.to_string()))?;
    let type_name = impl_type_for_method(&file, fn_name).ok_or_else(|| {
        syn::Error::new(
            proc_macro2::Span::call_site(),
            "#[conformance::transition] method: could not find enclosing impl type",
        )
    })?;
    let schema = schema_in_file(&file, &type_name)?;
    let watch = watch_one(&path);
    let fail = match eval_unfold_named(&schema, &src, fn_name) {
        Ok(report) if report.ok() => quote! {},
        Ok(report) => {
            let msg = format!("conformance `{fn_name}`:\n{}", report.fail_summary());
            quote! { compile_error!(#msg); }
        }
        Err(e) => {
            let msg = format!("conformance `{fn_name}`: {e}");
            quote! { compile_error!(#msg); }
        }
    };
    Ok((watch, fail))
}

fn impl_type_for_method(file: &syn::File, fn_name: &str) -> Option<String> {
    impl_type_in_items(&file.items, fn_name)
}

fn impl_type_in_items(items: &[Item], fn_name: &str) -> Option<String> {
    for item in items {
        match item {
            Item::Impl(im) => {
                let has = im
                    .items
                    .iter()
                    .any(|it| matches!(it, ImplItem::Fn(m) if m.sig.ident == fn_name));
                if has {
                    return type_last_ident(&im.self_ty);
                }
            }
            Item::Mod(m) => {
                if let Some((_, nested)) = &m.content {
                    if let Some(ty) = impl_type_in_items(nested, fn_name) {
                        return Some(ty);
                    }
                }
            }
            _ => {}
        }
    }
    None
}

fn schema_in_file(file: &syn::File, type_name: &str) -> syn::Result<Schema> {
    schema_in_items(&file.items, type_name).ok_or_else(|| {
        syn::Error::new(
            proc_macro2::Span::call_site(),
            format!("#[derive(Schema)] struct {type_name} not in this file"),
        )
    })
}

fn schema_in_items(items: &[Item], type_name: &str) -> Option<Schema> {
    for item in items {
        match item {
            Item::Struct(s) if s.ident == type_name && has_derive_schema(&s.attrs) => {
                let Fields::Named(fields) = &s.fields else {
                    continue;
                };
                return schema_from_fields(type_name, fields).ok();
            }
            Item::Mod(m) => {
                if let Some((_, nested)) = &m.content {
                    if let Some(schema) = schema_in_items(nested, type_name) {
                        return Some(schema);
                    }
                }
            }
            _ => {}
        }
    }
    None
}

fn has_derive_schema(attrs: &[Attribute]) -> bool {
    for attr in attrs {
        if !attr.path().is_ident("derive") {
            continue;
        }
        let Meta::List(list) = &attr.meta else {
            continue;
        };
        let parser = Punctuated::<syn::Path, Token![,]>::parse_terminated;
        let Ok(paths) = parser.parse2(list.tokens.clone()) else {
            continue;
        };
        if paths
            .iter()
            .any(|p| p.segments.last().is_some_and(|s| s.ident == "Schema"))
        {
            return true;
        }
    }
    false
}

fn schema_from_fields(name: &str, fields: &FieldsNamed) -> syn::Result<Schema> {
    let mut out = Vec::new();
    let mut rewrites = Vec::new();
    for f in &fields.named {
        let fname = f.ident.as_ref().unwrap().to_string();
        let mut invariants = Vec::new();
        for attr in &f.attrs {
            if attr.path().is_ident("enum_") {
                let list = parse_string_list(attr)?;
                let refs: Vec<&str> = list.iter().map(|s| s.as_str()).collect();
                let inv = one_of(&refs);
                invariants.push(if is_option_ty(&f.ty) {
                    or_absent(inv)
                } else {
                    inv
                });
            } else if attr.path().is_ident("required_if") {
                invariants.push(when(required_if_pred_ir(attr)?, defined()));
            } else if attr.path().is_ident("when") {
                match parse_when_attr(attr, &fname)? {
                    WhenSugar::Rewrite { pred, then } => {
                        rewrites.push(rewrite(&fname, pred, then));
                    }
                    WhenSugar::Photo { pred, then } => {
                        let then = if is_option_ty(&f.ty) {
                            or_absent(then)
                        } else {
                            then
                        };
                        invariants.push(when(pred, then));
                    }
                }
            } else if attr.path().is_ident("shape") {
                let form = parse_shape(attr)?;
                let form = match form.to_string().as_str() {
                    "Scalar" => Form::Scalar,
                    _ => Form::Array,
                };
                invariants.push(shape(form));
            } else if attr.path().is_ident("pos") {
                invariants.push(at(parse_usize(attr)?));
            } else if attr.path().is_ident("len") {
                invariants.push(width(parse_usize(attr)?));
            }
            // `#[refine(path)]` is a domain fn — expand-time IR cannot call it.
        }
        let locator_name = field_locator(&f.attrs).unwrap_or_else(|| fname.clone());
        out.push(Field {
            name: fname,
            locator: Locator::Path(locator_name),
            invariants,
            wire: None,
        });
    }
    Ok(Schema {
        name: name.into(),
        width: None,
        fields: out,
        rewrites,
    })
}

fn required_if_pred_ir(attr: &Attribute) -> syn::Result<Predicate> {
    let Meta::List(list) = &attr.meta else {
        return Err(syn::Error::new_spanned(
            attr,
            "expected #[required_if(...)]",
        ));
    };
    let parser = Punctuated::<Expr, Token![,]>::parse_terminated;
    let exprs = parser.parse2(list.tokens.clone())?;
    let mut preds = Vec::new();
    for expr in &exprs {
        preds.push(pred_ir(expr)?);
    }
    if preds.len() == 1 {
        Ok(preds.pop().unwrap())
    } else {
        Ok(Predicate::And(preds))
    }
}

fn pred_ir(expr: &Expr) -> syn::Result<Predicate> {
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
        }) => Ok(pred_eq(&field, &s.value())),
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
            let refs: Vec<&str> = lits.iter().map(|s| s.as_str()).collect();
            Ok(pred_in(&field, &refs))
        }
        _ => Err(syn::Error::new_spanned(
            &assign.right,
            "expected string literal or [\"a\", \"b\"]",
        )),
    }
}

fn source_path() -> syn::Result<PathBuf> {
    let path = proc_macro::Span::call_site().local_file().ok_or_else(|| {
        syn::Error::new(
            proc_macro2::Span::call_site(),
            "conformance needs a real source file",
        )
    })?;
    let path = if path.is_absolute() {
        path
    } else {
        std::env::current_dir().unwrap_or_default().join(path)
    };
    Ok(path.canonicalize().unwrap_or(path))
}

fn crate_root() -> Option<PathBuf> {
    if let Ok(file) = source_path() {
        let mut dir = file.parent().map(Path::to_path_buf);
        while let Some(d) = dir {
            if d.join("Cargo.toml").exists() {
                return Some(d);
            }
            dir = d.parent().map(Path::to_path_buf);
        }
    }
    std::env::var_os("CARGO_MANIFEST_DIR").map(PathBuf::from)
}

fn watch_one(path: &Path) -> proc_macro2::TokenStream {
    let Some(s) = path.to_str() else {
        return quote! {};
    };
    quote! {
        #[allow(dead_code)]
        const _: &str = include_str!(#s);
    }
}

fn watch_rs(dir: &Path) -> proc_macro2::TokenStream {
    if !dir.exists() {
        return quote! {};
    }
    let mut paths = Vec::new();
    let _ = collect_rs(dir, &mut paths);
    let lits: Vec<String> = paths
        .into_iter()
        .filter_map(|p| p.to_str().map(str::to_string))
        .collect();
    quote! {
        #(
            #[allow(dead_code)]
            const _: &str = include_str!(#lits);
        )*
    }
}

fn collect_rs(dir: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
    for ent in std::fs::read_dir(dir)? {
        let ent = ent?;
        let p = ent.path();
        if p.is_dir() {
            collect_rs(&p, out)?;
        } else if p.extension().and_then(|e| e.to_str()) == Some("rs") {
            out.push(p.canonicalize().unwrap_or(p));
        }
    }
    Ok(())
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

fn is_option_ty(ty: &Type) -> bool {
    match peel_refs(ty.clone()) {
        Type::Path(p) => p.path.segments.last().is_some_and(|s| s.ident == "Option"),
        _ => false,
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

enum RefineSugar {
    Path(syn::Path),
    Inline(syn::ExprClosure),
}

fn parse_refine_attr(attr: &Attribute) -> syn::Result<RefineSugar> {
    let Meta::List(list) = &attr.meta else {
        return Err(syn::Error::new_spanned(
            attr,
            "expected #[refine(path)] or #[refine(|x| …)]",
        ));
    };
    let expr: Expr = syn::parse2(list.tokens.clone())?;
    match expr {
        Expr::Path(p) => Ok(RefineSugar::Path(p.path)),
        Expr::Closure(c) => Ok(RefineSugar::Inline(c)),
        other => Err(syn::Error::new_spanned(
            other,
            "expected path or |x| closure",
        )),
    }
}

fn lift_inner_ty(ty: &Type) -> Type {
    let ty = peel_refs(ty.clone());
    if let Type::Path(p) = &ty {
        if let Some(seg) = p.path.segments.last() {
            if seg.ident == "Option" {
                if let syn::PathArguments::AngleBracketed(a) = &seg.arguments {
                    if let Some(syn::GenericArgument::Type(inner)) = a.args.first() {
                        return peel_refs(inner.clone());
                    }
                }
            }
        }
    }
    ty
}

/// Lift’s `a` for rustc: `String` → `str`. Other inners pass through.
fn peel_one_generic(ty: Type, name: &str) -> Type {
    let ty = peel_refs(ty);
    if let Type::Path(p) = &ty {
        if let Some(seg) = p.path.segments.last() {
            if seg.ident == name {
                if let syn::PathArguments::AngleBracketed(a) = &seg.arguments {
                    if let Some(syn::GenericArgument::Type(inner)) = a.args.first() {
                        return peel_refs(inner.clone());
                    }
                }
            }
        }
    }
    ty
}

fn lift_schema_ty(ty: &Type) -> Type {
    let ty = peel_one_generic(ty.clone(), "Option");
    let ty = peel_one_generic(ty, "Vec");
    peel_one_generic(ty, "Box")
}

fn quote_nested(ty: &Type) -> proc_macro2::TokenStream {
    let inner = lift_schema_ty(ty);
    let inv = quote! { ::conformance_lang::nested(#inner::conformance_schema()) };
    if is_option_ty(ty) {
        quote! { ::conformance_lang::or_absent(#inv) }
    } else {
        inv
    }
}

enum LocalTy {
    SchemaStruct,
    OtherStruct,
    Enum,
}

fn is_leaf_ident(name: &str) -> bool {
    matches!(
        name,
        "String"
            | "str"
            | "bool"
            | "char"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "f32"
            | "f64"
            | "HashMap"
            | "BTreeMap"
            | "HashSet"
            | "BTreeSet"
    )
}

fn should_nest(ty: &Type) -> bool {
    let inner = lift_schema_ty(ty);
    let Some(name) = type_last_ident(&inner) else {
        return false;
    };
    if is_leaf_ident(&name) {
        return false;
    }
    match lookup_local_ty(&name) {
        Some(LocalTy::SchemaStruct) => true,
        Some(LocalTy::OtherStruct | LocalTy::Enum) => false,
        None => true,
    }
}

fn lookup_local_ty(name: &str) -> Option<LocalTy> {
    if let Ok(path) = source_path() {
        if let Some(k) = classify_file(&path, name) {
            return Some(k);
        }
    }
    let root = crate_root()?;
    let src = root.join("src");
    let mut paths = Vec::new();
    let _ = collect_rs(&src, &mut paths);
    for p in paths {
        if let Some(k) = classify_file(&p, name) {
            return Some(k);
        }
    }
    None
}

fn classify_file(path: &Path, name: &str) -> Option<LocalTy> {
    let src = std::fs::read_to_string(path).ok()?;
    let file: syn::File = syn::parse_str(&src).ok()?;
    classify_items(&file.items, name)
}

fn classify_items(items: &[Item], name: &str) -> Option<LocalTy> {
    for item in items {
        match item {
            Item::Struct(s) if s.ident == name => {
                return Some(if has_derive_schema(&s.attrs) {
                    LocalTy::SchemaStruct
                } else {
                    LocalTy::OtherStruct
                });
            }
            Item::Enum(e) if e.ident == name => return Some(LocalTy::Enum),
            Item::Mod(m) => {
                if let Some((_, nested)) = &m.content {
                    if let Some(k) = classify_items(nested, name) {
                        return Some(k);
                    }
                }
            }
            _ => {}
        }
    }
    None
}

fn lift_refine_ty(ty: &Type) -> proc_macro2::TokenStream {
    let inner = lift_inner_ty(ty);
    if type_last_ident(&inner).as_deref() == Some("String") {
        quote! { str }
    } else {
        quote! { #inner }
    }
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

enum WhenSugar {
    Photo { pred: Predicate, then: Invariant },
    Rewrite { pred: Predicate, then: Invariant },
}

/// `rewrite` opens pre/write. Any other I is photo `when(P, I)` on the field.
fn parse_when_attr(attr: &Attribute, this_field: &str) -> syn::Result<WhenSugar> {
    let Meta::List(list) = &attr.meta else {
        return Err(syn::Error::new_spanned(
            attr,
            "expected #[when(P, rewrite I)] or #[when(P, I)]",
        ));
    };
    let field = this_field.to_string();
    let parser = |input: ParseStream| parse_when_inner(input, &field);
    parser.parse2(list.tokens.clone())
}

fn parse_when_inner(input: ParseStream, this_field: &str) -> syn::Result<WhenSugar> {
    let pred = parse_rewrite_pred(input, this_field)?;
    input.parse::<Token![,]>()?;
    if peek_ident(input, "then") {
        let _: Ident = input.parse()?;
    }
    let is_rewrite = peek_ident(input, "rewrite");
    if is_rewrite {
        let _: Ident = input.parse()?;
    }
    let then = parse_when_inv(input)?;
    if !input.is_empty() {
        return Err(input.error("unexpected tokens after when"));
    }
    if is_rewrite {
        Ok(WhenSugar::Rewrite { pred, then })
    } else {
        Ok(WhenSugar::Photo { pred, then })
    }
}

fn parse_when_inv(input: ParseStream) -> syn::Result<Invariant> {
    let first = parse_when_inv_atom(input)?;
    let mut parts = vec![first];
    while input.peek(Token![&&]) {
        input.parse::<Token![&&]>()?;
        parts.push(parse_when_inv_atom(input)?);
    }
    if parts.len() == 1 {
        Ok(parts.pop().unwrap())
    } else {
        Ok(Invariant::All(parts))
    }
}

fn parse_when_inv_atom(input: ParseStream) -> syn::Result<Invariant> {
    if input.peek(Ident) {
        let id: Ident = input.parse()?;
        if id == "None" || id == "absent" {
            return Ok(absent());
        }
        if id == "defined" {
            if input.peek(syn::token::Paren) {
                let _empty;
                syn::parenthesized!(_empty in input);
            }
            return Ok(defined());
        }
        if id == "one_of" {
            let content;
            syn::parenthesized!(content in input);
            let lits = parse_lit_strs(&content)?;
            if lits.is_empty() {
                return Err(syn::Error::new(id.span(), "expected one_of(\"…\", …)"));
            }
            let refs: Vec<&str> = lits.iter().map(|s| s.as_str()).collect();
            return Ok(one_of(&refs));
        }
        return Err(syn::Error::new(
            id.span(),
            "expected rewrite I, or one_of / defined / absent / None",
        ));
    }
    parse_rewrite_inv(input)
}

fn parse_rewrite_pred(input: ParseStream, this_field: &str) -> syn::Result<Predicate> {
    let mut parts = vec![parse_rewrite_term(input, this_field)?];
    while input.peek(Token![&&]) {
        input.parse::<Token![&&]>()?;
        parts.push(parse_rewrite_term(input, this_field)?);
    }
    if parts.len() == 1 {
        Ok(parts.pop().unwrap())
    } else {
        Ok(Predicate::And(parts))
    }
}

fn parse_rewrite_term(input: ParseStream, this_field: &str) -> syn::Result<Predicate> {
    if input.peek(syn::token::Paren) {
        let content;
        syn::parenthesized!(content in input);
        return parse_rewrite_pred(&content, this_field);
    }
    if input.peek(LitStr) {
        let first: LitStr = input.parse()?;
        let mut lits = vec![first.value()];
        while peek_ident(input, "or") {
            let _: Ident = input.parse()?;
            let next: LitStr = input.parse()?;
            lits.push(next.value());
        }
        if lits.len() == 1 {
            return Ok(pred_eq(this_field, &lits[0]));
        }
        let refs: Vec<&str> = lits.iter().map(|s| s.as_str()).collect();
        return Ok(pred_in(this_field, &refs));
    }
    let field: Ident = input.parse()?;
    let field = field.to_string();
    if input.peek(Token![!=]) {
        input.parse::<Token![!=]>()?;
        let lit: LitStr = input.parse()?;
        return Ok(pred_not(pred_eq(&field, &lit.value())));
    }
    if input.peek(Token![==]) {
        input.parse::<Token![==]>()?;
        let lit: LitStr = input.parse()?;
        return Ok(pred_eq(&field, &lit.value()));
    }
    if input.peek(Token![=]) {
        input.parse::<Token![=]>()?;
        if input.peek(syn::token::Bracket) {
            let content;
            syn::bracketed!(content in input);
            let lits = parse_lit_strs(&content)?;
            let refs: Vec<&str> = lits.iter().map(|s| s.as_str()).collect();
            return Ok(pred_in(&field, &refs));
        }
        let lit: LitStr = input.parse()?;
        return Ok(pred_eq(&field, &lit.value()));
    }
    Err(syn::Error::new(
        input.span(),
        "expected field != \"…\" / == / = or \"09\" or \"10\"",
    ))
}

fn parse_rewrite_inv(input: ParseStream) -> syn::Result<Invariant> {
    if input.peek(Ident) {
        let id: Ident = input.parse()?;
        if id == "None" || id == "absent" {
            return Ok(absent());
        }
        return Err(syn::Error::new(
            id.span(),
            "expected rewrite \"…\" / None / absent",
        ));
    }
    if input.peek(syn::token::Bracket) {
        let content;
        syn::bracketed!(content in input);
        let lits = parse_lit_strs(&content)?;
        let refs: Vec<&str> = lits.iter().map(|s| s.as_str()).collect();
        return Ok(one_of(&refs));
    }
    let lit: LitStr = input.parse()?;
    Ok(one_of(&[&lit.value()]))
}

fn parse_lit_strs(input: ParseStream) -> syn::Result<Vec<String>> {
    let lits = Punctuated::<LitStr, Token![,]>::parse_terminated(input)?;
    Ok(lits.into_iter().map(|s| s.value()).collect())
}

fn peek_ident(input: ParseStream, name: &str) -> bool {
    let fork = input.fork();
    matches!(fork.parse::<Ident>(), Ok(id) if id == name)
}

fn quote_pred(pred: &Predicate) -> proc_macro2::TokenStream {
    match pred {
        Predicate::Eq { field, lit } => quote! {
            ::conformance_lang::Predicate::Eq {
                field: #field.into(),
                lit: #lit.into(),
            }
        },
        Predicate::In { field, lits } => quote! {
            ::conformance_lang::Predicate::In {
                field: #field.into(),
                lits: vec![#(#lits.into()),*],
            }
        },
        Predicate::Defined { field } => quote! {
            ::conformance_lang::pred_defined(#field)
        },
        Predicate::And(xs) => {
            let inner = xs.iter().map(quote_pred);
            quote! { ::conformance_lang::Predicate::And(vec![#(#inner),*]) }
        }
        Predicate::Or(xs) => {
            let inner = xs.iter().map(quote_pred);
            quote! { ::conformance_lang::Predicate::Or(vec![#(#inner),*]) }
        }
        Predicate::Not(inner) => {
            let inner = quote_pred(inner);
            quote! { ::conformance_lang::pred_not(#inner) }
        }
    }
}

fn quote_inv(inv: &Invariant) -> proc_macro2::TokenStream {
    match inv {
        Invariant::OneOf(lits) => quote! { ::conformance_lang::one_of(&[#(#lits),*]) },
        Invariant::Defined => quote! { ::conformance_lang::defined() },
        Invariant::Absent => quote! { ::conformance_lang::absent() },
        Invariant::Unique => quote! { ::conformance_lang::unique() },
        Invariant::Nested(_) => quote! {
            ::core::compile_error!("nested schema cannot be quoted from expand IR — lift walks it at the Schema")
        },
        Invariant::Shape(form) => {
            let form = match form {
                Form::Scalar => quote! { Scalar },
                Form::Array => quote! { Array },
            };
            quote! { ::conformance_lang::shape(::conformance_lang::Form::#form) }
        }
        Invariant::Refine(_) => quote! {
            ::core::compile_error!(
                "domain refine cannot be quoted from expand IR — use #[refine(path)] or #[refine(|x|)]"
            )
        },
        Invariant::At(n) => quote! { ::conformance_lang::at(#n) },
        Invariant::Width(n) => quote! { ::conformance_lang::width(#n) },
        Invariant::When { pred, then } => {
            let pred = quote_pred(pred);
            let then = quote_inv(then);
            quote! { ::conformance_lang::when(#pred, #then) }
        }
        Invariant::All(xs) => {
            let inner = xs.iter().map(quote_inv);
            quote! { ::conformance_lang::Invariant::All(vec![#(#inner),*]) }
        }
        Invariant::Any(xs) => {
            let inner = xs.iter().map(quote_inv);
            quote! { ::conformance_lang::Invariant::Any(vec![#(#inner),*]) }
        }
    }
}
