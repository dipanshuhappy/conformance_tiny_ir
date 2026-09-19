use conformance_lang::{
    defined, eval_rewrite, eval_schema, eval_unfold, eval_unfold_named, msg_toy_schema, nested,
    one_of, or_absent, pred_eq, pred_in, pred_not, rewrite, unfold, when, AbsVal, Fact, Field,
    FindingKind, Locator, Predicate, Schema, ValueCtx,
};

fn reporting_schema() -> Schema {
    Schema {
        name: "R".into(),
        width: None,
        fields: vec![
            Field {
                name: "version".into(),
                locator: Locator::Path("version".into()),
                invariants: vec![],
                wire: None,
            },
            Field {
                name: "cancel".into(),
                locator: Locator::Path("cancel".into()),
                invariants: vec![],
                wire: None,
            },
            Field {
                name: "report".into(),
                locator: Locator::Path("report".into()),
                invariants: vec![when(
                    Predicate::And(vec![
                        pred_eq("version", "2.3.1"),
                        pred_in("cancel", &["09", "10"]),
                    ]),
                    defined(),
                )],
                wire: None,
            },
        ],
        rewrites: vec![],
    }
}

#[test]
fn hi_arm_name_none_fails() {
    let src = r#"
        fn for_kind(mut m: Msg) -> Msg {
            if m.kind == "hi" {
                m.name = None;
                return m;
            }
            m
        }
    "#;
    let report = eval_unfold(&msg_toy_schema(), src).unwrap();
    assert!(
        report.fails().any(|f| f.field == "name"),
        "{:?}",
        report.findings
    );
}

#[test]
fn return_m_on_hi_is_undecidable_not_fail() {
    let src = r#"
        fn for_kind(mut m: Msg) -> Msg {
            if m.kind == "hi" {
                return m;
            }
            m
        }
    "#;
    let report = eval_unfold(&msg_toy_schema(), src).unwrap();
    assert!(report.ok(), "no Fail: {:?}", report.findings);
    assert!(
        report
            .findings
            .iter()
            .any(|f| f.kind == FindingKind::Undecidable),
        "{:?}",
        report.findings
    );
}

#[test]
fn else_do_m_name_none_passes() {
    let src = r#"
        fn for_kind(mut m: Msg) -> Msg {
            if m.kind == "hi" {
                m.name = Some("Ada".into());
                return m;
            }
            do_m(m)
        }
        fn do_m(mut m: Msg) -> Msg {
            m.name = None;
            m
        }
    "#;
    let schema = msg_toy_schema();
    let obs = unfold(&schema, src).unwrap();
    let else_arm = obs
        .iter()
        .find(|o| o.label.contains("else"))
        .expect("else path");
    assert_eq!(else_arm.ctx.values.get("name"), Some(&AbsVal::Absent));
    assert!(else_arm
        .ctx
        .excluded
        .get("kind")
        .map(|s| s.contains("hi"))
        .unwrap_or(false));

    let report = eval_unfold(&schema, src).unwrap();
    assert!(
        report.ok(),
        "else of hi + name None must Pass: {:?}",
        report.findings
    );
}

#[test]
fn follow_do_m_that_writes_hi_and_none_fails() {
    let src = r#"
        fn for_kind(mut m: Msg) -> Msg {
            if m.kind == "hi" {
                m.name = Some("Ada".into());
                return m;
            }
            do_m(m)
        }
        fn do_m(mut m: Msg) -> Msg {
            m.kind = "hi".into();
            m.name = None;
            m
        }
    "#;
    let schema = msg_toy_schema();
    let obs = unfold(&schema, src).unwrap();
    let else_arm = obs
        .iter()
        .find(|o| o.label.contains("else"))
        .expect("else path");
    assert_eq!(
        else_arm.ctx.values.get("kind"),
        Some(&AbsVal::Known("hi".into()))
    );
    assert_eq!(else_arm.ctx.values.get("name"), Some(&AbsVal::Absent));
    let report = eval_schema(&schema, &else_arm.ctx, Some(&else_arm.label));
    assert!(
        report.fails().any(|f| f.field == "name"),
        "{:?}",
        report.findings
    );
}

#[test]
fn impl_self_rewrite() {
    let src = r#"
        impl Msg {
            fn for_kind(mut self) -> Self {
                if self.kind == "hi" {
                    self.name = None;
                    return self;
                }
                self
            }
        }
    "#;
    let report = eval_unfold(&msg_toy_schema(), src).unwrap();
    assert!(
        report.fails().any(|f| f.field == "name"),
        "{:?}",
        report.findings
    );
}

#[test]
fn matches_else_excludes() {
    let src = r#"
        fn for_kind(mut m: Msg) -> Msg {
            if matches!(m.kind.as_deref(), Some("hi") | Some("bye")) {
                m.name = Some("Ada".into());
                return m;
            }
            m
        }
    "#;
    let obs = unfold(&msg_toy_schema(), src).unwrap();
    let else_arm = obs.iter().find(|o| o.label.contains("else")).expect("else");
    assert!(else_arm.ctx.excluded.get("kind").unwrap().contains("hi"));
    assert!(else_arm.ctx.excluded.get("kind").unwrap().contains("bye"));
}

#[test]
fn eval_unfold_named_skips_other_fns() {
    let src = r#"
        fn for_kind(mut m: Msg) -> Msg {
            if m.kind == "hi" {
                m.name = Some("Ada".into());
                return m;
            }
            m
        }
        fn poison(mut m: Msg) -> Msg {
            m.kind = "hi".into();
            m.name = None;
            m
        }
    "#;
    let schema = msg_toy_schema();
    assert!(eval_unfold_named(&schema, src, "for_kind").unwrap().ok());
    assert!(!eval_unfold_named(&schema, src, "poison").unwrap().ok());
}

#[test]
fn except_mutes_site_not_follow() {
    let src = r#"
        #[except("poison is only reached from the else of hi")]
        fn poison(mut m: Msg) -> Msg {
            m.kind = "hi".into();
            m.name = None;
            m
        }
        fn ok(mut m: Msg) -> Msg {
            m.kind = "bye".into();
            m
        }
    "#;
    let schema = msg_toy_schema();
    let report = eval_unfold(&schema, src).unwrap();
    assert!(report.ok(), "{:?}", report.findings);
    assert_eq!(report.skipped.len(), 1);
    assert_eq!(report.skipped[0].site, "poison");
    assert!(report.skipped[0].reason.contains("else of hi"));

    let src2 = r#"
        #[except("not a site")]
        fn poison(mut m: Msg) -> Msg {
            m.kind = "hi".into();
            m.name = None;
            m
        }
        fn for_kind(mut m: Msg) -> Msg {
            if m.kind == "hi" {
                m.name = Some("Ada".into());
                return m;
            }
            poison(m)
        }
    "#;
    let report = eval_unfold(&schema, src2).unwrap();
    assert!(
        report.fails().any(|f| f.field == "name"),
        "follow still Fails: {:?}",
        report.findings
    );
    assert!(report.skipped.iter().any(|s| s.site == "poison"));
}

#[test]
fn eval_crate_walks_src() {
    use conformance_lang::eval_crate;
    let report = eval_crate(&msg_toy_schema(), env!("CARGO_MANIFEST_DIR")).unwrap();
    assert!(report.ok(), "{:?}", report.findings);
}

#[test]
fn from_new_format_lits_are_known() {
    let schema = msg_toy_schema();
    for src in [
        r#"fn f(mut m: Msg) -> Msg { m.kind = String::from("nope"); m }"#,
        r#"fn f(mut m: Msg) -> Msg { m.kind = String::new(); m }"#,
        r#"fn f(mut m: Msg) -> Msg { m.kind = format!("nope"); m }"#,
        r#"fn f(mut m: Msg) -> Msg { m.kind = format!("{}", "nope"); m }"#,
    ] {
        let report = eval_unfold(&schema, src).unwrap();
        assert!(
            report.fails().any(|f| f.field == "kind"),
            "expected oneOf Fail for {src}: {:?}",
            report.findings
        );
    }
}

#[test]
fn and_if_then_absent_fails() {
    let src = r#"
        fn f(mut r: R) -> R {
            if r.version == "2.3.1" && matches!(r.cancel.as_deref(), Some("09") | Some("10")) {
                r.report = None;
                return r;
            }
            r
        }
    "#;
    let report = eval_unfold(&reporting_schema(), src).unwrap();
    assert!(
        report.fails().any(|f| f.field == "report"),
        "&& then-arm must carry both conjuncts: {:?}",
        report.findings
    );
}

#[test]
fn nested_if_then_absent_fails() {
    let src = r#"
        fn f(mut r: R) -> R {
            if r.version == "2.3.1" {
                if matches!(r.cancel.as_deref(), Some("09") | Some("10")) {
                    r.report = None;
                    return r;
                }
            }
            r
        }
    "#;
    let report = eval_unfold(&reporting_schema(), src).unwrap();
    assert!(
        report.fails().any(|f| f.field == "report"),
        "nested if must accumulate: {:?}",
        report.findings
    );
}

#[test]
fn format_with_unknown_arg_stays_undecidable() {
    let src = r#"
        fn f(mut m: Msg) -> Msg {
            m.kind = format!("{}", x);
            m
        }
    "#;
    let report = eval_unfold(&msg_toy_schema(), src).unwrap();
    assert!(report.ok(), "Unknown ≠ Fail: {:?}", report.findings);
    assert!(
        report
            .findings
            .iter()
            .any(|f| f.kind == FindingKind::Undecidable && f.field == "kind"),
        "{:?}",
        report.findings
    );
}

fn remap_schema() -> Schema {
    Schema {
        name: "R".into(),
        width: None,
        fields: vec![
            Field {
                name: "version".into(),
                locator: Locator::Path("version".into()),
                invariants: vec![],
                wire: None,
            },
            Field {
                name: "cancel".into(),
                locator: Locator::Path("cancel".into()),
                invariants: vec![one_of(&["06", "07", "09", "10"])],
                wire: None,
            },
        ],
        rewrites: vec![rewrite(
            "cancel",
            Predicate::And(vec![
                pred_not(pred_eq("version", "2.3.1")),
                pred_in("cancel", &["09", "10"]),
            ]),
            one_of(&["06"]),
        )],
    }
}

#[allow(dead_code)]
#[derive(conformance_macros::Schema)]
struct Remap {
    version: String,
    #[enum_("06", "07", "09", "10")]
    #[when(version != "2.3.1" && "09" or "10", rewrite "06")]
    cancel: String,
}

#[test]
fn rewrite_eval_is_pre_and_write() {
    let schema = remap_schema();
    let rw = &schema.rewrites[0];
    let pre = ValueCtx::default()
        .exclude("version", "2.3.1")
        .one_of("cancel", ["09", "10"]);
    assert!(!eval_rewrite(&schema, rw, &pre, &Fact::Lit("07".into()), Some("remap")).ok());
    assert!(eval_rewrite(&schema, rw, &pre, &Fact::Lit("06".into()), Some("remap")).ok());
    let on_231 = ValueCtx::default()
        .lit("version", "2.3.1")
        .one_of("cancel", ["09", "10"]);
    assert!(eval_rewrite(&schema, rw, &on_231, &Fact::Lit("07".into()), None).ok());
}

#[test]
fn assign_07_after_09_on_22_fails_rewrite() {
    let src = r#"
        fn f(mut r: R) -> R {
            if r.version == "2.3.1" {
                return r;
            }
            if matches!(r.cancel.as_deref(), Some("09") | Some("10")) {
                r.cancel = "07".into();
                return r;
            }
            r
        }
    "#;
    let report = eval_unfold(&remap_schema(), src).unwrap();
    assert!(
        report.fails().any(|f| f.field == "cancel"),
        "Eval(rewrite, pre, write) at = : {:?}",
        report.findings
    );
}

#[test]
fn assign_06_after_09_on_22_passes_rewrite() {
    let src = r#"
        fn f(mut r: R) -> R {
            if r.version == "2.3.1" {
                return r;
            }
            if matches!(r.cancel.as_deref(), Some("09") | Some("10")) {
                r.cancel = "06".into();
                return r;
            }
            r
        }
    "#;
    let report = eval_unfold(&remap_schema(), src).unwrap();
    assert!(report.ok(), "{:?}", report.findings);
}

#[test]
fn derive_when_rewrite_matches_hand_ir() {
    let derived = Remap::conformance_schema();
    assert_eq!(derived.rewrites.len(), 1);
    let src = r#"
        fn f(mut r: Remap) -> Remap {
            if r.version == "2.3.1" {
                return r;
            }
            if matches!(r.cancel.as_deref(), Some("09") | Some("10")) {
                r.cancel = "07".into();
                return r;
            }
            r
        }
    "#;
    let report = eval_unfold(&derived, src).unwrap();
    assert!(
        report.fails().any(|f| f.field == "cancel"),
        "{:?}",
        report.findings
    );
}

#[allow(dead_code)]
#[derive(conformance_macros::Schema)]
struct Drop231 {
    version: String,
    #[when(version != "2.3.1", rewrite None)]
    report: Option<String>,
    #[when(version != "2.3.1" && "12", rewrite "09")]
    method: Option<String>,
}

#[test]
fn assign_some_report_on_22_fails_rewrite_none() {
    let src = r#"
        fn f(mut r: Drop231) -> Drop231 {
            if r.version == "2.3.1" {
                return r;
            }
            r.report = Some("x".into());
            r
        }
    "#;
    let report = eval_unfold(&Drop231::conformance_schema(), src).unwrap();
    assert!(
        report.fails().any(|f| f.field == "report"),
        "{:?}",
        report.findings
    );
}

#[test]
fn assign_none_report_on_22_passes_rewrite_none() {
    let src = r#"
        fn f(mut r: Drop231) -> Drop231 {
            if r.version == "2.3.1" {
                return r;
            }
            r.report = None;
            r
        }
    "#;
    let report = eval_unfold(&Drop231::conformance_schema(), src).unwrap();
    assert!(report.ok(), "{:?}", report.findings);
}

#[test]
fn assign_09_after_single_12_on_22_passes() {
    let src = r#"
        fn f(mut r: Drop231) -> Drop231 {
            if r.version == "2.3.1" {
                return r;
            }
            if matches!(r.method, Some(Single(ref s)) if s == "12") {
                r.method = Some(Single("09".into()));
                return r;
            }
            r
        }
    "#;
    let report = eval_unfold(&Drop231::conformance_schema(), src).unwrap();
    assert!(report.ok(), "{:?}", report.findings);
}

/// Table A.4 auth remap: slot follow + arg bind + match split.
fn auth_remap_schema() -> Schema {
    Schema {
        name: "RReq".into(),
        width: None,
        fields: vec![
            Field {
                name: "message_version".into(),
                locator: Locator::Path("message_version".into()),
                invariants: vec![],
                wire: None,
            },
            Field {
                name: "authentication_method".into(),
                locator: Locator::Path("authentication_method".into()),
                invariants: vec![],
                wire: None,
            },
            Field {
                name: "challenge_error_reporting".into(),
                locator: Locator::Path("challenge_error_reporting".into()),
                invariants: vec![],
                wire: None,
            },
        ],
        rewrites: vec![
            rewrite(
                "authentication_method",
                Predicate::And(vec![
                    pred_not(pred_eq("message_version", "2.3.1")),
                    pred_in("authentication_method", &["12"]),
                ]),
                one_of(&["09"]),
            ),
            rewrite(
                "authentication_method",
                Predicate::And(vec![
                    pred_not(pred_eq("message_version", "2.3.1")),
                    pred_in("authentication_method", &["14"]),
                ]),
                one_of(&["02"]),
            ),
            rewrite(
                "challenge_error_reporting",
                pred_not(pred_eq("message_version", "2.3.1")),
                conformance_lang::absent(),
            ),
        ],
    }
}

fn ampere_for_protocol_src(remap_12: &str) -> String {
    format!(
        r#"
        fn for_protocol(mut r: RReq) -> RReq {{
            if r.message_version == "2.3.1" {{
                return r;
            }}
            r.authentication_method = r
                .authentication_method
                .take()
                .map(|method| method.for_protocol(&r.message_version));
            r.challenge_error_reporting = None;
            r
        }}

        impl Auth {{
            fn for_protocol(self, message_version: &str) -> Self {{
                if message_version == "2.3.1" {{
                    return self;
                }}
                match self {{
                    Self::Single(method) => Self::Single(remap_2_2_0_authentication_method(&method)),
                    Self::Multiple(methods) => Self::Multiple(methods),
                }}
            }}
        }}

        fn remap_2_2_0_authentication_method(method: &str) -> String {{
            match method {{
                "12" => String::from("{remap_12}"),
                "14" => String::from("02"),
                other => other.to_owned(),
            }}
        }}
        "#
    )
}

#[test]
fn field_follow_map_for_protocol_passes() {
    let report = eval_unfold(&auth_remap_schema(), &ampere_for_protocol_src("09")).unwrap();
    assert!(
        report.ok(),
        "take().map(for_protocol) + None must be readable: {:?}",
        report.findings
    );
}

#[test]
fn field_follow_map_for_protocol_wrong_lit_fails() {
    let report = eval_unfold(&auth_remap_schema(), &ampere_for_protocol_src("07")).unwrap();
    assert!(
        report.fails().any(|f| f.field == "authentication_method"),
        "12 → 07 must Fail rewrite: {:?}",
        report.findings
    );
}

fn auth_codes_schema() -> Schema {
    Schema {
        name: "R".into(),
        width: None,
        fields: vec![Field {
            name: "method".into(),
            locator: Locator::Path("method".into()),
            invariants: vec![one_of(&["01", "02", "09"])],
            wire: None,
        }],
        rewrites: vec![],
    }
}

#[test]
fn unfold_single_is_one_string() {
    let src = r#"
        fn f(mut r: R) -> R {
            r.method = Single("01".into());
            r
        }
    "#;
    let report = eval_unfold(&auth_codes_schema(), src).unwrap();
    assert!(report.ok(), "{:?}", report.findings);
}

#[test]
fn unfold_multiple_one_of_each() {
    let ok = r#"
        fn f(mut r: R) -> R {
            r.method = Multiple(vec!["01".into(), "09".into()]);
            r
        }
    "#;
    let report = eval_unfold(&auth_codes_schema(), ok).unwrap();
    assert!(report.ok(), "{:?}", report.findings);

    let bad = r#"
        fn f(mut r: R) -> R {
            r.method = Multiple(vec!["01".into(), "77".into()]);
            r
        }
    "#;
    let report = eval_unfold(&auth_codes_schema(), bad).unwrap();
    assert!(
        report.fails().any(|f| f.field == "method"),
        "each of Multiple: {:?}",
        report.findings
    );
}

fn nested_report_schema() -> Schema {
    Schema {
        name: "R".into(),
        width: None,
        fields: vec![Field {
            name: "report".into(),
            locator: Locator::Path("report".into()),
            invariants: vec![or_absent(nested(Schema {
                name: "Erro".into(),
                width: None,
                fields: vec![Field {
                    name: "code".into(),
                    locator: Locator::Path("code".into()),
                    invariants: vec![one_of(&["01", "02"])],
                    wire: None,
                }],
                rewrites: vec![],
            }))],
            wire: None,
        }],
        rewrites: vec![],
    }
}

#[test]
fn unfold_nested_struct_literal() {
    let ok = r#"
        fn f(mut r: R) -> R {
            r.report = Erro { code: "01".into() };
            r
        }
    "#;
    let report = eval_unfold(&nested_report_schema(), ok).unwrap();
    assert!(report.ok(), "{:?}", report.findings);

    let bad = r#"
        fn f(mut r: R) -> R {
            r.report = Erro { code: "99".into() };
            r
        }
    "#;
    let report = eval_unfold(&nested_report_schema(), bad).unwrap();
    assert!(
        report.fails().any(|f| f.field.contains("code")),
        "nested walk: {:?}",
        report.findings
    );
}
