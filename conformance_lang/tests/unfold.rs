use conformance_lang::{eval_schema, eval_unfold, msg_toy_schema, unfold, AbsVal, FindingKind};

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
    use conformance_lang::eval_unfold_named;
    let schema = msg_toy_schema();
    assert!(eval_unfold_named(&schema, src, "for_kind").unwrap().ok());
    assert!(!eval_unfold_named(&schema, src, "poison").unwrap().ok());
}
