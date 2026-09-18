use conformance_lang::{
    eval_schema, msg_toy_schema, observe, pred_eq, pred_in, shape, when, AbsVal, Fact, Field,
    FindingKind, Form, Locator, Predicate, Schema, ValueCtx,
};

#[test]
fn hand_ctx_hi_without_name_fails() {
    let schema = msg_toy_schema();
    let ctx = ValueCtx::default().lit("kind", "hi").absent("name");
    let report = eval_schema(&schema, &ctx, Some("hand"));
    assert!(!report.ok());
    let fail = report.fails().next().expect("fail");
    assert_eq!(fail.field, "name");
    assert!(fail.message.contains("defined"), "{}", fail.message);
}

#[test]
fn hand_ctx_hi_with_name_passes() {
    let schema = msg_toy_schema();
    let ctx = ValueCtx::default().lit("kind", "hi").lit("name", "Ada");
    let report = eval_schema(&schema, &ctx, None);
    assert!(report.ok(), "{:?}", report.findings);
}

#[test]
fn hand_ctx_bye_without_name_passes() {
    let schema = msg_toy_schema();
    let ctx = ValueCtx::default().lit("kind", "bye").absent("name");
    let report = eval_schema(&schema, &ctx, None);
    assert!(report.ok(), "{:?}", report.findings);
}

#[test]
fn one_of_kind_with_absent_name_fails_hi_arm() {
    let schema = msg_toy_schema();
    let ctx = ValueCtx::default()
        .one_of("kind", ["hi", "bye"])
        .absent("name");
    let report = eval_schema(&schema, &ctx, None);
    assert!(!report.ok());
    assert!(report.fails().any(|f| f.field == "name"));
}

#[test]
fn unknown_kind_is_undecidable_not_pass() {
    let schema = msg_toy_schema();
    let ctx = ValueCtx::default().unknown("kind").absent("name");
    let report = eval_schema(&schema, &ctx, None);
    assert!(report.ok(), "no Fail");
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
fn unobserved_name_on_hi_is_undecidable_not_fail() {
    let schema = msg_toy_schema();
    let ctx = ValueCtx::default().lit("kind", "hi");
    let report = eval_schema(&schema, &ctx, None);
    assert!(report.ok(), "unobserved ≠ absent: {:?}", report.findings);
    assert!(report
        .findings
        .iter()
        .any(|f| f.kind == FindingKind::Undecidable && f.field == "name"));
}

/// Transition then check the resulting state — not the fn's syntax.
fn toy_for_protocol(kind: &str, name: Option<&str>) -> ValueCtx {
    let ctx = ValueCtx::default().lit("kind", kind);
    match name {
        Some(n) => ctx.lit("name", n),
        None => ctx.absent("name"),
    }
}

#[test]
fn transition_hi_without_name_fails() {
    let schema = msg_toy_schema();
    let ctx = toy_for_protocol("hi", None);
    let report = eval_schema(&schema, &ctx, Some("toy_for_protocol"));
    assert!(!report.ok());
    assert!(report.fails().any(|f| f.field == "name"));
}

#[test]
fn transition_hi_with_name_passes() {
    let schema = msg_toy_schema();
    let ctx = toy_for_protocol("hi", Some("Ada"));
    assert!(eval_schema(&schema, &ctx, None).ok());
}

#[test]
fn observe_fold_uses_locator_to_read() {
    let schema = Schema {
        name: "E1".into(),
        width: Some(90),
        fields: vec![Field {
            name: "amount".into(),
            locator: Locator::Wire("tracs_amount".into()),
            invariants: vec![conformance_lang::at(37), conformance_lang::width(11)],
            wire: None,
        }],
    };
    let ctx = observe(&schema, |f| match f.locator.key() {
        "tracs_amount" => Fact::Wire { pos: 37, len: 11 },
        _ => Fact::Unknown,
    });
    assert!(eval_schema(&schema, &ctx, None).ok());

    let bad = observe(&schema, |f| match f.locator.key() {
        "tracs_amount" => Fact::Wire { pos: 37, len: 12 },
        _ => Fact::Unknown,
    });
    let report = eval_schema(&schema, &bad, None);
    assert!(!report.ok());
    assert!(report.fails().any(|f| f.message.contains("width")));
}

#[test]
fn geometry_at_width() {
    use conformance_lang::{at, width, Field, Locator, Schema};

    let schema = Schema {
        name: "E1".into(),
        width: Some(90),
        fields: vec![Field {
            name: "amount".into(),
            locator: Locator::Wire("tracs_amount".into()),
            invariants: vec![at(37), width(11)],
            wire: None,
        }],
    };
    let ok = ValueCtx::default().with_wire("amount", 37, 11);
    assert!(eval_schema(&schema, &ok, None).ok());

    let bad = ValueCtx::default().with_wire("amount", 37, 12);
    let report = eval_schema(&schema, &bad, None);
    assert!(!report.ok());
    assert!(report.fails().any(|f| f.message.contains("width")));
}

#[test]
fn tiling_overlap_fails() {
    use conformance_lang::{at, width};

    let schema = Schema {
        name: "E1".into(),
        width: Some(10),
        fields: vec![
            Field {
                name: "a".into(),
                locator: Locator::Wire("a".into()),
                invariants: vec![at(1), width(5)],
                wire: None,
            },
            Field {
                name: "b".into(),
                locator: Locator::Wire("b".into()),
                invariants: vec![at(3), width(5)],
                wire: None,
            },
        ],
    };
    let ctx = observe(&schema, |f| match f.name.as_str() {
        "a" => Fact::Wire { pos: 1, len: 5 },
        "b" => Fact::Wire { pos: 3, len: 5 },
        _ => Fact::Unknown,
    });
    let report = eval_schema(&schema, &ctx, None);
    assert!(!report.ok());
    assert!(
        report.fails().any(|f| f.message.contains("overlaps")),
        "{:?}",
        report.findings
    );
}

#[test]
fn tiling_holes_are_padding() {
    use conformance_lang::{at, width};

    let schema = Schema {
        name: "E1".into(),
        width: Some(5),
        fields: vec![
            Field {
                name: "a".into(),
                locator: Locator::Wire("a".into()),
                invariants: vec![at(1), width(2)],
                wire: None,
            },
            Field {
                name: "b".into(),
                locator: Locator::Wire("b".into()),
                invariants: vec![at(3), width(2)],
                wire: None,
            },
        ],
    };
    let ctx = observe(&schema, |f| match f.name.as_str() {
        "a" => Fact::Wire { pos: 1, len: 2 },
        "b" => Fact::Wire { pos: 3, len: 2 },
        _ => Fact::Unknown,
    });
    assert!(eval_schema(&schema, &ctx, None).ok());
}

#[test]
fn tiling_one_span_does_not_demand_the_rest() {
    use conformance_lang::{at, width};

    let schema = Schema {
        name: "E1".into(),
        width: Some(90),
        fields: vec![
            Field {
                name: "amount".into(),
                locator: Locator::Wire("tracs_amount".into()),
                invariants: vec![at(37), width(11)],
                wire: None,
            },
            Field {
                name: "pan".into(),
                locator: Locator::Wire("tracs_pan".into()),
                invariants: vec![],
                wire: None,
            },
        ],
    };
    let ctx = ValueCtx::default().with_wire("amount", 37, 11);
    assert!(eval_schema(&schema, &ctx, None).ok());
}

#[test]
fn pred_in_and_shape() {
    let schema = Schema {
        name: "R".into(),
        width: None,
        fields: vec![
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
                    pred_in("cancel", &["09", "10"]),
                    conformance_lang::defined(),
                )],
                wire: None,
            },
            Field {
                name: "method".into(),
                locator: Locator::Path("method".into()),
                invariants: vec![shape(Form::Array)],
                wire: None,
            },
        ],
    };
    let fail = ValueCtx::default()
        .lit("cancel", "09")
        .absent("report")
        .array("method");
    assert!(!eval_schema(&schema, &fail, None).ok());

    let pass = ValueCtx::default()
        .lit("cancel", "07")
        .absent("report")
        .array("method");
    assert!(
        eval_schema(&schema, &pass, None).ok(),
        "{:?}",
        eval_schema(&schema, &pass, None).findings
    );

    let bad_shape = ValueCtx::default()
        .lit("cancel", "07")
        .absent("report")
        .lit("method", "01");
    assert!(eval_schema(&schema, &bad_shape, None)
        .fails()
        .any(|f| f.field == "method"));
}

#[test]
fn else_of_hi_excludes_so_when_skips() {
    let schema = msg_toy_schema();
    let ctx = ValueCtx::default().exclude("kind", "hi").absent("name");
    let report = eval_schema(&schema, &ctx, None);
    assert!(report.ok(), "{:?}", report.findings);
}

#[test]
fn sugar_derive_matches_hand_schema() {
    use conformance_macros::Schema;

    #[allow(dead_code)]
    #[derive(Schema)]
    struct Msg {
        #[enum_("hi", "bye")]
        kind: String,
        #[required_if(kind = "hi")]
        name: Option<String>,
    }

    let from_sugar = Msg::conformance_schema();
    let hand = msg_toy_schema();
    assert_eq!(from_sugar.name, hand.name);
    assert_eq!(from_sugar.fields.len(), hand.fields.len());

    let ctx = ValueCtx::default().lit("kind", "hi").absent("name");
    let a = eval_schema(&from_sugar, &ctx, None);
    let b = eval_schema(&hand, &ctx, None);
    assert_eq!(a.ok(), b.ok());
    assert!(!a.ok());
}

#[test]
fn sugar_required_if_and_in() {
    use conformance_macros::Schema;

    #[allow(dead_code)]
    #[derive(Schema)]
    struct R {
        version: String,
        cancel: String,
        #[required_if(version = "2.3.1", cancel = ["09", "10"])]
        report: Option<String>,
        #[shape(array)]
        method: Vec<String>,
    }

    let schema = R::conformance_schema();
    let fail = ValueCtx::default()
        .lit("version", "2.3.1")
        .lit("cancel", "09")
        .absent("report")
        .array("method");
    assert!(!eval_schema(&schema, &fail, None).ok());

    let skip = ValueCtx::default()
        .lit("version", "2.2.0")
        .lit("cancel", "09")
        .absent("report")
        .array("method");
    assert!(
        eval_schema(&schema, &skip, None).ok(),
        "{:?}",
        eval_schema(&schema, &skip, None).findings
    );
}

#[test]
fn absval_known_helper() {
    assert_eq!(AbsVal::known("hi"), AbsVal::Known("hi".into()));
    let _ = Predicate::Eq {
        field: "kind".into(),
        lit: "hi".into(),
    };
    let _ = pred_eq("kind", "hi");
}
