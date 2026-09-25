use conformance_lang::{
    all, eval_schema, matches as matches_text, msg_toy_schema, nested, observe, one_of, or_absent,
    pred_eq, pred_in, refine, shape, unique, when, AbsVal, Fact, Field, FindingKind, Form,
    Invariant, Locator, Predicate, Refine, Schema, ValueCtx,
};

/// Domain crate (Ampere would own these). Typed `Refine<str>`; Schema erases.
fn chars(n: usize) -> Refine<str> {
    refine(move |s| s.chars().count() == n)
}

fn eci() -> Refine<str> {
    refine(|s| s.chars().count() == 2 && s.chars().all(|c| c.is_ascii_digit()))
}

fn uuid() -> Refine<str> {
    refine(|s| {
        let b = s.as_bytes();
        b.len() == 36
            && b[8] == b'-'
            && b[13] == b'-'
            && b[18] == b'-'
            && b[23] == b'-'
            && b.iter().enumerate().all(|(i, c)| match i {
                8 | 13 | 18 | 23 => true,
                _ => c.is_ascii_hexdigit(),
            })
    })
}

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
        rewrites: vec![],
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
        rewrites: vec![],
    };
    let ok = ValueCtx::default().with_wire("amount", 37, 11);
    assert!(eval_schema(&schema, &ok, None).ok());

    let bad = ValueCtx::default().with_wire("amount", 37, 12);
    let report = eval_schema(&schema, &bad, None);
    assert!(!report.ok());
    assert!(report.fails().any(|f| f.message.contains("width")));
}

#[test]
fn sequential_wire_fragments_fold_to_absolute_geometry() {
    use conformance_lang::{at, eval_schema, width, Field, Locator, Schema, WireFragment};

    let schema = Schema {
        name: "E1".into(),
        width: Some(32),
        fields: vec![
            Field {
                name: "card_number".into(),
                locator: Locator::Wire("card_number".into()),
                invariants: vec![at(1), width(19)],
                wire: None,
            },
            Field {
                name: "transaction_code".into(),
                locator: Locator::Wire("transaction_code".into()),
                invariants: vec![at(20), width(2)],
                wire: None,
            },
            Field {
                name: "source_number".into(),
                locator: Locator::Wire("source_number".into()),
                invariants: vec![at(22), width(11)],
                wire: None,
            },
        ],
        rewrites: vec![],
    };

    let trace = WireFragment::emit("card_number", 19)
        .concat(WireFragment::emit("transaction_code", 2))
        .concat(WireFragment::emit("source_number", 11));
    assert_eq!(trace.extent(), 32);
    assert!(eval_schema(&schema, &trace.observe(1), None).ok());

    let illegal = WireFragment::emit("transaction_code", 2)
        .concat(WireFragment::emit("card_number", 19))
        .concat(WireFragment::emit("source_number", 11));
    let report = eval_schema(&schema, &illegal.observe(1), None);
    assert!(!report.ok());
    assert!(report.fails().any(|finding| {
        finding.message.contains("Invariant at(20) failed")
            && finding.message.contains("transaction_code")
    }));
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
        rewrites: vec![],
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
        rewrites: vec![],
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
        rewrites: vec![],
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
        rewrites: vec![],
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

#[allow(dead_code)]
#[derive(conformance_macros::Schema)]
struct OptEnum {
    #[enum_("Y", "N")]
    trust: Option<String>,
}

#[test]
fn enum_on_option_allows_none() {
    let schema = OptEnum::conformance_schema();
    assert!(eval_schema(&schema, &ValueCtx::default().absent("trust"), None).ok());
    assert!(eval_schema(&schema, &ValueCtx::default().lit("trust", "Y"), None).ok());
    assert!(
        eval_schema(&schema, &ValueCtx::default().lit("trust", "ZZ"), None)
            .fails()
            .any(|f| f.field == "trust")
    );
}

#[allow(dead_code)]
#[derive(conformance_macros::Schema)]
struct LeftoverCancel {
    version: String,
    #[when(version != "2.3.1", one_of("01", "03", "06"))]
    cancel: String,
}

#[test]
fn when_one_of_is_photo_not_rewrite() {
    let schema = LeftoverCancel::conformance_schema();
    assert!(
        schema.rewrites.is_empty(),
        "one_of after when is photo, not rewrite: {:?}",
        schema.rewrites.len()
    );
    let leftover = ValueCtx::default()
        .lit("version", "2.2.0")
        .lit("cancel", "09");
    assert!(
        eval_schema(&schema, &leftover, None)
            .fails()
            .any(|f| f.field == "cancel"),
        "{:?}",
        eval_schema(&schema, &leftover, None).findings
    );
    let ok = ValueCtx::default()
        .lit("version", "2.2.0")
        .lit("cancel", "06");
    assert!(eval_schema(&schema, &ok, None).ok());
    let v231 = ValueCtx::default()
        .lit("version", "2.3.1")
        .lit("cancel", "09");
    assert!(eval_schema(&schema, &v231, None).ok());
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

fn slot(name: &str, inv: impl Into<Invariant>) -> Schema {
    Schema {
        name: "T".into(),
        width: None,
        fields: vec![Field {
            name: name.into(),
            locator: Locator::Path(name.into()),
            invariants: vec![inv.into()],
            wire: None,
        }],
        rewrites: vec![],
    }
}

#[test]
fn chars_is_refine_string_on_known() {
    let schema = slot("n", chars(2));
    assert!(eval_schema(&schema, &ValueCtx::default().lit("n", "03"), None).ok());
    assert!(
        eval_schema(&schema, &ValueCtx::default().lit("n", "3"), None)
            .fails()
            .any(|f| f.field == "n")
    );
    let unobs = eval_schema(&schema, &ValueCtx::default(), None);
    assert!(unobs.ok());
    assert!(unobs
        .findings
        .iter()
        .any(|f| f.kind == FindingKind::Undecidable && f.field == "n"));
}

#[test]
fn domain_eci_is_refine_closure() {
    let schema = slot("n", eci());
    assert!(eval_schema(&schema, &ValueCtx::default().lit("n", "03"), None).ok());
    assert!(
        eval_schema(&schema, &ValueCtx::default().lit("n", "0a"), None)
            .fails()
            .any(|f| f.field == "n")
    );
}

#[test]
fn domain_uuid_is_refine_closure() {
    let schema = slot("id", uuid());
    let ok = "550e8400-e29b-41d4-a716-446655440000";
    assert!(eval_schema(&schema, &ValueCtx::default().lit("id", ok), None).ok());
    assert!(
        eval_schema(&schema, &ValueCtx::default().lit("id", "not-a-uuid"), None)
            .fails()
            .any(|f| f.field == "id")
    );
    let short36ish = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    assert_eq!(short36ish.chars().count(), 36);
    assert!(
        eval_schema(&schema, &ValueCtx::default().lit("id", short36ish), None)
            .fails()
            .any(|f| f.field == "id")
    );
}

#[test]
fn matches_is_full_string_refine_sugar() {
    let schema = slot("eci", matches_text("[0-9]{2}").expect("valid regex"));
    assert!(eval_schema(&schema, &ValueCtx::default().lit("eci", "05"), None).ok());
    assert!(
        eval_schema(&schema, &ValueCtx::default().lit("eci", "x05"), None)
            .fails()
            .any(|f| f.field == "eci")
    );

    let unknown = eval_schema(&schema, &ValueCtx::default().unknown("eci"), None);
    assert!(unknown.ok(), "Unknown is not known-illegal");
    assert!(unknown
        .findings
        .iter()
        .any(|f| f.kind == FindingKind::Undecidable && f.field == "eci"));

    let unobserved = eval_schema(&schema, &ValueCtx::default(), None);
    assert!(unobserved.ok(), "unobserved is not absent or known-illegal");
    assert!(unobserved
        .findings
        .iter()
        .any(|f| f.kind == FindingKind::Undecidable && f.field == "eci"));
}

#[test]
fn matches_rejects_an_invalid_pattern_when_schema_is_built() {
    assert!(matches_text("[").is_err());
}

#[test]
fn all_ands_two_string_refines() {
    let schema = slot("eci", all(chars(2), eci()));
    assert!(eval_schema(&schema, &ValueCtx::default().lit("eci", "05"), None).ok());
    assert!(
        eval_schema(&schema, &ValueCtx::default().lit("eci", "0a"), None)
            .fails()
            .any(|f| f.field == "eci")
    );
}

#[allow(dead_code)]
#[derive(conformance_macros::Schema)]
struct SugarIds {
    #[refine(chars_2)]
    counter: String,
    #[refine(uuid)]
    server_id: String,
    #[refine(eci)]
    eci: String,
}

fn chars_2() -> Refine<str> {
    chars(2)
}

#[test]
fn sugar_refine_path() {
    let schema = SugarIds::conformance_schema();
    let ok = ValueCtx::default()
        .lit("counter", "03")
        .lit("server_id", "550e8400-e29b-41d4-a716-446655440000")
        .lit("eci", "05");
    assert!(
        eval_schema(&schema, &ok, None).ok(),
        "{:?}",
        eval_schema(&schema, &ok, None).findings
    );
    let bad = ValueCtx::default()
        .lit("counter", "3")
        .lit("server_id", "550e8400-e29b-41d4-a716-446655440000")
        .lit("eci", "05");
    assert!(eval_schema(&schema, &bad, None)
        .fails()
        .any(|f| f.field == "counter"));
}

#[allow(dead_code)]
#[derive(conformance_macros::Schema)]
struct InlineEci {
    #[refine(|s| s.chars().count() == 2 && s.chars().all(|c| c.is_ascii_digit()))]
    eci: Option<String>,
}

#[test]
fn sugar_refine_inline_closure() {
    let schema = InlineEci::conformance_schema();
    assert!(eval_schema(&schema, &ValueCtx::default().lit("eci", "05"), None).ok());
    assert!(
        eval_schema(&schema, &ValueCtx::default().lit("eci", "0a"), None)
            .fails()
            .any(|f| f.field == "eci")
    );
    assert!(eval_schema(&schema, &ValueCtx::default().absent("eci"), None).ok());
}

#[allow(dead_code)]
#[derive(conformance_macros::Schema)]
struct WhenEci {
    version: String,
    #[when(version != "2.3.1", one_of("05", "06") && defined)]
    eci: Option<String>,
}

#[test]
fn when_refines_with_and() {
    let schema = WhenEci::conformance_schema();
    let ok = ValueCtx::default().lit("version", "2.2.0").lit("eci", "05");
    assert!(eval_schema(&schema, &ok, None).ok());
    let bad = ValueCtx::default().lit("version", "2.2.0").lit("eci", "0a");
    assert!(eval_schema(&schema, &bad, None)
        .fails()
        .any(|f| f.field == "eci"));
    let skip = ValueCtx::default().lit("version", "2.3.1").lit("eci", "0a");
    assert!(eval_schema(&schema, &skip, None).ok());
    let none = ValueCtx::default().lit("version", "2.2.0").absent("eci");
    assert!(
        eval_schema(&schema, &none, None).ok(),
        "Option + when I is ∨ Absent: {:?}",
        eval_schema(&schema, &none, None).findings
    );
}

#[test]
fn one_of_on_single_and_each_of_multiple() {
    let schema = slot("method", one_of(&["01", "02", "09"]));
    assert!(eval_schema(&schema, &ValueCtx::default().lit("method", "01"), None).ok());
    let list_ok = ValueCtx::default().array_of(
        "method",
        vec![AbsVal::known("01"), AbsVal::known("09")],
    );
    assert!(
        eval_schema(&schema, &list_ok, None).ok(),
        "{:?}",
        eval_schema(&schema, &list_ok, None).findings
    );
    let list_bad = ValueCtx::default().array_of(
        "method",
        vec![AbsVal::known("01"), AbsVal::known("77")],
    );
    assert!(eval_schema(&schema, &list_bad, None)
        .fails()
        .any(|f| f.field == "method"));
    let list_unk = ValueCtx::default().array_of(
        "method",
        vec![AbsVal::known("01"), AbsVal::Unknown],
    );
    let u = eval_schema(&schema, &list_unk, None);
    assert!(u.ok());
    assert!(u
        .findings
        .iter()
        .any(|f| f.kind == FindingKind::Undecidable && f.field == "method"));
}

#[test]
fn unique_fails_duplicate_list() {
    let schema = slot("method", unique());
    assert!(eval_schema(&schema, &ValueCtx::default().lit("method", "01"), None).ok());
    let dups = ValueCtx::default().array_of(
        "method",
        vec![AbsVal::known("01"), AbsVal::known("01")],
    );
    assert!(eval_schema(&schema, &dups, None)
        .fails()
        .any(|f| f.field == "method"));
    let ok = ValueCtx::default().array_of(
        "method",
        vec![AbsVal::known("01"), AbsVal::known("02")],
    );
    assert!(eval_schema(&schema, &ok, None).ok());
}

fn erro_schema() -> Schema {
    Schema {
        name: "Erro".into(),
        width: None,
        fields: vec![Field {
            name: "code".into(),
            locator: Locator::Path("code".into()),
            invariants: vec![one_of(&["01", "02"])],
            wire: None,
        }],
        rewrites: vec![],
    }
}

fn wrap_schema() -> Schema {
    Schema {
        name: "R".into(),
        width: None,
        fields: vec![Field {
            name: "report".into(),
            locator: Locator::Path("report".into()),
            invariants: vec![or_absent(nested(erro_schema()))],
            wire: None,
        }],
        rewrites: vec![],
    }
}

#[test]
fn nested_record_walks_inner_one_of() {
    let schema = wrap_schema();
    let ok = ValueCtx::default().record(
        "report",
        [("code".into(), AbsVal::known("01"))],
    );
    assert!(eval_schema(&schema, &ok, None).ok());
    let bad = ValueCtx::default().record(
        "report",
        [("code".into(), AbsVal::known("99"))],
    );
    let report = eval_schema(&schema, &bad, None);
    assert!(
        report.fails().any(|f| f.field == "report.code"),
        "{:?}",
        report.findings
    );
    assert!(eval_schema(&schema, &ValueCtx::default().absent("report"), None).ok());
}

#[test]
fn nested_array_walks_each_record() {
    let schema = Schema {
        name: "R".into(),
        width: None,
        fields: vec![Field {
            name: "exts".into(),
            locator: Locator::Path("exts".into()),
            invariants: vec![nested(erro_schema())],
            wire: None,
        }],
        rewrites: vec![],
    };
    let ok = ValueCtx::default().array_of(
        "exts",
        vec![
            AbsVal::Record([("code".into(), AbsVal::known("01"))].into()),
            AbsVal::Record([("code".into(), AbsVal::known("02"))].into()),
        ],
    );
    assert!(eval_schema(&schema, &ok, None).ok());
    let bad = ValueCtx::default().array_of(
        "exts",
        vec![AbsVal::Record([("code".into(), AbsVal::known("99"))].into())],
    );
    assert!(
        eval_schema(&schema, &bad, None)
            .fails()
            .any(|f| f.field.starts_with("exts")),
        "{:?}",
        eval_schema(&schema, &bad, None).findings
    );
}

#[allow(dead_code)]
#[derive(conformance_macros::Schema)]
struct Erro {
    #[enum_("01", "02")]
    code: String,
}

#[allow(dead_code)]
#[derive(conformance_macros::Schema)]
struct Wrap {
    report: Option<Erro>,
}

#[allow(dead_code)]
enum AuthSum {
    Single(String),
    Multiple(Vec<String>),
}

#[allow(dead_code)]
#[derive(conformance_macros::Schema)]
struct WithAuth {
    method: Option<AuthSum>,
}

#[allow(dead_code)]
#[derive(conformance_macros::Schema)]
struct LeafWrap {
    #[leaf]
    report: Option<Erro>,
}

#[test]
fn sugar_nested_option_struct() {
    let schema = Wrap::conformance_schema();
    let ok = ValueCtx::default().record(
        "report",
        [("code".into(), AbsVal::known("01"))],
    );
    assert!(eval_schema(&schema, &ok, None).ok());
    let bad = ValueCtx::default().record(
        "report",
        [("code".into(), AbsVal::known("99"))],
    );
    assert!(eval_schema(&schema, &bad, None)
        .fails()
        .any(|f| f.field.contains("code")));
}

#[test]
fn sum_is_not_nested_schema() {
    let schema = WithAuth::conformance_schema();
    assert!(
        schema.fields[0]
            .invariants
            .iter()
            .all(|i| !matches!(i, Invariant::Nested(_))),
        "{:?}",
        schema.fields[0].invariants
    );
}

#[test]
fn leaf_opts_out_of_nested_walk() {
    let schema = LeafWrap::conformance_schema();
    assert!(
        schema.fields[0]
            .invariants
            .iter()
            .all(|i| !matches!(i, Invariant::Nested(_))),
        "{:?}",
        schema.fields[0].invariants
    );
    let bad = ValueCtx::default().record(
        "report",
        [("code".into(), AbsVal::known("99"))],
    );
    assert!(eval_schema(&schema, &bad, None).ok());
}
