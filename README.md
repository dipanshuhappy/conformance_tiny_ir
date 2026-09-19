# conformance_tiny_ir

Tiny conformance engine: **Schema · Field · Invariant · Predicate · Compose · Eval**.

Schema = **legal region of state**. Observe fills a `ValueCtx`. Eval scores it. No AST hunt for `Msg { … }` or `fn -> Msg`.

## Primitives

| Name | Role |
|------|------|
| Schema | Legal states of a type |
| Field | Slot + locator |
| Invariant | `(state, field) → Pass \| Fail` |
| Predicate | `state → Bool` (gates an invariant) |
| Compose | `when` / `all` / `any` (on `Invariant`) |
| Eval | Score one photo (`eval_schema`). `rewrite` is the only thing that opens pre/write (`eval_rewrite`) |

Stdlib: `one_of`, `defined`, `when`, `at`, `width`, `shape`, `refine`, `all`, `pred_eq`, `pred_in`, `rewrite`. Domain: `fn eci() -> Refine<str> { refine(|s| …) }` + `#[refine(eci)]`, or `#[refine(|s| …)]` on one slot. Erase at Schema.

Observe = fold of `M` (`ValueCtx → ValueCtx`). Unfold is one backend of that fold.

## Quick run

```bash
cd ~/Desktop/projects/conformance_tiny_ir
cargo build          # Schema / transition Fail → compile_error
cargo test -p conformance_lang
```

## Toy (desugared IR)

```text
Schema Msg
  Field kind ⊢ Invariant oneOf(["hi","bye"])
  Field name ⊢ when(Predicate(kind=="hi"), Invariant defined)
```

Illegal **state** (however you built it):

```text
kind = "hi", name absent  →  Fail: defined
```

```rust
eval_schema(&schema, &ValueCtx::default().lit("kind", "hi").absent("name"), None)
```

Unobserved is not Absent: `.lit("kind", "hi")` with no name fact is **Undecidable**, not Fail.

## Toy (sugar)

```rust
use conformance_macros::Schema;

#[derive(Schema)]
struct Msg {
    #[enum_("hi", "bye")]
    kind: String,
    #[required_if(kind = "hi")]
    name: Option<String>,
}

// Msg::conformance_schema() → same IR
```

`#[enum_]` is `one_of`. On `Option`, sugar is `|| None` (`or_absent`). Required fields stay pure `one_of`.

First real schema (RReq). `required_if` is the 2.3.1 **photo**. `when` + `rewrite` is the pre-2.3.1 **edit**:

```rust
#[derive(Schema)]
struct RReq {
    #[enum_("2.0.0", "2.1.0", "2.2.0", "2.3.1")]
    message_version: String,
    #[enum_("01", "02", "03", "04", "05", "06", "07", "08", "09", "10")]
    /// Pre-2.3.1 Table A.4: CReq/CRes error cancels 09/10 remap to 06.
    #[when(message_version != "2.3.1" && "09" or "10", rewrite "06")]
    challenge_cancel: Option<String>,
    #[required_if(message_version = "2.3.1", challenge_cancel = ["09", "10"])]
    #[when(message_version != "2.3.1", rewrite None)]
    challenge_error_reporting: Option<String>,
}
```

Bare `"09" or "10"` is this field. `&&` = And. `rewrite` opens pre/write. `#[when(P, one_of(...))]` (any I except `rewrite`) is the photo — leftover 09/10 on 2.2, not an edit.

`#[derive(Schema)]` Unfolds `src/` at expand time (`compile_error!` on Fail). Mute a fn with `#[except("why")]` (site only; follow still enters). `#[transition]` is optional extra on one fn/`impl`/method.

## Observe / Unfold

```rust
observe(&schema, |f| match f.locator.key() {
    "tracs_amount" => Fact::Wire { pos: 37, len: 11 },
    _ => Fact::Unknown,
})

eval_unfold(&schema, r#"
    fn for_kind(mut m: Msg) -> Msg {
        if m.kind == "hi" { m.name = None; return m; }
        m
    }
"#)
```

Unfold path-splits `if` / `matches!`, follows callees that rewrite the same value, and evals each arm. Layout JSON does not go through Unfold.

Hook it to a function; illegal tuples fail `cargo build`:

```toml
conformance = { package = "conformance_macros", path = "../conformance_tiny_ir/conformance_macros" }
conformance_lang = { path = "../conformance_tiny_ir/conformance_lang" }
```

```rust
#[conformance::transition]
fn for_kind(mut m: Msg) -> Msg { /* … */ }

#[conformance::except("fixture for the illegal tuple")]
fn compute_hi(mut m: Msg) -> Msg {
    m.kind = "hi".into();
    m.name = None;
    m
}

#[conformance::transition]
impl Msg {
    fn for_protocol(mut self) -> Self { /* … */ }
}
```

Same file as callees so Unfold can follow them.

## Verify ≠ match attrs

Observed facts (literals, absent, wire pos/len) are evaluated against Invariants. Fail if `observed` breaks the Invariant — not if attribute text mismatches.

## Crates

- `conformance_lang` — IR, Observe, Unfold, `eval_schema`
- `conformance_macros` — `#[derive(Schema)]`, `#[transition]`, `#[except]`
