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
| Eval | Score one `ValueCtx` against the Schema (`eval_schema`) |

Stdlib: `one_of`, `defined`, `when`, `at`, `width`, `shape`, `pred_eq`, `pred_in`.

Observe = fold of `M` (`ValueCtx → ValueCtx`). Unfold is one backend of that fold.

## Quick run

```bash
cd ~/Desktop/projects/conformance_tiny_ir
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

`#[required_if(version = "2.3.1", cancel = ["09", "10"])]` is `And` + `In`.

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

Hook it to a function with a generated `#[test]` (`cargo test`, not rustc/Clippy):

```toml
conformance = { package = "conformance_macros", path = "../conformance_tiny_ir/conformance_macros" }
conformance_lang = { path = "../conformance_tiny_ir/conformance_lang" }
```

```rust
#[conformance::transition]
fn for_kind(mut m: Msg) -> Msg { /* … */ }

#[conformance::transition]
impl Msg {
    fn for_protocol(mut self) -> Self { /* … */ }
}
```

Not on an impl **method** — rustc only runs `#[test]` on free functions. Same file as callees so Unfold can follow them.

## Verify ≠ match attrs

Observed facts (literals, absent, wire pos/len) are evaluated against Invariants. Fail if `observed` breaks the Invariant — not if attribute text mismatches.

## Crates

- `conformance_lang` — IR, Observe, Unfold, `eval_schema`
- `conformance_macros` — `#[derive(Schema)]`, `#[transition]`
