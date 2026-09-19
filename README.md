# conformance_tiny_ir

Schema = legal region of state. Observe fills a photo. Eval scores it.

**Schema · Field · Locator · Invariant · Predicate · Compose · Eval**

This repo is the language. Ampere / recon hang their domains on it.

## The example

```rust
use conformance_macros::Schema;

#[derive(Schema)]
struct Msg {
    #[enum_("hi", "bye")]
    kind: String,
    #[required_if(kind = "hi")]
    name: Option<String>,
}
```

That is one region: `kind ∈ {hi, bye}`; `kind = hi ⇒ name` defined.

```text
kind = "hi", name absent  →  Fail (defined)
kind = "bye", name absent →  Pass
kind = "hi"               →  Undecidable (name unobserved, not Absent)
```

`#[enum_]` is `one_of`. On `Option`, sugar is `|| None`. The checker never sees the attrs — only the Schema.

## Detected anywhere

The illegal tuple is the **ending photo**, not `Msg { kind: "hi", name: None }`. Same Fail if you build it with assigns, a helper, or an `if` arm.

```rust
fn compute_hi(mut m: Msg) -> Msg {
    m.kind = "hi".into();
    m.name = None;           // Fail: hi ⇒ name defined
    m
}

fn for_kind(mut m: Msg) -> Msg {
    if m.kind == "hi" {
        m.name = None;       // Fail on this arm
        return m;
    }
    helper(m)                // else: kind is not hi — name None is fine
}

fn helper(mut m: Msg) -> Msg {
    m.name = None;
    m
}

fn sneak(mut m: Msg) -> Msg {
    helper(do_m(m))          // follow: do_m writes hi + None → Fail here too
}

fn do_m(mut m: Msg) -> Msg {
    m.kind = "hi".into();
    m.name = None;
    m
}
```

`#[derive(Schema)]` Unfolds `{crate}/src` at expand time. A Known-illegal photo is `compile_error!` — `cargo build` is the check. Path-split: do not union `if` arms. Follow enters callees (same file, depth 8). `#[except("why")]` mutes **that fn as a site**; follow from other sites still enters it.

Hand photo (tests / live JSON) is the same Eval:

```rust
eval_schema(&Msg::conformance_schema(),
    &ValueCtx::default().lit("kind", "hi").absent("name"),
    None)
```

Unknown / missing keys are Undecidable, not Fail.

## Complex domains live in the consumer

The kernel does not grow `uuid` / `eci` arms. A refine is `a → Score`. Lift picks `a` from the slot (`String`, each of a list, `Absent | T`). Ampere (or this test crate) owns the filter:

```rust
use conformance_lang::{refine, Refine};

fn eci() -> Refine<str> {
    refine(|s| s.chars().count() == 2 && s.chars().all(|c| c.is_ascii_digit()))
}

fn uuid() -> Refine<str> {
    refine(|s| s.len() == 36 /* … */)
}

#[derive(Schema)]
struct RReq {
    #[enum_("2.0.0", "2.1.0", "2.2.0", "2.3.1")]
    message_version: String,

    #[refine(eci)]
    eci: Option<String>,

    #[refine(uuid)]
    three_ds_server_trans_id: String,

    /// This slot only — same refine, no named fn.
    #[refine(|s| s.chars().count() == 2)]
    interaction_counter: String,

    /// Photo: leftover 09/10 illegal on 2.2. Rewrite: the edit at `=`.
    #[enum_("01", "02", "03", "04", "05", "06", "07", "08", "09", "10")]
    #[when(message_version != "2.3.1" && "09" or "10", rewrite "06")]
    #[when(message_version != "2.3.1", one_of("01", "03", "04", "05", "06", "07", "08"))]
    challenge_cancel: Option<String>,
}
```

`#[refine(eci)]` is `let r: Refine<str> = eci()` then erase to `Invariant` on the Schema. Option peels to `or_absent`. Expand-time `compile_error!` only scores **data** (`one_of`, `defined`, …). A domain closure is runtime Eval.

A Schema struct is walked by default (`report.code`). `#[leaf]` opts out. Sums are not nested Schemas.

```rust
#[derive(Schema)]
struct Erro {
    #[enum_("01", "02")]
    code: String,
}

#[derive(Schema)]
struct Wrap {
    report: Option<Erro>,   // walks Erro; Absent skips
}
```

## Use from GitHub

```toml
conformance_lang = { git = "https://github.com/dipanshuhappy/conformance_tiny_ir", package = "conformance_lang" }
conformance_macros = { git = "https://github.com/dipanshuhappy/conformance_tiny_ir", package = "conformance_macros" }
```

Pin `rev` when you want a freeze. You need `conformance_lang` if you call `eval_schema` / `refine` yourself; `#[derive(Schema)]` needs the macros crate.

```bash
cargo build          # Fail → compile_error
cargo test -p conformance_lang
```

## Crates

- `conformance_lang` — IR, Observe, Unfold, Eval
- `conformance_macros` — `#[derive(Schema)]`, `#[transition]`, `#[except]`

Law: [DESIGN.md](DESIGN.md).
