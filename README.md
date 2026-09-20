# conformance_tiny_ir

Annotate a Rust struct. **`cargo build` fails if your code constructs an illegal value.** The same rules run at **runtime** on a filled-in instance.

## Add it

```toml
conformance_lang = { git = "https://github.com/dipanshuhappy/conformance_tiny_ir", package = "conformance_lang" }
conformance_macros = { git = "https://github.com/dipanshuhappy/conformance_tiny_ir", package = "conformance_macros" }
```

Pin `rev` if you want a freeze.

## Example

`kind` is `"hi"` or `"bye"`. If `kind` is `"hi"`, `name` must be set.

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

| Value | Result |
|---|---|
| `kind = "hi"`, `name = Some("Ada")` | ok |
| `kind = "bye"`, `name = None` | ok |
| `kind = "hi"`, `name = None` | **error** |
| `kind = "hi"` and `name` never written | not an error — only known fields are checked |

### Compile time

`#[derive(Schema)]` walks `src/` when the crate compiles. It follows field assigns, `if` / `match` arms, and helpers in the same file. Any path that **definitely** leaves `kind = "hi"` and `name = None` is a `compile_error!`.

```rust
fn greet(mut m: Msg) -> Msg {
    m.kind = "hi".into();
    m.name = None;          // cargo build fails: name is required when kind is hi
    m
}

fn for_kind(mut m: Msg) -> Msg {
    if m.kind == "hi" {
        m.name = Some("Ada".into());
        return m;           // this arm is ok
    }
    m.name = None;          // else: kind is not hi — ok
    m
}

fn via_helper(m: Msg) -> Msg {
    bad(m)                  // still fails: bad() writes hi + None
}

fn bad(mut m: Msg) -> Msg {
    m.kind = "hi".into();
    m.name = None;
    m
}
```

Mute one function (tests / fixtures) with a reason. Other functions that call it are still checked.

```rust
#[conformance_macros::except("fixture for the illegal case")]
fn compute_hi(mut m: Msg) -> Msg {
    m.kind = "hi".into();
    m.name = None;
    m
}
```

### Runtime

Same rules, on values you already have (JSON, a test, a live struct you copied into a context):

```rust
use conformance_lang::{eval_schema, ValueCtx};

let schema = Msg::conformance_schema();

let bad = ValueCtx::default().lit("kind", "hi").absent("name");
assert!(!eval_schema(&schema, &bad, None).ok());

let good = ValueCtx::default().lit("kind", "hi").lit("name", "Ada");
assert!(eval_schema(&schema, &good, None).ok());
```

`.lit` is a known string. `.absent` is an explicit `None`. A field you omit is skipped, not treated as `None`.

## More on the same struct

Allowed strings: `#[enum_("hi", "bye")]`.  
`Option<T>` may be missing unless `#[required_if(...)]` says otherwise.  
A custom string check is a closure you own:

```rust
#[refine(|s| s.chars().count() == 2 && s.chars().all(|c| c.is_ascii_digit()))]
eci: Option<String>,
```

Or a named function: `fn eci() -> Refine<str> { refine(|s| …) }` then `#[refine(eci)]`. Nested structs that also `#[derive(Schema)]` are checked field-by-field (`report.code`). Put `#[leaf]` on a field to skip that.

```bash
cargo build                 # illegal construction → compile_error
cargo test -p conformance_lang
```
