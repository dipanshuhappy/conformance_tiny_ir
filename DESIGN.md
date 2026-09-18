# Design

Schema = **legal region of state**. Observe fills a `ValueCtx`. Eval scores it.

```text
source  --Observe-->  ValueCtx  --Eval(Schema)-->  Pass | Fail | Undecidable
```

Not a `{ }` / `fn -> T` hunt. Not Lean. Not recon’s per-field phone book as the product.

---

## Law

**Schema · Field · Locator · Invariant · Predicate · Compose · Eval**

| | |
|---|---|
| Schema | Allowed tuples (`Msg`, a TRACS line, …) |
| Field + Locator | Coordinate; Path / Wire / Tag on the *message*, not the Rust name |
| Invariant | `one_of`, `defined`, `absent`, `shape`, `at`, `width`, `when` / `all` / `any` |
| Predicate | Gates `when` (`kind == "hi"`, `cancel ∈ {09,10}`, And of those) |
| Eval | `eval_schema` — whole tuple, not one field’s global enum |

Sugar (`#[enum_]`, `#[required_if]`, `#[shape]`) only **writes** the Schema.

Toy: `kind ∈ {hi,bye}`; `kind=hi ⇒ name defined`. Illegal: hi + name **Absent**. Unobserved is not Absent.

Tiling (when `schema.width` is set): overlap / past-end Fail. Holes are padding.

---

## Facts

| AbsVal | Meaning |
|---|---|
| Known | this string |
| Absent | we saw it missing |
| Unknown | we saw a write we cannot read |
| unobserved | no write — **not** Fail (`Undecidable`) |

Fail only when the tuple is **Known-illegal**. “Can be wrong” is runtime Observe / tests.

---

## Observe

Observe = **fold of updates** `M = ValueCtx → ValueCtx` (last write wins):

`.put(Fact)` · `.lit` · `.absent` · `.with_wire` · `.unknown` · `.exclude`

Last write wins: a later `.lit` / `.absent` / … on a field drops its `exclude`.

`observe(schema, read)` folds `schema.fields`. `read` uses **locators**; Eval still names Schema fields. `M` does not depend on Schema.

**Walk ⊂ Observe.** A walk is one way to emit `M`s. Layout JSON and live values are Observe with **no** AST walk.

| Backend | Source | Emits |
|---|---|---|
| Fingers | tests | `.lit` / `.absent` / `.with_wire` |
| Live | JSON / struct after a transition | values |
| Layout | `tracs_layout.json` | `.with_wire` — **not** a rewrite of spec YAML |
| Unfold | `self` / `m` rewrite + literal `if`s; follow callees with Known writes | values on **that arm** |
| Phone book | `compute_field` → helper | per-field literals (recon-style; optional) |

Unfold is **one** backend. It is **not** the camera. Layout is **not** Unfold.

`#[conformance::transition]` (on a free fn or an `impl` block) generates a `#[test]` that Unfolds **this file** and evals that fn. Not a rustc lint.

**Path split:** don’t union ctxs across `if` arms. Eval each return. `else` of `kind=="hi"` **excludes** hi — `do_m` there is not the hi tuple.

---

## Two products, one algebra

**JSON messages:** Schema `when` (version, cancel, channel). Observe live and/or Unfold a transition. Proptest: generate → run → eval.

**Fixed-width records:** spec → Schema (`at`/`width` / domain). Layout JSON → Observe `.with_wire` → eval (+ tiling). Values = a **second** Observe.

Theoretically recon’s *verifier* is this. This repo is not that verifier yet.

---

## Now

1. **Observe API** — `Fact` + `observe` fold; locators seat the read.
2. **Unfold** — AST Observe: `self`/`m` rewrite, path split, follow Known writes, Unobserved ≠ Fail.
3. **Richer law** — Predicate `And` / `In` in sugar; `shape`; tiling.

Not in scope unless we reopen: live/runtime Observe product, layout-file reader, property tests, phone book, a specific message type.

**One line:** Schema = law; Observe = `M`-fold from a source; Eval = tuple ⊆ Schema.
