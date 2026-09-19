# Design

Schema = **legal region of state**. Observe fills a `ValueCtx`. Eval scores it.

```text
source  --Observe-->  ValueCtx  --Eval(Schema, photo)-->  Pass | Fail | Undecidable
assign  --Observe-->  (pre, write)  --Eval(Rewrite, pre, write)-->  …   // only if `rewrite`
```

Not a `{ }` / `fn -> T` hunt. Not Lean. Not recon’s per-field phone book as the product.

---

## Law

**Schema · Field · Locator · Invariant · Predicate · Compose · Eval**

| | |
|---|---|
| Schema | Allowed tuples (`Msg`, a TRACS line, …) |
| Field + Locator | Coordinate; Path / Wire / Tag on the *message*, not the Rust name |
| Invariant | A **refine** on a slot (see below). Today’s arms are values of that type. |
| Predicate | Gates `when` (`kind == "hi"`, `cancel ∈ {09,10}`, And of those) |
| Eval | `eval_schema` — one photo ⊆ region. `eval_rewrite` — only when `rewrite` names a write: P on **pre**, I on **write** |

Sugar (`#[enum_]`, `#[required_if]`, `#[refine]`, `#[when]`, `#[leaf]`) only **writes** the Schema. Lift walks a Schema struct by default; `#[leaf]` opts out.

Toy: `kind ∈ {hi,bye}`; `kind=hi ⇒ name defined`. Illegal: hi + name **Absent**. Unobserved is not Absent.

---

## Refine

A refine is a **filter**, not a map and not a pipe.

```text
type Score      = Pass | Fail | Undecidable
type Refine a   = a → Score
refine, all     : Refine a → Refine a → Refine a     -- And
```

`a` is whatever **lift** said the slot is — not only `String`.

```text
lift(String)         →  Refine String
lift(Option<T>)      →  Refine (Absent | T)
lift(Vec<T>)         →  Refine [T]              -- each element: Refine T
lift(Single|Multiple)→  Refine (String | [T])
lift(struct S)       →  Refine (photo of S)
defined, absent      →  Refine AbsVal           -- present / missing
```

String values of that type (`one_of`, domain `eci` / `uuid`) are the common case. Tiny_ir does not grow an arm per name.

```text
one_of xs s           =  s ∈ xs                 -- Refine String (data)
refine (|x|)          =  check x                -- Refine a; lift picks a
uuid / eci            =  refine (|s|)           -- Ampere (or tests), not this crate
all                   =  And of two refines
Single                =  Refine (this ctor)     -- not a list
```

`s : String` only when the refine is `Refine String`. `apply` unwraps the photo **as `a`**:

```text
apply r (Known s)   = r s          -- Refine String
apply r Array(xs)   = each r       -- Refine [T] / Multiple; unique on Known children
apply r Absent      = …            -- Refine (Absent | T)
apply _ missing     = Undecidable
apply _ Unknown     = Undecidable
```

`#[enum_]` writes `one_of`. `#[refine(path)]` writes `path()`. `#[refine(|x|)]` is the same refine on this slot. A 2.2 auth `Single` is `Refine` of that constructor. Same inhabitant scored twice is `all`, not a pipe.

**Map / filter / fold:** the transition `f` is map (`σ → σ'`). Observe is fold (photo). Refine / `when` / Eval are filter. `rewrite` is a filter on **one write**, not a refine and not the map.

**Domain refines:** `fn eci() -> Refine<str>`. `#[refine(eci)]` is `let r: Refine<str> = eci()` (lift after Option peel) then **erase** to `Invariant` on the Schema. This slot only = `#[refine(|x|)]`, same type. Expand-time `compile_error!` only `apply`s **data** (`one_of`, `defined`, …). A domain check is runtime Eval.

Not in the kernel: `shape` as `#`, `#[len]` as UUID (wire), rustc `typeof` as *P*.

---

## Lift · dependence

A slot **is** a Schema. Rust type gives the default region (`lift`). `when(P, S)` narrows it. `P` reads the **same** photo (any name). Nested Schema = those names under a path. Not a second checker. `shape(scalar|array)` is how the photo is stored — not `#`.

```text
lift(String)                       = Single              -- one string
lift(Option<T>)                    = Absent ∨ lift(T)
lift(Vec<T>)                       = Multiple            -- list of lift(T)
lift(Single(T) | Multiple(Vec<T>)) = Single ∨ Multiple
lift(struct with Schema)           = that Schema
```

`challenge_cancel: Option<String>` → `Absent | Single` (never a list).  
`authentication_method` photo is **form + code set**, not the Rust sum: 2.2 = `shape(scalar) && one_of(2.2)`; 2.3.1 = `shape(array) && one_of(full)`. `P` is `message_version`, not rustc `typeof` and not `Single` vs `Multiple`. `take().map(for_protocol)` may stay Unknown; rewrite is the map; live / fingers fill the photo.

`#[enum_]` / `#[refine(path)]` / `#[refine(|x|)]` are `Refine a` on `Single` (and each of `Multiple`). Today `a` is String. `#[len]` is wire width, not a string refine.

```text
each path of f  →  σ'                 -- Unfold
walk Schema on σ'  →  Pass|Fail|…     -- Eval; when / nested = deeper walk
```

Rewrite stays the other clock (`P` on pre, `I` on the write). AReq is the same photo with `areq.*` names when that pair exists — not a field of `RReq`.

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

Last write wins: a later `.lit` / `.absent` / … on a field drops its `exclude`. That is the ending picture. Without `rewrite` there is no old/new — `when` / `required_if` see that one photo. `#[when(P, rewrite I)]` is what opens the pair: P on **pre**, I on the write, scored **at the `=`**.

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

**Driver (not a new camera):** `#[derive(Schema)]` Unfolds `{crate}/src` at expand time. Fail is `compile_error!` (`cargo build`). Every rewrite of that type is a site. `#[except("why")]` mutes **that fn as a site** (reason required). Follow from other sites still enters it. `#[transition]` is an extra, per-fn stapler.

**Path split:** don’t union ctxs across `if` arms. Eval each return. `else` of `kind=="hi"` **excludes** hi — `do_m` there is not the hi tuple.

**Field follow (law of `=`):** a write is Observe of the RHS at that field. Tuple follow stays `helper(self)` (callee is the Schema). Slot follow walks `take().map(|m| m.foo())`, binds params to Schema fields (`message_version` is `self.message_version`), and reuses match-split on those names (`"12" => "09"`). Same file, depth 8. Unknown if we cannot name the result.

---

## Two products, one algebra

**JSON messages:** Schema `when` (version, cancel, channel). Observe live and/or Unfold a transition. Proptest: generate → run → eval.

**Fixed-width records:** spec → Schema (`at`/`width` / domain). Layout JSON → Observe `.with_wire` → eval (+ tiling). Values = a **second** Observe.

The recon **plugin** is this algebra on tape. This repo is the language; `enforce_layout!` is a driver. See below.

---

## Recon plugin

`recon/src_crates/conformance_macros` + `conformance/networks/<net>/conformance.yaml` is not a second checker. It is **Schema · Observe · Eval** with two Observe backends the language does not ship yet (layout file, phone book) and a spec→Schema pipeline (PDFs → yaml).

```text
guide / yaml     →  Schema          -- generated; never hand-edit
tracs_layout.json →  Observe .with_wire
compute_field     →  Observe phone book (literals in helpers)
tracs.yaml        →  Observe constants
enforce_layout!   →  driver         -- cargo build; same job as #[derive(Schema)]
#[accepted]       →  #[except]      -- reason required; stale fails
```

| Plugin check | This algebra |
|---|---|
| Record set | Schema names (`VOL1`, `E1`, …) |
| Geometry | `Locator::Wire` + `at` / `width` vs layout Observe |
| Type class (N vs A) | Refine on the slot (pad rule is domain, not a new primitive) |
| Tiling | `schema.width`; overlap / past-end Fail; holes are padding |
| Coverage | spec field never written = **unobserved** (latent fill), not Absent-Fail |
| Tags / subrecords | `Locator::Tag` or nested Schema |
| Computed values | phone-book Observe → `one_of` |
| Configured values | Observe of yaml constants → `one_of` |
| Bitmap bits | `refine` on the packed photo |
| Scenario / combination | `when(P, I)` on the **same** photo (not one field’s enum) |
| Translation (token → wire) | `rewrite` — same clock as auth `12→09` |
| Decision oracle | `when` + accepted; human reading, not the document |
| Staleness / grounding | not Eval — the Schema’s *source* must still re-derive |

Green in recon means red is reachable (`mutate.py`). Same beauty: a check that cannot fail is not a check. Silence on the wire is not permission when the document enumerated the domain.

What the plugin has that this crate does not: spec generation, layout-file Observe, phone book, citations, latent vs error, mutate. What this crate has that the plugin does not: path-split Unfold, photo `when` + `rewrite`, default nested walk, JSON messages, `Refine a`. Port means **reuse the IR**, not copy `check.rs` check-ids.

---

## Now

1. **Observe API** — `Fact` + `observe` fold; locators seat the read.
2. **Unfold** — AST Observe: `self`/`m` rewrite, path split, field-follow, Unobserved ≠ Fail.
3. **Law in sugar** — `when(P, I)` photo; `when(P, rewrite I)` edit; tiling; `refine`; `unique`; list `one_of` each.
4. **Nested** — `AbsVal::Record`; lift walks a Schema struct (`report.code`). `#[leaf]` opts out. Sums / leaves / structs without Schema are not walked.

**Next (honest):** `#[when(P, shape(scalar\|array))]` (auth 2.2 one string / 2.3.1 list); `#[unique]`; AReq `eq_field` (joined photo); live Observe; layout-file reader; phone book; plugin speaking this IR. Not kernel: `shape` as `#`, rustc `typeof` as *P*, leftover-12 as `one_of("09")` (that is not the 2.2 set).

Not in scope unless we reopen: Lean / ∀ `for_protocol`, rewriting Ampere `map()`.

**One line:** Schema = region; Refine = `a → Score`; lift writes the starting refine from `τ`; `when` picks a slice; Rewrite = one write; Observe = fold; Eval = filter.
