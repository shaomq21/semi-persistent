# IntervalZ

Unbounded integer intervals, in [src/ibig.rs](../src/ibig.rs) and [src/interval_z.rs](../src/interval_z.rs). The shape is the shared domain interface in [domain-traits.md](domain-traits.md).

```text
Lo        = NegInf | Fin(IBig)
Hi        = Fin(IBig) | PosInf
IntervalZ = { lo: Lo, hi: Hi }     private fields, lo <= hi when both are finite
values    = every integer z with lo <= z <= hi
empty     = BotOr::Bot, outside the type
```

There is no `empty` flag. A well-formed value is nonempty, and each set has one representation.

## Integers (`IBig`)

`IBig` is a trusted wrapper around `num_bigint::BigInt`. Its spec view is mathematical `int`. The trusted items, including `sub`, `mul`, `div_euclid`, and `div_trunc`, are listed in the ledger in [domain-traits.md](domain-traits.md). `div_euclid` is Verus `int` `/` (nonnegative remainder). `div_trunc` divides toward zero. This module is not verified code.

## Domain

`Domain` provides `top` (`[-∞, +∞]`), `leq`, `join`, `meet -> BotOr`, and Cousot `widen`. An unstable bound jumps to `±∞`, so the chain `[0,0]`, `[0,1]`, `[0,2]`, … reaches `+∞` in one step. `meet` of disjoint intervals is `Bot`. Contracts are soundness against `gamma`, with explicit `#[trigger]`s. `lemma_canonical` says equal concretizations are equal values.

## Arithmetic

`Arith<Euclid>` and `Arith<Trunc>` share `add`, `sub`, and `neg`, which are exact on the endpoints. Addition of an infinite bound is that infinity. `Mul<Euclid>` and `Mul<Trunc>` take the four endpoint products. `0 * ±∞ = 0`. Comparing those products borrows them and copies only the smaller or the larger one.

## Division

`DivRem<Euclid>::div` and `DivRem<Trunc>::div` return `(BotOr<IntervalZ>, DivZero)`.

| `DivZero` | When                                       | Quotient           |
| --------- | ------------------------------------------ | ------------------ |
| `Always`  | the divisor is `{0}`                       | `Bot`              |
| `Never`   | the divisor excludes 0                     | endpoint quotients |
| `Maybe`   | the divisor contains 0 and another integer | split, then join   |

Both directions are proved: `Never` if and only if 0 is absent, and `Always` if and only if every concrete divisor is 0. `div_nonzero` is private and requires that the divisor exclude 0.

A divisor that contains 0 is split into `(-∞, -1]` and `[1, +∞)`. Each side is divided separately and the results are joined. A wholly negative divisor is negated, divided, and the quotient is negated.

Endpoint quotients when the divisor is positive:

- a negative lower bound is divided by the smaller positive endpoint;
- a nonnegative lower bound is divided by the larger one, and `+∞` contributes `0`;
- a nonnegative upper bound is divided by the smaller positive endpoint;
- a negative upper bound is divided by the larger one. Euclidean `+∞` contributes `-1`. Truncation contributes `0`.

So `[-8, -1] / [1, +∞)` is `[-∞, -1]` for Euclidean division, not an interval that contains `0`. Truncation of `-7 / 2` is `-3`; the Euclidean quotient is `-4`.

When the quotient of two finite intervals is a single integer, the remainder is `x - q * y` at the four corners, so a singleton division is exact: Euclidean `10 % 3 = 1` and `-7 % 2 = 1`, while truncation gives `-7 % 2 = -1`. Otherwise the remainder is the magnitude bound: Euclidean `0 <= r < |y|`, and truncation keeps the sign of the dividend. `DivZero` is the same flag as for the quotient.

`narrow` replaces an infinite endpoint of the first interval by the same endpoint of the second, and returns `Bot` if the bounds cross. Every concrete value that lies in both intervals survives, and every surviving value was already in the first interval. `refine(fact, budget)` is one `meet` when `budget > 0`, and it leaves the interval unchanged when `budget == 0`. The result contains a concrete value exactly when that value satisfies both intervals and fuel was spent. `meet_chain` repeats that step. Its soundness proof says a value in the start value and in every fact is still present, including when fuel runs out before the facts do.

## Review checklist

Each item states the review requirement, then the implementation.

**1. Target type.** Use the #116 shape: `IntervalZ` with `Lo { NegInf, Fin(IBig) }` and `Hi { Fin(IBig), PosInf }`, private fields, and `lo <= hi` when both ends are finite. Prove the representation canonical, and implement `Domain` (Cousot widening) plus `Arith<Euclid>` and `Arith<Trunc>`.

The struct stores only private `lo` and `hi`. `wf` requires `lo.view() <= hi.view()` when both ends are `Fin`. `lemma_canonical` shows that two well-formed intervals with the same integer set have the same bounds. Both `Arith` impls provide add, sub, and neg. `widen` is Cousot: a looser lower bound becomes `NegInf`, and a looser upper bound becomes `PosInf`.

**2. Replace the division placeholders.** `DivRem<Euclid>` and `DivRem<Trunc>` were top placeholders with an exact `DivZero`. Put the precise division in their place. A `[0, 0]` divisor returns `Bot`, matching `DivZero::Always`.

`div` goes through `div_general`. Both ends `Fin(0)` returns `(Bot, Always)`. A divisor that excludes 0 uses the private `div_nonzero`. A divisor that contains 0 and some other integer is split into `(-∞, -1]` and `[1, +∞)`, each side is divided, and the results are joined, with flag `Maybe`.

**3. Remove the empty flag.** `IntervalZ { empty, lo, hi }` is well-formed for any bounds when `empty = true`, so there are infinitely many bottoms. `PartialEq` then disagrees with `eq_abs`, and a fixpoint `==` check misses stabilization. Bottom lives outside the domain: every well-formed value denotes a nonempty set, and emptiness is `lattice::BotOr::Bot`.

The struct stores only `lo` and `hi`. `meet` takes the tighter bounds and returns `BotOr::Bot` when they cross.

**4. Euclidean division, plus truncation.** Port the Euclidean division that splits the divisor at 0 into `DivRem<Euclid>`, and add truncated division as `DivRem<Trunc>`. C and Rust truncate toward zero: `-7 / 2 = -3`, while Euclidean division gives `-4`. The alarm is `DivZero`.

`DivRem<Euclid>::div` uses Verus `x / y` (nonnegative remainder). `DivRem<Trunc>::div` uses `tdiv`. `IBig::div_euclid` starts from truncating `BigInt` division and adjusts the quotient when the remainder is negative. `IBig::div_trunc` is `BigInt` `/`. The test `[-7, -7] / [2, 2]` checks Euclidean `-4` and truncated `-3`.

**5. `narrow` returns `BotOr`.** `narrow` replaces only the infinite endpoints of the receiver: `NegInf` takes the other interval's lower bound, and `PosInf` takes its upper bound. Finite bounds that cross return `Bot`. The proof says every integer in both intervals stays in the result, and every integer in the result was already in the first interval. `[-∞, +∞)` narrowed by `[1, 2]` is `[1, 2]`. `[0, +∞)` narrowed by `[-5, -1]` is `Bot`.

**6. Widening.** The old `widen` was `join` (`widen_spec == join_spec`), so `[0, 0], [0, 1], [0, 2], …` never stabilizes. Use Cousot widening, which #116 already provides. Thresholds are optional.

Cousot widening is in place, and thresholds are not added. A looser lower bound becomes `NegInf`; a looser upper bound becomes `PosInf`. `[0, 0] ∇ [0, 1]` contains `0` and `100`, and excludes `-1`.

**7. `IBig` is trusted; do not add a second wrapper.** `ibig.rs` is an external struct, `external_body` methods, and broadcast axioms. It should not be described as verified. Use #116's `IBig` and add the needed operations (`sub`, `mul`, `div`) to the ledger in `doc/domain-traits.md` §7.

The code uses that `IBig`. After the existing `add` and `neg`, it adds `sub`, `mul`, `div_euclid`, and `div_trunc`, all `external_body`. The ledger lists them and states that `div_euclid`'s spec is Verus `int` `/`. The docs treat the module as a trust boundary.

**8. Soundness for `refine` and `meet_chain`.** Those specs stated only precision (`r ⊑ self`). State soundness against `gamma`.

`refine(fact, 0)` keeps the original interval. `budget > 0` meets once: an integer is in the result exactly when it is in both intervals. `meet_chain` repeats that step. Fuel `0` stops at the current value. A meet that leaves the concrete set unchanged spends no fuel; a strict meet spends `1`. `meet_chain_sound` proves that an integer in the start value and in every fact is still present at the end, including when fuel runs out first.

**9. Triggers, and crossed bounds.** Replace `#![auto]` with explicit triggers. Require well-formed bounds instead of mapping a crossed pair to top.

`interval_z.rs` uses `#[trigger]` and has no `#![auto]`. `new` returns `None` when a finite lower bound is greater than a finite upper bound.

**10. The alarm's "exactly when" had one direction.** Both directions are proved. `classify` ensures `Never` if and only if `0` is absent, and `Always` if and only if every concrete divisor is `0`.

**11. Finite negative divided by `±∞`.** A finite negative divided by `±∞` produced `0`. The limit is `∓1`.

When the divisor's lower bound is `>= 1`, the dividend's upper bound is negative, and the divisor's upper bound is `PosInf`, the Euclidean quotient's upper bound is `Fin(-1)` and the truncated one is `Fin(0)`. A wholly negative divisor heading toward `−∞` is negated into a positive interval (`−∞` becomes `+∞`), divided, and the quotient is negated, so `-1` becomes `+1`. The test `[-8, -1] / [1, +∞)` checks that the Euclidean result contains `-1` and excludes `0`.

**12. `div_one` must exclude 0.** `div_one` was public and had no `!d.has(0)` precondition, so a caller could get a result that misses quotients.

The public `div_one` is removed. The private `div_nonzero` requires `!d.gamma(0)`. Only divisors that exclude 0 enter it. A divisor that contains 0 is split first, and each side excludes 0.

**13. Multiplication, and `min` / `max` should return references.** `mul` was 20–39× slower than an `i64` interval because `min` and `max` cloned their arguments. Returning references fixes most of it.

`Mul<Euclid>` and `Mul<Trunc>` both call `mul_int`. When both intervals contain 0 in their interior, the four endpoint products go through `min_ibig` and `max_ibig`, which return references and copy only the chosen endpoint. `0 * ±∞ = 0`, so `{0}` times any interval is `{0}`. The test `[-2, 3] * [-4, 5]` contains `-12` and `15`, and excludes `-13` and `16`.
