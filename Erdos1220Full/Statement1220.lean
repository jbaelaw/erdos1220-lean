/-
# Erdős Problem #1220 — the first-order sentence `Erdos1220` (statement definitions)

This module is the analogue of `Erdos501/FOL/Statement.lean` for problem #1220.  It *reuses*
erdos501's language `L`, its theory `ZFC`, its formula combinators (`allF`, `exF`, `memF`, …) and its
standard structure `zfsetStructure` on Mathlib's `ZFSet` by import, so that the target
`¬ (ZFC ⊨ᵇ Erdos1220)` is stated for literally the same `ZFC` as `erdos501_not_provable`.

## The problem (erdosproblems.com/1220; Erdős–Hajnal 1971)

Let `λ` be a singular cardinal such that `λ` and `cf λ` are `ℵ₀`-inaccessible
(`μ ^ ℵ₀ < κ` for every cardinal `μ < κ`).  Is it true that `λ → (λ, ℵ₁)²`, i.e. every
`f : [λ]² → {0, 1}` has a set of cardinality `λ` homogeneous in colour `0` or a set of cardinality
`ℵ₁` homogeneous in colour `1`?

## Rendering conventions (all inside the language `∅, ω, 𝒫, ⋃, (·,·), ∈`)

* ordinals: erdos501's `ordF` (transitive, `∈`-trichotomous, `∈`-well-founded);
* `|A| ≤ |B|` (`leqF`): there is an injective function `f` from `A` to `B` (erdos501's `isFunF`:
  every `x ∈ A` has exactly one `f`-value, which lies in `B`; plus injectivity);
  `|A| = |B|` (`eqCardF`): both inequalities (Cantor–Schröder–Bernstein);
* cardinals (`cardinalF`): ordinals `κ` with `¬ |κ| ≤ |α|` for all `α ∈ κ` (initial ordinals);
  `μ < κ` for cardinals is `μ ∈ κ`;
* `ℵ₀ ≤ |λ|`: `|ω| ≤ |λ|`; `ω₁` (`omega1F`): the ordinal `w` with `¬ |w| ≤ |ω|` and `|a| ≤ |ω|`
  for all `a ∈ w`;
* cofinality (`cofF l d`): `d` is the cardinal equal to the least cardinality of a cofinal subset
  `S ⊆ λ` (`∀ β ∈ λ, ∃ γ ∈ S, β ≤ γ`); singular (`singularF`): `ℵ₀ ≤ |λ|` and some cofinal
  `S ⊆ λ` has `|S| < |λ|`;
* `μ ^ ℵ₀ < κ` (`powLtF μ κ`): for some `α ∈ κ`, the class of all functions `ω → μ` (sets of ordered
  pairs, `fnF`, mirroring Mathlib's `ZFSet.IsFunc`) injects into `α` through a set `h`;
* colourings `f : [λ]² → {0, 1}` (`colouringF`): `f` assigns to every ordered pair `(α, β)` with
  `α ∈ β ∈ λ` (the unordered pair `{α, β}`) exactly one value, which is `0 = ∅` or `1 = {∅}`;
  `H` is homogeneous in colour `i` (`homogF`) if `f(α, β) = i` for all `α ∈ β` in `H`.
-/
import Erdos501.FOL.Statement
import Erdos1220

open scoped Cardinal FirstOrder
open FirstOrder FirstOrder.Language
open Erdos501.FOL

namespace Erdos1220.FOL

/-- `|A| ≤ |B|`: some `f` is an injective function from `A` to `B`. -/
def leqF (A B : Tm) : Fm :=
  exF fun f => andF (isFunF A B (varT f))
    (allIn A fun x => allIn A fun x' => allF fun y =>
      impF (appF (varT f) (varT x) (varT y)) <| impF (appF (varT f) (varT x') (varT y)) <|
        eqF (varT x) (varT x'))

/-- `|A| = |B|`. -/
def eqCardF (A B : Tm) : Fm := andF (leqF A B) (leqF B A)

/-- `k` (a level) is a cardinal, i.e. an initial ordinal. -/
def cardinalF (k : ℕ) : Fm :=
  andF (ordF k) (allIn (varT k) fun a => notF (leqF (varT k) (varT a)))

/-- `S` is cofinal in the ordinal `l`: `∀ β ∈ l, ∃ γ ∈ S, β ∈ γ ∨ β = γ`. -/
def cofinalF (S l : Tm) : Fm :=
  allIn l fun b => exIn S fun g => orF (memF (varT b) (varT g)) (eqF (varT b) (varT g))

/-- The cardinal `l` is singular: `ℵ₀ ≤ |l|` and some cofinal `S ⊆ l` has `|S| < |l|`. -/
def singularF (l : ℕ) : Fm :=
  andF (leqF omT (varT l))
    (exF fun S => andsF [subsetF (varT S) (varT l), cofinalF (varT S) (varT l),
      notF (leqF (varT l) (varT S))])

/-- `d = cf(l)`: `d` is a cardinal, some cofinal `S ⊆ l` has `|S| = |d|`, and every cofinal
`S ⊆ l` has `|d| ≤ |S|`. -/
def cofF (l d : ℕ) : Fm :=
  andsF [cardinalF d,
    exF (fun S => andsF [subsetF (varT S) (varT l), cofinalF (varT S) (varT l),
      eqCardF (varT S) (varT d)]),
    allF (fun S => impF (subsetF (varT S) (varT l)) <| impF (cofinalF (varT S) (varT l)) <|
      leqF (varT d) (varT S))]

/-- `f` is a function from `D` to `C` in the strict sense: a set of ordered pairs `(x, y)` with
`x ∈ D`, `y ∈ C`, relating each `x ∈ D` to exactly one `y` (Mathlib's `ZFSet.IsFunc`). -/
def fnF (D C f : Tm) : Fm :=
  andF (allIn f fun z => exIn D fun x => exIn C fun y => eqF (varT z) (pairT (varT x) (varT y)))
    (allIn D fun x => exF fun y => andF (appF f (varT x) (varT y))
      (allF fun y' => impF (appF f (varT x) (varT y')) (eqF (varT y') (varT y))))

/-- `|μ| ^ ℵ₀ < |k|` for a cardinal `k`: for some `α ∈ k` there is a set `h` relating every
function `f : ω → μ` to some `β ∈ α`, with no two distinct functions related to the same `β`
(i.e. the set of functions `ω → μ` injects into `α`). -/
def powLtF (μ k : Tm) : Fm :=
  exIn k fun α => exF fun h => andF
    (allF fun f => impF (fnF omT μ (varT f)) (exIn (varT α) fun b => appF (varT h) (varT f) (varT b)))
    (allF fun f => allF fun f' => allF fun b =>
      impF (fnF omT μ (varT f)) <| impF (fnF omT μ (varT f')) <|
      impF (appF (varT h) (varT f) (varT b)) <| impF (appF (varT h) (varT f') (varT b)) <|
        eqF (varT f) (varT f'))

/-- The cardinal `k` is `ℵ₀`-inaccessible: `μ ^ ℵ₀ < k` for every cardinal `μ < k`. -/
def omegaInaccF (k : ℕ) : Fm :=
  allIn (varT k) fun μ => impF (cardinalF μ) (powLtF (varT μ) (varT k))

/-- `i = 0`, i.e. `i = ∅`. -/
def zeroF (i : Tm) : Fm := eqF i empT

/-- `i = 1`, i.e. `i = {∅}`. -/
def oneF (i : Tm) : Fm := allF fun z => iffF (memF (varT z) i) (eqF (varT z) empT)

/-- `c` is a colouring `[l]² → {0, 1}`: every `(α, β)` with `α ∈ β ∈ l` has exactly one
`c`-value, and it is `0` or `1`. -/
def colouringF (l c : Tm) : Fm :=
  allIn l fun a => allIn l fun b => impF (memF (varT a) (varT b)) <|
    exF fun i => andsF [appF c (pairT (varT a) (varT b)) (varT i),
      orF (zeroF (varT i)) (oneF (varT i)),
      allF fun i' => impF (appF c (pairT (varT a) (varT b)) (varT i')) (eqF (varT i') (varT i))]

/-- `H` is homogeneous for `c` in colour `0`. -/
def homog0F (c H : Tm) : Fm :=
  allIn H fun a => allIn H fun b => impF (memF (varT a) (varT b)) <|
    allF fun i => impF (appF c (pairT (varT a) (varT b)) (varT i)) (zeroF (varT i))

/-- `H` is homogeneous for `c` in colour `1`. -/
def homog1F (c H : Tm) : Fm :=
  allIn H fun a => allIn H fun b => impF (memF (varT a) (varT b)) <|
    allF fun i => impF (appF c (pairT (varT a) (varT b)) (varT i)) (oneF (varT i))

/-- `w = ω₁`: `w` is an ordinal, `¬ |w| ≤ |ω|`, and `|a| ≤ |ω|` for all `a ∈ w`. -/
def omega1F (w : ℕ) : Fm :=
  andsF [ordF w, notF (leqF (varT w) omT), allIn (varT w) fun a => leqF (varT a) omT]

set_option linter.dupNamespace false in
/-- **Erdős problem #1220 as a sentence of `L`**: for every singular cardinal `λ` such that `λ`
and `cf λ` are `ℵ₀`-inaccessible, every colouring `c : [λ]² → {0, 1}` has a set `H ⊆ λ` with
`|H| = |λ|` homogeneous in colour `0` or a set `H ⊆ λ` with `|H| = |ω₁|` homogeneous in colour `1`. -/
def Erdos1220 : L.Sentence :=
  toSentence <|
    allF fun l =>
      impF (andsF [cardinalF l, singularF l, omegaInaccF l,
          allF fun d => impF (cofF l d) (omegaInaccF d)]) <|
      allF fun c => impF (colouringF (varT l) (varT c)) <|
        orF
          (exF fun H => andsF [subsetF (varT H) (varT l), eqCardF (varT H) (varT l),
            homog0F (varT c) (varT H)])
          (exF fun w => andF (omega1F w) <|
            exF fun H => andsF [subsetF (varT H) (varT l), eqCardF (varT H) (varT w),
              homog1F (varT c) (varT H)])

/-- **Target (headline)**: `ZFC` does not prove `Erdos1220`. -/
def Erdos1220NotProvable : Prop := ¬ (ZFC ⊨ᵇ Erdos1220)

/-- **Target (faithfulness)**: in Mathlib's `ZFSet`, `Erdos1220` holds iff the Mathlib-level
statement `Erdos1220.Problem1220` (universe `0`) holds. -/
def Erdos1220SentenceFaithful : Prop :=
  (ZFSet.{0} ⊨ Erdos1220) ↔ Erdos1220.Problem1220.{0}

end Erdos1220.FOL
