/-
# Erdős #1220 — two-valued unfolding of the sentence `Erdos1220` in `ZFSet`

We compute the realization of every combinator of `Statement1220` (and of the erdos501 combinators
it uses) in the standard structure `zfsetStructure` on `ZFSet.{0}`.  Variables are de Bruijn
*levels*; `val xs ℓ` is the value of level `ℓ` in the context `xs` (`∅` if out of range), and
`val (Fin.snoc xs a) ℓ` is computed by `val_snoc_eq` / `val_snoc_lt` (side conditions by `omega`).
-/
import Erdos1220Full.Statement1220

open scoped Cardinal FirstOrder
open FirstOrder FirstOrder.Language
open Erdos501.FOL

namespace Erdos1220.FOL

/-- The value of the level-`ℓ` variable in the context `xs`. -/
noncomputable def val {n : ℕ} (xs : Fin n → ZFSet.{0}) (ℓ : ℕ) : ZFSet.{0} :=
  if h : ℓ < n then xs ⟨ℓ, h⟩ else ∅

theorem val_snoc_eq {n ℓ : ℕ} (xs : Fin n → ZFSet.{0}) (a : ZFSet.{0}) (h : ℓ = n) :
    val (Fin.snoc (α := fun _ => ZFSet.{0}) xs a) ℓ = a := by
  subst h
  simp [val, Fin.snoc]

theorem val_snoc_lt {n ℓ : ℕ} (xs : Fin n → ZFSet.{0}) (a : ZFSet.{0}) (h : ℓ < n) :
    val (Fin.snoc (α := fun _ => ZFSet.{0}) xs a) ℓ = val xs ℓ := by
  simp [val, Fin.snoc, h, Nat.lt_succ_of_lt h, Fin.castLT]

variable {v : Empty → ZFSet.{0}}

theorem realize_varT {n : ℕ} (xs : Fin n → ZFSet.{0}) (ℓ : ℕ) :
    (varT ℓ n).realize (Sum.elim v xs) = val xs ℓ := by
  unfold varT val
  split_ifs <;> rfl

theorem realize_empT {n : ℕ} (xs : Fin n → ZFSet.{0}) :
    (empT n).realize (Sum.elim v xs) = ∅ := rfl

theorem realize_omT {n : ℕ} (xs : Fin n → ZFSet.{0}) :
    (omT n).realize (Sum.elim v xs) = ZFSet.omega := rfl

theorem realize_pairT {n : ℕ} (xs : Fin n → ZFSet.{0}) (s t : Tm) :
    (pairT s t n).realize (Sum.elim v xs) =
      ZFSet.pair ((s n).realize (Sum.elim v xs)) ((t n).realize (Sum.elim v xs)) := rfl

theorem realize_powT {n : ℕ} (xs : Fin n → ZFSet.{0}) (t : Tm) :
    (powT t n).realize (Sum.elim v xs) = ZFSet.powerset ((t n).realize (Sum.elim v xs)) := rfl

theorem realize_memF {n : ℕ} (xs : Fin n → ZFSet.{0}) (s t : Tm) :
    (memF s t n).Realize v xs ↔
      (s n).realize (Sum.elim v xs) ∈ (t n).realize (Sum.elim v xs) := Iff.rfl

theorem realize_eqF {n : ℕ} (xs : Fin n → ZFSet.{0}) (s t : Tm) :
    (eqF s t n).Realize v xs ↔ (s n).realize (Sum.elim v xs) = (t n).realize (Sum.elim v xs) :=
  Iff.rfl

theorem realize_andF {n : ℕ} (xs : Fin n → ZFSet.{0}) (φ ψ : Fm) :
    (andF φ ψ n).Realize v xs ↔ (φ n).Realize v xs ∧ (ψ n).Realize v xs :=
  BoundedFormula.realize_inf

theorem realize_orF {n : ℕ} (xs : Fin n → ZFSet.{0}) (φ ψ : Fm) :
    (orF φ ψ n).Realize v xs ↔ (φ n).Realize v xs ∨ (ψ n).Realize v xs :=
  BoundedFormula.realize_sup

theorem realize_impF {n : ℕ} (xs : Fin n → ZFSet.{0}) (φ ψ : Fm) :
    (impF φ ψ n).Realize v xs ↔ ((φ n).Realize v xs → (ψ n).Realize v xs) :=
  BoundedFormula.realize_imp

theorem realize_iffF {n : ℕ} (xs : Fin n → ZFSet.{0}) (φ ψ : Fm) :
    (iffF φ ψ n).Realize v xs ↔ ((φ n).Realize v xs ↔ (ψ n).Realize v xs) :=
  BoundedFormula.realize_iff

theorem realize_notF {n : ℕ} (xs : Fin n → ZFSet.{0}) (φ : Fm) :
    (notF φ n).Realize v xs ↔ ¬ (φ n).Realize v xs :=
  BoundedFormula.realize_not

theorem realize_allF {n : ℕ} (xs : Fin n → ZFSet.{0}) (φ : ℕ → Fm) :
    (allF φ n).Realize v xs ↔
      ∀ a : ZFSet.{0}, (φ n (n + 1)).Realize v (Fin.snoc (α := fun _ => ZFSet.{0}) xs a) :=
  BoundedFormula.realize_all

theorem realize_exF {n : ℕ} (xs : Fin n → ZFSet.{0}) (φ : ℕ → Fm) :
    (exF φ n).Realize v xs ↔
      ∃ a : ZFSet.{0}, (φ n (n + 1)).Realize v (Fin.snoc (α := fun _ => ZFSet.{0}) xs a) :=
  BoundedFormula.realize_ex

theorem realize_andsF_cons₂ {n : ℕ} (xs : Fin n → ZFSet.{0}) (φ ψ : Fm) (φs : List Fm) :
    (andsF (φ :: ψ :: φs) n).Realize v xs ↔
      (φ n).Realize v xs ∧ (andsF (ψ :: φs) n).Realize v xs :=
  BoundedFormula.realize_inf

theorem realize_andsF_one {n : ℕ} (xs : Fin n → ZFSet.{0}) (φ : Fm) :
    (andsF [φ] n).Realize v xs ↔ (φ n).Realize v xs := Iff.rfl

/-- The simp set for unfolding. -/
macro "zsimp" : tactic => `(tactic| simp (disch := omega) only [allIn, exIn, subsetF, appF, ltF,
  isFunF, ordF, realize_varT, realize_empT, realize_omT, realize_pairT, realize_powT,
  realize_memF, realize_eqF, realize_andF, realize_orF, realize_impF, realize_iffF, realize_notF,
  realize_allF, realize_exF, realize_andsF_cons₂, realize_andsF_one, val_snoc_eq, val_snoc_lt])

/-! ### Two-valued predicates on `ZFSet` -/

/-- `|A| ≤ |B|` as unfolded from `leqF`. -/
def LeqZ (A B : ZFSet.{0}) : Prop :=
  ∃ f : ZFSet.{0},
    (∀ x : ZFSet.{0}, x ∈ A → ∃ y : ZFSet.{0}, y ∈ B ∧
      (ZFSet.pair x y ∈ f ∧ ∀ y' : ZFSet.{0}, ZFSet.pair x y' ∈ f → y' = y)) ∧
    (∀ x : ZFSet.{0}, x ∈ A → ∀ x' : ZFSet.{0}, x' ∈ A → ∀ y : ZFSet.{0},
      ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x')

/-- The ordinal predicate, as unfolded from erdos501's `ordF`. -/
def OrdZ (a : ZFSet.{0}) : Prop :=
  ((∀ y : ZFSet.{0}, y ∈ a → ∀ z : ZFSet.{0}, z ∈ a → (y = z ∨ y ∈ z) ∨ z ∈ y) ∧
    (∀ y : ZFSet.{0}, (∀ z : ZFSet.{0}, z ∈ y → z ∈ a) → ¬ y = ∅ →
      ∃ z : ZFSet.{0}, z ∈ y ∧ ∀ w : ZFSet.{0}, w ∈ y → ¬ w ∈ z)) ∧
  ∀ y : ZFSet.{0}, y ∈ a → ∀ z : ZFSet.{0}, z ∈ y → z ∈ a

def CardZ (k : ZFSet.{0}) : Prop := OrdZ k ∧ ∀ a : ZFSet.{0}, a ∈ k → ¬ LeqZ k a

def SubZ (S l : ZFSet.{0}) : Prop := ∀ z : ZFSet.{0}, z ∈ S → z ∈ l

def CofinalZ (S l : ZFSet.{0}) : Prop :=
  ∀ b : ZFSet.{0}, b ∈ l → ∃ g : ZFSet.{0}, g ∈ S ∧ (b ∈ g ∨ b = g)

def SingZ (l : ZFSet.{0}) : Prop :=
  LeqZ ZFSet.omega l ∧ ∃ S : ZFSet.{0}, SubZ S l ∧ CofinalZ S l ∧ ¬ LeqZ l S

def CofZ (l d : ZFSet.{0}) : Prop :=
  CardZ d ∧ (∃ S : ZFSet.{0}, SubZ S l ∧ CofinalZ S l ∧ (LeqZ S d ∧ LeqZ d S)) ∧
    ∀ S : ZFSet.{0}, SubZ S l → CofinalZ S l → LeqZ d S

def FnZ (D C f : ZFSet.{0}) : Prop :=
  (∀ z : ZFSet.{0}, z ∈ f → ∃ x : ZFSet.{0}, x ∈ D ∧ ∃ y : ZFSet.{0}, y ∈ C ∧ z = ZFSet.pair x y) ∧
  ∀ x : ZFSet.{0}, x ∈ D → ∃ y : ZFSet.{0},
    ZFSet.pair x y ∈ f ∧ ∀ y' : ZFSet.{0}, ZFSet.pair x y' ∈ f → y' = y

def PowLtZ (μ k : ZFSet.{0}) : Prop :=
  ∃ α : ZFSet.{0}, α ∈ k ∧ ∃ h : ZFSet.{0},
    (∀ f : ZFSet.{0}, FnZ ZFSet.omega μ f → ∃ b : ZFSet.{0}, b ∈ α ∧ ZFSet.pair f b ∈ h) ∧
    (∀ f f' b : ZFSet.{0}, FnZ ZFSet.omega μ f → FnZ ZFSet.omega μ f' →
      ZFSet.pair f b ∈ h → ZFSet.pair f' b ∈ h → f = f')

def OInaccZ (k : ZFSet.{0}) : Prop := ∀ μ : ZFSet.{0}, μ ∈ k → CardZ μ → PowLtZ μ k

def OneZ (i : ZFSet.{0}) : Prop := ∀ z : ZFSet.{0}, z ∈ i ↔ z = ∅

def ColZ (l c : ZFSet.{0}) : Prop :=
  ∀ a : ZFSet.{0}, a ∈ l → ∀ b : ZFSet.{0}, b ∈ l → a ∈ b → ∃ i : ZFSet.{0},
    ZFSet.pair (ZFSet.pair a b) i ∈ c ∧ (i = ∅ ∨ OneZ i) ∧
      ∀ i' : ZFSet.{0}, ZFSet.pair (ZFSet.pair a b) i' ∈ c → i' = i

def Hom0Z (c H : ZFSet.{0}) : Prop :=
  ∀ a : ZFSet.{0}, a ∈ H → ∀ b : ZFSet.{0}, b ∈ H → a ∈ b →
    ∀ i : ZFSet.{0}, ZFSet.pair (ZFSet.pair a b) i ∈ c → i = ∅

def Hom1Z (c H : ZFSet.{0}) : Prop :=
  ∀ a : ZFSet.{0}, a ∈ H → ∀ b : ZFSet.{0}, b ∈ H → a ∈ b →
    ∀ i : ZFSet.{0}, ZFSet.pair (ZFSet.pair a b) i ∈ c → OneZ i

def Om1Z (w : ZFSet.{0}) : Prop :=
  OrdZ w ∧ ¬ LeqZ w ZFSet.omega ∧ ∀ a : ZFSet.{0}, a ∈ w → LeqZ a ZFSet.omega

/-- The two-valued content of `Erdos1220`. -/
def SemZ : Prop :=
  ∀ l : ZFSet.{0}, (CardZ l ∧ SingZ l ∧ OInaccZ l ∧ ∀ d : ZFSet.{0}, CofZ l d → OInaccZ d) →
    ∀ c : ZFSet.{0}, ColZ l c →
      (∃ H : ZFSet.{0}, SubZ H l ∧ (LeqZ H l ∧ LeqZ l H) ∧ Hom0Z c H) ∨
      (∃ w : ZFSet.{0}, Om1Z w ∧
        ∃ H : ZFSet.{0}, SubZ H l ∧ (LeqZ H w ∧ LeqZ w H) ∧ Hom1Z c H)

/-! ### Realization lemmas for the combinators -/

section
variable {n : ℕ} (xs : Fin n → ZFSet.{0})

theorem realize_leqF_vv {a b : ℕ} (ha : a < n) (hb : b < n) :
    (leqF (varT a) (varT b) n).Realize v xs ↔ LeqZ (val xs a) (val xs b) := by
  unfold leqF; zsimp; rfl

theorem realize_leqF_ov {b : ℕ} (hb : b < n) :
    (leqF omT (varT b) n).Realize v xs ↔ LeqZ ZFSet.omega (val xs b) := by
  unfold leqF; zsimp; rfl

theorem realize_leqF_vo {a : ℕ} (ha : a < n) :
    (leqF (varT a) omT n).Realize v xs ↔ LeqZ (val xs a) ZFSet.omega := by
  unfold leqF; zsimp; rfl

theorem realize_eqCardF_vv {a b : ℕ} (ha : a < n) (hb : b < n) :
    (eqCardF (varT a) (varT b) n).Realize v xs ↔
      (LeqZ (val xs a) (val xs b) ∧ LeqZ (val xs b) (val xs a)) := by
  unfold eqCardF
  rw [realize_andF, realize_leqF_vv xs ha hb, realize_leqF_vv xs hb ha]

theorem realize_ordF_v {a : ℕ} (ha : a < n) :
    (ordF a n).Realize v xs ↔ OrdZ (val xs a) := by
  zsimp; rfl

theorem realize_cardinalF {k : ℕ} (hk : k < n) :
    (cardinalF k n).Realize v xs ↔ CardZ (val xs k) := by
  unfold cardinalF
  zsimp
  simp (disch := omega) only [realize_leqF_vv, val_snoc_eq, val_snoc_lt]
  rfl

theorem realize_cofinalF_vv {S l : ℕ} (hS : S < n) (hl : l < n) :
    (cofinalF (varT S) (varT l) n).Realize v xs ↔ CofinalZ (val xs S) (val xs l) := by
  unfold cofinalF; zsimp; rfl

theorem realize_singularF {l : ℕ} (hl : l < n) :
    (singularF l n).Realize v xs ↔ SingZ (val xs l) := by
  unfold singularF
  zsimp
  simp (disch := omega) only [realize_leqF_ov, realize_leqF_vv, realize_cofinalF_vv,
    val_snoc_eq, val_snoc_lt]
  rfl

theorem realize_cofF {l d : ℕ} (hl : l < n) (hd : d < n) :
    (cofF l d n).Realize v xs ↔ CofZ (val xs l) (val xs d) := by
  unfold cofF
  zsimp
  simp (disch := omega) only [realize_cardinalF, realize_leqF_vv, realize_cofinalF_vv,
    realize_eqCardF_vv, val_snoc_eq, val_snoc_lt]
  rfl

theorem realize_fnF_ovv {μ f : ℕ} (hμ : μ < n) (hf : f < n) :
    (fnF omT (varT μ) (varT f) n).Realize v xs ↔ FnZ ZFSet.omega (val xs μ) (val xs f) := by
  unfold fnF; zsimp; rfl

theorem realize_powLtF_vv {μ k : ℕ} (hμ : μ < n) (hk : k < n) :
    (powLtF (varT μ) (varT k) n).Realize v xs ↔ PowLtZ (val xs μ) (val xs k) := by
  unfold powLtF
  zsimp
  simp (disch := omega) only [realize_fnF_ovv, val_snoc_eq, val_snoc_lt]
  rfl

theorem realize_omegaInaccF {k : ℕ} (hk : k < n) :
    (omegaInaccF k n).Realize v xs ↔ OInaccZ (val xs k) := by
  unfold omegaInaccF
  zsimp
  simp (disch := omega) only [realize_cardinalF, realize_powLtF_vv, val_snoc_eq, val_snoc_lt]
  rfl

theorem realize_colouringF_vv {l c : ℕ} (hl : l < n) (hc : c < n) :
    (colouringF (varT l) (varT c) n).Realize v xs ↔ ColZ (val xs l) (val xs c) := by
  unfold colouringF zeroF oneF; zsimp; rfl

theorem realize_homog0F_vv {c H : ℕ} (hc : c < n) (hH : H < n) :
    (homog0F (varT c) (varT H) n).Realize v xs ↔ Hom0Z (val xs c) (val xs H) := by
  unfold homog0F zeroF; zsimp; rfl

theorem realize_homog1F_vv {c H : ℕ} (hc : c < n) (hH : H < n) :
    (homog1F (varT c) (varT H) n).Realize v xs ↔ Hom1Z (val xs c) (val xs H) := by
  unfold homog1F oneF; zsimp; rfl

theorem realize_omega1F {w : ℕ} (hw : w < n) :
    (omega1F w n).Realize v xs ↔ Om1Z (val xs w) := by
  unfold omega1F
  zsimp
  simp (disch := omega) only [realize_leqF_vo, val_snoc_eq]
  rfl

end

/-- **Unfolding of the sentence**: `ZFSet ⊨ Erdos1220 ↔ SemZ`. -/
theorem realize_Erdos1220_iff_SemZ : (ZFSet.{0} ⊨ Erdos1220) ↔ SemZ := by
  change BoundedFormula.Realize (Erdos1220.FOL.Erdos1220 : L.BoundedFormula Empty 0)
    (default : Empty → ZFSet.{0}) (default : Fin 0 → ZFSet.{0}) ↔ SemZ
  unfold Erdos1220 toSentence
  zsimp
  simp (disch := omega) only [realize_cardinalF, realize_singularF, realize_omegaInaccF,
    realize_cofF, realize_colouringF_vv, realize_eqCardF_vv, realize_homog0F_vv,
    realize_homog1F_vv, realize_omega1F, val_snoc_eq, val_snoc_lt]
  rfl

end Erdos1220.FOL

#print axioms Erdos1220.FOL.realize_Erdos1220_iff_SemZ
