/-
Boolean value of `Erdos1220_f` in `V β`, following erdos501
`Flypitch4/Erdos501/Semantics.lean` (Apache 2.0, The Flypitch Project).
-/
import Erdos1220Full.SentenceF
import Flypitch4.Erdos501.Semantics

open Fol bSet
open scoped Flypitch

namespace Flypitch.Erdos1220

open Flypitch.Erdos501

variable {β : Type} [NontrivialCompleteBooleanAlgebra β]

namespace Sem

open Flypitch.Erdos501.Sem

def subset (s t : bSet β) : β := ⨅ z : bSet β, z ∈ᴮ s ⟹ z ∈ᴮ t

def leq (A B : bSet β) : β :=
  ⨆ f : bSet β, isFun A B f ⊓
    ⨅ x : bSet β, x ∈ᴮ A ⟹ ⨅ x' : bSet β, x' ∈ᴮ A ⟹ ⨅ y : bSet β,
      app f x y ⟹ (app f x' y ⟹ x =ᴮ x')

def eqCard (A B : bSet β) : β := leq A B ⊓ leq B A

def ord (a : bSet β) : β :=
  ((⨅ y : bSet β, y ∈ᴮ a ⟹ ⨅ z : bSet β, z ∈ᴮ a ⟹ ((y =ᴮ z ⊔ y ∈ᴮ z) ⊔ z ∈ᴮ y)) ⊓
    (⨅ y : bSet β, subset y a ⟹ ((y =ᴮ bSet.empty)ᶜ ⟹
      ⨆ z : bSet β, z ∈ᴮ y ⊓ ⨅ w : bSet β, w ∈ᴮ y ⟹ (w ∈ᴮ z)ᶜ))) ⊓
  ⨅ y : bSet β, y ∈ᴮ a ⟹ subset y a

def cardinal (k : bSet β) : β := ord k ⊓ ⨅ a : bSet β, a ∈ᴮ k ⟹ (leq k a)ᶜ

def cofinal (S l : bSet β) : β :=
  ⨅ b : bSet β, b ∈ᴮ l ⟹ ⨆ g : bSet β, g ∈ᴮ S ⊓ (b ∈ᴮ g ⊔ b =ᴮ g)

def singular (l : bSet β) : β :=
  leq bSet.omega l ⊓ ⨆ S : bSet β, subset S l ⊓ (cofinal S l ⊓ (leq l S)ᶜ)

def cof (l d : bSet β) : β :=
  cardinal d ⊓ ((⨆ S : bSet β, subset S l ⊓ (cofinal S l ⊓ eqCard S d)) ⊓
    ⨅ S : bSet β, subset S l ⟹ (cofinal S l ⟹ leq d S))

def fn (D C f : bSet β) : β :=
  (⨅ z : bSet β, z ∈ᴮ f ⟹ ⨆ x : bSet β, x ∈ᴮ D ⊓ ⨆ y : bSet β, y ∈ᴮ C ⊓ z =ᴮ pair x y) ⊓
    ⨅ x : bSet β, x ∈ᴮ D ⟹ ⨆ y : bSet β, app f x y ⊓ ⨅ y' : bSet β, app f x y' ⟹ y' =ᴮ y

def powLt (μ k : bSet β) : β :=
  ⨆ α : bSet β, α ∈ᴮ k ⊓ ⨆ h : bSet β,
    (⨅ f : bSet β, fn bSet.omega μ f ⟹ ⨆ b : bSet β, b ∈ᴮ α ⊓ app h f b) ⊓
    ⨅ f : bSet β, ⨅ f' : bSet β, ⨅ b : bSet β,
      fn bSet.omega μ f ⟹ (fn bSet.omega μ f' ⟹ (app h f b ⟹ (app h f' b ⟹ f =ᴮ f')))

def omegaInacc (k : bSet β) : β := ⨅ μ : bSet β, μ ∈ᴮ k ⟹ (cardinal μ ⟹ powLt μ k)

def zero (i : bSet β) : β := i =ᴮ bSet.empty

def one (i : bSet β) : β := ⨅ z : bSet β, bihimp (z ∈ᴮ i) (z =ᴮ bSet.empty)

def colouring (l c : bSet β) : β :=
  ⨅ a : bSet β, a ∈ᴮ l ⟹ ⨅ b : bSet β, b ∈ᴮ l ⟹ (a ∈ᴮ b ⟹
    ⨆ i : bSet β, app c (pair a b) i ⊓ ((zero i ⊔ one i) ⊓
      ⨅ i' : bSet β, app c (pair a b) i' ⟹ i' =ᴮ i))

def homog0 (c H : bSet β) : β :=
  ⨅ a : bSet β, a ∈ᴮ H ⟹ ⨅ b : bSet β, b ∈ᴮ H ⟹ (a ∈ᴮ b ⟹
    ⨅ i : bSet β, app c (pair a b) i ⟹ zero i)

def homog1 (c H : bSet β) : β :=
  ⨅ a : bSet β, a ∈ᴮ H ⟹ ⨅ b : bSet β, b ∈ᴮ H ⟹ (a ∈ᴮ b ⟹
    ⨅ i : bSet β, app c (pair a b) i ⟹ one i)

def omega1 (w : bSet β) : β :=
  ord w ⊓ ((leq w bSet.omega)ᶜ ⊓ ⨅ a : bSet β, a ∈ᴮ w ⟹ leq a bSet.omega)

/-- The hypotheses of #1220 on `l`. -/
def hyp (l : bSet β) : β :=
  cardinal l ⊓ (singular l ⊓ (omegaInacc l ⊓ ⨅ d : bSet β, cof l d ⟹ omegaInacc d))

/-- The conclusion of #1220 for the colouring `c` of `l`. -/
def arrow (l c : bSet β) : β :=
  (⨆ H : bSet β, subset H l ⊓ (eqCard H l ⊓ homog0 c H)) ⊔
    ⨆ w : bSet β, omega1 w ⊓ ⨆ H : bSet β, subset H l ⊓ (eqCard H w ⊓ homog1 c H)

def erdos1220 : β :=
  ⨅ l : bSet β, hyp l ⟹ ⨅ c : bSet β, colouring l c ⟹ arrow l c

end Sem

theorem realize_Erdos1220_f : ⟦Erdos1220_f⟧[V β] = (Sem.erdos1220 : β) := by
  simp only [Erdos1220_f, toSentence, allF, exF, allIn, exIn, andF, orF, impF, iffF, notF, memF,
    eqF, varT, pairT, omT, empT, appF, isFunF, andsF,
    leqF, eqCardF, cardinalF, cofinalF, singularF, cofF, fnF, powLtF, omegaInaccF, zeroF, oneF,
    colouringF, homog0F, homog1F, omega1F, ordF, subsetF,
    boolean_realize_sentence, boolean_realize_bounded_formula,
    boolean_realize_bounded_formula_and, boolean_realize_bounded_formula_or,
    boolean_realize_bounded_formula_not, boolean_realize_bounded_formula_ex,
    boolean_realize_bounded_formula_biimp, boolean_realize_bounded_formula_mem',
    boolean_realize_bounded_term_pair',
    boolean_realize_bounded_term_omega', boolean_realize_bounded_term_emptyset',
    boolean_realize_bounded_term, DVec.nth, V_forall, V_exists, V_eq,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceDIte]
  simp only [Sem.erdos1220, Sem.hyp, Sem.arrow, Sem.subset, Sem.leq, Sem.eqCard, Sem.ord,
    Sem.cardinal, Sem.cofinal, Sem.singular, Sem.cof, Sem.fn, Sem.powLt, Sem.omegaInacc,
    Sem.zero, Sem.one, Sem.colouring, Sem.homog0, Sem.homog1, Sem.omega1,
    Erdos501.Sem.isFun, Erdos501.Sem.app]
  rfl

/-- **Reduction for the negative direction.** Names `l, c` with `Γ ≤ hyp l`, `Γ ≤ colouring l c`
and `Γ ⊓ arrow l c ≤ ⊥` force `¬ Erdos1220_f` on `Γ`. -/
theorem forced_not_Erdos1220_f_of {Γ : β} (l c : bSet β) (hh : Γ ≤ Sem.hyp l)
    (hc : Γ ≤ Sem.colouring l c) (ha : Γ ⊓ Sem.arrow l c ≤ ⊥) :
    Γ ⊩[V β] (bd_not Erdos1220_f : sentence L_ZFC) := by
  change Γ ≤ ⟦bd_not Erdos1220_f⟧[V β]
  rw [boolean_realize_sentence_not, realize_Erdos1220_f]
  rw [le_compl_iff_disjoint_right, disjoint_iff]
  apply le_bot_iff.mp
  have h0 : Sem.erdos1220 ≤ (Sem.hyp l ⟹ ⨅ c', Sem.colouring l c' ⟹ Sem.arrow l c' : β) :=
    iInf_le (fun l => Sem.hyp l ⟹ ⨅ c', Sem.colouring l c' ⟹ Sem.arrow l c') l
  have h1 : Γ ⊓ Sem.erdos1220 ≤ (Sem.colouring l c ⟹ Sem.arrow l c : β) :=
    ((le_inf (inf_le_right.trans h0) (inf_le_left.trans hh)).trans Lattice.bv_imp_elim).trans
      (iInf_le (fun c' => Sem.colouring l c' ⟹ Sem.arrow l c') c)
  have h2 : Γ ⊓ Sem.erdos1220 ≤ Sem.arrow l c :=
    (le_inf h1 (inf_le_left.trans hc)).trans Lattice.bv_imp_elim
  exact (le_inf inf_le_left h2).trans ha

end Flypitch.Erdos1220

#print axioms Flypitch.Erdos1220.realize_Erdos1220_f
#print axioms Flypitch.Erdos1220.forced_not_Erdos1220_f_of
