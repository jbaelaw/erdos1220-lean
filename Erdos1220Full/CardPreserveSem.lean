import Erdos1220Full.CardPreserve
import Erdos1220Full.Semantics1220

/-!
# Cardinal preservation, restated for the predicates of `Semantics1220`

The generic predicates of `CardPreserve.lean` coincide definitionally with the
`Flypitch.Erdos1220.Sem` predicates computed from the sentence `Erdos1220`.
-/

open Cardinal Flypitch bSet

namespace Erdos1220Full.CardB

variable {β : Type} [NontrivialCompleteBooleanAlgebra β]

theorem sem_leq_eq (A B : bSet β) : Flypitch.Erdos1220.Sem.leq A B = leqB A B := rfl

theorem sem_ord_eq (a : bSet β) : Flypitch.Erdos1220.Sem.ord a = ordB a := rfl

theorem sem_cardinal_eq (k : bSet β) : Flypitch.Erdos1220.Sem.cardinal k = cardinalB k := rfl

theorem sem_cofinal_eq (S l : bSet β) : Flypitch.Erdos1220.Sem.cofinal S l = cofinalB S l := rfl

theorem sem_subset_eq (S l : bSet β) : Flypitch.Erdos1220.Sem.subset S l = subsetB S l := rfl

theorem sem_cardinal_card_ex_of_chainCondition {θ : Cardinal.{0}} (hcc : ChainCondition θ β)
    (hθ : θ.IsRegular) {lam : Cardinal.{0}} (hθlam : θ ≤ lam) :
    (⊤ : β) ≤ Flypitch.Erdos1220.Sem.cardinal (check (PSet.card_ex lam)) :=
  cardinalB_card_ex_of_chainCondition hcc hθ hθlam

theorem sem_cardinal_card_ex_of_distrib {ν : Cardinal.{0}} (hd : DistribHyp ν β)
    {lam : Cardinal.{0}} (hsmall : ∀ o < lam.ord, o.card ≤ ν) :
    (⊤ : β) ≤ Flypitch.Erdos1220.Sem.cardinal (check (PSet.card_ex lam)) :=
  cardinalB_card_ex_of_distrib hd hsmall

theorem sem_leq_check_of_injects {x y : PSet.{0}} (h : PSet.injects_into x y) :
    (⊤ : β) ≤ Flypitch.Erdos1220.Sem.leq (check x) (check y) :=
  leqB_check_of_injects h

theorem sem_cofinal_check {S l : PSet.{0}}
    (h : ∀ i : l.Type, ∃ j : S.Type, l.Func i ∈ S.Func j ∨ PSet.Equiv (l.Func i) (S.Func j)) :
    (⊤ : β) ≤ Flypitch.Erdos1220.Sem.cofinal (check S) (check l) :=
  cofinalB_check h

theorem sem_fn_eq (D C f : bSet β) : Flypitch.Erdos1220.Sem.fn D C f = fnB D C f := rfl

theorem sem_powLt_eq (μ k : bSet β) : Flypitch.Erdos1220.Sem.powLt μ k = powLtB μ k := rfl

theorem sem_powLt_check {μ k α : PSet.{0}} (hα : α ∈ k)
    (hinj : PSet.injects_into (PSet.functions PSet.omega μ) α)
    (hF : (⊤ : β) ≤ check (PSet.functions PSet.omega μ) =ᴮ functions bSet.omega (check μ)) :
    (⊤ : β) ≤ Flypitch.Erdos1220.Sem.powLt (check μ) (check k) :=
  powLtB_check hα hinj hF

theorem sem_leq_check_eq_bot_of_chainCondition {θ : Cardinal.{0}} (hcc : ChainCondition θ β)
    (x y : PSet.{0}) (hy : ∀ i j, i ≠ j → ¬ PSet.Equiv (y.Func i) (y.Func j))
    (hfib : ∀ g : y.Type → x.Type, ∃ ξ, θ ≤ #(g ⁻¹' {ξ})) :
    Flypitch.Erdos1220.Sem.leq (check y : bSet β) (check x) = ⊥ :=
  leqB_check_eq_bot_of_chainCondition hcc x y hy hfib

theorem sem_leq_check_eq_bot_of_distrib {ν : Cardinal.{0}} (hd : DistribHyp ν β)
    (x y : PSet.{0}) (hy : ∀ i j, i ≠ j → ¬ PSet.Equiv (y.Func i) (y.Func j))
    (hxν : #x.Type ≤ ν) (hxy : #x.Type < #y.Type) :
    Flypitch.Erdos1220.Sem.leq (check y : bSet β) (check x) = ⊥ :=
  leqB_check_eq_bot_of_distrib hd x y hy hxν hxy

end Erdos1220Full.CardB

#print axioms Erdos1220Full.CardB.sem_cardinal_eq
#print axioms Erdos1220Full.CardB.sem_cardinal_card_ex_of_chainCondition
#print axioms Erdos1220Full.CardB.sem_cardinal_card_ex_of_distrib
#print axioms Erdos1220Full.CardB.sem_leq_check_of_injects
#print axioms Erdos1220Full.CardB.sem_cofinal_check
#print axioms Erdos1220Full.CardB.sem_powLt_check
