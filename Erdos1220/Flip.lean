import Erdos1220.HistorySplice
import Erdos1220.Relabel
import Erdos1220.SwapExtension
import Erdos1220.HistoryConstruction

/-!
# Single flips of block-preserving histories (Sh:258 §3.5)

For a block-preserving history `H` and a stage `i` with `i + 1 ≤ H.length`,
let `t := H.step i` and let `σ` be the canonical ambient involution of the
overlap-fixing copying isomorphism `t.iso`. The flip at `i`

* relabels the whole prefix `[0, i]` by `σ` (states *and* recorded witnesses),
* replaces the boundary transition by its reverse `t.reverse`,
* keeps every state and transition from `i + 1` on unchanged.

We prove: history extensionality, the relabelling algebra, that flipping
preserves length, the terminal condition and block preservation, that flipping
twice at the same stage is the identity (including all witnesses), and prefix
naturality with respect to pure extension.
-/

open Cardinal Set Order

universe u v

namespace Erdos1220.BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

theorem relabel_relabel (p : BasicCondition V I block μ) (e e' : V ≃ V)
    (he : ∀ x, block (e x) = block x) (he' : ∀ x, block (e' x) = block x) :
    (p.relabel e he).relabel e' he' =
      p.relabel (e.trans e') (fun x => (he' (e x)).trans (he x)) :=
  eq_of_support_blue rfl (fun _ _ => Iff.rfl)

theorem relabel_refl (p : BasicCondition V I block μ)
    (he : ∀ x, block (Equiv.refl V x) = block x) :
    p.relabel (Equiv.refl V) he = p :=
  eq_of_support_blue rfl (fun _ _ => Iff.rfl)

theorem relabel_congr {p p' : BasicCondition V I block μ} (hp : p = p')
    {e e' : V ≃ V} (h : e = e') (he : ∀ x, block (e x) = block x)
    (he' : ∀ x, block (e' x) = block x) : p.relabel e he = p'.relabel e' he' := by
  subst hp
  subst h
  rfl

namespace Transition

variable {p r p' r' : BasicCondition V I block μ}

theorem relabel_heq_congr (hp : p = p') (hr : r = r')
    {t : Transition hμ p r} {t' : Transition hμ p' r'} (ht : HEq t t')
    {e e' : V ≃ V} (h : e = e') (he : ∀ x, block (e x) = block x)
    (he' : ∀ x, block (e' x) = block x) :
    HEq (t.relabel e he) (t'.relabel e' he') := by
  subst hp
  subst hr
  subst h
  cases ht
  rfl

theorem relabel_relabel (t : Transition hμ p r) (e e' : V ≃ V)
    (he : ∀ x, block (e x) = block x) (he' : ∀ x, block (e' x) = block x) :
    HEq ((t.relabel e he).relabel e' he')
      (t.relabel (e.trans e') (fun x => (he' (e x)).trans (he x))) := by
  cases t with
  | mk right iso fo fsb edge ss req =>
    cases edge <;> rfl

theorem relabel_refl (t : Transition hμ p r)
    (he : ∀ x, block (Equiv.refl V x) = block x) :
    HEq (t.relabel (Equiv.refl V) he) t := by
  cases t with
  | mk right iso fo fsb edge ss req =>
    cases edge <;> rfl

theorem reverse_heq_congr (hp : p = p') (hr : r = r')
    {t : Transition hμ p r} {t' : Transition hμ p' r'} (ht : HEq t t')
    (h : t.iso.PreservesBlocks) (h' : t'.iso.PreservesBlocks) :
    HEq (t.reverse h) (t'.reverse h') := by
  subst hp
  subst hr
  cases ht
  rfl

theorem reverse_reverse (t : Transition hμ p r) (h : t.iso.PreservesBlocks)
    (h' : (t.reverse h).iso.PreservesBlocks) :
    HEq ((t.reverse h).reverse h') t := by
  cases t with
  | mk right iso fo fsb edge ss req =>
    cases edge <;> rfl

/-- Transitions that agree up to transport have the same canonical swap. -/
theorem swap_eq_of_heq (hp : p = p') (hr : r = r')
    {t : Transition hμ p r} {t' : Transition hμ p' r'} (ht : HEq t t') :
    t.iso.swapExtension t.fixesOverlap = t'.iso.swapExtension t'.fixesOverlap := by
  subst hp
  subst hr
  cases ht
  rfl

end Transition
end Erdos1220.BasicCondition

namespace Erdos1220.History

open BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

/-! ### Extensionality -/

/-- Two histories with the same length, the same states and the same recorded
transitions (up to transport) are equal. -/
theorem ext_of {H K : History V I block μ hμ} (hl : H.length = K.length)
    (hs : ∀ i (hi : i ≤ H.length) (hk : i ≤ K.length), H.state i hi = K.state i hk)
    (hst : ∀ i (hi : Order.succ i ≤ H.length) (hk : Order.succ i ≤ K.length),
      HEq (H.step i hi) (K.step i hk)) : H = K := by
  cases H with
  | mk l1 lt1 s1 inc1 ir1 ib1 in1 st1 ls1 lb1 =>
  cases K with
  | mk l2 lt2 s2 inc2 ir2 ib2 in2 st2 ls2 lb2 =>
  dsimp only at hl hs hst
  subst hl
  have hs' : s1 = s2 := funext fun i => funext fun hi => hs i hi hi
  subst hs'
  have hst' : st1 = st2 := funext fun i => funext fun hi => eq_of_heq (hst i hi hi)
  subst hst'
  rfl

/-- A pure extension that is not longer is the identity. -/
theorem PureExtends.eq_of_length_le {H K : History V I block μ hμ}
    (h : PureExtends H K) (hl : K.length ≤ H.length) : H = K :=
  ext_of (le_antisymm h.length_le hl) (fun i hi _ => h.state_eq i hi)
    (fun i hi _ => h.step_heq i hi)

theorem PureExtends.antisymm {H K : History V I block μ hμ}
    (h : PureExtends H K) (h' : PureExtends K H) : H = K :=
  h.eq_of_length_le h'.length_le

/-! ### Relabelling algebra at the history level -/

theorem relabel_trans (H : History V I block μ hμ) (e e' : V ≃ V)
    (he : ∀ x, block (e x) = block x) (he' : ∀ x, block (e' x) = block x) :
    (H.relabel e he).relabel e' he' =
      H.relabel (e.trans e') (fun x => (he' (e x)).trans (he x)) :=
  ext_of rfl (fun _ _ _ => BasicCondition.relabel_relabel _ e e' he he')
    (fun _ _ _ => Transition.relabel_relabel _ e e' he he')

theorem relabel_refl (H : History V I block μ hμ)
    (he : ∀ x, block (Equiv.refl V x) = block x) :
    H.relabel (Equiv.refl V) he = H :=
  ext_of rfl (fun _ _ _ => BasicCondition.relabel_refl _ he)
    (fun _ _ _ => Transition.relabel_refl _ he)

theorem relabel_congr (H : History V I block μ hμ) {e e' : V ≃ V} (h : e = e')
    (he : ∀ x, block (e x) = block x) (he' : ∀ x, block (e' x) = block x) :
    H.relabel e he = H.relabel e' he' := by
  subst h
  rfl

theorem relabel_truncate (H : History V I block μ hμ) (δ : Ordinal.{u})
    (hδ : δ ≤ H.length) (e : V ≃ V) (he : ∀ x, block (e x) = block x) :
    (H.truncate δ hδ).relabel e he = (H.relabel e he).truncate δ hδ := rfl

theorem relabel_last (H : History V I block μ hμ) (e : V ≃ V)
    (he : ∀ x, block (e x) = block x) :
    (H.relabel e he).last = H.last.relabel e he := rfl

/-- Relabelling commutes with pure extension. -/
theorem PureExtends.relabel {H K : History V I block μ hμ} (h : PureExtends H K)
    (e : V ≃ V) (he : ∀ x, block (e x) = block x) :
    PureExtends (H.relabel e he) (K.relabel e he) := by
  refine ⟨h.length_le, ?_, ?_⟩
  · intro i hi
    exact congrArg (fun p : BasicCondition V I block μ => p.relabel e he) (h.state_eq i hi)
  · intro i hi
    exact Transition.relabel_heq_congr (h.state_eq i ((Order.le_succ i).trans hi))
      (h.state_eq (Order.succ i) hi) (h.step_heq i hi) rfl he he

/-! ### Transitions of an appended history -/

private theorem flip_mpr_heq {α β : Sort v} (h : α = β) (x : β) :
    HEq (Eq.mpr h x) x := by
  cases h
  exact HEq.rfl

theorem append_step_heq_last (H : History V I block μ hμ)
    (r : BasicCondition V I block μ) (t : Transition hμ H.last r)
    (hi : Order.succ H.length ≤ (H.append r t).length) :
    HEq ((H.append r t).step H.length hi) t := by
  simp only [History.append, eq_self, dite_true]
  exact flip_mpr_heq _ _

theorem append_step_heq_old (H : History V I block μ hμ)
    (r : BasicCondition V I block μ) (t : Transition hμ H.last r) (i : Ordinal.{u})
    (hi : Order.succ i ≤ (H.append r t).length) (hi' : Order.succ i ≤ H.length) :
    HEq ((H.append r t).step i hi) (H.step i hi') := by
  have heq : i ≠ H.length := by
    intro h
    rw [h] at hi'
    exact (Order.lt_succ _).not_ge hi'
  simp only [History.append, dite_eq_right heq, flip_mpr_heq]

/-! ### The single flip -/

section Flip

variable (H : History V I block μ hμ) (hH : H.BlockPreserving) (i : Ordinal.{u})
  (hi : Order.succ i ≤ H.length)

/-- The canonical ambient involution of the recorded `i`-th copying map. -/
noncomputable def flipSwap : V ≃ V :=
  (H.step i hi).iso.swapExtension (H.step i hi).fixesOverlap

include hH in
theorem flipSwap_block (x : V) : block (H.flipSwap i hi x) = block x :=
  (H.step i hi).iso.swapExtension_preservesBlocks _ (hH i hi) x

theorem flipSwap_trans_self : (H.flipSwap i hi).trans (H.flipSwap i hi) = Equiv.refl V :=
  Equiv.ext fun x => (H.step i hi).iso.swapExtension_involutive _ x

/-- The prefix `[0, i]`, relabelled by `σ`. -/
noncomputable def flipPrefix : History V I block μ hμ :=
  (H.truncate i ((Order.le_succ i).trans hi)).relabel (H.flipSwap i hi)
    (H.flipSwap_block hH i hi)

theorem flipPrefix_length : (H.flipPrefix hH i hi).length = i := rfl

theorem flipPrefix_last : (H.flipPrefix hH i hi).last = (H.step i hi).right :=
  relabel_eq_of_iso (H.step i hi).iso _ (H.flipSwap_block hH i hi)
    (fun x => (H.step i hi).iso.swapExtension_of_mem_left _ x x.property)

/-- The reversed boundary transition, now starting at the relabelled prefix. -/
noncomputable def flipBoundary :
    Transition hμ (H.flipPrefix hH i hi).last (H.state (Order.succ i) hi) :=
  ((H.step i hi).reverse (hH i hi)).cast (H.flipPrefix_last hH i hi).symm rfl

/-- The new head `[0, i + 1]`. -/
noncomputable def flipHead : History V I block μ hμ :=
  (H.flipPrefix hH i hi).append (H.state (Order.succ i) hi) (H.flipBoundary hH i hi)

theorem flipHead_length : (H.flipHead hH i hi).length = Order.succ i := rfl

theorem flipHead_last :
    (H.flipHead hH i hi).last = H.state (H.flipHead hH i hi).length hi :=
  append_last _ _ _

theorem flipHead_blockPreserving : (H.flipHead hH i hi).BlockPreserving := by
  apply BlockPreserving.append (relabel_blockPreserving (hH.truncate i _) _
    (H.flipSwap_block hH i hi))
  exact (transition_preservesBlocks_iff_of_heq (H.flipPrefix_last hH i hi) rfl
    (Transition.cast_heq _ _ _)).mpr
      (Transition.reverse_preservesBlocks (H.step i hi) (hH i hi))

/-- The single flip at stage `i`. -/
noncomputable def flip : History V I block μ hμ :=
  H.splice (H.flipHead hH i hi) hi (H.flipHead_last hH i hi)

theorem flip_length : (H.flip hH i hi).length = H.length := rfl

theorem flip_last : (H.flip hH i hi).last = H.last :=
  splice_last _ _ _ _

theorem flip_blockPreserving : (H.flip hH i hi).BlockPreserving :=
  splice_blockPreserving _ _ _ _ hH (H.flipHead_blockPreserving hH i hi)

theorem flip_state_le (j : Ordinal.{u}) (hj : j ≤ (H.flip hH i hi).length) (hji : j ≤ i) :
    (H.flip hH i hi).state j hj =
      (H.state j (hji.trans ((Order.le_succ i).trans hi))).relabel (H.flipSwap i hi)
        (H.flipSwap_block hH i hi) := by
  change H.spliceState (H.flipHead hH i hi) j hj = _
  rw [H.spliceState_prefix _ j hj (hji.trans (Order.le_succ i))]
  exact (H.flipPrefix hH i hi).appendedState_old _ j hji

theorem flip_state_ge (j : Ordinal.{u}) (hj : j ≤ (H.flip hH i hi).length)
    (hij : Order.succ i ≤ j) : (H.flip hH i hi).state j hj = H.state j hj :=
  H.spliceState_suffix (H.flipHead hH i hi) hi (H.flipHead_last hH i hi) j hj hij

theorem flip_step_lt (j : Ordinal.{u}) (hj : Order.succ j ≤ (H.flip hH i hi).length)
    (hji : Order.succ j ≤ i) :
    HEq ((H.flip hH i hi).step j hj)
      ((H.step j (hji.trans ((Order.le_succ i).trans hi))).relabel (H.flipSwap i hi)
        (H.flipSwap_block hH i hi)) :=
  (H.spliceStep_heq_prefix _ hi (H.flipHead_last hH i hi) j hj
    (hji.trans (Order.le_succ i))).trans
    (append_step_heq_old _ _ _ j _ hji)

theorem flip_step_eq (hi' : Order.succ i ≤ (H.flip hH i hi).length) :
    HEq ((H.flip hH i hi).step i hi') ((H.step i hi).reverse (hH i hi)) :=
  ((H.spliceStep_heq_prefix _ hi (H.flipHead_last hH i hi) i hi' le_rfl).trans
    (append_step_heq_last _ _ _ _)).trans (Transition.cast_heq _ _ _)

theorem flip_step_gt (j : Ordinal.{u}) (hj : Order.succ j ≤ (H.flip hH i hi).length)
    (hij : i < j) : HEq ((H.flip hH i hi).step j hj) (H.step j hj) :=
  H.spliceStep_heq_suffix _ hi (H.flipHead_last hH i hi) j hj
    (fun h => (Order.succ_le_succ_iff.mp h).not_gt hij)

theorem flip_state_i : (H.flip hH i hi).state i ((Order.le_succ i).trans hi) =
    (H.step i hi).right :=
  (H.flip_state_le hH i hi i _ le_rfl).trans (H.flipPrefix_last hH i hi)

/-- The flipped history records the same canonical involution at stage `i`. -/
theorem flipSwap_flip :
    (H.flip hH i hi).flipSwap i hi = H.flipSwap i hi :=
  (Transition.swap_eq_of_heq (H.flip_state_i hH i hi)
    (H.flip_state_ge hH i hi (Order.succ i) hi le_rfl)
    (H.flip_step_eq hH i hi hi)).trans
    ((H.step i hi).iso.swapExtension_symm_iso (H.step i hi).fixesOverlap)

/-- Flipping twice at the same stage restores every state and witness. -/
theorem flip_flip :
    (H.flip hH i hi).flip (H.flip_blockPreserving hH i hi) i hi = H := by
  set H' := H.flip hH i hi with hH'def
  have hH' : H'.BlockPreserving := H.flip_blockPreserving hH i hi
  have hσ : H'.flipSwap i hi = H.flipSwap i hi := H.flipSwap_flip hH i hi
  have hinv := H.flipSwap_trans_self i hi
  refine ext_of (H := H'.flip hH' i hi) (K := H) rfl ?_ ?_
  · intro j hj hj'
    by_cases hji : j ≤ i
    · rw [H'.flip_state_le hH' i hi j hj hji]
      calc
        (H'.state j _).relabel (H'.flipSwap i hi) (H'.flipSwap_block hH' i hi)
            = ((H.state j (hji.trans ((Order.le_succ i).trans hi))).relabel
                (H.flipSwap i hi) (H.flipSwap_block hH i hi)).relabel
                (H.flipSwap i hi) (H.flipSwap_block hH i hi) :=
              BasicCondition.relabel_congr (H.flip_state_le hH i hi j _ hji) hσ _ _
        _ = (H.state j _).relabel ((H.flipSwap i hi).trans (H.flipSwap i hi))
              (fun x => (H.flipSwap_block hH i hi _).trans (H.flipSwap_block hH i hi x)) :=
              BasicCondition.relabel_relabel _ _ _ _ _
        _ = (H.state j _).relabel (Equiv.refl V) (fun _ => rfl) :=
              BasicCondition.relabel_congr rfl hinv _ _
        _ = H.state j hj' := BasicCondition.relabel_refl _ _
    · have hij : Order.succ i ≤ j := Order.succ_le_of_lt (lt_of_not_ge hji)
      rw [H'.flip_state_ge hH' i hi j hj hij, H.flip_state_ge hH i hi j hj hij]
  · intro j hj hj'
    rcases lt_trichotomy j i with hlt | rfl | hgt
    · have hji : Order.succ j ≤ i := Order.succ_le_of_lt hlt
      refine (H'.flip_step_lt hH' i hi j hj hji).trans ?_
      refine (Transition.relabel_heq_congr
        (H.flip_state_le hH i hi j _ ((Order.le_succ j).trans hji))
        (H.flip_state_le hH i hi (Order.succ j) _ hji)
        (H.flip_step_lt hH i hi j _ hji) hσ _ (H.flipSwap_block hH i hi)).trans ?_
      refine (Transition.relabel_relabel _ _ _ _ _).trans ?_
      refine (Transition.relabel_heq_congr rfl rfl HEq.rfl hinv _ (fun _ => rfl)).trans ?_
      exact Transition.relabel_refl _ _
    · refine (H'.flip_step_eq hH' j hi hj).trans ?_
      refine (Transition.reverse_heq_congr (H.flip_state_i hH j hi)
        (H.flip_state_ge hH j hi (Order.succ j) hi le_rfl)
        (H.flip_step_eq hH j hi hi) _
        (Transition.reverse_preservesBlocks _ (hH j hi))).trans ?_
      exact Transition.reverse_reverse _ _ _
    · exact (H'.flip_step_gt hH' i hi j hj hgt).trans (H.flip_step_gt hH i hi j hj hgt)

end Flip

/-- Prefix naturality: flips commute with pure extension. -/
theorem flip_pureExtends {K N : History V I block μ hμ} (hK : K.BlockPreserving)
    (hN : N.BlockPreserving) (h : PureExtends K N) (i : Ordinal.{u})
    (hi : Order.succ i ≤ K.length) :
    PureExtends (K.flip hK i hi) (N.flip hN i (hi.trans h.length_le)) := by
  have hσ : K.flipSwap i hi = N.flipSwap i (hi.trans h.length_le) :=
    Transition.swap_eq_of_heq (h.state_eq i _) (h.state_eq (Order.succ i) hi)
      (h.step_heq i hi)
  refine ⟨h.length_le, ?_, ?_⟩
  · intro j hj
    by_cases hji : j ≤ i
    · rw [K.flip_state_le hK i hi j hj hji, N.flip_state_le hN i _ j _ hji]
      exact BasicCondition.relabel_congr (h.state_eq j _) hσ _ _
    · have hij : Order.succ i ≤ j := Order.succ_le_of_lt (lt_of_not_ge hji)
      rw [K.flip_state_ge hK i hi j hj hij, N.flip_state_ge hN i _ j _ hij]
      exact h.state_eq j hj
  · intro j hj
    rcases lt_trichotomy j i with hlt | rfl | hgt
    · have hji : Order.succ j ≤ i := Order.succ_le_of_lt hlt
      refine (K.flip_step_lt hK i hi j hj hji).trans ?_
      refine HEq.trans ?_ (N.flip_step_lt hN i _ j _ hji).symm
      exact Transition.relabel_heq_congr (h.state_eq j _) (h.state_eq (Order.succ j) _)
        (h.step_heq j _) hσ _ _
    · refine (K.flip_step_eq hK j hi hj).trans ?_
      refine HEq.trans ?_ (N.flip_step_eq hN j _ _).symm
      exact Transition.reverse_heq_congr (h.state_eq j _) (h.state_eq (Order.succ j) hi)
        (h.step_heq j hi) _ _
    · refine (K.flip_step_gt hK i hi j hj hgt).trans ?_
      refine HEq.trans ?_ (N.flip_step_gt hN i _ j _ hgt).symm
      exact h.step_heq j hj

end Erdos1220.History

#print axioms Erdos1220.History.ext_of
#print axioms Erdos1220.History.PureExtends.eq_of_length_le
#print axioms Erdos1220.History.relabel_trans
#print axioms Erdos1220.History.relabel_refl
#print axioms Erdos1220.History.relabel_truncate
#print axioms Erdos1220.History.flip_last
#print axioms Erdos1220.History.flip_blockPreserving
#print axioms Erdos1220.History.flip_flip
#print axioms Erdos1220.History.flip_pureExtends
