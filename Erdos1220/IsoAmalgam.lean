import Erdos1220.WeakOrder

/-!
# Amalgamation of a history with a relabelled copy (Sh:258 §3.8, §3.9)

Let `H` be a block-preserving history and `e` a block-preserving permutation
of the vertices fixing the overlap of the two terminal supports of `H` and
`K := H.relabel e`. Append to `H` the recorded amalgamation of `H.last` with
its copy `K.last`, witnessed by the support isomorphism induced by `e`. The
result `U` purely extends `H`. Flipping its final construction stage gives a
history whose pure prefix is `H.relabel σ`, where `σ` is the canonical swap;
since `σ` agrees with `e` on the terminal support, this prefix is `K`. Hence
`H` and `K` are both weakly below `U`. The final amalgam may be the all-red
one, or may carry one chosen blue (green) cross edge.
-/

open Cardinal Set Order

universe u

namespace Erdos1220.BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

/-- The identity tame isomorphism. -/
def TameIso.refl (p : BasicCondition V I block μ) : TameIso p p where
  toEquiv := Equiv.refl _
  blue_iff _ _ := Iff.rfl
  block_iff _ _ := Iff.rfl

/-- A relabelling fixing the support pointwise changes nothing. -/
theorem relabel_eq_self (p : BasicCondition V I block μ) (f : V ≃ V)
    (hf : ∀ x, block (f x) = block x) (h : ∀ x ∈ p.support, f x = x) :
    p.relabel f hf = p :=
  relabel_eq_of_iso (TameIso.refl p) f hf (fun x => h x x.2)

namespace Transition

/-- Extensionality of recorded transitions up to transport of endpoints. -/
theorem heq_of {p r p' r' : BasicCondition V I block μ} (hp : p = p') (hr : r = r')
    (t : Transition hμ p r) (t' : Transition hμ p' r') (hright : t.right = t'.right)
    (hiso : ∀ x (hx : x ∈ p.support) (hx' : x ∈ p'.support),
      (t.iso.toEquiv ⟨x, hx⟩ : V) = t'.iso.toEquiv ⟨x, hx'⟩)
    (hedge : t.edge.map (fun c => (c.left, c.right)) =
      t'.edge.map (fun c => (c.left, c.right))) :
    HEq t t' := by
  subst hp
  subst hr
  cases t with
  | mk R iso fo fsb edge ss req =>
  cases t' with
  | mk R' iso' fo' fsb' edge' ss' req' =>
  dsimp only at hright hiso hedge
  subst hright
  have hiso' : iso = iso' := by
    cases iso with
    | mk f fb fk =>
    cases iso' with
    | mk f' fb' fk' =>
    have : f = f' := Equiv.ext fun x => Subtype.ext (hiso x.1 x.2 x.2)
    subst this
    rfl
  subst hiso'
  have hedge' : edge = edge' := by
    cases edge with
    | none =>
      cases edge' with
      | none => rfl
      | some c' => simp at hedge
    | some c =>
      cases edge' with
      | none => simp at hedge
      | some c' =>
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hedge
        obtain ⟨h1, h2⟩ := hedge
        cases c
        cases c'
        dsimp only at h1 h2
        subst h1
        subst h2
        rfl
  subst hedge'
  rfl

/-- Relabelling by a permutation fixing the result support changes nothing. -/
theorem relabel_heq_self {p r : BasicCondition V I block μ} (t : Transition hμ p r)
    (f : V ≃ V) (hf : ∀ x, block (f x) = block x) (h : ∀ x ∈ r.support, f x = x) :
    HEq (t.relabel f hf) t := by
  have hp : ∀ x ∈ p.support, f x = x := fun x hx => h x (t.extends_left.1 hx)
  have hR : ∀ x ∈ t.right.support, f x = x := fun x hx => h x (by
    rw [t.support_eq]
    exact Or.inr hx)
  refine heq_of (relabel_eq_self p f hf hp) (relabel_eq_self r f hf h) _ _
    (relabel_eq_self t.right f hf hR) ?_ ?_
  · intro x hx hx'
    change f (t.iso.toEquiv ⟨f.symm x, hx⟩ : V) = _
    have hsx : f.symm x = x := f.symm_apply_eq.mpr (hp x hx').symm
    have hsub : (⟨f.symm x, hx⟩ : p.support) = ⟨x, hx'⟩ := Subtype.ext hsx
    rw [hsub]
    exact hR _ (t.iso.toEquiv ⟨x, hx'⟩).2
  · change (t.edge.map fun a => a.relabel f hf).map _ = t.edge.map _
    cases t.edge with
    | none => rfl
    | some c =>
      exact congrArg some (Prod.ext (hp _ c.left_mem) (hR _ c.right_mem))

end Transition

/-- The recorded amalgamation of a condition with its relabelled copy. -/
def isoTransition (p : BasicCondition V I block μ) (e : V ≃ V)
    (he : ∀ x, block (e x) = block x)
    (hfix : ∀ x ∈ p.support, x ∈ (p.relabel e he).support → e x = x)
    (edge : Option (CrossEdge p (p.relabel e he))) :
    Transition hμ p (amalgamResult p (p.relabel e he) hμ edge) where
  right := p.relabel e he
  iso := p.relabelIso e he
  fixesOverlap x hx := hfix x x.2 hx
  fixesSharedBlocks := (p.relabelIso_preservesBlocks e he).fixesSharedBlocks
  edge := edge
  sourceSeparated c _ :=
    c.sourceSeparated_of_preservesBlocks _ (p.relabelIso_preservesBlocks e he)
  result_eq := rfl

end Erdos1220.BasicCondition

namespace Erdos1220.History

open BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

/-- A relabelling fixing the terminal support pointwise fixes the whole
history, including every recorded witness. -/
theorem relabel_eq_self (H : History V I block μ hμ) (f : V ≃ V)
    (hf : ∀ x, block (f x) = block x) (h : ∀ x ∈ H.last.support, f x = x) :
    H.relabel f hf = H :=
  ext_of rfl
    (fun i hi _ => BasicCondition.relabel_eq_self _ f hf
      fun x hx => h x ((H.state_extends_last i hi).1 hx))
    (fun i hi _ => Transition.relabel_heq_self _ f hf
      fun x hx => h x ((H.state_extends_last _ hi).1 hx))

/-- Relabelling a history only depends on the values on its terminal support. -/
theorem relabel_eq_of_eqOn (H : History V I block μ hμ) {e e' : V ≃ V}
    (he : ∀ x, block (e x) = block x) (he' : ∀ x, block (e' x) = block x)
    (h : ∀ x ∈ H.last.support, e x = e' x) : H.relabel e he = H.relabel e' he' := by
  have hg : ∀ x, block ((e.trans e'.symm) x) = block x :=
    fun x => (symm_block e' he' (e x)).trans (he x)
  calc
    H.relabel e he = H.relabel ((e.trans e'.symm).trans e')
        (fun x => (he' ((e.trans e'.symm) x)).trans (hg x)) :=
      relabel_congr H (by ext x; simp) _ _
    _ = (H.relabel (e.trans e'.symm) hg).relabel e' he' := (relabel_trans H _ _ hg he').symm
    _ = H.relabel e' he' := by
      rw [relabel_eq_self H _ hg (fun x hx => by simp [h x hx])]

theorem pureExtends_append (H : History V I block μ hμ) (r : BasicCondition V I block μ)
    (t : Transition hμ H.last r) : PureExtends H (H.append r t) :=
  ⟨Order.le_succ _, fun i hi => (append_preserves_state H r t i hi).symm,
    fun i hi => (append_step_heq_old H r t i _ hi).symm⟩

end Erdos1220.History

namespace Erdos1220.BPHistory

open BasicCondition History

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

/-- The relabelled copy of a block-preserving history. -/
def relabelBP (H : BPHistory V I block μ hμ) (e : V ≃ V)
    (he : ∀ x, block (e x) = block x) : BPHistory V I block μ hμ :=
  ⟨H.1.relabel e he, relabel_blockPreserving H.2 e he⟩

section Amalgam

variable (H : BPHistory V I block μ hμ) (e : V ≃ V) (he : ∀ x, block (e x) = block x)
  (hfix : ∀ x ∈ H.1.last.support, x ∈ (H.1.relabel e he).last.support → e x = x)
  (edge : Option (CrossEdge H.1.last (H.1.relabel e he).last))

/-- Append the amalgamation of `H.last` with its copy `(H.relabel e).last`. -/
noncomputable def isoAmalgam : BPHistory V I block μ hμ :=
  ⟨H.1.append _ (isoTransition H.1.last e he hfix edge),
    H.2.append _ _ (H.1.last.relabelIso_preservesBlocks e he)⟩

theorem isoAmalgam_last :
    (isoAmalgam H e he hfix edge).1.last =
      amalgamResult H.1.last (H.1.relabel e he).last hμ edge :=
  append_last _ _ _

theorem isoAmalgam_pure : PureExtends H.1 (isoAmalgam H e he hfix edge).1 :=
  pureExtends_append _ _ _

theorem weakExtends_isoAmalgam_left : WeakExtends H (isoAmalgam H e he hfix edge) :=
  WeakExtends.of_pure (isoAmalgam_pure H e he hfix edge)

/-- The relabelled copy is weakly below the amalgam: flip the last stage. -/
theorem weakExtends_isoAmalgam_right :
    WeakExtends (relabelBP H e he) (isoAmalgam H e he hfix edge) := by
  let U := isoAmalgam H e he hfix edge
  have hi : Order.succ H.1.length ≤ U.1.length := le_rfl
  let t := isoTransition (hμ := hμ) H.1.last e he hfix edge
  have hσ : U.1.flipSwap H.1.length hi = t.iso.swapExtension t.fixesOverlap :=
    Transition.swap_eq_of_heq (append_preserves_state H.1 _ t H.1.length le_rfl)
      (H.1.appendedState_new _) (append_step_heq_last H.1 _ t hi)
  have hagree : ∀ x ∈ H.1.last.support, U.1.flipSwap H.1.length hi x = e x := by
    intro x hx
    rw [hσ]
    exact t.iso.swapExtension_of_mem_left t.fixesOverlap x hx
  have hrel : H.1.relabel (U.1.flipSwap H.1.length hi)
      (U.1.flipSwap_block U.2 H.1.length hi) = H.1.relabel e he :=
    relabel_eq_of_eqOn H.1 _ he hagree
  have hpure : PureExtends (H.1.relabel (U.1.flipSwap H.1.length hi)
      (U.1.flipSwap_block U.2 H.1.length hi)) (U.flip H.1.length hi).1 := by
    refine ⟨Order.le_succ _, ?_, ?_⟩
    · intro j hj
      refine Eq.trans ?_ (U.1.flip_state_le U.2 _ hi j _ hj).symm
      exact BasicCondition.relabel_congr (append_preserves_state H.1 _ t j hj).symm rfl
        (U.1.flipSwap_block U.2 _ hi) (U.1.flipSwap_block U.2 _ hi)
    · intro j hj
      refine HEq.trans ?_ (U.1.flip_step_lt U.2 _ hi j _ hj).symm
      exact Transition.relabel_heq_congr
        (append_preserves_state H.1 _ t j ((Order.le_succ j).trans hj)).symm
        (append_preserves_state H.1 _ t (Order.succ j) hj).symm
        (append_step_heq_old H.1 _ t j _ hj).symm rfl _ _
  refine ⟨U.flip H.1.length hi, FlipEquiv.flip U _ hi, ?_⟩
  show PureExtends (H.1.relabel e he) _
  rw [← hrel]
  exact hpure

include hfix in
/-- **Amalgamation of isomorphic histories (§3.8).** -/
theorem exists_isoAmalgam :
    ∃ U : BPHistory V I block μ hμ, WeakExtends H U ∧ WeakExtends (relabelBP H e he) U ∧
      PureExtends H.1 U.1 ∧
      U.1.last = amalgamResult H.1.last (H.1.relabel e he).last hμ edge :=
  ⟨isoAmalgam H e he hfix edge, weakExtends_isoAmalgam_left H e he hfix edge,
    weakExtends_isoAmalgam_right H e he hfix edge, isoAmalgam_pure H e he hfix edge,
    isoAmalgam_last H e he hfix edge⟩

end Amalgam

/-- **Compatibility, all-red version.** A history and an overlap-fixing
relabelled copy have a common weak extension whose terminal condition is the
red amalgam: no new blue edge between the two copies. -/
theorem exists_red_isoAmalgam (H : BPHistory V I block μ hμ) (e : V ≃ V)
    (he : ∀ x, block (e x) = block x)
    (hfix : ∀ x ∈ H.1.last.support, x ∈ (H.1.relabel e he).last.support → e x = x) :
    ∃ U : BPHistory V I block μ hμ, WeakExtends H U ∧ WeakExtends (relabelBP H e he) U ∧
      U.1.last = redAmalgam H.1.last (H.1.relabel e he).last hμ :=
  let ⟨U, h1, h2, _, h3⟩ := exists_isoAmalgam H e he hfix none
  ⟨U, h1, h2, h3⟩

/-- **Compatibility, green version (§3.9).** A chosen admissible cross pair
`x ∈ H.last \ K.last`, `y ∈ K.last \ H.last` in different blocks becomes
blue in a common weak extension. -/
theorem exists_green_isoAmalgam (H : BPHistory V I block μ hμ) (e : V ≃ V)
    (he : ∀ x, block (e x) = block x)
    (hfix : ∀ x ∈ H.1.last.support, x ∈ (H.1.relabel e he).last.support → e x = x)
    (x y : V) (hx : x ∈ H.1.last.support) (hxK : x ∉ (H.1.relabel e he).last.support)
    (hy : y ∈ (H.1.relabel e he).last.support) (hyH : y ∉ H.1.last.support)
    (hxy : block x ≠ block y) :
    ∃ U : BPHistory V I block μ hμ, WeakExtends H U ∧ WeakExtends (relabelBP H e he) U ∧
      U.1.last.blue x y ∧
      ∀ a b, U.1.last.blue a b ↔
        (H.1.last.blue a b ∨ (H.1.relabel e he).last.blue a b) ∨
          ((a = x ∧ b = y) ∨ (a = y ∧ b = x)) := by
  let c : CrossEdge H.1.last (H.1.relabel e he).last :=
    ⟨x, y, hx, hxK, hy, hyH, hxy⟩
  obtain ⟨U, h1, h2, _, h3⟩ := exists_isoAmalgam H e he hfix (some c)
  refine ⟨U, h1, h2, ?_, ?_⟩
  · rw [h3]
    exact blueAmalgam_has_chosen_edge _ _ hμ c
  · intro a b
    rw [h3]
    exact Iff.rfl

end Erdos1220.BPHistory

#print axioms Erdos1220.History.relabel_eq_self
#print axioms Erdos1220.History.relabel_eq_of_eqOn
#print axioms Erdos1220.BPHistory.weakExtends_isoAmalgam_right
#print axioms Erdos1220.BPHistory.exists_isoAmalgam
#print axioms Erdos1220.BPHistory.exists_red_isoAmalgam
#print axioms Erdos1220.BPHistory.exists_green_isoAmalgam
