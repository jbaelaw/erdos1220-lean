import Erdos1220.DeltaSystem
import Erdos1220.Relabel
import Erdos1220.SwapExtension

/-!
# Blueprints of histories and the `(2^μ)⁺`-chain-condition core (Sh:258 §3.8, no flips)

All data of a history `H` (every state's support and blue relation, every transition's `right`
condition, its copying isomorphism and its edge) lives inside `S_H := H.last.support`
(`rel_supp`).  We code `S_H` injectively into the fixed type `Coord μ := μ.out` (`code H`), code
the stages `i ≤ H.length` injectively into `Coord μ` as well (`stageCode`, depending only on the
length), and record:

* the length (an ordinal `< μ⁺`),
* the block label of every coded support point (`blk H : Coord μ → Option I`),
* all six relations of every stage, coded as one subset of `Coord μ × ℕ × Coord μ × Coord μ`.

This `blueprint` takes at most `2^μ` values when `#I ≤ 2^μ` (`mk_blueprint_le`).

Key lemma (`relabel_of_blueprint_eq`): if `blueprint H = blueprint K` and the codes of `H` and
`K` agree on `S_H ∩ S_K`, then the code-matching bijection `S_H ≃ S_K` fixes the overlap and
preserves blocks, and its canonical involutive extension `e : V ≃ V` (`TameIso.swapExtension`)
is block-preserving, fixes `S_H ∩ S_K` pointwise, maps `S_H` onto `S_K`, and satisfies
`H.relabel e he = K` (equality of histories, including all recorded transition witnesses).

Combined with the Δ-system lemma (`cc_histories`): among `(2^μ)⁺` histories there are two
distinct ones related in this way.  Only the coding bijection is used (no well-order on `V`).
-/

open Cardinal Set Order

universe u

namespace Erdos1220.HistoryBlueprint

open BasicCondition Erdos1220.DeltaSystem

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

/-! ### Extensionality for transitions and histories -/

theorem transition_ext {p r : BasicCondition V I block μ} {t t' : Transition hμ p r}
    (h1 : t.right = t'.right)
    (h2 : ∀ x : p.support, (t.iso.toEquiv x : V) = t'.iso.toEquiv x)
    (h3 : ∀ a b : V, (∃ c, t.edge = some c ∧ a = c.left ∧ b = c.right) ↔
      (∃ c, t'.edge = some c ∧ a = c.left ∧ b = c.right)) : t = t' := by
  cases t with
  | mk right iso fo fs edge ss re =>
  cases t' with
  | mk right' iso' fo' fs' edge' ss' re' =>
  dsimp only at h1 h2 h3
  subst h1
  have hiso : iso = iso' := by
    cases iso with
    | mk f bf bl =>
    cases iso' with
    | mk f' bf' bl' =>
    have : f = f' := Equiv.ext fun x => Subtype.ext (h2 x)
    subst this
    rfl
  subst hiso
  have hedge : edge = edge' := by
    cases edge with
    | none =>
      cases edge' with
      | none => rfl
      | some c =>
        exfalso
        obtain ⟨c', hc', -, -⟩ := (h3 c.left c.right).mpr ⟨c, rfl, rfl, rfl⟩
        cases hc'
    | some c =>
      cases edge' with
      | none =>
        exfalso
        obtain ⟨c', hc', -, -⟩ := (h3 c.left c.right).mp ⟨c, rfl, rfl, rfl⟩
        cases hc'
      | some c' =>
        obtain ⟨d, hd, hl, hr⟩ := (h3 c.left c.right).mp ⟨c, rfl, rfl, rfl⟩
        cases hd
        cases c with
        | mk l r lm lnm rm rnm bn =>
        cases c' with
        | mk l' r' lm' lnm' rm' rnm' bn' =>
        dsimp only at hl hr
        subst hl
        subst hr
        rfl
  subst hedge
  rfl

theorem history_ext {H K : History V I block μ hμ} (hlen : H.length = K.length)
    (hstate : ∀ i (hi : i ≤ H.length) (hi' : i ≤ K.length), H.state i hi = K.state i hi')
    (hright : ∀ i (hs : succ i ≤ H.length) (hs' : succ i ≤ K.length),
      (H.step i hs).right = (K.step i hs').right)
    (hiso : ∀ i (hs : succ i ≤ H.length) (hs' : succ i ≤ K.length) (x : V)
      (hx : x ∈ (H.state i ((Order.le_succ i).trans hs)).support)
      (hx' : x ∈ (K.state i ((Order.le_succ i).trans hs')).support),
      ((H.step i hs).iso.toEquiv ⟨x, hx⟩ : V) = (K.step i hs').iso.toEquiv ⟨x, hx'⟩)
    (hedge : ∀ i (hs : succ i ≤ H.length) (hs' : succ i ≤ K.length) (a b : V),
      (∃ c, (H.step i hs).edge = some c ∧ a = c.left ∧ b = c.right) ↔
        (∃ c, (K.step i hs').edge = some c ∧ a = c.left ∧ b = c.right)) : H = K := by
  cases H with
  | mk len lt st inc ir ibi int step ls lb =>
  cases K with
  | mk len' lt' st' inc' ir' ibi' int' step' ls' lb' =>
  dsimp only at hlen hstate hright hiso hedge
  subst hlen
  have hst : st = st' := funext fun i => funext fun hi => hstate i hi hi
  subst hst
  have hstep : step = step' := funext fun i => funext fun hs =>
    transition_ext (hright i hs hs) (fun x => hiso i hs hs x x.2 x.2) (hedge i hs hs)
  subst hstep
  rfl

/-! ### The six relations of a stage, all supported in the last support -/

/-- The data of stage `i` as six binary relations on `V`: state support (diagonal), state blue,
right support (diagonal), right blue, graph of the copying isomorphism, and the new edge. -/
def relN (H : History V I block μ hμ) (i : Ordinal.{u}) : ℕ → V → V → Prop
  | 0 => fun x y => ∃ hi : i ≤ H.length, x ∈ (H.state i hi).support ∧ y = x
  | 1 => fun x y => ∃ hi : i ≤ H.length, (H.state i hi).blue x y
  | 2 => fun x y => ∃ hs : succ i ≤ H.length, x ∈ (H.step i hs).right.support ∧ y = x
  | 3 => fun x y => ∃ hs : succ i ≤ H.length, (H.step i hs).right.blue x y
  | 4 => fun x y => ∃ hs : succ i ≤ H.length,
      ∃ hx : x ∈ (H.state i ((Order.le_succ i).trans hs)).support,
        ((H.step i hs).iso.toEquiv ⟨x, hx⟩ : V) = y
  | 5 => fun x y => ∃ hs : succ i ≤ H.length, ∃ c,
      (H.step i hs).edge = some c ∧ x = c.left ∧ y = c.right
  | _ => fun _ _ => False

lemma state_sub_last (H : History V I block μ hμ) (j : Ordinal.{u}) (hj : j ≤ H.length) :
    (H.state j hj).support ⊆ H.last.support :=
  (H.state_extends_last j hj).1

lemma right_sub_last (H : History V I block μ hμ) (j : Ordinal.{u})
    (hs : succ j ≤ H.length) : (H.step j hs).right.support ⊆ H.last.support := by
  intro z hz
  apply state_sub_last H _ hs
  rw [(H.step j hs).support_eq]
  exact Or.inr hz

/-- **All history data lives in the last support.** -/
lemma rel_supp (H : History V I block μ hμ) (i : Ordinal.{u}) (n : ℕ) {x y : V}
    (h : relN H i n x y) : x ∈ H.last.support ∧ y ∈ H.last.support := by
  rcases n with _ | _ | _ | _ | _ | _ | n
  · obtain ⟨hi, hx, rfl⟩ := h
    exact ⟨state_sub_last H i hi hx, state_sub_last H i hi hx⟩
  · obtain ⟨hi, hb⟩ := h
    obtain ⟨h1, h2⟩ := (H.state i hi).blue_support hb
    exact ⟨state_sub_last H i hi h1, state_sub_last H i hi h2⟩
  · obtain ⟨hs, hx, rfl⟩ := h
    exact ⟨right_sub_last H i hs hx, right_sub_last H i hs hx⟩
  · obtain ⟨hs, hb⟩ := h
    obtain ⟨h1, h2⟩ := (H.step i hs).right.blue_support hb
    exact ⟨right_sub_last H i hs h1, right_sub_last H i hs h2⟩
  · obtain ⟨hs, hx, rfl⟩ := h
    exact ⟨state_sub_last H i _ hx,
      right_sub_last H i hs ((H.step i hs).iso.toEquiv ⟨x, hx⟩).2⟩
  · obtain ⟨hs, c, -, rfl, rfl⟩ := h
    exact ⟨state_sub_last H i _ c.left_mem, right_sub_last H i hs c.right_mem⟩
  · exact False.elim h

/-! ### Coding -/

/-- The fixed coordinate type of size `μ`. -/
abbrev Coord (μ : Cardinal.{u}) : Type u := μ.out

lemma mk_coord (μ : Cardinal.{u}) : #(Coord μ) = μ := mk_out μ

lemma coord_nonempty (hμ : ℵ₀ ≤ μ) : Nonempty (Coord μ) :=
  Cardinal.mk_ne_zero_iff.mp (by rw [mk_coord]; exact (aleph0_pos.trans_le hμ).ne')

lemma exists_code (hμ : ℵ₀ ≤ μ) (s : Set V) (hs : #s ≤ μ) :
    ∃ f : V → Coord μ, InjOn f s := by
  classical
  obtain ⟨emb⟩ := (Cardinal.le_def s (Coord μ)).mp (by rw [mk_coord]; exact hs)
  haveI := coord_nonempty hμ
  refine ⟨fun x => if hx : x ∈ s then emb ⟨x, hx⟩ else Classical.choice inferInstance, ?_⟩
  intro x hx y hy hxy
  simp only [dite_eq_left hx, dite_eq_left hy] at hxy
  exact congrArg Subtype.val (emb.injective hxy)

/-- Injective code of the last support of `H`. -/
noncomputable def code (H : History V I block μ hμ) : V → Coord μ :=
  Classical.choose (exists_code hμ H.last.support H.last.small)

lemma code_injOn (H : History V I block μ hμ) : InjOn (code H) H.last.support :=
  Classical.choose_spec (exists_code hμ H.last.support H.last.small)

lemma exists_stageCode (hμ : ℵ₀ ≤ μ) (ℓ : Ordinal.{u}) (hℓ : ℓ < (succ μ).ord) :
    ∃ f : Ordinal.{u} → Coord μ, InjOn f (Iic ℓ) := by
  classical
  have := coord_nonempty hμ
  have h1 : (succ ℓ).card ≤ μ := by
    rw [Ordinal.card_succ]
    exact add_le_of_le hμ (card_lt_succ_ord_iff.mp hℓ) (one_le_aleph0.trans hμ)
  have hcard : Cardinal.lift.{u} #(Iic ℓ) ≤ Cardinal.lift.{u + 1} #(Coord μ) := by
    rw [← Order.Iio_succ, Cardinal.mk_Iio_ordinal, mk_coord, Cardinal.lift_lift]
    exact Cardinal.lift_le.mpr h1
  obtain ⟨emb⟩ := Cardinal.lift_mk_le'.mp hcard
  refine ⟨fun x => if hx : x ∈ Iic ℓ then emb ⟨x, hx⟩ else Classical.choice inferInstance, ?_⟩
  intro x hx y hy hxy
  simp only [dite_eq_left hx, dite_eq_left hy] at hxy
  exact congrArg Subtype.val (emb.injective hxy)

open Classical in
/-- Code of the stages `≤ ℓ`; depends only on the length `ℓ`. -/
noncomputable def stageCode (hμ : ℵ₀ ≤ μ) (ℓ : Ordinal.{u}) : Ordinal.{u} → Coord μ :=
  if h : ∃ f : Ordinal.{u} → Coord μ, InjOn f (Iic ℓ) then Classical.choose h
  else fun _ => Classical.choice (coord_nonempty hμ)

lemma stageCode_injOn (hμ : ℵ₀ ≤ μ) (ℓ : Ordinal.{u}) (hℓ : ℓ < (succ μ).ord) :
    InjOn (stageCode hμ ℓ) (Iic ℓ) := by
  have h := exists_stageCode hμ ℓ hℓ
  unfold stageCode
  rw [dif_pos h]
  exact Classical.choose_spec h

open Classical in
/-- Block labels of coded support points. -/
noncomputable def blk (H : History V I block μ hμ) : Coord μ → Option I := fun c =>
  if h : ∃ x, x ∈ H.last.support ∧ code H x = c then some (block (Classical.choose h)) else none

lemma blk_code (H : History V I block μ hμ) {x : V} (hx : x ∈ H.last.support) :
    blk H (code H x) = some (block x) := by
  have h : ∃ x', x' ∈ H.last.support ∧ code H x' = code H x := ⟨x, hx, rfl⟩
  unfold blk
  rw [dif_pos h]
  have hs := Classical.choose_spec h
  rw [code_injOn H hs.1 hx hs.2]

/-- All stage data, coded. -/
def stagePart (H : History V I block μ hμ) : Set (Coord μ × ℕ × Coord μ × Coord μ) :=
  {q | ∃ i, i ≤ H.length ∧ stageCode hμ H.length i = q.1 ∧
    ∃ x y, relN H i q.2.1 x y ∧ code H x = q.2.2.1 ∧ code H y = q.2.2.2}

lemma mem_stagePart (H : History V I block μ hμ) {i : Ordinal.{u}} (hi : i ≤ H.length)
    (n : ℕ) (c d : Coord μ) :
    (stageCode hμ H.length i, n, c, d) ∈ stagePart H ↔
      ∃ x y, relN H i n x y ∧ code H x = c ∧ code H y = d := by
  constructor
  · rintro ⟨i', hi', hc, h⟩
    have := stageCode_injOn hμ H.length H.length_lt hi' hi hc
    subst this
    exact h
  · intro h
    exact ⟨i, hi, rfl, h⟩

/-- The blueprint type. -/
abbrev Blueprint (I : Type u) (μ : Cardinal.{u}) : Type (u + 1) :=
  Iio (Order.succ μ).ord × (Coord μ → Option I) × Set (Coord μ × ℕ × Coord μ × Coord μ)

/-- The blueprint of a history. -/
noncomputable def blueprint (H : History V I block μ hμ) : Blueprint I μ :=
  (⟨H.length, H.length_lt⟩, blk H, stagePart H)

/-- **Counting blueprints**: at most `2^μ` (for `#I ≤ 2^μ`). -/
theorem mk_blueprint_le (hμ : ℵ₀ ≤ μ) (hI : #I ≤ 2 ^ μ) :
    #(Blueprint I μ) ≤ Cardinal.lift.{u + 1} (2 ^ μ) := by
  have h2 : ℵ₀ ≤ 2 ^ μ := hμ.trans (cantor μ).le
  have hC := mk_coord μ
  have hB : #(Coord μ → Option I) ≤ 2 ^ μ :=
    mk_arrow_le_two_pow hμ hC.le
      (by rw [mk_option]; exact add_le_of_le h2 hI (one_le_aleph0.trans h2))
  have hX : #(Coord μ × ℕ × Coord μ × Coord μ) ≤ μ := by
    have h1 : #(Coord μ × ℕ × Coord μ × Coord μ) = μ * (ℵ₀ * (μ * μ)) := by
      simp [hC]
    rw [h1, mul_eq_self hμ, aleph0_mul_eq hμ, mul_eq_self hμ]
  have hS : #(Set (Coord μ × ℕ × Coord μ × Coord μ)) ≤ 2 ^ μ := by
    rw [mk_set]
    exact power_le_power_left two_ne_zero hX
  have hQ : #((Coord μ → Option I) × Set (Coord μ × ℕ × Coord μ × Coord μ)) ≤ 2 ^ μ := by
    rw [← mul_def]
    exact (mul_le_mul' hB hS).trans (mul_eq_self h2).le
  rw [mk_prod]
  calc Cardinal.lift.{u} #(Iio (Order.succ μ).ord) *
        Cardinal.lift.{u + 1} #((Coord μ → Option I) × Set (Coord μ × ℕ × Coord μ × Coord μ))
      ≤ Cardinal.lift.{u + 1} (2 ^ μ) * Cardinal.lift.{u + 1} (2 ^ μ) :=
        mul_le_mul' (by simpa using mk_Iio_succ_ord_le (μ := μ)) (Cardinal.lift_le.mpr hQ)
    _ = Cardinal.lift.{u + 1} (2 ^ μ) := by rw [← Cardinal.lift_mul, mul_eq_self h2]

/-! ### Transport -/

/-- Generic transport of a coded relation along a code-matching bijection. -/
lemma transport {α γ : Type*} (e : α ≃ α) (cH cK : α → γ) (SK SH : Set α)
    (hK : InjOn cK SK) (he : ∀ x ∈ SH, e x ∈ SK ∧ cK (e x) = cH x)
    (r s : α → α → Prop) (hr : ∀ x y, r x y → x ∈ SH ∧ y ∈ SH)
    (hs : ∀ x y, s x y → x ∈ SK ∧ y ∈ SK)
    (hcode : ∀ c d, (∃ x y, r x y ∧ cH x = c ∧ cH y = d) ↔
      (∃ x y, s x y ∧ cK x = c ∧ cK y = d))
    (y₁ y₂ : α) : s y₁ y₂ ↔ r (e.symm y₁) (e.symm y₂) := by
  constructor
  · intro hsy
    obtain ⟨hy₁, hy₂⟩ := hs _ _ hsy
    obtain ⟨x₁, x₂, hr', h₁, h₂⟩ := (hcode _ _).mpr ⟨y₁, y₂, hsy, rfl, rfl⟩
    obtain ⟨hx₁, hx₂⟩ := hr _ _ hr'
    have e₁ : e x₁ = y₁ := hK (he x₁ hx₁).1 hy₁ ((he x₁ hx₁).2.trans h₁)
    have e₂ : e x₂ = y₂ := hK (he x₂ hx₂).1 hy₂ ((he x₂ hx₂).2.trans h₂)
    rw [← e₁, ← e₂, e.symm_apply_apply, e.symm_apply_apply]
    exact hr'
  · intro hry
    obtain ⟨hx₁, hx₂⟩ := hr _ _ hry
    obtain ⟨z₁, z₂, hsz, h₁, h₂⟩ := (hcode _ _).mp ⟨_, _, hry, rfl, rfl⟩
    obtain ⟨hz₁, hz₂⟩ := hs _ _ hsz
    have k₁ := he _ hx₁
    have k₂ := he _ hx₂
    rw [e.apply_symm_apply] at k₁ k₂
    have hz₁y : z₁ = y₁ := hK hz₁ k₁.1 (h₁.trans k₁.2.symm)
    have hz₂y : z₂ = y₂ := hK hz₂ k₂.1 (h₂.trans k₂.2.symm)
    rw [← hz₁y, ← hz₂y]
    exact hsz

lemma edge_map_iff {p q : BasicCondition V I block μ} (e : V ≃ V)
    (he : ∀ x, block (e x) = block x) (o : Option (CrossEdge p q)) (a b : V) :
    (∃ c, o.map (fun c => c.relabel e he) = some c ∧ a = c.left ∧ b = c.right) ↔
      (∃ c, o = some c ∧ e.symm a = c.left ∧ e.symm b = c.right) := by
  cases o with
  | none =>
    constructor
    · rintro ⟨c, hc, -⟩
      cases hc
    · rintro ⟨c, hc, -⟩
      cases hc
  | some c =>
    constructor
    · rintro ⟨c', hc', ha, hb⟩
      cases hc'
      subst ha
      subst hb
      exact ⟨c, rfl, e.symm_apply_apply c.left, e.symm_apply_apply c.right⟩
    · rintro ⟨c', hc', ha, hb⟩
      cases hc'
      refine ⟨_, rfl, ?_, ?_⟩
      · show a = e c.left
        rw [← ha, e.apply_symm_apply]
      · show b = e c.right
        rw [← hb, e.apply_symm_apply]

/-- If the six stage relations of `K` are those of `H` transported along `e`, then
`K = H.relabel e`. -/
theorem relabel_eq_of_key {H K : History V I block μ hμ} (e : V ≃ V)
    (he : ∀ x, block (e x) = block x) (hlen : H.length = K.length)
    (key : ∀ i, i ≤ H.length → ∀ n y₁ y₂,
      relN K i n y₁ y₂ ↔ relN H i n (e.symm y₁) (e.symm y₂)) :
    H.relabel e he = K := by
  apply history_ext (H := H.relabel e he) hlen
  · intro i hi hi'
    apply eq_of_support_blue
    · ext y
      have k := key i hi 0 y y
      constructor
      · intro hy
        obtain ⟨_, h, -⟩ := k.mpr ⟨hi, hy, rfl⟩
        exact h
      · intro hy
        obtain ⟨_, h, -⟩ := k.mp ⟨hi', hy, rfl⟩
        exact h
    · intro x y
      have k := key i hi 1 x y
      constructor
      · intro h
        obtain ⟨_, h'⟩ := k.mpr ⟨hi, h⟩
        exact h'
      · intro h
        obtain ⟨_, h'⟩ := k.mp ⟨hi', h⟩
        exact h'
  · intro i hs hs'
    have hi : i ≤ H.length := (Order.le_succ i).trans hs
    apply eq_of_support_blue
    · ext y
      have k := key i hi 2 y y
      constructor
      · intro hy
        obtain ⟨_, h, -⟩ := k.mpr ⟨hs, hy, rfl⟩
        exact h
      · intro hy
        obtain ⟨_, h, -⟩ := k.mp ⟨hs', hy, rfl⟩
        exact h
    · intro x y
      have k := key i hi 3 x y
      constructor
      · intro h
        obtain ⟨_, h'⟩ := k.mpr ⟨hs, h⟩
        exact h'
      · intro h
        obtain ⟨_, h'⟩ := k.mp ⟨hs', h⟩
        exact h'
  · intro i hs hs' x hx hx'
    have hi : i ≤ H.length := (Order.le_succ i).trans hs
    change e (((H.step i hs).iso.toEquiv ⟨e.symm x, hx⟩ : V)) = _
    obtain ⟨_, hx'', heq⟩ :=
      (key i hi 4 x ((K.step i hs').iso.toEquiv ⟨x, hx'⟩)).mp ⟨hs', hx', rfl⟩
    have h := congrArg e heq
    rw [e.apply_symm_apply] at h
    exact h
  · intro i hs hs' a b
    have hi : i ≤ H.length := (Order.le_succ i).trans hs
    have k := key i hi 5 a b
    refine (edge_map_iff e he (H.step i hs).edge a b).trans ?_
    constructor
    · intro h
      obtain ⟨_, h'⟩ := k.mpr ⟨hs, h⟩
      exact h'
    · intro h
      obtain ⟨_, h'⟩ := k.mp ⟨hs', h⟩
      exact h'

/-- A condition with prescribed support and no blue edges (only used to reuse the swap
extension of `SwapExtension.lean`). -/
def bare (s : Set V) (hs : #s ≤ μ) : BasicCondition V I block μ where
  support := s
  blue _ _ := False
  symmetric h := h
  irreflexive _ h := h
  blue_support h := h.elim
  different_blocks h := h.elim
  small := hs

lemma state_length_eq_last (K : History V I block μ hμ) (i : Ordinal.{u}) (hi : i ≤ K.length)
    (h : i = K.length) : K.state i hi = K.last := by
  subst h
  rfl

/-- **Key lemma.**  Equal blueprints plus agreement of the codes on the overlap of the last
supports give a block-preserving permutation `e` of `V`, fixing the overlap pointwise and mapping
`S_H` onto `S_K`, with `H.relabel e = K`. -/
theorem relabel_of_blueprint_eq {H K : History V I block μ hμ}
    (hbp : blueprint H = blueprint K)
    (hroot : ∀ x ∈ H.last.support ∩ K.last.support, code H x = code K x) :
    ∃ (e : V ≃ V) (he : ∀ x, block (e x) = block x),
      (∀ x ∈ H.last.support ∩ K.last.support, e x = x) ∧
      e '' H.last.support = K.last.support ∧ H.relabel e he = K := by
  classical
  have hlen : H.length = K.length :=
    congrArg (fun b : Blueprint I μ => (b.1 : Ordinal.{u})) hbp
  have hblk : blk H = blk K := congrArg (fun b : Blueprint I μ => b.2.1) hbp
  have hsp : stagePart H = stagePart K := congrArg (fun b : Blueprint I μ => b.2.2) hbp
  have hcode : ∀ i, i ≤ H.length → ∀ n c d,
      (∃ x y, relN H i n x y ∧ code H x = c ∧ code H y = d) ↔
        (∃ x y, relN K i n x y ∧ code K x = c ∧ code K y = d) := by
    intro i hi n c d
    rw [← mem_stagePart H hi, hsp, hlen, mem_stagePart K (hlen ▸ hi)]
  have hfwd : ∀ x : H.last.support, ∃ y : K.last.support, code K y = code H x := by
    intro x
    obtain ⟨z₁, z₂, hz, h₁, -⟩ :=
      (hcode H.length le_rfl 0 _ _).mp ⟨x, x, ⟨le_rfl, x.2, rfl⟩, rfl, rfl⟩
    exact ⟨⟨z₁, (rel_supp K _ 0 hz).1⟩, h₁⟩
  have hbwd : ∀ y : K.last.support, ∃ x : H.last.support, code H x = code K y := by
    intro y
    have hy : relN K H.length 0 y y := by
      refine ⟨hlen.le, ?_, rfl⟩
      rw [state_length_eq_last K H.length hlen.le hlen]
      exact y.2
    obtain ⟨z₁, z₂, hz, h₁, -⟩ := (hcode H.length le_rfl 0 _ _).mpr ⟨y, y, hy, rfl, rfl⟩
    exact ⟨⟨z₁, (rel_supp H _ 0 hz).1⟩, h₁⟩
  choose F hF using hfwd
  choose G hG using hbwd
  have hGF : ∀ x, G (F x) = x := fun x =>
    Subtype.ext (code_injOn H (G (F x)).2 x.2 ((hG _).trans (hF x)))
  have hFG : ∀ y, F (G y) = y := fun y =>
    Subtype.ext (code_injOn K (F (G y)).2 y.2 ((hF _).trans (hG y)))
  have hblock : ∀ x : H.last.support, block (F x : V) = block x := by
    intro x
    have h1 := blk_code K (F x).2
    rw [hF x, ← hblk, blk_code H x.2] at h1
    exact (Option.some.inj h1).symm
  have hfix : ∀ x : H.last.support, (x : V) ∈ K.last.support → (F x : V) = x := fun x hxK =>
    code_injOn K (F x).2 hxK ((hF x).trans (hroot x ⟨x.2, hxK⟩))
  let iso : TameIso (bare (block := block) H.last.support H.last.small)
      (bare (block := block) K.last.support K.last.small) :=
    { toEquiv := ⟨F, G, hGF, hFG⟩
      blue_iff := fun _ _ => Iff.rfl
      block_iff := fun x y => by
        change block (F x : V) = block (F y : V) ↔ block (x : V) = block (y : V)
        rw [hblock x, hblock y] }
  have hisofix : iso.FixesOverlap := fun x hx => hfix x hx
  have hpres : iso.PreservesBlocks := fun x => hblock x
  have he : ∀ x, block (iso.swapExtension hisofix x) = block x :=
    iso.swapExtension_preservesBlocks hisofix hpres
  have heH : ∀ x (hx : x ∈ H.last.support), iso.swapExtension hisofix x = F ⟨x, hx⟩ :=
    fun x hx => iso.swapExtension_of_mem_left hisofix x hx
  have htr : ∀ x ∈ H.last.support, iso.swapExtension hisofix x ∈ K.last.support ∧
      code K (iso.swapExtension hisofix x) = code H x := by
    intro x hx
    rw [heH x hx]
    exact ⟨(F _).2, hF _⟩
  refine ⟨iso.swapExtension hisofix, he, ?_, iso.swapExtension_image_left hisofix, ?_⟩
  · rintro x ⟨hxH, hxK⟩
    rw [heH x hxH]
    exact hfix ⟨x, hxH⟩ hxK
  · apply relabel_eq_of_key _ he hlen
    intro i hi n y₁ y₂
    exact transport (iso.swapExtension hisofix) (code H) (code K) K.last.support
      H.last.support (code_injOn K) htr (relN H i n) (relN K i n)
      (fun _ _ h => rel_supp H i n h) (fun _ _ h => rel_supp K i n h) (hcode i hi n) y₁ y₂

/-! ### The chain-condition core -/

/-- **cc core for histories (no flips).**  Among any `(2^μ)⁺` histories (with `#I ≤ 2^μ`)
there are two distinct indices `a ≠ b` and a block-preserving permutation `e` of `V` fixing
`S_a ∩ S_b` pointwise, mapping `S_a` onto `S_b`, with `H b = (H a).relabel e`. -/
theorem cc_histories (hI : #I ≤ 2 ^ μ) {A : Type u} (hA : Order.succ (2 ^ μ) ≤ #A)
    (H : A → History V I block μ hμ) :
    ∃ a b : A, a ≠ b ∧ ∃ (e : V ≃ V) (he : ∀ x, block (e x) = block x),
      (∀ x ∈ (H a).last.support ∩ (H b).last.support, e x = x) ∧
      e '' (H a).last.support = (H b).last.support ∧ H b = (H a).relabel e he := by
  obtain ⟨J, R, hJ, hf, hR, hΔ⟩ := cc_skeleton_two_pow hμ hA (fun a => blueprint (H a))
    (by simpa using mk_blueprint_le (I := I) hμ hI) (fun a => (H a).last.support)
    (fun a => (H a).last.small)
  have hRμ : #R ≤ μ := by
    obtain ⟨⟨a, ha⟩⟩ := Cardinal.mk_ne_zero_iff.mp
      (by rw [hJ]; exact (zero_le.trans_lt (Order.lt_succ (2 ^ μ))).ne')
    exact (mk_le_mk_of_subset (hR a ha)).trans (H a).last.small
  have hcodes : #(R → Coord μ) < Order.succ (2 ^ μ) := by
    rw [← power_def, mk_coord]
    refine lt_of_le_of_lt ?_ (Order.lt_succ _)
    calc μ ^ #R ≤ μ ^ μ := power_le_power_left (aleph0_pos.trans_le hμ).ne' hRμ
      _ = 2 ^ μ := power_self_eq hμ
  obtain ⟨J₂, hJ₂, hg⟩ := exists_const_on_large (θ := Order.succ (2 ^ μ))
    (two_pow_facts hμ).1 hJ.ge (fun a : J => fun r : R => code (H a.1) r.1)
    (by simpa using hcodes)
  have h2 : (2 : Cardinal) ≤ #J₂ := by
    rw [hJ₂]
    exact ((ofNat_lt_aleph0 : (2 : Cardinal.{u}) < ℵ₀).le.trans
      (hμ.trans (cantor μ).le)).trans (Order.le_succ _)
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := two_le_iff.mp h2
  have hab' : a.1 ≠ b.1 := fun h => hab (Subtype.ext (Subtype.ext h))
  have hroot : ∀ x ∈ (H a.1).last.support ∩ (H b.1).last.support,
      code (H a.1) x = code (H b.1) x := by
    intro x hx
    have hxR : x ∈ R := by rw [← hΔ a.1 a.2 b.1 b.2 hab']; exact hx
    exact congrFun (hg a ha b hb) ⟨x, hxR⟩
  obtain ⟨e, he, hfix, himg, heq⟩ :=
    relabel_of_blueprint_eq (hf a.1 a.2 b.1 b.2) hroot
  exact ⟨a.1, b.1, hab', e, he, hfix, himg, heq.symm⟩

/-- The relabelled history in `cc_histories` stays block-preserving. -/
theorem cc_histories_blockPreserving (hI : #I ≤ 2 ^ μ) {A : Type u}
    (hA : Order.succ (2 ^ μ) ≤ #A) (H : A → History V I block μ hμ)
    (hH : ∀ a, (H a).BlockPreserving) :
    ∃ a b : A, a ≠ b ∧ ∃ (e : V ≃ V) (he : ∀ x, block (e x) = block x),
      (∀ x ∈ (H a).last.support ∩ (H b).last.support, e x = x) ∧
      e '' (H a).last.support = (H b).last.support ∧ H b = (H a).relabel e he ∧
      ((H a).relabel e he).BlockPreserving := by
  obtain ⟨a, b, hab, e, he, hfix, himg, heq⟩ := cc_histories hI hA H
  exact ⟨a, b, hab, e, he, hfix, himg, heq, History.relabel_blockPreserving (hH a) e he⟩

end Erdos1220.HistoryBlueprint

#print axioms Erdos1220.HistoryBlueprint.history_ext
#print axioms Erdos1220.HistoryBlueprint.rel_supp
#print axioms Erdos1220.HistoryBlueprint.mk_blueprint_le
#print axioms Erdos1220.HistoryBlueprint.relabel_eq_of_key
#print axioms Erdos1220.HistoryBlueprint.relabel_of_blueprint_eq
#print axioms Erdos1220.HistoryBlueprint.cc_histories
#print axioms Erdos1220.HistoryBlueprint.cc_histories_blockPreserving
