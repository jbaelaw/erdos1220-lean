/-
# Erdős #1220 — cardinal toolkit on `ZFSet.{0}`

Bridges between the two-valued predicates of `Realize1220` and Mathlib's `Cardinal`/`Ordinal`:
`LeqZ A B ↔ card A ≤ card B`, `FnZ D C f ↔ f ∈ funs D C`, `card (funs D C) = card C ^ card D`,
`OrdZ ↔ IsOrdinal`, `CardZ k ↔ k = κ.ord.toZFSet`, `card ω = ℵ₀`, `PowLtZ` ↔ `μ ^ ℵ₀ < κ`.
-/
import Erdos1220Full.Realize1220
import Mathlib.SetTheory.ZFC.Cardinal
import Mathlib.SetTheory.ZFC.Ordinal

open Cardinal

namespace Erdos1220.FOL


/-! ### Injections -/

theorem card_le_of_rel {A B h : ZFSet.{0}}
    (h1 : ∀ x : ZFSet.{0}, x ∈ A → ∃ y : ZFSet.{0}, y ∈ B ∧ ZFSet.pair x y ∈ h)
    (h2 : ∀ x x' y : ZFSet.{0}, x ∈ A → x' ∈ A → ZFSet.pair x y ∈ h → ZFSet.pair x' y ∈ h → x = x') :
    ZFSet.card A ≤ ZFSet.card B := by
  rw [← Cardinal.lift_le.{1}, ← ZFSet.cardinalMk_coe_sort, ← ZFSet.cardinalMk_coe_sort]
  choose g hgB hg using h1
  refine Cardinal.mk_le_of_injective (f := fun x : A => (⟨g x.1 x.2, hgB x.1 x.2⟩ : B)) ?_
  rintro ⟨x, hx⟩ ⟨x', hx'⟩ hxx
  have hv : g x hx = g x' hx' := congrArg Subtype.val hxx
  exact Subtype.ext (h2 x x' _ hx hx' (hg x hx) (hv ▸ hg x' hx'))

/-- The graph of an embedding `A ↪ B`, as a `ZFSet`. -/
noncomputable def graphZ {A B : ZFSet.{0}} (e : A → B) : ZFSet.{0} :=
  ZFSet.range (fun x : A => ZFSet.pair x.1 (e x).1)

theorem pair_mem_graphZ {A B : ZFSet.{0}} (e : A → B) {x y : ZFSet.{0}} :
    ZFSet.pair x y ∈ graphZ e ↔ ∃ hx : x ∈ A, (e ⟨x, hx⟩).1 = y := by
  unfold graphZ
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨⟨x₀, hx₀⟩, h⟩
    rw [ZFSet.pair_inj] at h
    obtain ⟨rfl, h⟩ := h
    exact ⟨hx₀, h⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, by rw [h]⟩

theorem mem_graphZ {A B : ZFSet.{0}} (e : A → B) {z : ZFSet.{0}} :
    z ∈ graphZ e ↔ ∃ x : A, ZFSet.pair x.1 (e x).1 = z := by
  unfold graphZ; exact ZFSet.mem_range

theorem exists_graph_of_card_le {A B : ZFSet.{0}} (hAB : ZFSet.card A ≤ ZFSet.card B) :
    ∃ e : A → B, Function.Injective e := by
  rw [← Cardinal.lift_le.{1}, ← ZFSet.cardinalMk_coe_sort, ← ZFSet.cardinalMk_coe_sort] at hAB
  obtain ⟨e⟩ := (Cardinal.le_def _ _).1 hAB
  exact ⟨e, e.injective⟩

theorem leqZ_iff (A B : ZFSet.{0}) : LeqZ A B ↔ ZFSet.card A ≤ ZFSet.card B := by
  constructor
  · rintro ⟨f, hf, hinj⟩
    refine card_le_of_rel (h := f) (fun x hx => ?_) (fun x x' y hx hx' h1 h2 => hinj x hx x' hx' y h1 h2)
    obtain ⟨y, hy, hxy, -⟩ := hf x hx
    exact ⟨y, hy, hxy⟩
  · intro hAB
    obtain ⟨e, he⟩ := exists_graph_of_card_le hAB
    refine ⟨graphZ e, fun x hx => ⟨(e ⟨x, hx⟩).1, (e ⟨x, hx⟩).2,
      (pair_mem_graphZ e).2 ⟨hx, rfl⟩, fun y' hy' => ?_⟩, fun x hx x' hx' y h1 h2 => ?_⟩
    · obtain ⟨_, h⟩ := (pair_mem_graphZ e).1 hy'
      exact h.symm
    · obtain ⟨hx₁, h1⟩ := (pair_mem_graphZ e).1 h1
      obtain ⟨hx₂, h2⟩ := (pair_mem_graphZ e).1 h2
      have := he (Subtype.ext (h1.trans h2.symm))
      exact congrArg Subtype.val this

/-- Injective relations from a set `A` into `B` (the form used by `powLtF`). -/
theorem relInj_iff (A B : ZFSet.{0}) :
    (∃ h : ZFSet.{0}, (∀ f : ZFSet.{0}, f ∈ A → ∃ b : ZFSet.{0}, b ∈ B ∧ ZFSet.pair f b ∈ h) ∧
      (∀ f f' b : ZFSet.{0}, f ∈ A → f' ∈ A → ZFSet.pair f b ∈ h → ZFSet.pair f' b ∈ h → f = f')) ↔
    ZFSet.card A ≤ ZFSet.card B := by
  constructor
  · rintro ⟨h, h1, h2⟩
    exact card_le_of_rel h1 h2
  · intro hAB
    obtain ⟨e, he⟩ := exists_graph_of_card_le hAB
    refine ⟨graphZ e, fun x hx => ⟨(e ⟨x, hx⟩).1, (e ⟨x, hx⟩).2,
      (pair_mem_graphZ e).2 ⟨hx, rfl⟩⟩, fun x x' y hx hx' h1 h2 => ?_⟩
    obtain ⟨hx₁, h1⟩ := (pair_mem_graphZ e).1 h1
    obtain ⟨hx₂, h2⟩ := (pair_mem_graphZ e).1 h2
    have := he (Subtype.ext (h1.trans h2.symm))
    exact congrArg Subtype.val this

/-! ### Functions -/

theorem fnZ_iff (D C f : ZFSet.{0}) : FnZ D C f ↔ f ∈ ZFSet.funs D C := by
  rw [ZFSet.mem_funs, ZFSet.IsFunc, ZFSet.subset_def]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun z hz => ?_, fun x hx => ?_⟩
    · obtain ⟨x, hx, y, hy, rfl⟩ := h1 z hz
      exact ZFSet.pair_mem_prod.2 ⟨hx, hy⟩
    · obtain ⟨y, hy, hu⟩ := h2 x hx
      exact ⟨y, hy, hu⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun z hz => ?_, fun x hx => ?_⟩
    · obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.1 (h1 hz)
      exact ⟨a, ha, b, hb, rfl⟩
    · obtain ⟨y, hy, hu⟩ := h2 x hx
      exact ⟨y, hy, hu⟩

section funs
variable (D C : ZFSet.{0})

theorem funs_exists (f : ZFSet.funs D C) (x : D) : ∃ y : ZFSet.{0}, ZFSet.pair x.1 y ∈ f.1 :=
  ((ZFSet.mem_funs.1 f.2).2 x.1 x.2).exists

/-- The value of a set function at a point. -/
noncomputable def funsVal (f : ZFSet.funs D C) (x : D) : C :=
  ⟨Classical.choose (funs_exists D C f x), by
    have h := Classical.choose_spec (funs_exists D C f x)
    exact (ZFSet.pair_mem_prod.1 (ZFSet.subset_def.1 (ZFSet.mem_funs.1 f.2).1 h)).2⟩

theorem funsVal_spec (f : ZFSet.funs D C) (x : D) : ZFSet.pair x.1 (funsVal D C f x).1 ∈ f.1 :=
  Classical.choose_spec (funs_exists D C f x)

theorem funsVal_unique (f : ZFSet.funs D C) (x : D) (y : ZFSet.{0}) (hy : ZFSet.pair x.1 y ∈ f.1) :
    y = (funsVal D C f x).1 :=
  ((ZFSet.mem_funs.1 f.2).2 x.1 x.2).unique hy (funsVal_spec D C f x)

theorem graphZ_mem_funs (g : D → C) : graphZ g ∈ ZFSet.funs D C := by
  rw [ZFSet.mem_funs, ZFSet.IsFunc, ZFSet.subset_def]
  refine ⟨fun z hz => ?_, fun x hx => ⟨(g ⟨x, hx⟩).1, (pair_mem_graphZ g).2 ⟨hx, rfl⟩, ?_⟩⟩
  · obtain ⟨x, rfl⟩ := (mem_graphZ g).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨x.2, (g x).2⟩
  · intro y hy
    obtain ⟨_, h⟩ := (pair_mem_graphZ g).1 hy
    exact h.symm

theorem funsVal_bijective : Function.Bijective (funsVal D C) := by
  constructor
  · have key : ∀ f f' : ZFSet.funs D C, funsVal D C f = funsVal D C f' → ∀ z, z ∈ f.1 → z ∈ f'.1 := by
      intro f f' h z hz
      obtain ⟨a, ha, b, hb, rfl⟩ :=
        ZFSet.mem_prod.1 (ZFSet.subset_def.1 (ZFSet.mem_funs.1 f.2).1 hz)
      have hb' := funsVal_unique D C f ⟨a, ha⟩ b hz
      rw [h] at hb'
      rw [hb']
      exact funsVal_spec D C f' ⟨a, ha⟩
    intro f f' h
    exact Subtype.ext (ZFSet.ext fun z => ⟨key f f' h z, key f' f h.symm z⟩)
  · intro g
    refine ⟨⟨graphZ g, graphZ_mem_funs D C g⟩, funext fun x => Subtype.ext ?_⟩
    exact (funsVal_unique D C ⟨graphZ g, graphZ_mem_funs D C g⟩ x (g x).1
      ((pair_mem_graphZ g).2 ⟨x.2, rfl⟩)).symm

theorem card_funs : ZFSet.card (ZFSet.funs D C) = ZFSet.card C ^ ZFSet.card D := by
  apply Cardinal.lift_injective.{1}
  rw [← ZFSet.cardinalMk_coe_sort, Cardinal.lift_power, ← ZFSet.cardinalMk_coe_sort,
    ← ZFSet.cardinalMk_coe_sort, Cardinal.power_def]
  exact Cardinal.mk_congr (Equiv.ofBijective _ (funsVal_bijective D C))

end funs

/-! ### Ordinals and cardinals -/

theorem ordZ_iff (a : ZFSet.{0}) : OrdZ a ↔ ZFSet.IsOrdinal a := by
  constructor
  · rintro ⟨⟨htri, -⟩, htr⟩
    refine ⟨fun y hy => ZFSet.subset_def.2 fun z hz => htr y hy z hz, ?_⟩
    intro y z w hyz hzw hwa
    have hza : z ∈ a := htr w hwa z hzw
    have hya : y ∈ a := htr z hza y hyz
    rcases htri y hya w hwa with (rfl | h) | h
    · exact absurd hzw (ZFSet.mem_asymm hyz)
    · exact h
    · exact (ZFSet.mem_wf.asymmetric₃ _ _ _ hyz hzw h).elim
  · intro h
    refine ⟨⟨fun y hy z hz => ?_, fun y _ hne => ?_⟩, fun y hy z hz => ?_⟩
    · rcases ZFSet.IsOrdinal.mem_trichotomous (h.mem hy) (h.mem hz) with h1 | h1 | h1
      · exact Or.inl (Or.inr h1)
      · exact Or.inl (Or.inl h1)
      · exact Or.inr h1
    · have hne' : ({w | w ∈ y} : Set ZFSet.{0}).Nonempty := by
        by_contra hc
        apply hne
        rw [ZFSet.eq_empty]
        intro w hw
        exact hc ⟨w, hw⟩
      obtain ⟨z, hz, hmin⟩ := ZFSet.mem_wf.has_min _ hne'
      exact ⟨z, hz, fun w hw => hmin w hw⟩
    · exact ZFSet.subset_def.1 (h.subset_of_mem hy) hz

/-- The von Neumann initial ordinal of a cardinal. -/
noncomputable def cz (κ : Cardinal.{0}) : ZFSet.{0} := κ.ord.toZFSet

theorem card_cz (κ : Cardinal.{0}) : ZFSet.card (cz κ) = κ := by
  rw [cz, Ordinal.card_toZFSet, Cardinal.card_ord]

theorem cz_injective : Function.Injective cz := by
  intro κ μ h
  rw [← card_cz κ, ← card_cz μ, h]

theorem mem_cz_iff {κ : Cardinal.{0}} {x : ZFSet.{0}} :
    x ∈ cz κ ↔ ∃ b : Ordinal.{0}, b.card < κ ∧ b.toZFSet = x := by
  rw [cz, Ordinal.mem_toZFSet_iff]
  simp only [Cardinal.lt_ord]

theorem cz_mem_cz {κ μ : Cardinal.{0}} : cz μ ∈ cz κ ↔ μ < κ := by
  rw [cz, cz, Ordinal.toZFSet_mem_toZFSet_iff, Cardinal.ord_lt_ord]

theorem cardZ_iff (k : ZFSet.{0}) : CardZ k ↔ ∃ κ : Cardinal.{0}, k = cz κ := by
  constructor
  · rintro ⟨hord, hmin⟩
    rw [ordZ_iff] at hord
    refine ⟨(ZFSet.rank k).card, ?_⟩
    have hk : (ZFSet.rank k).toZFSet = k := hord.toZFSet_rank_eq
    set o := ZFSet.rank k
    rw [cz, ← hk]
    congr 1
    refine le_antisymm ?_ (Cardinal.ord_card_le o)
    by_contra hlt
    have hlt' := not_le.1 hlt
    apply hmin (o.card.ord.toZFSet) (by rw [← hk]; exact Ordinal.toZFSet_mem_toZFSet_iff.2 hlt')
    rw [leqZ_iff, ← hk, Ordinal.card_toZFSet, Ordinal.card_toZFSet, Cardinal.card_ord]
  · rintro ⟨κ, rfl⟩
    refine ⟨(ordZ_iff _).2 (ZFSet.isOrdinal_toZFSet _), fun a ha => ?_⟩
    obtain ⟨b, hb, rfl⟩ := mem_cz_iff.1 ha
    rw [leqZ_iff, card_cz, Ordinal.card_toZFSet]
    exact not_le.2 hb

theorem card_toZFSet_eq (b : Ordinal.{0}) : ZFSet.card b.toZFSet = b.card :=
  Ordinal.card_toZFSet b

/-! ### `ω` -/

/-- The finite von Neumann ordinals in `ZFSet`. -/
def natZ (n : ℕ) : ZFSet.{0} := ZFSet.mk (PSet.ofNat n)

theorem natZ_succ (n : ℕ) : natZ (n + 1) = insert (natZ n) (natZ n) := rfl

theorem mem_omega_iff {x : ZFSet.{0}} : x ∈ ZFSet.omega ↔ ∃ n : ℕ, x = natZ n := by
  refine Quotient.inductionOn x fun y => ?_
  change ZFSet.mk y ∈ ZFSet.mk PSet.omega ↔ _
  rw [ZFSet.mk_mem_iff, PSet.mem_def]
  constructor
  · rintro ⟨⟨n⟩, h⟩
    exact ⟨n, ZFSet.sound h⟩
  · rintro ⟨n, h⟩
    exact ⟨⟨n⟩, ZFSet.exact h⟩

theorem natZ_eq_toZFSet (n : ℕ) : natZ n = (n : Ordinal.{0}).toZFSet := by
  induction n with
  | zero => rw [Nat.cast_zero, Ordinal.toZFSet_zero]; rfl
  | succ n ih => rw [natZ_succ, ih, Nat.cast_succ, Ordinal.toZFSet_add_one]

theorem omega_eq : ZFSet.omega = (Ordinal.omega0 : Ordinal.{0}).toZFSet := by
  ext x
  rw [mem_omega_iff, Ordinal.mem_toZFSet_iff]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, Ordinal.natCast_lt_omega0 n, (natZ_eq_toZFSet n).symm⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 ha
    exact ⟨n, (natZ_eq_toZFSet n).symm⟩

theorem card_omega : ZFSet.card ZFSet.omega.{0} = ℵ₀ := by
  rw [omega_eq, Ordinal.card_toZFSet, Ordinal.card_omega0]

/-! ### `μ ^ ℵ₀ < κ` -/

theorem powLtZ_iff (μ k : ZFSet.{0}) :
    PowLtZ μ k ↔ ∃ α : ZFSet.{0}, α ∈ k ∧ ZFSet.card μ ^ ℵ₀ ≤ ZFSet.card α := by
  unfold PowLtZ
  simp only [fnZ_iff]
  refine exists_congr fun α => and_congr_right fun _ => ?_
  rw [relInj_iff, card_funs, card_omega]

theorem powLtZ_cz_iff (μ κ : Cardinal.{0}) : PowLtZ (cz μ) (cz κ) ↔ μ ^ ℵ₀ < κ := by
  rw [powLtZ_iff, card_cz]
  constructor
  · rintro ⟨α, hα, hle⟩
    obtain ⟨b, hb, rfl⟩ := mem_cz_iff.1 hα
    rw [card_toZFSet_eq] at hle
    exact hle.trans_lt hb
  · intro h
    refine ⟨cz (μ ^ ℵ₀), cz_mem_cz.2 h, (card_cz _).ge⟩

theorem oInaccZ_cz_iff (κ : Cardinal.{0}) : OInaccZ (cz κ) ↔ Erdos1220.IsOmegaInaccessible κ := by
  constructor
  · intro h μ hμ
    exact (powLtZ_cz_iff μ κ).1 (h (cz μ) (cz_mem_cz.2 hμ) ((cardZ_iff _).2 ⟨μ, rfl⟩))
  · intro h m hm hcard
    obtain ⟨μ, rfl⟩ := (cardZ_iff _).1 hcard
    exact (powLtZ_cz_iff μ κ).2 (h μ (cz_mem_cz.1 hm))

end Erdos1220.FOL

#print axioms Erdos1220.FOL.oInaccZ_cz_iff
#print axioms Erdos1220.FOL.card_funs
