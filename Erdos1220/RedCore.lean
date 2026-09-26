import Erdos1220.HistoryBlueprint
import Erdos1220.IsoAmalgam

/-!
# The combinatorial core of Shelah–Stanley §3.9 (red sets)

Among `(2^μ)⁺` block-preserving histories with designated points `x a` (in one block) and
`y a` (in another block), both families injective, two histories can be amalgamated so that
`x a` and `y b` become blue (green in the paper). Consequently no condition can force a red
homogeneous set containing all these points.
-/

open Cardinal Set Order

universe u

namespace Erdos1220.HistoryBlueprint

open BasicCondition Erdos1220.DeltaSystem

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

/-- `relabel_of_blueprint_eq` with the matching of codes exposed. -/
theorem relabel_of_blueprint_eq_code {H K : History V I block μ hμ}
    (hbp : blueprint H = blueprint K)
    (hroot : ∀ x ∈ H.last.support ∩ K.last.support, code H x = code K x) :
    ∃ (e : V ≃ V) (he : ∀ x, block (e x) = block x),
      (∀ x ∈ H.last.support ∩ K.last.support, e x = x) ∧
      e '' H.last.support = K.last.support ∧ H.relabel e he = K ∧
      ∀ x ∈ H.last.support, code K (e x) = code H x := by
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
  refine ⟨iso.swapExtension hisofix, he, ?_, iso.swapExtension_image_left hisofix, ?_,
    fun x hx => (htr x hx).2⟩
  · rintro x ⟨hxH, hxK⟩
    rw [heH x hxH]
    exact hfix ⟨x, hxH⟩ hxK
  · apply relabel_eq_of_key _ he hlen
    intro i hi n y₁ y₂
    exact transport (iso.swapExtension hisofix) (code H) (code K) K.last.support
      H.last.support (code_injOn K) htr (relN H i n) (relN K i n)
      (fun _ _ h => rel_supp H i n h) (fun _ _ h => rel_supp K i n h) (hcode i hi n) y₁ y₂


/-- **Pointed cc core.** Two of `(2^μ)⁺` histories are related by a block-preserving
permutation fixing the overlap and carrying the designated points to each other. -/
theorem cc_histories_pointed (hI : #I ≤ 2 ^ μ) {A : Type u} (hA : Order.succ (2 ^ μ) ≤ #A)
    (H : A → History V I block μ hμ) (x y : A → V)
    (hx : ∀ a, x a ∈ (H a).last.support) (hy : ∀ a, y a ∈ (H a).last.support) :
    ∃ a b : A, a ≠ b ∧ ∃ (e : V ≃ V) (he : ∀ z, block (e z) = block z),
      (∀ z ∈ (H a).last.support ∩ (H b).last.support, e z = z) ∧
      e '' (H a).last.support = (H b).last.support ∧ H b = (H a).relabel e he ∧
      e (x a) = x b ∧ e (y a) = y b := by
  have h1 : #(Blueprint I μ) ≤ Cardinal.lift.{u+1} (2 ^ μ) := by
    simpa using mk_blueprint_le (I := I) hμ hI
  have h2 : #(ULift.{u+1} (Coord μ × Coord μ)) ≤ Cardinal.lift.{u+1} (2 ^ μ) := by
    rw [mk_uLift, lift_le, mk_prod, lift_id, mk_coord, mul_eq_self hμ]
    exact (cantor μ).le
  have h3 : #(Blueprint I μ × ULift.{u+1} (Coord μ × Coord μ)) ≤
      Cardinal.lift.{u+1} (2 ^ μ) := by
    rw [mk_prod, lift_id, lift_id]
    calc _ ≤ Cardinal.lift.{u+1} (2 ^ μ) * Cardinal.lift.{u+1} (2 ^ μ) := mul_le_mul' h1 h2
      _ = _ := mul_eq_self (aleph0_le_lift.mpr (hμ.trans (cantor μ).le))
  have hX : Cardinal.lift.{u} #(Blueprint I μ × ULift.{u+1} (Coord μ × Coord μ)) ≤
      Cardinal.lift.{u+1} (2 ^ μ) := by simpa using h3
  obtain ⟨J, R, hJ, hf, hR, hΔ⟩ := cc_skeleton_two_pow hμ hA
    (fun a => (blueprint (H a), ULift.up (code (H a) (x a), code (H a) (y a)))) hX
    (fun a => (H a).last.support) (fun a => (H a).last.small)
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
  have hroot : ∀ z ∈ (H a.1).last.support ∩ (H b.1).last.support,
      code (H a.1) z = code (H b.1) z := by
    intro z hz
    have hzR : z ∈ R := by rw [← hΔ a.1 a.2 b.1 b.2 hab']; exact hz
    exact congrFun (hg a ha b hb) ⟨z, hzR⟩
  have hfab := hf a.1 a.2 b.1 b.2
  obtain ⟨e, he, hfix, himg, heq, hcode⟩ :=
    relabel_of_blueprint_eq_code (congrArg Prod.fst hfab) hroot
  have hxs : e (x a.1) ∈ (H b.1).last.support := himg ▸ ⟨x a.1, hx a.1, rfl⟩
  have hys : e (y a.1) ∈ (H b.1).last.support := himg ▸ ⟨y a.1, hy a.1, rfl⟩
  refine ⟨a.1, b.1, hab', e, he, hfix, himg, heq.symm, ?_, ?_⟩
  · apply code_injOn (H b.1) hxs (hx b.1)
    rw [hcode _ (hx a.1)]
    exact congrArg (fun t => t.2.down.1) hfab
  · apply code_injOn (H b.1) hys (hy b.1)
    rw [hcode _ (hy a.1)]
    exact congrArg (fun t => t.2.down.2) hfab

end Erdos1220.HistoryBlueprint

namespace Erdos1220.BPHistory

open BasicCondition History Erdos1220.HistoryBlueprint

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

/-- **§3.9 core.** Among `(2^μ)⁺` block-preserving histories with injective designated points
`x a` in block `b₁` and `y a` in block `b₂ ≠ b₁`, some two have a common weak extension in
which `x a` and `y b` are blue. -/
theorem red_core (hI : #I ≤ 2 ^ μ) {A : Type u} (hA : Order.succ (2 ^ μ) ≤ #A)
    (H : A → BPHistory V I block μ hμ) (x y : A → V)
    (hx : ∀ a, x a ∈ (H a).1.last.support) (hy : ∀ a, y a ∈ (H a).1.last.support)
    (hxinj : Function.Injective x) (hyinj : Function.Injective y)
    (hblock : ∀ a b, block (x a) ≠ block (y b)) :
    ∃ a b : A, a ≠ b ∧ ∃ U : BPHistory V I block μ hμ,
      WeakExtends (H a) U ∧ WeakExtends (H b) U ∧ U.1.last.blue (x a) (y b) := by
  obtain ⟨a, b, hab, e, he, hfix, himg, heq, hxe, hye⟩ :=
    cc_histories_pointed hI hA (fun a => (H a).1) x y hx hy
  have hlast : (((H a).1).relabel e he).last.support = (H b).1.last.support := by
    rw [← heq]
  have hfix' : ∀ z ∈ (H a).1.last.support, z ∈ ((H a).1.relabel e he).last.support →
      e z = z := fun z hz hz' => hfix z ⟨hz, hlast ▸ hz'⟩
  have hxK : x a ∉ ((H a).1.relabel e he).last.support := by
    rw [hlast]
    intro hxb
    have : e (x a) = x a := hfix _ ⟨hx a, hxb⟩
    exact hab (hxinj (this.symm.trans hxe))
  have hyH : y b ∉ (H a).1.last.support := by
    intro hya
    have hfixy : e (y b) = y b := hfix _ ⟨hya, hy b⟩
    have : y a = y b := e.injective (hye.trans hfixy.symm)
    exact hab (hyinj this)
  have hyK : y b ∈ ((H a).1.relabel e he).last.support := hlast ▸ hy b
  obtain ⟨U, h1, h2, h3, -⟩ := exists_green_isoAmalgam (H a) e he hfix' (x a) (y b) (hx a) hxK
    hyK hyH (hblock a b)
  have hHb : relabelBP (H a) e he = H b := Subtype.ext heq.symm
  exact ⟨a, b, hab, U, h1, hHb ▸ h2, h3⟩

end Erdos1220.BPHistory

#print axioms Erdos1220.HistoryBlueprint.relabel_of_blueprint_eq_code
#print axioms Erdos1220.HistoryBlueprint.cc_histories_pointed
#print axioms Erdos1220.BPHistory.red_core
