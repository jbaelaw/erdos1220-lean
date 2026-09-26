import Erdos1220.BethWitness

/-!
# The concrete witness: `λ = ℶ_{𝔠⁺}`, its vertex set and its blocks

Vertices are the elements of `λ.ord.ToType` (the index type of the ground ordinal `PSet`
`card_ex λ`). Block indices are `κ.ord.ToType` with `κ = 𝔠⁺`. The block of `v` is the least `i`
with `v < ℶ_{i+1}`. Blocks are intervals: a smaller block index forces a smaller ordinal.
Every block contains `ℶ_i` itself, which gives a section of the block map.
-/

open Cardinal Ordinal Order

universe u

namespace Erdos1220.Witness

/-- `κ = 𝔠⁺` as an ordinal. -/
noncomputable def κo : Ordinal.{u} := (Order.succ (Cardinal.continuum : Cardinal.{u})).ord

/-- `λ = ℶ_κ` as an ordinal. -/
noncomputable def lo : Ordinal.{u} := bethWitness.{u}.ord

/-- The vertex type. -/
abbrev Vtx : Type u := lo.{u}.ToType

/-- The block index type. -/
abbrev Blk : Type u := κo.{u}.ToType

theorem lo_eq : lo.{u} = (fun o => (beth o).ord) κo.{u} := rfl

theorem exists_lt_beth (v : Vtx.{u}) : ∃ j < κo.{u}, (v.toOrd : Ordinal) < (beth j).ord := by
  have hv : (v.toOrd : Ordinal) < lo.{u} := v.toOrd.2
  exact (isNormal_beth_ord.lt_iff_exists_lt succ_continuum_ord_isSuccLimit).mp hv

/-- The set of candidate block indices of `v`. -/
def cands (v : Vtx.{u}) : Set Ordinal.{u} := {i | (v.toOrd : Ordinal) < (beth (Order.succ i)).ord}

theorem cands_nonempty (v : Vtx.{u}) : (cands v).Nonempty := by
  obtain ⟨j, -, hj⟩ := exists_lt_beth v
  exact ⟨j, hj.trans_le (ord_le_ord.mpr (beth_le_beth.mpr (Order.le_succ j)))⟩

/-- The block index (as an ordinal) of `v`. -/
noncomputable def blockIdx (v : Vtx.{u}) : Ordinal.{u} := sInf (cands v)

theorem blockIdx_mem (v : Vtx.{u}) : blockIdx v ∈ cands v := csInf_mem (cands_nonempty v)

theorem blockIdx_lt (v : Vtx.{u}) : blockIdx v < κo.{u} := by
  obtain ⟨j, hj, hvj⟩ := exists_lt_beth v
  have hmem : j ∈ cands v :=
    hvj.trans_le (ord_le_ord.mpr (beth_le_beth.mpr (Order.le_succ j)))
  exact (csInf_le' hmem).trans_lt hj

/-- The block map. -/
noncomputable def block (v : Vtx.{u}) : Blk.{u} := Ordinal.ToType.mk ⟨blockIdx v, blockIdx_lt v⟩

theorem block_toOrd (v : Vtx.{u}) : ((block v).toOrd : Ordinal) = blockIdx v := by
  simp [block]

/-- Below the block index, the vertex lies above `ℶ_{j+1}`. -/
theorem le_of_lt_blockIdx (v : Vtx.{u}) {j : Ordinal.{u}} (hj : j < blockIdx v) :
    (beth (Order.succ j)).ord ≤ (v.toOrd : Ordinal) := by
  by_contra hlt
  exact absurd (csInf_le' (show j ∈ cands v from not_le.mp hlt)) (not_le.mpr hj)

/-- **Blocks are intervals.** A smaller block index forces a smaller ordinal. -/
theorem toOrd_lt_of_blockIdx_lt {u' v : Vtx.{u}} (h : blockIdx u' < blockIdx v) :
    (u'.toOrd : Ordinal) < v.toOrd :=
  (blockIdx_mem u').trans_le (le_of_lt_blockIdx v h)

theorem toOrd_lt_of_block_lt {u' v : Vtx.{u}}
    (h : ((block u').toOrd : Ordinal) < (block v).toOrd) :
    (u'.toOrd : Ordinal) < v.toOrd := by
  rw [block_toOrd, block_toOrd] at h
  exact toOrd_lt_of_blockIdx_lt h

theorem beth_lt_lo {i : Ordinal.{u}} (hi : i < κo.{u}) : (beth i).ord < lo.{u} := by
  rw [lo_eq]
  exact ord_lt_ord.mpr (beth_strictMono hi)

/-- The canonical representative `ℶ_i` of block `i`. -/
noncomputable def rep (i : Blk.{u}) : Vtx.{u} :=
  Ordinal.ToType.mk ⟨(beth (i.toOrd : Ordinal)).ord, beth_lt_lo i.toOrd.2⟩

theorem blockIdx_rep (i : Blk.{u}) : blockIdx (rep i) = (i.toOrd : Ordinal) := by
  have hv : ((rep i).toOrd : Ordinal) = (beth (i.toOrd : Ordinal)).ord := by simp [rep]
  apply le_antisymm
  · apply csInf_le' 
    show ((rep i).toOrd : Ordinal) < _
    rw [hv]
    exact ord_lt_ord.mpr (beth_strictMono (Order.lt_succ _))
  · apply le_csInf (cands_nonempty _)
    intro j hj
    by_contra hlt
    rw [not_le] at hlt
    have h1 : ((rep i).toOrd : Ordinal) < (beth (Order.succ j)).ord := hj
    rw [hv] at h1
    exact absurd h1 (not_lt.mpr (ord_le_ord.mpr (beth_le_beth.mpr (Order.succ_le_of_lt hlt))))

theorem block_rep (i : Blk.{u}) : block (rep i) = i := by
  have h : (⟨blockIdx (rep i), blockIdx_lt (rep i)⟩ : Set.Iio κo.{u}) = i.toOrd :=
    Subtype.ext (blockIdx_rep i)
  simp only [block, h]
  simp

theorem mk_Blk : #Blk.{u} = Order.succ (Cardinal.continuum : Cardinal.{u}) := by
  simp [Blk, κo]

theorem mk_Vtx : #Vtx.{u} = bethWitness.{u} := by
  simp [Vtx, lo]

end Erdos1220.Witness
