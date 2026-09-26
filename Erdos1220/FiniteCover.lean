import Mathlib.Data.Set.Countable

/-!
# Finite directed covers force countability

Suppose each index forbids finitely many indices and every distinct pair
is forbidden in at least one direction. The index type is countable.
The proof uses a countable sequence and a point outside its countably many
forbidden sets, without any partition or Δ-system theorem.
-/

open Set

universe u

namespace Erdos1220

/-- A finite-valued set map which covers every distinct pair in at least
one direction can exist only on a countable type. -/
theorem countable_of_finite_pair_cover {I : Type u} (f : I → Set I)
    (hf : ∀ i, (f i).Finite)
    (hcover : ∀ ⦃x y : I⦄, x ≠ y → y ∈ f x ∨ x ∈ f y) : Countable I := by
  classical
  by_contra hcount
  have hunc : ¬ (Set.univ : Set I).Countable := by
    simpa only [Set.countable_univ_iff] using hcount
  have hinf : (Set.univ : Set I).Infinite := fun h => hunc h.countable
  let e : ℕ ↪ (Set.univ : Set I) := Set.Infinite.natEmbedding Set.univ hinf
  let x : ℕ → I := fun n => (e n).val
  have hx : Function.Injective x := Subtype.val_injective.comp e.injective
  let B : Set I := ⋃ n : ℕ, insert (x n) (f (x n))
  have hB : B.Countable :=
    Set.countable_iUnion fun n => ((hf (x n)).insert (x n)).countable
  have hout : ∃ y : I, y ∉ B := by
    by_contra hn
    apply hunc
    apply hB.mono
    intro y _
    by_contra hy
    exact hn ⟨y, hy⟩
  obtain ⟨y, hy⟩ := hout
  have hsub : Set.range x ⊆ f y := by
    rintro _ ⟨n, rfl⟩
    have hxn : x n ∈ B :=
      Set.mem_iUnion.mpr ⟨n, Set.mem_insert (x n) (f (x n))⟩
    have hxy : x n ≠ y := fun h => hy (h ▸ hxn)
    rcases hcover hxy with h | h
    · exact False.elim (hy (Set.mem_iUnion.mpr
        ⟨n, Set.mem_insert_of_mem (x n) h⟩))
    · exact h
  exact (Set.infinite_range_of_injective hx) ((hf y).subset hsub)

end Erdos1220

#print axioms Erdos1220.countable_of_finite_pair_cover
