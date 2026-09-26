import Flypitch4.SetTheoryExt

/-!
# An uncountable free set for a finite set map

Enlarge each finite set `f i` by its index `i`, apply the uncountable
Δ-system lemma, and remove the finitely many indices lying in its root.
Distinct remaining indices cannot belong to each other's finite sets.
-/

open Cardinal Set

universe u

namespace Erdos1220

/-- Every finite-valued set map on an uncountable type has an uncountable
free set. Membership in both directions is excluded for distinct indices. -/
theorem exists_uncountable_free_set {I : Type u} (f : I → Set I)
    (hI : ℵ₀ < #I) (hf : ∀ i, (f i).Finite) :
    ∃ s : Set I, ℵ₀ < #s ∧
      ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → i ≠ j → j ∉ f i ∧ i ∉ f j := by
  classical
  let A : I → Set I := fun i => insert i (f i)
  have hA : ∀ i, (A i).Finite := fun i => (hf i).insert i
  obtain ⟨t, ht, root, hroot⟩ := delta_system_lemma_aleph1 A hI hA
  have ht_nontrivial : Nontrivial t :=
    Cardinal.one_lt_iff_nontrivial.mp (one_lt_aleph0.trans ht)
  obtain ⟨a, b, hab⟩ := ht_nontrivial.exists_pair_ne
  have hroot_finite : root.Finite := by
    rw [← hroot hab]
    exact (hA a.1).subset Set.inter_subset_left
  have hs : ℵ₀ < #(t \ root : Set I) := by
    rw [← not_le]
    intro hle
    have hc : (t \ root).Countable := Cardinal.le_aleph0_iff_set_countable.mp hle
    have htc : t.Countable :=
      (hc.union hroot_finite.countable).mono (Set.subset_sdiff_union t root)
    exact (not_le.mpr ht) (Cardinal.le_aleph0_iff_set_countable.mpr htc)
  refine ⟨t \ root, hs, ?_⟩
  intro i hi j hj hij
  have hij' : (⟨i, hi.1⟩ : t) ≠ ⟨j, hj.1⟩ :=
    fun h => hij (congrArg Subtype.val h)
  have hintersection : A i ∩ A j = root := hroot hij'
  constructor
  · intro hji
    apply hj.2
    rw [← hintersection]
    exact ⟨Set.mem_insert_of_mem i hji, Set.mem_insert j (f j)⟩
  · intro hij_mem
    apply hi.2
    rw [← hintersection]
    exact ⟨Set.mem_insert i (f i), Set.mem_insert_of_mem j hij_mem⟩

end Erdos1220

#print axioms Erdos1220.exists_uncountable_free_set
