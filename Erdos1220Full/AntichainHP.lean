import Erdos1220Full.HistoryForcing
import Erdos1220.IsoAmalgam
import Erdos1220.HistoryBlueprint

/-!
# The `(2^μ)⁺`-chain condition of the historical forcing (Sh:258 §3.8)

Among `(2^μ)⁺` block-preserving histories, the blueprint/Δ-system argument
(`HistoryBlueprint.cc_histories`) produces `a ≠ b` and a block-preserving permutation `e`
fixing `S_a ∩ S_b` with `H_b = H_a.relabel e`; the iso-amalgamation
(`BPHistory.exists_red_isoAmalgam`) gives a common weak extension.  Hence `HP` has no antichain
of size `(2^μ)⁺` (stated with the universe lift required by `AntichainBound` on
`HP : Type (u + 1)`).  Only `#I ≤ 2^μ` is assumed; no GCH.
-/

open Cardinal Set Order

universe u

namespace Erdos1220Full

open Erdos1220 Erdos1220.BasicCondition Erdos1220.History Erdos1220.BPHistory HistoryForcing

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

/-- Two block-preserving histories related by an overlap-fixing relabelling are compatible
in `HP`. -/
theorem compatible_of_relabel (p q : HP V I block μ hμ) (e : V ≃ V)
    (he : ∀ x, block (e x) = block x)
    (hfix : ∀ x ∈ (show BPHistory V I block μ hμ from p).1.last.support ∩
      (show BPHistory V I block μ hμ from q).1.last.support, e x = x)
    (hq : (show BPHistory V I block μ hμ from q).1 =
      (show BPHistory V I block μ hμ from p).1.relabel e he) :
    Compatible p q := by
  let P : BPHistory V I block μ hμ := p
  let Q : BPHistory V I block μ hμ := q
  have hfix' : ∀ x ∈ P.1.last.support, x ∈ (P.1.relabel e he).last.support → e x = x := by
    intro x hx hxr
    rw [← hq] at hxr
    exact hfix x ⟨hx, hxr⟩
  obtain ⟨U, h1, h2, -⟩ := exists_red_isoAmalgam P e he hfix'
  have hQ : relabelBP P e he = Q := Subtype.ext hq.symm
  rw [hQ] at h2
  exact ⟨U, h1, h2⟩

/-- **The `(2^μ)⁺`-antichain bound for `HP`** (ZFC, no GCH), assuming `#I ≤ 2^μ`. -/
theorem antichainBound_HP (hI : #I ≤ 2 ^ μ) :
    AntichainBound (Cardinal.lift.{u + 1} (Order.succ (2 ^ μ))) (HP V I block μ hμ) := by
  intro ι p hι
  obtain ⟨emb⟩ : Nonempty ((Order.succ ((2 : Cardinal.{u}) ^ μ)).out ↪ ι) := by
    rw [← Cardinal.lift_mk_le', mk_out, Cardinal.lift_id'.{u, u + 1}]
    exact hι
  let H : (Order.succ ((2 : Cardinal.{u}) ^ μ)).out → History V I block μ hμ := fun a =>
    (show BPHistory V I block μ hμ from p (emb a)).1
  obtain ⟨a, b, hab, e, he, hfix, -, heq⟩ :=
    HistoryBlueprint.cc_histories (hμ := hμ) hI (by rw [mk_out]) H
  exact ⟨emb a, emb b, fun h => hab (emb.injective h),
    compatible_of_relabel (p (emb a)) (p (emb b)) e he hfix heq⟩

end Erdos1220Full

#print axioms Erdos1220Full.compatible_of_relabel
#print axioms Erdos1220Full.antichainBound_HP
