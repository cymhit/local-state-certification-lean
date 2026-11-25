import LocalCertification.Extremal.SupportCompression
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
open scoped BigOperators Topology
open Set Finset
noncomputable section
namespace LocalCertification.Extremal
universe u

/-- A fixed finite simplex, including the empty-index boundary. -/
def weightsSet (n : ℕ) : Set (Fin n → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

theorem weightsSet_compact (n : ℕ) : IsCompact (weightsSet n) := by
  have hc : IsClosed (weightsSet n) := by
    have he : weightsSet n = (⋂ i : Fin n, {w | 0 ≤ w i}) ∩ {w | ∑ i, w i = 1} := by
      ext w; simp [weightsSet]
    rw [he]
    exact (isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))).inter
      (isClosed_eq (by fun_prop) continuous_const)
  apply IsCompact.of_isClosed_subset isCompact_Icc hc
  intro w hw
  refine ⟨hw.1, ?_⟩
  intro i
  have hi : w i ≤ ∑ j, w j := Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)
  simpa only [hw.2] using hi

def finiteCombinations {V : Type u} [AddCommGroup V] [Module ℝ V]
    (S : Set V) (n : ℕ) : Set V :=
  (fun wz : (Fin n → ℝ) × (Fin n → V) => ∑ i, wz.1 i • wz.2 i) ''
    (weightsSet n ×ˢ Set.pi Set.univ (fun _ => S))

theorem finiteCombinations_compact {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : Set V} (hS : IsCompact S) (n : ℕ) : IsCompact (finiteCombinations S n) := by
  exact ((weightsSet_compact n).prod (isCompact_univ_pi (fun _ => hS))).image (by fun_prop)

theorem convexHull_eq_finite_combinations {V : Type u} [AddCommGroup V] [Module ℝ V]
    [Module.Finite ℝ V] (S : Set V) :
    convexHull ℝ S = ⋃ n : Fin (Module.finrank ℝ V + 2), finiteCombinations S n := by
  ext y
  constructor
  · intro hy
    obtain ⟨ι, hι, z, a, hz, ha, hpos, hsum, heq⟩ := eq_pos_convex_span_of_mem_convexHull hy
    let e := (Fintype.equivFin ι).symm
    let z' : Fin (Fintype.card ι) → V := fun i => z (e i)
    let a' : Fin (Fintype.card ι) → ℝ := fun i => a (e i)
    have hcard : Fintype.card ι < Module.finrank ℝ V + 2 := by
      have h : Fintype.card ι ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range z')) + 1 := by
        simpa [z', Function.comp_def] using (ha.comp_embedding e.toEmbedding).card_le_finrank_succ
      have hd := (vectorSpan ℝ (Set.range z')).finrank_le
      omega
    apply Set.mem_iUnion.mpr
    refine ⟨⟨Fintype.card ι, hcard⟩, (a', z'), ?_, ?_⟩
    · exact ⟨⟨(fun i => (hpos (e i)).le), (Equiv.sum_comp e a).trans hsum⟩,
        fun i _ => hz ⟨e i, rfl⟩⟩
    · exact (Equiv.sum_comp e (fun i => a i • z i)).trans heq
  · intro hy
    obtain ⟨n, ⟨w, z⟩, hwz, he⟩ := Set.mem_iUnion.mp hy
    exact mem_convexHull_of_exists_fintype w z hwz.1.1 hwz.1.2
      (fun i => hwz.2 i (Set.mem_univ i)) he

/-- Finite-dimensional compact convex hull, for genuinely arbitrary compact sets. -/
theorem compact_convexHull {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Module.Finite ℝ V] {S : Set V} (hS : IsCompact S) : IsCompact (convexHull ℝ S) := by
  rw [convexHull_eq_finite_combinations]
  exact isCompact_iUnion (fun n => finiteCombinations_compact hS n)

end LocalCertification.Extremal
