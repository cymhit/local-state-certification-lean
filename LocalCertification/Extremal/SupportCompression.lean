/- Positive-weight support compression for finite dual representations. -/
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions

import Mathlib.Basic.Real.Basic

set_option autoImplicit false
open scoped BigOperators
open Finset
noncomputable section
namespace LocalCertification.Extremal
universe u v

/-- The common affine hyperplane upgrades affine to linear independence. -/
theorem linearIndependent_of_affine_of_functional
    {V : Type u} [AddCommGroup V] [Module ℝ V] {ι : Type v}
    {z : ι → V} (ℓ : V →ₗ[ℝ] ℝ) (hz : ∀ i, ℓ (z i) = 1)
    (ha : AffineIndependent ℝ z) : LinearIndependent ℝ z := by
  rw [linearIndependent_iff']
  intro s a h i hi
  have hs : ∑ j ∈ s, a j = 0 := by
    have he := congrArg ℓ h
    simpa only [map_sum, map_smul, hz, smul_eq_mul, mul_one, map_zero] using he
  exact ha.eq_zero_of_sum_eq_zero hs h i hi

/-- Positive normalized representation on distinct, linearly independent points;
no finiteness assumption is made on the original set. -/
theorem positive_support_compression
    {V : Type u} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
    (ℓ : V →ₗ[ℝ] ℝ) (S : Set V) (hS : ∀ x ∈ S, ℓ x = 1)
    {y : V} (hy : y ∈ convexHull ℝ S) :
    ∃ (n : ℕ) (z : Fin n → V) (a : Fin n → ℝ),
      (∀ i, z i ∈ S) ∧ (∀ i, 0 < a i) ∧ (∑ i, a i = 1) ∧
      (∑ i, a i • z i = y) ∧ LinearIndependent ℝ z ∧
      Function.Injective z ∧ n ≤ Module.finrank ℝ V := by
  obtain ⟨ι, hι, z, a, hz, ha, hpos, hsum, heq⟩ :=
    eq_pos_convex_span_of_mem_convexHull hy
  let e := (Fintype.equivFin ι).symm
  let z' : Fin (Fintype.card ι) → V := fun i => z (e i)
  let a' : Fin (Fintype.card ι) → ℝ := fun i => a (e i)
  have hind : LinearIndependent ℝ z' :=
    linearIndependent_of_affine_of_functional ℓ
      (fun i => hS _ (hz ⟨e i, rfl⟩)) (ha.comp_embedding e.toEmbedding)
  refine ⟨Fintype.card ι, z', a', (fun i => hz ⟨e i, rfl⟩),
    (fun i => hpos (e i)), ?_, ?_, hind, hind.injective, ?_⟩
  · exact (Equiv.sum_comp e a).trans hsum
  · exact (Equiv.sum_comp e (fun i => a i • z i)).trans heq
  · simpa using hind.fintype_card_le_finrank

end LocalCertification.Extremal
