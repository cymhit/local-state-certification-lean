import CertificationGaussian.ScalarMoments
import CertificationGaussian.KernelTrace
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev blockGaussian (I : Type*) [Fintype I] : Measure (I → ℝ × ℝ) :=
  Measure.pi (fun _ : I => standardGaussianPair)

private theorem list_prod_eq_univ (l : List I) (f : I → ℝ) :
    (l.map f).prod = ∏ i, (f i)^(l.count i) := by
  rw [Finset.prod_list_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  simp only [List.mem_toFinset] at hi
  rw [List.count_eq_zero_of_not_mem hi, pow_zero]

/-- Finite product moments with repeated coordinate indices, using their actual multiplicities. -/
theorem blockGaussian_list_moment (l : List I) :
    ∫ z, (l.map (fun i => radialPairOutcome (z i))).prod ∂blockGaussian I =
      ∏ i ∈ l.toFinset, ∫ w, (radialPairOutcome w)^(l.count i) ∂standardGaussianPair := by
  simp_rw [list_prod_eq_univ]
  rw [integral_fintype_prod_eq_prod (fun i (w : ℝ × ℝ) => (radialPairOutcome w)^(l.count i))]
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  simp only [List.mem_toFinset] at hi
  simp [List.count_eq_zero_of_not_mem hi]

theorem blockGaussian_list_integrable (l : List I) (hl : l.length ≤ 4) :
    Integrable (fun z => (l.map (fun i => radialPairOutcome (z i))).prod) (blockGaussian I) := by
  simp_rw [list_prod_eq_univ]
  exact Integrable.fintype_prod (fun i =>
    radialPairOutcome_integrable_pow _ (List.count_le_length.trans hl))

theorem blockGaussian_second_moment (i j : I) :
    ∫ z, radialPairOutcome (z i) * radialPairOutcome (z j) ∂blockGaussian I =
      if i = j then 1 else 0 := by
  have h := blockGaussian_list_moment [i,j]
  by_cases hij : i = j <;>
    simpa [hij, radialPairOutcome_mean, radialPairOutcome_moment_two] using h

/-- The fourth joint moment includes the excess fourth moment 6 at coinciding indices. -/
theorem blockGaussian_fourth_moment (i j k l : I) :
    ∫ z, radialPairOutcome (z i) * radialPairOutcome (z j) *
      radialPairOutcome (z k) * radialPairOutcome (z l) ∂blockGaussian I =
    (if i = j then 1 else 0) * (if k = l then 1 else 0) +
    (if i = k then 1 else 0) * (if j = l then 1 else 0) +
    (if i = l then 1 else 0) * (if j = k then 1 else 0) +
    (if i = j ∧ j = k ∧ k = l then 6 else 0) := by
  have h := blockGaussian_list_moment [i,j,k,l]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  simp only [← mul_assoc] at h
  rw [h]
  clear h
  simp only [List.count_cons, List.count_nil, beq_iff_eq]
  by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hil : i = l <;>
    by_cases hjk : j = k <;> by_cases hjl : j = l <;> by_cases hkl : k = l <;>
    simp_all [eq_comm, radialPairOutcome_mean, radialPairOutcome_moment_two,
      radialPairOutcome_moment_three, radialPairOutcome_moment_four]
  all_goals norm_num

/-- The unnormalized quadratic form in the actual independent centered square moduli. -/
def blockQuadratic (B : Matrix I I ℝ) (z : I → ℝ × ℝ) : ℝ :=
  ∑ i, ∑ j, B i j * radialPairOutcome (z i) * radialPairOutcome (z j)

theorem blockGaussian_pair_integrable (i j : I) :
    Integrable (fun z => radialPairOutcome (z i) * radialPairOutcome (z j)) (blockGaussian I) := by
  simpa using blockGaussian_list_integrable [i,j] (by simp)

theorem blockGaussian_four_integrable (i j k l : I) :
    Integrable (fun z => radialPairOutcome (z i) * radialPairOutcome (z j) *
      radialPairOutcome (z k) * radialPairOutcome (z l)) (blockGaussian I) := by
  simpa [mul_assoc] using blockGaussian_list_integrable [i,j,k,l] (by simp)

@[fun_prop] theorem blockQuadratic_integrable (B : Matrix I I ℝ) :
    Integrable (blockQuadratic B) (blockGaussian I) := by
  unfold blockQuadratic
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  simpa [mul_assoc] using (blockGaussian_pair_integrable i j).const_mul (B i j)

theorem blockQuadratic_mean (B : Matrix I I ℝ) :
    ∫ z, blockQuadratic B z ∂blockGaussian I = Matrix.trace B := by
  unfold blockQuadratic
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => by simpa [mul_assoc] using (blockGaussian_pair_integrable i j).const_mul (B i j)))]
  calc
    _ = ∑ i, ∑ j, B i j * (if i = j then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => by
        simpa [mul_assoc] using (blockGaussian_pair_integrable i j).const_mul (B i j))]
      apply Finset.sum_congr rfl
      intro j _
      simp only [mul_assoc, integral_const_mul, blockGaussian_second_moment]
    _ = Matrix.trace B := by simp [Matrix.trace, Matrix.diag]

omit [DecidableEq I] in
private theorem blockQuadratic_sq_expand (B : Matrix I I ℝ) (z : I → ℝ × ℝ) :
    (blockQuadratic B z)^2 = ∑ i, ∑ j, ∑ k, ∑ l,
      (B i j * B k l) * (radialPairOutcome (z i) * radialPairOutcome (z j) *
        radialPairOutcome (z k) * radialPairOutcome (z l)) := by
  simp only [blockQuadratic, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

@[fun_prop] theorem blockQuadratic_sq_integrable (B : Matrix I I ℝ) :
    Integrable (fun z => (blockQuadratic B z)^2) (blockGaussian I) := by
  simp_rw [blockQuadratic_sq_expand]
  apply integrable_finsetSum; intro i _
  apply integrable_finsetSum; intro j _
  apply integrable_finsetSum; intro k _
  apply integrable_finsetSum; intro l _
  exact (blockGaussian_four_integrable i j k l).const_mul _

theorem blockQuadratic_second_moment (B : Matrix I I ℝ) :
    ∫ z, (blockQuadratic B z)^2 ∂blockGaussian I =
      (Matrix.trace B)^2 + (∑ i, ∑ j, (B i j)^2) +
      (∑ i, ∑ j, B i j * B j i) + 6 * ∑ i, (B i i)^2 := by
  simp_rw [blockQuadratic_sq_expand]
  simp_rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => integrable_finsetSum _ (fun k _ => integrable_finsetSum _
      (fun l _ => (blockGaussian_four_integrable i j k l).const_mul _))))]
  simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _
    (fun k _ => integrable_finsetSum _
      (fun l _ => (blockGaussian_four_integrable _ j k l).const_mul _)))]
  simp_rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _
    (fun l _ => (blockGaussian_four_integrable _ _ k l).const_mul _))]
  simp_rw [integral_finsetSum _ (fun l _ =>
    (blockGaussian_four_integrable _ _ _ l).const_mul _)]
  simp_rw [integral_const_mul, blockGaussian_fourth_moment, mul_add,
    Finset.sum_add_distrib]
  simp only [mul_ite, mul_one, mul_zero, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.mem_univ, ite_true, Finset.sum_ite_eq]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, Matrix.trace, Matrix.diag, pow_two]
  ring

/-- The actual centered second moment of a real symmetric quadratic form. -/
theorem blockQuadratic_centered_second (B : Matrix I I ℝ)
    (hB : ∀ i j, B i j = B j i) :
    ∫ z, (blockQuadratic B z - Matrix.trace B)^2 ∂blockGaussian I =
      2 * Matrix.trace (B*B) + 6 * ∑ i, (B i i)^2 := by
  have he (z : I → ℝ × ℝ) : (blockQuadratic B z - Matrix.trace B)^2 =
      (blockQuadratic B z)^2 - (2*Matrix.trace B)*blockQuadratic B z + (Matrix.trace B)^2 := by ring
  simp_rw [he]
  erw [integral_add ((blockQuadratic_sq_integrable B).sub
    ((blockQuadratic_integrable B).const_mul _)) (integrable_const _),
    integral_sub (blockQuadratic_sq_integrable B)
      ((blockQuadratic_integrable B).const_mul _), integral_const_mul,
    blockQuadratic_mean, blockQuadratic_second_moment]
  have ht : (∑ i, ∑ j, B i j * B j i) = Matrix.trace (B*B) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [ht, ← trace_square_eq_sum_sq B hB]
  simp only [integral_const, probReal_univ, one_smul]
  ring

end CertificationGaussian
