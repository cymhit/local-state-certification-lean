import CertificationGaussian.ScalarMoments
import CertificationGaussian.GaussianDensity
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace CertificationGaussian

/-- The actual product of standard real Gaussian coordinate measures. -/
abbrev realGaussianProduct (I : Type*) [Fintype I] : Measure (I → ℝ) :=
  Measure.pi (fun _ : I => gaussianReal 0 1)

theorem standardGaussian_moment_one : ∫ x : ℝ, x ∂gaussianReal 0 1 = 0 := by
  simp

theorem standardGaussian_moment_three : ∫ x : ℝ, x^3 ∂gaussianReal 0 1 = 0 := by
  have h := standardGaussian_wick_mean (n := 3) (by decide)
  have he (x : ℝ) : wickMonomial 3 1 x = x^3-3*x := by norm_num [wickMonomial]; ring
  simp_rw [he] at h
  have hi : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := by
    simpa using standardGaussian_integrable_pow 1
  rw [integral_sub (standardGaussian_integrable_pow 3) (hi.const_mul 3),
    integral_const_mul, standardGaussian_moment_one] at h
  simpa using h

variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem real_list_prod_eq_univ (l : List I) (x : I → ℝ) :
    (l.map x).prod = ∏ i, (x i)^(l.count i) := by
  rw [Finset.prod_list_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  simp only [List.mem_toFinset] at hi
  rw [List.count_eq_zero_of_not_mem hi, pow_zero]

/-- Actual product Gaussian moments with repeated coordinate indices. -/
theorem realGaussianProduct_list_moment (l : List I) :
    ∫ x, (l.map x).prod ∂realGaussianProduct I =
      ∏ i ∈ l.toFinset, ∫ t : ℝ, t^(l.count i) ∂gaussianReal 0 1 := by
  simp_rw [real_list_prod_eq_univ]
  rw [integral_fintype_prod_eq_prod (fun i (t : ℝ) => t^(l.count i))]
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  simp only [List.mem_toFinset] at hi
  simp [List.count_eq_zero_of_not_mem hi]

theorem realGaussianProduct_list_integrable (l : List I) :
    Integrable (fun x => (l.map x).prod) (realGaussianProduct I) := by
  simp_rw [real_list_prod_eq_univ]
  exact Integrable.fintype_prod (fun i => standardGaussian_integrable_pow (l.count i))

theorem realGaussianProduct_second_moment (i j : I) :
    ∫ x, x i*x j ∂realGaussianProduct I = if i=j then 1 else 0 := by
  have h := realGaussianProduct_list_moment [i,j]
  by_cases hij : i=j <;> simpa [hij, standardGaussian_moment_one, standardGaussian_moment_two] using h

/-- Wick's fourth moment for the standard real Gaussian itself; there is no excess fourth cumulant. -/
theorem realGaussianProduct_fourth_moment (i j k l : I) :
    ∫ x, x i*x j*x k*x l ∂realGaussianProduct I =
      (if i=j then 1 else 0)*(if k=l then 1 else 0) +
      (if i=k then 1 else 0)*(if j=l then 1 else 0) +
      (if i=l then 1 else 0)*(if j=k then 1 else 0) := by
  have h := realGaussianProduct_list_moment [i,j,k,l]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  simp only [← mul_assoc] at h
  rw [h]
  clear h
  simp only [List.count_cons, List.count_nil, beq_iff_eq]
  by_cases hij : i=j <;> by_cases hik : i=k <;> by_cases hil : i=l <;>
    by_cases hjk : j=k <;> by_cases hjl : j=l <;> by_cases hkl : k=l <;>
    simp_all [eq_comm, standardGaussian_moment_two,
      standardGaussian_moment_three, standardGaussian_moment_four]
  all_goals norm_num

@[fun_prop] theorem realGaussianProduct_pair_integrable (i j : I) :
    Integrable (fun x => x i*x j) (realGaussianProduct I) := by
  simpa using realGaussianProduct_list_integrable [i,j]

@[fun_prop] theorem realGaussianProduct_four_integrable (i j k l : I) :
    Integrable (fun x => x i*x j*x k*x l) (realGaussianProduct I) := by
  simpa [mul_assoc] using realGaussianProduct_list_integrable [i,j,k,l]

omit [DecidableEq I] in
/-- Transport of arbitrary real integrands through the actual coordinate equivalence. -/
theorem stdGaussian_integral_eq_product (f : EuclideanSpace ℝ I → ℝ) :
    ∫ x, f x ∂stdGaussian (EuclideanSpace ℝ I) =
      ∫ x, f (WithLp.toLp 2 x) ∂realGaussianProduct I := by
  rw [← map_pi_eq_stdGaussian]
  exact (MeasurableEquiv.toLp 2 (I → ℝ)).measurableEmbedding.integral_map f

theorem stdGaussian_coordinate_second_moment (i j : I) :
    ∫ x : EuclideanSpace ℝ I, x i*x j ∂stdGaussian _ = if i=j then 1 else 0 := by
  rw [stdGaussian_integral_eq_product]
  exact realGaussianProduct_second_moment i j

theorem stdGaussian_coordinate_fourth_moment (i j k l : I) :
    ∫ x : EuclideanSpace ℝ I, x i*x j*x k*x l ∂stdGaussian _ =
      (if i=j then 1 else 0)*(if k=l then 1 else 0) +
      (if i=k then 1 else 0)*(if j=l then 1 else 0) +
      (if i=l then 1 else 0)*(if j=k then 1 else 0) := by
  rw [stdGaussian_integral_eq_product]
  exact realGaussianProduct_fourth_moment i j k l

theorem stdGaussian_norm_second_moment :
    ∫ x : EuclideanSpace ℝ I, ‖x‖^2 ∂stdGaussian _ = (Fintype.card I : ℝ) := by
  rw [stdGaussian_integral_eq_product]
  simp_rw [EuclideanSpace.real_norm_sq_eq, pow_two]
  rw [integral_finsetSum _ (fun i _ => realGaussianProduct_pair_integrable i i)]
  simp [realGaussianProduct_second_moment]

theorem stdGaussian_norm_fourth_moment :
    ∫ x : EuclideanSpace ℝ I, ‖x‖^4 ∂stdGaussian _ =
      (Fintype.card I : ℝ)*((Fintype.card I : ℝ)+2) := by
  rw [stdGaussian_integral_eq_product]
  have he (x : I → ℝ) : ‖WithLp.toLp 2 x‖^4 = ∑ i, ∑ j, x i*x i*x j*x j := by
    rw [show (4:Nat)=2*2 by norm_num, pow_mul, EuclideanSpace.real_norm_sq_eq]
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => realGaussianProduct_four_integrable i i j j))]
  simp_rw [integral_finsetSum _ (fun j _ => realGaussianProduct_four_integrable _ _ j j),
    realGaussianProduct_fourth_moment]
  simp only [ite_true, mul_one]
  simp only [mul_ite, mul_one, mul_zero]
  simp [Finset.sum_add_distrib]
  ring

end CertificationGaussian
