import CertificationGaussian.ChangedSiteContraction
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace CertificationGaussian

section FiniteTensors
variable {S T I : Type*} [Fintype S] [Fintype T] [Fintype I]
    [DecidableEq S] [DecidableEq T] [DecidableEq I]

omit [Fintype T] [DecidableEq T] [DecidableEq I] in
/-- Actual tensor matrices multiply site by site, including an empty set of physical sites. -/
theorem wickTensorMatrix_mul (A B : S → Matrix I I ℂ) :
    wickTensorMatrix A*wickTensorMatrix B=wickTensorMatrix (fun s => A s*B s) := by
  ext x y
  simp only [Matrix.mul_apply,wickTensorMatrix]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun s z => A s (x s) z*B s z (y s))).symm

omit [Fintype T] [DecidableEq T] in
/-- The original four-output matrix trace is the product of its physical-site traces. -/
theorem wickTensorMatrix_four_trace (P : Fin 4 → S → Matrix I I ℂ) :
    Matrix.trace (wickTensorMatrix (P 0)*wickTensorMatrix (P 1)*
      wickTensorMatrix (P 2)*wickTensorMatrix (P 3)) =
      ∏ s,Matrix.trace (P 0 s*P 1 s*P 2 s*P 3 s) := by
  simp only [wickTensorMatrix_mul,wickTensorMatrix_trace]

/-- The actual input tensor/Wick trace factors by sites, retaining the same inverse-permutation convention. -/
theorem wickTensorMatrix_site_permutation_trace (A : T → S → Matrix I I ℂ)
    (π : Equiv.Perm T) :
    Matrix.trace (wickTensorMatrix (fun t => wickTensorMatrix (A t))*wickTensorPermutationMatrix π) =
      ∏ s,Matrix.trace (wickTensorMatrix (fun t => A t s)*wickTensorPermutationMatrix π) := by
  simp only [wickTensorMatrix_permutation_trace,wickTensorMatrix]
  let e := Equiv.piComm (fun (_ : T) (_ : S) => I)
  rw [← e.symm.sum_comp (fun x : T → S → I => ∏ t,∏ s,A t s (x t s) (x (π.symm t) s))]
  calc
    _ = ∑ x : S → T → I, ∏ s,∏ t,A t s (x s t) (x s (π.symm t)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.prod_comm
    _ = _ := (Fintype.prod_sum (fun s (x : T → I) => ∏ t,A t s (x t) (x (π.symm t)))).symm

/-- The genuine output-cycle times input-Wick trace factors sitewise without taking absolute values. -/
theorem wickTensorMatrix_site_contraction (P : Fin 4 → S → Matrix I I ℂ)
    (A : (Fin 4 × Fin 2) → S → Matrix I I ℂ) (π : Equiv.Perm (Fin 4 × Fin 2)) :
    Matrix.trace (wickTensorMatrix (P 0)*wickTensorMatrix (P 1)*
      wickTensorMatrix (P 2)*wickTensorMatrix (P 3))*
      Matrix.trace (wickTensorMatrix (fun t => wickTensorMatrix (A t))*wickTensorPermutationMatrix π) =
      ∏ s,Matrix.trace (P 0 s*P 1 s*P 2 s*P 3 s)*
        Matrix.trace (wickTensorMatrix (fun t => A t s)*wickTensorPermutationMatrix π) := by
  rw [wickTensorMatrix_four_trace,wickTensorMatrix_site_permutation_trace,Finset.prod_mul_distrib]

end FiniteTensors

/-- Rearranging four complete global records into one four-record tuple at each physical site. -/
def fourRecordSiteEquiv (S Ω : Type*) [MeasurableSpace Ω] :
    (S → Ω × (Ω × (Ω × Ω))) ≃ᵐ ((S → Ω) × ((S → Ω) × ((S → Ω) × (S → Ω)))) where
  toFun x := (fun s => (x s).1,fun s => (x s).2.1,fun s => (x s).2.2.1,fun s => (x s).2.2.2)
  invFun x := fun s => (x.1 s,x.2.1 s,x.2.2.1 s,x.2.2.2 s)
  left_inv x := rfl
  right_inv x := rfl
  measurable_toFun := by
    change Measurable (fun x : S → Ω × (Ω × (Ω × Ω)) =>
      (fun s => (x s).1,fun s => (x s).2.1,fun s => (x s).2.2.1,fun s => (x s).2.2.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun x : (S → Ω) × ((S → Ω) × ((S → Ω) × (S → Ω))) =>
      fun s => (x.1 s,x.2.1 s,x.2.2.1 s,x.2.2.2 s))
    fun_prop

/-- The real four-copy law of the product record probability is precisely the product of the local four-copy laws. -/
theorem fourRecordSiteEquiv_measurePreserving {S Ω : Type*} [Fintype S] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    MeasurePreserving (fourRecordSiteEquiv S Ω)
      (Measure.pi (fun _ : S => fourReadoutLaw μ))
      (fourReadoutLaw (Measure.pi (fun _ : S => μ))) := by
  have h1 := measurePreserving_arrowProdEquivProdArrow Ω (Ω × (Ω × Ω)) S
    (fun _ => μ) (fun _ => μ.prod (μ.prod μ))
  have h2 := measurePreserving_arrowProdEquivProdArrow Ω (Ω × Ω) S
    (fun _ => μ) (fun _ => μ.prod μ)
  have h3 := measurePreserving_arrowProdEquivProdArrow Ω Ω S (fun _ => μ) (fun _ => μ)
  exact ((MeasurePreserving.id _).prod (((MeasurePreserving.id _).prod h3).comp h2)).comp h1

/-- Exact integral factorization for arbitrary complex local contractions under four genuine global records. -/
theorem fourRecordSite_integral_product {S Ω : Type*} [Fintype S] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : S → Ω × (Ω × (Ω × Ω)) → ℂ) :
    (∫ x,∏ s,f s (x.1 s,x.2.1 s,x.2.2.1 s,x.2.2.2 s)
      ∂fourReadoutLaw (Measure.pi (fun _ : S => μ))) =
      ∏ s,∫ x,f s x ∂fourReadoutLaw μ := by
  calc
    _ = ∫ x : S → Ω × (Ω × (Ω × Ω)),∏ s,f s (x s)
        ∂Measure.pi (fun _ : S => fourReadoutLaw μ) :=
      ((fourRecordSiteEquiv_measurePreserving (S:=S) μ).integral_comp'
        (fun x => ∏ s,f s (x.1 s,x.2.1 s,x.2.2.1 s,x.2.2.2 s))).symm
    _ = _ := integral_fintype_prod_eq_prod f

end CertificationGaussian
