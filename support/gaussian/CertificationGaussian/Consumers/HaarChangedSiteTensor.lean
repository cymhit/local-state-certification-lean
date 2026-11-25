import CertificationGaussian.HaarChangedSiteTensor

noncomputable section
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace CertificationGaussian.Consumers

/-- The actual local Haar tensor supplies every positivity and trace fact needed at a changed site. -/
theorem haar_changed_site_actual_tensor (d : ℕ) [NeZero d] (a b : Bool) :
    Integrable (localChangedSiteIntegrand d a b) (haarBasisRecords d) ∧
      (haarChangedSiteTensor d a b).PosSemidef ∧
      Matrix.trace (haarChangedSiteTensor d a b)=(d:ℂ)*((d:ℂ)-1)^(a.toNat+b.toNat) :=
  ⟨localChangedSiteIntegrand_integrable d a b,haarChangedSiteTensor_posSemidef d a b,
    haarChangedSiteTensor_trace_power d a b⟩

/-- Four actual local tensors, arbitrary input/complement choices and a genuine unitary contraction. -/
theorem haar_changed_site_cost (d : ℕ) [NeZero d] (hd : 2 ≤ d) (a b : Fin 4 → Bool)
    (U : Matrix (Fin 4 → ((Fin d × Fin d) × Fin d)) (Fin 4 → ((Fin d × Fin d) × Fin d)) ℂ)
    (hU : U ∈ unitary _) :
    ‖Matrix.trace (wickTensorMatrix (fun v : Fin 4 => haarChangedSiteTensor d (a v) (b v))*U)‖ ≤
      (d:ℝ)^4*((d:ℝ)-1)^8 := haarChangedSite_four_unitary_bound d hd a b U hU

/-- The constant is attained by the identity contraction when all eight input factors are complements. -/
theorem haar_changed_site_identity_sharp (d : ℕ) [NeZero d] :
    Matrix.trace (wickTensorMatrix (fun _v : Fin 4 => haarChangedSiteTensor d true true) * 1) =
      (d:ℂ)^4*((d:ℂ)-1)^8 := by
  rw [Matrix.mul_one,wickTensorMatrix_trace]
  simp only [haarChangedSiteTensor_trace,ite_true,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  ring

/-- In dimension two the actual tensor identity contraction has modulus 16. -/
theorem haar_changed_site_qubit_identity :
    ‖Matrix.trace (wickTensorMatrix (fun _v : Fin 4 => haarChangedSiteTensor 2 true true) * 1)‖ = (16:ℝ) := by
  rw [haar_changed_site_identity_sharp]
  norm_num

/-- The full-Haar qutrit instance has the actual changed-site cost 20736. -/
theorem haar_changed_site_qutrit_identity :
    ‖Matrix.trace (wickTensorMatrix (fun _v : Fin 4 => haarChangedSiteTensor 3 true true) * 1)‖ = (20736:ℝ) := by
  rw [haar_changed_site_identity_sharp]
  norm_num

/-- The one-dimensional endpoint still has a probability record and zero complement tensor trace. -/
theorem haar_changed_site_dimension_one :
    Matrix.trace (haarChangedSiteTensor 1 false false)=1 ∧
      Matrix.trace (haarChangedSiteTensor 1 true false)=0 ∧
      Matrix.trace (haarChangedSiteTensor 1 false true)=0 ∧
      Matrix.trace (haarChangedSiteTensor 1 true true)=0 := by
  norm_num [haarChangedSiteTensor_trace]

end CertificationGaussian.Consumers
