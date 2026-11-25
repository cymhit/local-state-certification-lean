import CertificationGaussian.RadialBellChoi

noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian.Consumers

/-- A genuine complete phase-unitary fixture, deliberately distinct from canonical Weyl definitions. -/
def completePhaseBellFamily (k : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![1,!![0,Complex.I;Complex.I,0],!![0,-Complex.I;Complex.I,0],!![1,0;0,-1]] k

theorem completePhaseBellFamily_identity : completePhaseBellFamily 0=1 := rfl

theorem completePhaseBellFamily_unitary (k : Fin 4) :
    completePhaseBellFamily k∈unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  change completePhaseBellFamily k∈Matrix.unitaryGroup (Fin 2) ℂ
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [completePhaseBellFamily,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two]

theorem completePhaseBellFamily_hilbertSchmidt (k l : Fin 4) :
    Matrix.trace ((completePhaseBellFamily k)ᴴ*completePhaseBellFamily l)=
      if k=l then (2:ℂ) else 0 := by
  fin_cases k <;> fin_cases l <;>
    norm_num [completePhaseBellFamily,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Fin.sum_univ_two]

/-- Individual Hermiticity is not used by the actual Bell/Choi identity. -/
theorem completePhaseBellFamily_not_hermitian : ¬(completePhaseBellFamily 1).IsHermitian := by
  intro h
  have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 0 1).im) h.eq
  norm_num [completePhaseBellFamily,Matrix.conjTranspose_apply] at he

/-- The actual weighted Bell operator for any number of sites and arbitrary signed coefficients. -/
theorem complete_phase_radial_choi (n r : ℕ) (lam : ℕ → ℝ) :
    weightedBellMatrix (fun w : Fin n → Fin 4 => wickTensorMatrix (fun s => completePhaseBellFamily (w s)))
      (fun w => radialFirstCoefficient 2 r lam (radialBellSupport 0 w).card)=
      radialChoiCombination 2 r lam := by
  exact radialFirstCoefficient_bell_matrix 2 (by omega) completePhaseBellFamily 0 rfl
    completePhaseBellFamily_hilbertSchmidt (by norm_num) r lam

/-- Its squared-weight companion is the same actual matrix as the second tensor Choi formula. -/
theorem complete_phase_second_radial_choi (n r : ℕ) (lam : ℕ → ℝ) :
    weightedBellMatrix (fun w : Fin n → Fin 4 => wickTensorMatrix (fun s => completePhaseBellFamily (w s)))
      (fun w => radialSecondCoefficient 2 r lam (radialBellSupport 0 w).card)=
      radialChoiSecondCombination 2 r lam := by
  exact radialSecondCoefficient_bell_matrix 2 (by omega) completePhaseBellFamily 0 rfl
    completePhaseBellFamily_hilbertSchmidt (by norm_num) r lam

/-- The signed three-qubit radial Bell matrix has partial-transpose norm at most 80/27. -/
theorem complete_phase_signed_three_qubit_bound :
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (partialTransposeFirst
      (weightedBellMatrix (fun w : Fin 3 → Fin 4 => wickTensorMatrix (fun s => completePhaseBellFamily (w s)))
        (fun w => radialFirstCoefficient 2 1 (fun j => if j=0 then 1 else -2)
          (radialBellSupport 0 w).card)))‖ ≤ (80:ℝ)/27 := by
  have h := radialFirstCoefficient_bell_partialTranspose_bound (S:=Fin 3) 2 (by omega)
    completePhaseBellFamily 0 rfl completePhaseBellFamily_hilbertSchmidt (by norm_num) 1
      (fun j => if j=0 then 1 else -2)
  norm_num [Fin.sum_univ_succ,Nat.choose] at h
  exact h

/-- Weight means support cardinality; repeated nonidentity labels at different sites are counted separately. -/
theorem radial_repeated_label_support :
    radialFirstCoefficient 2 1 (fun j => if j=0 then 1 else -2)
      (radialBellSupport (0:Fin 4) (fun _ : Fin 3 => (1:Fin 4))).card = -(11:ℝ)/27 := by
  norm_num [radialFirstCoefficient,radialBellSupport,Fin.sum_univ_succ,Nat.choose]

/-- Empty physical sites give zero support and retain the original constant coefficient. -/
theorem radial_empty_sites (d r : ℕ) (lam : ℕ → ℝ) (w : Fin 0 → Fin 4) :
    radialFirstCoefficient d r lam (radialBellSupport 0 w).card=lam 0 := by
  simp [radialBellSupport,radialFirstCoefficient,Fin.sum_univ_succ,Nat.choose_zero_succ]

/-- The dimension-one complete family is a genuine instance, rather than an excluded denominator case. -/
theorem radial_dimension_one_identity (n r : ℕ) (lam : ℕ → ℝ) :
    weightedBellMatrix (fun _w : Fin n → Fin 1 =>
      wickTensorMatrix (fun _s : Fin n => (1 : Matrix (Fin 1) (Fin 1) ℂ)))
      (fun w => radialFirstCoefficient 1 r lam (radialBellSupport 0 w).card)=
      radialChoiCombination 1 r lam := by
  apply radialFirstCoefficient_bell_matrix 1 (by omega) (fun _ : Fin 1 => 1) 0 rfl
  · intro k l
    fin_cases k
    fin_cases l
    norm_num [Matrix.trace,Matrix.diag_apply]
  · norm_num

end CertificationGaussian.Consumers
