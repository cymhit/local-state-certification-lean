import CertificationGaussian.BellPartialTranspose

noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian

/-- The actual local identity Bell projector, with the previously fixed normalization and ordering. -/
def radialChoiPhi (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  unitaryBellProjector (1 : Matrix (Fin d) (Fin d) ℂ)

/-- The local Choi factor with eigenvalue one on the identity Bell vector. -/
def radialChoiA0 (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  radialChoiPhi d + (d+1 : ℂ)⁻¹ • (1-radialChoiPhi d)

/-- The local complementary Choi factor. -/
def radialChoiR0 (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (d+1 : ℂ)⁻¹ • (1-radialChoiPhi d)

/-- Partial transpose fixes the actual identity matrix. -/
theorem partialTransposeFirst_one {I : Type*} [DecidableEq I] :
    partialTransposeFirst (1 : Matrix (I × I) (I × I) ℂ)=1 := by
  ext ⟨i,r⟩ ⟨j,s⟩
  simp only [partialTransposeFirst,Matrix.one_apply,Prod.mk.injEq]
  by_cases hij : i=j <;> by_cases hrs : r=s <;> simp_all [eq_comm]

theorem partialTransposeFirst_add {I : Type*} (A B : Matrix (I × I) (I × I) ℂ) :
    partialTransposeFirst (A+B)=partialTransposeFirst A+partialTransposeFirst B := by
  ext p q
  rfl

/-- This is the same genuine unitary involution as in the Bell partial-transpose theorem. -/
theorem radialChoiPhi_partialTranspose (d : ℕ) :
    partialTransposeFirst (radialChoiPhi d)=
      (d:ℂ)⁻¹ • bellPartialTransposeUnitary (1 : Matrix (Fin d) (Fin d) ℂ) := by
  simpa [radialChoiPhi] using
    unitaryBellProjector_partialTranspose (1 : Matrix (Fin d) (Fin d) ℂ)

/-- The exact local A0 partial transpose; the dimension is positive. -/
theorem radialChoiA0_partialTranspose (d : ℕ) (hd : 0<d) :
    partialTransposeFirst (radialChoiA0 d)=
      (d+1:ℂ)⁻¹ • (1+bellPartialTransposeUnitary (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  have hd0 : (d:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hd
  have hq0 : (d+1:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt (Nat.succ_pos d)
  rw [radialChoiA0,partialTransposeFirst_add,partialTransposeFirst_smul,
    partialTransposeFirst_sub,partialTransposeFirst_one,radialChoiPhi_partialTranspose]
  ext p q
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  field_simp
  ring

/-- The exact local R0 partial transpose, before any norm bound. -/
theorem radialChoiR0_partialTranspose (d : ℕ) :
    partialTransposeFirst (radialChoiR0 d)=
      (d+1:ℂ)⁻¹ • (1-(d:ℂ)⁻¹ • bellPartialTransposeUnitary (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  rw [radialChoiR0,partialTransposeFirst_smul,partialTransposeFirst_sub,
    partialTransposeFirst_one,radialChoiPhi_partialTranspose]

/-- The bound needed for the original Choi-tail estimate, in the actual L2 operator norm. -/
theorem radialChoiA0_partialTranspose_norm_le (d : ℕ) (hd : 0<d) :
    ‖partialTransposeFirst (radialChoiA0 d)‖ ≤ 2/(d+1:ℝ) := by
  let F := bellPartialTransposeUnitary (1 : Matrix (Fin d) (Fin d) ℂ)
  have hF : ‖F‖≤1 := by
    exact unitary_matrix_norm_le_one F (bellPartialTransposeUnitary_mem _ (by simp))
  have hI : ‖(1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)‖≤1 :=
    unitary_matrix_norm_le_one _ (by simp)
  rw [radialChoiA0_partialTranspose d hd,norm_smul,norm_inv]
  have hq : ‖(d+1:ℂ)‖=(d+1:ℝ) := by
    simpa only [Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one] using
      Complex.norm_of_nonneg (show 0≤(d:ℝ)+1 by positivity)
  rw [hq]
  calc
    _ ≤ (d+1:ℝ)⁻¹ * (1+1) := mul_le_mul_of_nonneg_left
      ((norm_add_le _ _).trans (add_le_add hI hF)) (by positivity)
    _ = _ := by ring

/-- The R0 bound includes d=1, where its actual norm is zero. -/
theorem radialChoiR0_partialTranspose_norm_le (d : ℕ) (hd : 0<d) :
    ‖partialTransposeFirst (radialChoiR0 d)‖ ≤ (d:ℝ)⁻¹ := by
  have hd0 : (d:ℝ)>0 := by exact_mod_cast hd
  let F := bellPartialTransposeUnitary (1 : Matrix (Fin d) (Fin d) ℂ)
  have hF : ‖F‖≤1 :=
    unitary_matrix_norm_le_one F (bellPartialTransposeUnitary_mem _ (by simp))
  have hI : ‖(1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)‖≤1 :=
    unitary_matrix_norm_le_one _ (by simp)
  rw [radialChoiR0_partialTranspose,norm_smul,norm_inv]
  have hq : ‖(d+1:ℂ)‖=(d+1:ℝ) := by
    simpa only [Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one] using
      Complex.norm_of_nonneg (show 0≤(d:ℝ)+1 by positivity)
  rw [hq]
  calc
    _ ≤ (d+1:ℝ)⁻¹ * (1+(d:ℝ)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine (norm_sub_le _ _).trans (add_le_add hI ?_)
      rw [norm_smul,norm_inv,Complex.norm_natCast]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hF (show 0≤(d:ℝ)⁻¹ by positivity)
    _ = _ := by field_simp

end CertificationGaussian
