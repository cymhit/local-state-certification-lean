import LocalCertification.Quantum.WeylOrbit

set_option autoImplicit false
open Matrix MeasureTheory Metric Set CertificationGaussian Classical
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace LocalCertification.Quantum

/-- The exact two-term rank-one perturbation bound for unit vectors. -/
theorem unit_rankOne_dist_le {I : Type*} [Fintype I]
    (v w : EuclideanSpace ℂ I) (hv : ‖v‖=1) (hw : ‖w‖=1) :
    ‖InnerProductSpace.rankOne ℂ v v - InnerProductSpace.rankOne ℂ w w‖ ≤ 2*‖v-w‖ := by
  have he : InnerProductSpace.rankOne ℂ v v - InnerProductSpace.rankOne ℂ w w =
      InnerProductSpace.rankOne ℂ (v-w) v + InnerProductSpace.rankOne ℂ w (v-w) := by
    simp only [map_sub, _root_.sub_apply]
    abel
  rw [he]
  calc
    _ ≤ ‖InnerProductSpace.rankOne ℂ (v-w) v‖ + ‖InnerProductSpace.rankOne ℂ w (v-w)‖ := norm_add_le _ _
    _ = 2*‖v-w‖ := by simp only [InnerProductSpace.norm_rankOne, hv, hw]; ring

/-- The CLM is the literal outer-product matrix, in the same Euclidean operator norm. -/
theorem rectangularEuclideanCLM_rankOne {I : Type*} [Fintype I] [DecidableEq I]
    (v w : EuclideanSpace ℂ I) :
    rectangularEuclideanCLM (Matrix.vecMulVec v (star w)) = InnerProductSpace.rankOne ℂ v w := by
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toEuclideanLin (Matrix.vecMulVec v (star w)) x = _
  rw [← InnerProductSpace.symm_toEuclideanLin_rankOne, LinearEquiv.apply_symm_apply]
  rfl

theorem unit_rankOne_matrix_dist_le {I : Type*} [Fintype I] [DecidableEq I]
    (v w : EuclideanSpace ℂ I) (hv : ‖v‖=1) (hw : ‖w‖=1) :
    ‖Matrix.vecMulVec v (star v)-Matrix.vecMulVec w (star w)‖ ≤ 2*‖v-w‖ := by
  have he : rectangularEuclideanCLM (Matrix.vecMulVec v (star v)-Matrix.vecMulVec w (star w)) =
      InnerProductSpace.rankOne ℂ v v-InnerProductSpace.rankOne ℂ w w := by
    have hs : rectangularEuclideanCLM (Matrix.vecMulVec v (star v)-Matrix.vecMulVec w (star w)) =
        rectangularEuclideanCLM (Matrix.vecMulVec v (star v))-rectangularEuclideanCLM (Matrix.vecMulVec w (star w)) := by
      apply ContinuousLinearMap.ext
      intro x
      change Matrix.toEuclideanLin (Matrix.vecMulVec v (star v)-Matrix.vecMulVec w (star w)) x =
        (Matrix.toEuclideanLin (Matrix.vecMulVec v (star v))-Matrix.toEuclideanLin (Matrix.vecMulVec w (star w))) x
      rw [map_sub]
    rw [hs, rectangularEuclideanCLM_rankOne, rectangularEuclideanCLM_rankOne]
  rw [← rectangularEuclideanCLM_norm, he]
  exact unit_rankOne_dist_le v w hv hw

variable {d n : ℕ} [NeZero d]

/-- The target's corrected column is the genuine column of Q selected by the canonical identity label. -/
def lowWeylCorrectedTarget (L : ℕ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    EuclideanSpace ℂ (QuditIndex d n) :=
  rectangularEuclideanCLM (matrixPolarCorrection (unitaryOrbitMatrix (lowWeylFamily d n L) ψ))
    (EuclideanSpace.single (lowWeylIdentity d n L) 1)

theorem lowWeylOrbit_identity_apply (L : ℕ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    rectangularEuclideanCLM (unitaryOrbitMatrix (lowWeylFamily d n L) ψ)
      (EuclideanSpace.single (lowWeylIdentity d n L) 1) = ψ := by
  ext i
  change (unitaryOrbitMatrix (lowWeylFamily d n L) ψ *ᵥ
    (Pi.single (lowWeylIdentity d n L) 1)) i = ψ i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using lowWeylOrbit_identity_column L ψ i

/-- The corrected target is unit length and its actual rank-one projector differs by at most 2t. -/
theorem lowWeylOrbit_target_projector (L : ℕ)
    (ψ : EuclideanSpace ℂ (QuditIndex d n)) (hψ : ‖ψ‖=1) (t : ℝ) (ht : t<1)
    (hg : ‖Matrix.toEuclideanCLM (n := LowWeylIndex d n L) (𝕜 := ℂ)
      (unitaryOrbitGramError (lowWeylFamily d n L) ψ)‖ ≤ t) :
    ‖lowWeylCorrectedTarget (d := d) (n := n) L ψ‖=1 ∧
      ‖lowWeylCorrectedTarget (d := d) (n := n) L ψ-(ψ : EuclideanSpace ℂ (QuditIndex d n))‖ ≤ t ∧
      ‖Matrix.vecMulVec (lowWeylCorrectedTarget (d := d) (n := n) L ψ) (star (lowWeylCorrectedTarget (d := d) (n := n) L ψ)) -
        Matrix.vecMulVec (ψ : EuclideanSpace ℂ (QuditIndex d n)) (star (ψ : EuclideanSpace ℂ (QuditIndex d n)))‖ ≤ 2*t := by
  let V := unitaryOrbitMatrix (lowWeylFamily d n L) (ψ : EuclideanSpace ℂ (QuditIndex d n))
  let Q := matrixPolarCorrection V
  let e : EuclideanSpace ℂ (LowWeylIndex d n L) := EuclideanSpace.single (lowWeylIdentity d n L) 1
  have he : ‖e‖=1 := by simp [e]
  have hp := lowWeylOrbit_polar (d := d) (n := n) L ψ t ht hg
  have hq : ‖lowWeylCorrectedTarget (d := d) (n := n) L ψ‖=1 := (hp.2.2.1 e).trans he
  have hv : rectangularEuclideanCLM V e = ψ := lowWeylOrbit_identity_apply (d := d) (n := n) L ψ
  have hsub : rectangularEuclideanCLM (V-Q) e = (ψ : EuclideanSpace ℂ (QuditIndex d n))-lowWeylCorrectedTarget (d := d) (n := n) L ψ := by
    change Matrix.toEuclideanLin (V-Q) e = _
    rw [map_sub, LinearMap.sub_apply]
    change rectangularEuclideanCLM V e-rectangularEuclideanCLM Q e = _
    rw [hv]
    rfl
  have hd : ‖lowWeylCorrectedTarget (d := d) (n := n) L ψ-(ψ : EuclideanSpace ℂ (QuditIndex d n))‖ ≤ t := by
    rw [norm_sub_rev, ← hsub]
    calc
      _ ≤ ‖rectangularEuclideanCLM (V-Q)‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ t := by rw [he, mul_one]; exact hp.2.1
  refine ⟨hq,hd,?_⟩
  exact (unit_rankOne_matrix_dist_le _ _ hq hψ).trans
    (mul_le_mul_of_nonneg_left hd (by norm_num))

end LocalCertification.Quantum
