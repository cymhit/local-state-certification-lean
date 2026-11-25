import CertificationGaussian.ReadoutRadialControl

noncomputable section
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian

/-- Deterministic error bound for the exact full-second-moment identity in the genuine Euclidean operator norm. -/
theorem full_second_identity_error_bound {I : Type*} [Fintype I] [DecidableEq I]
    (M S Z B : Matrix I I ℂ) (nu h a : ℝ)
    (hM : M=nu • (1:Matrix I I ℂ)+a • S+a^2 • Z+(2*(a-1)*h) • B-
      ((a-1)^2*(nu+h^2)) • (1:Matrix I I ℂ)) :
    ‖Matrix.toEuclideanCLM (n:=I) (𝕜:=ℂ) (M-nu • (1:Matrix I I ℂ)-S)‖ ≤
      |a-1| *‖Matrix.toEuclideanCLM (n:=I) (𝕜:=ℂ) S‖+
      a^2*‖Matrix.toEuclideanCLM (n:=I) (𝕜:=ℂ) Z‖+
      2*|a-1| *|h| *‖Matrix.toEuclideanCLM (n:=I) (𝕜:=ℂ) B‖+
      |a-1|^2*(|nu|+h^2) := by
  have he : M-nu • (1:Matrix I I ℂ)-S =
      (a-1) • S+a^2 • Z+(2*(a-1)*h) • B-((a-1)^2*(nu+h^2)) • (1:Matrix I I ℂ) := by
    rw [hM,sub_smul,one_smul]
    abel
  have hI : ‖(1:Matrix I I ℂ)‖≤1 := by
    simpa only [Matrix.l2_opNorm_toEuclideanCLM] using
      unitary_matrix_norm_le_one (1:Matrix I I ℂ) (by simp)
  have hc : ‖((a-1)^2*(nu+h^2)) • (1:Matrix I I ℂ)‖≤|a-1|^2*(|nu|+h^2) := by
    rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_pow]
    calc
      _ ≤ |a-1|^2*(|nu|+h^2)*1 := by gcongr; exact (abs_add_le _ _).trans_eq (by rw [abs_of_nonneg (sq_nonneg h)])
      _ = _ := mul_one _
  simp only [Matrix.l2_opNorm_toEuclideanCLM]
  rw [he]
  calc
    _ ≤ ‖(a-1) • S+a^2 • Z+(2*(a-1)*h) • B‖+
        ‖((a-1)^2*(nu+h^2)) • (1:Matrix I I ℂ)‖ := norm_sub_le _ _
    _ ≤ (‖(a-1) • S‖+‖a^2 • Z‖)+‖(2*(a-1)*h) • B‖+|a-1|^2*(|nu|+h^2) := by
      apply add_le_add _ hc
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = _ := by simp only [norm_smul,Real.norm_eq_abs,abs_pow,abs_mul,sq_abs,abs_of_pos (show (0:ℝ)<2 by norm_num)]

/-- On a good radius event the deterministic full-second-moment error has explicit finite bounds. -/
theorem full_second_identity_error_of_good_radius {I : Type*} [Fintype I] [DecidableEq I]
    (M S Z B : Matrix I I ℂ) (nu h a δ ε Kb Ks : ℝ)
    (hM : M=nu • (1:Matrix I I ℂ)+a • S+a^2 • Z+(2*(a-1)*h) • B-
      ((a-1)^2*(nu+h^2)) • (1:Matrix I I ℂ))
    (ha0 : 0≤a) (ha2 : a≤2) (hδ : 0≤δ) (ha : |a-1|≤2*δ)
    (hZ : ‖Matrix.toEuclideanCLM (n:=I) (𝕜:=ℂ) Z‖≤ε)
    (hB : ‖Matrix.toEuclideanCLM (n:=I) (𝕜:=ℂ) B‖≤Kb)
    (hS : ‖Matrix.toEuclideanCLM (n:=I) (𝕜:=ℂ) S‖≤Ks) :
    ‖Matrix.toEuclideanCLM (n:=I) (𝕜:=ℂ) (M-nu • (1:Matrix I I ℂ)-S)‖ ≤
      2*δ*Ks+4*ε+4*δ*|h| *Kb+4*δ^2*(|nu|+h^2) := by
  have hε : 0≤ε := (norm_nonneg _).trans hZ
  have hKb : 0≤Kb := (norm_nonneg _).trans hB
  have hKs : 0≤Ks := (norm_nonneg _).trans hS
  have haSq : a^2≤4 := by nlinarith
  have hsq : |a-1|^2≤(2*δ)^2 := pow_le_pow_left₀ (abs_nonneg _) ha 2
  refine (full_second_identity_error_bound M S Z B nu h a hM).trans ?_
  calc
    _ ≤ (2*δ)*Ks+4*ε+2*(2*δ)*|h| *Kb+(2*δ)^2*(|nu|+h^2) := by gcongr
    _ = _ := by ring

/-- On the actual radial and remainder good events, bounded actual B and S control the full second-moment error. -/
theorem cardinalityHaar_second_error_of_good_radius (d n r : ℕ) (hd : 2≤d) (hn : 2≤n) (lam : ℕ → ℝ) (Kb Ks : ℝ)
    (x : Fin 2 × QuditIndex d n → ℝ)
    (e₀ : Metric.sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)
    (hx : |gaussianRadius (QuditIndex d n) x-1|≤((n:ℝ)^(r+4))⁻¹) :
    let D := (d:ℝ)^n
    let h := cardinalityReadoutTraceScale d n r lam
    let nu := cardinalityReadoutTraceScale d n r (fun j => (lam j)^2)
    let ψ : QuditIndex d n → ℂ := (sphereDirection e₀ (WithLp.toLp 2 (complexCoordinate x)) : EuclideanSpace ℂ (QuditIndex d n))
    let B := cardinalityReadoutMean d (haarBasisRecords d) id r lam D ψ
    let S := cardinalityReadoutAuxiliary d (haarBasisRecords d) id r lam D ψ
    let M := cardinalityReadoutSecond d (haarBasisRecords d) id r lam D ψ
    let Z := cardinalityReadoutRemainder d (haarBasisRecords d) id r lam (complexCoordinate x)
    ‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ) Z‖≤((n:ℝ)^3)⁻¹ →
    ‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ) B‖≤Kb →
    ‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ) S‖≤Ks →
    ‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ) (M-nu • (1:Matrix (QuditIndex d n) (QuditIndex d n) ℂ)-S)‖ ≤
      2*((n:ℝ)^(r+4))⁻¹*Ks+4*((n:ℝ)^3)⁻¹+
      4*((n:ℝ)^(r+4))⁻¹*|h| *Kb+4*(((n:ℝ)^(r+4))⁻¹)^2*(|nu|+h^2) := by
  let : NeZero d := ⟨by omega⟩
  dsimp only
  intro hZ hB hS
  have hg := quditReadout_good_radius hn r x hx
  have he := cardinalityHaar_second_direction_identity d r lam (complexCoordinate x) hg.1 e₀
  simp only [Fintype.card_fin] at he
  exact full_second_identity_error_of_good_radius _ _ _ _ _ _ _ _ _ _ _ he
    hg.2.1 hg.2.2.1 (by positivity) hg.2.2.2 hZ hB hS

/-- On the actual radial and remainder good events, bounded actual B and S control the full second-moment error. -/
theorem cardinalityPauli_second_error_of_good_radius (n r : ℕ) (hn : 2≤n) (lam : ℕ → ℝ) (Kb Ks : ℝ)
    (x : Fin 2 × QuditIndex 2 n → ℝ)
    (e₀ : Metric.sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1)
    (hx : |gaussianRadius (QuditIndex 2 n) x-1|≤((n:ℝ)^(r+4))⁻¹) :
    let D := (2:ℝ)^n
    let h := cardinalityReadoutTraceScale 2 n r lam
    let nu := cardinalityReadoutTraceScale 2 n r (fun j => (lam j)^2)
    let ψ : QuditIndex 2 n → ℂ := (sphereDirection e₀ (WithLp.toLp 2 (complexCoordinate x)) : EuclideanSpace ℂ (QuditIndex 2 n))
    let B := cardinalityReadoutMean 2 pauliBasisRecords pauliFullRecord r lam D ψ
    let S := cardinalityReadoutAuxiliary 2 pauliBasisRecords pauliFullRecord r lam D ψ
    let M := cardinalityReadoutSecond 2 pauliBasisRecords pauliFullRecord r lam D ψ
    let Z := cardinalityReadoutRemainder 2 pauliBasisRecords pauliFullRecord r lam (complexCoordinate x)
    ‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ) Z‖≤((n:ℝ)^3)⁻¹ →
    ‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ) B‖≤Kb →
    ‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ) S‖≤Ks →
    ‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ) (M-nu • (1:Matrix (QuditIndex 2 n) (QuditIndex 2 n) ℂ)-S)‖ ≤
      2*((n:ℝ)^(r+4))⁻¹*Ks+4*((n:ℝ)^3)⁻¹+
      4*((n:ℝ)^(r+4))⁻¹*|h| *Kb+4*(((n:ℝ)^(r+4))⁻¹)^2*(|nu|+h^2) := by
  dsimp only
  intro hZ hB hS
  have hg := quditReadout_good_radius hn r x hx
  have he := cardinalityPauli_second_direction_identity r lam (complexCoordinate x) hg.1 e₀
  simp only [Fintype.card_fin] at he
  exact full_second_identity_error_of_good_radius _ _ _ _ _ _ _ _ _ _ _ he
    hg.2.1 hg.2.2.1 (by positivity) hg.2.2.2 hZ hB hS

end CertificationGaussian
