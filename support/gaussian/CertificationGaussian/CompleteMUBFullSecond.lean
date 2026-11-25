import CertificationGaussian.CompleteMUBSpectrum

noncomputable section
open Matrix MeasureTheory Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

theorem cardinalityMUB_second_error_of_good_radius (d n r : ℕ) (hd : 2≤d) (hn : 2≤n) (MUB : CompleteMUB d) (lam : ℕ → ℝ) (Kb Ks : ℝ)
    (x : Fin 2 × QuditIndex d n → ℝ)
    (e₀ : Metric.sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)
    (hx : |gaussianRadius (QuditIndex d n) x-1|≤((n:ℝ)^(r+4))⁻¹) :
    let D := (d:ℝ)^n
    let h := cardinalityReadoutTraceScale d n r lam
    let nu := cardinalityReadoutTraceScale d n r (fun j => (lam j)^2)
    let ψ : QuditIndex d n → ℂ := (sphereDirection e₀ (WithLp.toLp 2 (complexCoordinate x)) : EuclideanSpace ℂ (QuditIndex d n))
    let B := cardinalityReadoutMean d (completeMUBRecords d) (completeMUBFullRecord MUB) r lam D ψ
    let S := cardinalityReadoutAuxiliary d (completeMUBRecords d) (completeMUBFullRecord MUB) r lam D ψ
    let M := cardinalityReadoutSecond d (completeMUBRecords d) (completeMUBFullRecord MUB) r lam D ψ
    let Z := cardinalityReadoutRemainder d (completeMUBRecords d) (completeMUBFullRecord MUB) r lam (complexCoordinate x)
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
  have he := cardinalityReadoutSecond_direction_identity d (completeMUBRecords d)
    (completeMUBFullRecord MUB) continuous_of_discreteTopology
    (completeMUBRecords_projector_mean MUB) r lam (complexCoordinate x) hg.1 e₀
  simp only [Fintype.card_fin] at he
  exact full_second_identity_error_of_good_radius _ _ _ _ _ _ _ _ _ _ _ he
    hg.2.1 hg.2.2.1 (by positivity) hg.2.2.2 hZ hB hS

theorem radialMUB_full_second_control_eventually (d r : ℕ) (hd : 2≤d) [NeZero d] (B : CompleteMUB d)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin d) (Fin d) ℂ,W k0=1 →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      ∀ e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ∀ x : Fin 2 × QuditIndex d n → ℝ,
      sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)∉
        radialHighSphereBad d n r lam W k0 ∪ radialLowSphereBad d n r W k0 →
      |gaussianRadius (QuditIndex d n) x-1|≤((n:ℝ)^(r+4))⁻¹ →
      ‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
        (cardinalityReadoutRemainder (S:=Fin n) d (completeMUBRecords d) (completeMUBFullRecord B) r lam (complexCoordinate x))‖≤((n:ℝ)^3)⁻¹ →
      cardinalityReadoutSecondError d n r (completeMUBRecords d) (completeMUBFullRecord B) lam
        (sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x))≤C*((n:ℝ)^3)⁻¹ := by
  obtain ⟨Kb,Ks,hKb,hKs,hE⟩ := radialMUBReadout_norm_eventually d r hd B lam k0 hcard
  let A := complementLambdaCoefficient d r lam
  let An := complementLambdaCoefficient d r (fun j => (lam j)^2)
  have hA : 0≤A := complementLambdaCoefficient_nonneg d r (by omega) lam
  have hAn : 0≤An := complementLambdaCoefficient_nonneg d r (by omega) _
  refine ⟨2*Ks+4+4*A*Kb+4*(An+A^2),by positivity,?_⟩
  filter_upwards [hE,eventually_ge_atTop 2] with n he hn
  intro W h0 hHS e₀ x hgood hr hZ
  have hnorm := he W h0 hHS (sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)) hgood
  have h := cardinalityMUB_second_error_of_good_radius d n r hd hn B lam Kb Ks x e₀ hr hZ hnorm.1 hnorm.2
  exact h.trans (readout_full_error_scalar_le n r (by omega) A An Kb Ks _ _ hA hAn hKb.le hKs.le
    (cardinalityReadoutTraceScale_abs_le d n r (by omega) (by omega) lam)
    (cardinalityReadoutTraceScale_abs_le d n r (by omega) (by omega) _))

theorem cardinalityMUB_remainder_radius_eventually_bound (d r : ℕ) [NeZero d] (B : CompleteMUB d)
    (hd : 2≤d) (lam : ℕ → ℝ) :
    ∀ᶠ n : ℕ in atTop,
      pairedGaussian (QuditIndex d n) {x |
        ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
          (cardinalityReadoutRemainder (S:=Fin n) d (completeMUBRecords d) (completeMUBFullRecord B) r lam (complexCoordinate x))‖ ∨
        ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex d n) x-1|} ≤
      ENNReal.ofReal (Real.exp ((Real.log (completeMUBLocalKappa d)/2)*n)+
        Real.exp (-(Real.log d/4)*(n:ℝ)^3)) := by
  filter_upwards [cardinalityMUB_remainder_eventually_exponential B hd r lam,
    quditRadius_power_eventually_cubic (by omega : 2≤d) (r+4)] with n hZ ht
  calc
    _ ≤ pairedGaussian (QuditIndex d n) {x |
        ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
          (cardinalityReadoutRemainder (S:=Fin n) d (completeMUBRecords d) (completeMUBFullRecord B) r lam (complexCoordinate x))‖}+
        pairedGaussian (QuditIndex d n) {x | ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex d n) x-1|} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp ((Real.log (completeMUBLocalKappa d)/2)*n))+
        ENNReal.ofReal (Real.exp (-(Real.log d/4)*(n:ℝ)^3)) :=
      add_le_add hZ ((measure_mono (show {x | ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex d n) x-1|} ⊆
        {x | ((n:ℝ)^(r+4))⁻¹≤|gaussianRadius (QuditIndex d n) x-1|} from by
        intro x hx
        change ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex d n) x-1| at hx
        change ((n:ℝ)^(r+4))⁻¹≤|gaussianRadius (QuditIndex d n) x-1|
        exact hx.le)).trans ht)
    _ = _ := (ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)).symm

theorem cardinalityMUB_remainder_radius_inverse_power (d r k : ℕ) [NeZero d] (B : CompleteMUB d)
    (hd : 2≤d) (lam : ℕ → ℝ) :
    ∀ᶠ n : ℕ in atTop,
      pairedGaussian (QuditIndex d n) {x |
        ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
          (cardinalityReadoutRemainder (S:=Fin n) d (completeMUBRecords d) (completeMUBFullRecord B) r lam (complexCoordinate x))‖ ∨
        ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex d n) x-1|} ≤
      ENNReal.ofReal (((n:ℝ)^k)⁻¹) := by
  have ha : 0< -(Real.log (completeMUBLocalKappa d)/2) := by
    have h := Real.log_neg (completeMUBLocalKappa_pos (d:=d)) (completeMUBLocalKappa_lt_one hd)
    linarith
  have hb : 0<Real.log d/4 := div_pos (Real.log_pos (by exact_mod_cast (show 1<d by omega))) (by norm_num)
  filter_upwards [cardinalityMUB_remainder_radius_eventually_bound d r B hd lam,
    eventually_exp_pair_le_inverse_power ha hb k] with n hn hp
  exact hn.trans (ENNReal.ofReal_le_ofReal (by simpa only [neg_neg] using hp))

end CertificationGaussian
