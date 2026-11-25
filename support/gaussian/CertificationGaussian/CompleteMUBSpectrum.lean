import CertificationGaussian.CompleteMUBRemainder
import CertificationGaussian.ReadoutFullControl

noncomputable section
open Matrix MeasureTheory Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian

theorem cardinalityMUB_mean_spectrum {S K : Type*} [Fintype S] [DecidableEq S]
    [Fintype K] [DecidableEq K] (d : ℕ) [NeZero d] (B : CompleteMUB d)
    (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) (h0 : W k0=1)
    (hHS : ∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0)
    (hcard : Fintype.card K=d^2) (r : ℕ) (lam : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (S → Fin d)) :
    rectangularEuclideanCLM (cardinalityReadoutMean d (completeMUBRecords d) (completeMUBFullRecord B) r lam
      ((d:ℝ)^(Fintype.card S)) ψ.ofLp)=
      unitarySphereCentered (fun w : S → K => wickTensorMatrix (fun s => W (w s)))
        (fun w => radialFirstCoefficient d r lam (radialBellSupport k0 w).card) ψ :=
  cardinalityReadoutMean_spectrum d (Nat.pos_of_ne_zero (NeZero.ne d)) (completeMUBRecords d) (completeMUBFullRecord B) continuous_of_discreteTopology
    (completeMUBRecords_projector_mean B) (completeMUBRecords_choi_entries B) W k0 h0 hHS hcard r lam ψ

theorem cardinalityMUB_auxiliary_spectrum {S K : Type*} [Fintype S] [DecidableEq S]
    [Fintype K] [DecidableEq K] (d : ℕ) [NeZero d] (B : CompleteMUB d)
    (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) (h0 : W k0=1)
    (hHS : ∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0)
    (hcard : Fintype.card K=d^2) (r : ℕ) (lam : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (S → Fin d)) :
    rectangularEuclideanCLM (cardinalityReadoutAuxiliary d (completeMUBRecords d) (completeMUBFullRecord B) r lam
      ((d:ℝ)^(Fintype.card S)) ψ.ofLp)=
      unitarySphereCentered (fun w : S → K => wickTensorMatrix (fun s => W (w s)))
        (fun w => radialSecondCoefficient d r lam (radialBellSupport k0 w).card) ψ := by
  rw [cardinalityReadoutAuxiliary_eq_two_mean]
  have hs (M : Matrix (S → Fin d) (S → Fin d) ℂ) :
      rectangularEuclideanCLM ((2:ℂ) • M)=(2:ℂ) • rectangularEuclideanCLM M := by
    simp only [rectangularEuclideanCLM,map_smul]
  rw [hs,cardinalityMUB_mean_spectrum d B W k0 h0 hHS hcard r (fun j => (lam j)^2) ψ]
  exact (unitarySphereCentered_weight_smul _ _ 2 ψ).symm


/-- Identical actual B/S operators transport the existing high/low control to the finite MUB law. -/
theorem radialMUBReadoutPolar_control_eventually {K : Type*} [Fintype K] [DecidableEq K]
    (d r : ℕ) (hd : 2≤d) [NeZero d] (B : CompleteMUB d)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∃ C₁ C₂ : ℝ,0<C₁ ∧ 0<C₂ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin d) (Fin d) ℂ,W k0=1 →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ψ∉radialHighSphereBad d n r lam W k0 ∪ radialLowSphereBad d n r W k0 →
      radialReadoutPolarControl d n r (completeMUBRecords d) (completeMUBFullRecord B) lam W k0 C₁ C₂ ψ := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hE⟩ := radialHaarReadoutPolar_control_eventually d r hd lam k0 hcard
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  filter_upwards [hE] with n hn
  intro W h0 hHS ψ hgood
  have h := hn W h0 hHS ψ hgood
  have hb := (cardinalityHaar_mean_spectrum d W k0 h0 hHS hcard r lam ψ.val).trans
    (cardinalityMUB_mean_spectrum d B W k0 h0 hHS hcard r lam ψ.val).symm
  have hs := (cardinalityHaar_auxiliary_spectrum d W k0 h0 hHS hcard r lam ψ.val).trans
    (cardinalityMUB_auxiliary_spectrum d B W k0 h0 hHS hcard r lam ψ.val).symm
  simp only [Fintype.card_fin] at hb hs
  dsimp only [radialReadoutPolarControl] at h ⊢
  rw [hb,hs] at h
  exact h

theorem radialMUBReadout_norm_eventually {K : Type*} [Fintype K] [DecidableEq K]
    (d r : ℕ) (hd : 2≤d) [NeZero d] (B : CompleteMUB d)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∃ Kb Ks : ℝ,0<Kb ∧ 0<Ks ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin d) (Fin d) ℂ,W k0=1 →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ψ∉radialHighSphereBad d n r lam W k0 ∪ radialLowSphereBad d n r W k0 →
      ‖rectangularEuclideanCLM (cardinalityReadoutMean d (completeMUBRecords d) (completeMUBFullRecord B)
        r lam ((d:ℝ)^n) ψ.val.ofLp)‖≤Kb ∧
      ‖rectangularEuclideanCLM (cardinalityReadoutAuxiliary d (completeMUBRecords d) (completeMUBFullRecord B)
        r lam ((d:ℝ)^n) ψ.val.ofLp)‖≤Ks := by
  obtain ⟨Kb,Ks,hKb,hKs,hE⟩ := radialHaarReadout_norm_eventually d r hd lam k0 hcard
  refine ⟨Kb,Ks,hKb,hKs,?_⟩
  filter_upwards [hE] with n hn
  intro W h0 hHS ψ hg
  have h := hn W h0 hHS ψ hg
  have hb := (cardinalityHaar_mean_spectrum d W k0 h0 hHS hcard r lam ψ.val).trans
    (cardinalityMUB_mean_spectrum d B W k0 h0 hHS hcard r lam ψ.val).symm
  have hs := (cardinalityHaar_auxiliary_spectrum d W k0 h0 hHS hcard r lam ψ.val).trans
    (cardinalityMUB_auxiliary_spectrum d B W k0 h0 hHS hcard r lam ψ.val).symm
  simp only [Fintype.card_fin] at hb hs
  rw [hb,hs] at h
  exact h

end CertificationGaussian
