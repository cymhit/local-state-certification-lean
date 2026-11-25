import LocalCertification.Extremal.Gamma

set_option autoImplicit false
noncomputable section
namespace LocalCertification.Protocol

/-- The exact affine separation appearing in the achievable-budget proposition. -/
def scoreWindowGap (l u a b : ℝ) : ℝ := l+(1-l)*a-u-(1-u)*b

def scoreWindowThreshold (l u a b : ℝ) : ℝ := (l+(1-l)*a+u+(1-u)*b)/2

/-- Positive separation forces the upper envelope below one and keeps the gap at most the original tolerance width. -/
theorem scoreWindowGap_bounds {l u a b : ℝ} (hl : l≤0) (hu : 0≤u)
    (ha : a≤1) (hb0 : 0≤b) (hb1 : b≤1) (hg : 0<scoreWindowGap l u a b) :
    l<1 ∧ u<1 ∧ scoreWindowGap l u a b≤a-b ∧ scoreWindowGap l u a b≤1 := by
  have hla := mul_nonpos_of_nonpos_of_nonneg hl (sub_nonneg.mpr ha)
  have hub := mul_nonneg hu (sub_nonneg.mpr hb1)
  have hwidth : scoreWindowGap l u a b≤a-b := by unfold scoreWindowGap; nlinarith
  have hu1 : u<1 := by
    by_contra h
    have hnonneg := mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr (le_of_not_gt h))
    unfold scoreWindowGap at hg
    nlinarith
  exact ⟨lt_of_le_of_lt hl zero_lt_one,hu1,hwidth,by linarith⟩

/-- The actual midpoint threshold has margin at least a quarter of the positive gap on both promised classes. -/
theorem scoreWindowThreshold_margins {l u a b ηl ηu F m : ℝ}
    (hl : l≤0) (hu : 0≤u) (ha : a≤1) (hb0 : 0≤b) (hb1 : b≤1)
    (hg : 0<scoreWindowGap l u a b)
    (hηl : ηl≤scoreWindowGap l u a b/4) (hηu : ηu≤scoreWindowGap l u a b/4)
    (hmeanl : l+(1-l)*F-ηl≤m) (hmeanu : m≤u+(1-u)*F+ηu) :
    (a≤F → scoreWindowThreshold l u a b+scoreWindowGap l u a b/4≤m) ∧
    (F≤b → m+scoreWindowGap l u a b/4≤scoreWindowThreshold l u a b) := by
  obtain ⟨hl1,hu1,_,_⟩ := scoreWindowGap_bounds hl hu ha hb0 hb1 hg
  constructor
  · intro hF
    have h := mul_nonneg (sub_nonneg.mpr hl1.le) (sub_nonneg.mpr hF)
    unfold scoreWindowGap at hηl
    unfold scoreWindowThreshold scoreWindowGap
    nlinarith
  · intro hF
    have h := mul_nonneg (sub_nonneg.mpr hu1.le) (sub_nonneg.mpr hF)
    unfold scoreWindowGap at hηu
    unfold scoreWindowThreshold scoreWindowGap
    nlinarith

/-- Exact algebraic identity connecting the original envelope ratio with the achievable mean gap. -/
theorem scoreWindowGap_ratio (l u a b : ℝ) (hb : b≠1) (hl : l≠1) :
    scoreWindowGap l u a b = (1-b)*(1-l)*((a-b)/(1-b)-(u-l)/(1-l)) := by
  have hb' : 1-b≠0 := sub_ne_zero.mpr (Ne.symm hb)
  have hl' : 1-l≠0 := sub_ne_zero.mpr (Ne.symm hl)
  unfold scoreWindowGap
  field_simp
  ring

/-- One actual optimizing polynomial, chosen only from q and r, works simultaneously for all
windows strictly above the original gamma threshold. -/
theorem optimal_polynomial_score_gaps (q : ℝ) (hq : 1<q) (r : ℕ) :
    ∃ p : Polynomial ℝ, LocalCertification.Extremal.admissible r p ∧
      LocalCertification.Extremal.envelopeRatio q p=LocalCertification.Extremal.gamma q r ∧
      LocalCertification.Extremal.lowerEnvelope q p≤0 ∧ 0≤LocalCertification.Extremal.upperEnvelope q p ∧
      ∀ a b : ℝ, b<1 → LocalCertification.Extremal.gamma q r<(a-b)/(1-b) →
        0<scoreWindowGap (LocalCertification.Extremal.lowerEnvelope q p) (LocalCertification.Extremal.upperEnvelope q p) a b := by
  obtain ⟨p,hp,hr⟩ := LocalCertification.Extremal.gamma_attained q hq r
  obtain ⟨hl,hu⟩ := LocalCertification.Extremal.envelope_zero_bounds q hq p
  refine ⟨p,hp,hr,hl,hu,?_⟩
  intro a b hb hg
  have hl1 : LocalCertification.Extremal.lowerEnvelope q p<1 := lt_of_le_of_lt hl zero_lt_one
  rw [scoreWindowGap_ratio _ _ a b (ne_of_lt hb) (ne_of_lt hl1)]
  have hratio : 0<(a-b)/(1-b)-
      (LocalCertification.Extremal.upperEnvelope q p-LocalCertification.Extremal.lowerEnvelope q p)/(1-LocalCertification.Extremal.lowerEnvelope q p) := by
    change 0<(a-b)/(1-b)-LocalCertification.Extremal.envelopeRatio q p
    rw [hr]
    exact sub_pos.mpr hg
  exact mul_pos (mul_pos (sub_pos.mpr hb) (sub_pos.mpr hl1)) hratio

end LocalCertification.Protocol
