import LocalCertification.Protocol.ExponentialHierarchy
import LocalCertification.Certificates.TableValues

set_option autoImplicit false
open LocalCertification.Asymptotic LocalCertification.Extremal LocalCertification.Quantum CertificationGaussian MeasureTheory Metric Filter
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol

/-- The exact quartic window, with the upper endpoint included and the lower endpoint excluded. -/
theorem qubit_quartic_window (g : ℝ) (hg : 0<g) :
    criticalDegree 3 g=4 ↔ 5/1744<g ∧ g≤4/427 := by
  have h4 := criticalDegree_le_iff 3 (by norm_num) g hg 4
  have h3 := lt_criticalDegree_iff 3 (by norm_num) g hg 3
  rw [LocalCertification.Certificates.Examples.Degree4.exact_value] at h4
  rw [LocalCertification.Certificates.Examples.Degree3.exact_value] at h3
  constructor
  · intro h
    exact ⟨h4.mp (by omega),h3.mp (by omega)⟩
  · rintro ⟨hl,hu⟩
    have := h4.mpr hl
    have := h3.mpr hu
    omega

/-- Equality at the quartic critical value belongs to degree five, not four. -/
theorem qubit_quartic_lower_endpoint : criticalDegree 3 (5/1744)=5 := by
  rw [← LocalCertification.Certificates.Examples.Degree4.exact_value]
  exact criticalDegree_at_critical_value 3 (by norm_num) 4

/-- The original qubit quartic copy-complexity window, on one compact target event independent
of delta. This uses both original protocol budgets and the genuine canonical sphere law. -/
theorem qubit_quartic_copy_complexity (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1)
    (hl : 5/1744<(a-b)/(1-b)) (hu : (a-b)/(1-b)≤4/427) :
    ∃ c C cprob : ℝ,0<c ∧ 0<C ∧ 0<cprob ∧
    ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1),
      (∀ n,IsCompact (good n)) ∧
      ∀ᶠ n : ℕ in atTop,
        canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 n)) (good n)ᶜ≤
          ENNReal.ofReal (Real.exp (-cprob*n)) ∧
        ∀ ψ∈good n,∀ δ : ℝ,0<δ → δ≤1/3 →
          ENNReal.ofReal (c*(n:ℝ)^4*Real.log (1/δ))≤expectedBudget (spherePureVector ψ) a b δ ∧
          expectedBudget (spherePureVector ψ) a b δ≤ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ) ∧
          ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ)≤
            ENNReal.ofReal (C*(n:ℝ)^4*Real.log (1/δ)) := by
  have hg : 0<(a-b)/(1-b) := lt_trans (by norm_num) hl
  have hr := (qubit_quartic_window _ hg).mpr ⟨hl,hu⟩
  simpa only [Nat.cast_ofNat,show (2:ℝ)+1=3 by norm_num,hr] using
    qudit_proposition_six_one 2 (by norm_num) a b hb hab ha

end LocalCertification.Protocol
