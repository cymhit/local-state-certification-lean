import LocalCertification.Paper

/-! Dimension conventions for the analytic bounds, rational certificates and low-degree values. -/

set_option autoImplicit false
open Polynomial LocalCertification LocalCertification.Certificates

section
variable (d : ℝ) (hd : 0 < d) (j : ℕ)

example :
    let α := 1 / (d + 1)
    2 * α ^ (j + 1) /
      (1 + Asymptotic.blaschkeCoefficientConstant (d + 1) * Real.sqrt (j + 1)) ≤
        Manuscript.gamma d j := by
  simpa only [one_div] using Paper.S25 d hd j

example :
    let α := 1 / (d + 1)
    2 * α ^ (j + 1) / (1 + ∑' n, |Asymptotic.blaschkeCoeff α (j + 1) n|) ≤
      Manuscript.gamma d j := by
  simpa only [one_div] using Paper.S25_coefficient d hd j
end

section
variable (d : ℚ) (hd : 0 < d) (j : ℕ)

example (c : CanonicalCandidate (d + 1) j) (M : ℕ) (hc : c.canonicalCheck M) :
    let p := c.p.map (Rat.castHom ℝ)
    Extremal.extremalValue ((d : ℝ) + 1) j = (c.beta : ℝ) ∧
    Manuscript.gamma d j = 2 / (1 + (c.beta : ℝ)) ∧
    Extremal.admissible j p ∧ Extremal.envelopeRatio ((d : ℝ) + 1) p = Manuscript.gamma d j ∧
    ∀ f : ℝ[X], Extremal.admissible j f →
      Extremal.envelopeRatio ((d : ℝ) + 1) f = Manuscript.gamma d j → f = p := by
  obtain ⟨hB, hγ, hp⟩ := Paper.S30 d hd j c M hc
  exact ⟨hB.symm, by simpa using hγ, hp⟩

example : ∃ (c : CanonicalCandidate (d + 1) j) (M : ℕ),
    c.canonicalCheck M ∧ Extremal.admissible j (c.p.map (Rat.castHom ℝ)) ∧
      Extremal.envelopeRatio ((d : ℝ) + 1) (c.p.map (Rat.castHom ℝ)) = Manuscript.gamma d j :=
  Paper.S31 d hd j

example :
    let h := Manuscript.certificate_base_gt_one hd
    ∃ N, stagedFind (d + 1) j N = some (stagedSearch (d + 1) h j) ∧
      canonicalRawCheck (d + 1) j (stagedSearch (d + 1) h j) = true :=
  ⟨_, Paper.S32_termination d hd j, (Paper.S32_correct d hd j).1⟩

example :
    let h := Manuscript.certificate_base_gt_one hd
    let p := (Polynomial.ofFn (j + 1) (stagedPolynomial (d + 1) h j)).map (Rat.castHom ℝ)
    (stagedGamma (d + 1) h j : ℝ) = Manuscript.gamma d j ∧
    Extremal.admissible j p ∧ Extremal.envelopeRatio ((d : ℝ) + 1) p = Manuscript.gamma d j ∧
    ∀ f : ℝ[X], Extremal.admissible j f →
      Extremal.envelopeRatio ((d : ℝ) + 1) f = Manuscript.gamma d j → f = p :=
  (Paper.S32_correct d hd j).2
end

example :
    (∀ d : ℝ, 0 < d → Manuscript.gamma d 0 = 1 / (d + 1)) ∧
    (∀ d : ℝ, 1 ≤ d → Manuscript.gamma d 1 = 1 / ((d + 1)^2 + 1)) ∧
    (∀ d : ℝ, 3 ≤ d → Manuscript.gamma d 2 = 1 / ((d + 1)*((d + 1)^2 + 3))) ∧
    Manuscript.gamma 2 2 = 1 / 35 := Paper.S33

example : Manuscript.gamma (1 / 2) 0 = 2 / 3 ∧ Manuscript.gamma 2 2 = 1 / 35 := by
  exact ⟨by norm_num [(Paper.low_degree_values.1 _ (by norm_num) :
      Manuscript.gamma (1 / 2) 0 = _)], Paper.low_degree_values.2.2.2⟩

#eval IO.println "REGRESSION_CHECK\tPaperNotation\tPASS"
