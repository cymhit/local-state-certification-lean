import LocalCertification.Protocol.QuantitativeFixedScore
import LocalCertification.Extremal.DegreeZero
import LocalCertification.Extremal.DegreeHierarchy

/-! Actual product-basis protocols on one target event throughout a closed
near-critical window. The protocol and its every-path integer cap are retained. -/
set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory Metric Filter Set CertificationGaussian
  LocalCertification.Quantum LocalCertification.Extremal LocalCertification.Probability
open scoped BigOperators ENNReal Matrix.Norms.L2Operator Topology
noncomputable section
namespace LocalCertification.Protocol
universe u

def NearCriticalBasisUpperConclusion (d j : ℕ) [NeZero d] (b η : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
  ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
    (∀ n, IsCompact (good n)) ∧
    Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n))
      atTop (nhds 1) ∧
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ ψ ∈ good n,
      ∀ ε : ℝ, -η ≤ ε → ε ≤ η → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        ∃ m : ℕ, ∃ Q : CanonicalProtocol d n,
          Valid Q.toRaw (spherePureVector ψ)
            (b + (1 - b) * (gamma ((d : ℝ) + 1) j + ε)) b δ ∧
          Capped Q.toRaw m ∧
          (m : ℝ) ≤ C * ((n : ℝ)^(j + 1) / (1 + (n : ℝ) * (max ε 0)^2)) *
            Real.log (1 / δ)

/-- A single compact target family supports the capped tests on a closed threshold rectangle. -/
def NearCriticalBasisUpperWindow (d j : ℕ) [NeZero d] (blo bhi η : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
  ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
    (∀ n, IsCompact (good n)) ∧
    Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n))
      atTop (nhds 1) ∧
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ ψ ∈ good n,
      ∀ b : ℝ, blo ≤ b → b ≤ bhi → ∀ ε : ℝ, -η ≤ ε → ε ≤ η → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        ∃ m : ℕ, ∃ Q : CanonicalProtocol d n,
          Valid Q.toRaw (spherePureVector ψ)
            (b + (1 - b) * (gamma ((d : ℝ) + 1) j + ε)) b δ ∧
          Capped Q.toRaw m ∧
          (m : ℝ) ≤ C * ((n : ℝ)^(j + 1) / (1 + (n : ℝ) * (max ε 0)^2)) *
            Real.log (1 / δ)

private theorem moving_score_gap (l u b g ε t : ℝ) (hl : l ≤ 0) (hb : b < 1)
    (hr : (u - l) / (1 - l) = t) :
    scoreWindowGap l u (b + (1 - b) * (g + ε)) b =
      (1 - b) * (1 - l) * (g + ε - t) := by
  have he : u - l = t * (1 - l) := (div_eq_iff (by linarith)).mp hr
  unfold scoreWindowGap
  nlinarith [he]

private theorem inverse_square_good_probability (d : ℕ) (hd : 2 ≤ d)
    (good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1))
    (hc : ∀ n, IsCompact (good n))
    (hbad : ∀ᶠ n : ℕ in atTop,
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ ≤
        ENNReal.ofReal (2 * ((n : ℝ)^2)⁻¹)) :
    Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n))
      atTop (nhds 1) := by
  have hi := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).pow 2
  have ht : Tendsto (fun n : ℕ => 2 * ((n : ℝ)^2)⁻¹) atTop (nhds 0) := by
    simpa only [Function.comp_apply, inv_pow, zero_pow (by omega : 2 ≠ 0), mul_zero]
      using tendsto_const_nhds.mul hi
  have hz : Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n))
      (good n)ᶜ) atTop (nhds 0) := by
    have ht' : Tendsto (fun n : ℕ => ENNReal.ofReal (2 * ((n : ℝ)^2)⁻¹)) atTop (nhds 0) := by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht'
      (Filter.Eventually.of_forall (fun _ => bot_le)) hbad
  have h := (ENNReal.continuous_sub_left (show (1 : ℝ≥0∞) ≠ ∞ by simp)).continuousAt.tendsto.comp hz
  have he (n : ℕ) : 1 - canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ =
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n) := by
    let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0, by omega⟩⟩
    simpa only [compl_compl] using
      (prob_compl_eq_one_sub (hc n).isClosed.measurableSet.compl).symm
  simpa only [Function.comp_def, tsub_zero, he] using h

variable {H : Type u} [MeasurableSpace H] [TopologicalSpace H] [BorelSpace H]
  [CompactSpace H] [SecondCountableTopology H] {d n : ℕ} [NeZero d]

omit [CompactSpace H] in
private theorem fixedScore_canonical_cap (hd : 2 ≤ d) (hn : 1 ≤ n)
    (setting : H → LocalUnitary d) (hs : Continuous setting)
    (ν : Measure H) [IsProbabilityMeasure ν] (r : ℕ) (lam : ℕ → ℝ) (h0 : lam 0 = 1)
    (a b δ : ℝ) (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hg : 0 < scoreWindowGap
      (lowerEnvelope ((d : ℝ)+1) (radialPolynomial d r lam))
      (upperEnvelope ((d : ℝ)+1) (radialPolynomial d r lam)) a b)
    (hδ : 0 < δ) (hh : δ ≤ 1/2) (ψ : QIT.PureVector (QuditIndex d n))
    (h : FixedScoreAchievable setting hs ν r lam (radialSecondCoefficientSup d r lam) a b δ ψ) :
    ∃ m : ℕ, ∃ Q : CanonicalProtocol d n, Valid Q.toRaw ψ a b δ ∧ Capped Q.toRaw m ∧
      (m : ℝ) ≤ (1548 * (complementLambdaCoefficient d r (fun k => (lam k)^2) +
        radialSecondCoefficientSup d r lam + 1)) * (n : ℝ)^r /
        (scoreWindowGap (lowerEnvelope ((d : ℝ)+1) (radialPolynomial d r lam))
          (upperEnvelope ((d : ℝ)+1) (radialPolynomial d r lam)) a b)^2 * Real.log (1/δ) := by
  let E := radialSecondCoefficientSup d r lam
  let A := complementLambdaCoefficient d r (fun k => (lam k)^2)
  let V := cardinalityReadoutTraceScale d n r (fun k => (lam k)^2) + E + 1
  let Δ := scoreWindowGap (lowerEnvelope ((d : ℝ)+1) (radialPolynomial d r lam))
    (upperEnvelope ((d : ℝ)+1) (radialPolynomial d r lam)) a b
  have hE : 0 < E := (radialSecondCoefficientSup_bounds d r (by omega) lam h0).1
  have hq : 1 < (d : ℝ)+1 := by exact_mod_cast (show 1 < d+1 by omega)
  have hΔ1 : Δ ≤ 1 := (scoreWindowGap_bounds
    (envelope_zero_bounds _ hq _).1 (envelope_zero_bounds _ hq _).2 ha hb0 hb1 hg).2.2.2
  let m := blockCount δ * blockCopies V Δ
  obtain ⟨Q, hv, hc⟩ := capFeasible_of_raw _ ψ a b δ h.1 m h.2.1
  refine ⟨m, Q, hv, hc, ?_⟩
  have hV : 1 ≤ V := by
    have := squared_traceScale_nonneg d n r (by omega) lam
    dsimp [V]; linarith
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (1 : ℝ) ≤ (n : ℝ)^r := one_le_pow₀ hnR
  have hv : V ≤ (A + E + 1) * (n : ℝ)^r := by
    have := squared_traceScale_le_polynomial d n r (by omega) hn lam
    dsimp [V, A]; nlinarith
  have hlog : 0 ≤ Real.log (1/δ) := Real.log_nonneg ((le_div_iff₀ hδ).mpr (by linarith))
  refine (majorityBornProtocol_budget hV hg hΔ1 hδ hh).trans ?_
  have hmul := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 1548))
      (sq_nonneg Δ)) hlog
  convert hmul using 1; dsimp only [A, E, Δ]; ring

private theorem transition_large (x ε : ℝ) (j : ℕ) (hx : 1 ≤ x)
    (h : 1 ≤ x * (max ε 0)^2) :
    0 < ε ∧ 1 / x ≤ ε ∧
      x^j / ε^2 ≤ 2 * (x^(j+1) / (1 + x * (max ε 0)^2)) := by
  have he : 0 < ε := by
    by_contra hn
    rw [max_eq_right (le_of_not_gt hn)] at h
    norm_num at h
  rw [max_eq_left he.le] at h ⊢
  have hx0 : 0 < x := by linarith
  have hxe : 1 ≤ x * ε := by
    by_contra hn
    have hxe : x * ε < 1 := lt_of_not_ge hn
    have he1 : ε < 1 := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg hx0.le he.le) (sub_nonneg.mpr he1.le)]
  refine ⟨he, (div_le_iff₀ hx0).mpr (by nlinarith), ?_⟩
  have hden : 0 < 1 + x * ε^2 := by positivity
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (sq_pos_of_pos he) hden).mpr
  have hm := mul_le_mul_of_nonneg_left (show 1 + x * ε^2 ≤ 2 * x * ε^2 by nlinarith)
    (pow_nonneg hx0.le j)
  convert hm using 1; ring

private theorem transition_small (x ε : ℝ) (j : ℕ) (hx : 1 ≤ x)
    (h : x * (max ε 0)^2 ≤ 1) :
    x^(j+1) ≤ 2 * (x^(j+1) / (1 + x * (max ε 0)^2)) := by
  have hden : 0 < 1 + x * (max ε 0)^2 := by positivity
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hden).mpr
  have hm := mul_le_mul_of_nonneg_left (show 1 + x * (max ε 0)^2 ≤ 2 by linarith)
    (pow_nonneg (by linarith : 0 ≤ x) (j+1))
  nlinarith

set_option maxHeartbeats 1000000 in
omit [CompactSpace H] in
private theorem nearCritical_upper_from_scores (hd : 2 ≤ d)
    (setting : H → LocalUnitary d) (hs : Continuous setting)
    (ν : Measure H) [IsProbabilityMeasure ν]
    (hScores : ∀ (r : ℕ) (lam : ℕ → ℝ), lam 0 = 1 → ∀ K : ℝ, 0 < K →
      UniformScoreGapConclusion setting hs ν r lam K)
    (j : ℕ) (blo bhi η : ℝ) (hlo : 0 < blo) (hhi : bhi < 1)
    (hηup : gamma ((d : ℝ)+1) j + η ≤ 1)
    (hηgap : η < gamma ((d : ℝ)+1) j - gamma ((d : ℝ)+1) (j+1)) :
    NearCriticalBasisUpperWindow d j blo bhi η := by
  obtain ⟨p, lam, _hp, hpoly, h0, hr, hl, _hu, _hc, _hg⟩ := optimal_radial_parameters d j hd
  obtain ⟨p', lam', _hp', hpoly', h0', hr', hl', _hu', _hc', _hg'⟩ :=
    optimal_radial_parameters d (j+1) hd
  let A := (1-bhi) * (1-lowerEnvelope ((d : ℝ)+1) p)
  let B := (1-bhi) * (1-lowerEnvelope ((d : ℝ)+1) p') *
    (gamma ((d : ℝ)+1) j - gamma ((d : ℝ)+1) (j+1) - η)
  have hA : 0 < A := mul_pos (by linarith) (by linarith)
  have hB : 0 < B := mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  let D := 1548 * (complementLambdaCoefficient d j (fun k => (lam k)^2) +
    radialSecondCoefficientSup d j lam + 1)
  let D' := 1548 * (complementLambdaCoefficient d (j+1) (fun k => (lam' k)^2) +
    radialSecondCoefficientSup d (j+1) lam' + 1)
  have hD : 0 < D := by
    have := complementLambdaCoefficient_nonneg d j (by omega) (fun k => (lam k)^2)
    have := (radialSecondCoefficientSup_bounds d j (by omega) lam h0).1
    dsimp [D]; positivity
  have hD' : 0 < D' := by
    have := complementLambdaCoefficient_nonneg d (j+1) (by omega) (fun k => (lam' k)^2)
    have := (radialSecondCoefficientSup_bounds d (j+1) (by omega) lam' h0').1
    dsimp [D']; positivity
  let C := 2 * (D / A^2 + D' / B^2)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨good₀, hc₀, N₀, hN₀, he₀⟩ := hScores j lam h0 A hA
  obtain ⟨good₁, hc₁, N₁, hN₁, he₁⟩ := hScores (j+1) lam' h0' B hB
  let good := fun n => good₀ n ∩ good₁ n
  let N := max N₀ N₁
  have hcgood : ∀ n, IsCompact (good n) := fun n => (hc₀ n).inter (hc₁ n)
  have hbad : ∀ n, N ≤ n →
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ ≤
        ENNReal.ofReal (2 * ((n : ℝ)^2)⁻¹) := by
    intro n hn
    dsimp only [good]
    rw [compl_inter]
    calc
      _ ≤ canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good₀ n)ᶜ +
          canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good₁ n)ᶜ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (((n : ℝ)^2)⁻¹) + ENNReal.ofReal (((n : ℝ)^2)⁻¹) :=
        add_le_add (he₀ n ((le_max_left _ _).trans hn)).1 (he₁ n ((le_max_right _ _).trans hn)).1
      _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  refine ⟨C, hC, good, hcgood,
    inverse_square_good_probability d hd good hcgood (eventually_atTop.mpr ⟨N, hbad⟩),
    N, hN₀.trans (le_max_left _ _), ?_⟩
  intro n hn ψ hψ b hblo hbhi ε helo hehi δ hδ hhalf
  have hb0 := hlo.trans_le hblo
  have hb1 := hbhi.trans_lt hhi
  have hn1 : 1 ≤ n := hN₀.trans ((le_max_left _ _).trans hn)
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hx0 : 0 < (n : ℝ) := by linarith
  let a := b + (1-b) * (gamma ((d : ℝ)+1) j + ε)
  have ha : a ≤ 1 := by dsimp [a]; nlinarith
  have hlog : 0 ≤ Real.log (1/δ) := Real.log_nonneg ((le_div_iff₀ hδ).mpr (by linarith))
  have hscale : 0 ≤ (n : ℝ)^(j+1) / (1 + (n : ℝ)*(max ε 0)^2) := by positivity
  by_cases hlarge : 1 ≤ (n : ℝ)*(max ε 0)^2
  · obtain ⟨hepos, heinv, hscalej⟩ := transition_large (n : ℝ) ε j hx hlarge
    have hgap : A * ε ≤ scoreWindowGap
        (lowerEnvelope ((d : ℝ)+1) (radialPolynomial d j lam))
        (upperEnvelope ((d : ℝ)+1) (radialPolynomial d j lam)) a b := by
      rw [hpoly, moving_score_gap _ _ b (gamma ((d : ℝ)+1) j) ε _ hl hb1 hr,
        add_sub_cancel_left]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (sub_le_sub_left hbhi 1) (by linarith)) hepos.le
    have hmin : 0 < A * ε := mul_pos hA hepos
    have hg := hmin.trans_le hgap
    have hk : A / (n : ℝ) ≤ scoreWindowGap
        (lowerEnvelope ((d : ℝ)+1) (radialPolynomial d j lam))
        (upperEnvelope ((d : ℝ)+1) (radialPolynomial d j lam)) a b := by
      rw [div_eq_mul_one_div]
      exact (mul_le_mul_of_nonneg_left heinv hA.le).trans hgap
    have hscore := (he₀ n ((le_max_left _ _).trans hn)).2 ψ hψ.1 a b ha hb0.le hb1.le hk δ hδ hhalf.le
    obtain ⟨m, Q, hv, hc, hm⟩ := fixedScore_canonical_cap hd hn1 setting hs ν j lam h0
      a b δ ha hb0.le hb1.le hg hδ hhalf.le (spherePureVector ψ) hscore
    refine ⟨m, Q, hv, hc, hm.trans ?_⟩
    change D * (n : ℝ)^j / _ * _ ≤ _
    calc
      _ ≤ D * (n : ℝ)^j / (A*ε)^2 * Real.log (1/δ) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity)
          (sq_pos_of_pos hmin) (pow_le_pow_left₀ hmin.le hgap 2)) hlog
      _ =
          (D/A^2) * ((n : ℝ)^j/ε^2) * Real.log (1/δ) := by field_simp
      _ ≤ (D/A^2) * (2*((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2))) * Real.log (1/δ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscalej (by positivity)) hlog
      _ ≤ C * ((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2)) * Real.log (1/δ) := by
        apply mul_le_mul_of_nonneg_right _ hlog
        have hpos : 0 ≤ D'/B^2 := by positivity
        dsimp only [C]
        nlinarith [mul_nonneg hpos hscale]
  · have hgap : B ≤ scoreWindowGap
        (lowerEnvelope ((d : ℝ)+1) (radialPolynomial d (j+1) lam'))
        (upperEnvelope ((d : ℝ)+1) (radialPolynomial d (j+1) lam')) a b := by
      rw [hpoly', moving_score_gap _ _ b (gamma ((d : ℝ)+1) j) ε _ hl' hb1 hr']
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (sub_le_sub_left hbhi 1) (by linarith)
      · linarith
      · linarith
      · exact mul_nonneg (by linarith) (by linarith)
    have hg := hB.trans_le hgap
    have hk : B / (n : ℝ) ≤ scoreWindowGap
        (lowerEnvelope ((d : ℝ)+1) (radialPolynomial d (j+1) lam'))
        (upperEnvelope ((d : ℝ)+1) (radialPolynomial d (j+1) lam')) a b :=
      (div_le_self hB.le hx).trans hgap
    have hscore := (he₁ n ((le_max_right _ _).trans hn)).2 ψ hψ.2 a b ha hb0.le hb1.le hk δ hδ hhalf.le
    obtain ⟨m, Q, hv, hc, hm⟩ := fixedScore_canonical_cap hd hn1 setting hs ν (j+1) lam' h0'
      a b δ ha hb0.le hb1.le hg hδ hhalf.le (spherePureVector ψ) hscore
    refine ⟨m, Q, hv, hc, hm.trans ?_⟩
    change D' * (n : ℝ)^(j+1) / _ * _ ≤ _
    have hsquare : B^2 ≤ (scoreWindowGap
        (lowerEnvelope ((d : ℝ)+1) (radialPolynomial d (j+1) lam'))
        (upperEnvelope ((d : ℝ)+1) (radialPolynomial d (j+1) lam')) a b)^2 :=
      pow_le_pow_left₀ hB.le hgap 2
    calc
      _ ≤ D' * (n : ℝ)^(j+1)/B^2 * Real.log (1/δ) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hB) hsquare) hlog
      _ = (D'/B^2)*(n : ℝ)^(j+1)*Real.log (1/δ) := by ring
      _ ≤ (D'/B^2)*(2*((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2)))*Real.log (1/δ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (transition_small (n : ℝ) ε j hx (le_of_not_ge hlarge)) (by positivity)) hlog
      _ ≤ C*((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2))*Real.log (1/δ) := by
        apply mul_le_mul_of_nonneg_right _ hlog
        have hpos : 0 ≤ D/A^2 := by positivity
        dsimp only [C]
        nlinarith [mul_nonneg hpos hscale]

/-- Uniform capped basis tests for all lower thresholds in a compact subinterval of (0,1). -/
theorem qudit_nearCritical_basis_upper_uniform (d j : ℕ) [NeZero d] (hd : 2 ≤ d) (blo bhi η : ℝ)
    (hlo : 0 < blo) (_hbounds : blo ≤ bhi) (hhi : bhi < 1) (hη : 0 < η)
    (hwindow : η < (1/2 : ℝ) * min
      ((if j = 0 then 1 else gamma ((d : ℝ)+1) (j-1)) - gamma ((d : ℝ)+1) j)
      (gamma ((d : ℝ)+1) j - gamma ((d : ℝ)+1) (j+1))) :
    NearCriticalBasisUpperWindow d j blo bhi η := by
  have hq : 1 < (d : ℝ)+1 := by exact_mod_cast (show 1 < d+1 by omega)
  have hprev : (if j = 0 then 1 else gamma ((d : ℝ)+1) (j-1)) ≤ (1 : ℝ) := by
    split_ifs
    · rfl
    · exact (gamma_le_inverse _ hq _).trans (inv_le_one_of_one_le₀ hq.le)
  have hleft := min_le_left
    ((if j = 0 then 1 else gamma ((d : ℝ)+1) (j-1)) - gamma ((d : ℝ)+1) j)
    (gamma ((d : ℝ)+1) j - gamma ((d : ℝ)+1) (j+1))
  have hright := min_le_right
    ((if j = 0 then 1 else gamma ((d : ℝ)+1) (j-1)) - gamma ((d : ℝ)+1) j)
    (gamma ((d : ℝ)+1) j - gamma ((d : ℝ)+1) (j+1))
  have hup : gamma ((d : ℝ)+1) j + η ≤ 1 := by linarith
  have hgap : η < gamma ((d : ℝ)+1) j - gamma ((d : ℝ)+1) (j+1) := by linarith
  by_cases hd2 : d = 2
  · subst d
    exact nearCritical_upper_from_scores hd pauliBasisUnitary continuous_of_discreteTopology
      (uniformFiniteOutcome 3) fixedScore_pauli_uniform_gap j blo bhi η hlo hhi hup hgap
  · exact nearCritical_upper_from_scores hd id continuous_id (complexUnitaryHaar (Fin d))
      (fun r lam h0 K hK => fixedScore_haar_uniform_gap d r (by omega) lam h0 K hK)
      j blo bhi η hlo hhi hup hgap

/-- The closed near-critical window admits one compact high-probability target family and
one cutoff before epsilon and confidence. This is an actual basis protocol cap. -/
theorem qudit_nearCritical_basis_upper (d j : ℕ) [NeZero d] (hd : 2 ≤ d) (b η : ℝ)
    (hb0 : 0 < b) (hb1 : b < 1) (hη : 0 < η)
    (hwindow : η < (1/2 : ℝ) * min
      ((if j = 0 then 1 else gamma ((d : ℝ)+1) (j-1)) - gamma ((d : ℝ)+1) j)
      (gamma ((d : ℝ)+1) j - gamma ((d : ℝ)+1) (j+1))) :
    NearCriticalBasisUpperConclusion d j b η := by
  obtain ⟨C, hC, good, hc, hp, N, hN, h⟩ :=
    qudit_nearCritical_basis_upper_uniform d j hd b b η hb0 le_rfl hb1 hη hwindow
  exact ⟨C, hC, good, hc, hp, N, hN, fun n hn ψ hψ => h n hn ψ hψ b le_rfl le_rfl⟩

end LocalCertification.Protocol
