import LocalCertification.Extremal.FiniteDual
set_option autoImplicit false
open scoped BigOperators Topology OnePoint
open Set Filter Polynomial
noncomputable section
namespace LocalCertification.Extremal

/-- Positive-integer sample: k represents w=k+1. -/
def weightedValue (q : ℝ) (p : ℝ[X]) (k : ℕ) : ℝ :=
  (q⁻¹) ^ (k+1) * p.eval ((k+1 : ℕ) : ℝ)
def lowerEnvelope (q : ℝ) (p : ℝ[X]) : ℝ := sInf (Set.range (weightedValue q p))
def upperEnvelope (q : ℝ) (p : ℝ[X]) : ℝ := sSup (Set.range (weightedValue q p))
def admissible (r : ℕ) (p : ℝ[X]) : Prop := p.natDegree ≤ r ∧ p.eval 0 = 1
def envelopeRatio (q : ℝ) (p : ℝ[X]) : ℝ :=
  (upperEnvelope q p - lowerEnvelope q p) / (1 - lowerEnvelope q p)
/-- Canonical gamma: the original envelope-fraction infimum, not a definition through B. -/
def gamma (q : ℝ) (r : ℕ) : ℝ :=
  sInf (envelopeRatio q '' {p : ℝ[X] | admissible r p})

theorem weightedValue_eq_node (q : ℝ) (p : ℝ[X]) (k : ℕ) :
    weightedValue q p k = polynomialNode q 0 p (k : OnePoint ℕ) := by simp [weightedValue]
theorem weightedValue_tendsto (q : ℝ) (hq : 1 < q) (p : ℝ[X]) :
    Tendsto (weightedValue q p) atTop (𝓝 0) :=
  (polynomial_decay_tendsto q hq p).comp (tendsto_add_atTop_nat 1)
theorem envelope_bounded (q : ℝ) (hq : 1 < q) (p : ℝ[X]) :
    BddBelow (Set.range (weightedValue q p)) ∧ BddAbove (Set.range (weightedValue q p)) := by
  have hc := isCompact_range (polynomialNode_continuous q hq 0 p)
  have hs : Set.range (weightedValue q p) ⊆ Set.range (polynomialNode q 0 p) := by
    rintro t ⟨k, rfl⟩
    exact ⟨(k : OnePoint ℕ), (weightedValue_eq_node q p k).symm⟩
  exact ⟨hc.bddBelow.mono hs, hc.bddAbove.mono hs⟩
theorem lowerEnvelope_le (q : ℝ) (hq : 1 < q) (p : ℝ[X]) (k : ℕ) :
    lowerEnvelope q p ≤ weightedValue q p k := csInf_le (envelope_bounded q hq p).1 ⟨k, rfl⟩
theorem le_upperEnvelope (q : ℝ) (hq : 1 < q) (p : ℝ[X]) (k : ℕ) :
    weightedValue q p k ≤ upperEnvelope q p := le_csSup (envelope_bounded q hq p).2 ⟨k, rfl⟩
theorem envelope_zero_bounds (q : ℝ) (hq : 1 < q) (p : ℝ[X]) :
    lowerEnvelope q p ≤ 0 ∧ 0 ≤ upperEnvelope q p :=
  ⟨ge_of_tendsto' (weightedValue_tendsto q hq p) (lowerEnvelope_le q hq p),
    le_of_tendsto' (weightedValue_tendsto q hq p) (le_upperEnvelope q hq p)⟩
theorem envelope_width_pos (q : ℝ) (hq : 1 < q) {p : ℝ[X]} (hp : p.eval 0 = 1) :
    0 < upperEnvelope q p - lowerEnvelope q p := by
  have hb := envelope_zero_bounds q hq p
  by_contra hn
  have hzero : ∀ k, weightedValue q p k = 0 := by
    intro k
    have hl := lowerEnvelope_le q hq p k
    have hu := le_upperEnvelope q hq p k
    push Not at hn
    linarith
  have he : ((0 : ℝ), p) = (0, (0 : ℝ[X])) := by
    apply polynomialNode_pair_injective q hq
    funext x
    induction x using OnePoint.rec with
    | infty => rfl
    | coe k =>
      change polynomialNode q 0 p (k : OnePoint ℕ) = polynomialNode q 0 0 (k : OnePoint ℕ)
      rw [← weightedValue_eq_node, hzero]
      simp
  have hpoly : p = 0 := congrArg (fun t : ℝ × ℝ[X] => t.2) he
  simp [hpoly] at hp

theorem envelope_denominator_pos (q : ℝ) (hq : 1 < q) (p : ℝ[X]) :
    0 < 1 - lowerEnvelope q p := by
  have h := (envelope_zero_bounds q hq p).1
  linarith
theorem envelopeRatio_pos (q : ℝ) (hq : 1 < q) {r : ℕ} {p : ℝ[X]}
    (hp : admissible r p) : 0 < envelopeRatio q p :=
  div_pos (envelope_width_pos q hq hp.2) (envelope_denominator_pos q hq p)
theorem admissible_one (r : ℕ) : admissible r (1 : ℝ[X]) := by constructor <;> simp
theorem envelope_ratios_nonempty (q : ℝ) (r : ℕ) :
    (envelopeRatio q '' {p : ℝ[X] | admissible r p}).Nonempty :=
  ⟨envelopeRatio q 1, 1, admissible_one r, rfl⟩
theorem envelope_ratios_bddBelow (q : ℝ) (hq : 1 < q) (r : ℕ) :
    BddBelow (envelopeRatio q '' {p : ℝ[X] | admissible r p}) := by
  refine ⟨0, ?_⟩
  rintro t ⟨p, hp, rfl⟩
  exact (envelopeRatio_pos q hq hp).le
theorem gamma_nonneg (q : ℝ) (hq : 1 < q) (r : ℕ) : 0 ≤ gamma q r := by
  apply le_csInf (envelope_ratios_nonempty q r)
  rintro t ⟨p, hp, rfl⟩
  exact (envelopeRatio_pos q hq hp).le

end LocalCertification.Extremal
