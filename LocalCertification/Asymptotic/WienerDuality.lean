import LocalCertification.Extremal.BinomialMoments
import LocalCertification.Asymptotic.InfiniteDual

/-! # Extrapolation and the augmented Wiener coefficient norm

The sequence `f` stores the coefficients of orders 1,2,… . Its constant
term is fixed at `a^(r+1)`. Polynomial moment conditions express the
repeated-node constraints. The separate boundary value retains the dual
mass at the compactification point.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Topology OnePoint
open Polynomial
noncomputable section
namespace LocalCertification.Asymptotic.Wiener

def tailNorm (f : ℕ → ℝ) : ℝ := ∑' n, |f n|

def atOne (a : ℝ) (r : ℕ) (f : ℕ → ℝ) : ℝ := a ^ (r + 1) + ∑' n, f n

def augmentedNorm (a : ℝ) (r : ℕ) (f : ℕ → ℝ) : ℝ :=
  tailNorm f + |atOne a r f|

/-- Vanishing moments against all polynomials of degree at most `r`. -/
def MomentFeasible (a : ℝ) (r : ℕ) (f : ℕ → ℝ) : Prop :=
  Summable (fun n => |f n|) ∧
  ∀ p : ℝ[X], p.natDegree ≤ r →
    HasSum (fun n : ℕ => f n * a ^ (n + 1) * p.eval ((n : ℝ) + 1))
      (-(a ^ (r + 1)) * p.eval 0)

private def embedWeights {m : ℕ} (j : Fin m → ℕ) (weights : Fin m → ℝ) (n : ℕ) : ℝ :=
  ∑ i, if j i = n then weights i else 0

private theorem embed_hasSum {m : ℕ} (j : Fin m → ℕ) (weights : Fin m → ℝ)
    (g : ℕ → ℝ) :
    HasSum (fun n => embedWeights j weights n * g n) (∑ i, weights i * g (j i)) := by
  have hs (i : Fin m) : HasSum (fun n : ℕ => if j i = n then weights i * g (j i) else 0)
      (weights i * g (j i)) := by
    simpa only [eq_comm] using (hasSum_ite_eq (j i) (weights i * g (j i)))
  apply (hasSum_sum (s := Finset.univ) (fun i _ => hs i)).congr_fun
  intro n
  rw [embedWeights, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases he : j i = n <;> simp [he]

private theorem embed_abs {m : ℕ} (j : Fin m → ℕ) (hj : Function.Injective j)
    (weights : Fin m → ℝ) (n : ℕ) :
    |embedWeights j weights n| = embedWeights j (fun i => |weights i|) n := by
  by_cases hn : ∃ i, j i = n
  · obtain ⟨i, rfl⟩ := hn
    simp [embedWeights, hj.eq_iff]
  · simp [embedWeights, not_exists.mp hn]

/-- A norming finite dual gives a feasible finite series with *exact* augmented norm. -/
theorem finite_dual_attains (q : ℝ) (hq : 1 < q) (r : ℕ) :
    ∃ f : ℕ → ℝ, MomentFeasible q⁻¹ r f ∧
      augmentedNorm q⁻¹ r f = q⁻¹ ^ (r + 1) * Extremal.extremalValue q r := by
  obtain ⟨c, x, μ, _, _, hx, ho, hinf, _, hrepro, htv, _⟩ :=
    Extremal.finite_extremal_dual_complete q hq r
  obtain ⟨j, hj, he⟩ := Extremal.ordered_finite_labels r x hx ho hinf
  let A := q⁻¹ ^ (r + 1)
  let μfin := fun i : Fin (r + 1) => μ i.castSucc
  let μinf := μ (Fin.last (r + 1))
  let f := fun n => -A * embedWeights j μfin n
  have hA : 0 < A := pow_pos (inv_pos.mpr (by linarith)) _
  have hmass : (∑ i, μfin i) + μinf = 1 := by
    simpa only [Fin.sum_univ_castSucc] using Extremal.finite_dual_mass q r x μ hrepro
  have hvar : (∑ i, |μfin i|) + |μinf| = Extremal.extremalValue q r := by
    simpa only [Fin.sum_univ_castSucc] using htv
  have hs : HasSum f (-A * ∑ i, μfin i) := by
    simpa only [f, mul_one] using (embed_hasSum j μfin (fun _ => 1)).mul_left (-A)
  have habs : HasSum (fun n => |f n|) (A * ∑ i, |μfin i|) := by
    simpa only [f, abs_mul, abs_neg, abs_of_pos hA, embed_abs j hj.injective, mul_one] using
      (embed_hasSum j (fun i => |μfin i|) (fun _ => 1)).mul_left A
  refine ⟨f, ⟨habs.summable, ?_⟩, ?_⟩
  · intro p hp
    have hm := Extremal.finite_dual_polynomial q r x μ hrepro p hp
    rw [Fin.sum_univ_castSucc, hinf] at hm
    simp only [← he, Extremal.polynomialNode_nat, Extremal.polynomialNode_infty,
      zero_add, mul_zero, add_zero, Nat.cast_add, Nat.cast_one] at hm
    have h := (embed_hasSum j μfin (fun n => q⁻¹ ^ (n + 1) * p.eval ((n : ℝ) + 1))).mul_left (-A)
    rw [hm]
    simpa only [f, μfin, mul_assoc] using h
  · have hboundary : atOne q⁻¹ r f = A * μinf := by
      rw [atOne, hs.tsum_eq]
      change A + -A * _ = _
      linear_combination -A * hmass
    rw [augmentedNorm, tailNorm, habs.tsum_eq, hboundary, abs_mul, abs_of_pos hA]
    change A * _ + A * _ = A * _
    rw [← mul_add, hvar]

theorem moment_reproduction (q : ℝ) (hq : 1 < q) (r : ℕ) (f : ℕ → ℝ)
    (hf : MomentFeasible q⁻¹ r f) (h : ℝ) (p : ℝ[X]) (hp : p.natDegree ≤ r) :
    HasSum (fun n : ℕ => -(q⁻¹ ^ (r + 1))⁻¹ * f n *
      Extremal.polynomialNode q h p (n : OnePoint ℕ))
      (h + p.eval 0 - (q⁻¹ ^ (r + 1))⁻¹ * atOne q⁻¹ r f * h) := by
  let A := q⁻¹ ^ (r + 1)
  have hA : A ≠ 0 := (pow_pos (inv_pos.mpr (by linarith : 0 < q)) _).ne'
  have hn : Summable (fun n => ‖f n‖) := by simpa only [Real.norm_eq_abs] using hf.1
  have hsum : Summable f := hn.of_norm
  have ht := ((hsum.hasSum.mul_right h).add (hf.2 p hp)).mul_left (-A⁻¹)
  convert ht using 1
  · funext n
    simp only [Extremal.polynomialNode_nat, Nat.cast_add, Nat.cast_one, A]
    ring
  · unfold atOne
    change h + p.eval 0 - A⁻¹ * (A + ∑' n, f n) * h =
      -A⁻¹ * ((∑' n, f n) * h + -A * p.eval 0)
    field_simp
    ring

/-- Any feasible summable series is an extrapolation dual with the boundary mass at 1. -/
theorem extremal_le_augmented (q : ℝ) (hq : 1 < q) (r : ℕ) (f : ℕ → ℝ)
    (hf : MomentFeasible q⁻¹ r f) :
    Extremal.extremalValue q r ≤ (q⁻¹ ^ (r + 1))⁻¹ * augmentedNorm q⁻¹ r f := by
  let A := q⁻¹ ^ (r + 1)
  have hA : 0 < A := pow_pos (inv_pos.mpr (by linarith)) _
  obtain ⟨c, hc, hm⟩ := Extremal.extremalValue_attained q hq r
  let p := Extremal.coefficientPolynomial c
  have hs := moment_reproduction q hq r f hf c.1 p (Extremal.coefficientPolynomial_degree c)
  have hpt (n : ℕ) : -A⁻¹ * f n * Extremal.polynomialNode q c.1 p (n : OnePoint ℕ)
      ≤ A⁻¹ * |f n| := by
    let t := Extremal.polynomialNode q c.1 p (n : OnePoint ℕ)
    have ht : |t| ≤ 1 := hc (n : OnePoint ℕ)
    calc
      _ ≤ |-A⁻¹ * f n * t| := le_abs_self _
      _ = (A⁻¹ * |f n|) * |t| := by rw [abs_mul, abs_mul, abs_neg, abs_inv, abs_of_pos hA]
      _ ≤ A⁻¹ * |f n| := mul_le_of_le_one_right (by positivity) ht
  have hsum := hs.tsum_eq
  have hle := hs.summable.tsum_le_tsum hpt (hf.1.mul_left A⁻¹)
  rw [hsum, tsum_mul_left] at hle
  have hfirst : c.1 + p.eval 0 = Extremal.extremalValue q r := by
    simpa only [Extremal.extrapolation_formula] using hm
  rw [hfirst] at hle
  have hinf : |c.1| ≤ 1 := hc ∞
  have hb : atOne q⁻¹ r f * c.1 ≤ |atOne q⁻¹ r f| :=
    (le_abs_self _).trans ((abs_mul _ _).le.trans
      (mul_le_of_le_one_right (abs_nonneg _) hinf))
  change _ ≤ A⁻¹ * (tailNorm f + |atOne q⁻¹ r f|)
  change Extremal.extremalValue q r - A⁻¹ * atOne q⁻¹ r f * c.1 ≤ A⁻¹ * tailNorm f at hle
  linarith [mul_le_mul_of_nonneg_left hb (inv_pos.mpr hA).le]

/-- Infimum of the positive-order coefficient norm over the real moment constraints. -/
def momentInfimum (a : ℝ) (r : ℕ) : ℝ := sInf (tailNorm '' {f | MomentFeasible a r f})

private theorem scaled_extremal_le (q : ℝ) (hq : 1 < q) (r : ℕ) (f : ℕ → ℝ)
    (hf : MomentFeasible q⁻¹ r f) :
    q⁻¹ ^ (r + 1) * Extremal.extremalValue q r ≤ augmentedNorm q⁻¹ r f := by
  have ha : 0 < q⁻¹ ^ (r + 1) := pow_pos (inv_pos.mpr (by linarith)) _
  have h := mul_le_mul_of_nonneg_left (extremal_le_augmented q hq r f hf) ha.le
  simpa only [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] using h

theorem augmented_infimum_eq (q : ℝ) (hq : 1 < q) (r : ℕ) :
    sInf (augmentedNorm q⁻¹ r '' {f | MomentFeasible q⁻¹ r f}) =
      q⁻¹ ^ (r + 1) * Extremal.extremalValue q r := by
  obtain ⟨f, hf, he⟩ := finite_dual_attains q hq r
  have hl : ∀ t ∈ augmentedNorm q⁻¹ r '' {f | MomentFeasible q⁻¹ r f},
      q⁻¹ ^ (r + 1) * Extremal.extremalValue q r ≤ t := by
    rintro t ⟨g, hg, rfl⟩
    exact scaled_extremal_le q hq r g hg
  have hm : _ ∈ augmentedNorm q⁻¹ r '' {f | MomentFeasible q⁻¹ r f} := ⟨f, hf, he⟩
  exact le_antisymm (csInf_le ⟨_, hl⟩ hm) (le_csInf ⟨_, hm⟩ hl)

theorem moment_infimum_sandwich (q : ℝ) (hq : 1 < q) (r : ℕ) :
    (q⁻¹ ^ (r + 1))⁻¹ * momentInfimum q⁻¹ r ≤ Extremal.extremalValue q r ∧
    Extremal.extremalValue q r ≤ 2 * (q⁻¹ ^ (r + 1))⁻¹ * momentInfimum q⁻¹ r + 1 := by
  let A := q⁻¹ ^ (r + 1)
  have ha : 0 < A := pow_pos (inv_pos.mpr (by linarith)) _
  obtain ⟨f, hf, he⟩ := finite_dual_attains q hq r
  have mem : tailNorm f ∈ tailNorm '' {t | MomentFeasible q⁻¹ r t} := ⟨f, hf, rfl⟩
  have hb : BddBelow (tailNorm '' {t | MomentFeasible q⁻¹ r t}) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨g, _, rfl⟩
    exact tsum_nonneg (fun _ => abs_nonneg _)
  have hu : momentInfimum q⁻¹ r ≤ A * Extremal.extremalValue q r := by
    calc
      _ ≤ tailNorm f := csInf_le hb mem
      _ ≤ augmentedNorm q⁻¹ r f := le_add_of_nonneg_right (abs_nonneg _)
      _ = _ := he
  have hl : (A * Extremal.extremalValue q r - A) / 2 ≤ momentInfimum q⁻¹ r := by
    apply le_csInf ⟨_, mem⟩
    rintro _ ⟨g, hg, rfl⟩
    have h := scaled_extremal_le q hq r g hg
    have hs : |∑' n, g n| ≤ tailNorm g := by
      simpa only [Real.norm_eq_abs, tailNorm] using (norm_tsum_le_tsum_norm
        (show Summable (fun n => ‖g n‖) by simpa only [Real.norm_eq_abs] using hg.1))
    have hbound : |atOne q⁻¹ r g| ≤ A + tailNorm g := by
      exact (abs_add_le _ _).trans (add_le_add ((abs_of_pos ha).le) hs)
    change A * Extremal.extremalValue q r ≤ tailNorm g + |atOne q⁻¹ r g| at h
    linarith
  constructor
  · change A⁻¹ * _ ≤ _
    rw [← div_eq_inv_mul]
    exact (div_le_iff₀ ha).mpr (by linarith)
  · change _ ≤ 2 * A⁻¹ * _ + 1
    have hh : Extremal.extremalValue q r ≤ (2 * momentInfimum q⁻¹ r + A) / A := by
      apply (le_div_iff₀ ha).mpr
      linarith
    convert hh using 1
    field_simp

end LocalCertification.Asymptotic.Wiener
