import LocalCertification.Quantum.HardStateInformation

set_option autoImplicit false
open LocalCertification.Extremal MeasureTheory InformationTheory Filter Metric
open scoped Topology ENNReal
noncomputable section
namespace LocalCertification.Quantum

/-- The actual shell cutoff D^(-3/4), expressed exponentially for the fixed local dimension. -/
def exponentialOverlapCutoff (d n : ℕ) : ℝ :=
  Real.exp (-(3/4)*Real.log (d:ℝ)*n)

theorem exponentialOverlapCutoff_pos (d n : ℕ) : 0<exponentialOverlapCutoff d n :=
  Real.exp_pos _

theorem dimension_eq_exp_log (d n : ℕ) (hd : 0<d) :
    (d:ℝ)^n=Real.exp (Real.log (d:ℝ)*n) := by
  rw [mul_comm,Real.exp_nat_mul,Real.exp_log (by exact_mod_cast hd)]

theorem exponentialOverlapCutoff_eq_rpow (d n : ℕ) (hd : 0<d) :
    exponentialOverlapCutoff d n=((d:ℝ)^n)^(-(3/4):ℝ) := by
  rw [Real.rpow_def_of_pos (pow_pos (by exact_mod_cast hd) n),Real.log_pow]
  unfold exponentialOverlapCutoff
  congr 1
  ring

/-- The maximally mixed target overlap is below the calibration cutoff, including n=0. -/
theorem uniform_fidelity_le_exponentialOverlapCutoff (d n : ℕ) (hd : 2≤d) :
    ((d:ℝ)^n)⁻¹≤exponentialOverlapCutoff d n := by
  rw [dimension_eq_exp_log d n (by omega),← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  have hlog : 0≤Real.log (d:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤d by omega))
  nlinarith [mul_nonneg hlog (Nat.cast_nonneg n)]

/-- The calibration contribution D*t^2 is exponentially small with exact rate log(d)/2. -/
theorem exponentialOverlapCutoff_square_dimension (d n : ℕ) (hd : 0<d) :
    (d:ℝ)^n*(exponentialOverlapCutoff d n)^2=Real.exp (-(Real.log (d:ℝ)/2)*n) := by
  rw [dimension_eq_exp_log d n hd,exponentialOverlapCutoff,← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  norm_num
  ring

/-- Every fixed polynomial is negligible relative to an actual exponential, with positive rate. -/
theorem nat_pow_exp_decay (c : ℝ) (hc : 0<c) (k : ℕ) :
    Tendsto (fun n : ℕ => (n:ℝ)^k*Real.exp (-c*n)) atTop (nhds 0) := by
  have h := monomial_decay_tendsto (Real.exp c) (Real.one_lt_exp_iff.mpr hc) k
  simpa only [← Real.exp_neg,← Real.exp_nat_mul,mul_comm] using h

theorem exponentialOverlapCutoff_tendsto (d : ℕ) (hd : 2≤d) :
    Tendsto (exponentialOverlapCutoff d) atTop (nhds 0) := by
  have hlog : 0<Real.log (d:ℝ) := Real.log_pos (by exact_mod_cast (show 1<d by omega))
  have h := nat_pow_exp_decay (3/4*Real.log (d:ℝ)) (by positivity) 0
  change Tendsto (fun n : ℕ => Real.exp (-(3/4)*Real.log (d:ℝ)*n)) atTop (nhds 0)
  simpa only [pow_zero,one_mul,neg_mul] using h

/-- The finite shell Markov union bound has an explicit exponential upper bound. -/
theorem exponentialOverlapCutoff_failure_le (d n r : ℕ) (hd : 2≤d) :
    ((r+1:ℕ):ℝ)/(exponentialOverlapCutoff d n*((d:ℝ)^n+1))≤
      ((r+1:ℕ):ℝ)*Real.exp (-(Real.log (d:ℝ)/4)*n) := by
  have ht := exponentialOverlapCutoff_pos d n
  have hD : 0<(d:ℝ)^n := pow_pos (by exact_mod_cast (show 0<d by omega)) n
  have hid : exponentialOverlapCutoff d n*(d:ℝ)^n=Real.exp ((Real.log (d:ℝ)/4)*n) := by
    rw [dimension_eq_exp_log d n (by omega),exponentialOverlapCutoff,← Real.exp_add]
    congr 1
    ring
  calc
    _≤((r+1:ℕ):ℝ)/(exponentialOverlapCutoff d n*(d:ℝ)^n) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    _=((r+1:ℕ):ℝ)*Real.exp (-(Real.log (d:ℝ)/4)*n) := by
      rw [hid,div_eq_mul_inv,← Real.exp_neg]
      congr 2
      ring

end LocalCertification.Quantum
