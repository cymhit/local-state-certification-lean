import CertificationGaussian.RadialCoefficientBounds

/-! # Finite high-weight maxima for the Weyl coefficients

The high-weight maximum in the exponential typicality proof is over weights
of words of length `n`. The absolute bound on the entire coefficient sequence
used for the low-weight compression is independent of this restriction.
-/

namespace LocalCertification.Quantum

open CertificationGaussian

/-- The first and second radial coefficient sequences on the physical high-weight
interval. An empty interval needs no estimate; `hne` is used only to form its maximum. -/
theorem finite_high_weight_maxima (d n r L : ℕ) (hn : 1 ≤ n)
    (hne : (Finset.Ioc L n).Nonempty) (lam : ℕ → ℝ) :
    (Finset.Ioc L n).sup' hne (fun w => |radialFirstCoefficient d r lam w|) ≤
        radialCoefficientPolynomialConstant d r lam * (n : ℝ)^r * ((d+1 : ℝ)⁻¹)^L ∧
    (Finset.Ioc L n).sup' hne (fun w => |radialSecondCoefficient d r lam w|) ≤
        2 * (radialCoefficientPolynomialConstant d r (fun j => (lam j)^2) *
          (n : ℝ)^r * ((d+1 : ℝ)⁻¹)^L) := by
  have hbase : (d+1 : ℝ)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le
      (show (0 : ℝ) < 1 by norm_num) (show (1 : ℝ) ≤ d+1 by linarith [Nat.cast_nonneg (α := ℝ) d])
  have bound (u : ℕ → ℝ) (w : ℕ) (hw : w ∈ Finset.Ioc L n) :
      |radialFirstCoefficient d r u w| ≤
        radialCoefficientPolynomialConstant d r u * (n : ℝ)^r * ((d+1 : ℝ)⁻¹)^L := by
    obtain ⟨hL, hwn⟩ := Finset.mem_Ioc.mp hw
    exact (radialFirstCoefficient_bound_of_le d n r w hn hwn u).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by positivity) hbase hL.le)
        (mul_nonneg (radialCoefficientPolynomialConstant_nonneg d r u) (by positivity)))
  constructor
  · exact Finset.sup'_le hne _ (bound lam)
  · apply Finset.sup'_le
    intro w hw
    simpa only [radialSecondCoefficient, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      using mul_le_mul_of_nonneg_left (bound (fun j => (lam j)^2) w hw) (by norm_num : (0 : ℝ) ≤ 2)

end LocalCertification.Quantum
