import CertificationGaussian.RadialLowAsymptotics

noncomputable section
open Filter
open scoped BigOperators Topology
namespace CertificationGaussian.Consumers

/-- The actual four-symbol low label set includes precisely the empty word at n=0. -/
theorem radial_low_empty_word (d r : ℕ) :
    (radialLowLabels (S:=Fin 0) d r (0:Fin 4)).card=1 := by
  rw [radialLowLabels_card]
  simp [radialWeightCutoff]

/-- At n=1 the original logarithmic cutoff is zero, so only the true distinguished word remains. -/
theorem radial_low_one_site (d r : ℕ) :
    (radialLowLabels (S:=Fin 1) d r (0:Fin 4)).card=1 := by
  rw [radialLowLabels_card]
  simp [radialWeightCutoff]

/-- The actual low-label counting correction in the Gram tail at tolerance n^-3 vanishes faster than n^-8. -/
theorem radial_low_gram_correction {K : Type*} [Fintype K] [DecidableEq K]
    (d r : ℕ) (hd : 2≤d) (k0 : K) :
    ∀ᶠ n : ℕ in atTop,
      ((radialLowLabels (S:=Fin n) d r k0).card:ℝ)*
        (((radialLowLabels (S:=Fin n) d r k0).card:ℝ)-1)/((d:ℝ)^n+1)*(n:ℝ)^6 ≤
          ((n:ℝ)^8)⁻¹ := by
  filter_upwards [radialLowLabels_polynomial_ratio_inverse d r hd k0 1 6 2 8] with n hn
  let m : ℝ := (radialLowLabels (S:=Fin n) d r k0).card
  have hm : 0≤m := Nat.cast_nonneg _
  have hD : (0:ℝ)<(d:ℝ)^n := pow_pos (by exact_mod_cast (show 0<d by omega)) _
  have hfrac : m*(m-1)/((d:ℝ)^n+1)≤m^2/(d:ℝ)^n := by
    apply (div_le_div_iff₀ (by positivity) hD).mpr
    nlinarith [mul_nonneg hm hD.le,sq_nonneg m]
  calc
    _ ≤ m^2/(d:ℝ)^n*(n:ℝ)^6 := mul_le_mul_of_nonneg_right hfrac (by positivity)
    _ = (n:ℝ)^6*m^2/(d:ℝ)^n := by ring
    _ ≤ _ := by simpa only [one_mul] using hn

/-- The asymptotic constants stay outside n and the theorem also accepts a fixed signed prefactor. -/
theorem radial_low_signed_prefactor (r : ℕ) :
    ∀ᶠ n : ℕ in atTop,(-3:ℝ)*(n:ℝ)^4*
      ((radialLowLabels (S:=Fin n) 2 r (0:Fin 4)).card:ℝ)^2/(2:ℝ)^n≤((n:ℝ)^12)⁻¹ :=
  radialLowLabels_polynomial_ratio_inverse 2 r (by norm_num) (0:Fin 4) (-3) 4 2 12

end CertificationGaussian.Consumers
