import LocalCertification.Asymptotic.OscillatoryVariation

open scoped Topology
open MeasureTheory Set Real Complex

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section
namespace LocalCertification.Asymptotic

def complexRegularizedReciprocal (ρ x : ℝ) : ℂ := (regularizedReciprocal ρ x : ℂ) / Complex.I

def complexRegularizedReciprocalDerivative (ρ x : ℝ) : ℂ :=
  (regularizedReciprocalDerivative ρ x : ℂ) / Complex.I

theorem complexRegularizedReciprocal_norm (ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) :
    ‖complexRegularizedReciprocal ρ x‖ ≤ 1 / (2 * ρ) := by
  simpa [complexRegularizedReciprocal, norm_div] using regularizedReciprocal_abs ρ hρ x

theorem complexRegularizedReciprocalDerivative_norm (ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) :
    ‖complexRegularizedReciprocalDerivative ρ x‖ ≤ 1 / (x ^ 2 + ρ ^ 2) := by
  simpa [complexRegularizedReciprocalDerivative, norm_div] using regularizedReciprocalDerivative_abs ρ hρ x

theorem complexRegularizedReciprocal_hasDerivAt (ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) :
    HasDerivAt (complexRegularizedReciprocal ρ) (complexRegularizedReciprocalDerivative ρ x) x := by
  convert (regularizedReciprocal_hasDerivAt ρ hρ x).ofReal_comp.div_const Complex.I using 1 <;> rfl

theorem regularization_identity (ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) (A E : ℂ) :
    A * E = A * ((ρ ^ 2 / (x ^ 2 + ρ ^ 2) : ℝ) : ℂ) * E +
      (A * complexRegularizedReciprocal ρ x) * (Complex.I * (x : ℂ) * E) := by
  have hd : ((x ^ 2 + ρ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (regularization_denominator_pos ρ hρ x).ne'
  unfold complexRegularizedReciprocal regularizedReciprocal
  push_cast at hd ⊢
  field_simp
  ring

/-- One integration by parts over the whole interval, with no regularity assumption outside it. -/
theorem oscillatory_regularization_bound {A A' E : ℝ → ℂ} {f f' : ℝ → ℝ}
    {a b ρ c S : ℝ} (hab : a ≤ b) (hρ : 0 < ρ)
    (hA : ContinuousOn A (Icc a b)) (hA' : ContinuousOn A' (Icc a b))
    (hf : ContinuousOn f (Icc a b)) (hf' : ContinuousOn f' (Icc a b))
    (hE : ContinuousOn E (Icc a b))
    (hdA : ∀ t ∈ Ioo a b, HasDerivAt A (A' t) t)
    (hdf : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hdE : ∀ t ∈ Ioo a b, HasDerivAt E (Complex.I * (f t : ℂ) * E t) t)
    (hEnorm : ∀ t ∈ Icc a b, ‖E t‖ = 1)
    (hS : ∀ t ∈ Icc a b, ‖A t‖ ≤ S)
    (hcontrol : ∀ t ∈ Icc a b, ‖A t‖ ≤ c * |f' t|) :
    ‖∫ t in a..b, A t * E t‖ ≤
      (c * ρ ^ 2 + S) * (∫ t in a..b, |f' t| / (f t ^ 2 + ρ ^ 2)) + S / ρ +
      (∫ t in a..b, ‖A' t‖) / (2 * ρ) := by
  let Q : ℝ → ℂ := fun t => complexRegularizedReciprocal ρ (f t)
  let Q' : ℝ → ℂ := fun t => complexRegularizedReciprocalDerivative ρ (f t) * (f' t : ℂ)
  let H : ℝ → ℂ := fun t => A t * Q t
  let H' : ℝ → ℂ := fun t => A' t * Q t + A t * Q' t
  let E' : ℝ → ℂ := fun t => Complex.I * (f t : ℂ) * E t
  let N : ℝ → ℂ := fun t => A t * ((ρ ^ 2 / (f t ^ 2 + ρ ^ 2) : ℝ) : ℂ) * E t
  let J : ℝ → ℝ := fun t => |f' t| / (f t ^ 2 + ρ ^ 2)
  have hQ : ContinuousOn Q (Icc a b) := by
    exact ((Complex.continuous_ofReal.comp (regularizedReciprocal_continuous ρ hρ)).div_const Complex.I).comp_continuousOn hf
  have hQ' : ContinuousOn Q' (Icc a b) := by
    exact (((Complex.continuous_ofReal.comp (regularizedReciprocalDerivative_continuous ρ hρ)).div_const Complex.I).comp_continuousOn hf).mul (Complex.continuous_ofReal.comp_continuousOn hf')
  have hH : ContinuousOn H (Icc a b) := hA.mul hQ
  have hH' : ContinuousOn H' (Icc a b) := (hA'.mul hQ).add (hA.mul hQ')
  have hE' : ContinuousOn E' (Icc a b) := (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hf)).mul hE
  have hJ : ContinuousOn J (Icc a b) := hf'.abs.div ((hf.pow 2).add continuousOn_const)
    (fun t _ => (regularization_denominator_pos ρ hρ (f t)).ne')
  have hN : ContinuousOn N (Icc a b) := by
    exact (hA.mul (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.div
      ((hf.pow 2).add continuousOn_const) (fun t _ => (regularization_denominator_pos ρ hρ (f t)).ne')))).mul hE
  have hdH (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt H (H' t) t := by
    have hdQ := ((regularizedReciprocal_hasDerivAt ρ hρ (f t)).comp t (hdf t ht)).ofReal_comp.div_const Complex.I
    convert (hdA t ht).mul hdQ using 1
    · rfl
    · dsimp [H', Q, Q', complexRegularizedReciprocal, complexRegularizedReciprocalDerivative]
      push_cast
      ring
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (by simpa only [uIcc_of_le hab] using hH) (by simpa only [uIcc_of_le hab] using hE)
    (by simpa only [min_eq_left hab, max_eq_right hab] using hdH)
    (by simpa only [min_eq_left hab, max_eq_right hab] using hdE)
    (hH'.intervalIntegrable_of_Icc hab) (hE'.intervalIntegrable_of_Icc hab)
  have hid : (∫ t in a..b, A t * E t) =
      (∫ t in a..b, N t) + (H b * E b - H a * E a - ∫ t in a..b, H' t * E t) := by
    have hadd : (∫ t in a..b, N t + H t * E' t) =
        (∫ t in a..b, N t) + (∫ t in a..b, H t * E' t) :=
      intervalIntegral.integral_add (hN.intervalIntegrable_of_Icc hab) ((hH.mul hE').intervalIntegrable_of_Icc hab)
    rw [← hibp, ← hadd]
    apply intervalIntegral.integral_congr
    intro t _
    exact regularization_identity ρ hρ (f t) (A t) (E t)
  have hNnorm (t : ℝ) (ht : t ∈ Icc a b) : ‖N t‖ ≤ c * ρ ^ 2 * J t := by
    dsimp [N, J]
    rw [norm_mul, norm_mul, hEnorm t ht, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (sq_nonneg _) (regularization_denominator_pos ρ hρ (f t)).le)]
    calc
      _ ≤ (c * |f' t|) * (ρ ^ 2 / (f t ^ 2 + ρ ^ 2)) :=
        mul_le_mul_of_nonneg_right (hcontrol t ht) (by positivity)
      _ = _ := by ring
  have hRnorm (t : ℝ) (ht : t ∈ Icc a b) :
      ‖H' t * E t‖ ≤ ‖A' t‖ / (2 * ρ) + S * J t := by
    dsimp [H', Q', Q, J]
    rw [norm_mul, hEnorm t ht, mul_one]
    calc
      _ ≤ ‖A' t * complexRegularizedReciprocal ρ (f t)‖ +
          ‖A t * (complexRegularizedReciprocalDerivative ρ (f t) * (f' t : ℂ))‖ := norm_add_le _ _
      _ = ‖A' t‖ * ‖complexRegularizedReciprocal ρ (f t)‖ +
          ‖A t‖ * (‖complexRegularizedReciprocalDerivative ρ (f t)‖ * |f' t|) := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖A' t‖ * (1 / (2 * ρ)) + S * ((1 / (f t ^ 2 + ρ ^ 2)) * |f' t|) :=
        add_le_add (mul_le_mul_of_nonneg_left (complexRegularizedReciprocal_norm ρ hρ (f t)) (norm_nonneg _))
          (mul_le_mul (hS t ht)
            (mul_le_mul_of_nonneg_right (complexRegularizedReciprocalDerivative_norm ρ hρ (f t)) (abs_nonneg _))
            (mul_nonneg (norm_nonneg _) (abs_nonneg _)) ((norm_nonneg _).trans (hS t ht)))
      _ = _ := by ring
  have hbnd (t : ℝ) (ht : t ∈ Icc a b) : ‖H t * E t‖ ≤ S / (2 * ρ) := by
    dsimp [H, Q]
    rw [norm_mul, norm_mul, hEnorm t ht, mul_one]
    exact (mul_le_mul (hS t ht) (complexRegularizedReciprocal_norm ρ hρ (f t))
      (norm_nonneg _) ((norm_nonneg _).trans (hS t ht))).trans_eq (by ring)
  have hnint : ‖∫ t in a..b, N t‖ ≤ c * ρ ^ 2 * ∫ t in a..b, J t := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hab
      (Filter.Eventually.of_forall (fun t ht => hNnorm t (Ioc_subset_Icc_self ht)))
      ((continuousOn_const.mul hJ).intervalIntegrable_of_Icc hab)
    simpa only [intervalIntegral.integral_const_mul] using hh
  have hrint : ‖∫ t in a..b, H' t * E t‖ ≤ (∫ t in a..b, ‖A' t‖) / (2 * ρ) + S * ∫ t in a..b, J t := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hab
      (Filter.Eventually.of_forall (fun t ht => hRnorm t (Ioc_subset_Icc_self ht)))
      (((hA'.norm.div_const (2 * ρ)).add (continuousOn_const.mul hJ)).intervalIntegrable_of_Icc hab)
    have hadd : (∫ t in a..b, ‖A' t‖ / (2 * ρ) + S * J t) =
        (∫ t in a..b, ‖A' t‖ / (2 * ρ)) + (∫ t in a..b, S * J t) :=
      intervalIntegral.integral_add ((hA'.norm.div_const (2 * ρ)).intervalIntegrable_of_Icc hab)
        ((continuousOn_const.mul hJ).intervalIntegrable_of_Icc hab)
    change ‖∫ t in a..b, H' t * E t‖ ≤ ∫ t in a..b, ‖A' t‖ / (2 * ρ) + S * J t at hh
    rw [hadd] at hh
    simpa only [div_eq_mul_inv, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const_mul] using hh
  rw [hid]
  have he : ‖H b * E b - H a * E a‖ ≤ S / ρ := by
    calc
      _ ≤ ‖H b * E b‖ + ‖H a * E a‖ := norm_sub_le _ _
      _ ≤ S / (2 * ρ) + S / (2 * ρ) := add_le_add (hbnd b ⟨hab, le_rfl⟩) (hbnd a ⟨le_rfl, hab⟩)
      _ = _ := by ring
  calc
    _ ≤ ‖∫ t in a..b, N t‖ + ‖H b * E b - H a * E a - ∫ t in a..b, H' t * E t‖ := norm_add_le _ _
    _ ≤ ‖∫ t in a..b, N t‖ + (‖H b * E b - H a * E a‖ + ‖∫ t in a..b, H' t * E t‖) :=
      add_le_add le_rfl (norm_sub_le _ _)
    _ ≤ c * ρ ^ 2 * (∫ t in a..b, J t) + (S / ρ + ((∫ t in a..b, ‖A' t‖) / (2 * ρ) + S * ∫ t in a..b, J t)) :=
      add_le_add hnint (add_le_add he hrint)
    _ = _ := by dsimp [J]; ring

end LocalCertification.Asymptotic
