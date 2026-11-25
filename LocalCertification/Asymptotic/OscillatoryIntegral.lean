import LocalCertification.Asymptotic.OscillatoryRegularization

open scoped Topology
open MeasureTheory Set Real Complex

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section
namespace LocalCertification.Asymptotic

/-- Interval C1/C2 data suffice; each half may have either weak monotonicity direction. -/
theorem oscillatory_integral_regularized {A A' : ℝ → ℂ} {θ θ' θ'' : ℝ → ℝ}
    {m w C S ρ : ℝ} (hm : 0 < m) (hρ : 0 < ρ) (hC : 0 ≤ C) (hS0 : 0 ≤ S)
    (hA : ContinuousOn A (Icc 0 (2 * Real.pi)))
    (hA' : ContinuousOn A' (Icc 0 (2 * Real.pi)))
    (hθ : ContinuousOn θ (Icc 0 (2 * Real.pi)))
    (hθ' : ContinuousOn θ' (Icc 0 (2 * Real.pi)))
    (hθ'' : ContinuousOn θ'' (Icc 0 (2 * Real.pi)))
    (hdA : ∀ t ∈ Ioo 0 (2 * Real.pi), HasDerivAt A (A' t) t)
    (hdθ : ∀ t ∈ Ioo 0 (2 * Real.pi), HasDerivAt θ (θ' t) t)
    (hdθ' : ∀ t ∈ Ioo 0 (2 * Real.pi), HasDerivAt θ' (θ'' t) t)
    (hfirst : MonotoneOn θ' (Icc 0 Real.pi) ∨ AntitoneOn θ' (Icc 0 Real.pi))
    (hsecond : MonotoneOn θ' (Icc Real.pi (2 * Real.pi)) ∨ AntitoneOn θ' (Icc Real.pi (2 * Real.pi)))
    (hS : ∀ t ∈ Icc 0 (2 * Real.pi), ‖A t‖ ≤ S)
    (hcontrol : ∀ t ∈ Icc 0 (2 * Real.pi), ‖A t‖ ≤ C * |θ'' t|) :
    ‖∫ t in (0 : ℝ)..(2 * Real.pi), A t * Complex.exp (Complex.I * ((m * θ t - w * t : ℝ) : ℂ))‖ ≤
      2 * Real.pi * C * ρ / m + (2 * Real.pi + 1) * S / ρ +
        (∫ t in (0 : ℝ)..(2 * Real.pi), ‖A' t‖) / (2 * ρ) := by
  let f : ℝ → ℝ := fun t => m * θ' t - w
  let f' : ℝ → ℝ := fun t => m * θ'' t
  let E : ℝ → ℂ := fun t => Complex.exp (Complex.I * ((m * θ t - w * t : ℝ) : ℂ))
  let J : ℝ → ℝ := fun t => |f' t| / (f t ^ 2 + ρ ^ 2)
  have h0π : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hπ2 : Real.pi ≤ 2 * Real.pi := by linarith [Real.pi_pos]
  have h02 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hf : ContinuousOn f (Icc 0 (2 * Real.pi)) := (continuousOn_const.mul hθ').sub continuousOn_const
  have hf' : ContinuousOn f' (Icc 0 (2 * Real.pi)) := continuousOn_const.mul hθ''
  have hE : ContinuousOn E (Icc 0 (2 * Real.pi)) :=
    Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn ((continuousOn_const.mul hθ).sub
        (continuousOn_const.mul continuousOn_id))))
  have hdf (t : ℝ) (ht : t ∈ Ioo 0 (2 * Real.pi)) : HasDerivAt f (f' t) t :=
    ((hdθ' t ht).const_mul m).sub_const w
  have hdE (t : ℝ) (ht : t ∈ Ioo 0 (2 * Real.pi)) : HasDerivAt E (Complex.I * (f t : ℂ) * E t) t := by
    have hd := ((((hdθ t ht).const_mul m).sub ((hasDerivAt_id t).const_mul w)).ofReal_comp.const_mul Complex.I).cexp
    convert hd using 1
    · rfl
    · dsimp [f, E]
      push_cast
      ring
  have hEnorm (t : ℝ) (_ : t ∈ Icc 0 (2 * Real.pi)) : ‖E t‖ = 1 :=
    Complex.norm_exp_I_mul_ofReal _
  have hctr (t : ℝ) (ht : t ∈ Icc 0 (2 * Real.pi)) : ‖A t‖ ≤ (C / m) * |f' t| := by
    calc
      _ ≤ C * |θ'' t| := hcontrol t ht
      _ = _ := by dsimp [f']; rw [abs_mul, abs_of_pos hm]; field_simp
  have hJ : ContinuousOn J (Icc 0 (2 * Real.pi)) := hf'.abs.div ((hf.pow 2).add continuousOn_const)
    (fun t _ => (regularization_denominator_pos ρ hρ (f t)).ne')
  have hsub1 : Icc (0 : ℝ) Real.pi ⊆ Icc 0 (2 * Real.pi) := by
    intro t ht; exact ⟨ht.1, ht.2.trans hπ2⟩
  have hsub2 : Icc Real.pi (2 * Real.pi) ⊆ Icc (0 : ℝ) (2 * Real.pi) := by
    intro t ht; exact ⟨h0π.trans ht.1, ht.2⟩
  have hmono1 : MonotoneOn f (Icc 0 Real.pi) ∨ AntitoneOn f (Icc 0 Real.pi) := by
    rcases hfirst with h | h
    · left; intro x hx y hy hxy; dsimp [f]; nlinarith [h hx hy hxy]
    · right; intro x hx y hy hxy; dsimp [f]; nlinarith [h hx hy hxy]
  have hmono2 : MonotoneOn f (Icc Real.pi (2 * Real.pi)) ∨ AntitoneOn f (Icc Real.pi (2 * Real.pi)) := by
    rcases hsecond with h | h
    · left; intro x hx y hy hxy; dsimp [f]; nlinarith [h hx hy hxy]
    · right; intro x hx y hy hxy; dsimp [f]; nlinarith [h hx hy hxy]
  have hj1 : (∫ t in (0 : ℝ)..Real.pi, J t) ≤ Real.pi / ρ :=
    integral_abs_arctan_weight_le h0π hρ (hf.mono hsub1) (hf'.mono hsub1)
      (fun t ht => hdf t ⟨ht.1, ht.2.trans_le hπ2⟩) hmono1
  have hj2 : (∫ t in Real.pi..(2 * Real.pi), J t) ≤ Real.pi / ρ :=
    integral_abs_arctan_weight_le hπ2 hρ (hf.mono hsub2) (hf'.mono hsub2)
      (fun t ht => hdf t ⟨h0π.trans_lt ht.1, ht.2⟩) hmono2
  have hj : (∫ t in (0 : ℝ)..(2 * Real.pi), J t) ≤ 2 * Real.pi / ρ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      ((hJ.mono hsub1).intervalIntegrable_of_Icc h0π) ((hJ.mono hsub2).intervalIntegrable_of_Icc hπ2)]
    exact (add_le_add hj1 hj2).trans_eq (by ring)
  have hbase := oscillatory_regularization_bound h02 hρ hA hA' hf hf' hE hdA hdf hdE hEnorm hS hctr
  calc
    _ ≤ (C / m * ρ ^ 2 + S) * (∫ t in (0 : ℝ)..(2 * Real.pi), J t) + S / ρ +
        (∫ t in (0 : ℝ)..(2 * Real.pi), ‖A' t‖) / (2 * ρ) := hbase
    _ ≤ (C / m * ρ ^ 2 + S) * (2 * Real.pi / ρ) + S / ρ +
        (∫ t in (0 : ℝ)..(2 * Real.pi), ‖A' t‖) / (2 * ρ) := by
      gcongr
    _ = _ := by field_simp; ring

/-- The numerical choice of the smoothing scale preserves the paper's constants. -/
theorem oscillatory_scale_bound {m C S V : ℝ} (hm : 0 < m)
    (hC : 0 ≤ C) (hS : 0 ≤ S) (hV : 0 ≤ V) :
    2 * Real.pi * C * (5 * Real.sqrt m / 8) / m +
        (2 * Real.pi + 1) * S / (5 * Real.sqrt m / 8) + V / (2 * (5 * Real.sqrt m / 8)) ≤
      (4 * C + 12 * S + V) / Real.sqrt m := by
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hsq : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm.le
  have hpi : Real.pi < 16 / 5 := by linarith [Real.pi_lt_d2]
  have hnum : 5 * Real.pi / 4 * C + 8 * (2 * Real.pi + 1) / 5 * S + 4 / 5 * V ≤ 4 * C + 12 * S + V := by
    nlinarith [mul_nonneg hC (show 0 ≤ 16 / 5 - Real.pi by linarith),
      mul_nonneg hS (show 0 ≤ 16 / 5 - Real.pi by linarith)]
  calc
    _ = (5 * Real.pi / 4 * C + 8 * (2 * Real.pi + 1) / 5 * S + 4 / 5 * V) / Real.sqrt m := by
      field_simp
      rw [hsq]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hnum hs.le

/-- Oscillatory integral estimate with interval regularity, real frequency and nonnegative constant. -/
theorem oscillatory_integral_bound {A A' : ℝ → ℂ} {θ θ' θ'' : ℝ → ℝ}
    {m w C S : ℝ} (hm : 1 ≤ m) (hC : 0 ≤ C) (hS0 : 0 ≤ S)
    (hA : ContinuousOn A (Icc 0 (2 * Real.pi)))
    (hA' : ContinuousOn A' (Icc 0 (2 * Real.pi)))
    (hθ : ContinuousOn θ (Icc 0 (2 * Real.pi)))
    (hθ' : ContinuousOn θ' (Icc 0 (2 * Real.pi)))
    (hθ'' : ContinuousOn θ'' (Icc 0 (2 * Real.pi)))
    (hdA : ∀ t ∈ Ioo 0 (2 * Real.pi), HasDerivAt A (A' t) t)
    (hdθ : ∀ t ∈ Ioo 0 (2 * Real.pi), HasDerivAt θ (θ' t) t)
    (hdθ' : ∀ t ∈ Ioo 0 (2 * Real.pi), HasDerivAt θ' (θ'' t) t)
    (hfirst : MonotoneOn θ' (Icc 0 Real.pi) ∨ AntitoneOn θ' (Icc 0 Real.pi))
    (hsecond : MonotoneOn θ' (Icc Real.pi (2 * Real.pi)) ∨ AntitoneOn θ' (Icc Real.pi (2 * Real.pi)))
    (hS : ∀ t ∈ Icc 0 (2 * Real.pi), ‖A t‖ ≤ S)
    (hcontrol : ∀ t ∈ Icc 0 (2 * Real.pi), ‖A t‖ ≤ C * |θ'' t|) :
    ‖∫ t in (0 : ℝ)..(2 * Real.pi), A t * Complex.exp (Complex.I * ((m * θ t - w * t : ℝ) : ℂ))‖ ≤
      (4 * C + 12 * S + ∫ t in (0 : ℝ)..(2 * Real.pi), ‖A' t‖) / Real.sqrt m := by
  have hm0 : 0 < m := by linarith
  have hρ : 0 < 5 * Real.sqrt m / 8 := by positivity
  exact (oscillatory_integral_regularized hm0 hρ hC hS0 hA hA' hθ hθ' hθ'' hdA hdθ hdθ'
    hfirst hsecond hS hcontrol).trans (oscillatory_scale_bound hm0 hC hS0
      (intervalIntegral.integral_nonneg_of_forall (by positivity) (fun t => norm_nonneg (A' t))))

end LocalCertification.Asymptotic
