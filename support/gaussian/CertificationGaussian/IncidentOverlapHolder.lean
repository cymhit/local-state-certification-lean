import CertificationGaussian.FourVertexOverlap
import Mathlib.MeasureTheory.Integral.MeanInequalities

noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators ENNReal NNReal
namespace CertificationGaussian
namespace IncidentHolder
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [CompactSpace Ω] [SecondCountableTopology Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem compact_integrable (f : Ω → ℝ) (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Six-factor Hölder on the original record probability space. -/
theorem integral_six_holder {J : Type*} [Fintype J] (hJ : Fintype.card J = 6)
    (f : J → Ω → ℝ) (hf : ∀ i, Continuous (f i)) (hn : ∀ i x, 0 ≤ f i x) :
    (∫ x, ∏ i, f i x ∂μ) ≤ ∏ i, (∫ x, (f i x)^6 ∂μ)^((1:ℝ)/6) := by
  classical
  have hi i := compact_integrable μ (fun x => (f i x)^6) ((hf i).pow 6)
  have hp := compact_integrable μ (fun x => ∏ i, f i x) (continuous_finsetProd _ (fun i _ => hf i))
  have hsum : ∑ i : J, (1:ℝ)/6 = 1 := by simp [hJ]
  have hmeas (i : J) : AEMeasurable (fun x => ENNReal.ofReal ((f i x)^6)) μ :=
    ((hf i).pow 6).measurable.ennreal_ofReal.aemeasurable
  have h := ENNReal.lintegral_prod_norm_pow_le (μ := μ) (Finset.univ : Finset J)
    (f := fun (i : J) (x : Ω) => ENNReal.ofReal ((f i x)^6))
    (fun i _ => hmeas i)
    (p := fun _ => (1:ℝ)/6) hsum (fun _ _ => by norm_num)
  have hroot (x : ℝ≥0∞) : (x^6)^((1:ℝ)/6)=x := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simp_rw [ENNReal.ofReal_pow (hn _ _), hroot] at h
  have he i : (∫⁻ x, (ENNReal.ofReal (f i x))^6 ∂μ) =
      ENNReal.ofReal (∫ x, (f i x)^6 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hi i) (Filter.Eventually.of_forall (fun x => pow_nonneg (hn i x) 6))]
    simp_rw [ENNReal.ofReal_pow (hn _ _)]
  simp_rw [he] at h
  have hleft : (∫⁻ x, ∏ i, ENNReal.ofReal (f i x) ∂μ) =
      ENNReal.ofReal (∫ x, ∏ i, f i x ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hp
      (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => hn i x)))]
    congr 1
    funext x
    exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => hn i x)).symm
  rw [hleft] at h
  have hm i : 0 ≤ ∫ x, (f i x)^6 ∂μ := integral_nonneg (fun x => pow_nonneg (hn i x) 6)
  simp_rw [ENNReal.ofReal_rpow_of_nonneg (hm _) (by norm_num : (0:ℝ)≤1/6)] at h
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hm i) _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hm i) _))).mp h

/-- Add exactly `6 - card J` constant-one slots before applying six-factor Hölder. -/
theorem integral_incident_holder {J : Type*} [Fintype J] (hJ : Fintype.card J ≤ 6)
    (f : J → Ω → ℝ) (hf : ∀ i, Continuous (f i)) (hn : ∀ i x, 0 ≤ f i x)
    (m : ℝ) (hm : ∀ i, (∫ x, (f i x)^6 ∂μ) = m) :
    (∫ x, ∏ i, f i x ∂μ) ≤ (m^((1:ℝ)/6))^(Fintype.card J) := by
  let F : J ⊕ Fin (6 - Fintype.card J) → Ω → ℝ := Sum.elim f (fun _ _ => 1)
  have hcard : Fintype.card (J ⊕ Fin (6 - Fintype.card J)) = 6 := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have h := integral_six_holder μ hcard F
    (by intro i; cases i with | inl i => exact hf i | inr i => exact continuous_const)
    (by intro i x; cases i with | inl i => exact hn i x | inr i => exact zero_le_one)
  simpa [F, Fintype.prod_sum_type, hm] using h

/-- Repeated incident edges are separate labeled factors, even for coincident neighbors. -/
theorem integral_three_incident (a b c : ℕ) (habc : a+b+c ≤ 6)
    (f g h : Ω → ℝ) (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (nf : ∀ x, 0 ≤ f x) (ng : ∀ x, 0 ≤ g x) (nh : ∀ x, 0 ≤ h x)
    (m : ℝ) (mf : (∫ x, f x^6 ∂μ)=m) (mg : (∫ x, g x^6 ∂μ)=m)
    (mh : (∫ x, h x^6 ∂μ)=m) :
    (∫ x, f x^a*g x^b*h x^c ∂μ) ≤ (m^((1:ℝ)/6))^(a+b+c) := by
  let F : Fin a ⊕ (Fin b ⊕ Fin c) → Ω → ℝ :=
    Sum.elim (fun _ => f) (Sum.elim (fun _ => g) (fun _ => h))
  have hhcard : Fintype.card (Fin a ⊕ (Fin b ⊕ Fin c)) ≤ 6 := by
    simpa [Fintype.card_sum, Nat.add_assoc] using habc
  have hc : ∀ i, Continuous (F i) := by
    intro i; rcases i with i | (i | i); exact hf; exact hg; exact hh
  have hn : ∀ i x, 0 ≤ F i x := by
    intro i x; rcases i with i | (i | i); exact nf x; exact ng x; exact nh x
  have hm : ∀ i, (∫ x, (F i x)^6 ∂μ)=m := by
    intro i; rcases i with i | (i | i); exact mf; exact mg; exact mh
  have ht := integral_incident_holder μ hhcard F hc hn m hm
  simpa [F, Fintype.prod_sum_type, mul_assoc, Nat.add_assoc] using ht

variable {I : Type*} [Fintype I]
variable (u : Ω → sphere (0 : EuclideanSpace ℂ I) 1)

/-- The sixth root is used only to keep all graph exponents integral. -/
theorem sixthRoot_pow_six (m : ℝ) (hm : 0 ≤ m) : (m^((1:ℝ)/6))^6=m := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hm]
  norm_num

theorem incident_overlap_holder (hu : Continuous u) (m : ℝ)
    (hm : ∀ x, (∫ y, recordOverlap u x y^6 ∂μ)=m)
    (a b c : ℕ) (habc : a+b+c ≤ 6) (x y z : Ω) :
    (∫ s, recordOverlap u x s^a*recordOverlap u y s^b*recordOverlap u z s^c ∂μ)
      ≤ (m^((1:ℝ)/6))^(a+b+c) := by
  exact integral_three_incident μ a b c habc _ _ _
    (by unfold recordOverlap; fun_prop) (by unfold recordOverlap; fun_prop)
    (by unfold recordOverlap; fun_prop) (recordOverlap_nonneg u x)
    (recordOverlap_nonneg u y) (recordOverlap_nonneg u z) m (hm x) (hm y) (hm z)
/-- The remaining triangle is eliminated at its third vertex, then its second.
No matching identity is used; exponents count each remaining edge once. -/
theorem triangle_elimination (hu : Continuous u) (m : ℝ) (hm0 : 0 ≤ m)
    (hm : ∀ x, (∫ y, recordOverlap u x y^6 ∂μ)=m)
    (a b c : ℕ) (ha : a ≤ 6) (hbc : b+c ≤ 6) :
    (∫ x, ∫ y, ∫ z, recordOverlap u x y^a*recordOverlap u x z^b*
      recordOverlap u y z^c ∂μ ∂μ ∂μ) ≤ (m^((1:ℝ)/6))^(a+b+c) := by
  let r := m^((1:ℝ)/6)
  have hr : 0 ≤ r := Real.rpow_nonneg hm0 _
  have hz (x y : Ω) :
      (∫ z, recordOverlap u x y^a*recordOverlap u x z^b*recordOverlap u y z^c ∂μ)
        ≤ recordOverlap u x y^a*r^(b+c) := by
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (recordOverlap_nonneg u x y) _)
    simpa [r] using incident_overlap_holder μ u hu m hm b c 0 (by omega) x y x
  have hy (x : Ω) :
      (∫ y, ∫ z, recordOverlap u x y^a*recordOverlap u x z^b*
        recordOverlap u y z^c ∂μ ∂μ) ≤ r^(a+b+c) := by
    calc
      _ ≤ ∫ y, recordOverlap u x y^a*r^(b+c) ∂μ := by
        refine integral_mono_of_nonneg ?_ (compact_integrable μ _ (by unfold recordOverlap; fun_prop)) ?_
        · exact Filter.Eventually.of_forall (fun y => integral_nonneg (fun z => by unfold recordOverlap; positivity))
        · exact Filter.Eventually.of_forall (hz x)
      _ = (∫ y, recordOverlap u x y^a ∂μ)*r^(b+c) := integral_mul_const _ _
      _ ≤ r^a*r^(b+c) := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr _)
        simpa [r] using incident_overlap_holder μ u hu m hm a 0 0 (by omega) x x x
      _ = r^(a+b+c) := by rw [← pow_add]; congr 1; omega
  calc
    _ ≤ ∫ _ : Ω, r^(a+b+c) ∂μ := by
      refine integral_mono_of_nonneg ?_ (integrable_const _) ?_
      · exact Filter.Eventually.of_forall (fun x => integral_nonneg (fun y =>
          integral_nonneg (fun z => by unfold recordOverlap; positivity)))
      · exact Filter.Eventually.of_forall hy
    _ = _ := by simp [r]

/-- The four-vertex graph is reduced to a triangle by its last vertex.
Its twelve labeled edges contribute twelve factors of the sixth root. -/
theorem overlap_integral_le (g : FourVertexMultigraph) (hg : g.IsSixRegular)
    (hu : Continuous u) (m : ℝ) (hm0 : 0 ≤ m)
    (hm : ∀ x, (∫ y, recordOverlap u x y^6 ∂μ)=m) :
    (∫ x, g.overlapProduct u x ∂fourReadoutLaw μ) ≤ m^2 := by
  let r := m^((1:ℝ)/6)
  have hr : 0 ≤ r := Real.rpow_nonneg hm0 _
  have hr6 : r^6=m := sixthRoot_pow_six m hm0
  have hs : g.e01+g.e02+g.e12=6 := by
    obtain ⟨h0,h1,h2,h3⟩ := hg
    omega
  have hlast : g.e03+g.e13+g.e23=6 := hg.2.2.2
  have hb : g.e02+g.e12 ≤ 6 := by have := hg.2.2.1; omega
  have ha : g.e01 ≤ 6 := by have := hg.1; omega
  have ht := triangle_elimination μ u hu m hm0 hm g.e01 g.e02 g.e12 ha hb
  rw [hs,hr6] at ht
  rw [fourReadoutLaw_integral μ _ (by unfold FourVertexMultigraph.overlapProduct recordOverlap; fun_prop)]
  have hz (a b c : Ω) :
      (∫ d, g.overlapProduct u (a,b,c,d) ∂μ) ≤
        recordOverlap u a b^g.e01*recordOverlap u a c^g.e02*recordOverlap u b c^g.e12*m := by
    have he (d : Ω) : g.overlapProduct u (a,b,c,d) =
        (recordOverlap u a b^g.e01*recordOverlap u a c^g.e02*recordOverlap u b c^g.e12)*
        (recordOverlap u a d^g.e03*recordOverlap u b d^g.e13*recordOverlap u c d^g.e23) := by
      unfold FourVertexMultigraph.overlapProduct
      ring
    simp_rw [he]
    rw [integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ (by unfold recordOverlap; positivity)
    simpa only [hlast, sixthRoot_pow_six m hm0] using incident_overlap_holder μ u hu m hm
      g.e03 g.e13 g.e23 hlast.le a b c
  have hc (a b : Ω) : (∫ c, ∫ d, g.overlapProduct u (a,b,c,d) ∂μ ∂μ) ≤
      (∫ c, recordOverlap u a b^g.e01*recordOverlap u a c^g.e02*recordOverlap u b c^g.e12 ∂μ)*m := by
    rw [← integral_mul_const]
    refine integral_mono_of_nonneg ?_ (compact_integrable μ _ (by unfold recordOverlap; fun_prop)) ?_
    · exact Filter.Eventually.of_forall (fun c => integral_nonneg (fun d => by
        unfold FourVertexMultigraph.overlapProduct recordOverlap; positivity))
    · exact Filter.Eventually.of_forall (hz a b)
  have hi (a : Ω) : Integrable
      (fun b => (∫ c, recordOverlap u a b^g.e01*recordOverlap u a c^g.e02*
        recordOverlap u b c^g.e12 ∂μ)*m) μ := by
    have h := compact_integrable (μ.prod μ)
      (fun x : Ω × Ω => recordOverlap u a x.1^g.e01*recordOverlap u a x.2^g.e02*
        recordOverlap u x.1 x.2^g.e12) (by unfold recordOverlap; fun_prop)
    exact h.integral_prod_left.mul_const m
  have hbnd (a : Ω) : (∫ b, ∫ c, ∫ d, g.overlapProduct u (a,b,c,d) ∂μ ∂μ ∂μ) ≤
      (∫ b, ∫ c, recordOverlap u a b^g.e01*recordOverlap u a c^g.e02*
        recordOverlap u b c^g.e12 ∂μ ∂μ)*m := by
    rw [← integral_mul_const]
    refine integral_mono_of_nonneg ?_ (hi a) ?_
    · exact Filter.Eventually.of_forall (fun b => integral_nonneg (fun c => integral_nonneg (fun d => by
        unfold FourVertexMultigraph.overlapProduct recordOverlap; positivity)))
    · exact Filter.Eventually.of_forall (hc a)
  have houter : Integrable
      (fun a => (∫ b, ∫ c, recordOverlap u a b^g.e01*recordOverlap u a c^g.e02*
        recordOverlap u b c^g.e12 ∂μ ∂μ)*m) μ := by
    have h := compact_integrable (μ.prod (μ.prod μ))
      (fun x : Ω × (Ω × Ω) => recordOverlap u x.1 x.2.1^g.e01*
        recordOverlap u x.1 x.2.2^g.e02*recordOverlap u x.2.1 x.2.2^g.e12)
      (by unfold recordOverlap; fun_prop)
    have he (a : Ω) :
        (∫ x : Ω × Ω, recordOverlap u a x.1^g.e01*recordOverlap u a x.2^g.e02*
          recordOverlap u x.1 x.2^g.e12 ∂μ.prod μ) =
        (∫ b, ∫ c, recordOverlap u a b^g.e01*recordOverlap u a c^g.e02*
          recordOverlap u b c^g.e12 ∂μ ∂μ) :=
      integral_prod _ (compact_integrable (μ.prod μ) _ (by unfold recordOverlap; fun_prop))
    have hh := h.integral_prod_left
    simp only [he] at hh
    exact hh.mul_const m
  calc
    _ ≤ ∫ a, (∫ b, ∫ c, recordOverlap u a b^g.e01*recordOverlap u a c^g.e02*
        recordOverlap u b c^g.e12 ∂μ ∂μ)*m ∂μ := by
      refine integral_mono_of_nonneg ?_ houter ?_
      · exact Filter.Eventually.of_forall (fun a => integral_nonneg (fun b => integral_nonneg (fun c =>
          integral_nonneg (fun d => by unfold FourVertexMultigraph.overlapProduct recordOverlap; positivity))))
      · exact Filter.Eventually.of_forall hbnd
    _ = (∫ a, ∫ b, ∫ c, recordOverlap u a b^g.e01*recordOverlap u a c^g.e02*
        recordOverlap u b c^g.e12 ∂μ ∂μ ∂μ)*m := integral_mul_const _ _
    _ ≤ m*m := mul_le_mul_of_nonneg_right ht hm0
    _ = m^2 := (pow_two m).symm
/-- The same incident estimate with the integrated vertex in the first overlap slot. -/
theorem incident_overlap_holder_left (hu : Continuous u) (m : ℝ)
    (hm : ∀ x, (∫ y, recordOverlap u x y^6 ∂μ)=m)
    (a b c : ℕ) (habc : a+b+c ≤ 6) (x y z : Ω) :
    (∫ s, recordOverlap u s x^a*recordOverlap u s y^b*recordOverlap u s z^c ∂μ)
      ≤ (m^((1:ℝ)/6))^(a+b+c) := by
  calc
    _ = ∫ s, recordOverlap u x s^a*recordOverlap u y s^b*recordOverlap u z s^c ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun s => by dsimp only; rw [recordOverlap_symm u s x,
        recordOverlap_symm u s y, recordOverlap_symm u s z])
    _ ≤ _ := incident_overlap_holder μ u hu m hm a b c habc x y z
end IncidentHolder
end CertificationGaussian










