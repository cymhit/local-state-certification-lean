import CertificationGaussian.HaarOverlapSixth
import Mathlib.Analysis.MeanInequalities

noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators
namespace CertificationGaussian

/-- Six natural multiplicities encode all edges of a loopless four-vertex multigraph. -/
structure FourVertexMultigraph where
  e01 : ℕ
  e02 : ℕ
  e03 : ℕ
  e12 : ℕ
  e13 : ℕ
  e23 : ℕ

def FourVertexMultigraph.IsSixRegular (g : FourVertexMultigraph) : Prop :=
  g.e01+g.e02+g.e03=6 ∧ g.e01+g.e12+g.e13=6 ∧
    g.e02+g.e12+g.e23=6 ∧ g.e03+g.e13+g.e23=6

def FourVertexMultigraph.ContainsFourCycle (g : FourVertexMultigraph) : Prop :=
  0<g.e01 ∧ 0<g.e12 ∧ 0<g.e23 ∧ 0<g.e03

/-- Regularity forces equal multiplicities on opposite pairs, without a simplicity assumption. -/
theorem FourVertexMultigraph.opposite_eq (g : FourVertexMultigraph) (h : g.IsSixRegular) :
    g.e01=g.e23 ∧ g.e02=g.e13 ∧ g.e03=g.e12 := by
  obtain ⟨h0,h1,h2,h3⟩ := h
  omega

/-- The weighted arithmetic/geometric mean bound used for the three perfect matchings. -/
theorem three_matching_sixth_bound (a b c : ℕ) (habc : a+b+c=6)
    (x y z : ℝ) (hx : 0≤x) (hy : 0≤y) (hz : 0≤z) :
    x^a*y^b*z^c ≤ ((a:ℝ)*x^6+(b:ℝ)*y^6+(c:ℝ)*z^6)/6 := by
  have he (u : ℝ) (hu : 0≤u) (k : ℕ) : (u^6)^((k:ℝ)/6)=u^k := by
    rw [← Real.rpow_natCast u 6,← Real.rpow_mul hu]
    have hk : (6:ℝ)*((k:ℝ)/6)=k := by ring
    norm_num only [Nat.cast_ofNat] at *
    rw [hk,Real.rpow_natCast]
  have hsum : (a:ℝ)/6+(b:ℝ)/6+(c:ℝ)/6=1 := by
    have h : (a:ℝ)+b+c=6 := by exact_mod_cast habc
    linarith
  have h := Real.geom_mean_le_arith_mean3_weighted
    (show (0:ℝ)≤(a:ℝ)/6 by positivity)
    (show (0:ℝ)≤(b:ℝ)/6 by positivity)
    (show (0:ℝ)≤(c:ℝ)/6 by positivity)
    (pow_nonneg hx 6) (pow_nonneg hy 6) (pow_nonneg hz 6) hsum
  rw [he x hx a,he y hy b,he z hz c] at h
  convert h using 1
  ring

/-- Four independent complete records, not merely a replacement vector law. -/
def fourReadoutLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    Measure (Ω × (Ω × (Ω × Ω))) := μ.prod (μ.prod (μ.prod μ))

instance fourReadoutLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : IsProbabilityMeasure (fourReadoutLaw μ) := by
  unfold fourReadoutLaw
  infer_instance

section Records
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [CompactSpace Ω] [SecondCountableTopology Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {I : Type*} [Fintype I]
variable (u : Ω → sphere (0 : EuclideanSpace ℂ I) 1)

/-- Absolute overlap of the actual recorded unit vectors. -/
def recordOverlap (x y : Ω) : ℝ := ‖inner ℂ (u x).val (u y).val‖

omit [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [SecondCountableTopology Ω] in
theorem recordOverlap_nonneg (x y : Ω) : 0≤recordOverlap u x y := norm_nonneg _

omit [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [SecondCountableTopology Ω] in
theorem recordOverlap_le_one (x y : Ω) : recordOverlap u x y≤1 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (u x).val (u y).val
  simpa only [recordOverlap,mem_sphere_zero_iff_norm.mp (u x).property,
    mem_sphere_zero_iff_norm.mp (u y).property,mul_one] using h

omit [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [SecondCountableTopology Ω] in
theorem recordOverlap_symm (x y : Ω) : recordOverlap u x y=recordOverlap u y x :=
  norm_inner_symm _ _

omit [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [SecondCountableTopology Ω] in
@[fun_prop] theorem recordOverlap_continuous (hu : Continuous u) :
    Continuous (Function.uncurry (recordOverlap u)) := by
  unfold recordOverlap
  fun_prop

/-- Fubini for continuous functions on the actual compact four-record probability space. -/
theorem fourReadoutLaw_integral (f : Ω × (Ω × (Ω × Ω)) → ℝ) (hf : Continuous f) :
    ∫ x, f x ∂fourReadoutLaw μ = ∫ a, ∫ b, ∫ c, ∫ d, f (a,b,c,d) ∂μ ∂μ ∂μ ∂μ := by
  have hi : Integrable f (fourReadoutLaw μ) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [fourReadoutLaw,integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with a
  have hb : Continuous (fun x : Ω × (Ω × Ω) => f (a,x)) :=
    hf.comp (continuous_const.prodMk continuous_id)
  rw [integral_prod _ (hb.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply integral_congr_ae
  filter_upwards [] with b
  have hc : Continuous (fun x : Ω × Ω => f (a,b,x)) :=
    hb.comp (continuous_const.prodMk continuous_id)
  exact integral_prod _ (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

def matchingOverlap01 (x : Ω × (Ω × (Ω × Ω))) : ℝ :=
  recordOverlap u x.1 x.2.1 * recordOverlap u x.2.2.1 x.2.2.2

def matchingOverlap02 (x : Ω × (Ω × (Ω × Ω))) : ℝ :=
  recordOverlap u x.1 x.2.2.1 * recordOverlap u x.2.1 x.2.2.2

def matchingOverlap03 (x : Ω × (Ω × (Ω × Ω))) : ℝ :=
  recordOverlap u x.2.1 x.2.2.1 * recordOverlap u x.1 x.2.2.2

theorem matchingOverlap01_sixth (hu : Continuous u) (m : ℝ)
    (hm : ∀ a, (∫ b, recordOverlap u a b^6 ∂μ)=m) :
    (∫ x, matchingOverlap01 u x^6 ∂fourReadoutLaw μ)=m^2 := by
  rw [fourReadoutLaw_integral μ _ (by unfold matchingOverlap01 recordOverlap; fun_prop)]
  simp only [matchingOverlap01,mul_pow]
  simp_rw [integral_const_mul,integral_mul_const,hm]
  simp [pow_two]

theorem matchingOverlap02_sixth (hu : Continuous u) (m : ℝ)
    (hm : ∀ a, (∫ b, recordOverlap u a b^6 ∂μ)=m) :
    (∫ x, matchingOverlap02 u x^6 ∂fourReadoutLaw μ)=m^2 := by
  rw [fourReadoutLaw_integral μ _ (by unfold matchingOverlap02 recordOverlap; fun_prop)]
  simp only [matchingOverlap02,mul_pow]
  simp_rw [integral_const_mul,integral_mul_const,hm]
  simp [pow_two]

theorem matchingOverlap03_sixth (hu : Continuous u) (m : ℝ)
    (hm : ∀ a, (∫ b, recordOverlap u a b^6 ∂μ)=m) :
    (∫ x, matchingOverlap03 u x^6 ∂fourReadoutLaw μ)=m^2 := by
  rw [fourReadoutLaw_integral μ _ (by unfold matchingOverlap03 recordOverlap; fun_prop)]
  simp only [matchingOverlap03,mul_pow]
  simp_rw [integral_const_mul,integral_mul_const,hm]
  simp [pow_two]

/-- All twelve multigraph edges retain their multiplicities in the actual integrand. -/
def FourVertexMultigraph.overlapProduct (g : FourVertexMultigraph)
    (x : Ω × (Ω × (Ω × Ω))) : ℝ :=
  recordOverlap u x.1 x.2.1^g.e01 * recordOverlap u x.1 x.2.2.1^g.e02 *
    recordOverlap u x.1 x.2.2.2^g.e03 * recordOverlap u x.2.1 x.2.2.1^g.e12 *
    recordOverlap u x.2.1 x.2.2.2^g.e13 * recordOverlap u x.2.2.1 x.2.2.2^g.e23

omit [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [SecondCountableTopology Ω] in
theorem FourVertexMultigraph.overlapProduct_matchings (g : FourVertexMultigraph)
    (hg : g.IsSixRegular) (x : Ω × (Ω × (Ω × Ω))) :
    g.overlapProduct u x =
      matchingOverlap01 u x^g.e01 * matchingOverlap02 u x^g.e02 * matchingOverlap03 u x^g.e03 := by
  obtain ⟨h1,h2,h3⟩ := g.opposite_eq hg
  unfold FourVertexMultigraph.overlapProduct matchingOverlap01 matchingOverlap02 matchingOverlap03
  rw [← h1,← h2,← h3]
  simp only [mul_pow]
  ring

/-- The finite graph bound follows from the three genuine disjoint matching moments. -/
theorem FourVertexMultigraph.overlap_integral_le (g : FourVertexMultigraph)
    (hg : g.IsSixRegular) (hu : Continuous u) (m : ℝ)
    (hm : ∀ a, (∫ b, recordOverlap u a b^6 ∂μ)=m) :
    (∫ x, g.overlapProduct u x ∂fourReadoutLaw μ) ≤ m^2 := by
  have hi (f : Ω × (Ω × (Ω × Ω)) → ℝ) (hf : Continuous f) :
      Integrable f (fourReadoutLaw μ) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hb := integral_mono
    (hi (fun x => g.overlapProduct u x) (by unfold FourVertexMultigraph.overlapProduct recordOverlap; fun_prop))
    (hi (fun x => ((g.e01:ℝ)*matchingOverlap01 u x^6+
      (g.e02:ℝ)*matchingOverlap02 u x^6+(g.e03:ℝ)*matchingOverlap03 u x^6)/6)
      (by unfold matchingOverlap01 matchingOverlap02 matchingOverlap03 recordOverlap; fun_prop))
    (fun x => by
      rw [g.overlapProduct_matchings u hg]
      exact three_matching_sixth_bound g.e01 g.e02 g.e03 hg.1 _ _ _
        (mul_nonneg (recordOverlap_nonneg _ _ _) (recordOverlap_nonneg _ _ _))
        (mul_nonneg (recordOverlap_nonneg _ _ _) (recordOverlap_nonneg _ _ _))
        (mul_nonneg (recordOverlap_nonneg _ _ _) (recordOverlap_nonneg _ _ _)))
  rw [integral_div,integral_add (hi _ (by unfold matchingOverlap01 matchingOverlap02 recordOverlap; fun_prop))
    (hi _ (by unfold matchingOverlap03 recordOverlap; fun_prop)),
    integral_add (hi _ (by unfold matchingOverlap01 recordOverlap; fun_prop))
      (hi _ (by unfold matchingOverlap02 recordOverlap; fun_prop))] at hb
  simp_rw [integral_const_mul,matchingOverlap01_sixth μ u hu m hm,
    matchingOverlap02_sixth μ u hu m hm,matchingOverlap03_sixth μ u hu m hm] at hb
  have hsum : (g.e01:ℝ)+g.e02+g.e03=6 := by exact_mod_cast hg.1
  nlinarith

end Records
end CertificationGaussian
