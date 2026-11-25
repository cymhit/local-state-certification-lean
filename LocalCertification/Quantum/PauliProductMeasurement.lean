import LocalCertification.Quantum.CompleteBornRecord
import LocalCertification.Quantum.PauliMeasurement

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Classical CertificationGaussian
open scoped BigOperators ENNReal
noncomputable section
namespace LocalCertification.Quantum

/-- Uniform words are exactly independent uniform local labels, including the empty word. -/
theorem finiteUniformMeasure_words (d n : ℕ) [NeZero d] [Nonempty (Fin d)] :
    finiteUniformMeasure (Fin n → Fin d) = Measure.pi (fun _ : Fin n => uniformFiniteOutcome d) := by
  apply Measure.ext_of_singleton
  intro x
  rw [finiteUniformMeasure_atom, Measure.pi_singleton]
  simp [uniformFiniteOutcome, Measure.smul_apply, ENNReal.inv_pow]

/-- Every site retains its actual Z/X/Y basis label. -/
def pauliProductSetting (n : ℕ) (b : Fin n → Fin 3) : Fin n → LocalUnitary 2 :=
  fun i => pauliBasisUnitary (b i)

theorem pauliProductSetting_measurable (n : ℕ) : Measurable (pauliProductSetting n) :=
  measurable_of_countable _

/-- The complete global reference record consists of independent uniform bases and independent uniform outcomes. -/
def pauliProductReference (n : ℕ) : Measure ((Fin n → Fin 3) × QuditIndex 2 n) :=
  (Measure.pi (fun _ : Fin n => uniformFiniteOutcome 3)).prod
    (Measure.pi (fun _ : Fin n => uniformFiniteOutcome 2))

instance pauliProductReference_probability (n : ℕ) : IsProbabilityMeasure (pauliProductReference n) := by
  unfold pauliProductReference
  infer_instance

/-- Regrouping complete local records loses no basis or outcome information. -/
def pauliProductRecordEquiv (n : ℕ) :
    (Fin n → PauliRecord) ≃ᵐ ((Fin n → Fin 3) × QuditIndex 2 n) where
  toFun ω := (fun i => (ω i).1, fun i => (ω i).2)
  invFun z := fun i => (z.1 i,z.2 i)
  left_inv ω := by funext i; exact Prod.mk.eta
  right_inv z := by cases z; rfl
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

/-- The global reference law is precisely the product of the actual six local Pauli records. -/
theorem pauliProductReference_eq_local_records (n : ℕ) :
    (Measure.pi (fun _ : Fin n => pauliBasisRecords)).map (pauliProductRecordEquiv n) =
      pauliProductReference n := by
  apply Measure.ext_of_singleton
  intro z
  rw [MeasurableEquiv.map_apply]
  rw [show (pauliProductRecordEquiv n) ⁻¹' {z} = {(pauliProductRecordEquiv n).symm z} by
    ext w
    change pauliProductRecordEquiv n w = z ↔ w = (pauliProductRecordEquiv n).symm z
    constructor
    · intro h; rw [← h]; simp
    · intro h; rw [h]; simp]
  rw [Measure.pi_singleton]
  simp only [CertificationGaussian.Consumers.pauli_record_mass, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [pauliProductReference, show ({z} : Set ((Fin n → Fin 3) × QuditIndex 2 n)) =
    {z.1} ×ˢ {z.2} by ext w; simp [Prod.ext_iff], Measure.prod_prod,
    Measure.pi_singleton, Measure.pi_singleton]
  simp only [uniformFiniteOutcome, Measure.smul_apply, Measure.count_singleton, smul_eq_mul,
    mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← mul_pow]
  congr 1
  rw [← ENNReal.mul_inv (by norm_num) (by norm_num)]
  norm_num

/-- The physical mixed state is sampled only after the complete product basis is chosen. -/
def pauliProductBornLaw (n : ℕ) (ρ : QIT.State (QuditIndex 2 n)) :
    Measure ((Fin n → Fin 3) × QuditIndex 2 n) :=
  completeBornRecordLaw ρ (pauliProductSetting n) (pauliProductSetting_measurable n)
    (Measure.pi (fun _ : Fin n => uniformFiniteOutcome 3))

instance pauliProductBornLaw_probability (n : ℕ) (ρ : QIT.State (QuditIndex 2 n)) :
    IsProbabilityMeasure (pauliProductBornLaw n ρ) := by
  unfold pauliProductBornLaw
  infer_instance

/-- The complete reference/Born Radon--Nikodym density is the actual 2^n times QIT probability. -/
theorem pauliProductBornLaw_density (n : ℕ) (ρ : QIT.State (QuditIndex 2 n)) :
    (pauliProductReference n).withDensity (fun z =>
      ENNReal.ofReal ((2:ℝ)^n * productBorn 2 n (pauliProductSetting n z.1) ρ z.2)) =
      pauliProductBornLaw n ρ := by
  have h := completeBornRecordLaw_density ρ (pauliProductSetting n)
    (pauliProductSetting_measurable n) (Measure.pi (fun _ : Fin n => uniformFiniteOutcome 3))
  simpa only [finiteUniformMeasure_words, pauliProductReference, pauliProductBornLaw, Nat.cast_ofNat] using h

/-- Every literal basis word has probability 3^-n before the copy is measured. -/
theorem pauliProductBornLaw_fst (n : ℕ) (ρ : QIT.State (QuditIndex 2 n)) :
    (pauliProductBornLaw n ρ).fst = Measure.pi (fun _ : Fin n => uniformFiniteOutcome 3) :=
  completeBornRecordLaw_fst ρ _ _ _

/-- The actual complete record has mass 3^-n times its possibly zero Born probability. -/
theorem pauliProductBornLaw_atom (n : ℕ) (ρ : QIT.State (QuditIndex 2 n))
    (b : Fin n → Fin 3) (x : QuditIndex 2 n) :
    pauliProductBornLaw n ρ {(b,x)} = (3:ℝ≥0∞)⁻¹^n *
      ENNReal.ofReal (productBorn 2 n (pauliProductSetting n b) ρ x) := by
  rw [show ({(b,x)} : Set ((Fin n → Fin 3) × QuditIndex 2 n)) = {b} ×ˢ {x} by
    ext w; simp [Prod.ext_iff], pauliProductBornLaw,
    completeBornRecordLaw_rectangle ρ _ _ _ {b} (measurableSet_singleton b) x,
    lintegral_singleton, Measure.pi_singleton]
  simp only [uniformFiniteOutcome, Measure.smul_apply, Measure.count_singleton,
    smul_eq_mul, mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_comm _ _

/-- This global effect is the tensor product of the actual six-record local projectors. -/
theorem pauliProductPOVM_effect (n : ℕ) (b : Fin n → Fin 3) (x : QuditIndex 2 n) :
    (productBasisPOVM 2 n (pauliProductSetting n b)).effects x =
      tensorMatrix (fun i => pauliRecordedProjector (b i,x i)) := by
  rw [productBasisPOVM_effect]
  congr 1
  funext i
  exact basisPOVM_pauliRecordedProjector (b i,x i)

/-- All outcomes of each actual product Pauli basis have total probability one. -/
theorem pauliProductBorn_sum (n : ℕ) (b : Fin n → Fin 3) (ρ : QIT.State (QuditIndex 2 n)) :
    ∑ x, productBorn 2 n (pauliProductSetting n b) ρ x = 1 :=
  productBorn_sum 2 n _ ρ

/-- Any real or complex score is integrated against the genuine Born law by weighting the complete reference record. -/
theorem pauliProductBornLaw_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (ρ : QIT.State (QuditIndex 2 n)) (f : ((Fin n → Fin 3) × QuditIndex 2 n) → E) :
    ∫ z, f z ∂pauliProductBornLaw n ρ =
      ∫ z, ((2:ℝ)^n * productBorn 2 n (pauliProductSetting n z.1) ρ z.2) • f z
        ∂pauliProductReference n := by
  rw [← pauliProductBornLaw_density, integral_withDensity_eq_integral_toReal_smul
    (measurable_of_countable _) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal
    (mul_nonneg (by positivity : 0 ≤ (2:ℝ)^n) (productBorn_nonneg 2 n _ ρ _))]

end LocalCertification.Quantum
