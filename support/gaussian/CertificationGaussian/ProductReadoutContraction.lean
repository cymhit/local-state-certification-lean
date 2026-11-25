import CertificationGaussian.TensorReadoutFactorization

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace CertificationGaussian

variable {S Ω : Type*} [Fintype S] [DecidableEq S]

/-- The actual tensor product of the recorded local projectors on physical-site coordinates. -/
def productRecordedProjector (d : ℕ) (r : Ω → ComplexUnitary (Fin d) × Fin d) (ω : S → Ω) :
    Matrix (S → Fin d) (S → Fin d) ℂ :=
  wickTensorMatrix (fun s => recordedProjector d (r (ω s)))

/-- A finite-complement tensor uses I-P exactly at the selected sites and P elsewhere. -/
def productReadoutFactor (d : ℕ) (r : Ω → ComplexUnitary (Fin d) × Fin d)
    (A : Finset S) (ω : S → Ω) : Matrix (S → Fin d) (S → Fin d) ℂ :=
  wickTensorMatrix (fun s => localReadoutFactor d (decide (s∈A)) (r (ω s)))

/-- One genuine term of the four-output/eight-input global Wick expansion. -/
def productRecordWickIntegrand (d : ℕ) (r : Ω → ComplexUnitary (Fin d) × Fin d)
    (A : Fin 4 × Fin 2 → Finset S) (π : Equiv.Perm (Fin 4 × Fin 2))
    (x : (S → Ω) × ((S → Ω) × ((S → Ω) × (S → Ω)))) : ℂ :=
  Matrix.trace (productRecordedProjector d r x.1*productRecordedProjector d r x.2.1*
    productRecordedProjector d r x.2.2.1*productRecordedProjector d r x.2.2.2)*
  Matrix.trace (wickTensorMatrix (fun t : Fin 4 × Fin 2 =>
    productReadoutFactor d r (A t) (fourRecordAt x t.1))*wickTensorPermutationMatrix π)

/-- The original complex matrix integrand is a product over sites, with no norm relaxation. -/
theorem productRecordWickIntegrand_eq_prod (d : ℕ)
    (r : Ω → ComplexUnitary (Fin d) × Fin d) (A : Fin 4 × Fin 2 → Finset S)
    (π : Equiv.Perm (Fin 4 × Fin 2))
    (x : (S → Ω) × ((S → Ω) × ((S → Ω) × (S → Ω)))) :
    productRecordWickIntegrand d r A π x =
      ∏ s,recordedChangedSiteIntegrand d r (fun t => decide (s∈A t)) π
        (x.1 s,x.2.1 s,x.2.2.1 s,x.2.2.2 s) := by
  have hx (b : Fin 4) (s : S) : fourRecordAt x b s =
      fourRecordAt (x.1 s,x.2.1 s,x.2.2.1 s,x.2.2.2 s) b := by
    fin_cases b <;> rfl
  have h0 (z : Ω × (Ω × (Ω × Ω))) : fourRecordAt z 0=z.1 := rfl
  have h1 (z : Ω × (Ω × (Ω × Ω))) : fourRecordAt z 1=z.2.1 := rfl
  have h2 (z : Ω × (Ω × (Ω × Ω))) : fourRecordAt z 2=z.2.2.1 := rfl
  have h3 (z : Ω × (Ω × (Ω × Ω))) : fourRecordAt z 3=z.2.2.2 := rfl
  have h := wickTensorMatrix_site_contraction
    (fun b s => recordedProjector d (r (fourRecordAt x b s)))
    (fun t s => localReadoutFactor d (decide (s∈A t)) (r (fourRecordAt x t.1 s))) π
  simpa only [productRecordWickIntegrand,productRecordedProjector,productReadoutFactor,
    recordedChangedSiteIntegrand,hx,h0,h1,h2,h3] using h

/-- The normalized actual global integral factors into the normalized local integrals under the genuine product law. -/
theorem productRecordWickIntegral_eq_prod [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ)
    (r : Ω → ComplexUnitary (Fin d) × Fin d) (A : Fin 4 × Fin 2 → Finset S)
    (π : Equiv.Perm (Fin 4 × Fin 2)) :
    ((d:ℂ)^(Fintype.card S))^4*
      (∫ x,productRecordWickIntegrand d r A π x ∂fourReadoutLaw (Measure.pi (fun _ : S => μ))) =
      ∏ s,(d:ℂ)^4*(∫ x,recordedChangedSiteIntegrand d r (fun t => decide (s∈A t)) π x
        ∂fourReadoutLaw μ) := by
  simp_rw [productRecordWickIntegrand_eq_prod]
  rw [fourRecordSite_integral_product,Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ]
  congr 1
  rw [← pow_mul,← pow_mul,Nat.mul_comm]

/-- The physical sites touched by the eight selected finite complements. -/
def eightComplementUnion (A : Fin 4 × Fin 2 → Finset S) : Finset S := Finset.univ.biUnion A

omit [Fintype S] in
/-- Eight complements, each of order at most r, can change at most 8r sites. -/
theorem eightComplementUnion_card_le (A : Fin 4 × Fin 2 → Finset S) (r : ℕ)
    (hA : ∀ t,(A t).card≤r) : (eightComplementUnion A).card≤8*r := by
  have h := Finset.card_biUnion_le_card_mul Finset.univ A r (fun t _ => hA t)
  simpa [eightComplementUnion] using h

omit [Fintype S] in
/-- Outside the actual union all eight choices are P, irrespective of repeated or overlapping subsets. -/
theorem eightComplementUnion_outside (A : Fin 4 × Fin 2 → Finset S) (s : S)
    (hs : s∉eightComplementUnion A) : (fun t => decide (s∈A t))=(fun _ => false) := by
  funext t
  have hst : s∉A t := fun h => hs (Finset.mem_biUnion.mpr ⟨t,Finset.mem_univ t,h⟩)
  simp [hst]

omit [Fintype S] in
/-- A generic finite product estimate, used only after all local contraction hypotheses are concretely proved. -/
theorem finite_site_cost_bound (F : Finset S) (z : S → ℂ) (C κ : ℝ)
    (h : ∀ s,‖z s‖≤(if s∈F then C else κ)) [Fintype S] :
    ‖∏ s,z s‖≤C^F.card*κ^(Fintype.card S-F.card) := by
  rw [norm_prod]
  calc
    _ ≤ ∏ s : S,if s∈F then C else κ := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun s _ => h s)
    _ = _ := by
      rw [Finset.prod_ite]
      simp [← Finset.sdiff_eq_filter,Finset.card_sdiff]

/-- Haar product readout terms retain the exact support size and the actual dimension-only local constants. -/
theorem haarProductRecordWickContraction_le (d : ℕ) [NeZero d] (hd : 2≤d)
    (A : Fin 4 × Fin 2 → Finset S) (π : Equiv.Perm (Fin 4 × Fin 2))
    (hπ : π∈fourBlockDerangements) :
    ‖((d:ℂ)^(Fintype.card S))^4*
      (∫ x,productRecordWickIntegrand d id A π x
        ∂fourReadoutLaw (Measure.pi (fun _ : S => haarBasisRecords d)))‖ ≤
      ((d:ℝ)^4*((d:ℝ)-1)^8)^(eightComplementUnion A).card*
        (haarLocalKappa d)^(Fintype.card S-(eightComplementUnion A).card) := by
  rw [productRecordWickIntegral_eq_prod]
  apply finite_site_cost_bound (eightComplementUnion A)
  intro s
  split_ifs with hs
  · exact haarChangedSiteContraction_le d hd _ π
  · rw [eightComplementUnion_outside A s hs]
    exact haarUnchangedSiteContraction_le d π hπ

/-- The identical finite-site product estimate holds for the same six-record Pauli ensemble. -/
theorem pauliProductRecordWickContraction_le
    (A : Fin 4 × Fin 2 → Finset S) (π : Equiv.Perm (Fin 4 × Fin 2))
    (hπ : π∈fourBlockDerangements) :
    ‖((2:ℂ)^(Fintype.card S))^4*
      (∫ x,productRecordWickIntegrand 2 pauliFullRecord A π x
        ∂fourReadoutLaw (Measure.pi (fun _ : S => pauliBasisRecords)))‖ ≤
      (16:ℝ)^(eightComplementUnion A).card*
        pauliLocalKappa^(Fintype.card S-(eightComplementUnion A).card) := by
  have hp := productRecordWickIntegral_eq_prod pauliBasisRecords 2 pauliFullRecord A π
  norm_num only [Nat.cast_ofNat] at hp
  rw [hp]
  apply finite_site_cost_bound (eightComplementUnion A)
  intro s
  split_ifs with hs
  · exact pauliChangedSiteContraction_le _ π
  · rw [eightComplementUnion_outside A s hs]
    exact pauliUnchangedSiteContraction_le π hπ


@[fun_prop] theorem productRecordWickIntegrand_continuous [TopologicalSpace Ω]
    (d : ℕ) (r : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous r)
    (A : Fin 4 × Fin 2 → Finset S) (π : Equiv.Perm (Fin 4 × Fin 2)) :
    Continuous (productRecordWickIntegrand d r A π) := by
  simp_rw [funext (productRecordWickIntegrand_eq_prod d r A π)]
  fun_prop

/-- Compact actual record spaces give genuine absolute integrability of every global contraction. -/
theorem productRecordWickIntegrand_integrable [TopologicalSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] [CompactSpace Ω] [SecondCountableTopology Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ)
    (r : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous r)
    (A : Fin 4 × Fin 2 → Finset S) (π : Equiv.Perm (Fin 4 × Fin 2)) :
    Integrable (productRecordWickIntegrand d r A π)
      (fourReadoutLaw (Measure.pi (fun _ : S => μ))) := by
  let : BorelSpace (S → Ω) := inferInstance
  let : SecondCountableTopology (S → Ω) := inferInstance
  exact (productRecordWickIntegrand_continuous d r hr A π).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [Fintype S] [DecidableEq S] in
/-- Enlarging the allowed support increases the bound when C≥1 and 0≤κ≤1. -/
theorem finite_site_cost_le_uniform (C κ : ℝ) (hC : 1≤C) (hκ0 : 0≤κ) (hκ1 : κ≤1)
    (n t R : ℕ) (ht : t≤R) : C^t*κ^(n-t)≤C^R*κ^(n-R) := by
  apply mul_le_mul (pow_le_pow_right₀ hC ht)
    (pow_le_pow_of_le_one hκ0 hκ1 (Nat.sub_le_sub_left ht n))
  · exact pow_nonneg hκ0 _
  · exact pow_nonneg (by linarith) _

/-- Every actual Haar Wick term has the common eight-complement bound, with no assumed factorization or local estimate. -/
theorem haarProductRecordWickContraction_uniform (d : ℕ) [NeZero d] (hd : 3≤d)
    (r : ℕ) (A : Fin 4 × Fin 2 → Finset S) (hA : ∀ t,(A t).card≤r)
    (π : Equiv.Perm (Fin 4 × Fin 2)) (hπ : π∈fourBlockDerangements) :
    ‖((d:ℂ)^(Fintype.card S))^4*
      (∫ x,productRecordWickIntegrand d id A π x
        ∂fourReadoutLaw (Measure.pi (fun _ : S => haarBasisRecords d)))‖ ≤
      ((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*(haarLocalKappa d)^(Fintype.card S-8*r) := by
  have hd' : (3:ℝ)≤d := by exact_mod_cast hd
  have hC1 : (1:ℝ)≤(d:ℝ)^4 := one_le_pow₀ (by linarith)
  have hC2 : (1:ℝ)≤((d:ℝ)-1)^8 := one_le_pow₀ (by linarith)
  have hC : (1:ℝ)≤(d:ℝ)^4*((d:ℝ)-1)^8 := one_le_mul_of_one_le_of_one_le hC1 hC2
  exact (haarProductRecordWickContraction_le d (by omega) A π hπ).trans
    (finite_site_cost_le_uniform _ _ hC (haarLocalKappa_pos d (by omega)).le
      (haarLocalKappa_lt_one d hd).le _ _ _ (eightComplementUnion_card_le A r hA))

/-- The genuine six-record Pauli product law has the same uniform eight-complement form with C2=16. -/
theorem pauliProductRecordWickContraction_uniform
    (r : ℕ) (A : Fin 4 × Fin 2 → Finset S) (hA : ∀ t,(A t).card≤r)
    (π : Equiv.Perm (Fin 4 × Fin 2)) (hπ : π∈fourBlockDerangements) :
    ‖((2:ℂ)^(Fintype.card S))^4*
      (∫ x,productRecordWickIntegrand 2 pauliFullRecord A π x
        ∂fourReadoutLaw (Measure.pi (fun _ : S => pauliBasisRecords)))‖ ≤
      (16:ℝ)^(8*r)*pauliLocalKappa^(Fintype.card S-8*r) :=
  (pauliProductRecordWickContraction_le A π hπ).trans
    (finite_site_cost_le_uniform _ _ (by norm_num) pauliLocalKappa_pos.le pauliLocalKappa_lt_one.le
      _ _ _ (eightComplementUnion_card_le A r hA))

end CertificationGaussian
