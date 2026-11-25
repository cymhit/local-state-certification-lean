import LocalCertification.Quantum.FixedBlockIndex
import LocalCertification.Quantum.BornMeasure
import LocalCertification.Quantum.HaarProductBasis
import LocalCertification.Quantum.HaarWeylOverlap

set_option autoImplicit false
open Matrix MeasureTheory Metric CertificationGaussian
open scoped BigOperators ENNReal
noncomputable section
namespace LocalCertification.Quantum
variable {k m : ℕ}

/-- One actual orthonormal basis of the physical km-qubit space, a product only across the fixed blocks. -/
def fixedBlockPhysicalBasis (P : FixedBlockPartition k m)
    (U : Fin m → LocalUnitary (2^k)) : ↥(unitary (Matrix (QuditIndex 2 (k*m)) (QuditIndex 2 (k*m)) ℂ)) :=
  unitaryReindex (fixedBlockIndexEquiv P).symm
    ⟨tensorUnitaryMatrix (2^k) m U,tensorUnitaryMatrix_unitary (2^k) m U⟩

/-- The actual matrix factors across precisely the prescribed blocks, with no within-block product restriction. -/
theorem fixedBlockPhysicalBasis_apply (P : FixedBlockPartition k m)
    (U : Fin m → LocalUnitary (2^k)) (a b : QuditIndex 2 (k*m)) :
    (fixedBlockPhysicalBasis P U).val a b=
      ∏ s : Fin m,(U s).val (fixedBlockIndexEquiv P a s) (fixedBlockIndexEquiv P b s) := rfl

/-- Actual full outcome probabilities of that physical basis, with an invertible label for every bit string. -/
def fixedBlockBorn (P : FixedBlockPartition k m) (U : Fin m → LocalUnitary (2^k))
    (ρ : QIT.State (QuditIndex 2 (k*m))) (x : QuditIndex (2^k) m) : ℝ :=
  basisBorn (fixedBlockPhysicalBasis P U) ρ ((fixedBlockIndexEquiv P).symm x)

theorem fixedBlockBorn_eq (P : FixedBlockPartition k m) (U : Fin m → LocalUnitary (2^k))
    (ρ : QIT.State (QuditIndex 2 (k*m))) (x : QuditIndex (2^k) m) :
    fixedBlockBorn P U ρ x=productBorn (2^k) m U (ρ.reindex (fixedBlockIndexEquiv P)) x := by
  have h := basisBorn_reindex (fixedBlockIndexEquiv P) (fixedBlockPhysicalBasis P U) ρ
    ((fixedBlockIndexEquiv P).symm x)
  rw [Equiv.apply_symm_apply] at h
  have he : unitaryReindex (fixedBlockIndexEquiv P) (fixedBlockPhysicalBasis P U)=
      ⟨tensorUnitaryMatrix (2^k) m U,tensorUnitaryMatrix_unitary (2^k) m U⟩ :=
    unitaryReindex_inverse (fixedBlockIndexEquiv P).symm _
  rw [he] at h
  exact h.symm

/-- Genuine physical complete-basis Born measure, transported only by the invertible outcome labeling. -/
def fixedBlockBornMeasure (P : FixedBlockPartition k m) (U : Fin m → LocalUnitary (2^k))
    (ρ : QIT.State (QuditIndex 2 (k*m))) : Measure (QuditIndex (2^k) m) :=
  (povmBornMeasure (basisPOVM (fixedBlockPhysicalBasis P U)) ρ).map (fixedBlockIndexEquiv P)

/-- The full measure, not merely a few moments, equals the original qudit product-measurement law. -/
theorem fixedBlockBornMeasure_eq (P : FixedBlockPartition k m) (U : Fin m → LocalUnitary (2^k))
    (ρ : QIT.State (QuditIndex 2 (k*m))) :
    fixedBlockBornMeasure P U ρ=productBornMeasure (2^k) m U (ρ.reindex (fixedBlockIndexEquiv P)) := by
  apply Measure.ext_of_singleton
  intro x
  rw [fixedBlockBornMeasure,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton x)]
  have he : (fixedBlockIndexEquiv P) ⁻¹' {x} = {(fixedBlockIndexEquiv P).symm x} := by
    ext y
    exact ((fixedBlockIndexEquiv P).eq_symm_apply).symm
  rw [he]
  simp only [productBornMeasure,povmBornMeasure_atom]
  apply congrArg (fun t : NNReal => (t : ℝ≥0∞))
  apply NNReal.eq
  exact fixedBlockBorn_eq P U ρ x

/-- Every arbitrary basis inside a block is covered by the complete Fin(2^k) unitary label space. -/
theorem fixedBlock_local_basis_surjective (k : ℕ)
    (V : ↥(unitary (Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ))) :
    ∃ U : LocalUnitary (2^k),unitaryReindex (blockLabelEquiv k).symm U=V :=
  ⟨unitaryReindex (blockLabelEquiv k) V,unitaryReindex_inverse (blockLabelEquiv k) V⟩

/-- The fixed physical identification is a real Hilbert-space isometry. -/
def fixedBlockIsometry (P : FixedBlockPartition k m) :
    EuclideanSpace ℂ (QuditIndex 2 (k*m)) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (QuditIndex (2^k) m) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℂ (fixedBlockIndexEquiv P)

/-- The same coordinate identification restricts to actual canonical unit spheres. -/
def fixedBlockSphere (P : FixedBlockPartition k m) := sphereIsometry (fixedBlockIsometry P)

/-- Canonical Haar sphere probability is preserved by the specified physical partition. -/
theorem fixedBlockSphere_measure (P : FixedBlockPartition k m) :
    (canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*m)))).map (fixedBlockSphere P)=
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex (2^k) m)) :=
  sphereIsometry_canonical_map (fixedBlockIsometry P)

/-- The QIT pure-vector representation uses exactly the same isometry as the Haar transfer. -/
theorem fixedBlockSphere_pure (P : FixedBlockPartition k m)
    (ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 (k*m))) 1) :
    spherePureVector (fixedBlockSphere P ψ)=(spherePureVector ψ).reindex (fixedBlockIndexEquiv P) := by
  rfl

end LocalCertification.Quantum
