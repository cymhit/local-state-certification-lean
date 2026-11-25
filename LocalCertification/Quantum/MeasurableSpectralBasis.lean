import LocalCertification.Quantum.OrderedEigenprojector
import LocalCertification.Quantum.MeasurableEigenbasisSlots
import QIT.Core.Pure

/-! A measurable orthonormal eigenbasis determined by spectral projections
and fixed-order Gram–Schmidt. The ordinary eigenbasis in the spectral
theorem is used only to verify the projected subspaces pointwise. -/

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory InnerProductSpace Module Set
open scoped ComplexOrder
namespace LocalCertification.Quantum
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
local notation "E" => EuclideanSpace ℂ I
local notation "D" => Fintype.card I
local notation "Slots" => Fin (D * D)

private theorem project_basis {A : Matrix I I ℂ} (hA : A.IsHermitian) (i : Fin D) (j : I) :
    toEuclideanLin (orderedEigenprojector hA i) (hA.eigenvectorBasis j) =
      if hA.eigenvalues j = hA.eigenvalues₀ i then hA.eigenvectorBasis j else 0 := by
  have he := orderedEigenprojector_mulVec hA i j
  split_ifs at he ⊢ with h
  · exact PiLp.ext (fun k => congrFun he k)
  · exact PiLp.ext (fun k => congrFun he k)

/-- Projected coordinate vectors, listed first by spectral slot and then by coordinate. -/
def projectedCoordinates {A : Matrix I I ℂ} (hA : A.IsHermitian) (k : Slots) : E :=
  let p : Fin D × Fin D := finProdFinEquiv.symm k
  toEuclideanLin (orderedEigenprojector hA p.1)
    (EuclideanSpace.basisFun I ℂ ((Fintype.equivFin I).symm p.2))

private theorem projectedCoordinates_apply {A : Matrix I I ℂ} (hA : A.IsHermitian) (i : Fin D) (j : I) :
    projectedCoordinates hA (finProdFinEquiv (i,Fintype.equivFin I j)) =
      toEuclideanLin (orderedEigenprojector hA i) (EuclideanSpace.basisFun I ℂ j) := by
  simp [projectedCoordinates]

theorem measurable_projectedCoordinates (A : Ω → Matrix I I ℂ) (hA : Measurable A)
    (hh : ∀ s, (A s).IsHermitian) (k : Slots) :
    Measurable (fun s => projectedCoordinates (hh s) k) := by
  let p : Fin D × Fin D := finProdFinEquiv.symm k
  have hP := measurable_orderedEigenprojector A hA hh p.1
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply Measurable.of_eval
  intro i
  change Measurable (fun s => ((orderedEigenprojector (hh s) p.1) *ᵥ
    ⇑(EuclideanSpace.basisFun I ℂ ((Fintype.equivFin I).symm p.2))) i)
  simp only [mulVec, dotProduct]
  apply Finset.measurable_sum
  intro j _
  exact hP.eval_matrix.mul measurable_const

theorem projectedCoordinates_span {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    Submodule.span ℂ (range (projectedCoordinates hA)) = ⊤ := by
  let V := Submodule.span ℂ (range (projectedCoordinates hA))
  have hproj (i : Fin D) (v : E) : toEuclideanLin (orderedEigenprojector hA i) v ∈ V := by
    let B := (EuclideanSpace.basisFun I ℂ).toBasis
    nth_rw 1 [← B.sum_repr v]
    simp only [map_sum, map_smul]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨finProdFinEquiv (i,Fintype.equivFin I j),
      projectedCoordinates_apply hA i j⟩
  apply top_unique
  rw [← hA.eigenvectorBasis.toBasis.span_eq]
  apply Submodule.span_le.mpr
  rintro v ⟨j, rfl⟩
  let i := (Fintype.equivOfCardEq (Fintype.card_fin D)).symm j
  have hx := hproj i (hA.eigenvectorBasis j)
  rw [project_basis hA i j, ite_eq_left (show hA.eigenvalues j = hA.eigenvalues₀ i from rfl)] at hx
  exact hx

private theorem spectralProjector_range {A : Matrix I I ℂ} (hA : A.IsHermitian) (i : Fin D) (v : E) :
    toEuclideanLin (orderedEigenprojector hA i) v ∈ End.eigenspace (toEuclideanLin A) (hA.eigenvalues₀ i : ℂ) := by
  let B := hA.eigenvectorBasis.toBasis
  nth_rw 1 [← B.sum_repr v]
  simp only [map_sum, map_smul]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  change toEuclideanLin (orderedEigenprojector hA i) (hA.eigenvectorBasis j) ∈ _
  rw [project_basis]
  split_ifs with h
  · rw [End.mem_eigenspace_iff, ← h]
    have he : A *ᵥ ⇑(hA.eigenvectorBasis j) =
        (hA.eigenvalues j : ℂ) • ⇑(hA.eigenvectorBasis j) := by
      ext k
      simpa only [Pi.smul_apply, Complex.real_smul, smul_eq_mul] using
        congrFun (hA.mulVec_eigenvectorBasis j) k
    exact PiLp.ext (fun k => congrFun he k)
  · exact Submodule.zero_mem _

/-- The selected eigenbasis. Repeated eigenvalues and zero eigenvalues are included. -/
def measurableSpectralBasis {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    OrthonormalBasis (Fin D) ℂ E :=
  selectedGramSchmidtBasis (projectedCoordinates hA) (projectedCoordinates_span hA)

/-- The ordered spectral value at the block of a retained residual. -/
def selectedEigenvalue {A : Matrix I I ℂ} (hA : A.IsHermitian) (i : Fin D) : ℝ :=
  let k := activeGramSchmidtSlot (projectedCoordinates hA) (projectedCoordinates_span hA) i
  hA.eigenvalues₀ (finProdFinEquiv.symm k).1

/-- Removing zero residuals preserves the original nonincreasing spectral order. -/
theorem selectedEigenvalue_antitone {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    Antitone (selectedEigenvalue hA) := by
  intro i j hij
  apply hA.eigenvalues₀_antitone
  let v := projectedCoordinates hA
  let hs := projectedCoordinates_span hA
  have hslots : (activeGramSchmidtSlot v hs i).val ≤ (activeGramSchmidtSlot v hs j).val :=
    (activeGramSchmidtEquiv v hs).monotone hij
  exact Nat.div_le_div_right hslots

theorem measurable_spectralBasis (A : Ω → Matrix I I ℂ) (hA : Measurable A)
    (hh : ∀ s, (A s).IsHermitian) (i : Fin D) :
    Measurable (fun s => measurableSpectralBasis (hh s) i) :=
  measurable_selectedGramSchmidtBasis _ (measurable_projectedCoordinates A hA hh)
    (fun s => projectedCoordinates_span (hh s)) i

theorem measurable_selectedEigenvalue (A : Ω → Matrix I I ℂ) (hA : Measurable A)
    (hh : ∀ s, (A s).IsHermitian) (i : Fin D) :
    Measurable (fun s => selectedEigenvalue (hh s) i) := by
  let D' := Fintype.card I
  let block (k : Fin (D' * D')) : Fin D' := (finProdFinEquiv.symm k).1
  have hslot := measurable_activeGramSchmidtSlot _ (measurable_projectedCoordinates A hA hh)
    (fun s => projectedCoordinates_span (hh s)) i
  have hspec := measurable_ordered_eigenvalues A hA hh
  exact measurable_at_slot (fun s k => (hh s).eigenvalues₀ (block k))
    (fun k => (measurable_pi_apply (block k)).comp hspec) _ hslot

theorem spectralBasis_eigenvector {A : Matrix I I ℂ} (hA : A.IsHermitian) (i : Fin D) :
    toEuclideanLin A (measurableSpectralBasis hA i) =
      (selectedEigenvalue hA i : ℂ) • measurableSpectralBasis hA i := by
  let mu (k : Slots) : ℂ := (hA.eigenvalues₀ (finProdFinEquiv.symm k).1 : ℝ)
  let slot := activeGramSchmidtSlot (projectedCoordinates hA) (projectedCoordinates_span hA) i
  have he := gramSchmidtNormed_mem_eigenspace (toEuclideanLin A) (isSymmetric_toEuclideanLin_iff.mpr hA)
    mu (projectedCoordinates hA) (fun k => spectralProjector_range hA _ _) slot
  simp only [measurableSpectralBasis, selectedGramSchmidtBasis_apply]
  simpa only [mu, slot, selectedEigenvalue] using End.mem_eigenspace_iff.mp he

theorem selectedEigenvalue_nonneg {A : Matrix I I ℂ} (hA : A.PosSemidef) (i : Fin D) :
    0 ≤ selectedEigenvalue hA.isHermitian i := by
  let slot := activeGramSchmidtSlot (projectedCoordinates hA.isHermitian)
    (projectedCoordinates_span hA.isHermitian) i
  let k : Fin D := (finProdFinEquiv.symm slot).1
  let e : Fin D ≃ I := Fintype.equivOfCardEq (Fintype.card_fin D)
  change 0 ≤ hA.isHermitian.eigenvalues₀ k
  have hp := hA.eigenvalues_nonneg (e k)
  change 0 ≤ hA.isHermitian.eigenvalues₀ (e.symm (e k)) at hp
  simpa only [Equiv.symm_apply_apply] using hp

private theorem rankOne_action (v w : E) :
    toEuclideanLin (QIT.rankOneMatrix (fun i => v i)) w = inner ℂ v w • v := by
  change toEuclideanLin (Matrix.vecMulVec v (star ⇑v)) w = _
  rw [← InnerProductSpace.symm_toEuclideanLin_rankOne, LinearEquiv.apply_symm_apply]
  rfl

/-- Pointwise spectral reconstruction on the original index space. -/
theorem sum_selectedEigenvalue_rankOne {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    ∑ i, selectedEigenvalue hA i • QIT.rankOneMatrix (fun j => measurableSpectralBasis hA i j) = A := by
  let B := measurableSpectralBasis hA
  apply toEuclideanLin.injective
  apply B.toBasis.ext
  intro k
  have hconv (i : Fin D) : selectedEigenvalue hA i • QIT.rankOneMatrix (fun j => B i j) =
      (selectedEigenvalue hA i : ℂ) • QIT.rankOneMatrix (fun j => B i j) :=
    RCLike.real_smul_eq_coe_smul (K := ℂ) _ _
  change toEuclideanLin (∑ i, selectedEigenvalue hA i • QIT.rankOneMatrix (fun j => B i j)) (B k) =
    toEuclideanLin A (B k)
  simp only [hconv, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, rankOne_action]
  rw [spectralBasis_eigenvector hA]
  rw [Finset.sum_eq_single k]
  · simp only [orthonormal_iff_ite.mp B.orthonormal, ite_true, one_smul]
    rfl
  · intro i _ hik
    simp only [orthonormal_iff_ite.mp B.orthonormal, ite_eq_right hik, zero_smul, smul_zero]
  · simp

end LocalCertification.Quantum

