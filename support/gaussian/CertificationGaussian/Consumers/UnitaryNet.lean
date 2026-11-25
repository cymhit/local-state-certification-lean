import CertificationGaussian.TensorUnitaryNet

noncomputable section
open scoped BigOperators
namespace CertificationGaussian.Consumers

/-- Every product basis is covered by a finite family of genuine unitary matrices on the actual qudit space. -/
theorem actual_product_unitary_net {d : Nat} (hd : 2 ≤ d) (n : Nat) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset (Matrix (QuditIndex d n) (QuditIndex d n) ℂ),
      (∀ W ∈ S, W ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ)) ∧
      (S.card:ℝ) ≤ (2+4*d/ε)^(2*d^2*n) ∧
      ∀ U : Fin n → LocalUnitary d, ∃ W ∈ S,
        ‖Matrix.toEuclideanCLM (n := QuditIndex d n) (𝕜 := ℂ)
          (tensorUnitaryMatrix d n U-W)‖ ≤ n*(d:ℝ)^n*ε := by
  have hd1 : 1 ≤ d := by omega
  refine ⟨productUnitaryMatrixNet d n hd1 ε hε, ?_, productUnitaryMatrixNet_card hd1 hε, ?_⟩
  · exact fun _ hW => productUnitaryMatrixNet_unitary hd1 hε hW
  · exact productUnitaryMatrixNet_covers hd1 hε

/-- Empty tensor products have the identity action on the single complex coordinate, even at d=0. -/
theorem zero_qudits_tensor_identity (d : Nat) (U : Fin 0 → LocalUnitary d) :
    tensorUnitaryMatrix d 0 U = 1 := by
  ext x y
  simp [tensorUnitaryMatrix, Matrix.one_apply, Subsingleton.elim x y]

/-- With no sites the actual product matrix net has one element. -/
theorem zero_qudits_net_card {d : Nat} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    (productUnitaryMatrixNet d 0 hd ε hε).card = 1 := by
  have hle : ((productUnitaryMatrixNet d 0 hd ε hε).card:ℝ) ≤ 1 := by
    simpa using productUnitaryMatrixNet_card (n := 0) hd hε
  have hleNat : (productUnitaryMatrixNet d 0 hd ε hε).card ≤ 1 := by exact_mod_cast hle
  obtain ⟨W, hW, _⟩ := productUnitaryMatrixNet_covers (n := 0) hd hε Fin.elim0
  have hpos := Finset.card_pos.mpr ⟨W, hW⟩
  omega

end CertificationGaussian.Consumers
