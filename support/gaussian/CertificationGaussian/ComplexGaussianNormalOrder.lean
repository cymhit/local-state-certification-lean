import CertificationGaussian.ComplexGaussianWick

noncomputable section
open MeasureTheory MvPolynomial Finset
open scoped BigOperators
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Creation of a conjugated coordinate, including its exact Gaussian contraction correction. -/
def gaussianBarCreation (i : I) (P : MvPolynomial (Fin 2 × I) ℂ) :=
  gaussianBarZPolynomial i * P - wirtingerZ i P

/-- Creation of an unconjugated coordinate. -/
def gaussianZCreation (i : I) (P : MvPolynomial (Fin 2 × I) ℂ) :=
  gaussianZPolynomial i * P - wirtingerBar i P

/-- Creation is adjoint to the actual Wirtinger derivative under Gaussian expectation. -/
theorem gaussianBarCreation_adjoint (i : I) (P Q : MvPolynomial (Fin 2 × I) ℂ) :
    complexGaussianPolyExpectation (gaussianBarCreation i P * Q) =
      complexGaussianPolyExpectation (P * wirtingerZ i Q) := by
  rw [gaussianBarCreation, sub_mul, complexGaussianPolyExpectation_sub,
    mul_assoc, complexGaussianPolyExpectation_barz_ibp, wirtingerZ_mul,
    complexGaussianPolyExpectation_add]
  ring

theorem gaussianZCreation_adjoint (i : I) (P Q : MvPolynomial (Fin 2 × I) ℂ) :
    complexGaussianPolyExpectation (gaussianZCreation i P * Q) =
      complexGaussianPolyExpectation (P * wirtingerBar i Q) := by
  rw [gaussianZCreation, sub_mul, complexGaussianPolyExpectation_sub,
    mul_assoc, complexGaussianPolyExpectation_z_ibp, wirtingerBar_mul,
    complexGaussianPolyExpectation_add]
  ring

/-- A block of two bar and two unbar positions. Coordinates may coincide. -/
def gaussianNormalQuartic (a b c d : I) : MvPolynomial (Fin 2 × I) ℂ :=
  gaussianBarCreation a (gaussianBarCreation b (gaussianZCreation c (gaussianZCreation d 1)))

/-- A normal block acts by four actual derivatives on the other factor. -/
theorem gaussianNormalQuartic_adjoint (a b c d : I) (P : MvPolynomial (Fin 2 × I) ℂ) :
    complexGaussianPolyExpectation (gaussianNormalQuartic a b c d * P) =
      complexGaussianPolyExpectation
        (wirtingerBar d (wirtingerBar c (wirtingerZ b (wirtingerZ a P)))) := by
  rw [gaussianNormalQuartic, gaussianBarCreation_adjoint, gaussianBarCreation_adjoint,
    gaussianZCreation_adjoint, gaussianZCreation_adjoint, one_mul]

omit [Fintype I] [DecidableEq I] in
theorem wirtingerZ_sub (i : I) (P Q : MvPolynomial (Fin 2 × I) ℂ) :
    wirtingerZ i (P-Q) = wirtingerZ i P - wirtingerZ i Q := by
  simp only [wirtingerZ, map_sub]
  ring

omit [Fintype I] [DecidableEq I] in
theorem wirtingerBar_sub (i : I) (P Q : MvPolynomial (Fin 2 × I) ℂ) :
    wirtingerBar i (P-Q) = wirtingerBar i P - wirtingerBar i Q := by
  simp only [wirtingerBar, map_sub]
  ring

/-- Kronecker delta as a constant polynomial, keeping repeated positions distinct. -/
def gaussianDeltaPolynomial (i j : I) : MvPolynomial (Fin 2 × I) ℂ :=
  C (if i=j then 1 else 0)

omit [Fintype I] in
/-- The seven-term normal-order formula: four single contractions and two double contractions. -/
theorem gaussianNormalQuartic_expansion (a b c d : I) :
    gaussianNormalQuartic a b c d =
      gaussianBarZPolynomial a * gaussianBarZPolynomial b * gaussianZPolynomial c * gaussianZPolynomial d
      - gaussianDeltaPolynomial a c * gaussianBarZPolynomial b * gaussianZPolynomial d
      - gaussianDeltaPolynomial a d * gaussianBarZPolynomial b * gaussianZPolynomial c
      - gaussianDeltaPolynomial b c * gaussianBarZPolynomial a * gaussianZPolynomial d
      - gaussianDeltaPolynomial b d * gaussianBarZPolynomial a * gaussianZPolynomial c
      + gaussianDeltaPolynomial a c * gaussianDeltaPolynomial b d
      + gaussianDeltaPolynomial a d * gaussianDeltaPolynomial b c := by
  have hb1 (i : I) : wirtingerBar i (1 : MvPolynomial (Fin 2 × I) ℂ)=0 := by
    simpa only [map_one] using wirtingerBar_C i 1
  have hd (i j k : I) : wirtingerZ i (gaussianDeltaPolynomial j k)=0 := wirtingerZ_C _ _
  have hz (i j : I) : wirtingerZ i (gaussianZPolynomial j)=gaussianDeltaPolynomial i j := by
    rw [wirtingerZ_z]
    by_cases h : i=j <;> simp [gaussianDeltaPolynomial,h]
  simp only [gaussianNormalQuartic, gaussianZCreation, gaussianBarCreation, hb1,
    mul_one, sub_zero, wirtingerBar_z, zero_mul, mul_zero, add_zero,
    wirtingerZ_sub, wirtingerZ_add, wirtingerZ_mul, wirtingerZ_barz, hz, hd]
  ring

/-- Normal ordering removes the mean under the actual probability law. -/
theorem gaussianNormalQuartic_mean_zero (a b c d : I) :
    complexGaussianPolyExpectation (gaussianNormalQuartic a b c d) = 0 := by
  have h := gaussianNormalQuartic_adjoint a b c d 1
  simpa [wirtingerZ, wirtingerBar, complexGaussianPolyExpectation_zero] using h

/-- One actual squared-modulus coordinate, represented as a complex polynomial in real coordinates. -/
def gaussianRadialMonomial (i : I) : MvPolynomial (Fin 2 × I) ℂ :=
  gaussianBarZPolynomial i * gaussianZPolynomial i

/-- All radial powers have the factorial moments derived from actual Wick contractions. -/
theorem gaussianRadialMonomial_moment (i : I) (n : ℕ) :
    complexGaussianPolyExpectation (gaussianRadialMonomial i ^ n) = (n.factorial : ℂ) := by
  simpa [gaussianBalancedMonomial, gaussianMixedMonomial, complexGaussianPairingSum,
    gaussianRadialMonomial, mul_pow, Fintype.card_perm] using
    complexGaussian_balanced_wick n (fun _ => i) (fun _ => i)

omit [Fintype I] in
/-- Coincident labels retain all four single and both double contractions. -/
theorem gaussianNormalQuartic_same (i : I) :
    gaussianNormalQuartic i i i i =
      gaussianRadialMonomial i ^ 2 - C 4 * gaussianRadialMonomial i + C 2 := by
  rw [gaussianNormalQuartic_expansion]
  simp [gaussianDeltaPolynomial, gaussianRadialMonomial]
  simp only [map_ofNat]
  ring

/-- The scalar normal block's fourth moment; multiplicities are inherited from n! through order eight. -/
theorem gaussianNormalQuartic_same_fourth (i : I) :
    complexGaussianPolyExpectation (gaussianNormalQuartic i i i i ^ 4) = 4752 := by
  rw [gaussianNormalQuartic_same]
  have he (S : MvPolynomial (Fin 2 × I) ℂ) :
      (S^2-C 4*S+C 2)^4 =
        S^8 - C 16*S^7 + C 104*S^6 - C 352*S^5 + C 664*S^4 -
        C 704*S^3 + C 416*S^2 - C 128*S + C 16 := by
    simp only [map_ofNat]
    ring
  rw [he]
  simp only [complexGaussianPolyExpectation_add, complexGaussianPolyExpectation_sub,
    complexGaussianPolyExpectation_C_mul, complexGaussianPolyExpectation_C,
    gaussianRadialMonomial_moment]
  have h1 := gaussianRadialMonomial_moment i 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at h1
  rw [h1]
  norm_num [Nat.factorial]

omit [Fintype I] in
/-- The true scalar complex Gaussian variable, with its exact seven-term normal ordering. -/
theorem gaussianNormalQuartic_same_eval (i : I) (x : Fin 2 × I → ℝ) :
    complexCoordinatePolyEval (gaussianNormalQuartic i i i i) x =
      (star (complexCoordinate x i)*complexCoordinate x i)^2 -
        4*(star (complexCoordinate x i)*complexCoordinate x i) + 2 := by
  rw [gaussianNormalQuartic_same]
  simp only [complexCoordinatePolyEval, map_add, map_sub, map_mul, map_pow, eval_C,
    gaussianRadialMonomial,
    show eval (fun c => (x c:ℂ)) (gaussianZPolynomial i) = complexCoordinate x i from
      complexCoordinatePolyEval_z i x,
    show eval (fun c => (x c:ℂ)) (gaussianBarZPolynomial i) = star (complexCoordinate x i) from
      complexCoordinatePolyEval_barz i x]

/-- Actual expectation, not a formal coefficient count, of the scalar block's fourth power. -/
theorem complexGaussian_normal_scalar_fourth (i : I) :
    (∫ x, ((star (complexCoordinate x i)*complexCoordinate x i)^2 -
      4*(star (complexCoordinate x i)*complexCoordinate x i) + 2)^4 ∂pairedGaussian I) = (4752:ℂ) := by
  have h := gaussianNormalQuartic_same_fourth i
  unfold complexGaussianPolyExpectation at h
  simpa only [complexCoordinatePolyEval, map_pow,
    show ∀ x, eval (fun c => (x c:ℂ)) (gaussianNormalQuartic i i i i) =
      (star (complexCoordinate x i)*complexCoordinate x i)^2 -
        4*(star (complexCoordinate x i)*complexCoordinate x i) + 2 from
      fun x => gaussianNormalQuartic_same_eval i x] using h

end CertificationGaussian
