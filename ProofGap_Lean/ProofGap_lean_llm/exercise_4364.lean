import Mathlib

noncomputable section

namespace ProofGraderGenerated

abbrev Point3 := ℝ × ℝ × ℝ
abbrev Point2 := ℝ × ℝ

def diff {α : Type} (_ : α) : ℝ := 0
def DefInt (_ _ : ℝ) (_ : ℝ) : ℝ := 0
def VectorSurfaceInt (_ : Set Point3) (_ : ℝ) : ℝ := 0
def ScalarSurfaceInt (_ : Set Point3) (_ : ℝ) : ℝ := 0
def VectorCurveInt (_ : Set Point3) (_ : ℝ) : ℝ := 0
def VolumeInt (_ : Set Point2) (_ : ℝ) : ℝ := 0
def ScalarSurfaceInt2 (_ : Set Point2) (_ : ℝ) : ℝ := 0
def SurfaceElem (_ : Set Point3) : ℝ := 0
def CurveOn (_ : ℝ → Point3) (_ : Set Point3) : Prop := True
def ContinuousOnInterval (_ : ℝ → ℝ) (_ _ : ℝ) : Prop := True

def frac (x y : ℝ) : ℝ := x / y
def sqrtn (_ : ℕ) (x : ℝ) : ℝ := Real.sqrt x


/- exercise_4364, gaps 1-21. Outward surface integral on cone split into base S1 and side S2. -/
variable (S S1 S2 : Set Point3) (D : Set Point2) (h I I1 I2 alpha beta gamma : ℝ)

def coneSetup4364 : Prop := 0 < h ∧ S = {p : Point3 | p.1^2 + p.2.1^2 = p.2.2^2 ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ h} ∧ S1 = {p : Point3 | p.2.2 = h ∧ p.1^2 + p.2.1^2 ≤ h^2} ∧ S2 = {p : Point3 | p.1^2 + p.2.1^2 = p.2.2^2 ∧ 0 < p.2.2 ∧ p.2.2 ≤ h} ∧ D = {q : Point2 | q.1^2 + q.2^2 ≤ h^2}
def total4364 : Prop := I = VectorSurfaceInt S 0
def baseDef4364 : Prop := I1 = VectorSurfaceInt S1 0
def baseProj4364 : Prop := I1 = VolumeInt D 0
def basePolar4364 : Prop := ∀ phi, 0 ≤ phi ∧ phi ≤ 2*Real.pi → VolumeInt D 0 = DefInt 0 (2*Real.pi) (diff phi) * DefInt 0 h (h^2*(Real.cos phi - Real.sin phi)*diff h)
def baseRadial4364 : Prop := ∀ phi, 0 ≤ phi ∧ phi ≤ 2*Real.pi → DefInt 0 (2*Real.pi) (diff phi) * DefInt 0 h (h^2*(Real.cos phi - Real.sin phi)*diff h) = frac (h^3) 3 * DefInt 0 (2*Real.pi) ((Real.cos phi - Real.sin phi)*diff phi)
def baseZeroExpr4364 : Prop := frac (h^3) 3 * DefInt 0 (2*Real.pi) (diff h) = 0
def sideDef4364 : Prop := I2 = VectorSurfaceInt S2 0
def normalRatio14364 : Prop := ∀ x y, frac (Real.cos alpha) x = frac (Real.cos beta) y
def normalRatio24364 : Prop := ∀ y z, 0 < z ∧ z ≤ h → frac (Real.cos beta) y = frac (Real.cos gamma) (-z)
def gammaProj4364 : Prop := Real.cos gamma * SurfaceElem S = -diff D
def alphaProj4364 : Prop := ∀ x z, 0 < z ∧ z ≤ h → Real.cos alpha * SurfaceElem S = frac x z * diff D
def betaProj4364 : Prop := ∀ y z, 0 < z ∧ z ≤ h → Real.cos beta * SurfaceElem S = frac y z * diff D
def sideNormal4364 : Prop := ∀ x y z, 0 < z ∧ z ≤ h → I2 = ScalarSurfaceInt S2 (((y-z)*Real.cos alpha + (z-x)*Real.cos beta + (x-y)*Real.cos gamma) * SurfaceElem S)
def sideProject4364 : Prop := ∀ z, 0 < z ∧ z ≤ h → I2 = VolumeInt D 0
def sideAlgebra4364 : Prop := ∀ z, 0 < z ∧ z ≤ h → VolumeInt D 0 = -2 * VolumeInt D 0
def sideZeroExpr4364 : Prop := -2 * VolumeInt D 0 = 0

theorem proof_gap_exercise_4364_1 (hs : coneSetup4364 S S1 S2 D h) : total4364 S I := by sorry
theorem proof_gap_exercise_4364_2 (hs : coneSetup4364 S S1 S2 D h) (h1 : total4364 S I) : baseDef4364 S1 I1 := by sorry
theorem proof_gap_exercise_4364_3 (h2 : baseDef4364 S1 I1) : baseProj4364 D I1 := by sorry
theorem proof_gap_exercise_4364_4 (hs : coneSetup4364 S S1 S2 D h) (h3 : baseProj4364 D I1) : basePolar4364 D h := by sorry
theorem proof_gap_exercise_4364_5 (h4 : basePolar4364 D h) : baseRadial4364 h := by sorry
theorem proof_gap_exercise_4364_6 (h5 : baseRadial4364 h) : baseZeroExpr4364 h := by sorry
theorem proof_gap_exercise_4364_7 (h3 : baseProj4364 D I1) (h4 : basePolar4364 D h) (h5 : baseRadial4364 h) (h6 : baseZeroExpr4364 h) : I1 = 0 := by sorry
theorem proof_gap_exercise_4364_8 (hs : coneSetup4364 S S1 S2 D h) : sideDef4364 S2 I2 := by sorry
theorem proof_gap_exercise_4364_9 : normalRatio14364 alpha beta := by sorry
theorem proof_gap_exercise_4364_10 : normalRatio24364 beta gamma h := by sorry
theorem proof_gap_exercise_4364_11 : gammaProj4364 S D gamma := by sorry
theorem proof_gap_exercise_4364_12 : alphaProj4364 S D h alpha := by sorry
theorem proof_gap_exercise_4364_13 : betaProj4364 S D h beta := by sorry
theorem proof_gap_exercise_4364_14 (h8 : sideDef4364 S2 I2) : sideNormal4364 S S2 h I2 alpha beta gamma := by sorry
theorem proof_gap_exercise_4364_15 (h14 : sideNormal4364 S S2 h I2 alpha beta gamma) : sideProject4364 D h I2 := by sorry
theorem proof_gap_exercise_4364_16 (h15 : sideProject4364 D h I2) : sideAlgebra4364 D h := by sorry
theorem proof_gap_exercise_4364_17 (h16 : sideAlgebra4364 D h) : sideZeroExpr4364 D := by sorry
theorem proof_gap_exercise_4364_18 (h15 : sideProject4364 D h I2) (h16 : sideAlgebra4364 D h) (h17 : sideZeroExpr4364 D) : I2 = 0 := by sorry
theorem proof_gap_exercise_4364_19 (h1 : total4364 S I) (h2 : baseDef4364 S1 I1) (h8 : sideDef4364 S2 I2) : I = I1 + I2 := by sorry
theorem proof_gap_exercise_4364_20 (h7 : I1 = 0) (h18 : I2 = 0) : I1 + I2 = 0 := by sorry
theorem proof_gap_exercise_4364_21 (h19 : I = I1 + I2) (h20 : I1 + I2 = 0) : I = 0 := by sorry

end ProofGraderGenerated
