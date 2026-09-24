import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3665

noncomputable section

open scoped Matrix

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ
  deriving DecidableEq

def objective (a b c : ℝ) (q : Point3) : ℝ :=
  q.x ^ 2 / a ^ 2 + q.y ^ 2 / b ^ 2 + q.z ^ 2 / c ^ 2

def constraint (alpha beta gamma : ℝ) : Set Point3 :=
  {q | q.x ^ 2 + q.y ^ 2 + q.z ^ 2 = 1 ∧
    q.x * Real.cos alpha + q.y * Real.cos beta +
      q.z * Real.cos gamma = 0}

def critical (a b c alpha beta gamma : ℝ)
    (q : Point3) (lambda mu : ℝ) : Prop :=
  2 * (1 / a ^ 2 - lambda) * q.x + mu * Real.cos alpha = 0 ∧
    2 * (1 / b ^ 2 - lambda) * q.y + mu * Real.cos beta = 0 ∧
    2 * (1 / c ^ 2 - lambda) * q.z + mu * Real.cos gamma = 0 ∧
    q ∈ constraint alpha beta gamma

def traceCoefficient (a b c alpha beta gamma : ℝ) : ℝ :=
  Real.sin alpha ^ 2 / a ^ 2 +
    Real.sin beta ^ 2 / b ^ 2 +
    Real.sin gamma ^ 2 / c ^ 2

def determinantCoefficient (a b c alpha beta gamma : ℝ) : ℝ :=
  Real.cos alpha ^ 2 / (b ^ 2 * c ^ 2) +
    Real.cos beta ^ 2 / (c ^ 2 * a ^ 2) +
    Real.cos gamma ^ 2 / (a ^ 2 * b ^ 2)

def eigenPolynomial (a b c alpha beta gamma lambda : ℝ) : ℝ :=
  lambda ^ 2 - traceCoefficient a b c alpha beta gamma * lambda +
    determinantCoefficient a b c alpha beta gamma

def spectralDiscriminant (a b c alpha beta gamma : ℝ) : ℝ :=
  traceCoefficient a b c alpha beta gamma ^ 2 -
    4 * determinantCoefficient a b c alpha beta gamma

def lowEigenvalue (a b c alpha beta gamma : ℝ) : ℝ :=
  (traceCoefficient a b c alpha beta gamma -
    Real.sqrt (spectralDiscriminant a b c alpha beta gamma)) / 2

def highEigenvalue (a b c alpha beta gamma : ℝ) : ℝ :=
  (traceCoefficient a b c alpha beta gamma +
    Real.sqrt (spectralDiscriminant a b c alpha beta gamma)) / 2

def minimizers (a b c alpha beta gamma : ℝ) : Set Point3 :=
  {q | q ∈ constraint alpha beta gamma ∧
    ∀ r ∈ constraint alpha beta gamma,
      objective a b c q ≤ objective a b c r}

def maximizers (a b c alpha beta gamma : ℝ) : Set Point3 :=
  {q | q ∈ constraint alpha beta gamma ∧
    ∀ r ∈ constraint alpha beta gamma,
      objective a b c r ≤ objective a b c q}

theorem gap1 (a b c alpha beta gamma : ℝ)
    (q : Point3) (lambda mu : ℝ)
    (hcrit : critical a b c alpha beta gamma q lambda mu) :
    lambda = objective a b c q := by
  rcases hcrit with ⟨hx, hy, hz, hunit, hplane⟩
  have hx' := congrArg (fun t : ℝ => t * q.x) hx
  have hy' := congrArg (fun t : ℝ => t * q.y) hy
  have hz' := congrArg (fun t : ℝ => t * q.z) hz
  have hplane' := congrArg (fun t : ℝ => mu * t) hplane
  have hunit' := congrArg (fun t : ℝ => lambda * t) hunit
  simp only [one_div, zero_mul, mul_zero] at hx' hy' hz' hplane' hunit'
  unfold objective
  simp only [div_eq_mul_inv]
  nlinarith

theorem gap2 (a b c alpha beta gamma : ℝ)
    (q : Point3) (lambda mu : ℝ)
    (hunit : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1)
    (hcrit : critical a b c alpha beta gamma q lambda mu) :
    mu = -2 * (q.x * Real.cos alpha / a ^ 2 +
      q.y * Real.cos beta / b ^ 2 +
      q.z * Real.cos gamma / c ^ 2) := by
  rcases hcrit with ⟨hx, hy, hz, hqUnit, hplane⟩
  have hx' := congrArg (fun t : ℝ => t * Real.cos alpha) hx
  have hy' := congrArg (fun t : ℝ => t * Real.cos beta) hy
  have hz' := congrArg (fun t : ℝ => t * Real.cos gamma) hz
  have hplane' := congrArg (fun t : ℝ => lambda * t) hplane
  have hunit' := congrArg (fun t : ℝ => mu * t) hunit
  simp only [one_div, zero_mul, mul_zero] at hx' hy' hz' hplane' hunit'
  simp only [div_eq_mul_inv]
  nlinarith

private def companion (alpha beta gamma : ℝ) (q : Point3) : Point3 :=
  ⟨Real.cos beta * q.z - Real.cos gamma * q.y,
    Real.cos gamma * q.x - Real.cos alpha * q.z,
    Real.cos alpha * q.y - Real.cos beta * q.x⟩

private def mixedObjective (a b c : ℝ) (q r : Point3) : ℝ :=
  q.x * r.x / a ^ 2 + q.y * r.y / b ^ 2 +
    q.z * r.z / c ^ 2

private def pointVec (q : Point3) : Fin 3 → ℝ :=
  ![q.x, q.y, q.z]

private def normalVec (alpha beta gamma : ℝ) : Fin 3 → ℝ :=
  ![Real.cos alpha, Real.cos beta, Real.cos gamma]

private theorem companion_vec (alpha beta gamma : ℝ) (q : Point3) :
    pointVec (companion alpha beta gamma q) =
      normalVec alpha beta gamma ⨯₃ pointVec q := by
  rfl

private theorem companion_coordinate_squares
    (alpha beta gamma : ℝ) (q : Point3)
    (hnormal : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1)
    (hunit : q.x ^ 2 + q.y ^ 2 + q.z ^ 2 = 1)
    (hplane : q.x * Real.cos alpha + q.y * Real.cos beta +
      q.z * Real.cos gamma = 0) :
    q.x ^ 2 + (companion alpha beta gamma q).x ^ 2 =
        Real.sin alpha ^ 2 ∧
      q.y ^ 2 + (companion alpha beta gamma q).y ^ 2 =
        Real.sin beta ^ 2 ∧
      q.z ^ 2 + (companion alpha beta gamma q).z ^ 2 =
        Real.sin gamma ^ 2 := by
  have htrigA := Real.sin_sq_add_cos_sq alpha
  have htrigB := Real.sin_sq_add_cos_sq beta
  have htrigC := Real.sin_sq_add_cos_sq gamma
  have hrestX :
      Real.cos beta * q.y + Real.cos gamma * q.z =
        -Real.cos alpha * q.x := by
    linarith
  have hrestY :
      Real.cos gamma * q.z + Real.cos alpha * q.x =
        -Real.cos beta * q.y := by
    linarith
  have hrestZ :
      Real.cos alpha * q.x + Real.cos beta * q.y =
        -Real.cos gamma * q.z := by
    linarith
  have hsqX := congrArg (fun t : ℝ => t ^ 2) hrestX
  have hsqY := congrArg (fun t : ℝ => t ^ 2) hrestY
  have hsqZ := congrArg (fun t : ℝ => t ^ 2) hrestZ
  have hcrossX :
      (Real.cos beta ^ 2 + Real.cos gamma ^ 2) *
          (q.y ^ 2 + q.z ^ 2) -
        (Real.cos beta * q.z - Real.cos gamma * q.y) ^ 2 =
      (Real.cos beta * q.y + Real.cos gamma * q.z) ^ 2 := by
    ring
  have hcrossY :
      (Real.cos gamma ^ 2 + Real.cos alpha ^ 2) *
          (q.z ^ 2 + q.x ^ 2) -
        (Real.cos gamma * q.x - Real.cos alpha * q.z) ^ 2 =
      (Real.cos gamma * q.z + Real.cos alpha * q.x) ^ 2 := by
    ring
  have hcrossZ :
      (Real.cos alpha ^ 2 + Real.cos beta ^ 2) *
          (q.x ^ 2 + q.y ^ 2) -
        (Real.cos alpha * q.y - Real.cos beta * q.x) ^ 2 =
      (Real.cos alpha * q.x + Real.cos beta * q.y) ^ 2 := by
    ring
  unfold companion
  simp only
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem companion_objective_sum
    (a b c alpha beta gamma : ℝ) (q : Point3)
    (hnormal : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1)
    (hq : q ∈ constraint alpha beta gamma) :
    objective a b c q +
        objective a b c (companion alpha beta gamma q) =
      traceCoefficient a b c alpha beta gamma := by
  rcases hq with ⟨hunit, hplane⟩
  rcases companion_coordinate_squares alpha beta gamma q
      hnormal hunit hplane with ⟨hx, hy, hz⟩
  calc
    objective a b c q +
          objective a b c (companion alpha beta gamma q) =
        (q.x ^ 2 + (companion alpha beta gamma q).x ^ 2) /
            a ^ 2 +
          (q.y ^ 2 + (companion alpha beta gamma q).y ^ 2) /
            b ^ 2 +
          (q.z ^ 2 + (companion alpha beta gamma q).z ^ 2) /
            c ^ 2 := by
      unfold objective
      ring
    _ = traceCoefficient a b c alpha beta gamma := by
      rw [hx, hy, hz]
      rfl

private theorem companion_dot_self (alpha beta gamma : ℝ) (q : Point3) :
    q.x * (companion alpha beta gamma q).x +
      q.y * (companion alpha beta gamma q).y +
      q.z * (companion alpha beta gamma q).z = 0 := by
  unfold companion
  simp only
  ring

private theorem companion_dot_normal (alpha beta gamma : ℝ) (q : Point3) :
    Real.cos alpha * (companion alpha beta gamma q).x +
      Real.cos beta * (companion alpha beta gamma q).y +
      Real.cos gamma * (companion alpha beta gamma q).z = 0 := by
  unfold companion
  simp only
  ring

private theorem point_decomposition
    (alpha beta gamma : ℝ) (p q : Point3)
    (hnormal : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1)
    (hp : p ∈ constraint alpha beta gamma)
    (hq : q ∈ constraint alpha beta gamma) :
    let r := companion alpha beta gamma p
    let s := q.x * p.x + q.y * p.y + q.z * p.z
    let t := q.x * r.x + q.y * r.y + q.z * r.z
    q.x = s * p.x + t * r.x ∧
      q.y = s * p.y + t * r.y ∧
      q.z = s * p.z + t * r.z := by
  let n := normalVec alpha beta gamma
  let pv := pointVec p
  let qv := pointVec q
  let rv := pointVec (companion alpha beta gamma p)
  let s : ℝ := qv ⬝ᵥ pv
  let t : ℝ := qv ⬝ᵥ rv
  have hn : n ⬝ᵥ n = 1 := by
    dsimp [n, normalVec]
    rw [Matrix.vec3_dotProduct]
    simpa [pow_two] using hnormal
  have hpNorm : pv ⬝ᵥ pv = 1 := by
    rcases hp with ⟨hpUnit, hpPlane⟩
    dsimp [pv, pointVec]
    rw [Matrix.vec3_dotProduct]
    simpa [pow_two] using hpUnit
  have hnp : n ⬝ᵥ pv = 0 := by
    rcases hp with ⟨hpUnit, hpPlane⟩
    dsimp [n, pv, normalVec, pointVec]
    rw [Matrix.vec3_dotProduct]
    simpa [mul_comm] using hpPlane
  have hnq : n ⬝ᵥ qv = 0 := by
    rcases hq with ⟨hqUnit, hqPlane⟩
    dsimp [n, qv, normalVec, pointVec]
    rw [Matrix.vec3_dotProduct]
    simpa [mul_comm] using hqPlane
  have hrv : rv = n ⨯₃ pv := by
    dsimp [rv, n, pv]
    exact companion_vec alpha beta gamma p
  have hrNorm : rv ⬝ᵥ rv = 1 := by
    rw [hrv, cross_dot_cross]
    have hpn : pv ⬝ᵥ n = 0 := by
      rw [dotProduct_comm]
      exact hnp
    rw [hn, hpNorm, hnp, hpn]
    norm_num
  have hrnCross : rv ⨯₃ n = pv := by
    rw [hrv, cross_cross_eq_smul_sub_smul]
    have hpn : pv ⬝ᵥ n = 0 := by
      rw [dotProduct_comm]
      exact hnp
    rw [hn, hpn]
    simp
  have hxr : qv ⨯₃ rv = s • n := by
    rw [hrv, cross_cross_eq_smul_sub_smul']
    rw [hnq]
    simp only [zero_smul, sub_zero]
    rfl
  have htriple :=
    cross_cross_eq_smul_sub_smul' rv qv rv
  have hrelation :
      s • pv = qv - t • rv := by
    rw [hxr, map_smul, hrnCross] at htriple
    rw [hrNorm] at htriple
    simpa [s, t] using htriple
  have hdecomp : qv = s • pv + t • rv :=
    (eq_sub_iff_add_eq.mp hrelation).symm
  have hx := congrFun hdecomp (0 : Fin 3)
  have hy := congrFun hdecomp (1 : Fin 3)
  have hz := congrFun hdecomp (2 : Fin 3)
  dsimp [qv, pv, rv, pointVec, s, t] at hx hy hz
  simp only [Matrix.vec3_dotProduct] at hx hy hz
  dsimp [companion] at hx hy hz
  dsimp [companion]
  constructor
  · convert hx using 1 <;> ring
  constructor
  · convert hy using 1 <;> ring
  · convert hz using 1 <;> ring

private theorem companion_minors
    (alpha beta gamma : ℝ) (q : Point3)
    (hunit : q.x ^ 2 + q.y ^ 2 + q.z ^ 2 = 1)
    (hplane : q.x * Real.cos alpha + q.y * Real.cos beta +
      q.z * Real.cos gamma = 0) :
    q.y * (companion alpha beta gamma q).z -
          q.z * (companion alpha beta gamma q).y =
        Real.cos alpha ∧
      q.z * (companion alpha beta gamma q).x -
          q.x * (companion alpha beta gamma q).z =
        Real.cos beta ∧
      q.x * (companion alpha beta gamma q).y -
          q.y * (companion alpha beta gamma q).x =
        Real.cos gamma := by
  have hplaneX := congrArg (fun t : ℝ => q.x * t) hplane
  have hplaneY := congrArg (fun t : ℝ => q.y * t) hplane
  have hplaneZ := congrArg (fun t : ℝ => q.z * t) hplane
  have hunitA := congrArg (fun t : ℝ => Real.cos alpha * t) hunit
  have hunitB := congrArg (fun t : ℝ => Real.cos beta * t) hunit
  have hunitC := congrArg (fun t : ℝ => Real.cos gamma * t) hunit
  simp only [mul_zero] at hplaneX hplaneY hplaneZ hunitA hunitB hunitC
  unfold companion
  simp only
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem companion_determinant_identity
    (a b c alpha beta gamma : ℝ) (q : Point3)
    (hq : q ∈ constraint alpha beta gamma) :
    objective a b c q *
          objective a b c (companion alpha beta gamma q) -
        mixedObjective a b c q (companion alpha beta gamma q) ^ 2 =
      determinantCoefficient a b c alpha beta gamma := by
  rcases hq with ⟨hunit, hplane⟩
  rcases companion_minors alpha beta gamma q hunit hplane with
    ⟨hminorA, hminorB, hminorC⟩
  have hLagrange :
      objective a b c q *
            objective a b c (companion alpha beta gamma q) -
          mixedObjective a b c q (companion alpha beta gamma q) ^ 2 =
        (q.y * (companion alpha beta gamma q).z -
            q.z * (companion alpha beta gamma q).y) ^ 2 /
            (b ^ 2 * c ^ 2) +
          (q.z * (companion alpha beta gamma q).x -
            q.x * (companion alpha beta gamma q).z) ^ 2 /
            (c ^ 2 * a ^ 2) +
          (q.x * (companion alpha beta gamma q).y -
            q.y * (companion alpha beta gamma q).x) ^ 2 /
            (a ^ 2 * b ^ 2) := by
    unfold objective mixedObjective
    ring
  rw [hLagrange, hminorA, hminorB, hminorC]
  rfl

private def projectedEigenMatrix
    (a b c alpha beta gamma lambda : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![(1 / a ^ 2) * (1 - Real.cos alpha ^ 2) - lambda,
      -Real.cos alpha * Real.cos beta * (1 / b ^ 2),
      -Real.cos alpha * Real.cos gamma * (1 / c ^ 2);
    -Real.cos beta * Real.cos alpha * (1 / a ^ 2),
      (1 / b ^ 2) * (1 - Real.cos beta ^ 2) - lambda,
      -Real.cos beta * Real.cos gamma * (1 / c ^ 2);
    -Real.cos gamma * Real.cos alpha * (1 / a ^ 2),
      -Real.cos gamma * Real.cos beta * (1 / b ^ 2),
      (1 / c ^ 2) * (1 - Real.cos gamma ^ 2) - lambda]

set_option maxHeartbeats 800000 in
private theorem projectedEigenMatrix_det
    (a b c alpha beta gamma lambda : ℝ)
    (hunit : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1) :
    (projectedEigenMatrix a b c alpha beta gamma lambda).det =
      -lambda * eigenPolynomial a b c alpha beta gamma lambda := by
  have hsinA := Real.sin_sq_add_cos_sq alpha
  have hsinB := Real.sin_sq_add_cos_sq beta
  have hsinC := Real.sin_sq_add_cos_sq gamma
  have hgamma :
      Real.cos gamma ^ 2 =
        1 - Real.cos alpha ^ 2 - Real.cos beta ^ 2 := by
    linarith
  have hgamma4 :
      Real.cos gamma ^ 4 =
        (1 - Real.cos alpha ^ 2 - Real.cos beta ^ 2) ^ 2 := by
    calc
      Real.cos gamma ^ 4 = (Real.cos gamma ^ 2) ^ 2 := by ring
      _ = (1 - Real.cos alpha ^ 2 - Real.cos beta ^ 2) ^ 2 := by
        rw [hgamma]
  unfold projectedEigenMatrix eigenPolynomial traceCoefficient
    determinantCoefficient
  rw [Matrix.det_fin_three]
  simp
  rw [show Real.sin alpha ^ 2 = 1 - Real.cos alpha ^ 2 by linarith,
    show Real.sin beta ^ 2 = 1 - Real.cos beta ^ 2 by linarith,
    show Real.sin gamma ^ 2 = 1 - Real.cos gamma ^ 2 by linarith]
  ring_nf
  simp_rw [hgamma]
  ring

theorem gap3 (a b c alpha beta gamma : ℝ)
    (q : Point3) (lambda mu : ℝ)
    (hunit : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1)
    (hcrit : critical a b c alpha beta gamma q lambda mu) :
    lambda * eigenPolynomial a b c alpha beta gamma lambda = 0 := by
  have hq : q ∈ constraint alpha beta gamma := hcrit.2.2.2
  have hsum :=
    companion_objective_sum a b c alpha beta gamma q hunit hq
  have hdet :=
    companion_determinant_identity a b c alpha beta gamma q hq
  rcases hcrit with ⟨hx, hy, hz, hq'⟩
  have hx' := congrArg
    (fun t : ℝ => t * (companion alpha beta gamma q).x) hx
  have hy' := congrArg
    (fun t : ℝ => t * (companion alpha beta gamma q).y) hy
  have hz' := congrArg
    (fun t : ℝ => t * (companion alpha beta gamma q).z) hz
  have hdotQ := companion_dot_self alpha beta gamma q
  have hdotN := companion_dot_normal alpha beta gamma q
  have hdotQ' := congrArg (fun t : ℝ => lambda * t) hdotQ
  have hdotN' := congrArg (fun t : ℝ => mu * t) hdotN
  simp only [mul_zero] at hdotQ' hdotN'
  have hmixed :
      mixedObjective a b c q (companion alpha beta gamma q) = 0 := by
    unfold mixedObjective
    simp only [one_div, div_eq_mul_inv, zero_mul, mul_zero] at hx' hy' hz' ⊢
    nlinarith
  have hlambda :=
    gap1 a b c alpha beta gamma q lambda mu
      ⟨hx, hy, hz, hq'⟩
  rw [hlambda]
  rw [hmixed] at hdet
  norm_num at hdet
  have hsum' := congrArg
    (fun t : ℝ => objective a b c q * t) hsum
  have hpoly :
      eigenPolynomial a b c alpha beta gamma
        (objective a b c q) = 0 := by
    unfold eigenPolynomial
    nlinarith
  rw [hpoly]
  ring

theorem gap4 (a b c alpha beta gamma : ℝ)
    (ha : a > b) (hb : b > c) (hc : c > 0)
    (q : Point3) (lambda mu : ℝ)
    (hcrit : critical a b c alpha beta gamma q lambda mu) :
    lambda ≠ 0 := by
  have ha0 : a ≠ 0 := by linarith
  have hb0 : b ≠ 0 := by linarith
  have hc0 : c ≠ 0 := ne_of_gt hc
  rcases hcrit.2.2.2 with ⟨hunit, hplane⟩
  have hcoord :
      q.x ≠ 0 ∨ q.y ≠ 0 ∨ q.z ≠ 0 := by
    by_contra h
    push_neg at h
    rcases h with ⟨hx, hy, hz⟩
    rw [hx, hy, hz] at hunit
    norm_num at hunit
  have hxnonneg : 0 ≤ q.x ^ 2 / a ^ 2 := by positivity
  have hynonneg : 0 ≤ q.y ^ 2 / b ^ 2 := by positivity
  have hznonneg : 0 ≤ q.z ^ 2 / c ^ 2 := by positivity
  have hobj : 0 < objective a b c q := by
    unfold objective
    rcases hcoord with hx | hyz
    · have hxpos : 0 < q.x ^ 2 / a ^ 2 :=
        div_pos (sq_pos_iff.mpr hx) (sq_pos_iff.mpr ha0)
      linarith
    · rcases hyz with hy | hz
      · have hypos : 0 < q.y ^ 2 / b ^ 2 :=
          div_pos (sq_pos_iff.mpr hy) (sq_pos_iff.mpr hb0)
        linarith
      · have hzpos : 0 < q.z ^ 2 / c ^ 2 :=
          div_pos (sq_pos_iff.mpr hz) (sq_pos_iff.mpr hc0)
        linarith
  rw [gap1 a b c alpha beta gamma q lambda mu hcrit]
  exact hobj.ne'

theorem gap5 (a b c alpha beta gamma : ℝ)
    (hdisc : spectralDiscriminant a b c alpha beta gamma > 0) :
    lowEigenvalue a b c alpha beta gamma <
      highEigenvalue a b c alpha beta gamma := by
  have hsqrt :
      0 < Real.sqrt
        (spectralDiscriminant a b c alpha beta gamma) :=
    Real.sqrt_pos.2 hdisc
  unfold lowEigenvalue highEigenvalue
  linarith

private theorem reciprocal_square_orders
    {a b c : ℝ} (ha : a > b) (hb : b > c) (hc : c > 0) :
    1 / a ^ 2 < 1 / b ^ 2 ∧ 1 / b ^ 2 < 1 / c ^ 2 := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos (by linarith)
  have hcb2 : c ^ 2 < b ^ 2 := by nlinarith
  have hba2 : b ^ 2 < a ^ 2 := by nlinarith
  exact ⟨one_div_lt_one_div_of_lt hb2 hba2,
    one_div_lt_one_div_of_lt hc2 hcb2⟩

private theorem spectralDiscriminant_nonnegative
    (a b c alpha beta gamma : ℝ)
    (ha : a > b) (hb : b > c) (hc : c > 0)
    (hunit : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1) :
    0 ≤ spectralDiscriminant a b c alpha beta gamma := by
  rcases reciprocal_square_orders ha hb hc with ⟨hAB, hBC⟩
  have hAC : 0 < 1 / c ^ 2 - 1 / a ^ 2 := by linarith
  have hBC' : 0 < 1 / c ^ 2 - 1 / b ^ 2 := by linarith
  have hsinA := Real.sin_sq_add_cos_sq alpha
  have hsinB := Real.sin_sq_add_cos_sq beta
  have hsinC := Real.sin_sq_add_cos_sq gamma
  have hgamma :
      Real.cos gamma ^ 2 =
        1 - Real.cos alpha ^ 2 - Real.cos beta ^ 2 := by
    linarith
  have hgamma4 :
      Real.cos gamma ^ 4 =
        (1 - Real.cos alpha ^ 2 - Real.cos beta ^ 2) ^ 2 := by
    calc
      Real.cos gamma ^ 4 = (Real.cos gamma ^ 2) ^ 2 := by ring
      _ = (1 - Real.cos alpha ^ 2 - Real.cos beta ^ 2) ^ 2 := by
        rw [hgamma]
  have hsos :
      spectralDiscriminant a b c alpha beta gamma =
        ((1 / c ^ 2 - 1 / a ^ 2) -
            (1 / c ^ 2 - 1 / b ^ 2) -
            Real.cos alpha ^ 2 * (1 / c ^ 2 - 1 / a ^ 2) +
            Real.cos beta ^ 2 * (1 / c ^ 2 - 1 / b ^ 2)) ^ 2 +
          4 * Real.cos alpha ^ 2 * Real.cos beta ^ 2 *
            (1 / c ^ 2 - 1 / a ^ 2) *
            (1 / c ^ 2 - 1 / b ^ 2) := by
    unfold spectralDiscriminant traceCoefficient determinantCoefficient
    rw [show Real.sin alpha ^ 2 = 1 - Real.cos alpha ^ 2 by linarith,
      show Real.sin beta ^ 2 = 1 - Real.cos beta ^ 2 by linarith,
      show Real.sin gamma ^ 2 = 1 - Real.cos gamma ^ 2 by linarith]
    ring_nf
    simp_rw [hgamma4, hgamma]
    ring
  rw [hsos]
  positivity

private theorem determinantCoefficient_pos
    (a b c alpha beta gamma : ℝ)
    (ha : a > b) (hb : b > c) (hc : c > 0)
    (hunit : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1) :
    0 < determinantCoefficient a b c alpha beta gamma := by
  have ha0 : a ≠ 0 := by linarith
  have hb0 : b ≠ 0 := by linarith
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hnormal :
      Real.cos alpha ≠ 0 ∨ Real.cos beta ≠ 0 ∨
        Real.cos gamma ≠ 0 := by
    by_contra h
    push_neg at h
    rcases h with ⟨hA, hB, hC⟩
    rw [hA, hB, hC] at hunit
    norm_num at hunit
  have hA0 :
      0 ≤ Real.cos alpha ^ 2 / (b ^ 2 * c ^ 2) := by positivity
  have hB0 :
      0 ≤ Real.cos beta ^ 2 / (c ^ 2 * a ^ 2) := by positivity
  have hC0 :
      0 ≤ Real.cos gamma ^ 2 / (a ^ 2 * b ^ 2) := by positivity
  unfold determinantCoefficient
  rcases hnormal with hA | hBC
  · have hpos :
        0 < Real.cos alpha ^ 2 / (b ^ 2 * c ^ 2) :=
      div_pos (sq_pos_iff.mpr hA)
        (mul_pos (sq_pos_iff.mpr hb0) (sq_pos_iff.mpr hc0))
    linarith
  · rcases hBC with hB | hC
    · have hpos :
          0 < Real.cos beta ^ 2 / (c ^ 2 * a ^ 2) :=
        div_pos (sq_pos_iff.mpr hB)
          (mul_pos (sq_pos_iff.mpr hc0) (sq_pos_iff.mpr ha0))
      linarith
    · have hpos :
          0 < Real.cos gamma ^ 2 / (a ^ 2 * b ^ 2) :=
        div_pos (sq_pos_iff.mpr hC)
          (mul_pos (sq_pos_iff.mpr ha0) (sq_pos_iff.mpr hb0))
      linarith

private theorem low_high_root_data
    (a b c alpha beta gamma : ℝ)
    (ha : a > b) (hb : b > c) (hc : c > 0)
    (hunit : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1) :
    eigenPolynomial a b c alpha beta gamma
          (lowEigenvalue a b c alpha beta gamma) = 0 ∧
      eigenPolynomial a b c alpha beta gamma
          (highEigenvalue a b c alpha beta gamma) = 0 ∧
      lowEigenvalue a b c alpha beta gamma ≠ 0 ∧
      highEigenvalue a b c alpha beta gamma ≠ 0 := by
  have hdisc :=
    spectralDiscriminant_nonnegative a b c alpha beta gamma
      ha hb hc hunit
  have hsqrt :
      Real.sqrt (spectralDiscriminant a b c alpha beta gamma) ^ 2 =
        spectralDiscriminant a b c alpha beta gamma :=
    Real.sq_sqrt hdisc
  unfold spectralDiscriminant at hsqrt
  have hlow :
      eigenPolynomial a b c alpha beta gamma
        (lowEigenvalue a b c alpha beta gamma) = 0 := by
    unfold eigenPolynomial lowEigenvalue spectralDiscriminant
    nlinarith
  have hhigh :
      eigenPolynomial a b c alpha beta gamma
        (highEigenvalue a b c alpha beta gamma) = 0 := by
    unfold eigenPolynomial highEigenvalue spectralDiscriminant
    nlinarith
  have hproduct :
      lowEigenvalue a b c alpha beta gamma *
          highEigenvalue a b c alpha beta gamma =
        determinantCoefficient a b c alpha beta gamma := by
    unfold lowEigenvalue highEigenvalue spectralDiscriminant
    nlinarith
  have hdetpos :=
    determinantCoefficient_pos a b c alpha beta gamma
      ha hb hc hunit
  have hprodne :
      lowEigenvalue a b c alpha beta gamma *
          highEigenvalue a b c alpha beta gamma ≠ 0 := by
    rw [hproduct]
    exact hdetpos.ne'
  exact ⟨hlow, hhigh, (mul_ne_zero_iff.mp hprodne).1,
    (mul_ne_zero_iff.mp hprodne).2⟩

set_option maxHeartbeats 800000 in
private theorem critical_exists_of_root
    (a b c alpha beta gamma lambda : ℝ)
    (hunit : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1)
    (hroot : eigenPolynomial a b c alpha beta gamma lambda = 0)
    (hlambda : lambda ≠ 0) :
    ∃ q mu, critical a b c alpha beta gamma q lambda mu := by
  let M := projectedEigenMatrix a b c alpha beta gamma lambda
  have hdet : M.det = 0 := by
    dsimp [M]
    rw [projectedEigenMatrix_det a b c alpha beta gamma lambda hunit,
      hroot]
    ring
  rcases Matrix.exists_mulVec_eq_zero_iff.mpr hdet with
    ⟨v, hvne, hMv⟩
  have hrow0 := congrFun hMv (0 : Fin 3)
  have hrow1 := congrFun hMv (1 : Fin 3)
  have hrow2 := congrFun hMv (2 : Fin 3)
  simp [M, projectedEigenMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] at hrow0 hrow1 hrow2
  let N : ℝ := v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2
  have hcoord :
      v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 := by
    by_contra h
    push_neg at h
    rcases h with ⟨h0, h1, h2⟩
    apply hvne
    funext i
    fin_cases i <;> assumption
  have hN : 0 < N := by
    dsimp [N]
    rcases hcoord with h0 | h12
    · nlinarith [sq_pos_iff.mpr h0, sq_nonneg (v 1),
        sq_nonneg (v 2)]
    · rcases h12 with h1 | h2
      · nlinarith [sq_pos_iff.mpr h1, sq_nonneg (v 0),
          sq_nonneg (v 2)]
      · nlinarith [sq_pos_iff.mpr h2, sq_nonneg (v 0),
          sq_nonneg (v 1)]
  let s : ℝ := Real.sqrt N
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 hN
  have hsSq : s ^ 2 = N := by
    dsimp [s]
    exact Real.sq_sqrt hN.le
  have hgamma :
      Real.cos gamma ^ 2 =
        1 - Real.cos alpha ^ 2 - Real.cos beta ^ 2 := by
    linarith
  have hgamma3 :
      Real.cos gamma ^ 3 =
        Real.cos gamma *
          (1 - Real.cos alpha ^ 2 - Real.cos beta ^ 2) := by
    calc
      Real.cos gamma ^ 3 =
          Real.cos gamma * Real.cos gamma ^ 2 := by ring
      _ = Real.cos gamma *
          (1 - Real.cos alpha ^ 2 - Real.cos beta ^ 2) := by
        rw [hgamma]
  have hplaneRaw :
      Real.cos alpha * v 0 + Real.cos beta * v 1 +
        Real.cos gamma * v 2 = 0 := by
    have hcombined :
        Real.cos alpha *
              ((1 / a ^ 2) * (1 - Real.cos alpha ^ 2) * v 0 -
                lambda * v 0 -
                Real.cos alpha * Real.cos beta * (1 / b ^ 2) * v 1 -
                Real.cos alpha * Real.cos gamma * (1 / c ^ 2) * v 2) +
            Real.cos beta *
              (-Real.cos beta * Real.cos alpha * (1 / a ^ 2) * v 0 +
                (1 / b ^ 2) * (1 - Real.cos beta ^ 2) * v 1 -
                lambda * v 1 -
                Real.cos beta * Real.cos gamma * (1 / c ^ 2) * v 2) +
            Real.cos gamma *
              (-Real.cos gamma * Real.cos alpha * (1 / a ^ 2) * v 0 -
                Real.cos gamma * Real.cos beta * (1 / b ^ 2) * v 1 +
                (1 / c ^ 2) * (1 - Real.cos gamma ^ 2) * v 2 -
                lambda * v 2) =
          0 := by
      have hr0 := congrArg (fun t : ℝ => Real.cos alpha * t) hrow0
      have hr1 := congrArg (fun t : ℝ => Real.cos beta * t) hrow1
      have hr2 := congrArg (fun t : ℝ => Real.cos gamma * t) hrow2
      simp only [mul_zero] at hr0 hr1 hr2
      simp only [one_div] at hr0 hr1 hr2 ⊢
      nlinarith
    have hid :
        Real.cos alpha *
              ((1 / a ^ 2) * (1 - Real.cos alpha ^ 2) * v 0 -
                lambda * v 0 -
                Real.cos alpha * Real.cos beta * (1 / b ^ 2) * v 1 -
                Real.cos alpha * Real.cos gamma * (1 / c ^ 2) * v 2) +
            Real.cos beta *
              (-Real.cos beta * Real.cos alpha * (1 / a ^ 2) * v 0 +
                (1 / b ^ 2) * (1 - Real.cos beta ^ 2) * v 1 -
                lambda * v 1 -
                Real.cos beta * Real.cos gamma * (1 / c ^ 2) * v 2) +
            Real.cos gamma *
              (-Real.cos gamma * Real.cos alpha * (1 / a ^ 2) * v 0 -
                Real.cos gamma * Real.cos beta * (1 / b ^ 2) * v 1 +
                (1 / c ^ 2) * (1 - Real.cos gamma ^ 2) * v 2 -
                lambda * v 2) =
          -lambda * (Real.cos alpha * v 0 +
            Real.cos beta * v 1 + Real.cos gamma * v 2) := by
      ring_nf
      simp_rw [hgamma3, hgamma]
      ring
    have hmul :
        lambda * (Real.cos alpha * v 0 +
          Real.cos beta * v 1 + Real.cos gamma * v 2) = 0 := by
      nlinarith
    exact (mul_eq_zero.mp hmul).resolve_left hlambda
  let S : ℝ :=
    (1 / a ^ 2) * Real.cos alpha * v 0 +
      (1 / b ^ 2) * Real.cos beta * v 1 +
      (1 / c ^ 2) * Real.cos gamma * v 2
  have hproj0 :
      (1 / a ^ 2 - lambda) * v 0 -
        Real.cos alpha * S = 0 := by
    dsimp [S]
    convert hrow0 using 1 <;> ring
  have hproj1 :
      (1 / b ^ 2 - lambda) * v 1 -
        Real.cos beta * S = 0 := by
    dsimp [S]
    convert hrow1 using 1 <;> ring
  have hproj2 :
      (1 / c ^ 2 - lambda) * v 2 -
        Real.cos gamma * S = 0 := by
    dsimp [S]
    convert hrow2 using 1 <;> ring
  let q : Point3 := ⟨v 0 / s, v 1 / s, v 2 / s⟩
  let mu : ℝ := -2 * S / s
  refine ⟨q, mu, ?_, ?_, ?_, ?_⟩
  · dsimp [q, mu]
    field_simp [hs.ne']
    nlinarith
  · dsimp [q, mu]
    field_simp [hs.ne']
    nlinarith
  · dsimp [q, mu]
    field_simp [hs.ne']
    nlinarith
  · constructor
    · dsimp [q, N] at hsSq ⊢
      field_simp [hs.ne']
      nlinarith
    · dsimp [q]
      calc
        v 0 / s * Real.cos alpha + v 1 / s * Real.cos beta +
            v 2 / s * Real.cos gamma =
            (Real.cos alpha * v 0 + Real.cos beta * v 1 +
              Real.cos gamma * v 2) / s := by ring
        _ = 0 := by rw [hplaneRaw]; simp

private theorem eigenPolynomial_root_iff
    (a b c alpha beta gamma lambda : ℝ)
    (hdisc : 0 ≤ spectralDiscriminant a b c alpha beta gamma) :
    eigenPolynomial a b c alpha beta gamma lambda = 0 ↔
      lambda = lowEigenvalue a b c alpha beta gamma ∨
        lambda = highEigenvalue a b c alpha beta gamma := by
  have hsqrt :
      Real.sqrt (spectralDiscriminant a b c alpha beta gamma) ^ 2 =
        spectralDiscriminant a b c alpha beta gamma :=
    Real.sq_sqrt hdisc
  constructor
  · intro hroot
    have hsquare :
        (2 * lambda -
            traceCoefficient a b c alpha beta gamma) ^ 2 =
          Real.sqrt
            (spectralDiscriminant a b c alpha beta gamma) ^ 2 := by
      unfold eigenPolynomial at hroot
      unfold spectralDiscriminant at hsqrt ⊢
      nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with hplus | hminus
    · right
      unfold highEigenvalue
      linarith
    · left
      unfold lowEigenvalue
      linarith
  · intro h
    rcases h with rfl | rfl
    · have hroot :
          eigenPolynomial a b c alpha beta gamma
            (lowEigenvalue a b c alpha beta gamma) = 0 := by
        unfold eigenPolynomial lowEigenvalue
        unfold spectralDiscriminant at hsqrt ⊢
        nlinarith
      exact hroot
    · have hroot :
          eigenPolynomial a b c alpha beta gamma
            (highEigenvalue a b c alpha beta gamma) = 0 := by
        unfold eigenPolynomial highEigenvalue
        unfold spectralDiscriminant at hsqrt ⊢
        nlinarith
      exact hroot

theorem gap6 (a b c alpha beta gamma : ℝ)
    (ha : a > b) (hb : b > c) (hc : c > 0)
    (hunit : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1) :
    {lambda | ∃ q mu, critical a b c alpha beta gamma q lambda mu} =
      ({lowEigenvalue a b c alpha beta gamma,
        highEigenvalue a b c alpha beta gamma} : Set ℝ) := by
  have hdisc :=
    spectralDiscriminant_nonnegative a b c alpha beta gamma
      ha hb hc hunit
  have hrootData :=
    low_high_root_data a b c alpha beta gamma ha hb hc hunit
  ext lambda
  constructor
  · rintro ⟨q, mu, hcrit⟩
    have hproduct :=
      gap3 a b c alpha beta gamma q lambda mu hunit hcrit
    have hlambda :=
      gap4 a b c alpha beta gamma ha hb hc q lambda mu hcrit
    have hroot : eigenPolynomial a b c alpha beta gamma lambda = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left hlambda
    simpa using
      (eigenPolynomial_root_iff a b c alpha beta gamma lambda
        hdisc).mp hroot
  · intro hlambda
    have hcases :
        lambda = lowEigenvalue a b c alpha beta gamma ∨
          lambda = highEigenvalue a b c alpha beta gamma := by
      simpa using hlambda
    rcases hcases with rfl | rfl
    · exact critical_exists_of_root a b c alpha beta gamma
        (lowEigenvalue a b c alpha beta gamma) hunit
        hrootData.1 hrootData.2.2.1
    · exact critical_exists_of_root a b c alpha beta gamma
        (highEigenvalue a b c alpha beta gamma) hunit
        hrootData.2.1 hrootData.2.2.2

theorem gap7 (a b c alpha beta gamma : ℝ)
    (ha : a > b) (hb : b > c) (hc : c > 0)
    (hunit : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1) :
    ∃ P₁ mu, critical a b c alpha beta gamma P₁
      (lowEigenvalue a b c alpha beta gamma) mu := by
  have hdata :=
    low_high_root_data a b c alpha beta gamma ha hb hc hunit
  exact critical_exists_of_root a b c alpha beta gamma
    (lowEigenvalue a b c alpha beta gamma) hunit
    hdata.1 hdata.2.2.1

theorem gap8 (a b c alpha beta gamma : ℝ)
    (ha : a > b) (hb : b > c) (hc : c > 0)
    (hunit : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1) :
    ∃ P₁ P₂ : Point3, ∃ mu : ℝ,
      critical a b c alpha beta gamma P₁
        (lowEigenvalue a b c alpha beta gamma) mu ∧
        P₂ = ⟨-P₁.x, -P₁.y, -P₁.z⟩ := by
  rcases gap7 a b c alpha beta gamma ha hb hc hunit with
    ⟨P₁, mu, hcrit⟩
  exact ⟨P₁, ⟨-P₁.x, -P₁.y, -P₁.z⟩, mu, hcrit, rfl⟩

theorem gap9 (a b c alpha beta gamma : ℝ)
    (ha : a > b) (hb : b > c) (hc : c > 0)
    (hunit : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1) :
    ∃ P₃ mu, critical a b c alpha beta gamma P₃
      (highEigenvalue a b c alpha beta gamma) mu := by
  have hdata :=
    low_high_root_data a b c alpha beta gamma ha hb hc hunit
  exact critical_exists_of_root a b c alpha beta gamma
    (highEigenvalue a b c alpha beta gamma) hunit
    hdata.2.1 hdata.2.2.2

theorem gap10 (a b c alpha beta gamma : ℝ)
    (ha : a > b) (hb : b > c) (hc : c > 0)
    (hunit : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1) :
    ∃ P₃ P₄ : Point3, ∃ mu : ℝ,
      critical a b c alpha beta gamma P₃
        (highEigenvalue a b c alpha beta gamma) mu ∧
        P₄ = ⟨-P₃.x, -P₃.y, -P₃.z⟩ := by
  rcases gap9 a b c alpha beta gamma ha hb hc hunit with
    ⟨P₃, mu, hcrit⟩
  exact ⟨P₃, ⟨-P₃.x, -P₃.y, -P₃.z⟩, mu, hcrit, rfl⟩

private theorem eigenPolynomial_factor
    (a b c alpha beta gamma lambda : ℝ)
    (hdisc : 0 ≤ spectralDiscriminant a b c alpha beta gamma) :
    eigenPolynomial a b c alpha beta gamma lambda =
      (lambda - lowEigenvalue a b c alpha beta gamma) *
        (lambda - highEigenvalue a b c alpha beta gamma) := by
  have hsqrt :
      Real.sqrt (spectralDiscriminant a b c alpha beta gamma) ^ 2 =
        spectralDiscriminant a b c alpha beta gamma :=
    Real.sq_sqrt hdisc
  unfold eigenPolynomial lowEigenvalue highEigenvalue
  unfold spectralDiscriminant at hsqrt ⊢
  nlinarith

private theorem objective_polynomial_nonpos
    (a b c alpha beta gamma : ℝ) (q : Point3)
    (hnormal : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1)
    (hq : q ∈ constraint alpha beta gamma) :
    eigenPolynomial a b c alpha beta gamma (objective a b c q) ≤ 0 := by
  have hsum :=
    companion_objective_sum a b c alpha beta gamma q hnormal hq
  have hdet :=
    companion_determinant_identity a b c alpha beta gamma q hq
  have hsum' := congrArg
    (fun t : ℝ => objective a b c q * t) hsum
  unfold eigenPolynomial
  nlinarith [sq_nonneg
    (mixedObjective a b c q (companion alpha beta gamma q))]

private theorem objective_bounds
    (a b c alpha beta gamma : ℝ)
    (ha : a > b) (hb : b > c) (hc : c > 0)
    (hunit : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1)
    (hdisc : spectralDiscriminant a b c alpha beta gamma > 0)
    (q : Point3) (hq : q ∈ constraint alpha beta gamma) :
    lowEigenvalue a b c alpha beta gamma ≤ objective a b c q ∧
      objective a b c q ≤ highEigenvalue a b c alpha beta gamma := by
  have hpoly :=
    objective_polynomial_nonpos a b c alpha beta gamma q hunit hq
  rw [eigenPolynomial_factor a b c alpha beta gamma
    (objective a b c q) hdisc.le] at hpoly
  have hlowHigh :=
    gap5 a b c alpha beta gamma hdisc
  rcases mul_nonpos_iff.mp hpoly with hbetween | himpossible
  · exact ⟨by linarith [hbetween.1], by linarith [hbetween.2]⟩
  · exfalso
    linarith [himpossible.1, himpossible.2]

private def antipode (p : Point3) : Point3 :=
  ⟨-p.x, -p.y, -p.z⟩

private theorem critical_companion_mixed_zero
    (a b c alpha beta gamma : ℝ)
    (p : Point3) (lambda mu : ℝ)
    (hcrit : critical a b c alpha beta gamma p lambda mu) :
    mixedObjective a b c p (companion alpha beta gamma p) = 0 := by
  rcases hcrit with ⟨hx, hy, hz, hp⟩
  have hx' := congrArg
    (fun z : ℝ => z * (companion alpha beta gamma p).x) hx
  have hy' := congrArg
    (fun z : ℝ => z * (companion alpha beta gamma p).y) hy
  have hz' := congrArg
    (fun z : ℝ => z * (companion alpha beta gamma p).z) hz
  have hdotP := companion_dot_self alpha beta gamma p
  have hdotN := companion_dot_normal alpha beta gamma p
  have hdotP' := congrArg (fun z : ℝ => lambda * z) hdotP
  have hdotN' := congrArg (fun z : ℝ => mu * z) hdotN
  simp only [mul_zero] at hdotP' hdotN'
  unfold mixedObjective
  simp only [div_eq_mul_inv, zero_mul] at hx' hy' hz' ⊢
  nlinarith

set_option maxHeartbeats 800000 in
private theorem critical_level_unique_up_to_antipode
    (a b c alpha beta gamma : ℝ)
    (hnormal : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1)
    (p : Point3) (lambda mu other : ℝ)
    (hcrit : critical a b c alpha beta gamma p lambda mu)
    (hcompanion :
      objective a b c (companion alpha beta gamma p) = other)
    (hother : other ≠ lambda)
    (q : Point3) (hq : q ∈ constraint alpha beta gamma)
    (hqLevel : objective a b c q = lambda) :
    q = p ∨ q = antipode p := by
  let r := companion alpha beta gamma p
  let s : ℝ := q.x * p.x + q.y * p.y + q.z * p.z
  let t : ℝ := q.x * r.x + q.y * r.y + q.z * r.z
  have hp : p ∈ constraint alpha beta gamma := hcrit.2.2.2
  have hdecomp :=
    point_decomposition alpha beta gamma p q hnormal hp hq
  change
    q.x = s * p.x + t * r.x ∧
      q.y = s * p.y + t * r.y ∧
      q.z = s * p.z + t * r.z at hdecomp
  rcases hdecomp with ⟨hx, hy, hz⟩
  have hxSq := congrArg (fun z : ℝ => z ^ 2) hx
  have hySq := congrArg (fun z : ℝ => z ^ 2) hy
  have hzSq := congrArg (fun z : ℝ => z ^ 2) hz
  change q.x ^ 2 = (s * p.x + t * r.x) ^ 2 at hxSq
  change q.y ^ 2 = (s * p.y + t * r.y) ^ 2 at hySq
  change q.z ^ 2 = (s * p.z + t * r.z) ^ 2 at hzSq
  have hpUnit := hp.1
  have hqUnit := hq.1
  have hcoordSq :=
    companion_coordinate_squares alpha beta gamma p
      hnormal hp.1 hp.2
  have htrigA := Real.sin_sq_add_cos_sq alpha
  have htrigB := Real.sin_sq_add_cos_sq beta
  have htrigC := Real.sin_sq_add_cos_sq gamma
  have hrUnit :
      r.x ^ 2 + r.y ^ 2 + r.z ^ 2 = 1 := by
    dsimp [r]
    rcases hcoordSq with ⟨hA, hB, hC⟩
    nlinarith
  have hdot :
      p.x * r.x + p.y * r.y + p.z * r.z = 0 := by
    dsimp [r]
    exact companion_dot_self alpha beta gamma p
  have hst :
      s ^ 2 + t ^ 2 = 1 := by
    calc
      s ^ 2 + t ^ 2 =
          (s * p.x + t * r.x) ^ 2 +
            (s * p.y + t * r.y) ^ 2 +
            (s * p.z + t * r.z) ^ 2 := by
        rw [show
          (s * p.x + t * r.x) ^ 2 +
                (s * p.y + t * r.y) ^ 2 +
                (s * p.z + t * r.z) ^ 2 =
              s ^ 2 * (p.x ^ 2 + p.y ^ 2 + p.z ^ 2) +
                t ^ 2 * (r.x ^ 2 + r.y ^ 2 + r.z ^ 2) +
                2 * s * t *
                  (p.x * r.x + p.y * r.y + p.z * r.z) by ring,
          hpUnit, hrUnit, hdot]
        ring
      _ = q.x ^ 2 + q.y ^ 2 + q.z ^ 2 := by
        nlinarith
      _ = 1 := hqUnit
  have hpLevel :
      objective a b c p = lambda :=
    (gap1 a b c alpha beta gamma p lambda mu hcrit).symm
  have hmixed :
      mixedObjective a b c p r = 0 := by
    dsimp [r]
    exact critical_companion_mixed_zero
      a b c alpha beta gamma p lambda mu hcrit
  have hobjective :
      objective a b c q =
        s ^ 2 * objective a b c p +
          t ^ 2 * objective a b c r +
          2 * s * t * mixedObjective a b c p r := by
    calc
      objective a b c q =
          (s * p.x + t * r.x) ^ 2 / a ^ 2 +
            (s * p.y + t * r.y) ^ 2 / b ^ 2 +
            (s * p.z + t * r.z) ^ 2 / c ^ 2 := by
        unfold objective
        rw [hxSq, hySq, hzSq]
      _ = s ^ 2 * objective a b c p +
          t ^ 2 * objective a b c r +
          2 * s * t * mixedObjective a b c p r := by
        unfold objective mixedObjective
        ring
  have hproduct : (other - lambda) * t ^ 2 = 0 := by
    change objective a b c r = other at hcompanion
    have hlevelEq :
        objective a b c q =
          s ^ 2 * lambda + t ^ 2 * other := by
      simpa [hpLevel, hcompanion, hmixed] using hobjective
    calc
      (other - lambda) * t ^ 2 =
          (s ^ 2 * lambda + t ^ 2 * other) -
            lambda * (s ^ 2 + t ^ 2) := by ring
      _ = objective a b c q - lambda := by
        rw [← hlevelEq, hst]
        ring
      _ = 0 := by rw [hqLevel]; ring
  have htSq : t ^ 2 = 0 :=
    (mul_eq_zero.mp hproduct).resolve_left (sub_ne_zero.mpr hother)
  have ht : t = 0 := sq_eq_zero_iff.mp htSq
  have hsSq : s ^ 2 = 1 := by
    calc
      s ^ 2 = s ^ 2 + t ^ 2 := by rw [htSq]; ring
      _ = 1 := hst
  have hqForm :
      q = ⟨s * p.x, s * p.y, s * p.z⟩ := by
    calc
      q = ⟨q.x, q.y, q.z⟩ := by rfl
      _ = ⟨s * p.x, s * p.y, s * p.z⟩ := by
        rw [hx, hy, hz, ht]
        simp
  rcases sq_eq_one_iff.mp hsSq with hs | hs
  · left
    rw [hqForm, hs]
    cases p
    simp
  · right
    rw [hqForm, hs]
    cases p
    simp [antipode]

private theorem antipode_constraint
    (alpha beta gamma : ℝ) (p : Point3)
    (hp : p ∈ constraint alpha beta gamma) :
    antipode p ∈ constraint alpha beta gamma := by
  rcases hp with ⟨hunit, hplane⟩
  unfold antipode constraint
  constructor <;> simp only
  · nlinarith
  · nlinarith

private theorem objective_antipode
    (a b c : ℝ) (p : Point3) :
    objective a b c (antipode p) = objective a b c p := by
  unfold objective antipode
  simp only
  ring

theorem gap11 (a b c alpha beta gamma : ℝ)
    (ha : a > b) (hb : b > c) (hc : c > 0)
    (hunit : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1)
    (hdisc : spectralDiscriminant a b c alpha beta gamma > 0) :
    ∃ P₁ P₂, P₂ = ⟨-P₁.x, -P₁.y, -P₁.z⟩ ∧
      minimizers a b c alpha beta gamma =
        ({P₁, P₂} : Set Point3) := by
  rcases gap7 a b c alpha beta gamma ha hb hc hunit with
    ⟨P₁, mu, hcrit⟩
  let P₂ := antipode P₁
  have hP₁ : P₁ ∈ constraint alpha beta gamma := hcrit.2.2.2
  have hP₂ : P₂ ∈ constraint alpha beta gamma := by
    dsimp [P₂]
    exact antipode_constraint alpha beta gamma P₁ hP₁
  have hP₁Level :
      objective a b c P₁ =
        lowEigenvalue a b c alpha beta gamma :=
    (gap1 a b c alpha beta gamma P₁
      (lowEigenvalue a b c alpha beta gamma) mu hcrit).symm
  have hP₂Level :
      objective a b c P₂ =
        lowEigenvalue a b c alpha beta gamma := by
    dsimp [P₂]
    rw [objective_antipode, hP₁Level]
  have hP₁Min :
      P₁ ∈ minimizers a b c alpha beta gamma := by
    refine ⟨hP₁, ?_⟩
    intro q hq
    rw [hP₁Level]
    exact (objective_bounds a b c alpha beta gamma
      ha hb hc hunit hdisc q hq).1
  have hP₂Min :
      P₂ ∈ minimizers a b c alpha beta gamma := by
    refine ⟨hP₂, ?_⟩
    intro q hq
    rw [hP₂Level]
    exact (objective_bounds a b c alpha beta gamma
      ha hb hc hunit hdisc q hq).1
  have hrootSum :
      lowEigenvalue a b c alpha beta gamma +
          highEigenvalue a b c alpha beta gamma =
        traceCoefficient a b c alpha beta gamma := by
    unfold lowEigenvalue highEigenvalue
    ring
  have hcompanion :
      objective a b c (companion alpha beta gamma P₁) =
        highEigenvalue a b c alpha beta gamma := by
    have hsum :=
      companion_objective_sum a b c alpha beta gamma
        P₁ hunit hP₁
    nlinarith
  have hdistinct :
      highEigenvalue a b c alpha beta gamma ≠
        lowEigenvalue a b c alpha beta gamma :=
    (gap5 a b c alpha beta gamma hdisc).ne'
  refine ⟨P₁, P₂, ?_, ?_⟩
  · dsimp [P₂, antipode]
  · ext q
    constructor
    · intro hqMin
      have hqConstraint := hqMin.1
      have hqUpper := hqMin.2 P₁ hP₁
      have hqLower :=
        (objective_bounds a b c alpha beta gamma
          ha hb hc hunit hdisc q hqConstraint).1
      have hqLevel :
          objective a b c q =
            lowEigenvalue a b c alpha beta gamma := by
        rw [hP₁Level] at hqUpper
        linarith
      have hcases :=
        critical_level_unique_up_to_antipode
          a b c alpha beta gamma hunit P₁
          (lowEigenvalue a b c alpha beta gamma) mu
          (highEigenvalue a b c alpha beta gamma)
          hcrit hcompanion hdistinct q hqConstraint hqLevel
      rcases hcases with hqP₁ | hqP₂
      · simp [hqP₁]
      · have : q = P₂ := by
          simpa [P₂] using hqP₂
        simp [this]
    · intro hqPair
      have hcases : q = P₁ ∨ q = P₂ := by
        simpa using hqPair
      rcases hcases with rfl | rfl
      · exact hP₁Min
      · exact hP₂Min

theorem gap12 (a b c alpha beta gamma : ℝ)
    (ha : a > b) (hb : b > c) (hc : c > 0)
    (hunit : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1)
    (hdisc : spectralDiscriminant a b c alpha beta gamma > 0) :
    ∃ P₁ P₂, P₁ ∈ minimizers a b c alpha beta gamma ∧
      P₂ ∈ minimizers a b c alpha beta gamma ∧
      objective a b c P₁ = objective a b c P₂ := by
  rcases gap11 a b c alpha beta gamma ha hb hc hunit hdisc with
    ⟨P₁, P₂, hP₂, hset⟩
  refine ⟨P₁, P₂, ?_, ?_, ?_⟩
  · rw [hset]
    simp
  · rw [hset]
    simp
  · rw [hP₂]
    symm
    exact objective_antipode a b c P₁

theorem gap13 (a b c alpha beta gamma : ℝ)
    (ha : a > b) (hb : b > c) (hc : c > 0)
    (hunit : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1)
    (hdisc : spectralDiscriminant a b c alpha beta gamma > 0) :
    ∃ P₂, P₂ ∈ minimizers a b c alpha beta gamma ∧
      objective a b c P₂ =
        lowEigenvalue a b c alpha beta gamma := by
  rcases gap7 a b c alpha beta gamma ha hb hc hunit with
    ⟨P₂, mu, hcrit⟩
  have hconstraint : P₂ ∈ constraint alpha beta gamma :=
    hcrit.2.2.2
  have hlevel :
      objective a b c P₂ =
        lowEigenvalue a b c alpha beta gamma :=
    (gap1 a b c alpha beta gamma P₂
      (lowEigenvalue a b c alpha beta gamma) mu hcrit).symm
  refine ⟨P₂, ⟨hconstraint, ?_⟩, hlevel⟩
  intro q hq
  rw [hlevel]
  exact (objective_bounds a b c alpha beta gamma
    ha hb hc hunit hdisc q hq).1

theorem gap14 (a b c alpha beta gamma : ℝ)
    (ha : a > b) (hb : b > c) (hc : c > 0)
    (hunit : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1)
    (hdisc : spectralDiscriminant a b c alpha beta gamma > 0) :
    ∃ P₃ P₄, P₄ = ⟨-P₃.x, -P₃.y, -P₃.z⟩ ∧
      maximizers a b c alpha beta gamma =
        ({P₃, P₄} : Set Point3) := by
  rcases gap9 a b c alpha beta gamma ha hb hc hunit with
    ⟨P₃, mu, hcrit⟩
  let P₄ := antipode P₃
  have hP₃ : P₃ ∈ constraint alpha beta gamma := hcrit.2.2.2
  have hP₄ : P₄ ∈ constraint alpha beta gamma := by
    dsimp [P₄]
    exact antipode_constraint alpha beta gamma P₃ hP₃
  have hP₃Level :
      objective a b c P₃ =
        highEigenvalue a b c alpha beta gamma :=
    (gap1 a b c alpha beta gamma P₃
      (highEigenvalue a b c alpha beta gamma) mu hcrit).symm
  have hP₄Level :
      objective a b c P₄ =
        highEigenvalue a b c alpha beta gamma := by
    dsimp [P₄]
    rw [objective_antipode, hP₃Level]
  have hP₃Max :
      P₃ ∈ maximizers a b c alpha beta gamma := by
    refine ⟨hP₃, ?_⟩
    intro q hq
    rw [hP₃Level]
    exact (objective_bounds a b c alpha beta gamma
      ha hb hc hunit hdisc q hq).2
  have hP₄Max :
      P₄ ∈ maximizers a b c alpha beta gamma := by
    refine ⟨hP₄, ?_⟩
    intro q hq
    rw [hP₄Level]
    exact (objective_bounds a b c alpha beta gamma
      ha hb hc hunit hdisc q hq).2
  have hrootSum :
      lowEigenvalue a b c alpha beta gamma +
          highEigenvalue a b c alpha beta gamma =
        traceCoefficient a b c alpha beta gamma := by
    unfold lowEigenvalue highEigenvalue
    ring
  have hcompanion :
      objective a b c (companion alpha beta gamma P₃) =
        lowEigenvalue a b c alpha beta gamma := by
    have hsum :=
      companion_objective_sum a b c alpha beta gamma
        P₃ hunit hP₃
    nlinarith
  have hdistinct :
      lowEigenvalue a b c alpha beta gamma ≠
        highEigenvalue a b c alpha beta gamma :=
    (gap5 a b c alpha beta gamma hdisc).ne
  refine ⟨P₃, P₄, ?_, ?_⟩
  · dsimp [P₄, antipode]
  · ext q
    constructor
    · intro hqMax
      have hqConstraint := hqMax.1
      have hqLower := hqMax.2 P₃ hP₃
      have hqUpper :=
        (objective_bounds a b c alpha beta gamma
          ha hb hc hunit hdisc q hqConstraint).2
      have hqLevel :
          objective a b c q =
            highEigenvalue a b c alpha beta gamma := by
        rw [hP₃Level] at hqLower
        linarith
      have hcases :=
        critical_level_unique_up_to_antipode
          a b c alpha beta gamma hunit P₃
          (highEigenvalue a b c alpha beta gamma) mu
          (lowEigenvalue a b c alpha beta gamma)
          hcrit hcompanion hdistinct q hqConstraint hqLevel
      rcases hcases with hqP₃ | hqP₄
      · simp [hqP₃]
      · have : q = P₄ := by
          simpa [P₄] using hqP₄
        simp [this]
    · intro hqPair
      have hcases : q = P₃ ∨ q = P₄ := by
        simpa using hqPair
      rcases hcases with rfl | rfl
      · exact hP₃Max
      · exact hP₄Max

theorem gap15 (a b c alpha beta gamma : ℝ)
    (ha : a > b) (hb : b > c) (hc : c > 0)
    (hunit : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1)
    (hdisc : spectralDiscriminant a b c alpha beta gamma > 0) :
    ∃ P₃ P₄, P₃ ∈ maximizers a b c alpha beta gamma ∧
      P₄ ∈ maximizers a b c alpha beta gamma ∧
      objective a b c P₃ = objective a b c P₄ := by
  rcases gap14 a b c alpha beta gamma ha hb hc hunit hdisc with
    ⟨P₃, P₄, hP₄, hset⟩
  refine ⟨P₃, P₄, ?_, ?_, ?_⟩
  · rw [hset]
    simp
  · rw [hset]
    simp
  · rw [hP₄]
    symm
    exact objective_antipode a b c P₃

theorem gap16 (a b c alpha beta gamma : ℝ)
    (ha : a > b) (hb : b > c) (hc : c > 0)
    (hunit : Real.cos alpha ^ 2 + Real.cos beta ^ 2 +
      Real.cos gamma ^ 2 = 1)
    (hdisc : spectralDiscriminant a b c alpha beta gamma > 0) :
    ∃ P₄, P₄ ∈ maximizers a b c alpha beta gamma ∧
      objective a b c P₄ =
        highEigenvalue a b c alpha beta gamma := by
  rcases gap9 a b c alpha beta gamma ha hb hc hunit with
    ⟨P₄, mu, hcrit⟩
  have hconstraint : P₄ ∈ constraint alpha beta gamma :=
    hcrit.2.2.2
  have hlevel :
      objective a b c P₄ =
        highEigenvalue a b c alpha beta gamma :=
    (gap1 a b c alpha beta gamma P₄
      (highEigenvalue a b c alpha beta gamma) mu hcrit).symm
  refine ⟨P₄, ⟨hconstraint, ?_⟩, hlevel⟩
  intro q hq
  rw [hlevel]
  exact (objective_bounds a b c alpha beta gamma
    ha hb hc hunit hdisc q hq).2

end

end ProofGap.Exercise3665
