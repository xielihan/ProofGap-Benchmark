import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3724

noncomputable section

open Filter
open scoped Interval Topology

def target (x : ℝ) : ℝ :=
  Real.sqrt (1 + x ^ 2)

def objective (p : ℝ × ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (p.1 + p.2 * x - target x) ^ 2

def radius (p : ℝ × ℝ) : ℝ :=
  Real.sqrt (p.1 ^ 2 + p.2 ^ 2)

def IsCoercive (g : (ℝ × ℝ) → ℝ) : Prop :=
  ∀ p : ℕ → ℝ × ℝ,
    Tendsto (fun n => ‖p n‖) atTop atTop →
      Tendsto (fun n => g (p n)) atTop atTop

def IsMinimizer (p : ℝ × ℝ) : Prop :=
  ∀ q : ℝ × ℝ, objective p ≤ objective q

def partialA (p : ℝ × ℝ) : ℝ :=
  deriv (fun a => objective (a, p.2)) p.1

def partialB (p : ℝ × ℝ) : ℝ :=
  deriv (fun b => objective (p.1, b)) p.2

def optimalA : ℝ :=
  2 * (1 - Real.sqrt 2 + Real.log (1 + Real.sqrt 2))

def optimalB : ℝ :=
  5 * Real.sqrt 2 - 4 - 3 * Real.log (1 + Real.sqrt 2)

def optimalPair : ℝ × ℝ :=
  (optimalA, optimalB)

def Approx (actual expected tolerance : ℝ) : Prop :=
  |actual - expected| < tolerance

private def sqrtAntiderivative (x : ℝ) : ℝ :=
  (x * Real.sqrt (1 + x ^ 2) + Real.arsinh x) / 2

private def weightedSqrtAntiderivative (x : ℝ) : ℝ :=
  Real.sqrt (1 + x ^ 2) ^ 3 / 3

private lemma hasDerivAt_sqrt_one_add_sq (x : ℝ) :
    HasDerivAt
      (fun t : ℝ => Real.sqrt (1 + t ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
  have hinner :
      HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add
      ((hasDerivAt_id x).pow 2) using 1 <;>
        simp [id_eq]
  convert hinner.sqrt (by positivity) using 1 <;> ring

private lemma hasDerivAt_sqrtAntiderivative (x : ℝ) :
    HasDerivAt sqrtAntiderivative (Real.sqrt (1 + x ^ 2)) x := by
  have hsqrt := hasDerivAt_sqrt_one_add_sq x
  have harsinh := Real.hasDerivAt_arsinh x
  have hspos : 0 < Real.sqrt (1 + x ^ 2) := by positivity
  have hsq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt (by positivity)
  unfold sqrtAntiderivative
  convert ((hasDerivAt_id x).mul hsqrt).add harsinh |>.div_const 2 using 1
  simp only [id_eq]
  field_simp
  nlinarith

private lemma hasDerivAt_weightedSqrtAntiderivative (x : ℝ) :
    HasDerivAt weightedSqrtAntiderivative
      (x * Real.sqrt (1 + x ^ 2)) x := by
  have hsqrt := hasDerivAt_sqrt_one_add_sq x
  have hspos : 0 < Real.sqrt (1 + x ^ 2) := by positivity
  unfold weightedSqrtAntiderivative
  convert (hsqrt.pow 3).div_const 3 using 1
  norm_num
  field_simp [hspos.ne']

private lemma integral_target :
    (∫ x in (0 : ℝ)..1, target x) =
      (Real.sqrt 2 + Real.log (1 + Real.sqrt 2)) / 2 := by
  unfold target
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_sqrtAntiderivative x)
    ((by
      unfold target
      fun_prop : Continuous target).intervalIntegrable 0 1)]
  unfold sqrtAntiderivative
  dsimp [Real.arsinh]
  norm_num

private lemma integral_weighted_target :
    (∫ x in (0 : ℝ)..1, x * target x) =
      (2 * Real.sqrt 2 - 1) / 3 := by
  unfold target
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_weightedSqrtAntiderivative x)
    ((by
      unfold target
      fun_prop : Continuous (fun x : ℝ => x * target x)).intervalIntegrable 0 1)]
  unfold weightedSqrtAntiderivative
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg 2
  norm_num
  nlinarith

private def objectiveAntiderivative (a b x : ℝ) : ℝ :=
  a ^ 2 * x + a * b * x ^ 2 + b ^ 2 * x ^ 3 / 3 -
      2 * a * sqrtAntiderivative x -
    2 * b * weightedSqrtAntiderivative x +
      x + x ^ 3 / 3

private lemma hasDerivAt_objectiveAntiderivative (a b x : ℝ) :
    HasDerivAt (objectiveAntiderivative a b)
      ((a + b * x - target x) ^ 2) x := by
  have h1 := (hasDerivAt_id x).const_mul (a ^ 2)
  have h2 := ((hasDerivAt_id x).pow 2).const_mul (a * b)
  have h3 := ((hasDerivAt_id x).pow 3).const_mul (b ^ 2) |>.div_const 3
  have h4 := (hasDerivAt_sqrtAntiderivative x).const_mul (2 * a)
  have h5 := (hasDerivAt_weightedSqrtAntiderivative x).const_mul (2 * b)
  have h6 := hasDerivAt_id x
  have h7 := ((hasDerivAt_id x).pow 3).div_const 3
  have h := (((((h1.add h2).add h3).sub h4).sub h5).add h6).add h7
  have hsq : target x ^ 2 = 1 + x ^ 2 := by
    unfold target
    exact Real.sq_sqrt (by positivity)
  convert h using 1
  simp only [id_eq]
  unfold target at hsq ⊢
  norm_num
  nlinarith

private lemma objective_formula (a b : ℝ) :
    objective (a, b) =
      a ^ 2 + a * b + b ^ 2 / 3 -
        a * (Real.sqrt 2 + Real.log (1 + Real.sqrt 2)) -
        b * ((2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1)) +
        4 / 3 := by
  unfold objective
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_objectiveAntiderivative a b x)
    ((by
      unfold target
      fun_prop : Continuous
        (fun x : ℝ => (a + b * x - target x) ^ 2)).intervalIntegrable 0 1)]
  unfold objectiveAntiderivative sqrtAntiderivative
    weightedSqrtAntiderivative
  dsimp [Real.arsinh]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg 2
  have hs3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    calc
      Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [hs]
  norm_num
  rw [hs3]
  ring

private lemma objective_centered (a b : ℝ) :
    objective (a, b) =
      objective optimalPair +
        (a - optimalA + (b - optimalB) / 2) ^ 2 +
        (b - optimalB) ^ 2 / 12 := by
  rw [objective_formula, objective_formula]
  unfold optimalPair optimalA optimalB
  ring

private lemma residual_integral_formula (a b : ℝ) :
    2 * (∫ x in (0 : ℝ)..1, (a + b * x - target x)) =
      2 * a + b - (Real.sqrt 2 + Real.log (1 + Real.sqrt 2)) := by
  let F : ℝ → ℝ :=
    fun x => a * x + b * x ^ 2 / 2 - sqrtAntiderivative x
  have hF : ∀ x : ℝ,
      HasDerivAt F (a + b * x - target x) x := by
    intro x
    dsimp [F]
    have h :=
      (((hasDerivAt_id x).const_mul a).add
        (((hasDerivAt_id x).pow 2).const_mul b |>.div_const 2)).sub
          (hasDerivAt_sqrtAntiderivative x)
    convert h using 1 <;> simp [id_eq] <;> unfold target <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hF x)
    ((by
      unfold target
      fun_prop : Continuous
        (fun x : ℝ => a + b * x - target x)).intervalIntegrable 0 1)]
  dsimp [F, sqrtAntiderivative, Real.arsinh]
  norm_num
  ring

private lemma weighted_residual_integral_formula (a b : ℝ) :
    2 * (∫ x in (0 : ℝ)..1, x * (a + b * x - target x)) =
      a + (2 / 3 : ℝ) * b -
        (2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1) := by
  let F : ℝ → ℝ :=
    fun x => a * x ^ 2 / 2 + b * x ^ 3 / 3 -
      weightedSqrtAntiderivative x
  have hF : ∀ x : ℝ,
      HasDerivAt F (x * (a + b * x - target x)) x := by
    intro x
    dsimp [F]
    have h :=
      ((((hasDerivAt_id x).pow 2).const_mul a |>.div_const 2).add
        (((hasDerivAt_id x).pow 3).const_mul b |>.div_const 3)).sub
          (hasDerivAt_weightedSqrtAntiderivative x)
    convert h using 1 <;> simp [id_eq] <;> unfold target <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hF x)
    ((by
      unfold target
      fun_prop : Continuous
        (fun x : ℝ => x * (a + b * x - target x))).intervalIntegrable 0 1)]
  dsimp [F, weightedSqrtAntiderivative]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg 2
  norm_num
  nlinarith

private lemma sqrt_two_bounds :
    (1414213 / 1000000 : ℝ) < Real.sqrt 2 ∧
      Real.sqrt 2 < (1414214 / 1000000 : ℝ) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg 2
  constructor <;> nlinarith

private lemma log_one_add_sqrt_two_bounds :
    (8813 / 10000 : ℝ) < Real.log (1 + Real.sqrt 2) ∧
      Real.log (1 + Real.sqrt 2) < (8814 / 10000 : ℝ) := by
  let x : ℝ := Real.sqrt 2 - 1
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg 2
  have hslo := sqrt_two_bounds.1
  have hshi := sqrt_two_bounds.2
  have hx0 : 0 ≤ x := by
    dsimp [x]
    nlinarith
  have hx1 : x < 1 := by
    dsimp [x]
    nlinarith
  have hratio : (1 + x) / (1 - x) = 1 + Real.sqrt 2 := by
    dsimp [x]
    rw [div_eq_iff (by nlinarith : 1 - (Real.sqrt 2 - 1) ≠ 0)]
    nlinarith
  constructor
  · have hseries := Real.sum_range_le_log_div hx0 hx1 6
    rw [hratio] at hseries
    let r : ℝ := 4142 / 10000
    have hr0 : 0 ≤ r := by norm_num [r]
    have hrx : r ≤ x := by
      dsimp [r, x]
      linarith
    have hmono :
        (∑ i ∈ Finset.range 6,
            r ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) ≤
          ∑ i ∈ Finset.range 6,
            x ^ (2 * i + 1) / (2 * (i : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr
    have hrat :
        (8813 / 20000 : ℝ) <
          ∑ i ∈ Finset.range 6,
            r ^ (2 * i + 1) / (2 * (i : ℝ) + 1) := by
      norm_num [r, Finset.sum_range_succ]
    nlinarith
  · have hseries := Real.log_div_le_sum_range_add hx0 hx1 6
    rw [hratio] at hseries
    let r : ℝ := 414214 / 1000000
    have hr0 : 0 ≤ r := by norm_num [r]
    have hr1 : r < 1 := by norm_num [r]
    have hxr : x ≤ r := by
      dsimp [r, x]
      linarith
    have hmono :
        (∑ i ∈ Finset.range 6,
            x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) ≤
          ∑ i ∈ Finset.range 6,
            r ^ (2 * i + 1) / (2 * (i : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr
    have herr :
        x ^ (2 * 6 + 1) / (1 - x ^ 2) ≤
          r ^ (2 * 6 + 1) / (1 - r ^ 2) := by
      gcongr
    have hrat :
        (∑ i ∈ Finset.range 6,
            r ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) +
            r ^ (2 * 6 + 1) / (1 - r ^ 2) <
          (8814 / 20000 : ℝ) := by
      norm_num [r, Finset.sum_range_succ]
    nlinarith

theorem gap1 (p : ℝ × ℝ) :
    ∃ r : ℝ, r = radius p ∧ r = Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := by
  exact ⟨radius p, rfl, rfl⟩

theorem gap2 (p : ℕ → ℝ × ℝ)
    (hp : Tendsto (fun n => ‖p n‖) atTop atTop) :
    Tendsto (fun n => radius (p n)) atTop atTop := by
  apply tendsto_atTop_mono (fun n => ?_) hp
  simp only [Prod.norm_def, radius, Real.norm_eq_abs]
  rw [max_le_iff]
  have hs : 0 ≤ (p n).1 ^ 2 + (p n).2 ^ 2 := by positivity
  have hsqrt := Real.sq_sqrt hs
  have hsqrt0 := Real.sqrt_nonneg ((p n).1 ^ 2 + (p n).2 ^ 2)
  constructor
  · have ha : |(p n).1| ^ 2 ≤ (p n).1 ^ 2 + (p n).2 ^ 2 := by
      rw [sq_abs]
      exact le_add_of_nonneg_right (sq_nonneg (p n).2)
    nlinarith [sq_nonneg
      (|(p n).1| + Real.sqrt ((p n).1 ^ 2 + (p n).2 ^ 2))]
  · have hb : |(p n).2| ^ 2 ≤ (p n).1 ^ 2 + (p n).2 ^ 2 := by
      rw [sq_abs]
      exact le_add_of_nonneg_left (sq_nonneg (p n).1)
    nlinarith [sq_nonneg
      (|(p n).2| + Real.sqrt ((p n).1 ^ 2 + (p n).2 ^ 2))]

theorem gap3 :
    Tendsto (fun r : ℝ => r) atTop atTop := by
  exact tendsto_id

theorem gap4 :
    IsCoercive objective := by
  intro p hp
  rw [tendsto_atTop] at hp ⊢
  intro C
  let K : ℝ := |optimalA| + |optimalB|
  let M : ℝ := max C 0 + 1
  filter_upwards [hp (2 * (12 * M) + K)] with n hn
  let c : ℝ := (p n).1 - optimalA + ((p n).2 - optimalB) / 2
  let d : ℝ := (p n).2 - optimalB
  let m : ℝ := max |c| |d|
  have hm0 : 0 ≤ m :=
    (abs_nonneg c).trans (le_max_left _ _)
  have hc : |c| ≤ m := le_max_left _ _
  have hd : |d| ≤ m := le_max_right _ _
  have haeq : (p n).1 = c - d / 2 + optimalA := by
    dsimp [c, d]
    ring
  have hbeq : (p n).2 = d + optimalB := by
    dsimp [d]
    ring
  have haabs : |(p n).1| ≤ 2 * m + |optimalA| := by
    rw [haeq]
    calc
      |c - d / 2 + optimalA| ≤ |c - d / 2| + |optimalA| :=
        abs_add_le _ _
      _ ≤ (|c| + |d / 2|) + |optimalA| := by
        gcongr
        exact abs_sub _ _
      _ ≤ 2 * m + |optimalA| := by
        rw [abs_div]
        norm_num
        nlinarith
  have hbabs : |(p n).2| ≤ 2 * m + |optimalB| := by
    rw [hbeq]
    calc
      |d + optimalB| ≤ |d| + |optimalB| := abs_add_le _ _
      _ ≤ 2 * m + |optimalB| := by nlinarith
  have hnorm : ‖p n‖ ≤ 2 * m + K := by
    simp only [Prod.norm_def, Real.norm_eq_abs]
    dsimp [K]
    apply max_le
    · nlinarith [abs_nonneg optimalB]
    · nlinarith [abs_nonneg optimalA]
  have hmLower : 12 * M ≤ m := by
    nlinarith
  have hm_sq : m ^ 2 ≤ c ^ 2 + d ^ 2 := by
    dsimp [m]
    rcases le_total |c| |d| with hcd | hdc
    · rw [max_eq_right hcd, sq_abs]
      exact le_add_of_nonneg_left (sq_nonneg c)
    · rw [max_eq_left hdc, sq_abs]
      exact le_add_of_nonneg_right (sq_nonneg d)
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg (le_max_right _ _) zero_le_one
  have hM1 : 1 ≤ M := by
    dsimp [M]
    linarith [le_max_right C 0]
  have hCM : C ≤ M := by
    dsimp [M]
    linarith [le_max_left C 0]
  have hopt : 0 ≤ objective optimalPair := by
    unfold objective
    exact intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (fun _ => sq_nonneg _)
  have hmLower_sq : (12 * M) ^ 2 ≤ m ^ 2 := by
    nlinarith [sq_nonneg (m + 12 * M)]
  have hm12 : m ^ 2 / 12 ≤ c ^ 2 + d ^ 2 / 12 := by
    nlinarith [sq_nonneg c, sq_nonneg d]
  have hM_m12 : M ≤ m ^ 2 / 12 := by
    nlinarith [sq_nonneg M]
  rw [objective_centered]
  change C ≤
    objective optimalPair + c ^ 2 + d ^ 2 / 12
  linarith

theorem gap5 (a b : ℝ) :
    partialA (a, b) =
      2 * ∫ x in (0 : ℝ)..1, (a + b * x - target x) := by
  rw [partialA]
  have hderiv :
      HasDerivAt
        (fun t : ℝ =>
          t ^ 2 + t * b + b ^ 2 / 3 -
            t * (Real.sqrt 2 + Real.log (1 + Real.sqrt 2)) -
            b * ((2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1)) +
            4 / 3)
        (2 * a + b -
          (Real.sqrt 2 + Real.log (1 + Real.sqrt 2))) a := by
    have h :=
      (((((hasDerivAt_id a).pow 2).add
        ((hasDerivAt_id a).const_mul b)).add
          (hasDerivAt_const a
            (b ^ 2 / 3))).sub
              ((hasDerivAt_id a).const_mul
                (Real.sqrt 2 + Real.log (1 + Real.sqrt 2)))).add
                  (hasDerivAt_const a
                    (-b * ((2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1)) +
                      4 / 3))
    convert h using 1
    · funext t
      simp [id_eq]
      ring
    · simp [id_eq]
  rw [show (fun t : ℝ => objective (t, b)) =
      fun t : ℝ =>
        t ^ 2 + t * b + b ^ 2 / 3 -
          t * (Real.sqrt 2 + Real.log (1 + Real.sqrt 2)) -
          b * ((2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1)) +
          4 / 3 by
        funext t
        exact objective_formula t b]
  rw [hderiv.deriv, residual_integral_formula]

theorem gap6 (a b : ℝ) :
    2 * (∫ x in (0 : ℝ)..1, (a + b * x - target x)) =
      2 * a + b - (Real.sqrt 2 + Real.log (1 + Real.sqrt 2)) := by
  exact residual_integral_formula a b

theorem gap7 (a b : ℝ) (hmin : IsMinimizer (a, b)) :
    2 * a + b - (Real.sqrt 2 + Real.log (1 + Real.sqrt 2)) = 0 := by
  let e : ℝ :=
    2 * a + b - (Real.sqrt 2 + Real.log (1 + Real.sqrt 2))
  have hstep := hmin (a - e / 2, b)
  rw [objective_formula, objective_formula] at hstep
  dsimp [e] at hstep
  nlinarith

theorem gap8 (a b : ℝ) (hmin : IsMinimizer (a, b)) :
    partialA (a, b) = 0 := by
  rw [gap5, gap6]
  exact gap7 a b hmin

theorem gap9 (a b : ℝ) :
    partialB (a, b) =
      2 * ∫ x in (0 : ℝ)..1, x * (a + b * x - target x) := by
  rw [partialB]
  have hderiv :
      HasDerivAt
        (fun t : ℝ =>
          a ^ 2 + a * t + t ^ 2 / 3 -
            a * (Real.sqrt 2 + Real.log (1 + Real.sqrt 2)) -
            t * ((2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1)) +
            4 / 3)
        (a + (2 / 3 : ℝ) * b -
          (2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1)) b := by
    have h :=
      ((((hasDerivAt_const b
        (a ^ 2 - a *
          (Real.sqrt 2 + Real.log (1 + Real.sqrt 2)) + 4 / 3)).add
            ((hasDerivAt_id b).const_mul a)).add
              (((hasDerivAt_id b).pow 2).div_const 3)).sub
                ((hasDerivAt_id b).const_mul
                  ((2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1))))
    convert h using 1
    · funext t
      simp [id_eq]
      ring
    · simp [id_eq]
      ring
  rw [show (fun t : ℝ => objective (a, t)) =
      fun t : ℝ =>
        a ^ 2 + a * t + t ^ 2 / 3 -
          a * (Real.sqrt 2 + Real.log (1 + Real.sqrt 2)) -
          t * ((2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1)) +
          4 / 3 by
        funext t
        exact objective_formula a t]
  rw [hderiv.deriv, weighted_residual_integral_formula]

theorem gap10 (a b : ℝ) :
    2 * (∫ x in (0 : ℝ)..1, x * (a + b * x - target x)) =
      a + (2 / 3 : ℝ) * b - (2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1) := by
  exact weighted_residual_integral_formula a b

theorem gap11 (a b : ℝ) (hmin : IsMinimizer (a, b)) :
    a + (2 / 3 : ℝ) * b - (2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1) = 0 := by
  let e : ℝ :=
    a + (2 / 3 : ℝ) * b -
      (2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1)
  have hstep := hmin (a, b - (3 / 2 : ℝ) * e)
  rw [objective_formula, objective_formula] at hstep
  dsimp [e] at hstep
  nlinarith

theorem gap12 (a b : ℝ) (hmin : IsMinimizer (a, b)) :
    partialB (a, b) = 0 := by
  rw [gap9, gap10]
  exact gap11 a b hmin

theorem gap13 (a b : ℝ) (hmin : IsMinimizer (a, b)) :
    Approx a 0.934 0.001 := by
  have ha := gap7 a b hmin
  have hb := gap11 a b hmin
  have haeq : a = optimalA := by
    unfold optimalA
    linarith
  rw [haeq]
  unfold Approx optimalA
  rw [abs_lt]
  have hslo := sqrt_two_bounds.1
  have hshi := sqrt_two_bounds.2
  have hllo := log_one_add_sqrt_two_bounds.1
  have hlhi := log_one_add_sqrt_two_bounds.2
  constructor <;> norm_num at * <;> linarith

theorem gap14 (a b : ℝ) (hmin : IsMinimizer (a, b)) :
    Approx b 0.427 0.001 := by
  have ha := gap7 a b hmin
  have hb := gap11 a b hmin
  have hbeq : b = optimalB := by
    unfold optimalB
    linarith
  rw [hbeq]
  unfold Approx optimalB
  rw [abs_lt]
  have hslo := sqrt_two_bounds.1
  have hshi := sqrt_two_bounds.2
  have hllo := log_one_add_sqrt_two_bounds.1
  have hlhi := log_one_add_sqrt_two_bounds.2
  constructor <;> norm_num at * <;> linarith

theorem gap15 :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Approx (target x) (0.934 + 0.427 * x) 0.067 := by
  intro x hx
  unfold Approx
  rw [abs_lt]
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have ht0 : 0 ≤ target x := by
    unfold target
    positivity
  have htsq : target x ^ 2 = 1 + x ^ 2 := by
    unfold target
    exact Real.sq_sqrt (by positivity)
  constructor
  · have hline0 : 0 ≤ (867 / 1000 : ℝ) + (427 / 1000 : ℝ) * x := by
      positivity
    have hpoly :
        ((867 / 1000 : ℝ) + (427 / 1000 : ℝ) * x) ^ 2 <
          1 + x ^ 2 := by
      nlinarith [sq_nonneg (x - (453 / 1000 : ℝ))]
    norm_num at *
    nlinarith [sq_nonneg
      (target x + ((867 / 1000 : ℝ) + (427 / 1000 : ℝ) * x))]
  · have hline0 : 0 ≤ (1001 / 1000 : ℝ) + (427 / 1000 : ℝ) * x := by
      positivity
    have hpoly :
        1 + x ^ 2 <
          ((1001 / 1000 : ℝ) + (427 / 1000 : ℝ) * x) ^ 2 := by
      nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
    norm_num at *
    nlinarith [sq_nonneg
      (target x + ((1001 / 1000 : ℝ) + (427 / 1000 : ℝ) * x))]

theorem gap16 (a b : ℝ)
    (hp : (a, b) ∈ ({optimalPair} : Set (ℝ × ℝ))) :
    IsMinimizer (a, b) := by
  simp only [Set.mem_singleton_iff] at hp
  rcases Prod.ext_iff.mp hp with ⟨ha, hb⟩
  change a = optimalA at ha
  change b = optimalB at hb
  subst a
  subst b
  intro q
  change objective optimalPair ≤ objective q
  have hq :
      objective q =
        objective optimalPair +
          (q.1 - optimalA + (q.2 - optimalB) / 2) ^ 2 +
          (q.2 - optimalB) ^ 2 / 12 := by
    simpa only [Prod.eta] using objective_centered q.1 q.2
  rw [hq]
  nlinarith [sq_nonneg
    (q.1 - optimalA + (q.2 - optimalB) / 2),
    sq_nonneg (q.2 - optimalB)]

end

end ProofGap.Exercise3724
