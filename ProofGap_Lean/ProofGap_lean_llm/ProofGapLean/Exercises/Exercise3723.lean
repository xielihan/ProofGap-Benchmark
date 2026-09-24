import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3723

noncomputable section

open Filter
open scoped Interval Topology

def objective (p : ℝ × ℝ) : ℝ :=
  ∫ x in (1 : ℝ)..3, (p.1 + p.2 * x - x ^ 2) ^ 2

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

def optimalPair : ℝ × ℝ :=
  (-(11 / 3 : ℝ), 4)

private theorem hasDerivAt_quintic
    (c0 c1 c2 c3 c4 c5 x : ℝ) :
    HasDerivAt
      (fun t : ℝ => c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 +
        c4 * t ^ 4 + c5 * t ^ 5)
      (c1 + 2 * c2 * x + 3 * c3 * x ^ 2 +
        4 * c4 * x ^ 3 + 5 * c5 * x ^ 4) x := by
  have h0 := hasDerivAt_const x c0
  have h1 := (hasDerivAt_id x).const_mul c1
  have h2 := ((hasDerivAt_id x).pow 2).const_mul c2
  have h3 := ((hasDerivAt_id x).pow 3).const_mul c3
  have h4 := ((hasDerivAt_id x).pow 4).const_mul c4
  have h5 := ((hasDerivAt_id x).pow 5).const_mul c5
  have h := ((((h0.add h1).add h2).add h3).add h4).add h5
  convert h using 1
  · simp only [id_eq]
    ring

private theorem objective_formula (a b : ℝ) :
    objective (a, b) =
      2 * a ^ 2 + 8 * a * b + (26 / 3) * b ^ 2 -
        (52 / 3) * a - 40 * b + 242 / 5 := by
  unfold objective
  let F : ℝ → ℝ := fun x =>
    a ^ 2 * x + a * b * x ^ 2 - (2 * a / 3) * x ^ 3 +
      (b ^ 2 / 3) * x ^ 3 - (b / 2) * x ^ 4 + x ^ 5 / 5
  have hF : ∀ x : ℝ,
      HasDerivAt F ((a + b * x - x ^ 2) ^ 2) x := by
    intro x
    dsimp [F]
    convert hasDerivAt_quintic 0 (a ^ 2) (a * b)
      (-(2 * a / 3) + b ^ 2 / 3) (-(b / 2)) (1 / 5) x using 1
    · funext t
      ring
    · ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hF x) ((by fun_prop : Continuous
      (fun x : ℝ => (a + b * x - x ^ 2) ^ 2)).intervalIntegrable 1 3)]
  dsimp [F]
  norm_num
  ring

private theorem objective_centered (a b : ℝ) :
    objective (a, b) =
      (8 / 45 : ℝ) +
        2 * (a + 11 / 3 + 2 * (b - 4)) ^ 2 +
        (2 / 3) * (b - 4) ^ 2 := by
  rw [objective_formula]
  ring

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
    nlinarith [sq_nonneg (|(p n).1| + Real.sqrt ((p n).1 ^ 2 + (p n).2 ^ 2))]
  · have hb : |(p n).2| ^ 2 ≤ (p n).1 ^ 2 + (p n).2 ^ 2 := by
      rw [sq_abs]
      exact le_add_of_nonneg_left (sq_nonneg (p n).1)
    nlinarith [sq_nonneg (|(p n).2| + Real.sqrt ((p n).1 ^ 2 + (p n).2 ^ 2))]

theorem gap3 :
    Tendsto (fun r : ℝ => r) atTop atTop := by
  exact tendsto_id

theorem gap4 :
    IsCoercive objective := by
  intro p hp
  rw [tendsto_atTop] at hp ⊢
  intro C
  filter_upwards [hp (3 * (max C 0 + 1) + 4)] with n hn
  let c : ℝ := (p n).1 + 11 / 3 + 2 * ((p n).2 - 4)
  let d : ℝ := (p n).2 - 4
  let m : ℝ := max |c| |d|
  have hm0 : 0 ≤ m := by
    exact le_trans (abs_nonneg c) (le_max_left _ _)
  have hc : |c| ≤ m := le_max_left _ _
  have hd : |d| ≤ m := le_max_right _ _
  have haeq : (p n).1 = c - 2 * d - 11 / 3 := by
    dsimp [c, d]
    ring
  have hbeq : (p n).2 = d + 4 := by
    dsimp [d]
    ring
  have haabs : |(p n).1| ≤ 3 * m + 4 := by
    rw [haeq]
    calc
      |c - 2 * d - 11 / 3| ≤ |c - 2 * d| + |(11 / 3 : ℝ)| := abs_sub _ _
      _ ≤ |c| + |2 * d| + |(11 / 3 : ℝ)| := by
        gcongr
        exact abs_sub c (2 * d)
      _ ≤ 3 * m + 4 := by
        rw [abs_mul]
        norm_num
        nlinarith
  have hbabs : |(p n).2| ≤ 3 * m + 4 := by
    rw [hbeq]
    calc
      |d + 4| ≤ |d| + |(4 : ℝ)| := abs_add_le _ _
      _ ≤ 3 * m + 4 := by
        norm_num
        nlinarith
  have hnorm : ‖p n‖ ≤ 3 * m + 4 := by
    simp only [Prod.norm_def, Real.norm_eq_abs]
    exact max_le haabs hbabs
  have hmLower : max C 0 + 1 ≤ m := by
    nlinarith
  have hm_sq : m ^ 2 ≤ c ^ 2 + d ^ 2 := by
    dsimp [m]
    rcases le_total |c| |d| with hcd | hdc
    · rw [max_eq_right hcd, sq_abs]
      exact le_add_of_nonneg_left (sq_nonneg c)
    · rw [max_eq_left hdc, sq_abs]
      exact le_add_of_nonneg_right (sq_nonneg d)
  have hbase0 : 0 ≤ max C 0 := le_max_right _ _
  have hCbase : C ≤ max C 0 := le_max_left _ _
  have hthreshold_sq : (max C 0 + 1) ^ 2 ≤ m ^ 2 := by
    nlinarith [sq_nonneg (m + (max C 0 + 1))]
  have hC_sq : (3 / 2 : ℝ) * C ≤ (max C 0 + 1) ^ 2 := by
    nlinarith [sq_nonneg (max C 0)]
  rw [objective_centered]
  change C ≤
    8 / 45 + 2 * c ^ 2 + (2 / 3) * d ^ 2
  nlinarith [sq_nonneg c, sq_nonneg d]

theorem gap5 (a b : ℝ) :
    partialA (a, b) =
      2 * ∫ x in (1 : ℝ)..3, (a + b * x - x ^ 2) := by
  rw [partialA]
  have hderiv :
      HasDerivAt
        (fun t : ℝ =>
          2 * t ^ 2 + 8 * t * b + (26 / 3) * b ^ 2 -
            (52 / 3) * t - 40 * b + 242 / 5)
        (4 * a + 8 * b - 52 / 3) a := by
    convert hasDerivAt_quintic
      ((26 / 3) * b ^ 2 - 40 * b + 242 / 5)
      (8 * b - 52 / 3) 2 0 0 0 a using 1
    · funext t
      ring
    · ring
  rw [show (fun t : ℝ => objective (t, b)) =
      fun t => 2 * t ^ 2 + 8 * t * b + (26 / 3) * b ^ 2 -
        (52 / 3) * t - 40 * b + 242 / 5 by
      funext t
      exact objective_formula t b]
  rw [hderiv.deriv]
  let F : ℝ → ℝ := fun x => a * x + b * x ^ 2 / 2 - x ^ 3 / 3
  have hF : ∀ x : ℝ, HasDerivAt F (a + b * x - x ^ 2) x := by
    intro x
    dsimp [F]
    convert hasDerivAt_quintic 0 a (b / 2) (-(1 / 3)) 0 0 x using 1
    · funext t
      ring
    · ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hF x) ((by fun_prop : Continuous
      (fun x : ℝ => a + b * x - x ^ 2)).intervalIntegrable 1 3)]
  dsimp [F]
  norm_num
  ring

theorem gap6 (a b : ℝ) :
    2 * (∫ x in (1 : ℝ)..3, (a + b * x - x ^ 2)) =
      4 * a + 8 * b - 52 / 3 := by
  let F : ℝ → ℝ := fun x => a * x + b * x ^ 2 / 2 - x ^ 3 / 3
  have hF : ∀ x : ℝ, HasDerivAt F (a + b * x - x ^ 2) x := by
    intro x
    dsimp [F]
    convert hasDerivAt_quintic 0 a (b / 2) (-(1 / 3)) 0 0 x using 1
    · funext t
      ring
    · ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hF x) ((by fun_prop : Continuous
      (fun x : ℝ => a + b * x - x ^ 2)).intervalIntegrable 1 3)]
  dsimp [F]
  norm_num
  ring

theorem gap7 (a b : ℝ) (hmin : IsMinimizer (a, b)) :
    4 * a + 8 * b - 52 / 3 = 0 := by
  have hstep := hmin (a - (4 * a + 8 * b - 52 / 3) / 4, b)
  rw [objective_formula, objective_formula] at hstep
  nlinarith

theorem gap8 (a b : ℝ) (hmin : IsMinimizer (a, b)) :
    partialA (a, b) = 0 := by
  rw [gap5, gap6]
  exact gap7 a b hmin

theorem gap9 (a b : ℝ) :
    partialB (a, b) =
      2 * ∫ x in (1 : ℝ)..3, x * (a + b * x - x ^ 2) := by
  rw [partialB]
  have hderiv :
      HasDerivAt
        (fun t : ℝ =>
          2 * a ^ 2 + 8 * a * t + (26 / 3) * t ^ 2 -
            (52 / 3) * a - 40 * t + 242 / 5)
        (8 * a + (52 / 3) * b - 40) b := by
    convert hasDerivAt_quintic
      (2 * a ^ 2 - (52 / 3) * a + 242 / 5)
      (8 * a - 40) (26 / 3) 0 0 0 b using 1
    · funext t
      ring
    · ring
  rw [show (fun t : ℝ => objective (a, t)) =
      fun t => 2 * a ^ 2 + 8 * a * t + (26 / 3) * t ^ 2 -
        (52 / 3) * a - 40 * t + 242 / 5 by
      funext t
      exact objective_formula a t]
  rw [hderiv.deriv]
  let F : ℝ → ℝ := fun x => a * x ^ 2 / 2 + b * x ^ 3 / 3 - x ^ 4 / 4
  have hF : ∀ x : ℝ, HasDerivAt F (x * (a + b * x - x ^ 2)) x := by
    intro x
    dsimp [F]
    convert hasDerivAt_quintic 0 0 (a / 2) (b / 3) (-(1 / 4)) 0 x using 1
    · funext t
      ring
    · ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hF x) ((by fun_prop : Continuous
      (fun x : ℝ => x * (a + b * x - x ^ 2))).intervalIntegrable 1 3)]
  dsimp [F]
  norm_num
  ring

theorem gap10 (a b : ℝ) :
    2 * (∫ x in (1 : ℝ)..3, x * (a + b * x - x ^ 2)) =
      8 * a + (52 / 3) * b - 40 := by
  let F : ℝ → ℝ := fun x => a * x ^ 2 / 2 + b * x ^ 3 / 3 - x ^ 4 / 4
  have hF : ∀ x : ℝ, HasDerivAt F (x * (a + b * x - x ^ 2)) x := by
    intro x
    dsimp [F]
    convert hasDerivAt_quintic 0 0 (a / 2) (b / 3) (-(1 / 4)) 0 x using 1
    · funext t
      ring
    · ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hF x) ((by fun_prop : Continuous
      (fun x : ℝ => x * (a + b * x - x ^ 2))).intervalIntegrable 1 3)]
  dsimp [F]
  norm_num
  ring

theorem gap11 (a b : ℝ) (hmin : IsMinimizer (a, b)) :
    8 * a + (52 / 3) * b - 40 = 0 := by
  have hstep := hmin (a, b - (3 / 52) * (8 * a + (52 / 3) * b - 40))
  rw [objective_formula, objective_formula] at hstep
  nlinarith

theorem gap12 (a b : ℝ) (hmin : IsMinimizer (a, b)) :
    partialB (a, b) = 0 := by
  rw [gap9, gap10]
  exact gap11 a b hmin

theorem gap13 (a b : ℝ) (hmin : IsMinimizer (a, b)) :
    a = -(11 / 3 : ℝ) := by
  have ha := gap7 a b hmin
  have hb := gap11 a b hmin
  linarith

theorem gap14 (a b : ℝ) (hmin : IsMinimizer (a, b)) :
    b = 4 := by
  have ha := gap7 a b hmin
  have hb := gap11 a b hmin
  linarith

theorem gap15 (a b : ℝ) (hp : (a, b) ∈ ({optimalPair} : Set (ℝ × ℝ))) :
    IsMinimizer (a, b) := by
  simp only [Set.mem_singleton_iff] at hp
  rcases Prod.ext_iff.mp hp with ⟨ha, hb⟩
  change a = -(11 / 3 : ℝ) at ha
  change b = 4 at hb
  subst a
  subst b
  intro q
  rw [objective_centered, objective_centered]
  norm_num
  nlinarith [sq_nonneg (q.1 + 11 / 3 + 2 * (q.2 - 4)),
    sq_nonneg (q.2 - 4)]

end

end ProofGap.Exercise3723
