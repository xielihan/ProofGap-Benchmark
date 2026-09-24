import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3632

noncomputable section

def quadraticPart (p : ℝ × ℝ) : ℝ :=
  8 * p.1 ^ 2 - 6 * p.1 * p.2 + 3 * p.2 ^ 2

def z (p : ℝ × ℝ) : ℝ :=
  Real.exp (2 * p.1 + 3 * p.2) * quadraticPart p

def partialX (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => g (x, p.2)) p.1

def partialY (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => g (p.1, y)) p.2

def partialXX (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => partialX g (x, p.2)) p.1

def partialXY (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => partialX g (p.1, y)) p.2

def partialYY (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => partialY g (p.1, y)) p.2

def p₀ : ℝ × ℝ :=
  (0, 0)

def p₁ : ℝ × ℝ :=
  (-(1 / 4 : ℝ), -(1 / 2 : ℝ))

def criticalPoints : Set (ℝ × ℝ) :=
  {p₀, p₁}

def hessianA (p : ℝ × ℝ) : ℝ :=
  partialXX z p

def hessianB (p : ℝ × ℝ) : ℝ :=
  partialXY z p

def hessianC (p : ℝ × ℝ) : ℝ :=
  partialYY z p

def hessianDiscriminant (p : ℝ × ℝ) : ℝ :=
  hessianA p * hessianC p - hessianB p ^ 2

def IsLocalMinimum
    (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ q : ℝ × ℝ, ‖q - p‖ < ε → g p ≤ g q

def IsLocalMaximum
    (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ q : ℝ × ℝ, ‖q - p‖ < ε → g q ≤ g p

def IsUniqueGlobalMinimizer
    (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Prop :=
  (∀ q, g p ≤ g q) ∧ (∀ q, g q = g p → q = p)

private theorem hasDerivAt_quadratic_x (x y : ℝ) :
    HasDerivAt (fun t : ℝ => quadraticPart (t, y)) (16 * x - 6 * y) x := by
  convert
    (((((hasDerivAt_id x).mul (hasDerivAt_id x)).const_mul 8).sub
      (((hasDerivAt_id x).mul (hasDerivAt_const x y)).const_mul 6)).add_const
        (3 * y ^ 2)) using 1 <;>
    first
    | (funext t; dsimp [quadraticPart]; ring_nf)
    | (dsimp; ring_nf)

private theorem hasDerivAt_quadratic_y (x y : ℝ) :
    HasDerivAt (fun t : ℝ => quadraticPart (x, t)) (-6 * x + 6 * y) y := by
  convert
    (((hasDerivAt_const y (8 * x ^ 2)).sub
      ((hasDerivAt_id y).const_mul (6 * x))).add
        (((hasDerivAt_id y).mul (hasDerivAt_id y)).const_mul 3)) using 1 <;>
    first
    | (funext t; dsimp [quadraticPart]; ring_nf)
    | (dsimp; ring_nf)

private theorem hasDerivAt_expLinear_x (x y : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (2 * t + 3 * y))
      (2 * Real.exp (2 * x + 3 * y)) x := by
  have hi : HasDerivAt (fun t : ℝ => 2 * t + 3 * y) 2 x := by
    convert ((hasDerivAt_id x).const_mul 2).add_const (3 * y) using 1 <;> ring
  convert (Real.hasDerivAt_exp (2 * x + 3 * y)).comp x hi using 1 <;> ring

private theorem hasDerivAt_expLinear_y (x y : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (2 * x + 3 * t))
      (3 * Real.exp (2 * x + 3 * y)) y := by
  have hi : HasDerivAt (fun t : ℝ => 2 * x + 3 * t) 3 y := by
    convert (hasDerivAt_const y (2 * x)).add ((hasDerivAt_id y).const_mul 3) using 1 <;> ring
  convert (Real.hasDerivAt_exp (2 * x + 3 * y)).comp y hi using 1 <;> ring

private theorem hasDerivAt_z_x (x y : ℝ) :
    HasDerivAt (fun t : ℝ => z (t, y))
      (2 * Real.exp (2 * x + 3 * y) *
        (quadraticPart (x, y) + 8 * x - 3 * y)) x := by
  convert (hasDerivAt_expLinear_x x y).mul (hasDerivAt_quadratic_x x y) using 1 <;>
    first
    | (funext t; dsimp [z]; ring_nf)
    | ring_nf

private theorem hasDerivAt_z_y (x y : ℝ) :
    HasDerivAt (fun t : ℝ => z (x, t))
      (3 * Real.exp (2 * x + 3 * y) *
        (quadraticPart (x, y) - 2 * x + 2 * y)) y := by
  convert (hasDerivAt_expLinear_y x y).mul (hasDerivAt_quadratic_y x y) using 1 <;>
    first
    | (funext t; dsimp [z]; ring_nf)
    | ring_nf

private theorem partialX_z_formula (p : ℝ × ℝ) :
    partialX z p =
      2 * Real.exp (2 * p.1 + 3 * p.2) *
        (quadraticPart p + 8 * p.1 - 3 * p.2) := by
  simpa [partialX] using (hasDerivAt_z_x p.1 p.2).deriv

private theorem partialY_z_formula (p : ℝ × ℝ) :
    partialY z p =
      3 * Real.exp (2 * p.1 + 3 * p.2) *
        (quadraticPart p - 2 * p.1 + 2 * p.2) := by
  simpa [partialY] using (hasDerivAt_z_y p.1 p.2).deriv

private theorem hasDerivAt_partialX_formula (x y : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        2 * Real.exp (2 * t + 3 * y) *
          (quadraticPart (t, y) + 8 * t - 3 * y))
      (4 * Real.exp (2 * x + 3 * y) *
        (quadraticPart (x, y) + 16 * x - 6 * y + 4)) x := by
  have hr :
      HasDerivAt
        (fun t : ℝ => quadraticPart (t, y) + 8 * t - 3 * y)
        (16 * x - 6 * y + 8) x := by
    convert (hasDerivAt_quadratic_x x y).add
      (((hasDerivAt_id x).const_mul 8).sub_const (3 * y)) using 1 <;>
      first
      | (funext t; dsimp [quadraticPart]; ring_nf)
      | ring_nf
  convert ((hasDerivAt_expLinear_x x y).mul hr).const_mul 2 using 1 <;>
    first
    | (funext t; dsimp [quadraticPart]; ring_nf)
    | ring_nf

private theorem hasDerivAt_partialY_formula_y (x y : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        3 * Real.exp (2 * x + 3 * t) *
          (quadraticPart (x, t) - 2 * x + 2 * t))
      (9 * Real.exp (2 * x + 3 * y) *
        (quadraticPart (x, y) - 4 * x + 4 * y + (2 / 3 : ℝ))) y := by
  have hr :
      HasDerivAt
        (fun t : ℝ => quadraticPart (x, t) - 2 * x + 2 * t)
        (-6 * x + 6 * y + 2) y := by
    convert (hasDerivAt_quadratic_y x y).add
      ((hasDerivAt_const y (-2 * x)).add ((hasDerivAt_id y).const_mul 2)) using 1 <;>
      first
      | (funext t; dsimp [quadraticPart]; ring_nf)
      | ring_nf
  convert ((hasDerivAt_expLinear_y x y).mul hr).const_mul 3 using 1 <;>
    first
    | (funext t; dsimp [quadraticPart]; ring_nf)
    | ring_nf

private theorem hasDerivAt_partialX_formula_y (x y : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        2 * Real.exp (2 * x + 3 * t) *
          (quadraticPart (x, t) + 8 * x - 3 * t))
      (6 * Real.exp (2 * x + 3 * y) *
        (quadraticPart (x, y) + 6 * x - y - 1)) y := by
  have hr :
      HasDerivAt
        (fun t : ℝ => quadraticPart (x, t) + 8 * x - 3 * t)
        (-6 * x + 6 * y - 3) y := by
    convert (hasDerivAt_quadratic_y x y).add
      ((hasDerivAt_const y (8 * x)).sub ((hasDerivAt_id y).const_mul 3)) using 1 <;>
      first
      | (funext t; dsimp [quadraticPart]; ring_nf)
      | ring_nf
  convert ((hasDerivAt_expLinear_y x y).mul hr).const_mul 2 using 1 <;>
    first
    | (funext t; dsimp [quadraticPart]; ring_nf)
    | ring_nf

private theorem quadraticPart_nonneg (p : ℝ × ℝ) : 0 ≤ quadraticPart p := by
  have hident :
      quadraticPart p = 5 * p.1 ^ 2 + 3 * (p.1 - p.2) ^ 2 := by
    simp [quadraticPart]
    ring
  rw [hident]
  exact add_nonneg
    (mul_nonneg (by norm_num) (sq_nonneg p.1))
    (mul_nonneg (by norm_num) (sq_nonneg (p.1 - p.2)))

private theorem quadraticPart_eq_zero (p : ℝ × ℝ)
    (h : quadraticPart p = 0) : p = p₀ := by
  rcases p with ⟨x, y⟩
  have hident :
      quadraticPart (x, y) = 5 * x ^ 2 + 3 * (x - y) ^ 2 := by
    simp [quadraticPart]
    ring
  rw [hident] at h
  have hx : x = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg (x - y)]
  have hy : y = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg (x - y)]
  simp [hx, hy, p₀]

private theorem z_at_p₁ :
    z p₁ = Real.exp (-2) * (1 / 2 : ℝ) := by
  norm_num [z, p₁, quadraticPart]

private theorem z_perturb_up (t : ℝ) :
    z (p₁.1 + 3 * t, p₁.2 - 2 * t) =
      Real.exp (-2) * ((1 / 2 : ℝ) + 120 * t ^ 2) := by
  norm_num [z, p₁, quadraticPart] <;> ring_nf

private theorem z_perturb_down (t : ℝ) :
    z (p₁.1 + t, p₁.2 + 2 * t) =
      Real.exp (-2) * (1 / 2 : ℝ) *
        (Real.exp (4 * t) * (1 - 4 * t)) ^ 2 := by
  calc
    z (p₁.1 + t, p₁.2 + 2 * t) =
        Real.exp (-2 + 8 * t) * ((1 / 2 : ℝ) - 4 * t + 8 * t ^ 2) := by
          norm_num [z, p₁, quadraticPart] <;> ring_nf
    _ = Real.exp (-2) * (1 / 2 : ℝ) *
        (Real.exp (4 * t) * (1 - 4 * t)) ^ 2 := by
      rw [Real.exp_add]
      have he : Real.exp (8 * t) = Real.exp (4 * t) * Real.exp (4 * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring

private theorem norm_three_neg_two (t : ℝ) (ht : 0 ≤ t) :
    ‖((3 * t, -2 * t) : ℝ × ℝ)‖ = 3 * t := by
  change max ‖(3 * t : ℝ)‖ ‖(-2 * t : ℝ)‖ = 3 * t
  simp only [Real.norm_eq_abs]
  have h3 : |3 * t| = 3 * t := abs_of_nonneg (mul_nonneg (by norm_num) ht)
  have h2 : |-2 * t| = 2 * t := by
    rw [abs_of_nonpos (by nlinarith)]
    ring
  rw [h3, h2, max_eq_left]
  nlinarith

private theorem norm_one_two (t : ℝ) (ht : 0 ≤ t) :
    ‖((t, 2 * t) : ℝ × ℝ)‖ = 2 * t := by
  change max ‖(t : ℝ)‖ ‖(2 * t : ℝ)‖ = 2 * t
  simp only [Real.norm_eq_abs]
  have h1 : |t| = t := abs_of_nonneg ht
  have h2 : |2 * t| = 2 * t := abs_of_nonneg (mul_nonneg (by norm_num) ht)
  rw [h1, h2, max_eq_right]
  nlinarith

theorem gap1 :
    ∀ p : ℝ × ℝ, p ∈ criticalPoints →
      partialX z p =
          2 * Real.exp (2 * p.1 + 3 * p.2) *
            (quadraticPart p + 8 * p.1 - 3 * p.2) ∧
      2 * Real.exp (2 * p.1 + 3 * p.2) *
          (quadraticPart p + 8 * p.1 - 3 * p.2) = 0 ∧
      partialY z p =
          3 * Real.exp (2 * p.1 + 3 * p.2) *
            (quadraticPart p - 2 * p.1 + 2 * p.2) ∧
      3 * Real.exp (2 * p.1 + 3 * p.2) *
          (quadraticPart p - 2 * p.1 + 2 * p.2) = 0 := by
  intro p hp
  have hp' : p = p₀ ∨ p = p₁ := by
    simpa [criticalPoints] using hp
  refine ⟨partialX_z_formula p, ?_, partialY_z_formula p, ?_⟩
  · rcases hp' with rfl | rfl <;>
      norm_num [p₀, p₁, quadraticPart]
  · rcases hp' with rfl | rfl <;>
      norm_num [p₀, p₁, quadraticPart]

theorem gap2 :
    p₀ = (0, 0) := by
  rfl

theorem gap3 :
    p₁ = (-(1 / 4 : ℝ), -(1 / 2 : ℝ)) := by
  rfl

theorem gap4 :
    ∀ p : ℝ × ℝ,
      partialXX z p =
        4 * Real.exp (2 * p.1 + 3 * p.2) *
          (quadraticPart p + 16 * p.1 - 6 * p.2 + 4) := by
  intro p
  unfold partialXX
  have hfun :
      (fun x => partialX z (x, p.2)) =
        (fun x =>
          2 * Real.exp (2 * x + 3 * p.2) *
            (quadraticPart (x, p.2) + 8 * x - 3 * p.2)) := by
    funext x
    simpa using partialX_z_formula (x, p.2)
  rw [hfun]
  exact (hasDerivAt_partialX_formula p.1 p.2).deriv

theorem gap5 :
    ∀ p : ℝ × ℝ,
      partialYY z p =
        9 * Real.exp (2 * p.1 + 3 * p.2) *
          (quadraticPart p - 4 * p.1 + 4 * p.2 + (2 / 3 : ℝ)) := by
  intro p
  unfold partialYY
  have hfun :
      (fun y => partialY z (p.1, y)) =
        (fun y =>
          3 * Real.exp (2 * p.1 + 3 * y) *
            (quadraticPart (p.1, y) - 2 * p.1 + 2 * y)) := by
    funext y
    simpa using partialY_z_formula (p.1, y)
  rw [hfun]
  exact (hasDerivAt_partialY_formula_y p.1 p.2).deriv

theorem gap6 :
    ∀ p : ℝ × ℝ,
      partialXY z p =
        6 * Real.exp (2 * p.1 + 3 * p.2) *
          (quadraticPart p + 6 * p.1 - p.2 - 1) := by
  intro p
  unfold partialXY
  have hfun :
      (fun y => partialX z (p.1, y)) =
        (fun y =>
          2 * Real.exp (2 * p.1 + 3 * y) *
            (quadraticPart (p.1, y) + 8 * p.1 - 3 * y)) := by
    funext y
    simpa using partialX_z_formula (p.1, y)
  rw [hfun]
  exact (hasDerivAt_partialX_formula_y p.1 p.2).deriv

theorem gap7 :
    hessianA p₀ = 16 := by
  rw [hessianA, gap4]
  norm_num [p₀, quadraticPart]

theorem gap8 :
    hessianB p₀ = -6 := by
  rw [hessianB, gap6]
  norm_num [p₀, quadraticPart]

theorem gap9 :
    hessianC p₀ = 6 := by
  rw [hessianC, gap5]
  norm_num [p₀, quadraticPart]

theorem gap10 :
    hessianDiscriminant p₀ = 60 := by
  rw [hessianDiscriminant, gap7, gap8, gap9]
  norm_num

theorem gap11 :
    (60 : ℝ) > 0 := by
  norm_num

theorem gap12 :
    IsUniqueGlobalMinimizer z p₀ := by
  constructor
  · intro q
    have hz0 : z p₀ = 0 := by
      norm_num [z, p₀, quadraticPart]
    rw [hz0]
    exact mul_nonneg (Real.exp_pos _).le (quadraticPart_nonneg q)
  · intro q hq
    have hz0 : z p₀ = 0 := by
      norm_num [z, p₀, quadraticPart]
    have hz : Real.exp (2 * q.1 + 3 * q.2) * quadraticPart q = 0 := by
      rw [hz0] at hq
      simpa [z] using hq
    have hquad : quadraticPart q = 0 :=
      (mul_eq_zero.mp hz).resolve_left (ne_of_gt (Real.exp_pos _))
    exact quadraticPart_eq_zero q hquad

theorem gap13 :
    z p₀ = 0 := by
  norm_num [z, p₀, quadraticPart]

theorem gap14 :
    hessianA p₁ = 14 * Real.exp (-2) := by
  rw [hessianA, gap4]
  norm_num [p₁, quadraticPart]
  ring

theorem gap15 :
    hessianB p₁ = -9 * Real.exp (-2) := by
  rw [hessianB, gap6]
  norm_num [p₁, quadraticPart]
  ring

theorem gap16 :
    hessianC p₁ = (3 / 2 : ℝ) * Real.exp (-2) := by
  rw [hessianC, gap5]
  norm_num [p₁, quadraticPart]
  ring

theorem gap17 :
    hessianDiscriminant p₁ = -60 * Real.exp (-4) := by
  rw [hessianDiscriminant, gap14, gap15, gap16]
  calc
    14 * Real.exp (-2) * ((3 / 2 : ℝ) * Real.exp (-2)) -
          (-9 * Real.exp (-2)) ^ 2 =
        -60 * (Real.exp (-2) * Real.exp (-2)) := by ring
    _ = -60 * Real.exp (-4) := by
      rw [← Real.exp_add]
      norm_num

theorem gap18 :
    -60 * Real.exp (-4) < 0 := by
  have he : 0 < Real.exp (-4) := Real.exp_pos _
  nlinarith

theorem gap19 :
    ¬ IsLocalMaximum z p₁ := by
  unfold IsLocalMaximum
  rintro ⟨ε, hε, hmax⟩
  let t : ℝ := ε / 4
  have ht : 0 < t := by
    dsimp [t]
    nlinarith
  let q : ℝ × ℝ := (p₁.1 + 3 * t, p₁.2 - 2 * t)
  have hqdiff : q - p₁ = (3 * t, -2 * t) := by
    ext <;> simp [q, p₁] <;> ring
  have hdist : ‖q - p₁‖ < ε := by
    rw [hqdiff, norm_three_neg_two t ht.le]
    dsimp [t]
    nlinarith
  have hgreater : z p₁ < z q := by
    dsimp [q]
    rw [z_at_p₁, z_perturb_up]
    apply mul_lt_mul_of_pos_left _ (Real.exp_pos _)
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
    nlinarith
  exact (not_lt_of_ge (hmax q hdist)) hgreater

theorem gap20 :
    ¬ IsLocalMinimum z p₁ := by
  unfold IsLocalMinimum
  rintro ⟨ε, hε, hmin⟩
  let t : ℝ := min (ε / 4) (1 / 8)
  have ht : 0 < t := by
    dsimp [t]
    exact lt_min (by nlinarith) (by norm_num)
  have htε : t ≤ ε / 4 := by
    dsimp [t]
    exact min_le_left _ _
  have htq : t < 1 / 4 := by
    have hle : t ≤ (1 / 8 : ℝ) := by
      dsimp [t]
      exact min_le_right _ _
    nlinarith
  let q : ℝ × ℝ := (p₁.1 + t, p₁.2 + 2 * t)
  have hqdiff : q - p₁ = (t, 2 * t) := by
    ext <;> simp [q, p₁] <;> ring
  have hdist : ‖q - p₁‖ < ε := by
    rw [hqdiff, norm_one_two t ht.le]
    nlinarith
  let a : ℝ := Real.exp (4 * t) * (1 - 4 * t)
  have hne : (-4 * t : ℝ) ≠ 0 := by nlinarith
  have hexp : 1 - 4 * t < Real.exp (-4 * t) := by
    convert Real.add_one_lt_exp hne using 1 <;> ring
  have hone : Real.exp (4 * t) * Real.exp (-4 * t) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have halt : a < 1 := by
    have h := mul_lt_mul_of_pos_left hexp (Real.exp_pos (4 * t))
    rw [hone] at h
    simpa [a] using h
  have hale : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (Real.exp_pos _).le (by nlinarith)
  have ha2 : a ^ 2 < 1 := by
    have hp : 0 < (1 - a) * (1 + a) :=
      mul_pos (sub_pos.mpr halt) (by nlinarith)
    nlinarith
  have hlower : z q < z p₁ := by
    dsimp [q]
    rw [z_perturb_down, z_at_p₁]
    rw [show Real.exp (4 * t) * (1 - 4 * t) = a from rfl]
    have hcoef : 0 < Real.exp (-2) * (1 / 2 : ℝ) :=
      mul_pos (Real.exp_pos _) (by norm_num)
    simpa using mul_lt_mul_of_pos_left ha2 hcoef
  exact (not_lt_of_ge (hmin q hdist)) hlower

end

end ProofGap.Exercise3632
