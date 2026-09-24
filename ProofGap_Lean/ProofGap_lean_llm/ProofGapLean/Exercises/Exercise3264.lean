import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3264

noncomputable section

def u (x y : ℝ) : ℝ :=
  (x ^ 2 + y ^ 2) * Real.exp (x + y)

def u₁ (x y : ℝ) : ℝ :=
  x ^ 2 * Real.exp x * Real.exp y

def u₂ (x y : ℝ) : ℝ :=
  y ^ 2 * Real.exp y * Real.exp x

def iterDeriv (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) g

def partialXOrder (m : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  iterDeriv m (fun t => g t y) x

def partialYOrder (n : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  iterDeriv n (fun t => g x t) y

def mixedOrder (m n : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialYOrder n (fun a b => partialXOrder m g a b) x y

def mixedOrderViaXDerivative (m n : ℕ)
    (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialYOrder n (fun a b => partialXOrder m g a b) x y

def fallingTwo (n : ℕ) : ℝ :=
  (n : ℝ) * ((n - 1 : ℕ) : ℝ)

def yLeibnizForm (n : ℕ) (x y : ℝ) : ℝ :=
  Real.exp x *
    (y ^ 2 * iterDeriv n Real.exp y +
      (Nat.choose n 1 : ℝ) * deriv (fun t : ℝ => t ^ 2) y *
        iterDeriv (n - 1) Real.exp y +
      (Nat.choose n 2 : ℝ) *
        deriv (fun t => deriv (fun s : ℝ => s ^ 2) t) y *
        iterDeriv (n - 2) Real.exp y)

def u₂Closed (n : ℕ) (x y : ℝ) : ℝ :=
  Real.exp (x + y) *
    (y ^ 2 + 2 * (n : ℝ) * y + fallingTwo n)

def u₁Closed (m : ℕ) (x y : ℝ) : ℝ :=
  Real.exp (x + y) *
    (x ^ 2 + 2 * (m : ℝ) * x + fallingTwo m)

def totalClosed (m n : ℕ) (x y : ℝ) : ℝ :=
  Real.exp (x + y) *
    (x ^ 2 + y ^ 2 +
      2 * (m : ℝ) * x + 2 * (n : ℝ) * y +
      fallingTwo m + fallingTwo n)

private theorem fallingTwo_succ (n : ℕ) :
    fallingTwo (Nat.succ n) = fallingTwo n + 2 * (n : ℝ) := by
  cases n with
  | zero => norm_num [fallingTwo]
  | succ n =>
      simp [fallingTwo]
      ring

private theorem iterDeriv_fixed (g : ℝ → ℝ) (hg : deriv g = g) :
    ∀ n, iterDeriv n g = g := by
  intro n
  induction n with
  | zero => simp [iterDeriv]
  | succ n ih =>
      change (deriv^[Nat.succ n]) g = g
      rw [Function.iterate_succ_apply']
      change deriv (iterDeriv n g) = g
      rw [ih, hg]

private theorem iterDeriv_exp (n : ℕ) (x : ℝ) :
    iterDeriv n Real.exp x = Real.exp x := by
  have hg : deriv Real.exp = Real.exp := by
    funext t
    exact (Real.hasDerivAt_exp t).deriv
  exact congrFun (iterDeriv_fixed Real.exp hg n) x

private theorem iterDeriv_exp_mul_const (n : ℕ) (c x : ℝ) :
    iterDeriv n (fun t => Real.exp t * c) x = Real.exp x * c := by
  let g : ℝ → ℝ := fun t => Real.exp t * c
  have hg : deriv g = g := by
    funext t
    exact (Real.hasDerivAt_exp t).mul_const c |>.deriv
  exact congrFun (iterDeriv_fixed g hg n) x

private theorem iterDeriv_scaled_quad_exp :
    ∀ (n : ℕ) (c k x : ℝ),
      iterDeriv n (fun t => c * ((t ^ 2 + k) * Real.exp t)) x =
        c * Real.exp x *
          (x ^ 2 + 2 * (n : ℝ) * x + fallingTwo n + k) := by
  intro n
  induction n with
  | zero =>
      intro c k x
      simp [iterDeriv, fallingTwo]
      ring
  | succ n ih =>
      intro c k x
      have hfun :
          iterDeriv n (fun t => c * ((t ^ 2 + k) * Real.exp t)) =
            fun t => c * Real.exp t *
              (t ^ 2 + 2 * (n : ℝ) * t + fallingTwo n + k) := by
        funext t
        exact ih c k t
      change
        (deriv^[Nat.succ n])
            (fun t => c * ((t ^ 2 + k) * Real.exp t)) x = _
      rw [Function.iterate_succ_apply']
      change
        deriv
            (iterDeriv n (fun t => c * ((t ^ 2 + k) * Real.exp t))) x = _
      rw [hfun]
      have hp :
          HasDerivAt
            (fun t : ℝ =>
              t ^ 2 + 2 * (n : ℝ) * t + fallingTwo n + k)
            (2 * x + 2 * (n : ℝ)) x := by
        convert
          (((((hasDerivAt_id x).mul (hasDerivAt_id x)).add
              ((hasDerivAt_id x).const_mul (2 * (n : ℝ)))).add_const
                (fallingTwo n)).add_const k) using 1
        · funext t
          simp <;> ring
        · simp <;> ring
      have hd :
          HasDerivAt
            (fun t : ℝ =>
              c * Real.exp t *
                (t ^ 2 + 2 * (n : ℝ) * t + fallingTwo n + k))
            (c * Real.exp x *
                (x ^ 2 + 2 * (n : ℝ) * x + fallingTwo n + k) +
              c * Real.exp x * (2 * x + 2 * (n : ℝ))) x :=
        ((Real.hasDerivAt_exp x).const_mul c).mul hp
      rw [hd.deriv, fallingTwo_succ]
      simp only [Nat.cast_succ]
      ring

private theorem iterDeriv_scaled_sq_exp (n : ℕ) (c x : ℝ) :
    iterDeriv n (fun t => c * (t ^ 2 * Real.exp t)) x =
      c * Real.exp x *
        (x ^ 2 + 2 * (n : ℝ) * x + fallingTwo n) := by
  simpa only [add_zero] using iterDeriv_scaled_quad_exp n c 0 x

private theorem iterDeriv_sq_exp (n : ℕ) (x : ℝ) :
    iterDeriv n (fun t => t ^ 2 * Real.exp t) x =
      Real.exp x * (x ^ 2 + 2 * (n : ℝ) * x + fallingTwo n) := by
  simpa using iterDeriv_scaled_sq_exp n 1 x

private theorem deriv_sq (x : ℝ) :
    deriv (fun t : ℝ => t ^ 2) x = 2 * x := by
  convert ((hasDerivAt_id x).mul (hasDerivAt_id x)).deriv using 1
  · apply congrArg (fun f : ℝ → ℝ => deriv f x)
    funext t
    simp [pow_two] <;> ring
  · simp <;> ring

private theorem deriv_deriv_sq (x : ℝ) :
    deriv (fun t => deriv (fun s : ℝ => s ^ 2) t) x = 2 := by
  have hfun :
      (fun t => deriv (fun s : ℝ => s ^ 2) t) = fun t => 2 * t := by
    funext t
    exact deriv_sq t
  rw [hfun]
  convert ((hasDerivAt_id x).const_mul 2).deriv using 1 <;> ring

private theorem choose_one_real (n : ℕ) :
    (Nat.choose n 1 : ℝ) = (n : ℝ) := by
  simp

private theorem choose_two_real (n : ℕ) :
    (Nat.choose n 2 : ℝ) * 2 = fallingTwo n := by
  induction n with
  | zero => norm_num [fallingTwo]
  | succ n ih =>
      rw [Nat.choose]
      simp only [Nat.cast_add, Nat.choose_one_right]
      rw [fallingTwo_succ, add_mul, ih]
      ring

private theorem yLeibniz_eq_closed (n : ℕ) (x y : ℝ) :
    yLeibnizForm n x y = u₂Closed n x y := by
  unfold yLeibnizForm u₂Closed
  rw [iterDeriv_exp n y, iterDeriv_exp (n - 1) y,
    iterDeriv_exp (n - 2) y]
  rw [deriv_sq y, deriv_deriv_sq y]
  rw [choose_one_real n, choose_two_real n, Real.exp_add]
  ring

private theorem partialX_u₂ (m : ℕ) (x y : ℝ) :
    partialXOrder m u₂ x y = Real.exp x * y ^ 2 * Real.exp y := by
  unfold partialXOrder
  have hf :
      (fun t => u₂ t y) = fun t => Real.exp t * (y ^ 2 * Real.exp y) := by
    funext t
    unfold u₂
    ring
  rw [hf, iterDeriv_exp_mul_const]
  ring

private theorem partialX_u₁ (m : ℕ) (x y : ℝ) :
    partialXOrder m u₁ x y =
      Real.exp y *
        (Real.exp x * (x ^ 2 + 2 * (m : ℝ) * x + fallingTwo m)) := by
  unfold partialXOrder
  have hf :
      (fun t => u₁ t y) = fun t => Real.exp y * (t ^ 2 * Real.exp t) := by
    funext t
    unfold u₁
    ring
  rw [hf, iterDeriv_scaled_sq_exp]
  ring

private theorem partialX_u (m : ℕ) (x y : ℝ) :
    partialXOrder m u x y =
      Real.exp x *
        ((y ^ 2 +
            (x ^ 2 + 2 * (m : ℝ) * x + fallingTwo m)) * Real.exp y) := by
  unfold partialXOrder
  have hf :
      (fun t => u t y) =
        fun t => Real.exp y * ((t ^ 2 + y ^ 2) * Real.exp t) := by
    funext t
    unfold u
    rw [Real.exp_add]
    ring
  rw [hf, iterDeriv_scaled_quad_exp]
  ring

private theorem sq_exp_expression_closed (n : ℕ) (x y : ℝ) :
    Real.exp x * iterDeriv n (fun t => t ^ 2 * Real.exp t) y =
      u₂Closed n x y := by
  rw [iterDeriv_sq_exp]
  unfold u₂Closed
  rw [Real.exp_add]
  ring

private theorem mixed_u₂_closed (m n : ℕ) (x y : ℝ) :
    mixedOrder m n u₂ x y = u₂Closed n x y := by
  unfold mixedOrder partialYOrder
  have hf :
      (fun t => partialXOrder m u₂ x t) =
        fun t => Real.exp x * (t ^ 2 * Real.exp t) := by
    funext t
    rw [partialX_u₂]
    ring
  rw [hf, iterDeriv_scaled_sq_exp]
  unfold u₂Closed
  rw [Real.exp_add]

private theorem mixed_u₁_closed (m n : ℕ) (x y : ℝ) :
    mixedOrder m n u₁ x y = u₁Closed m x y := by
  unfold mixedOrder partialYOrder
  let c : ℝ :=
    Real.exp x * (x ^ 2 + 2 * (m : ℝ) * x + fallingTwo m)
  have hf :
      (fun t => partialXOrder m u₁ x t) = fun t => Real.exp t * c := by
    funext t
    rw [partialX_u₁]
  rw [hf, iterDeriv_exp_mul_const]
  unfold c u₁Closed
  rw [Real.exp_add]
  ring

private theorem mixed_u_closed (m n : ℕ) (x y : ℝ) :
    mixedOrder m n u x y = totalClosed m n x y := by
  unfold mixedOrder partialYOrder
  let k : ℝ := x ^ 2 + 2 * (m : ℝ) * x + fallingTwo m
  have hf :
      (fun t => partialXOrder m u x t) =
        fun t => Real.exp x * ((t ^ 2 + k) * Real.exp t) := by
    funext t
    rw [partialX_u]
  rw [hf, iterDeriv_scaled_quad_exp]
  unfold k totalClosed
  rw [Real.exp_add]
  ring

theorem gap1 :
    ∀ x y, u x y = (x ^ 2 + y ^ 2) * Real.exp (x + y) := by
  intro x y
  rfl

theorem gap2 :
    ∀ x y,
      (x ^ 2 + y ^ 2) * Real.exp (x + y) =
        x ^ 2 * Real.exp x * Real.exp y +
          y ^ 2 * Real.exp y * Real.exp x := by
  intro x y
  rw [Real.exp_add]
  ring

theorem gap3 :
    ∃ v₁ v₂ : ℝ → ℝ → ℝ,
      v₁ = u₁ ∧ v₂ = u₂ ∧
        ∀ x y,
          x ^ 2 * Real.exp x * Real.exp y +
              y ^ 2 * Real.exp y * Real.exp x =
            v₁ x y + v₂ x y := by
  refine ⟨u₁, u₂, rfl, rfl, ?_⟩
  intro x y
  rfl

theorem gap4 :
    ∃ v₁ v₂ : ℝ → ℝ → ℝ,
      v₁ = u₁ ∧ v₂ = u₂ ∧
        ∀ x y, u x y = v₁ x y + v₂ x y := by
  refine ⟨u₁, u₂, rfl, rfl, ?_⟩
  intro x y
  rw [gap1 x y, gap2 x y]
  rfl

theorem gap5 :
    ∃ v₂ : ℝ → ℝ → ℝ, v₂ = u₂ ∧
      ∀ m x y, partialXOrder m v₂ x y =
        Real.exp x * y ^ 2 * Real.exp y := by
  refine ⟨u₂, rfl, ?_⟩
  intro m x y
  exact partialX_u₂ m x y

theorem gap6 :
    ∃ v₂ : ℝ → ℝ → ℝ, v₂ = u₂ ∧
      ∀ m n x y,
        mixedOrder m n v₂ x y =
          mixedOrderViaXDerivative m n v₂ x y := by
  refine ⟨u₂, rfl, ?_⟩
  intro m n x y
  rfl

theorem gap7 :
    ∃ v₂ : ℝ → ℝ → ℝ, v₂ = u₂ ∧
      ∀ m n x y,
        mixedOrderViaXDerivative m n v₂ x y =
          partialYOrder n
            (fun a b => Real.exp a * b ^ 2 * Real.exp b) x y := by
  refine ⟨u₂, rfl, ?_⟩
  intro m n x y
  unfold mixedOrderViaXDerivative partialYOrder
  have hf :
      (fun t => partialXOrder m u₂ x t) =
        (fun t => Real.exp x * t ^ 2 * Real.exp t) := by
    funext t
    exact partialX_u₂ m x t
  rw [hf]

theorem gap8 :
    ∀ n x y,
      partialYOrder n
          (fun a b => Real.exp a * b ^ 2 * Real.exp b) x y =
        Real.exp x * iterDeriv n (fun t => t ^ 2 * Real.exp t) y := by
  intro n x y
  unfold partialYOrder
  have hscaled := iterDeriv_scaled_sq_exp n (Real.exp x) y
  have hplain := iterDeriv_sq_exp n y
  rw [hplain]
  simpa [mul_assoc] using hscaled

theorem gap9 :
    ∃ v₂ : ℝ → ℝ → ℝ, v₂ = u₂ ∧
      ∀ m n x y,
        mixedOrder m n v₂ x y =
          Real.exp x * iterDeriv n (fun t => t ^ 2 * Real.exp t) y := by
  refine ⟨u₂, rfl, ?_⟩
  intro m n x y
  exact (mixed_u₂_closed m n x y).trans (sq_exp_expression_closed n x y).symm

theorem gap10 :
    ∃ v₂ : ℝ → ℝ → ℝ, v₂ = u₂ ∧
      ∀ m n x y, mixedOrder m n v₂ x y = yLeibnizForm n x y := by
  refine ⟨u₂, rfl, ?_⟩
  intro m n x y
  exact (mixed_u₂_closed m n x y).trans (yLeibniz_eq_closed n x y).symm

theorem gap11 :
    ∃ v₂ : ℝ → ℝ → ℝ, v₂ = u₂ ∧
      ∀ m n x y, mixedOrder m n v₂ x y = u₂Closed n x y := by
  refine ⟨u₂, rfl, ?_⟩
  intro m n x y
  exact mixed_u₂_closed m n x y

theorem gap12 :
    ∃ v₁ : ℝ → ℝ → ℝ, v₁ = u₁ ∧
      ∀ m n x y, mixedOrder m n v₁ x y = u₁Closed m x y := by
  refine ⟨u₁, rfl, ?_⟩
  intro m n x y
  exact mixed_u₁_closed m n x y

theorem gap13 :
    ∃ v₁ v₂ : ℝ → ℝ → ℝ,
      v₁ = u₁ ∧ v₂ = u₂ ∧
        ∀ m n x y,
          mixedOrder m n u x y =
            mixedOrder m n v₁ x y + mixedOrder m n v₂ x y := by
  refine ⟨u₁, u₂, rfl, rfl, ?_⟩
  intro m n x y
  rw [mixed_u_closed m n x y, mixed_u₁_closed m n x y,
    mixed_u₂_closed m n x y]
  unfold totalClosed u₁Closed u₂Closed
  ring

theorem gap14 :
    ∃ v₁ v₂ : ℝ → ℝ → ℝ,
      v₁ = u₁ ∧ v₂ = u₂ ∧
        ∀ m n x y,
          mixedOrder m n v₁ x y + mixedOrder m n v₂ x y =
            totalClosed m n x y := by
  refine ⟨u₁, u₂, rfl, rfl, ?_⟩
  intro m n x y
  rw [mixed_u₁_closed m n x y, mixed_u₂_closed m n x y]
  unfold u₁Closed u₂Closed totalClosed
  ring

theorem gap15 :
    ∀ m n x y, mixedOrder m n u x y = totalClosed m n x y := by
  intro m n x y
  exact mixed_u_closed m n x y

end

end ProofGap.Exercise3264
