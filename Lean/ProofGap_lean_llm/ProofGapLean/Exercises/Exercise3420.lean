import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3420

noncomputable section

def partialX (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => u s y) x

def partialY (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => u x s) y

def differential (u : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX u x y * dx + partialY u x y * dy

def iterX : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, u => u
  | n + 1, u => partialX (iterX n u)

def iterY : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, u => u
  | n + 1, u => partialY (iterY n u)

def weighted (φ : ℝ → ℝ) (z u : ℝ → ℝ → ℝ)
    (n : ℕ) (x y : ℝ) : ℝ :=
  (φ (z x y)) ^ n * partialX u x y

def derivativeFormula (φ : ℝ → ℝ) (z u : ℝ → ℝ → ℝ)
    (n : ℕ) (x y : ℝ) : ℝ :=
  iterX (n - 1) (weighted φ z u n) x y

theorem gap1 (φ : ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (hImplicit : ∀ x y, z x y = x + y * φ (z x y))
    (hφ : Differentiable ℝ φ)
    (hz : Differentiable ℝ (Function.uncurry z)) :
    ∀ x y dx dy,
      differential z x y dx dy =
        dx + φ (z x y) * dy +
          y * deriv φ (z x y) * differential z x y dx dy := by
  intro x y dx dy
  have hpairX : DifferentiableAt ℝ (fun s : ℝ => (s, y)) x :=
    differentiableAt_id.prodMk (differentiableAt_const (c := y))
  have hpairY : DifferentiableAt ℝ (fun s : ℝ => (x, s)) y :=
    (differentiableAt_const (c := x)).prodMk differentiableAt_id
  have hzx : DifferentiableAt ℝ (fun s : ℝ => z s y) x := by
    simpa [Function.comp_def, Function.uncurry] using
      (hz (x, y)).comp x hpairX
  have hzy : DifferentiableAt ℝ (fun s : ℝ => z x s) y := by
    simpa [Function.comp_def, Function.uncurry] using
      (hz (x, y)).comp y hpairY
  have hφx :
      HasDerivAt (fun s : ℝ => φ (z s y))
        (deriv φ (z x y) * partialX z x y) x := by
    simpa [Function.comp_def, partialX] using
      ((hφ (z x y)).hasDerivAt.comp x hzx.hasDerivAt)
  have hφy :
      HasDerivAt (fun s : ℝ => φ (z x s))
        (deriv φ (z x y) * partialY z x y) y := by
    simpa [Function.comp_def, partialY] using
      ((hφ (z x y)).hasDerivAt.comp y hzy.hasDerivAt)
  have hx :
      partialX z x y =
        1 + y * deriv φ (z x y) * partialX z x y := by
    have hfun :
        (fun s : ℝ => z s y) =
          (fun s : ℝ => s + y * φ (z s y)) := by
      funext s
      exact hImplicit s y
    have hright :
        HasDerivAt (fun s : ℝ => s + y * φ (z s y))
          (1 + y * (deriv φ (z x y) * partialX z x y)) x :=
      by
        convert (hasDerivAt_id x).add ((hasDerivAt_const x y).mul hφx) using 1 <;>
          simp <;> ring
    calc
      partialX z x y = deriv (fun s : ℝ => z s y) x := rfl
      _ = deriv (fun s : ℝ => s + y * φ (z s y)) x :=
        congrArg (fun g : ℝ → ℝ => deriv g x) hfun
      _ = 1 + y * deriv φ (z x y) * partialX z x y := by
        rw [hright.deriv]
        ring
  have hy :
      partialY z x y =
        φ (z x y) + y * deriv φ (z x y) * partialY z x y := by
    have hfun :
        (fun s : ℝ => z x s) =
          (fun s : ℝ => x + s * φ (z x s)) := by
      funext s
      exact hImplicit x s
    have hright :
        HasDerivAt (fun s : ℝ => x + s * φ (z x s))
          (0 + (φ (z x y) + y *
            (deriv φ (z x y) * partialY z x y))) y :=
      by
        convert (hasDerivAt_const y x).add ((hasDerivAt_id y).mul hφy) using 1 <;>
          simp <;> ring
    calc
      partialY z x y = deriv (fun s : ℝ => z x s) y := rfl
      _ = deriv (fun s : ℝ => x + s * φ (z x s)) y :=
        congrArg (fun g : ℝ → ℝ => deriv g y) hfun
      _ = φ (z x y) + y * deriv φ (z x y) * partialY z x y := by
        rw [hright.deriv]
        ring
  unfold differential
  conv_lhs =>
    rw [hx, hy]
  ring

theorem gap2 (φ : ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (hDifferential :
      ∀ x y dx dy,
        differential z x y dx dy =
          dx + φ (z x y) * dy +
            y * deriv φ (z x y) * differential z x y dx dy)
    (hDenom : ∀ x y, 1 - y * deriv φ (z x y) ≠ 0) :
    ∀ x y,
      partialX z x y = 1 / (1 - y * deriv φ (z x y)) := by
  intro x y
  have h := hDifferential x y 1 0
  simp [differential] at h
  apply (eq_div_iff (hDenom x y)).2
  nlinarith

theorem gap3 (φ : ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (hDifferential :
      ∀ x y dx dy,
        differential z x y dx dy =
          dx + φ (z x y) * dy +
            y * deriv φ (z x y) * differential z x y dx dy)
    (hDenom : ∀ x y, 1 - y * deriv φ (z x y) ≠ 0) :
    ∀ x y,
      partialY z x y =
        φ (z x y) / (1 - y * deriv φ (z x y)) := by
  intro x y
  have h := hDifferential x y 0 1
  simp [differential] at h
  apply (eq_div_iff (hDenom x y)).2
  nlinarith

theorem gap4 (φ : ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (hX :
      ∀ x y, partialX z x y = 1 / (1 - y * deriv φ (z x y))) :
    ∀ x y,
      φ (z x y) / (1 - y * deriv φ (z x y)) =
        φ (z x y) * partialX z x y := by
  intro x y
  rw [hX x y]
  simp [div_eq_mul_inv]

theorem gap5 (φ : ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (hY :
      ∀ x y,
        partialY z x y =
          φ (z x y) / (1 - y * deriv φ (z x y)))
    (hRewrite :
      ∀ x y,
        φ (z x y) / (1 - y * deriv φ (z x y)) =
          φ (z x y) * partialX z x y) :
    ∀ x y, partialY z x y = φ (z x y) * partialX z x y := by
  intro x y
  exact (hY x y).trans (hRewrite x y)

theorem gap6 (f : ℝ → ℝ) (z u : ℝ → ℝ → ℝ)
    (hComposition : ∀ x y, u x y = f (z x y))
    (hRegular :
      ∀ x y,
        DifferentiableAt ℝ f (z x y) ∧
          DifferentiableAt ℝ (fun s => z x s) y) :
    ∀ x y,
      partialY u x y = deriv f (z x y) * partialY z x y := by
  intro x y
  have hfun :
      (fun s : ℝ => u x s) = (fun s : ℝ => f (z x s)) := by
    funext s
    exact hComposition x s
  have hchain :=
    (hRegular x y).1.hasDerivAt.comp y (hRegular x y).2.hasDerivAt
  calc
    partialY u x y = deriv (fun s : ℝ => u x s) y := rfl
    _ = deriv (fun s : ℝ => f (z x s)) y :=
      congrArg (fun g : ℝ → ℝ => deriv g y) hfun
    _ = deriv f (z x y) * partialY z x y := by
      simpa [Function.comp_def, partialY] using hchain.deriv

theorem gap7 (f φ : ℝ → ℝ) (z u : ℝ → ℝ → ℝ)
    (hZ : ∀ x y, partialY z x y = φ (z x y) * partialX z x y)
    (hUX :
      ∀ x y, partialX u x y = deriv f (z x y) * partialX z x y) :
    ∀ x y,
      deriv f (z x y) * partialY z x y =
        φ (z x y) * partialX u x y := by
  intro x y
  rw [hZ x y, hUX x y]
  ring

theorem gap8 (f φ : ℝ → ℝ) (z u : ℝ → ℝ → ℝ)
    (hChain :
      ∀ x y, partialY u x y = deriv f (z x y) * partialY z x y)
    (hRewrite :
      ∀ x y,
        deriv f (z x y) * partialY z x y =
          φ (z x y) * partialX u x y) :
    ∀ x y, partialY u x y = φ (z x y) * partialX u x y := by
  intro x y
  exact (hChain x y).trans (hRewrite x y)

theorem gap9 (φ : ℝ → ℝ) (z u : ℝ → ℝ → ℝ)
    (hFirst : ∀ x y, partialY u x y = φ (z x y) * partialX u x y) :
    ∀ x y, partialY u x y = derivativeFormula φ z u 1 x y := by
  intro x y
  simpa [derivativeFormula, weighted, iterX] using hFirst x y

theorem gap10 (g : ℝ → ℝ) (z u : ℝ → ℝ → ℝ)
    (hRegular :
      ∀ x y,
        DifferentiableAt ℝ g (z x y) ∧
          DifferentiableAt ℝ (fun s => z x s) y ∧
          DifferentiableAt ℝ (fun s => partialX u x s) y) :
    ∀ x y,
      partialY (fun x y => g (z x y) * partialX u x y) x y =
        deriv g (z x y) * partialY z x y * partialX u x y +
          g (z x y) * partialY (partialX u) x y := by
  intro x y
  have hgz :
      HasDerivAt (fun s : ℝ => g (z x s))
        (deriv g (z x y) * partialY z x y) y := by
    simpa [Function.comp_def, partialY] using
      ((hRegular x y).1.hasDerivAt.comp y (hRegular x y).2.1.hasDerivAt)
  have hprod := hgz.mul (hRegular x y).2.2.hasDerivAt
  simpa [partialY, mul_assoc] using hprod.deriv

theorem gap11 (g φ : ℝ → ℝ) (z u : ℝ → ℝ → ℝ)
    (hProduct :
      ∀ x y,
        partialY (fun x y => g (z x y) * partialX u x y) x y =
          deriv g (z x y) * partialY z x y * partialX u x y +
            g (z x y) * partialY (partialX u) x y)
    (hZ : ∀ x y, partialY z x y = φ (z x y) * partialX z x y)
    (hMixed : ∀ x y, partialY (partialX u) x y = partialX (partialY u) x y)
    (hFirst : ∀ x y, partialY u x y = φ (z x y) * partialX u x y) :
    ∀ x y,
      partialY (fun x y => g (z x y) * partialX u x y) x y =
        φ (z x y) * deriv g (z x y) * partialX z x y *
            partialX u x y +
          g (z x y) *
            partialX (fun x y => φ (z x y) * partialX u x y) x y := by
  intro x y
  rw [hProduct x y, hZ x y, hMixed x y]
  have hfun :
      partialY u = (fun x y => φ (z x y) * partialX u x y) := by
    funext a b
    exact hFirst a b
  rw [hfun]
  ring

theorem gap12 (g φ : ℝ → ℝ) (z u : ℝ → ℝ → ℝ)
    (hExpanded :
      ∀ x y,
        partialY (fun x y => g (z x y) * partialX u x y) x y =
          φ (z x y) * deriv g (z x y) * partialX z x y *
              partialX u x y +
            g (z x y) *
              partialX (fun x y => φ (z x y) * partialX u x y) x y)
    (hRegular :
      ∀ x y,
        DifferentiableAt ℝ φ (z x y) ∧
          DifferentiableAt ℝ g (z x y) ∧
          DifferentiableAt ℝ (fun s => z s y) x ∧
          DifferentiableAt ℝ (fun s => partialX u s y) x) :
    ∀ x y,
      partialY (fun x y => g (z x y) * partialX u x y) x y =
        partialX
          (fun x y => φ (z x y) * g (z x y) * partialX u x y) x y := by
  intro x y
  rcases hRegular x y with ⟨hφ, hg, hz, hu⟩
  have hφz :
      HasDerivAt (fun s : ℝ => φ (z s y))
        (deriv φ (z x y) * partialX z x y) x := by
    simpa [Function.comp_def, partialX] using
      (hφ.hasDerivAt.comp x hz.hasDerivAt)
  have hgz :
      HasDerivAt (fun s : ℝ => g (z s y))
        (deriv g (z x y) * partialX z x y) x := by
    simpa [Function.comp_def, partialX] using
      (hg.hasDerivAt.comp x hz.hasDerivAt)
  have hderiv := (hφz.mul hgz).mul hu.hasDerivAt
  have hrhs :
      partialX
          (fun x y => φ (z x y) * g (z x y) * partialX u x y) x y =
        φ (z x y) * deriv g (z x y) * partialX z x y *
              partialX u x y +
            g (z x y) *
              partialX (fun x y => φ (z x y) * partialX u x y) x y := by
    have hinner := hφz.mul hu.hasDerivAt
    have hinnerDeriv :
        partialX (fun x y => φ (z x y) * partialX u x y) x y =
          deriv φ (z x y) * partialX z x y * partialX u x y +
            φ (z x y) * partialX (partialX u) x y := by
      simpa [partialX] using hinner.deriv
    rw [hinnerDeriv]
    have hmain :
        partialX
            (fun x y => φ (z x y) * g (z x y) * partialX u x y) x y =
          ((deriv φ (z x y) * partialX z x y) * g (z x y) +
              φ (z x y) * (deriv g (z x y) * partialX z x y)) *
                partialX u x y +
            (φ (z x y) * g (z x y)) * partialX (partialX u) x y := by
      simpa [partialX] using hderiv.deriv
    rw [hmain]
    ring
  exact (hExpanded x y).trans hrhs.symm

theorem gap13 (u : ℝ → ℝ → ℝ) :
    ∀ x y, iterY 2 u x y = partialY (partialY u) x y := by
  intro x y
  rfl

theorem gap14 (φ : ℝ → ℝ) (z u : ℝ → ℝ → ℝ)
    (hFirst : ∀ x y, partialY u x y = φ (z x y) * partialX u x y) :
    ∀ x y,
      partialY (partialY u) x y =
        partialY (weighted φ z u 1) x y := by
  intro x y
  have hfun : partialY u = weighted φ z u 1 := by
    funext a b
    simpa [weighted] using hFirst a b
  rw [hfun]

theorem gap15 (φ : ℝ → ℝ) (z u : ℝ → ℝ → ℝ)
    (hTransform :
      ∀ (g : ℝ → ℝ) x y,
        partialY (fun x y => g (z x y) * partialX u x y) x y =
          partialX
            (fun x y => φ (z x y) * g (z x y) * partialX u x y) x y) :
    ∀ x y,
      partialY (weighted φ z u 1) x y =
        partialX (weighted φ z u 2) x y := by
  intro x y
  have hleft :
      weighted φ z u 1 =
        (fun x y => φ (z x y) * partialX u x y) := by
    funext a b
    simp [weighted]
  have hright :
      weighted φ z u 2 =
        (fun x y => φ (z x y) * φ (z x y) * partialX u x y) := by
    funext a b
    simp [weighted, pow_two, mul_assoc]
  rw [hleft, hright]
  exact hTransform φ x y

theorem gap16 (φ : ℝ → ℝ) (z u : ℝ → ℝ → ℝ)
    (hSecond : ∀ x y, iterY 2 u x y = partialY (partialY u) x y)
    (hSubstitute :
      ∀ x y,
        partialY (partialY u) x y = partialY (weighted φ z u 1) x y)
    (hTransform :
      ∀ x y,
        partialY (weighted φ z u 1) x y =
          partialX (weighted φ z u 2) x y) :
    ∀ x y, iterY 2 u x y = derivativeFormula φ z u 2 x y := by
  intro x y
  rw [hSecond x y, hSubstitute x y, hTransform x y]
  rfl

theorem gap17 (φ : ℝ → ℝ) (z u : ℝ → ℝ → ℝ) :
    ∀ k x y, 1 ≤ k →
      iterY k u x y = derivativeFormula φ z u k x y →
      iterY (k + 1) u x y = partialY (iterY k u) x y := by
  intro k x y _ _
  rfl

-- Statement correction: differentiating the induction hypothesis requires equality
-- as functions of both variables, not merely equality at the evaluation point.
theorem gap18 (φ : ℝ → ℝ) (z u : ℝ → ℝ → ℝ)
    (hCommute :
      ∀ k x y, 1 ≤ k →
        partialY (iterX (k - 1) (weighted φ z u k)) x y =
          iterX (k - 1) (partialY (weighted φ z u k)) x y) :
    ∀ k x y, 1 ≤ k →
      (∀ a b, iterY k u a b = derivativeFormula φ z u k a b) →
      partialY (iterY k u) x y =
        iterX (k - 1) (partialY (weighted φ z u k)) x y := by
  intro k x y hk heq
  have hfun :
      iterY k u = iterX (k - 1) (weighted φ z u k) := by
    funext a b
    exact heq a b
  exact (congrArg (fun v => partialY v x y) hfun).trans
    (hCommute k x y hk)

-- Statement correction: the derivative-moving premise and induction hypothesis
-- must carry the fixed-k equality globally in the spatial variables.
theorem gap19 (φ : ℝ → ℝ) (z u : ℝ → ℝ → ℝ)
    (hSuccessor :
      ∀ k x y, 1 ≤ k →
        iterY k u x y = derivativeFormula φ z u k x y →
        iterY (k + 1) u x y = partialY (iterY k u) x y)
    (hMoveDerivative :
      ∀ k x y, 1 ≤ k →
        (∀ a b, iterY k u a b = derivativeFormula φ z u k a b) →
        partialY (iterY k u) x y =
          iterX (k - 1) (partialY (weighted φ z u k)) x y) :
    ∀ k x y, 1 ≤ k →
      (∀ a b, iterY k u a b = derivativeFormula φ z u k a b) →
      iterY (k + 1) u x y =
        iterX (k - 1) (partialY (weighted φ z u k)) x y := by
  intro k x y hk heq
  exact (hSuccessor k x y hk (heq x y)).trans
    (hMoveDerivative k x y hk heq)

-- Statement correction: the inductive interface must retain the fixed-k global
-- equality introduced when differentiating the induction hypothesis.
theorem gap20 (φ : ℝ → ℝ) (z u : ℝ → ℝ → ℝ)
    (hInductive :
      ∀ k x y, 1 ≤ k →
        (∀ a b, iterY k u a b = derivativeFormula φ z u k a b) →
        iterY (k + 1) u x y =
          iterX (k - 1) (partialY (weighted φ z u k)) x y)
    (hTransform :
      ∀ k x y, 1 ≤ k →
        partialY (weighted φ z u k) x y =
          partialX (weighted φ z u (k + 1)) x y) :
    ∀ k x y, 1 ≤ k →
      (∀ a b, iterY k u a b = derivativeFormula φ z u k a b) →
      iterY (k + 1) u x y =
        iterX (k - 1) (partialX (weighted φ z u (k + 1))) x y := by
  intro k x y hk heq
  rw [hInductive k x y hk heq]
  have hfun :
      partialY (weighted φ z u k) =
        partialX (weighted φ z u (k + 1)) := by
    funext a b
    exact hTransform k a b hk
  rw [hfun]

private theorem iterX_partialX (n : ℕ) (v : ℝ → ℝ → ℝ) :
    iterX n (partialX v) = iterX (n + 1) v := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change partialX (iterX n (partialX v)) =
        partialX (iterX (n + 1) v)
      rw [ih]

theorem gap21 (φ : ℝ → ℝ) (z u : ℝ → ℝ → ℝ) :
    ∀ k x y, 1 ≤ k →
      iterY k u x y = derivativeFormula φ z u k x y →
      iterX (k - 1) (partialX (weighted φ z u (k + 1))) x y =
        iterX k (weighted φ z u (k + 1)) x y := by
  intro k x y hk _
  have hkpos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
  simpa using congrFun (congrFun
    (iterX_partialX m (weighted φ z u (Nat.succ m + 1))) x) y

-- Statement correction: the pre-collapse interface must retain the fixed-k
-- equality globally so that the derivative step is justified.
theorem gap22 (φ : ℝ → ℝ) (z u : ℝ → ℝ → ℝ)
    (hBefore :
      ∀ k x y, 1 ≤ k →
        (∀ a b, iterY k u a b = derivativeFormula φ z u k a b) →
        iterY (k + 1) u x y =
          iterX (k - 1) (partialX (weighted φ z u (k + 1))) x y)
    (hCollapse :
      ∀ k x y, 1 ≤ k →
        iterY k u x y = derivativeFormula φ z u k x y →
        iterX (k - 1) (partialX (weighted φ z u (k + 1))) x y =
          iterX k (weighted φ z u (k + 1)) x y) :
    ∀ k x y, 1 ≤ k →
      (∀ a b, iterY k u a b = derivativeFormula φ z u k a b) →
      iterY (k + 1) u x y = derivativeFormula φ z u (k + 1) x y := by
  intro k x y hk heq
  rw [hBefore k x y hk heq, hCollapse k x y hk (heq x y)]
  simp [derivativeFormula]

-- Statement correction: each induction step needs the preceding fixed-k
-- equality at every point in order to justify differentiating it.
theorem gap23 (φ : ℝ → ℝ) (z u : ℝ → ℝ → ℝ)
    (hBase : ∀ x y, iterY 1 u x y = derivativeFormula φ z u 1 x y)
    (hStep :
      ∀ k x y, 1 ≤ k →
        (∀ a b, iterY k u a b = derivativeFormula φ z u k a b) →
        iterY (k + 1) u x y = derivativeFormula φ z u (k + 1) x y) :
    ∀ x y n, 1 ≤ n →
      iterY n u x y = derivativeFormula φ z u n x y := by
  intro x y n hn
  have hall :
      ∀ m, 1 ≤ m →
        ∀ a b, iterY m u a b = derivativeFormula φ z u m a b := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hBase
    | succ m hm ih =>
        intro a b
        exact hStep m a b hm ih
  exact hall n hn x y

theorem gap24 (φ : ℝ → ℝ) (z u : ℝ → ℝ → ℝ)
    (hPositive :
      ∀ x y n, 1 ≤ n →
        iterY n u x y = derivativeFormula φ z u n x y) :
    ∀ n x y, 1 ≤ n →
      iterY n u x y = derivativeFormula φ z u n x y := by
  intro n x y hn
  exact hPositive x y n hn

end

end ProofGap.Exercise3420
