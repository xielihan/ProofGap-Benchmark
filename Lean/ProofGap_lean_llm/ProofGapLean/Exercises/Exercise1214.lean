import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1214

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def amplitude (a b : ℝ) : ℝ := Real.sqrt (a ^ 2 + b ^ 2)
def y₁ (a b x : ℝ) : ℝ := Real.cosh (a * x) * Real.cos (b * x)
def y₂ (a b x : ℝ) : ℝ := Real.cosh (a * x) * Real.sin (b * x)
def y₃ (a b x : ℝ) : ℝ := Real.sinh (a * x) * Real.cos (b * x)
def y₄ (a b x : ℝ) : ℝ := Real.sinh (a * x) * Real.sin (b * x)

private def closedPhase (φ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * φ - (n : ℝ) / 2 * Real.pi

private def closedArg (b x : ℝ) (n : ℕ) : ℝ :=
  b * x + (n : ℝ) / 2 * Real.pi

private def closedF1 (a b φ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  amplitude a b ^ n *
    (Real.cos (closedPhase φ n) * Real.cosh (a * x) * Real.cos (closedArg b x n) -
      Real.sin (closedPhase φ n) * Real.sinh (a * x) * Real.sin (closedArg b x n))

private def closedF2 (a b φ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  amplitude a b ^ n *
    (Real.cos (closedPhase φ n) * Real.cosh (a * x) * Real.sin (closedArg b x n) +
      Real.sin (closedPhase φ n) * Real.sinh (a * x) * Real.cos (closedArg b x n))

private def closedF3 (a b φ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  amplitude a b ^ n *
    (Real.cos (closedPhase φ n) * Real.sinh (a * x) * Real.cos (closedArg b x n) -
      Real.sin (closedPhase φ n) * Real.cosh (a * x) * Real.sin (closedArg b x n))

private def closedF4 (a b φ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  amplitude a b ^ n *
    (Real.cos (closedPhase φ n) * Real.sinh (a * x) * Real.sin (closedArg b x n) +
      Real.sin (closedPhase φ n) * Real.cosh (a * x) * Real.cos (closedArg b x n))

private theorem closedAlgebra (r a b c s cp sp H S C T : ℝ) (n : ℕ)
    (ha : a = r * c) (hb : b = r * s) :
    r ^ (n + 1) *
        ((sp * c + cp * s) * H * (-T) - (-(cp * c - sp * s)) * S * C) =
      r ^ n *
        (cp * (a * S * C - b * H * T) - sp * (a * H * T + b * S * C)) ∧
    r ^ (n + 1) *
        ((sp * c + cp * s) * H * C + (-(cp * c - sp * s)) * S * (-T)) =
      r ^ n *
        (cp * (a * S * T + b * H * C) + sp * (a * H * C - b * S * T)) ∧
    r ^ (n + 1) *
        ((sp * c + cp * s) * S * (-T) - (-(cp * c - sp * s)) * H * C) =
      r ^ n *
        (cp * (a * H * C - b * S * T) - sp * (a * S * T + b * H * C)) ∧
    r ^ (n + 1) *
        ((sp * c + cp * s) * S * C + (-(cp * c - sp * s)) * H * (-T)) =
      r ^ n *
        (cp * (a * H * T + b * S * C) + sp * (a * S * C - b * H * T)) := by
  subst a
  subst b
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

private theorem closedFormsStep (a b φ : ℝ) (n : ℕ)
    (hamp : 0 < a ^ 2 + b ^ 2)
    (hs : Real.sin φ = b / amplitude a b)
    (hc : Real.cos φ = a / amplitude a b) (x : ℝ) :
    HasDerivAt (closedF1 a b φ n) (closedF1 a b φ (n + 1) x) x ∧
    HasDerivAt (closedF2 a b φ n) (closedF2 a b φ (n + 1) x) x ∧
    HasDerivAt (closedF3 a b φ n) (closedF3 a b φ (n + 1) x) x ∧
    HasDerivAt (closedF4 a b φ n) (closedF4 a b φ (n + 1) x) x := by
  have hr : 0 < amplitude a b := by
    exact Real.sqrt_pos.2 hamp
  have ha : a = amplitude a b * Real.cos φ := by
    rw [hc]
    field_simp [ne_of_gt hr]
  have hb : b = amplitude a b * Real.sin φ := by
    rw [hs]
    field_simp [ne_of_gt hr]
  have hphase : closedPhase φ (n + 1) = closedPhase φ n + φ - Real.pi / 2 := by
    unfold closedPhase
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have harg : closedArg b x (n + 1) = closedArg b x n + Real.pi / 2 := by
    unfold closedArg
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have hcphase : Real.cos (closedPhase φ (n + 1)) =
      Real.sin (closedPhase φ n + φ) := by
    rw [hphase, Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hsphase : Real.sin (closedPhase φ (n + 1)) =
      -Real.cos (closedPhase φ n + φ) := by
    rw [hphase, Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hcarg : Real.cos (closedArg b x (n + 1)) =
      -Real.sin (closedArg b x n) := by
    rw [harg, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hsarg : Real.sin (closedArg b x (n + 1)) =
      Real.cos (closedArg b x n) := by
    rw [harg, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hax : HasDerivAt (fun z : ℝ => a * z) a x := by
    convert (hasDerivAt_id x).const_mul a using 1 <;> ring
  have hbx : HasDerivAt
      (fun z : ℝ => b * z + (n : ℝ) / 2 * Real.pi) b x := by
    convert ((hasDerivAt_id x).const_mul b).add_const
      ((n : ℝ) / 2 * Real.pi) using 1 <;> ring
  have hcosh : HasDerivAt (fun z : ℝ => Real.cosh (a * z))
      (a * Real.sinh (a * x)) x := by
    convert (Real.hasDerivAt_cosh (a * x)).comp x hax using 1 <;> ring
  have hsinh : HasDerivAt (fun z : ℝ => Real.sinh (a * z))
      (a * Real.cosh (a * x)) x := by
    convert (Real.hasDerivAt_sinh (a * x)).comp x hax using 1 <;> ring
  have hcos : HasDerivAt (fun z : ℝ => Real.cos (closedArg b z n))
      (-b * Real.sin (closedArg b x n)) x := by
    convert (Real.hasDerivAt_cos (closedArg b x n)).comp x hbx using 1 <;>
      simp [closedArg] <;> ring
  have hsin : HasDerivAt (fun z : ℝ => Real.sin (closedArg b z n))
      (b * Real.cos (closedArg b x n)) x := by
    convert (Real.hasDerivAt_sin (closedArg b x n)).comp x hbx using 1 <;>
      simp [closedArg] <;> ring
  have hd1 : HasDerivAt (closedF1 a b φ n)
      (amplitude a b ^ n *
        (Real.cos (closedPhase φ n) *
            (a * Real.sinh (a * x) * Real.cos (closedArg b x n) -
              b * Real.cosh (a * x) * Real.sin (closedArg b x n)) -
          Real.sin (closedPhase φ n) *
            (a * Real.cosh (a * x) * Real.sin (closedArg b x n) +
              b * Real.sinh (a * x) * Real.cos (closedArg b x n)))) x := by
    convert ((((hcosh.mul hcos).const_mul (Real.cos (closedPhase φ n))).sub
      ((hsinh.mul hsin).const_mul (Real.sin (closedPhase φ n)))).const_mul
        (amplitude a b ^ n)) using 1
    · funext y
      simp [closedF1] <;> ring_nf <;> simp
    · ring <;> simp
  have hd2 : HasDerivAt (closedF2 a b φ n)
      (amplitude a b ^ n *
        (Real.cos (closedPhase φ n) *
            (a * Real.sinh (a * x) * Real.sin (closedArg b x n) +
              b * Real.cosh (a * x) * Real.cos (closedArg b x n)) +
          Real.sin (closedPhase φ n) *
            (a * Real.cosh (a * x) * Real.cos (closedArg b x n) -
              b * Real.sinh (a * x) * Real.sin (closedArg b x n)))) x := by
    convert ((((hcosh.mul hsin).const_mul (Real.cos (closedPhase φ n))).add
      ((hsinh.mul hcos).const_mul (Real.sin (closedPhase φ n)))).const_mul
        (amplitude a b ^ n)) using 1
    · funext y
      simp [closedF2] <;> ring_nf <;> simp
    · ring <;> simp
  have hd3 : HasDerivAt (closedF3 a b φ n)
      (amplitude a b ^ n *
        (Real.cos (closedPhase φ n) *
            (a * Real.cosh (a * x) * Real.cos (closedArg b x n) -
              b * Real.sinh (a * x) * Real.sin (closedArg b x n)) -
          Real.sin (closedPhase φ n) *
            (a * Real.sinh (a * x) * Real.sin (closedArg b x n) +
              b * Real.cosh (a * x) * Real.cos (closedArg b x n)))) x := by
    convert ((((hsinh.mul hcos).const_mul (Real.cos (closedPhase φ n))).sub
      ((hcosh.mul hsin).const_mul (Real.sin (closedPhase φ n)))).const_mul
        (amplitude a b ^ n)) using 1
    · funext y
      simp [closedF3] <;> ring_nf <;> simp
    · ring <;> simp
  have hd4 : HasDerivAt (closedF4 a b φ n)
      (amplitude a b ^ n *
        (Real.cos (closedPhase φ n) *
            (a * Real.cosh (a * x) * Real.sin (closedArg b x n) +
              b * Real.sinh (a * x) * Real.cos (closedArg b x n)) +
          Real.sin (closedPhase φ n) *
            (a * Real.sinh (a * x) * Real.cos (closedArg b x n) -
              b * Real.cosh (a * x) * Real.sin (closedArg b x n)))) x := by
    convert ((((hsinh.mul hsin).const_mul (Real.cos (closedPhase φ n))).add
      ((hcosh.mul hcos).const_mul (Real.sin (closedPhase φ n)))).const_mul
        (amplitude a b ^ n)) using 1
    · funext y
      simp [closedF4] <;> ring_nf <;> simp
    · ring <;> simp
  have halg := closedAlgebra (amplitude a b) a b (Real.cos φ) (Real.sin φ)
    (Real.cos (closedPhase φ n)) (Real.sin (closedPhase φ n))
    (Real.cosh (a * x)) (Real.sinh (a * x))
    (Real.cos (closedArg b x n)) (Real.sin (closedArg b x n)) n ha hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hd1 using 1
    rw [closedF1, hcphase, hsphase, hcarg, hsarg,
      Real.sin_add, Real.cos_add]
    exact halg.1
  · convert hd2 using 1
    rw [closedF2, hcphase, hsphase, hcarg, hsarg,
      Real.sin_add, Real.cos_add]
    exact halg.2.1
  · convert hd3 using 1
    rw [closedF3, hcphase, hsphase, hcarg, hsarg,
      Real.sin_add, Real.cos_add]
    exact halg.2.2.1
  · convert hd4 using 1
    rw [closedF4, hcphase, hsphase, hcarg, hsarg,
      Real.sin_add, Real.cos_add]
    exact halg.2.2.2

private theorem closedForms (a b φ : ℝ)
    (hamp : 0 < a ^ 2 + b ^ 2)
    (hs : Real.sin φ = b / amplitude a b)
    (hc : Real.cos φ = a / amplitude a b) : ∀ n : ℕ,
    (∀ x, iterDeriv n (y₁ a b) x = closedF1 a b φ n x) ∧
    (∀ x, iterDeriv n (y₂ a b) x = closedF2 a b φ n x) ∧
    (∀ x, iterDeriv n (y₃ a b) x = closedF3 a b φ n x) ∧
    (∀ x, iterDeriv n (y₄ a b) x = closedF4 a b φ n x) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro x <;>
        simp [iterDeriv, closedF1, closedF2, closedF3, closedF4,
          closedPhase, closedArg, y₁, y₂, y₃, y₄]
  | succ n ih =>
      rcases ih with ⟨ih1, ih2, ih3, ih4⟩
      have e1 : iterDeriv n (y₁ a b) = closedF1 a b φ n := funext ih1
      have e2 : iterDeriv n (y₂ a b) = closedF2 a b φ n := funext ih2
      have e3 : iterDeriv n (y₃ a b) = closedF3 a b φ n := funext ih3
      have e4 : iterDeriv n (y₄ a b) = closedF4 a b φ n := funext ih4
      have s1 : iterDeriv (n + 1) (y₁ a b) = deriv (iterDeriv n (y₁ a b)) := by
        simp [iterDeriv, Function.iterate_succ_apply']
      have s2 : iterDeriv (n + 1) (y₂ a b) = deriv (iterDeriv n (y₂ a b)) := by
        simp [iterDeriv, Function.iterate_succ_apply']
      have s3 : iterDeriv (n + 1) (y₃ a b) = deriv (iterDeriv n (y₃ a b)) := by
        simp [iterDeriv, Function.iterate_succ_apply']
      have s4 : iterDeriv (n + 1) (y₄ a b) = deriv (iterDeriv n (y₄ a b)) := by
        simp [iterDeriv, Function.iterate_succ_apply']
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x
        rw [s1, e1]
        exact (closedFormsStep a b φ n hamp hs hc x).1.deriv
      · intro x
        rw [s2, e2]
        exact (closedFormsStep a b φ n hamp hs hc x).2.1.deriv
      · intro x
        rw [s3, e3]
        exact (closedFormsStep a b φ n hamp hs hc x).2.2.1.deriv
      · intro x
        rw [s4, e4]
        exact (closedFormsStep a b φ n hamp hs hc x).2.2.2.deriv

theorem gap1 (a b x : ℝ) :
    y₁ a b x =
      (1 / 2 : ℝ) * Real.exp (a * x) * Real.cos (b * x) +
        (1 / 2 : ℝ) * Real.exp (-a * x) * Real.cos (b * x) := by
  rw [y₁, Real.cosh_eq]
  have hneg : -(a * x) = -a * x := by ring
  rw [hneg]
  ring

theorem gap2 (a b φ x : ℝ) (n : ℕ) (hamp : 0 < a ^ 2 + b ^ 2)
    (hs : Real.sin φ = b / amplitude a b)
    (hc : Real.cos φ = a / amplitude a b) :
    iterDeriv n (y₁ a b) x =
      (1 / 2 : ℝ) * amplitude a b ^ n *
        (Real.exp (a * x) * Real.cos (b * x + (n : ℝ) * φ) +
          Real.exp (-a * x) *
            Real.cos (b * x + (n : ℝ) * Real.pi - (n : ℝ) * φ)) := by
  have h := (closedForms a b φ hamp hs hc n).1 x
  rw [h]
  unfold closedF1 closedArg closedPhase
  have hp : b * x + (n : ℝ) / 2 * Real.pi +
      ((n : ℝ) * φ - (n : ℝ) / 2 * Real.pi) =
      b * x + (n : ℝ) * φ := by ring
  have hm : b * x + (n : ℝ) / 2 * Real.pi -
      ((n : ℝ) * φ - (n : ℝ) / 2 * Real.pi) =
      b * x + (n : ℝ) * Real.pi - (n : ℝ) * φ := by ring
  have hcp : Real.cos (b * x + (n : ℝ) * φ) =
      Real.cos (b * x + (n : ℝ) / 2 * Real.pi) *
          Real.cos ((n : ℝ) * φ - (n : ℝ) / 2 * Real.pi) -
        Real.sin (b * x + (n : ℝ) / 2 * Real.pi) *
          Real.sin ((n : ℝ) * φ - (n : ℝ) / 2 * Real.pi) := by
    rw [← hp, Real.cos_add]
  have hcm : Real.cos (b * x + (n : ℝ) * Real.pi - (n : ℝ) * φ) =
      Real.cos (b * x + (n : ℝ) / 2 * Real.pi) *
          Real.cos ((n : ℝ) * φ - (n : ℝ) / 2 * Real.pi) +
        Real.sin (b * x + (n : ℝ) / 2 * Real.pi) *
          Real.sin ((n : ℝ) * φ - (n : ℝ) / 2 * Real.pi) := by
    rw [← hm, Real.cos_sub]
  rw [hcp, hcm, Real.cosh_eq, Real.sinh_eq]
  have hneg : -(a * x) = -a * x := by ring
  rw [hneg]
  ring

theorem gap3 (a b φ x : ℝ) (n : ℕ) (hamp : 0 < a ^ 2 + b ^ 2)
    (hs : Real.sin φ = b / amplitude a b)
    (hc : Real.cos φ = a / amplitude a b) :
    iterDeriv n (y₁ a b) x =
      amplitude a b ^ n *
        (Real.cos ((n : ℝ) * φ - (n : ℝ) / 2 * Real.pi) *
            Real.cosh (a * x) * Real.cos (b * x + (n : ℝ) / 2 * Real.pi) -
          Real.sin ((n : ℝ) * φ - (n : ℝ) / 2 * Real.pi) *
            Real.sinh (a * x) * Real.sin (b * x + (n : ℝ) / 2 * Real.pi)) := by
  exact (closedForms a b φ hamp hs hc n).1 x

theorem gap4 (a b φ x : ℝ) (n : ℕ) (hamp : 0 < a ^ 2 + b ^ 2)
    (hs : Real.sin φ = b / amplitude a b)
    (hc : Real.cos φ = a / amplitude a b) :
    iterDeriv n (y₂ a b) x =
      amplitude a b ^ n *
        (Real.cos ((n : ℝ) * φ - (n : ℝ) / 2 * Real.pi) *
            Real.cosh (a * x) * Real.sin (b * x + (n : ℝ) / 2 * Real.pi) +
          Real.sin ((n : ℝ) * φ - (n : ℝ) / 2 * Real.pi) *
            Real.sinh (a * x) * Real.cos (b * x + (n : ℝ) / 2 * Real.pi)) := by
  exact (closedForms a b φ hamp hs hc n).2.1 x

theorem gap5 (a b φ x : ℝ) (n : ℕ) (hamp : 0 < a ^ 2 + b ^ 2)
    (hs : Real.sin φ = b / amplitude a b)
    (hc : Real.cos φ = a / amplitude a b) :
    iterDeriv n (y₃ a b) x =
      amplitude a b ^ n *
        (Real.cos ((n : ℝ) * φ - (n : ℝ) / 2 * Real.pi) *
            Real.sinh (a * x) * Real.cos (b * x + (n : ℝ) / 2 * Real.pi) -
          Real.sin ((n : ℝ) * φ - (n : ℝ) / 2 * Real.pi) *
            Real.cosh (a * x) * Real.sin (b * x + (n : ℝ) / 2 * Real.pi)) := by
  exact (closedForms a b φ hamp hs hc n).2.2.1 x

theorem gap6 (a b φ x : ℝ) (n : ℕ) (hamp : 0 < a ^ 2 + b ^ 2)
    (hs : Real.sin φ = b / amplitude a b)
    (hc : Real.cos φ = a / amplitude a b) :
    iterDeriv n (y₄ a b) x =
      amplitude a b ^ n *
        (Real.cos ((n : ℝ) * φ - (n : ℝ) / 2 * Real.pi) *
            Real.sinh (a * x) * Real.sin (b * x + (n : ℝ) / 2 * Real.pi) +
          Real.sin ((n : ℝ) * φ - (n : ℝ) / 2 * Real.pi) *
            Real.cosh (a * x) * Real.cos (b * x + (n : ℝ) / 2 * Real.pi)) := by
  exact (closedForms a b φ hamp hs hc n).2.2.2 x

end

end ProofGap.Exercise1214
