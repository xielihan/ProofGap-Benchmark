import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1213_2

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def wave (a b c x : ℝ) : ℝ := Real.exp (a * x) * Real.cos (b * x + c)
def amplitude (a b : ℝ) : ℝ := Real.sqrt (a ^ 2 + b ^ 2)

theorem gap1 (a b c φ x : ℝ) (n : ℕ) (hamp : 0 < a ^ 2 + b ^ 2)
    (hs : Real.sin φ = b / amplitude a b)
    (hc : Real.cos φ = a / amplitude a b) :
    iterDeriv n (wave a b c) x =
      amplitude a b ^ n * Real.exp (a * x) *
        Real.cos (b * x + c + (n : ℝ) * φ) := by
  have hApos : 0 < amplitude a b := by
    simpa [amplitude] using Real.sqrt_pos.2 hamp
  have hAne : amplitude a b ≠ 0 := ne_of_gt hApos
  have hAc : amplitude a b * Real.cos φ = a := by
    calc
      amplitude a b * Real.cos φ = amplitude a b * (a / amplitude a b) := by rw [hc]
      _ = a := by field_simp [hAne]
  have hAs : amplitude a b * Real.sin φ = b := by
    calc
      amplitude a b * Real.sin φ = amplitude a b * (b / amplitude a b) := by rw [hs]
      _ = b := by field_simp [hAne]
  have hderiv (d y : ℝ) :
      HasDerivAt (wave a b d)
        (amplitude a b * Real.exp (a * y) *
          Real.cos (b * y + d + φ)) y := by
    have ha : HasDerivAt (fun z : ℝ => a * z) a y := by
      simpa using (hasDerivAt_id y).const_mul a
    have he : HasDerivAt (fun z : ℝ => Real.exp (a * z))
        (a * Real.exp (a * y)) y := by
      convert (Real.hasDerivAt_exp (a * y)).comp y ha using 1 <;> ring
    have hb0 : HasDerivAt (fun z : ℝ => b * z) b y := by
      simpa using (hasDerivAt_id y).const_mul b
    have hb : HasDerivAt (fun z : ℝ => b * z + d) b y := by
      simpa using hb0.add_const d
    have hco : HasDerivAt (fun z : ℝ => Real.cos (b * z + d))
        (-b * Real.sin (b * y + d)) y := by
      convert (Real.hasDerivAt_cos (b * y + d)).comp y hb using 1 <;> ring
    have hp : HasDerivAt (wave a b d)
        ((a * Real.exp (a * y)) * Real.cos (b * y + d) +
          Real.exp (a * y) * (-b * Real.sin (b * y + d))) y := by
      simpa [wave] using he.mul hco
    have hphase :
        a * Real.cos (b * y + d) - b * Real.sin (b * y + d) =
          amplitude a b * Real.cos (b * y + d + φ) := by
      calc
        a * Real.cos (b * y + d) - b * Real.sin (b * y + d) =
            (amplitude a b * Real.cos φ) * Real.cos (b * y + d) -
              (amplitude a b * Real.sin φ) * Real.sin (b * y + d) := by
                rw [hAc, hAs]
        _ = amplitude a b *
            (Real.cos (b * y + d) * Real.cos φ -
              Real.sin (b * y + d) * Real.sin φ) := by ring
        _ = amplitude a b * Real.cos (b * y + d + φ) := by
              rw [Real.cos_add (b * y + d) φ]
    have hcoef :
        (a * Real.exp (a * y)) * Real.cos (b * y + d) +
            Real.exp (a * y) * (-b * Real.sin (b * y + d)) =
          amplitude a b * Real.exp (a * y) *
            Real.cos (b * y + d + φ) := by
      calc
        (a * Real.exp (a * y)) * Real.cos (b * y + d) +
            Real.exp (a * y) * (-b * Real.sin (b * y + d)) =
          Real.exp (a * y) *
            (a * Real.cos (b * y + d) - b * Real.sin (b * y + d)) := by ring
        _ = Real.exp (a * y) *
            (amplitude a b * Real.cos (b * y + d + φ)) := by rw [hphase]
        _ = amplitude a b * Real.exp (a * y) *
            Real.cos (b * y + d + φ) := by ring
    rw [← hcoef]
    exact hp
  have hiter : ∀ m : ℕ,
      iterDeriv m (wave a b c) =
        fun y => amplitude a b ^ m *
          wave a b (c + (m : ℝ) * φ) y := by
    intro m
    induction m with
    | zero =>
        funext y
        simp [iterDeriv]
    | succ m ih =>
        funext y
        change (deriv^[Nat.succ m]) (wave a b c) y = _
        rw [Function.iterate_succ_apply']
        change deriv (iterDeriv m (wave a b c)) y = _
        rw [ih]
        calc
          deriv (fun z => amplitude a b ^ m *
              wave a b (c + (m : ℝ) * φ) z) y =
              amplitude a b ^ m *
                (amplitude a b * Real.exp (a * y) *
                  Real.cos (b * y + (c + (m : ℝ) * φ) + φ)) :=
            ((hderiv (c + (m : ℝ) * φ) y).const_mul
              (amplitude a b ^ m)).deriv
          _ = amplitude a b ^ Nat.succ m *
              wave a b (c + (Nat.succ m : ℝ) * φ) y := by
                simp only [wave, pow_succ, Nat.cast_succ]
                ring_nf
  simpa only [wave, mul_assoc, add_assoc] using congrFun (hiter n) x

theorem gap2 (a b c φ x : ℝ) (n : ℕ) (hamp : 0 < a ^ 2 + b ^ 2)
    (hs : Real.sin φ = b / amplitude a b)
    (hc : Real.cos φ = a / amplitude a b) :
    iterDeriv n (wave a b c) x =
      Real.exp (a * x) * amplitude a b ^ n *
        Real.cos (b * x + c + (n : ℝ) * φ) := by
  calc
    iterDeriv n (wave a b c) x =
        amplitude a b ^ n * Real.exp (a * x) *
          Real.cos (b * x + c + (n : ℝ) * φ) :=
      gap1 a b c φ x n hamp hs hc
    _ = Real.exp (a * x) * amplitude a b ^ n *
          Real.cos (b * x + c + (n : ℝ) * φ) := by ring

end

end ProofGap.Exercise1213_2
