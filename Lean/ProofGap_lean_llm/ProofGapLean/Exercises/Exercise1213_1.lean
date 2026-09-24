import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1213_1

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def wave (a b c x : ℝ) : ℝ := Real.exp (a * x) * Real.sin (b * x + c)
def amplitude (a b : ℝ) : ℝ := Real.sqrt (a ^ 2 + b ^ 2)

private theorem wave_hasDerivAt (a b c x : ℝ) :
    HasDerivAt (wave a b c)
      (Real.exp (a * x) *
        (a * Real.sin (b * x + c) + b * Real.cos (b * x + c))) x := by
  have hax : HasDerivAt (fun y : ℝ => a * y) a x := by
    simpa using (hasDerivAt_id x).const_mul a
  have hbx : HasDerivAt (fun y : ℝ => b * y + c) b x := by
    simpa using ((hasDerivAt_id x).const_mul b).const_add c
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (a * y))
      (Real.exp (a * x) * a) x :=
    (Real.hasDerivAt_exp (a * x)).comp x hax
  have hsin0 :
      HasDerivAt Real.sin (Real.cos (b * x + c)) (b * x + c) :=
    Real.hasDerivAt_sin (b * x + c)
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (b * y + c))
      (Real.cos (b * x + c) * b) x := by
    simpa only [Function.comp_apply] using hsin0.comp x hbx
  have hraw : HasDerivAt (wave a b c)
      ((Real.exp (a * x) * a) * Real.sin (b * x + c) +
        Real.exp (a * x) * (Real.cos (b * x + c) * b)) x := by
    simpa [wave] using hexp.mul hsin
  have hval :
      (Real.exp (a * x) * a) * Real.sin (b * x + c) +
          Real.exp (a * x) * (Real.cos (b * x + c) * b) =
        Real.exp (a * x) *
          (a * Real.sin (b * x + c) + b * Real.cos (b * x + c)) := by
    ring
  rw [hval] at hraw
  exact hraw

private theorem iterDeriv_step
    (a b c φ x : ℝ) (n : ℕ) (hamp : 0 < a ^ 2 + b ^ 2)
    (hs : Real.sin φ = b / amplitude a b)
    (hc : Real.cos φ = a / amplitude a b) :
    HasDerivAt
      (fun y : ℝ =>
        amplitude a b ^ n *
          (Real.exp (a * y) *
            Real.sin (b * y + c + (n : ℝ) * φ)))
      (amplitude a b ^ Nat.succ n *
        (Real.exp (a * x) *
          Real.sin (b * x + c + (Nat.succ n : ℝ) * φ))) x := by
  let R : ℝ := amplitude a b
  let t : ℝ := b * x + c + (n : ℝ) * φ
  change HasDerivAt
    (fun y : ℝ =>
      R ^ n *
        (Real.exp (a * y) * Real.sin (b * y + c + (n : ℝ) * φ)))
    (R ^ Nat.succ n *
      (Real.exp (a * x) *
        Real.sin (b * x + c + (Nat.succ n : ℝ) * φ))) x
  change Real.sin φ = b / R at hs
  change Real.cos φ = a / R at hc
  have hRpos : 0 < R := by
    dsimp [R, amplitude]
    exact Real.sqrt_pos.2 hamp
  have hR : R ≠ 0 := ne_of_gt hRpos
  have ha : a = R * Real.cos φ := by
    rw [hc]
    field_simp [hR] <;> ring
  have hb : b = R * Real.sin φ := by
    rw [hs]
    field_simp [hR] <;> ring
  have hax : HasDerivAt (fun y : ℝ => a * y) a x := by
    simpa using (hasDerivAt_id x).const_mul a
  have harg : HasDerivAt
      (fun y : ℝ => b * y + c + (n : ℝ) * φ) b x := by
    simpa using
      ((((hasDerivAt_id x).const_mul b).const_add c).const_add
        ((n : ℝ) * φ))
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (a * y))
      (Real.exp (a * x) * a) x :=
    (Real.hasDerivAt_exp (a * x)).comp x hax
  have hsin0 :
      HasDerivAt Real.sin
        (Real.cos (b * x + c + (n : ℝ) * φ))
        (b * x + c + (n : ℝ) * φ) :=
    Real.hasDerivAt_sin (b * x + c + (n : ℝ) * φ)
  have hsin : HasDerivAt
      (fun y : ℝ => Real.sin (b * y + c + (n : ℝ) * φ))
      (Real.cos (b * x + c + (n : ℝ) * φ) * b) x := by
    simpa only [Function.comp_apply] using hsin0.comp x harg
  have hraw : HasDerivAt
      (fun y : ℝ =>
        R ^ n *
          (Real.exp (a * y) * Real.sin (b * y + c + (n : ℝ) * φ)))
      (R ^ n *
        (((Real.exp (a * x) * a) * Real.sin t) +
          Real.exp (a * x) * (Real.cos t * b))) x := by
    dsimp [t]
    exact (hexp.mul hsin).const_mul (R ^ n)
  have htrig :
      a * Real.sin t + b * Real.cos t = R * Real.sin (t + φ) := by
    rw [ha, hb, Real.sin_add t φ]
    ring
  have hphase :
      t + φ = b * x + c + (Nat.succ n : ℝ) * φ := by
    dsimp [t]
    rw [Nat.cast_succ]
    ring
  have hval :
      R ^ n *
          (((Real.exp (a * x) * a) * Real.sin t) +
            Real.exp (a * x) * (Real.cos t * b)) =
        R ^ Nat.succ n *
          (Real.exp (a * x) *
            Real.sin (b * x + c + (Nat.succ n : ℝ) * φ)) := by
    calc
      R ^ n *
          (((Real.exp (a * x) * a) * Real.sin t) +
            Real.exp (a * x) * (Real.cos t * b)) =
          R ^ n *
            (Real.exp (a * x) *
              (a * Real.sin t + b * Real.cos t)) := by ring
      _ = R ^ n *
            (Real.exp (a * x) * (R * Real.sin (t + φ))) := by
          rw [htrig]
      _ = R ^ Nat.succ n *
            (Real.exp (a * x) * Real.sin (t + φ)) := by
          rw [pow_succ]
          ring
      _ = R ^ Nat.succ n *
            (Real.exp (a * x) *
              Real.sin (b * x + c + (Nat.succ n : ℝ) * φ)) := by
          rw [hphase]
  rw [hval] at hraw
  exact hraw

private theorem iterDeriv_closedForm
    (a b c φ x : ℝ) (n : ℕ) (hamp : 0 < a ^ 2 + b ^ 2)
    (hs : Real.sin φ = b / amplitude a b)
    (hc : Real.cos φ = a / amplitude a b) :
    iterDeriv n (wave a b c) x =
      amplitude a b ^ n *
        (Real.exp (a * x) *
          Real.sin (b * x + c + (n : ℝ) * φ)) := by
  induction n generalizing x with
  | zero =>
      simp [iterDeriv, wave]
  | succ n ih =>
      have hfun :
          (deriv^[n]) (wave a b c) =
            fun y : ℝ =>
              amplitude a b ^ n *
                (Real.exp (a * y) *
                  Real.sin (b * y + c + (n : ℝ) * φ)) := by
        funext y
        simpa only [iterDeriv] using (ih y)
      change (deriv^[Nat.succ n]) (wave a b c) x =
        amplitude a b ^ Nat.succ n *
          (Real.exp (a * x) *
            Real.sin (b * x + c + (Nat.succ n : ℝ) * φ))
      rw [Function.iterate_succ_apply']
      rw [hfun]
      exact (iterDeriv_step a b c φ x n hamp hs hc).deriv

theorem gap1 (a b c x : ℝ) :
    deriv (wave a b c) x =
      Real.exp (a * x) * (a * Real.sin (b * x + c) + b * Real.cos (b * x + c)) := by
  exact (wave_hasDerivAt a b c x).deriv

theorem gap2 (a b c x : ℝ) (hamp : 0 < a ^ 2 + b ^ 2) :
    deriv (wave a b c) x =
      amplitude a b * Real.exp (a * x) *
        (a / amplitude a b * Real.sin (b * x + c) +
          b / amplitude a b * Real.cos (b * x + c)) := by
  rw [gap1]
  have hA : amplitude a b ≠ 0 := by
    apply ne_of_gt
    unfold amplitude
    exact Real.sqrt_pos.2 hamp
  field_simp [hA] <;> ring

theorem gap3 (a b c φ x : ℝ) (hamp : 0 < a ^ 2 + b ^ 2)
    (hs : Real.sin φ = b / amplitude a b)
    (hc : Real.cos φ = a / amplitude a b) :
    deriv (wave a b c) x =
      amplitude a b * Real.exp (a * x) * Real.sin (b * x + c + φ) := by
  rw [gap2 a b c x hamp]
  rw [← hc, ← hs]
  rw [Real.sin_add (b * x + c) φ]
  ring

theorem gap4 (a b φ : ℝ) (hamp : 0 < a ^ 2 + b ^ 2)
    (hs : Real.sin φ = b / amplitude a b) :
    Real.sin φ = b / amplitude a b := by
  exact hs

theorem gap5 (a b φ : ℝ) (hamp : 0 < a ^ 2 + b ^ 2)
    (hc : Real.cos φ = a / amplitude a b) :
    Real.cos φ = a / amplitude a b := by
  exact hc

theorem gap6 (a b c φ x : ℝ) (hamp : 0 < a ^ 2 + b ^ 2)
    (hs : Real.sin φ = b / amplitude a b)
    (hc : Real.cos φ = a / amplitude a b) :
    iterDeriv 2 (wave a b c) x =
      amplitude a b ^ 2 * Real.exp (a * x) *
        Real.sin (b * x + c + 2 * φ) := by
  simpa [mul_assoc] using
    (iterDeriv_closedForm a b c φ x 2 hamp hs hc)

theorem gap7 (a b c φ x : ℝ) (n : ℕ) (hamp : 0 < a ^ 2 + b ^ 2)
    (hs : Real.sin φ = b / amplitude a b)
    (hc : Real.cos φ = a / amplitude a b) :
    iterDeriv n (wave a b c) x =
      amplitude a b ^ n * Real.exp (a * x) *
        Real.sin (b * x + c + (n : ℝ) * φ) := by
  simpa [mul_assoc] using
    (iterDeriv_closedForm a b c φ x n hamp hs hc)

theorem gap8 (a b c φ x : ℝ) (n : ℕ) (hamp : 0 < a ^ 2 + b ^ 2)
    (hs : Real.sin φ = b / amplitude a b)
    (hc : Real.cos φ = a / amplitude a b) :
    iterDeriv n (wave a b c) x =
      Real.exp (a * x) * amplitude a b ^ n *
        Real.sin (b * x + c + (n : ℝ) * φ) := by
  rw [gap7 a b c φ x n hamp hs hc]
  ring

end

end ProofGap.Exercise1213_1
