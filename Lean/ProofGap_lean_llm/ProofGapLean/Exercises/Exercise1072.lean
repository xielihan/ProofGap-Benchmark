import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1072

def cubic (p q x : ℝ) : ℝ := x ^ 3 + p * x + q

def repeatedRoot (p q : ℝ) : Prop :=
  ∃ x, 3 * x ^ 2 + p = 0 ∧ cubic p q x = 0

theorem gap1 (p q x : ℝ) :
    HasDerivAt (cubic p q) (3 * x ^ 2 + p) x := by
  unfold cubic
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hsquare : HasDerivAt (fun y : ℝ => y * y) (x + x) x := by
    simpa only [one_mul, mul_one] using hid.mul hid
  have hcubeRaw :
      HasDerivAt (fun y : ℝ => (y * y) * y) ((x + x) * x + x * x) x := by
    simpa only [one_mul, mul_one] using hsquare.mul hid
  have hcube : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    have hf : (fun y : ℝ => (y * y) * y) = fun y : ℝ => y ^ 3 := by
      funext y
      ring
    have hd : (x + x) * x + x * x = 3 * x ^ 2 := by
      ring
    rw [hf, hd] at hcubeRaw
    exact hcubeRaw
  have hlinear : HasDerivAt (fun y : ℝ => p * y) p x := by
    simpa only [zero_mul, zero_add, mul_one] using
      (hasDerivAt_const x p).mul hid
  have hconstant : HasDerivAt (fun _ : ℝ => q) 0 x := hasDerivAt_const x q
  have hsum :
      HasDerivAt (fun y : ℝ => y ^ 3 + p * y + q)
        ((3 * x ^ 2 + p) + 0) x :=
    HasDerivAt.add (HasDerivAt.add hcube hlinear) hconstant
  simpa only [add_zero] using hsum

theorem gap2 (p q : ℝ) (hrep : repeatedRoot p q) :
    ∃ x, 3 * x ^ 2 + p = 0 ∧ cubic p q x = 0 := by
  exact hrep

theorem gap3 (p q : ℝ) (hrep : repeatedRoot p q) :
    ∃ x, cubic p q x = 0 ∧ 3 * x ^ 2 + p = 0 := by
  rcases hrep with ⟨x, hd, hc⟩
  exact ⟨x, hc, hd⟩

theorem gap4 (p q : ℝ) (hrep : repeatedRoot p q) :
    ∃ x, 3 * x ^ 2 + p = 0 ∧ cubic p q x = 0 := by
  exact hrep

theorem gap5 (p q : ℝ) (hrep : repeatedRoot p q) :
    ∃ x, x ^ 2 = -(p / 3) := by
  rcases hrep with ⟨x, hd, _⟩
  refine ⟨x, ?_⟩
  linarith

theorem gap6 (p q : ℝ) (hrep : repeatedRoot p q) :
    ∃ x, x * (x ^ 2 + p) = -q := by
  rcases hrep with ⟨x, _, hc⟩
  refine ⟨x, ?_⟩
  calc
    x * (x ^ 2 + p) = cubic p q x - q := by
      unfold cubic
      ring
    _ = -q := by
      rw [hc]
      ring

theorem gap7 (p q : ℝ) (hrep : repeatedRoot p q) :
    ∃ x, x ^ 2 = -(p / 3) ∧ x * (-(p / 3) + p) = -q := by
  rcases hrep with ⟨x, hd, hc⟩
  have hs : x ^ 2 = -(p / 3) := by
    linarith
  refine ⟨x, hs, ?_⟩
  calc
    x * (-(p / 3) + p) = x * (x ^ 2 + p) := by rw [hs]
    _ = cubic p q x - q := by
      unfold cubic
      ring
    _ = -q := by
      rw [hc]
      ring

theorem gap8 (p q : ℝ) (hrep : repeatedRoot p q) :
    ∃ x, x ^ 2 = -(p / 3) ∧ x * (2 * p / 3) = -q := by
  rcases gap7 p q hrep with ⟨x, hs, hq⟩
  refine ⟨x, hs, ?_⟩
  calc
    x * (2 * p / 3) = x * (-(p / 3) + p) := by ring
    _ = -q := hq

theorem gap9 (p q : ℝ) (hrep : repeatedRoot p q) (hp : p ≠ 0) :
    ∃ x, x = -(3 * q) / (2 * p) := by
  exact ⟨-(3 * q) / (2 * p), rfl⟩

theorem gap10 (p q : ℝ) (hrep : repeatedRoot p q) (hp : p ≠ 0) :
    (-(3 * q) / (2 * p)) ^ 2 = -(p / 3) := by
  rcases gap8 p q hrep with ⟨x, hs, hxq⟩
  have hx : x = -(3 * q) / (2 * p) := by
    field_simp [hp] <;> nlinarith [hxq]
  rw [← hx]
  exact hs

theorem gap11 (p q : ℝ) (hrep : repeatedRoot p q) (hp : p ≠ 0) :
    9 * q ^ 2 / (4 * p ^ 2) = -(p / 3) := by
  calc
    9 * q ^ 2 / (4 * p ^ 2) = (-(3 * q) / (2 * p)) ^ 2 := by
      field_simp [hp] <;> ring
    _ = -(p / 3) := gap10 p q hrep hp

theorem gap12 (p q : ℝ) (hrep : repeatedRoot p q) (hp : p ≠ 0) :
    27 * q ^ 2 = -4 * p ^ 3 := by
  calc
    27 * q ^ 2 = 3 * (4 * p ^ 2) * (9 * q ^ 2 / (4 * p ^ 2)) := by
      field_simp [hp] <;> ring
    _ = 3 * (4 * p ^ 2) * (-(p / 3)) := by
      rw [gap11 p q hrep hp]
    _ = -4 * p ^ 3 := by ring

theorem gap13 (p q : ℝ) (hrep : repeatedRoot p q) :
    4 * p ^ 3 + 27 * q ^ 2 = 0 := by
  by_cases hp : p = 0
  · subst p
    rcases hrep with ⟨x, hd, hc⟩
    have hx : x = 0 := by
      nlinarith [sq_nonneg x]
    subst x
    simp [cubic] at hc
    simp [hc]
  · have h := gap12 p q hrep hp
    nlinarith [h]

theorem gap14 (p q : ℝ) (hrep : repeatedRoot p q) :
    (p / 3) ^ 3 + (q / 2) ^ 2 = 0 := by
  calc
    (p / 3) ^ 3 + (q / 2) ^ 2 = (4 * p ^ 3 + 27 * q ^ 2) / 108 := by ring
    _ = 0 := by
      rw [gap13 p q hrep]
      ring

theorem gap15 (p q : ℝ) :
    (p, q) ∈ {r : ℝ × ℝ | (r.1 / 3) ^ 3 + (r.2 / 2) ^ 2 = 0} ↔
      repeatedRoot p q := by
  constructor
  · intro hcurve
    change (p / 3) ^ 3 + (q / 2) ^ 2 = 0 at hcurve
    unfold repeatedRoot
    have hdisc : 4 * p ^ 3 + 27 * q ^ 2 = 0 := by
      calc
        4 * p ^ 3 + 27 * q ^ 2 = 108 * ((p / 3) ^ 3 + (q / 2) ^ 2) := by ring
        _ = 0 := by rw [hcurve]; ring
    by_cases hp : p = 0
    · subst p
      have hq : q = 0 := by
        nlinarith [sq_nonneg q]
      subst q
      refine ⟨0, ?_, ?_⟩
      · ring
      · unfold cubic
        ring
    · let x : ℝ := -(3 * q) / (2 * p)
      have hs : x ^ 2 = -(p / 3) := by
        dsimp [x]
        field_simp [hp] <;> nlinarith [hdisc]
      have hxq : x * (2 * p / 3) = -q := by
        dsimp [x]
        field_simp [hp] <;> ring
      have hd : 3 * x ^ 2 + p = 0 := by
        rw [hs]
        ring
      have hc : cubic p q x = 0 := by
        unfold cubic
        calc
          x ^ 3 + p * x + q = x * (x ^ 2 + p) + q := by ring
          _ = x * (-(p / 3) + p) + q := by rw [hs]
          _ = x * (2 * p / 3) + q := by ring
          _ = 0 := by rw [hxq]; ring
      exact ⟨x, hd, hc⟩
  · intro hrep
    change (p / 3) ^ 3 + (q / 2) ^ 2 = 0
    exact gap14 p q hrep

end ProofGap.Exercise1072
