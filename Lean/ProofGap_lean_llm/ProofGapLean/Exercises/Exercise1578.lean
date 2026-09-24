import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1578

noncomputable section

def height (V r : ℝ) : ℝ := V / (Real.pi * r ^ 2) - (2 / 3 : ℝ) * r
def surface (V r : ℝ) : ℝ := (5 / 3 : ℝ) * Real.pi * r ^ 2 + 2 * V / r
def optimizer (V : ℝ) : ℝ := Real.cbrt (3 * V / (5 * Real.pi))

def Feasible (V r h : ℝ) : Prop :=
  0 < r ∧ 0 < h ∧
    V = (2 / 3 : ℝ) * Real.pi * r ^ 3 + Real.pi * r ^ 2 * h

def IsOptimal (V r h : ℝ) : Prop :=
  Feasible V r h ∧ ∀ r₁ h₁, Feasible V r₁ h₁ →
    3 * Real.pi * r ^ 2 + 2 * Real.pi * r * h ≤
      3 * Real.pi * r₁ ^ 2 + 2 * Real.pi * r₁ * h₁

private lemma cbrt_cubed_of_pos (x : ℝ) (hx : 0 < x) :
    Real.cbrt (x ^ 3) = x := by
  have hcube : 0 < x ^ 3 := by positivity
  have hrpow : (x ^ 3 : ℝ) ^ (1 / 3 : ℝ) = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  simpa [Real.cbrt, hcube, hcube.le, hx, hx.le] using hrpow

private lemma optimizer_spec (V : ℝ) (hV : 0 < V) :
    0 < optimizer V ∧
      optimizer V ^ 3 = 3 * V / (5 * Real.pi) ∧
      V = (5 / 3 : ℝ) * Real.pi * optimizer V ^ 3 := by
  have harg : 0 < 3 * V / (5 * Real.pi) := by
    positivity
  have hcform :
      optimizer V = (3 * V / (5 * Real.pi)) ^ (1 / 3 : ℝ) := by
    unfold optimizer
    simp [Real.cbrt, harg, harg.le]
  have hx : 0 < optimizer V := by
    rw [hcform]
    exact Real.rpow_pos_of_pos harg _
  have hxcube : optimizer V ^ 3 = 3 * V / (5 * Real.pi) := by
    rw [hcform, ← Real.rpow_natCast, ← Real.rpow_mul harg.le]
    norm_num
  have hVx : V = (5 / 3 : ℝ) * Real.pi * optimizer V ^ 3 := by
    rw [hxcube]
    field_simp [ne_of_gt Real.pi_pos] <;> ring
  exact ⟨hx, hxcube, hVx⟩

theorem gap1 (V r h : ℝ) (hfeas : Feasible V r h) :
    V = (2 / 3 : ℝ) * Real.pi * r ^ 3 + Real.pi * r ^ 2 * h := by
  exact hfeas.2.2

theorem gap2 (V r h : ℝ) (hfeas : Feasible V r h) :
    h = height V r := by
  rcases hfeas with ⟨hr, _, hvol⟩
  unfold height
  rw [hvol]
  field_simp [hr.ne', ne_of_gt Real.pi_pos] <;> ring

theorem gap3 (V r : ℝ) :
    3 * Real.pi * r ^ 2 + 2 * Real.pi * r * height V r =
      surface V r := by
  unfold height surface
  by_cases hr : r = 0
  · subst r
    simp
  · field_simp [hr, ne_of_gt Real.pi_pos] <;> ring

theorem gap4 (V r : ℝ) :
    3 * Real.pi * r ^ 2 +
        2 * Real.pi * r * (V / (Real.pi * r ^ 2) - (2 / 3 : ℝ) * r) =
      (5 / 3 : ℝ) * Real.pi * r ^ 2 + 2 * V / r := by
  by_cases hr : r = 0
  · subst r
    simp
  · field_simp [hr, ne_of_gt Real.pi_pos] <;> ring

theorem gap5 (V r : ℝ) :
    surface V r = (5 / 3 : ℝ) * Real.pi * r ^ 2 + 2 * V / r := by
  rfl

theorem gap6 (V r : ℝ) (hr : r ≠ 0) :
    deriv (surface V) r = (10 / 3 : ℝ) * Real.pi * r - 2 * V / r ^ 2 := by
  have hsq : HasDerivAt (fun x : ℝ => x * x) (2 * r) r := by
    convert (hasDerivAt_id r).mul (hasDerivAt_id r) using 1 <;>
      dsimp [id] <;> ring
  have hfirst :
      HasDerivAt (fun x : ℝ => (5 / 3 : ℝ) * Real.pi * x ^ 2)
        ((10 / 3 : ℝ) * Real.pi * r) r := by
    convert hsq.const_mul ((5 / 3 : ℝ) * Real.pi) using 1 <;>
      norm_num <;> ring
  have hsecond :
      HasDerivAt (fun x : ℝ => 2 * V / x) (-2 * V / r ^ 2) r := by
    convert (hasDerivAt_const r (2 * V)).div (hasDerivAt_id r) hr using 1 <;>
      dsimp [id] <;> ring
  have hsum :
      HasDerivAt
        (fun x : ℝ =>
          (5 / 3 : ℝ) * Real.pi * x ^ 2 + 2 * V / x)
        ((10 / 3 : ℝ) * Real.pi * r + (-2 * V / r ^ 2)) r :=
    hfirst.add hsecond
  change deriv
      (fun x : ℝ => (5 / 3 : ℝ) * Real.pi * x ^ 2 + 2 * V / x) r = _
  convert hsum.deriv using 1 <;> ring

theorem gap7 (V r : ℝ) (hV : 0 < V) (hr : 0 < r)
    (hcrit : deriv (surface V) r = 0) :
    r = optimizer V := by
  have heq : (10 / 3 : ℝ) * Real.pi * r - 2 * V / r ^ 2 = 0 := by
    calc
      (10 / 3 : ℝ) * Real.pi * r - 2 * V / r ^ 2 = deriv (surface V) r :=
        (gap6 V r hr.ne').symm
      _ = 0 := hcrit
  have hc : r ^ 3 = 3 * V / (5 * Real.pi) := by
    field_simp [hr.ne', ne_of_gt Real.pi_pos] at heq ⊢
    nlinarith
  simpa only [optimizer, hc] using (cbrt_cubed_of_pos r hr).symm

theorem gap8 (V : ℝ) (hV : 0 < V) :
    height V (optimizer V) = optimizer V := by
  rcases optimizer_spec V hV with ⟨hx, _, hVx⟩
  unfold height
  rw [sub_eq_iff_eq_add]
  have hden : Real.pi * optimizer V ^ 2 ≠ 0 := by
    positivity
  apply (div_eq_iff hden).2
  calc
    V = (5 / 3 : ℝ) * Real.pi * optimizer V ^ 3 := hVx
    _ = (optimizer V + (2 / 3 : ℝ) * optimizer V) *
          (Real.pi * optimizer V ^ 2) := by ring

theorem gap9 (V : ℝ) (hV : 0 < V) :
    ∀ r > 0, surface V (optimizer V) ≤ surface V r := by
  intro r hr
  let x := optimizer V
  have hspec :
      0 < x ∧ x ^ 3 = 3 * V / (5 * Real.pi) ∧
        V = (5 / 3 : ℝ) * Real.pi * x ^ 3 := by
    simpa only [x] using optimizer_spec V hV
  rcases hspec with ⟨hx, _, hVx⟩
  change surface V x ≤ surface V r
  have hsx : surface V x = 5 * Real.pi * x ^ 2 := by
    rw [gap5, hVx]
    field_simp [hx.ne'] <;> ring
  rw [hsx, gap5 V r, hVx]
  let d : ℝ :=
    (5 / 3 : ℝ) * Real.pi * r ^ 2 +
      2 * ((5 / 3 : ℝ) * Real.pi * x ^ 3) / r -
      5 * Real.pi * x ^ 2
  have hid :
      r * d =
        (5 / 3 : ℝ) * Real.pi * (r - x) ^ 2 * (r + 2 * x) := by
    dsimp [d]
    field_simp [hr.ne'] <;> ring
  have hprod :
      0 ≤ (5 / 3 : ℝ) * Real.pi * (r - x) ^ 2 * (r + 2 * x) := by
    positivity
  have hrd : 0 ≤ r * d := by
    rw [hid]
    exact hprod
  have hd : 0 ≤ d := by
    by_contra hnot
    have hdneg : d < 0 := lt_of_not_ge hnot
    exact (not_lt_of_ge hrd) (mul_neg_of_pos_of_neg hr hdneg)
  dsimp [d] at hd
  exact sub_nonneg.mp hd

theorem gap10 (V : ℝ) (hV : 0 < V) :
    IsOptimal V (optimizer V) (optimizer V) := by
  let x := optimizer V
  have hspec :
      0 < x ∧ x ^ 3 = 3 * V / (5 * Real.pi) ∧
        V = (5 / 3 : ℝ) * Real.pi * x ^ 3 := by
    simpa only [x] using optimizer_spec V hV
  rcases hspec with ⟨hx, _, hVx⟩
  have hfeas : Feasible V x x := by
    refine ⟨hx, hx, ?_⟩
    rw [hVx]
    ring
  refine ⟨hfeas, ?_⟩
  intro r₁ h₁ hfeas₁
  have hs : surface V x ≤ surface V r₁ := by
    simpa only [x] using gap9 V hV r₁ hfeas₁.1
  have hxheight : height V x = x := by
    simpa only [x] using gap8 V hV
  have hh₁ : h₁ = height V r₁ := gap2 V r₁ h₁ hfeas₁
  calc
    3 * Real.pi * x ^ 2 + 2 * Real.pi * x * x = surface V x := by
      simpa only [hxheight] using gap3 V x
    _ ≤ surface V r₁ := hs
    _ = 3 * Real.pi * r₁ ^ 2 + 2 * Real.pi * r₁ * h₁ := by
      simpa only [hh₁] using (gap3 V r₁).symm

end

end ProofGap.Exercise1578
