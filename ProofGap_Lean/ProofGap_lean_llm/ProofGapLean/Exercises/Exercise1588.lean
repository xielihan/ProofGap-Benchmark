import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise1588

noncomputable section

def cost (a k s v : ℝ) := (a + k * v ^ 3) * (s / v)
def expandedCost (a k s v : ℝ) := a * s / v + s * k * v ^ 2
def cubeRoot (x : ℝ) := Real.rpow x (1 / 3 : ℝ)
def optimizer (a k : ℝ) := cubeRoot (a / (2 * k))
def Optimal (a k s v : ℝ) : Prop :=
  0 < v ∧ ∀ v₁, 0 < v₁ → expandedCost a k s v ≤ expandedCost a k s v₁

private theorem optimizer_pos (a k : ℝ) (ha : 0 < a) (hk : 0 < k) :
    0 < optimizer a k := by
  unfold optimizer cubeRoot
  apply Real.rpow_pos_of_pos
  exact div_pos ha (mul_pos zero_lt_two hk)

private theorem optimizer_cube (a k : ℝ) (ha : 0 < a) (hk : 0 < k) :
    optimizer a k ^ 3 = a / (2 * k) := by
  have hx : 0 < a / (2 * k) := div_pos ha (mul_pos zero_lt_two hk)
  unfold optimizer cubeRoot
  have hdef :
      Real.rpow (a / (2 * k)) (1 / 3 : ℝ) =
        Real.exp (Real.log (a / (2 * k)) * (1 / 3 : ℝ)) :=
    Real.rpow_def_of_pos hx (1 / 3 : ℝ)
  rw [hdef]
  let y : ℝ := Real.log (a / (2 * k)) * (1 / 3 : ℝ)
  change Real.exp y ^ 3 = a / (2 * k)
  calc
    Real.exp y ^ 3 = Real.exp (3 * y) := by
      rw [pow_three, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (Real.log (a / (2 * k))) := by
      congr 1
      dsimp [y]
      ring
    _ = a / (2 * k) := Real.exp_log hx

private theorem optimizer_relation (a k : ℝ) (ha : 0 < a) (hk : 0 < k) :
    a = 2 * k * optimizer a k ^ 3 := by
  have hc := optimizer_cube a k ha hk
  calc
    a = (a / (2 * k)) * (2 * k) := by
      field_simp [ne_of_gt hk]
    _ = optimizer a k ^ 3 * (2 * k) := by rw [← hc]
    _ = 2 * k * optimizer a k ^ 3 := by ring

private theorem optimizer_strict_expanded (a k s v : ℝ)
    (ha : 0 < a) (hk : 0 < k) (hs : 0 < s) (hv : 0 < v)
    (hne : v ≠ optimizer a k) :
    expandedCost a k s (optimizer a k) < expandedCost a k s v := by
  let r : ℝ := optimizer a k
  have hr : 0 < r := by
    dsimp [r]
    exact optimizer_pos a k ha hk
  have hrel : a = 2 * k * r ^ 3 := by
    dsimp [r]
    exact optimizer_relation a k ha hk
  have hne' : v ≠ r := by
    simpa [r] using hne
  have hdiff :
      expandedCost a k s v - expandedCost a k s r =
        s * k * (((v - r) ^ 2 * (v + 2 * r)) / v) := by
    unfold expandedCost
    rw [hrel]
    field_simp [ne_of_gt hv, ne_of_gt hr] <;> ring
  have hsub : v - r ≠ 0 := sub_ne_zero.mpr hne'
  have hsq : 0 < (v - r) ^ 2 := by
    rw [pow_two]
    exact mul_self_pos.mpr hsub
  have hsum : 0 < v + 2 * r :=
    add_pos hv (mul_pos zero_lt_two hr)
  have hfrac : 0 < ((v - r) ^ 2 * (v + 2 * r)) / v :=
    div_pos (mul_pos hsq hsum) hv
  have hpositive :
      0 < s * k * (((v - r) ^ 2 * (v + 2 * r)) / v) :=
    mul_pos (mul_pos hs hk) hfrac
  change expandedCost a k s r < expandedCost a k s v
  linarith [hdiff]

private theorem optimizer_min_expanded (a k s : ℝ)
    (ha : 0 < a) (hk : 0 < k) (hs : 0 < s) :
    ∀ v, 0 < v →
      expandedCost a k s (optimizer a k) ≤ expandedCost a k s v := by
  intro v hv
  by_cases hveq : v = optimizer a k
  · subst v
    exact le_rfl
  · exact le_of_lt (optimizer_strict_expanded a k s v ha hk hs hv hveq)

private theorem optimal_eq_optimizer (a k s v : ℝ)
    (ha : 0 < a) (hk : 0 < k) (hs : 0 < s)
    (h : Optimal a k s v) :
    v = optimizer a k := by
  by_contra hne
  have hstrict := optimizer_strict_expanded a k s v ha hk hs h.1 hne
  have hreverse := h.2 (optimizer a k) (optimizer_pos a k ha hk)
  exact (not_lt_of_ge hreverse) hstrict

theorem gap1 (a k s v : ℝ) (ha : 0 < a) (hk : 0 < k)
    (hs : 0 < s) (h : Optimal a k s v) :
    cost a k s v = (a + k * v ^ 3) * (s / v) := by
  rfl
theorem gap2 (a k s v : ℝ) (hv : v ≠ 0) :
    (a + k * v ^ 3) * (s / v) = expandedCost a k s v := by
  unfold expandedCost
  field_simp [hv] <;> ring
theorem gap3 (a k s v : ℝ) (hv : v ≠ 0) :
    cost a k s v = expandedCost a k s v := by
  unfold cost
  exact gap2 a k s v hv
theorem gap4 (a k s v : ℝ) (ha : 0 < a) (hk : 0 < k)
    (hs : 0 < s) (h : Optimal a k s v) :
    deriv (cost a k s) v = 0 := by
  have hv : v = optimizer a k := optimal_eq_optimizer a k s v ha hk hs h
  subst v
  let r : ℝ := optimizer a k
  have hrpos : 0 < r := by
    dsimp [r]
    exact optimizer_pos a k ha hk
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have hrel : a = 2 * k * r ^ 3 := by
    dsimp [r]
    exact optimizer_relation a k ha hk
  have hx3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * r ^ 2) r := by
    simpa [id, mul_comm] using (hasDerivAt_id r).pow 3
  have hnum :
      HasDerivAt (fun x : ℝ => a + k * x ^ 3)
        (3 * k * r ^ 2) r := by
    convert (hasDerivAt_const r a).add
      ((hasDerivAt_const r k).mul hx3) using 1 <;> ring
  have hden :
      HasDerivAt (fun x : ℝ => s / x) (-s / r ^ 2) r := by
    simpa [id] using
      (hasDerivAt_const r s).div (hasDerivAt_id r) hrne
  have hcost :
      HasDerivAt (cost a k s)
        ((3 * k * r ^ 2) * (s / r) +
          (a + k * r ^ 3) * (-s / r ^ 2)) r := by
    simpa only [cost] using hnum.mul hden
  have hd := hcost.deriv
  rw [hd, hrel]
  field_simp [hrne] <;> ring
theorem gap5 (a k s v : ℝ) (ha : 0 < a) (hk : 0 < k)
    (hs : 0 < s) (h : Optimal a k s v) :
    v = optimizer a k := by
  exact optimal_eq_optimizer a k s v ha hk hs h
theorem gap6 (a k s : ℝ) (ha : 0 < a) (hk : 0 < k) (hs : 0 < s) :
    IsMinOn (cost a k s) (Set.Ioi 0) (optimizer a k) := by
  intro v hv
  change cost a k s (optimizer a k) ≤ cost a k s v
  have hr : 0 < optimizer a k := optimizer_pos a k ha hk
  calc
    cost a k s (optimizer a k) =
        expandedCost a k s (optimizer a k) :=
      gap3 a k s (optimizer a k) (ne_of_gt hr)
    _ ≤ expandedCost a k s v :=
      optimizer_min_expanded a k s ha hk hs v hv
    _ = cost a k s v :=
      (gap3 a k s v (ne_of_gt hv)).symm
theorem gap7 (a k s v : ℝ) (ha : 0 < a) (hk : 0 < k) (hs : 0 < s) :
    v = optimizer a k ↔ Optimal a k s v := by
  constructor
  · intro hv
    subst v
    refine ⟨optimizer_pos a k ha hk, ?_⟩
    intro v₁ hv₁
    exact optimizer_min_expanded a k s ha hk hs v₁ hv₁
  · intro h
    exact optimal_eq_optimizer a k s v ha hk hs h

end
end ProofGap.Exercise1588
