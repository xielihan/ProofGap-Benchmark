import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3276

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def nthDifferential (n : ℕ) (f : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  iterDeriv n (fun t => f (x + t * dx) (y + t * dy)) 0

def coordinateDifferential (n : ℕ) (f : ℝ → ℝ)
    (x dx : ℝ) : ℝ :=
  iterDeriv n f x * dx ^ n

def leibnizDifferential (n : ℕ) (X Y : ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℝ) *
      coordinateDifferential (n - k) X x dx *
      coordinateDifferential k Y y dy

def coordinateExpansion (n : ℕ) (X Y : ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℝ) *
      iterDeriv (n - k) X x * iterDeriv k Y y *
      dx ^ (n - k) * dy ^ k

private theorem iterDeriv_affine (n : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ n f) (x dx : ℝ) :
    iterDeriv n (fun t => f (x + t * dx)) 0 =
      iterDeriv n f x * dx ^ n := by
  unfold iterDeriv
  rw [← iteratedDeriv_eq_iterate, ← iteratedDeriv_eq_iterate]
  let g : ℝ → ℝ := fun z => f (x + z)
  have hg : ContDiff ℝ n g := by
    dsimp [g]
    fun_prop
  have hscale := congrFun (iteratedDeriv_comp_const_mul hg dx) 0
  have hshift := congrFun (iteratedDeriv_comp_const_add n f x) 0
  rw [show (fun t => f (x + t * dx)) = fun t => g (dx * t) by
    funext t
    simp [g, mul_comm]]
  rw [hscale]
  simp only [mul_zero]
  change dx ^ n * iteratedDeriv n g 0 =
    iteratedDeriv n f x * dx ^ n
  rw [show iteratedDeriv n g 0 = iteratedDeriv n f x by
    simpa [g] using hshift]
  ring

theorem gap1 (u : ℝ → ℝ → ℝ) (X Y : ℝ → ℝ)
    (hu : ∀ x y, u x y = X x * Y y)
    (n : ℕ) (hX : ContDiff ℝ n X) (hY : ContDiff ℝ n Y)
    (x y dx dy : ℝ) :
    nthDifferential n u x y dx dy =
      leibnizDifferential n X Y x y dx dy := by
  unfold nthDifferential leibnizDifferential coordinateDifferential
  rw [show (fun t => u (x + t * dx) (y + t * dy)) =
      fun t => Y (y + t * dy) * X (x + t * dx) by
    funext t
    rw [hu]
    ring]
  unfold iterDeriv
  rw [← iteratedDeriv_eq_iterate]
  have hXline : ContDiff ℝ n (fun t => X (x + t * dx)) := by
    fun_prop
  have hYline : ContDiff ℝ n (fun t => Y (y + t * dy)) := by
    fun_prop
  rw [iteratedDeriv_fun_mul hYline.contDiffAt hXline.contDiffAt]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ n := by
    simpa using (Finset.mem_range.mp hk)
  have hnk_le : n - k ≤ n := Nat.sub_le n k
  have hyline :
      iteratedDeriv k (fun t => Y (y + t * dy)) 0 =
        (deriv^[k]) Y y * dy ^ k := by
    simpa [iterDeriv, iteratedDeriv_eq_iterate] using
      iterDeriv_affine k Y
        (hY.of_le
          (WithTop.coe_le_coe.mpr (ENat.coe_le_coe.mpr hk_le))) y dy
  have hxline :
      iteratedDeriv (n - k) (fun t => X (x + t * dx)) 0 =
        (deriv^[n - k]) X x * dx ^ (n - k) := by
    simpa [iterDeriv, iteratedDeriv_eq_iterate] using
      iterDeriv_affine (n - k) X
        (hX.of_le
          (WithTop.coe_le_coe.mpr (ENat.coe_le_coe.mpr hnk_le))) x dx
  rw [hyline, hxline]
  ring

theorem gap2 (n : ℕ) (X Y : ℝ → ℝ) (x y dx dy : ℝ) :
    leibnizDifferential n X Y x y dx dy =
      coordinateExpansion n X Y x y dx dy := by
  unfold leibnizDifferential coordinateExpansion coordinateDifferential
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem gap3 (u : ℝ → ℝ → ℝ) (X Y : ℝ → ℝ)
    (hu : ∀ x y, u x y = X x * Y y)
    (n : ℕ) (hX : ContDiff ℝ n X) (hY : ContDiff ℝ n Y)
    (x y dx dy : ℝ) :
    nthDifferential n u x y dx dy =
      coordinateExpansion n X Y x y dx dy := by
  rw [gap1 u X Y hu n hX hY x y dx dy,
    gap2 n X Y x y dx dy]

end

end ProofGap.Exercise3276
