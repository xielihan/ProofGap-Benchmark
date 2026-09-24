import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

open Filter Topology
open scoped Interval

namespace ProofGap.Exercise2224

noncomputable section

def riemannSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n,
    (1 / (n : ℝ)) * Real.sqrt (1 + (i : ℝ) / n)

private theorem sqrt_integral_value :
    (∫ x in (0 : ℝ)..1, Real.sqrt (1 + x)) =
      (2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1) := by
  let F : ℝ → ℝ := fun x => (2 / 3 : ℝ) * ((1 + x) * Real.sqrt (1 + x))
  have hcont : Continuous (fun x : ℝ => Real.sqrt (1 + x)) :=
    Real.continuous_sqrt.comp (continuous_const.add continuous_id)
  have hint : IntervalIntegrable (fun x : ℝ => Real.sqrt (1 + x))
      MeasureTheory.volume 0 1 :=
    hcont.continuousOn.intervalIntegrable
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt F (Real.sqrt (1 + x)) x := by
    intro x hx
    have hx' : 0 ≤ x ∧ x ≤ 1 := by
      simpa [Set.mem_uIcc] using hx
    have hxpos : 0 < 1 + x := by linarith [hx'.1]
    have hg : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
      simpa using (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
    have hs : HasDerivAt (fun y : ℝ => Real.sqrt (1 + y))
        ((2 * Real.sqrt (1 + x))⁻¹) x := by
      simpa using (Real.hasDerivAt_sqrt (ne_of_gt hxpos)).comp x hg
    have hspos : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.2 hxpos
    have hsq : (Real.sqrt (1 + x)) ^ 2 = 1 + x :=
      Real.sq_sqrt (le_of_lt hxpos)
    have hp := (hg.mul hs).const_mul (2 / 3 : ℝ)
    convert hp using 1
    field_simp [ne_of_gt hspos]
    nlinarith [hsq]
  calc
    (∫ x in (0 : ℝ)..1, Real.sqrt (1 + x)) = F 1 - F 0 :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt hF) hint
    _ = (2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1) := by
      norm_num [F]
      ring

theorem gap1 :
    Tendsto riemannSum atTop
      (𝓝 (∫ x in (0 : ℝ)..1, Real.sqrt (1 + x))) := by
  rw [sqrt_integral_value]
  let X : ℕ → ℕ → ℝ := fun n i => Real.sqrt (1 + (i : ℝ) / n)
  let A : ℕ → ℕ → ℝ := fun n i =>
    (2 / 3 : ℝ) * ((1 + (i : ℝ) / n) * X n i)
  have htel (B : ℕ → ℝ) (m : ℕ) :
      Finset.sum (Finset.range (m + 1))
        (fun i => B i - B (i - 1)) = B m - B 0 := by
    induction m with
    | zero => simp
    | succ m ihm =>
        rw [Finset.sum_range_succ, ihm] <;>
          simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] <;> ring
  have htel_Icc (B : ℕ → ℝ) (m : ℕ) :
      Finset.sum (Finset.Icc 1 m) (fun i => B i - B (i - 1)) =
        B m - B 0 := by
    have hset : Finset.Icc 1 m = (Finset.range (m + 1)).erase 0 := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
      omega
    rw [hset]
    calc
      Finset.sum ((Finset.range (m + 1)).erase 0)
          (fun i => B i - B (i - 1)) =
          Finset.sum (Finset.range (m + 1))
            (fun i => B i - B (i - 1)) := by
        apply Finset.sum_subset
        · exact Finset.erase_subset _ _
        · intro i hiRange hiErase
          have hi0 : i = 0 := by
            by_contra hne
            exact hiErase (Finset.mem_erase.mpr ⟨hne, hiRange⟩)
          subst i
          simp
      _ = B m - B 0 := htel B m
  have hbds : ∀ᶠ n : ℕ in atTop,
      (2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1) ≤ riemannSum n ∧
      riemannSum n ≤ (2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1) +
        (1 / (n : ℝ)) * (Real.sqrt 2 - 1) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < n := by omega
    have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hnR : (n : ℝ) ≠ 0 := ne_of_gt hnRpos
    have hlocal : ∀ i ∈ Finset.Icc 1 n,
        0 ≤ (1 / (n : ℝ)) * X n i - (A n i - A n (i - 1)) ∧
        (1 / (n : ℝ)) * X n i - (A n i - A n (i - 1)) ≤
          (1 / (n : ℝ)) * (X n i - X n (i - 1)) := by
      intro i hi
      have hi' : 1 ≤ i ∧ i ≤ n := by simpa using hi
      have hiCast : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
        rw [Nat.cast_sub hi'.1] <;> norm_num
      let a : ℝ := X n (i - 1)
      let b : ℝ := X n i
      have ha : 0 ≤ a := by
        dsimp [a, X]
        exact Real.sqrt_nonneg _
      have hb : 0 ≤ b := by
        dsimp [b, X]
        exact Real.sqrt_nonneg _
      have ha2 : a ^ 2 = 1 + ((i - 1 : ℕ) : ℝ) / n := by
        dsimp [a, X]
        rw [Real.sq_sqrt] <;> positivity
      have hb2 : b ^ 2 = 1 + (i : ℝ) / n := by
        dsimp [b, X]
        rw [Real.sq_sqrt] <;> positivity
      have hstep : b ^ 2 - a ^ 2 = 1 / (n : ℝ) := by
        rw [hb2, ha2, hiCast]
        field_simp [hnR] <;> ring
      have hAi : A n i = (2 / 3 : ℝ) * b ^ 3 := by
        dsimp [A]
        change (2 / 3 : ℝ) * ((1 + (i : ℝ) / n) * b) = _
        rw [← hb2] <;> ring
      have hAim1 : A n (i - 1) = (2 / 3 : ℝ) * a ^ 3 := by
        dsimp [A]
        change (2 / 3 : ℝ) *
          ((1 + ((i - 1 : ℕ) : ℝ) / n) * a) = _
        rw [← ha2] <;> ring
      have hfac1 :
          (1 / (n : ℝ)) * b -
              ((2 / 3 : ℝ) * b ^ 3 - (2 / 3 : ℝ) * a ^ 3) =
            (1 / 3 : ℝ) * (b - a) ^ 2 * (b + 2 * a) := by
        rw [← hstep] <;> ring
      have hfac2 :
          (1 / (n : ℝ)) * (b - a) -
              ((1 / (n : ℝ)) * b -
                ((2 / 3 : ℝ) * b ^ 3 - (2 / 3 : ℝ) * a ^ 3)) =
            (1 / 3 : ℝ) * (b - a) ^ 2 * (2 * b + a) := by
        rw [← hstep] <;> ring
      constructor
      · change 0 ≤ (1 / (n : ℝ)) * b - (A n i - A n (i - 1))
        rw [hAi, hAim1, hfac1]
        positivity
      · change (1 / (n : ℝ)) * b - (A n i - A n (i - 1)) ≤
          (1 / (n : ℝ)) * (b - a)
        rw [hAi, hAim1]
        have hnonneg :
            0 ≤ (1 / 3 : ℝ) * (b - a) ^ 2 * (2 * b + a) := by
          positivity
        nlinarith [hfac2]
    have hnonneg :
        0 ≤ Finset.sum (Finset.Icc 1 n)
          (fun i => (1 / (n : ℝ)) * X n i -
            (A n i - A n (i - 1))) := by
      exact Finset.sum_nonneg fun i hi => (hlocal i hi).1
    have hupper :
        Finset.sum (Finset.Icc 1 n)
            (fun i => (1 / (n : ℝ)) * X n i -
              (A n i - A n (i - 1))) ≤
          Finset.sum (Finset.Icc 1 n)
            (fun i => (1 / (n : ℝ)) * (X n i - X n (i - 1))) := by
      exact Finset.sum_le_sum fun i hi => (hlocal i hi).2
    have hAend : A n n - A n 0 =
        (2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1) := by
      dsimp [A, X]
      simp [hnR] <;> ring
    have hXend : X n n - X n 0 = Real.sqrt 2 - 1 := by
      dsimp [X]
      simp [hnR] <;> norm_num
    have htelA' :
        Finset.sum (Finset.Icc 1 n)
            (fun i => A n i - A n (i - 1)) =
          (2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1) :=
      (htel_Icc (A n) n).trans hAend
    have htelX' :
        Finset.sum (Finset.Icc 1 n)
            (fun i => X n i - X n (i - 1)) =
          Real.sqrt 2 - 1 :=
      (htel_Icc (X n) n).trans hXend
    have hscaledX :
        Finset.sum (Finset.Icc 1 n)
            (fun i => (1 / (n : ℝ)) * (X n i - X n (i - 1))) =
          (1 / (n : ℝ)) * (Real.sqrt 2 - 1) := by
      simpa only [Finset.mul_sum] using
        (congrArg (fun z : ℝ => (1 / (n : ℝ)) * z) htelX')
    have hsum : riemannSum n =
        Finset.sum (Finset.Icc 1 n)
          (fun i => (1 / (n : ℝ)) * X n i) := by
      rfl
    rw [Finset.sum_sub_distrib, htelA'] at hnonneg
    rw [Finset.sum_sub_distrib, htelA', hscaledX] at hupper
    constructor
    · rw [hsum]
      linarith
    · rw [hsum]
      linarith
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto
      (fun _ : ℕ => (2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1)) atTop
      (nhds ((2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1))) :=
    tendsto_const_nhds
  have herr : Tendsto
      (fun n : ℕ => ((n : ℝ)⁻¹) * (Real.sqrt 2 - 1)) atTop
      (nhds 0) := by
    simpa using
      (hinv.mul (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => Real.sqrt 2 - 1) atTop
        (nhds (Real.sqrt 2 - 1))))
  have hupp : Tendsto
      (fun n : ℕ => (2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1) +
        (1 / (n : ℝ)) * (Real.sqrt 2 - 1)) atTop
      (nhds ((2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1))) := by
    simpa [div_eq_mul_inv] using hconst.add herr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hconst hupp (hbds.mono fun _ h => h.1) (hbds.mono fun _ h => h.2)

theorem gap2 :
    (∫ x in (0 : ℝ)..1, Real.sqrt (1 + x)) =
      (2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1) := by
  exact sqrt_integral_value

theorem gap3 :
    Tendsto riemannSum atTop
      (𝓝 ((2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1))) := by
  simpa only [gap2] using gap1

end

end ProofGap.Exercise2224
