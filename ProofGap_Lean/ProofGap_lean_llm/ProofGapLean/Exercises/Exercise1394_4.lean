import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ProofGap.Exercise1394_4

noncomputable section

def f (x : ℝ) : ℝ := Real.sqrt (1 + x)
def iterDeriv (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) g

def taylorPolynomial (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m,
    iterDeriv k f 0 / (Nat.factorial k : ℝ) * x ^ k

def remainder (m : ℕ) (x : ℝ) : ℝ := f x - taylorPolynomial m x

def RemainderFormula (n : ℕ) (x : ℝ) : Prop :=
  ∃ θ ∈ Set.Ioo (0 : ℝ) 1,
    remainder (n + 1) x =
      iterDeriv (n + 1) f (θ * x) / (Nat.factorial (n + 1) : ℝ) *
        x ^ (n + 1)

private theorem iterDeriv_three_f (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    iterDeriv 3 f x =
      (3 / 8 : ℝ) * (1 / Real.rpow (1 + x) (5 / 2 : ℝ)) := by
  rw [iterDeriv, ← iteratedDeriv_eq_iterate]
  unfold f
  simp_rw [Real.sqrt_eq_rpow]
  rw [congrFun
    (iteratedDeriv_comp_const_add 3
      (fun z : ℝ => z ^ (1 / 2 : ℝ)) 1) x]
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
  norm_num [descPochhammer_succ_eval]
  rw [Real.rpow_neg]
  linarith [hx.1]

theorem gap1 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ n : ℕ, RemainderFormula n x := by
  intro n
  by_cases hx0 : x = 0
  · subst x
    have hpoly : taylorPolynomial (n + 1) 0 = 1 := by
      rw [taylorPolynomial]
      rw [Finset.sum_eq_single 0]
      · simp [iterDeriv, f]
      · intro k hk hk0
        simp [hk0]
      · simp
    refine ⟨1 / 2, by norm_num, ?_⟩
    rw [remainder, hpoly]
    simp [f]
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hf : ContDiffOn ℝ (n + 1) f (Set.Icc 0 x) := by
      intro y hy
      exact ((contDiffAt_const.add contDiffAt_id).sqrt
        (by simpa only [id_eq] using
          (ne_of_gt (by linarith [hy.1] : (0 : ℝ) < 1 + y)))).contDiffWithinAt
    rcases taylor_mean_remainder_lagrange_iteratedDeriv hxpos hf with
      ⟨c, hc, hrem⟩
    have heval :
        taylorWithinEval f n (Set.Icc 0 x) 0 x =
          taylorPolynomial (n + 1) x := by
      rw [taylor_within_apply]
      dsimp [taylorPolynomial]
      apply Finset.sum_congr rfl
      intro k hk
      rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc hxpos)
        (show ContDiffAt ℝ k f 0 by
          exact (contDiffAt_const.add contDiffAt_id).sqrt
            (by norm_num [id_eq]))
        ⟨le_rfl, hxpos.le⟩]
      rw [iteratedDeriv_eq_iterate]
      simp only [iterDeriv]
      ring
    refine ⟨c / x, ⟨div_pos hc.1 hxpos,
      (div_lt_one hxpos).2 hc.2⟩, ?_⟩
    rw [heval] at hrem
    rw [remainder]
    rw [show c / x * x = c by field_simp]
    rw [iterDeriv, ← iteratedDeriv_eq_iterate]
    rw [hrem]
    ring

theorem gap2 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hsmooth : ContDiffAt ℝ 3 f x) :
    |iterDeriv 3 f x| =
      (3 / 8 : ℝ) * |1 / Real.rpow (1 + x) (5 / 2 : ℝ)| := by
  rw [iterDeriv_three_f x hx, abs_mul]
  norm_num

theorem gap3 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (3 / 8 : ℝ) * |1 / Real.rpow (1 + x) (5 / 2 : ℝ)| ≤
      (3 / 8 : ℝ) := by
  have hpow : 1 ≤ Real.rpow (1 + x) (5 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith [hx.1]) (by norm_num)
  have hpowpos : 0 < Real.rpow (1 + x) (5 / 2 : ℝ) :=
    lt_of_lt_of_le zero_lt_one hpow
  rw [abs_of_pos (one_div_pos.mpr hpowpos)]
  have hinv : 1 / Real.rpow (1 + x) (5 / 2 : ℝ) ≤ 1 :=
    (div_le_one hpowpos).2 hpow
  nlinarith

theorem gap4 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |iterDeriv 3 f x| ≤ (3 / 8 : ℝ) := by
  have hsmooth : ContDiffAt ℝ 3 f x := by
    exact (contDiffAt_const.add contDiffAt_id).sqrt
      (by
        simpa only [id_eq] using
          (ne_of_gt (by linarith [hx.1] : (0 : ℝ) < 1 + x)))
  rw [gap2 x hx hsmooth]
  exact gap3 x hx

theorem gap5 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hR : RemainderFormula 2 x) :
    |remainder 3 x| ≤ (3 / 8 : ℝ) * (1 / (Nat.factorial 3 : ℝ)) := by
  rcases hR with ⟨θ, hθ, hrem⟩
  have hθx : θ * x ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg hθ.1.le hx.1
    · calc
        θ * x ≤ 1 * x := mul_le_mul_of_nonneg_right hθ.2.le hx.1
        _ ≤ 1 := by simpa using hx.2
  have hderiv : |iterDeriv 3 f (θ * x)| ≤ (3 / 8 : ℝ) :=
    gap4 (θ * x) hθx
  have hxabs : |x| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hxpow : |x| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg x) hxabs
  have hfact : (0 : ℝ) < Nat.factorial 3 := by positivity
  rw [show 2 + 1 = 3 by norm_num] at hrem
  rw [hrem, abs_mul, abs_div, abs_pow, abs_of_pos hfact]
  calc
    |iterDeriv 3 f (θ * x)| / (Nat.factorial 3 : ℝ) * |x| ^ 3
        ≤ ((3 / 8 : ℝ) / (Nat.factorial 3 : ℝ)) * 1 := by
          gcongr
    _ = (3 / 8 : ℝ) * (1 / (Nat.factorial 3 : ℝ)) := by ring

theorem gap6 :
    (3 / 8 : ℝ) * (1 / (Nat.factorial 3 : ℝ)) = (1 / 16 : ℝ) := by
  norm_num [Nat.factorial]

theorem gap7 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hR : RemainderFormula 2 x) :
    |remainder 3 x| ≤ (1 / 16 : ℝ) := by
  rw [← gap6]
  exact gap5 x hx hR

end

end ProofGap.Exercise1394_4
