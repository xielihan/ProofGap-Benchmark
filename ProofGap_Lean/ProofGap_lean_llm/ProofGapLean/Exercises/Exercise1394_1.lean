import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ProofGap.Exercise1394_1

noncomputable section

def f (x : ℝ) : ℝ := Real.exp x
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

private theorem iterDeriv_f (n : ℕ) :
    iterDeriv n f = Real.exp := by
  exact Real.iter_deriv_exp n

theorem gap1 (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    RemainderFormula n x := by
  by_cases hx0 : x = 0
  · subst x
    have hpoly : taylorPolynomial (n + 1) 0 = 1 := by
      rw [taylorPolynomial]
      rw [Finset.sum_eq_single 0]
      · simp [iterDeriv_f, f]
      · intro k hk hk0
        simp [hk0]
      · simp
    refine ⟨1 / 2, by norm_num, ?_⟩
    rw [remainder, hpoly]
    simp [f]
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hf : ContDiffOn ℝ (n + 1) f (Set.Icc 0 x) := by
      simpa only [f] using
        (Real.contDiff_exp :
          ContDiff ℝ (n + 1) Real.exp).contDiffOn
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
          simpa only [f] using
            (Real.contDiff_exp :
              ContDiff ℝ k Real.exp).contDiffAt)
        ⟨le_rfl, hxpos.le⟩]
      rw [iteratedDeriv_eq_iterate]
      simp only [iterDeriv, smul_eq_mul]
      ring
    refine ⟨c / x, ⟨div_pos hc.1 hxpos,
      (div_lt_one hxpos).2 hc.2⟩, ?_⟩
    rw [heval] at hrem
    rw [remainder]
    rw [show c / x * x = c by field_simp]
    rw [iterDeriv, ← iteratedDeriv_eq_iterate]
    rw [hrem]
    ring

theorem gap2 (n : ℕ) (x : ℝ) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) 1,
      iterDeriv (n + 1) f (θ * x) = Real.exp (θ * x) := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  rw [iterDeriv_f]

theorem gap3 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) 1, Real.exp (θ * x) < Real.exp 1 := by
  refine ⟨1 / 2, by norm_num, Real.exp_lt_exp.mpr ?_⟩
  calc
    (1 / 2 : ℝ) * x ≤ (1 / 2 : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hx.2 (by norm_num)
    _ < 1 := by norm_num

theorem gap4 (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) 1,
      iterDeriv (n + 1) f (θ * x) < Real.exp 1 := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  rw [iterDeriv_f]
  exact Real.exp_lt_exp.mpr (by
    calc
      (1 / 2 : ℝ) * x ≤ (1 / 2 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hx.2 (by norm_num)
      _ < 1 := by norm_num)

theorem gap5 (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hR : RemainderFormula n x) :
    |remainder (n + 1) x| ≤
      Real.exp 1 / (Nat.factorial (n + 1) : ℝ) * |x| ^ (n + 1) := by
  rcases hR with ⟨θ, hθ, hrem⟩
  rw [iterDeriv_f] at hrem
  have hθx : θ * x < 1 := by
    calc
      θ * x ≤ θ * 1 :=
        mul_le_mul_of_nonneg_left hx.2 hθ.1.le
      _ < 1 := by simpa using hθ.2
  have hexp : Real.exp (θ * x) ≤ Real.exp 1 :=
    (Real.exp_lt_exp.mpr hθx).le
  have hfact :
      (0 : ℝ) < Nat.factorial (n + 1) := by positivity
  rw [hrem, abs_mul, abs_div, abs_pow,
    abs_of_pos (Real.exp_pos _), abs_of_pos hfact]
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hexp hfact.le) (by positivity)

theorem gap6 (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp 1 / (Nat.factorial (n + 1) : ℝ) * |x| ^ (n + 1) ≤
      Real.exp 1 / (Nat.factorial (n + 1) : ℝ) := by
  have hxabs : |x| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hp : |x| ^ (n + 1) ≤ 1 := pow_le_one₀ (abs_nonneg x) hxabs
  have hc : 0 ≤ Real.exp 1 / (Nat.factorial (n + 1) : ℝ) := by
    positivity
  nlinarith

theorem gap7 (n : ℕ) :
    Real.exp 1 / (Nat.factorial (n + 1) : ℝ) <
      3 / (Nat.factorial (n + 1) : ℝ) := by
  exact (div_lt_div_iff_of_pos_right
    (by positivity : (0 : ℝ) < Nat.factorial (n + 1))).2
      Real.exp_one_lt_three

theorem gap8 (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hR : RemainderFormula n x) :
    |remainder (n + 1) x| < 3 / (Nat.factorial (n + 1) : ℝ) := by
  exact lt_of_le_of_lt (gap5 n x hx hR)
    (lt_of_le_of_lt (gap6 n x hx) (gap7 n))

end

end ProofGap.Exercise1394_1
