import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise1394_2

noncomputable section

def f (x : ℝ) : ℝ := Real.sin x
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

private theorem iterDeriv_eq_iterated (n : ℕ) :
    iterDeriv n f = iteratedDeriv n Real.sin := by
  change (deriv^[n]) Real.sin = iteratedDeriv n Real.sin
  rw [iteratedDeriv_eq_iterate]

private theorem remainderFormula_pos (n : ℕ) {x : ℝ} (hx : 0 < x) :
    RemainderFormula n x := by
  have hf : ContDiffOn ℝ (n + 1) f (Set.Icc 0 x) := by
    simpa only [f] using
      (Real.contDiff_sin :
        ContDiff ℝ (n + 1) Real.sin).contDiffOn
  rcases taylor_mean_remainder_lagrange_iteratedDeriv hx hf with
    ⟨c, hc, hrem⟩
  have heval :
      taylorWithinEval f n (Set.Icc 0 x) 0 x =
        taylorPolynomial (n + 1) x := by
    rw [taylor_within_apply]
    dsimp [taylorPolynomial]
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc hx)
      (show ContDiffAt ℝ k f 0 by
        simpa only [f] using
          (Real.contDiff_sin :
            ContDiff ℝ k Real.sin).contDiffAt)
      ⟨le_rfl, hx.le⟩]
    rw [iteratedDeriv_eq_iterate]
    simp only [iterDeriv, smul_eq_mul]
    ring
  refine ⟨c / x, ⟨div_pos hc.1 hx,
    (div_lt_one hx).2 hc.2⟩, ?_⟩
  rw [heval] at hrem
  rw [remainder]
  rw [show c / x * x = c by field_simp]
  rw [iterDeriv, ← iteratedDeriv_eq_iterate]
  rw [hrem]
  ring

theorem gap1 (x : ℝ) (hx : |x| ≤ (1 / 2 : ℝ)) :
    ∀ n : ℕ, RemainderFormula n x := by
  intro n
  by_cases hx0 : x = 0
  · subst x
    have hpoly : taylorPolynomial (n + 1) 0 = 0 := by
      rw [taylorPolynomial]
      rw [Finset.sum_eq_single 0]
      · simp [iterDeriv, f]
      · intro k hk hk0
        simp [hk0]
      · simp
    refine ⟨1 / 2, by norm_num, ?_⟩
    rw [remainder, hpoly]
    simp [f]
  · by_cases hxpos : 0 < x
    · exact remainderFormula_pos n hxpos
    · have hxneg : x < 0 := lt_of_le_of_ne
        (le_of_not_gt hxpos) hx0
      let y : ℝ := -x
      let g : ℝ → ℝ := fun t => f (-t)
      have hy : 0 < y := by
        dsimp [y]
        linarith
      have hgall : ContDiff ℝ (n + 1) g := by
        dsimp [g, f]
        exact (Real.contDiff_sin :
          ContDiff ℝ (n + 1) Real.sin).comp contDiff_neg
      rcases taylor_mean_remainder_lagrange_iteratedDeriv hy
        hgall.contDiffOn with ⟨c, hc, hrem⟩
      have heval :
          taylorWithinEval g n (Set.Icc 0 y) 0 y =
            taylorPolynomial (n + 1) x := by
        rw [taylor_within_apply]
        dsimp [taylorPolynomial]
        apply Finset.sum_congr rfl
        intro k hk
        rw [iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_Icc hy)
          (show ContDiffAt ℝ k g 0 by
            dsimp [g, f]
            exact ((Real.contDiff_sin :
              ContDiff ℝ k Real.sin).comp contDiff_neg).contDiffAt)
          ⟨le_rfl, hy.le⟩]
        dsimp [g, y]
        rw [iteratedDeriv_comp_neg, iteratedDeriv_eq_iterate]
        simp only [iterDeriv, neg_zero, smul_eq_mul]
        rw [sub_zero, neg_pow]
        ring_nf
        rw [Even.neg_one_pow
          (show Even (k * 2) by exact ⟨k, by omega⟩)]
        ring
      rw [heval] at hrem
      rw [iteratedDeriv_comp_neg] at hrem
      dsimp [g, y] at hrem
      simp only [neg_neg, smul_eq_mul] at hrem
      refine ⟨c / y, ⟨div_pos hc.1 hy,
        (div_lt_one hy).2 hc.2⟩, ?_⟩
      rw [remainder]
      rw [show c / y * x = -c by
        dsimp [y]
        field_simp]
      rw [iterDeriv, ← iteratedDeriv_eq_iterate]
      rw [hrem]
      rw [sub_zero, neg_pow]
      ring_nf
      rw [Even.neg_one_pow
        (show Even (n * 2) by exact ⟨n, by omega⟩)]
      ring

theorem gap2 (x : ℝ) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) 1,
      |iterDeriv 5 f (θ * x)| =
        |Real.sin (θ * x + (5 / 2 : ℝ) * Real.pi)| := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  rw [iterDeriv_eq_iterated, show (5 : ℕ) = 2 * 2 + 1 by norm_num,
    Real.iteratedDeriv_odd_sin]
  norm_num
  rw [show (5 / 2 : ℝ) * Real.pi =
    2 * Real.pi + Real.pi / 2 by ring]
  rw [Real.sin_add, Real.sin_add]
  simp [Real.cos_add]

theorem gap3 (x : ℝ) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) 1,
      |Real.sin (θ * x + (5 / 2 : ℝ) * Real.pi)| ≤ 1 := by
  exact ⟨1 / 2, by norm_num, Real.abs_sin_le_one _⟩

theorem gap4 (x : ℝ) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) 1, |iterDeriv 5 f (θ * x)| ≤ 1 := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  rw [iterDeriv_eq_iterated]
  exact Real.abs_iteratedDeriv_sin_le_one 5 _

theorem gap5 (x : ℝ)
    (hx : |x| ≤ (1 / 2 : ℝ)) (hR : RemainderFormula 4 x) :
    |remainder 5 x| ≤ (1 / (Nat.factorial 5 : ℝ)) * |x| ^ 5 := by
  rcases hR with ⟨θ, hθ, hrem⟩
  have hderiv : |iterDeriv 5 f (θ * x)| ≤ 1 := by
    rw [iterDeriv_eq_iterated]
    exact Real.abs_iteratedDeriv_sin_le_one 5 _
  rw [hrem, abs_mul, abs_div, abs_pow]
  have hfact : (0 : ℝ) < Nat.factorial 5 := by positivity
  rw [abs_of_pos hfact]
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hderiv hfact.le) (by positivity)

theorem gap6 (x : ℝ) (hx : |x| ≤ (1 / 2 : ℝ)) :
    (1 / (Nat.factorial 5 : ℝ)) * |x| ^ 5 ≤
      (1 / (Nat.factorial 5 : ℝ)) * (1 / (2 : ℝ) ^ 5) := by
  have hp : |x| ^ 5 ≤ (1 / 2 : ℝ) ^ 5 :=
    pow_le_pow_left₀ (abs_nonneg x) hx 5
  calc
    (1 / (Nat.factorial 5 : ℝ)) * |x| ^ 5 ≤
        (1 / (Nat.factorial 5 : ℝ)) * (1 / 2 : ℝ) ^ 5 :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (1 / (Nat.factorial 5 : ℝ)) * (1 / (2 : ℝ) ^ 5) := by
      norm_num

theorem gap7 :
    (1 / (Nat.factorial 5 : ℝ)) * (1 / (2 : ℝ) ^ 5) =
      (1 / 3840 : ℝ) := by
  norm_num [Nat.factorial]

theorem gap8 (x : ℝ)
    (hx : |x| ≤ (1 / 2 : ℝ)) (hR : RemainderFormula 4 x) :
    |remainder 5 x| ≤ (1 / 3840 : ℝ) := by
  rw [← gap7]
  exact (gap5 x hx hR).trans (gap6 x hx)

end

end ProofGap.Exercise1394_2
