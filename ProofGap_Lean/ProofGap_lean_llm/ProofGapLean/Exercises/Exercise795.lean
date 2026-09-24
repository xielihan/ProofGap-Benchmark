import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise795

noncomputable section

def f (x : ℝ) : ℝ := Real.log x
def xseq (n : ℕ) : ℝ := 1 / n
def yseq (n : ℕ) : ℝ := 1 / (2 * n)

theorem gap1 (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε : ε₀ < Real.log 2)
    (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, |xseq n - yseq n| = 1 / (2 * n) := by
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hnNat
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hid :
      (1 : ℝ) / (n : ℝ) - 1 / (2 * (n : ℝ)) =
        1 / (2 * (n : ℝ)) := by
    field_simp [hn0]
    norm_num
  simp only [xseq, yseq]
  rw [hid, abs_of_pos (by positivity)]
theorem gap2 (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε : ε₀ < Real.log 2)
    (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) / (2 * n) < δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (2 * δ))
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hnlarge : (1 : ℝ) / (2 * δ) < (n : ℝ) :=
    lt_of_lt_of_le hN hcast
  have h2δ : (0 : ℝ) < 2 * δ := by positivity
  have hthreshold : (0 : ℝ) < 1 / (2 * δ) := by positivity
  have hNR : (0 : ℝ) < (N : ℝ) := lt_trans hthreshold hN
  have hnR : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hNR hcast
  have hprod : (1 : ℝ) < (2 * δ) * (n : ℝ) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((div_lt_iff₀ h2δ).1 hnlarge)
  have h2n : (0 : ℝ) < 2 * (n : ℝ) := by positivity
  apply (div_lt_iff₀ h2n).2
  calc
    (1 : ℝ) < (2 * δ) * (n : ℝ) := hprod
    _ = δ * (2 * (n : ℝ)) := by ring
theorem gap3 (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε : ε₀ < Real.log 2)
    (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, |xseq n - yseq n| < δ := by
  filter_upwards [gap1 ε₀ δ hε₀ hε hδ, gap2 ε₀ δ hε₀ hε hδ] with n hxy hnδ
  rw [hxy]
  exact hnδ
theorem gap4 (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε : ε₀ < Real.log 2)
    (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      |f (xseq n) - f (yseq n)| = Real.log 2 := by
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hnNat
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hx : xseq n ≠ 0 := by
    simp [xseq, hn0]
  have hy : yseq n ≠ 0 := by
    simp [yseq, hn0]
  have hratio : xseq n / yseq n = (2 : ℝ) := by
    simp only [xseq, yseq]
    field_simp [hn0]
  change |Real.log (xseq n) - Real.log (yseq n)| = Real.log 2
  rw [← Real.log_div hx hy, hratio]
  exact abs_of_pos (Real.log_pos (by norm_num))
theorem gap5 (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε : ε₀ < Real.log 2)
    (hδ : 0 < δ) :
    ∀ᶠ _n : ℕ in Filter.atTop, ε₀ < Real.log 2 := by
  exact Filter.Eventually.of_forall (fun _n => hε)
theorem gap6 (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε : ε₀ < Real.log 2)
    (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, ε₀ < |f (xseq n) - f (yseq n)| := by
  filter_upwards [gap4 ε₀ δ hε₀ hε hδ, gap5 ε₀ δ hε₀ hε hδ] with n hlog hbound
  rw [hlog]
  exact hbound
theorem gap7 : ¬ UniformContinuousOn f (Set.Ioo 0 1) := by
  intro huc
  rw [Metric.uniformContinuousOn_iff] at huc
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  let ε₀ : ℝ := Real.log 2 / 2
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    positivity
  have hε : ε₀ < Real.log 2 := by
    dsimp [ε₀]
    linarith
  rcases huc ε₀ hε₀ with ⟨δ, hδ, hmod⟩
  have hevfalse : ∀ᶠ n : ℕ in Filter.atTop, False := by
    filter_upwards [gap3 ε₀ δ hε₀ hε hδ,
      gap6 ε₀ δ hε₀ hε hδ,
      Filter.eventually_ge_atTop 2] with n hxy hfxy hn
    have hnR2 : (2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hnR : (0 : ℝ) < (n : ℝ) := by linarith
    have hnR1 : (1 : ℝ) < (n : ℝ) := by linarith
    have hx0 : 0 < xseq n := by
      simp only [xseq]
      positivity
    have hx1 : xseq n < 1 := by
      simp only [xseq]
      apply (div_lt_iff₀ hnR).2
      simpa using hnR1
    have hdenR : (0 : ℝ) < 2 * (n : ℝ) := by positivity
    have hy0 : 0 < yseq n := by
      simp only [yseq]
      positivity
    have hy1 : yseq n < 1 := by
      simp only [yseq]
      apply (div_lt_iff₀ hdenR).2
      nlinarith
    have hxmem : xseq n ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
    have hymem : yseq n ∈ Set.Ioo (0 : ℝ) 1 := ⟨hy0, hy1⟩
    have hin : dist (xseq n) (yseq n) < δ := by
      simpa only [Real.dist_eq] using hxy
    have hout : dist (f (xseq n)) (f (yseq n)) < ε₀ := by
      apply hmod
      · exact hxmem
      · exact hymem
      · exact hin
    have houtAbs : |f (xseq n) - f (yseq n)| < ε₀ := by
      simpa only [Real.dist_eq] using hout
    exact lt_asymm hfxy houtAbs
  rcases hevfalse.exists with ⟨n, hn⟩
  exact hn
theorem gap8 : ¬ UniformContinuousOn (fun x : ℝ => Real.log x) (Set.Ioo 0 1) := by
  simpa only [f] using gap7

end

end ProofGap.Exercise795
