import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise509

noncomputable section

def seq (n : ℕ) : ℝ :=
  Real.sin (2 * Real.pi * n / (3 * n + 1)) ^ n

/-- Source: `proof_gap/exercise_509/1.txt`. -/
private theorem angle_tendsto :
    Filter.Tendsto
      (fun n : ℕ => 2 * Real.pi * n / (3 * n + 1))
      Filter.atTop (nhds (2 * Real.pi / 3)) := by
  have hn :
      Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hinv :
      Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hn
  have hnum :
      Filter.Tendsto (fun _ : ℕ => (2 * Real.pi : ℝ))
        Filter.atTop (nhds (2 * Real.pi)) :=
    tendsto_const_nhds
  have hden :
      Filter.Tendsto (fun n : ℕ => (3 : ℝ) + (n : ℝ)⁻¹)
        Filter.atTop (nhds 3) := by
    simpa using
      ((tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ => (3 : ℝ)) Filter.atTop (nhds 3)).add hinv)
  have hratio :
      Filter.Tendsto
        (fun n : ℕ => (2 * Real.pi) / ((3 : ℝ) + (n : ℝ)⁻¹))
        Filter.atTop (nhds (2 * Real.pi / 3)) :=
    hnum.div hden (by norm_num : (3 : ℝ) ≠ 0)
  have heq :
      (fun n : ℕ => 2 * Real.pi * n / (3 * n + 1)) =ᶠ[Filter.atTop]
        (fun n : ℕ => (2 * Real.pi) / ((3 : ℝ) + (n : ℝ)⁻¹)) := by
    refine Filter.eventually_atTop.2 ⟨1, ?_⟩
    intro n hn_pos
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn_pos
    have hn0r : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden0 : (3 * (n : ℝ) + 1) ≠ 0 := by
      nlinarith
    have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hn_nonneg
    have hsum0 : (3 : ℝ) + (n : ℝ)⁻¹ ≠ 0 := by
      nlinarith
    field_simp [hn0r, hden0, hsum0]
    <;> ring
  exact Filter.Tendsto.congr' heq.symm hratio

theorem gap1 (n : ℕ) :
    |Real.sin (2 * Real.pi * n / (3 * n + 1))| ≤ 1 := by
  exact
    abs_le.2
      ⟨Real.neg_one_le_sin (2 * Real.pi * n / (3 * n + 1)),
        Real.sin_le_one (2 * Real.pi * n / (3 * n + 1))⟩

/-- Source: `proof_gap/exercise_509/2.txt`. -/
theorem gap2 : Filter.Tendsto seq Filter.atTop (nhds 0) := by
  have hsin :
      Filter.Tendsto
        (fun n : ℕ => Real.sin (2 * Real.pi * n / (3 * n + 1)))
        Filter.atTop
        (nhds (Real.sin (2 * Real.pi / 3))) := by
    simpa only [Function.comp_apply] using
      (Filter.Tendsto.comp Real.continuous_sin.continuousAt angle_tendsto)
  have habs_t :
      Filter.Tendsto
        (fun n : ℕ => |Real.sin (2 * Real.pi * n / (3 * n + 1))|)
        Filter.atTop
        (nhds |Real.sin (2 * Real.pi / 3)|) := by
    simpa only [Function.comp_apply] using
      (Filter.Tendsto.comp continuous_abs.continuousAt hsin)
  have hval :
      Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    have heq : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by
      ring
    rw [heq, Real.sin_pi_sub, Real.sin_pi_div_three]
  have hsqrt_lt : Real.sqrt (3 : ℝ) < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_nonneg (3 : ℝ)]
  have hlim_lt : |Real.sin (2 * Real.pi / 3)| < 1 := by
    rw [hval, abs_of_nonneg
      (div_nonneg (Real.sqrt_nonneg (3 : ℝ)) (by norm_num))]
    linarith
  let c : ℝ := (|Real.sin (2 * Real.pi / 3)| + 1) / 2
  have hc0 : 0 ≤ c := by
    dsimp [c]
    nlinarith [abs_nonneg (Real.sin (2 * Real.pi / 3))]
  have hc1 : c < 1 := by
    dsimp [c]
    linarith
  have hlim_c : |Real.sin (2 * Real.pi / 3)| < c := by
    dsimp [c]
    linarith
  have hbound :
      ∀ᶠ n : ℕ in Filter.atTop,
        |Real.sin (2 * Real.pi * n / (3 * n + 1))| ≤ c := by
    have hlt :
        ∀ᶠ n : ℕ in Filter.atTop,
          |Real.sin (2 * Real.pi * n / (3 * n + 1))| < c :=
      habs_t.eventually (Iio_mem_nhds hlim_c)
    exact hlt.mono (fun _ hn => le_of_lt hn)
  have hcpow :
      Filter.Tendsto (fun n : ℕ => c ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1
  apply Metric.tendsto_atTop.2
  intro ε hε
  rcases (Metric.tendsto_atTop.1 hcpow) ε hε with ⟨N₁, hN₁⟩
  rcases Filter.eventually_atTop.1 hbound with ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hb := hN₂ n (le_trans (Nat.le_max_right N₁ N₂) hn)
  have hpowdist := hN₁ n (le_trans (Nat.le_max_left N₁ N₂) hn)
  have hpowlt : c ^ n < ε := by
    have habspow : |c| ^ n < ε := by
      simpa [Real.dist_eq] using hpowdist
    simpa [abs_of_nonneg hc0] using habspow
  have hp :
      ∀ k : ℕ,
        |Real.sin (2 * Real.pi * n / (3 * n + 1))| ^ k ≤ c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        simp only [pow_succ]
        exact mul_le_mul ih hb (abs_nonneg _) (pow_nonneg hc0 k)
  simpa only [seq, Real.dist_eq, sub_zero, abs_pow] using
    lt_of_le_of_lt (hp n) hpowlt

end

end ProofGap.Exercise509
