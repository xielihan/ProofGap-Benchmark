import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise800

noncomputable section

def f (x : ℝ) : ℝ := x * Real.sin x
def u (n : ℕ) : ℝ := 2 * (n + 1 : ℝ) * Real.pi + 1 / (n + 1 : ℝ)
def v (n : ℕ) : ℝ := 2 * (n + 1 : ℝ) * Real.pi

private theorem reciprocal_succ_tendsto : Filter.Tendsto
    (fun n : ℕ => 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun n => by
      have hpos : 0 < 1 / (n + 1 : ℝ) := by positivity
      linarith)
  · intro b hb
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (1 / b)
    filter_upwards [Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
    have hN' : 1 < (N : ℝ) * b := (div_lt_iff₀ hb).mp hN
    have hNn : (N : ℝ) ≤ (n : ℝ) := (Nat.cast_le).2 hn
    rw [div_lt_iff₀ (by positivity : 0 < (n + 1 : ℝ))]
    nlinarith

theorem gap1 (n : ℕ) : |u n - v n| = 1 / (n + 1 : ℝ) := by
  unfold u v
  rw [show
    2 * (n + 1 : ℝ) * Real.pi + 1 / (n + 1 : ℝ) -
        2 * (n + 1 : ℝ) * Real.pi =
      1 / (n + 1 : ℝ) by ring]
  exact abs_of_nonneg (by positivity)
theorem gap2 (n : ℕ) : |f (u n) - f (v n)| =
    (2 * (n + 1 : ℝ) * Real.pi + 1 / (n + 1 : ℝ)) *
      Real.sin (1 / (n + 1 : ℝ)) := by
  have hsin_u : Real.sin (u n) = Real.sin (1 / (n + 1 : ℝ)) := by
    rw [show u n =
      1 / (n + 1 : ℝ) +
        ((((n + 1 : ℕ) : ℤ) : ℝ)) * (2 * Real.pi) by
      norm_num [u] <;> ring]
    simpa using
      (Real.sin_add_int_mul_two_pi (1 / (n + 1 : ℝ)) ((n + 1 : ℕ) : ℤ))
  have hsin_v : Real.sin (v n) = 0 := by
    rw [show v n =
      0 + ((((n + 1 : ℕ) : ℤ) : ℝ)) * (2 * Real.pi) by
      norm_num [v] <;> ring]
    simpa using (Real.sin_add_int_mul_two_pi 0 ((n + 1 : ℕ) : ℤ))
  have hden : 0 < (n + 1 : ℝ) := by positivity
  have hq0 : 0 ≤ 1 / (n + 1 : ℝ) := by positivity
  have hq_le_one : 1 / (n + 1 : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hden).2
    norm_num <;> positivity
  have hqpi : 1 / (n + 1 : ℝ) ≤ Real.pi := by
    calc
      1 / (n + 1 : ℝ) ≤ 1 := hq_le_one
      _ ≤ Real.pi := by linarith [Real.two_le_pi]
  have hsin_nonneg : 0 ≤ Real.sin (1 / (n + 1 : ℝ)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hq0 hqpi
  have hu_nonneg : 0 ≤ u n := by
    unfold u
    positivity
  have hdiff :
      f (u n) - f (v n) =
        u n * Real.sin (1 / (n + 1 : ℝ)) := by
    simp [f, hsin_u, hsin_v]
  rw [hdiff, abs_of_nonneg (mul_nonneg hu_nonneg hsin_nonneg)]
  rfl
theorem gap3 (n : ℕ) :
    (2 * (n + 1 : ℝ) * Real.pi + 1 / (n + 1 : ℝ)) *
      Real.sin (1 / (n + 1 : ℝ)) =
    2 * (n + 1 : ℝ) * Real.pi * Real.sin (1 / (n + 1 : ℝ)) +
      1 / (n + 1 : ℝ) * Real.sin (1 / (n + 1 : ℝ)) := by
  ring
theorem gap4 (n : ℕ) : |f (u n) - f (v n)| =
    2 * (n + 1 : ℝ) * Real.pi * Real.sin (1 / (n + 1 : ℝ)) +
      1 / (n + 1 : ℝ) * Real.sin (1 / (n + 1 : ℝ)) := by
  rw [gap2, gap3]
theorem gap5 : Filter.Tendsto
    (fun n : ℕ => 1 / (n + 1 : ℝ) * Real.sin (1 / (n + 1 : ℝ)))
    Filter.atTop (nhds 0) := by
  have hsin : Filter.Tendsto
      (fun n : ℕ => Real.sin (1 / (n + 1 : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using
      (Real.continuous_sin.continuousAt.tendsto.comp reciprocal_succ_tendsto)
  simpa using reciprocal_succ_tendsto.mul hsin
theorem gap6 : (fun n : ℕ => 2 * (n + 1 : ℝ) * Real.pi *
    Real.sin (1 / (n + 1 : ℝ))) =
    (fun n : ℕ => 2 * Real.pi *
      (Real.sin (1 / (n + 1 : ℝ)) / (1 / (n + 1 : ℝ)))) := by
  funext n
  simp only [div_eq_mul_inv, one_mul, inv_inv]
  ring
theorem gap7 : Filter.Tendsto
    (fun n : ℕ => 2 * Real.pi *
      (Real.sin (1 / (n + 1 : ℝ)) / (1 / (n + 1 : ℝ))))
    Filter.atTop (nhds (2 * Real.pi)) := by
  have hpunctured : Filter.Tendsto
      (fun n : ℕ => 1 / (n + 1 : ℝ)) Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨reciprocal_succ_tendsto, Filter.Eventually.of_forall ?_⟩
    intro n
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (by positivity)
  have hsin_ratio : Filter.Tendsto
      (fun x : ℝ => Real.sin x / x)
      (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_sin 0).tendsto_slope_zero
  have hratio : Filter.Tendsto
      (fun n : ℕ => Real.sin (1 / (n + 1 : ℝ)) /
        (1 / (n + 1 : ℝ)))
      Filter.atTop (nhds 1) :=
    hsin_ratio.comp hpunctured
  have hconst : Filter.Tendsto (fun _ : ℕ => 2 * Real.pi)
      Filter.atTop (nhds (2 * Real.pi)) := tendsto_const_nhds
  simpa using hconst.mul hratio
theorem gap8 : Filter.Tendsto
    (fun n : ℕ => 2 * (n + 1 : ℝ) * Real.pi * Real.sin (1 / (n + 1 : ℝ)))
    Filter.atTop (nhds (2 * Real.pi)) := by
  rw [gap6]
  exact gap7
theorem gap9 : Filter.Tendsto (fun n : ℕ => |f (u n) - f (v n)|)
    Filter.atTop (nhds (2 * Real.pi)) := by
  simpa only [gap4, add_zero] using gap8.add gap5
theorem gap10 (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in Filter.atTop, |u n - v n| < δ := by
  have hevent :=
    (tendsto_order.1 reciprocal_succ_tendsto).2 δ hδ
  filter_upwards [hevent] with n hn
  simpa only [gap1] using hn
theorem gap11 : ∀ᶠ n in Filter.atTop,
    2 * Real.pi - 1 < |f (u n) - f (v n)| := by
  apply (tendsto_order.1 gap9).1
  linarith
theorem gap12 : (2 * Real.pi - 1 : ℝ) = 2 * Real.pi - 1 := by
  rfl
theorem gap13 : ∀ᶠ n in Filter.atTop,
    2 * Real.pi - 1 < |f (u n) - f (v n)| := by
  exact gap11
theorem gap14 : ¬ UniformContinuousOn f (Set.Ici 0) := by
  intro h
  rw [Metric.uniformContinuousOn_iff] at h
  have heps : 0 < 2 * Real.pi - 1 := by
    linarith [Real.two_le_pi]
  rcases h (2 * Real.pi - 1) heps with ⟨δ, hδ, hcontrol⟩
  rcases Filter.Eventually.exists ((gap10 δ hδ).and gap13) with
    ⟨n, hnclose, hnfar⟩
  have hu : u n ∈ Set.Ici 0 := by
    simp only [Set.mem_Ici]
    unfold u
    positivity
  have hv : v n ∈ Set.Ici 0 := by
    simp only [Set.mem_Ici]
    unfold v
    positivity
  have hdist : dist (u n) (v n) < δ := by
    simpa only [Real.dist_eq] using hnclose
  have hsmall := hcontrol (u n) hu (v n) hv hdist
  have himage : |f (u n) - f (v n)| < 2 * Real.pi - 1 := by
    simpa only [Real.dist_eq] using hsmall
  linarith
theorem gap15 : ¬ UniformContinuousOn f (Set.Ici 0) := by
  exact gap14

end
end ProofGap.Exercise800
