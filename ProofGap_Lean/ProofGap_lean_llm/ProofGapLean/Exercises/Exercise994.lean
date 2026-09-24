import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise994

open Filter

noncomputable section

def f (a : ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (x - a) * φ x

def dq (g : ℝ → ℝ) (a h : ℝ) : ℝ :=
  (g (a + h) - g a) / h

def rawQ (a : ℝ) (φ : ℝ → ℝ) (h : ℝ) : ℝ :=
  (h * φ (a + h) - 0) / h

theorem gap1 (a h : ℝ) (φ : ℝ → ℝ) :
    dq (f a φ) a h = rawQ a φ h := by
  simp [dq, f, rawQ]

theorem gap2 (a : ℝ) (φ : ℝ → ℝ) (L : ℝ) :
    Tendsto (rawQ a φ) (nhdsWithin 0 {0}ᶜ) (nhds L) ↔
      Tendsto (fun h => φ (a + h)) (nhdsWithin 0 {0}ᶜ) (nhds L) := by
  have heq : rawQ a φ =ᶠ[nhdsWithin 0 {0}ᶜ]
      (fun h => φ (a + h)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hne : h ≠ 0 := by
      simpa using hh
    simp [rawQ, hne]
  constructor
  · intro ht
    exact ht.congr' heq
  · intro ht
    exact ht.congr' heq.symm

theorem gap3 (a : ℝ) (φ : ℝ → ℝ) (L : ℝ) :
    Tendsto (dq (f a φ) a) (nhdsWithin 0 {0}ᶜ) (nhds L) ↔
      Tendsto (fun h => φ (a + h)) (nhdsWithin 0 {0}ᶜ) (nhds L) := by
  have hdq : dq (f a φ) a = rawQ a φ := by
    funext h
    exact gap1 a h φ
  rw [hdq]
  exact gap2 a φ L

theorem gap4 (a : ℝ) (φ : ℝ → ℝ) (hφ : ContinuousAt φ a) :
    Tendsto (fun h => φ (a + h)) (nhds 0) (nhds (φ a)) := by
  have hc : Tendsto (fun _ : ℝ => a) (nhds 0) (nhds a) :=
    tendsto_const_nhds
  have hi : Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0) :=
    tendsto_id
  have ha : Tendsto (fun h : ℝ => a + h) (nhds 0) (nhds a) := by
    simpa using hc.add hi
  exact hφ.tendsto.comp ha

theorem gap5 (a : ℝ) (φ : ℝ → ℝ) (hφ : ContinuousAt φ a) :
    Tendsto (dq (f a φ) a) (nhdsWithin 0 {0}ᶜ) (nhds (φ a)) := by
  apply (gap3 a φ (φ a)).2
  exact (gap4 a φ hφ).mono_left inf_le_left

theorem gap6 (a : ℝ) (φ : ℝ → ℝ) (hφ : ContinuousAt φ a) :
    HasDerivAt (f a φ) (φ a) a := by
  apply hasDerivAt_iff_isLittleO_nhds_zero.2
  have hconst : Tendsto (fun _ : ℝ => φ a) (nhds 0) (nhds (φ a)) :=
    tendsto_const_nhds
  have ht : Tendsto (fun h : ℝ => φ (a + h) - φ a)
      (nhds 0) (nhds 0) := by
    simpa using (gap4 a φ hφ).sub hconst
  have hp : (fun h : ℝ => h * (φ (a + h) - φ a)) =o[nhds 0]
      (fun h : ℝ => h) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hev : ∀ᶠ h in nhds 0, ‖φ (a + h) - φ a‖ < c := by
      simpa [Real.dist_eq] using (Metric.tendsto_nhds.1 ht c hc)
    filter_upwards [hev] with h hh
    simpa [norm_mul, mul_comm] using
      mul_le_mul_of_nonneg_left (le_of_lt hh) (norm_nonneg h)
  simpa [f, mul_sub] using hp

end

end ProofGap.Exercise994
