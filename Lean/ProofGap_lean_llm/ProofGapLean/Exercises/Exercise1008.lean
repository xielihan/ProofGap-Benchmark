import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1008

open Filter

noncomputable section

def f (x : ℝ) : ℝ :=
  if x = 2 then 0 else (x - 2) * Real.arctan (1 / (x - 2))

def dq (g : ℝ → ℝ) (a h : ℝ) : ℝ := (g (a + h) - g a) / h
def HasLeftDerivAt (g : ℝ → ℝ) (g' a : ℝ) : Prop :=
  Tendsto (dq g a) (nhdsWithin 0 (Set.Iio 0)) (nhds g')
def HasRightDerivAt (g : ℝ → ℝ) (g' a : ℝ) : Prop :=
  Tendsto (dq g a) (nhdsWithin 0 (Set.Ioi 0)) (nhds g')

def rawDerivative (x : ℝ) : ℝ :=
  Real.arctan (1 / (x - 2)) +
    (x - 2) / (1 + (1 / (x - 2)) ^ 2) * (-1 / (x - 2) ^ 2)

def finalDerivative (x : ℝ) : ℝ :=
  Real.arctan (1 / (x - 2)) - (x - 2) / ((x - 2) ^ 2 + 1)

def cuspModel (h : ℝ) : ℝ := Real.arctan (1 / h)

private theorem derivative_data (x : ℝ) (hx : x ≠ 2) :
    rawDerivative x = finalDerivative x ∧
      (HasLeftDerivAt f (finalDerivative x) x ∧
        HasRightDerivAt f (finalDerivative x) x) := by
  have hxsub : x - 2 ≠ 0 := sub_ne_zero.mpr hx
  have hrawden : 1 + (1 / (x - 2)) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (1 / (x - 2))]
  have hfinalden : (x - 2) ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg (x - 2)]
  have hraw : rawDerivative x = finalDerivative x := by
    unfold rawDerivative finalDerivative
    field_simp [hxsub, hrawden, hfinalden] <;> ring
  have hu :
      HasDerivAt (fun y : ℝ => 1 / (y - 2))
        (-1 / (x - 2) ^ 2) x := by
    convert
      (hasDerivAt_const x (1 : ℝ)).div
        ((hasDerivAt_id x).sub_const 2) hxsub using 1 <;>
      simp [id] <;> ring
  have ha :
      HasDerivAt (fun y : ℝ => Real.arctan (1 / (y - 2)))
        (1 / (1 + (1 / (x - 2)) ^ 2) * (-1 / (x - 2) ^ 2)) x := by
    convert (Real.hasDerivAt_arctan (1 / (x - 2))).comp x hu using 1 <;> ring
  have hg :
      HasDerivAt
        (fun y : ℝ => (y - 2) * Real.arctan (1 / (y - 2)))
        (rawDerivative x) x := by
    simpa [rawDerivative, div_eq_mul_inv, mul_assoc] using
      (((hasDerivAt_id x).sub_const 2).mul ha)
  have heq :
      f =ᶠ[nhds x]
        (fun y : ℝ => (y - 2) * Real.arctan (1 / (y - 2))) := by
    have hmem : x ∈ ({2}ᶜ : Set ℝ) := by
      simpa using hx
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hmem] with y hy
    have hy' : y ≠ 2 := by
      simpa using hy
    simp [f, hy']
  have hfderiv : HasDerivAt f (finalDerivative x) x := by
    rw [← hraw]
    exact hg.congr_of_eventuallyEq heq
  have hdq :
      dq f x = (fun t : ℝ => t⁻¹ * (f (x + t) - f x)) := by
    funext t
    unfold dq
    rw [div_eq_mul_inv, mul_comm]
  have hslope :
      Tendsto (dq f x) (nhdsWithin 0 ({0}ᶜ : Set ℝ))
        (nhds (finalDerivative x)) := by
    rw [hdq]
    exact hfderiv.tendsto_slope_zero
  have hleft_le :
      nhdsWithin 0 (Set.Iio 0) ≤ nhdsWithin 0 ({0}ᶜ : Set ℝ) := by
    apply nhdsWithin_mono
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_lt hy
  have hright_le :
      nhdsWithin 0 (Set.Ioi 0) ≤ nhdsWithin 0 ({0}ᶜ : Set ℝ) := by
    apply nhdsWithin_mono
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt hy
  exact ⟨hraw, hslope.mono_left hleft_le, hslope.mono_left hright_le⟩

theorem gap1 (x : ℝ) (hx : x ≠ 2) :
    HasLeftDerivAt f (finalDerivative x) x ∧
      HasRightDerivAt f (finalDerivative x) x := by
  exact (derivative_data x hx).2

theorem gap2 (x : ℝ) (hx : x ≠ 2) :
    HasRightDerivAt f (rawDerivative x) x := by
  have hd := derivative_data x hx
  simpa only [hd.1] using hd.2.2

theorem gap3 (x : ℝ) (hx : x ≠ 2) :
    rawDerivative x = finalDerivative x := by
  exact (derivative_data x hx).1

theorem gap4 (x : ℝ) (hx : x ≠ 2) :
    HasLeftDerivAt f (finalDerivative x) x := by
  exact (derivative_data x hx).2.1

theorem gap5 (L : ℝ) :
    Tendsto (dq f 2) (nhdsWithin 0 (Set.Iio 0)) (nhds L) ↔
      Tendsto cuspModel (nhdsWithin 0 (Set.Iio 0)) (nhds L) := by
  have heq :
      dq f 2 =ᶠ[nhdsWithin 0 (Set.Iio 0)] cuspModel := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : h ≠ 0 := ne_of_lt hh
    have hsum : 2 + h ≠ 2 := by
      intro hsum
      apply hh0
      calc
        h = (2 + h) - 2 := by ring
        _ = 0 := by rw [hsum]; ring
    simp [dq, f, cuspModel, hsum, hh0]
  exact tendsto_congr' heq

theorem gap6 :
    Tendsto cuspModel (nhdsWithin 0 (Set.Iio 0))
      (nhds (-Real.pi / 2)) := by
  have heq :
      cuspModel =ᶠ[nhdsWithin 0 (Set.Iio 0)]
        (fun h : ℝ => -(Real.pi / 2) - Real.arctan h) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    simpa [cuspModel, one_div] using Real.arctan_inv_of_neg hh
  refine (tendsto_congr' heq).2 ?_
  have hc :
      ContinuousAt (fun h : ℝ => -(Real.pi / 2) - Real.arctan h) 0 :=
    continuousAt_const.sub (Real.hasDerivAt_arctan 0).continuousAt
  convert (hc.tendsto.mono_left inf_le_left) using 1 <;> simp <;> ring

theorem gap7 :
    HasLeftDerivAt f (-Real.pi / 2) 2 := by
  unfold HasLeftDerivAt
  exact (gap5 (-Real.pi / 2)).2 gap6

theorem gap8 :
    HasRightDerivAt f (Real.pi / 2) 2 := by
  unfold HasRightDerivAt
  have hdq :
      dq f 2 =ᶠ[nhdsWithin 0 (Set.Ioi 0)] cuspModel := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : h ≠ 0 := ne_of_gt hh
    have hsum : 2 + h ≠ 2 := by
      intro hsum
      apply hh0
      calc
        h = (2 + h) - 2 := by ring
        _ = 0 := by rw [hsum]; ring
    simp [dq, f, cuspModel, hsum, hh0]
  refine (tendsto_congr' hdq).2 ?_
  have harctan :
      cuspModel =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun h : ℝ => Real.pi / 2 - Real.arctan h) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    simpa [cuspModel, one_div] using Real.arctan_inv_of_pos hh
  refine (tendsto_congr' harctan).2 ?_
  have hc :
      ContinuousAt (fun h : ℝ => Real.pi / 2 - Real.arctan h) 0 :=
    continuousAt_const.sub (Real.hasDerivAt_arctan 0).continuousAt
  simpa using (hc.tendsto.mono_left inf_le_left)

end

end ProofGap.Exercise1008
