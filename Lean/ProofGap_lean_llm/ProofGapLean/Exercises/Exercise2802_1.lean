import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2802_1

noncomputable section

open scoped Topology

def f (α : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.rpow ((n : ℝ) + 1) α * x *
    Real.exp (-(((n : ℝ) + 1) * x))

def PointwiseConvergent (α : ℝ) : Prop :=
  ∀ x ∈ Set.Icc (0 : ℝ) 1,
    Tendsto (fun n : ℕ => f α n x) atTop (𝓝 0)

theorem gap1 (α : ℝ) (n : ℕ) :
    f α n 0 = 0 := by
  simp [f]

theorem gap2 (α x : ℝ) (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => f α n x) atTop (𝓝 0) := by
  have hdecay :
      Tendsto
        (fun t : ℝ => Real.rpow t α * Real.exp (-(x * t)))
        atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, ← Real.exp_neg] using
      (isLittleO_rpow_exp_pos_mul_atTop α hx.1).tendsto_div_nhds_zero
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    refine Filter.tendsto_atTop.2 (fun b => ?_)
    refine Filter.eventually_atTop.2 ?_
    refine ⟨Nat.ceil b, fun n hn => ?_⟩
    have hcast : (Nat.ceil b : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
    exact (Nat.le_ceil b).trans
      (hcast.trans (le_add_of_nonneg_right zero_le_one))
  have hseq := hdecay.comp hn
  have hconst : Tendsto (fun _ : ℕ => x) atTop (𝓝 x) :=
    tendsto_const_nhds
  simpa [f, mul_assoc, mul_comm, mul_left_comm] using hseq.mul hconst

theorem gap3 :
    ∀ α : ℝ, PointwiseConvergent α := by
  intro α x hx
  by_cases hzero : x = 0
  · subst x
    simpa only [gap1] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · exact gap2 α x ⟨lt_of_le_of_ne hx.1 (Ne.symm hzero), hx.2⟩

theorem gap4 :
    {α : ℝ | PointwiseConvergent α} = Set.univ := by
  ext α
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact gap3 α

end

end ProofGap.Exercise2802_1
