import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2807

noncomputable section

open Filter
open scoped BigOperators Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  x ^ (n + 1) - x ^ (n + 2)

def factoredTerm (n : ℕ) (x : ℝ) : ℝ :=
  x ^ (n + 1) * (1 - x)

def seriesSum (x : ℝ) : ℝ :=
  ∑' n : ℕ, term n x

theorem gap1 :
    ∀ x : ℝ, 0 ≤ x → x < 1 →
      (∑' n : ℕ, term n x) = ∑' n : ℕ, factoredTerm n x := by
  intro x hx hlt
  apply tsum_congr
  intro n
  simp only [term, factoredTerm, pow_succ]
  ring

theorem gap2 :
    ∀ x : ℝ, 0 ≤ x → x < 1 →
      (∑' n : ℕ, factoredTerm n x) = x * (1 - x) / (1 - x) := by
  intro x hx hlt
  have hnorm : ‖x‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hx] using hlt
  have hs :
      HasSum (fun n : ℕ => x ^ n * (x * (1 - x)))
        ((1 - x)⁻¹ * (x * (1 - x))) :=
    (hasSum_geometric_of_norm_lt_one hnorm).mul_right (x * (1 - x))
  simpa [factoredTerm, pow_succ, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using hs.tsum_eq

theorem gap3 :
    ∀ x : ℝ, 0 ≤ x → x < 1 →
      x * (1 - x) / (1 - x) = x := by
  intro x hx hlt
  have hne : 1 - x ≠ 0 := by linarith
  calc
    x * (1 - x) / (1 - x) = x * ((1 - x) / (1 - x)) := by
      rw [mul_div_assoc]
    _ = x := by rw [div_self hne, mul_one]

theorem gap4 :
    ∀ x : ℝ, 0 ≤ x → x < 1 → seriesSum x = x := by
  intro x hx hlt
  unfold seriesSum
  calc
    (∑' n : ℕ, term n x) = ∑' n : ℕ, factoredTerm n x := gap1 x hx hlt
    _ = x * (1 - x) / (1 - x) := gap2 x hx hlt
    _ = x := gap3 x hx hlt

theorem gap5 :
    Tendsto seriesSum (𝓝[<] (1 : ℝ)) (𝓝 1) ↔
      Tendsto (fun x : ℝ => x) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
  have hpos_nhds : ∀ᶠ x : ℝ in 𝓝 (1 : ℝ), 0 < x :=
    Ioi_mem_nhds zero_lt_one
  have hpos : ∀ᶠ x : ℝ in 𝓝[<] (1 : ℝ), 0 < x :=
    Filter.Eventually.filter_mono inf_le_left hpos_nhds
  have heq : seriesSum =ᶠ[𝓝[<] (1 : ℝ)] (fun x : ℝ => x) := by
    filter_upwards [hpos, self_mem_nhdsWithin] with x hx hxlt
    exact gap4 x hx.le hxlt
  exact tendsto_congr' heq

theorem gap6 :
    Tendsto (fun x : ℝ => x) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
  exact (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 (1 : ℝ)) (𝓝 1)).mono_left inf_le_left

theorem gap7 :
    Tendsto seriesSum (𝓝[<] (1 : ℝ)) (𝓝 1) := by
  exact gap5.mpr gap6

end

end ProofGap.Exercise2807
