import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2553

noncomputable section

def IsInteger (k : ℝ) : Prop := ∃ z : ℤ, k = z
def sineTerm (x : ℝ) (n : ℕ) : ℝ := Real.sin ((n + 1) * x)

theorem gap1 (k x : ℝ) (hx : x = k * Real.pi) (hk : IsInteger k)
    (n : ℕ) :
    Real.sin (n * x) = 0 := by
  rcases hk with ⟨z, hz⟩
  rw [hx, hz]
  refine Real.sin_eq_zero_iff.mpr ?_
  exact ⟨(n : ℤ) * z, by norm_num [Int.cast_mul, mul_assoc]⟩
theorem gap2 (k x : ℝ) (hx : x = k * Real.pi) (hk : IsInteger k) :
    HasSum (sineTerm x) 0 := by
  have hzero : sineTerm x = (fun _ : ℕ => (0 : ℝ)) := by
    funext n
    simpa only [sineTerm, Nat.cast_add, Nat.cast_one] using
      gap1 k x hx hk (n + 1)
  exact Eq.mpr
    (congrArg (fun f : ℕ → ℝ => HasSum f 0) hzero)
    (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
theorem gap3 (x : ℝ)
    (h : Filter.Tendsto (fun n : ℕ => Real.sin (n * x))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ => Real.sin ((n + 1) * x))
      Filter.atTop (nhds 0) := by
  have hsucc : Filter.Tendsto (fun n : ℕ => n + 1)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    refine Filter.eventually_atTop.2 ⟨b, ?_⟩
    intro a ha
    omega
  simpa [Function.comp_def] using h.comp hsucc
theorem gap4 (x : ℝ) (n : ℕ) :
    Real.sin ((n + 1) * x) =
      Real.sin (n * x) * Real.cos x +
        Real.cos (n * x) * Real.sin x := by
  simpa [Nat.cast_add, add_mul] using
    (Real.sin_add ((n : ℝ) * x) x)
theorem gap5 (x : ℝ)
    (h : Filter.Tendsto (fun n : ℕ => Real.sin (n * x))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ => Real.cos (n * x) * Real.sin x)
      Filter.atTop (nhds 0) := by
  have hs := gap3 x h
  simpa [gap4] using hs.sub (h.mul_const (Real.cos x))
theorem gap6 (k x : ℝ) (hx : x = k * Real.pi) :
    Real.sin x = Real.sin (k * Real.pi) := by
  simpa [hx]
theorem gap7 (k : ℝ) (hk : ¬ IsInteger k) :
    Real.sin (k * Real.pi) ≠ 0 := by
  intro hzero
  apply hk
  rcases Real.sin_eq_zero_iff.mp hzero with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  nlinarith [Real.pi_pos]
theorem gap8 (k x : ℝ) (hx : x = k * Real.pi) (hk : ¬ IsInteger k) :
    Real.sin x ≠ 0 := by
  rw [hx]
  exact gap7 k hk
theorem gap9 (x : ℝ) (hsinx : Real.sin x ≠ 0)
    (h : Filter.Tendsto (fun n : ℕ => Real.cos (n * x) * Real.sin x)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ => Real.cos (n * x))
      Filter.atTop (nhds 0) := by
  have h' := h.mul_const (Real.sin x)⁻¹
  simpa [mul_assoc, hsinx] using h'
theorem gap10 (x : ℝ) (n : ℕ) :
    1 = Real.sin (n * x) ^ 2 + Real.cos (n * x) ^ 2 := by
  simpa using (Real.sin_sq_add_cos_sq (n * x)).symm
theorem gap11 (x : ℝ)
    (hs : Filter.Tendsto (fun n : ℕ => Real.sin (n * x))
      Filter.atTop (nhds 0))
    (hc : Filter.Tendsto (fun n : ℕ => Real.cos (n * x))
      Filter.atTop (nhds 0)) :
    False := by
  have hsq := (hs.pow 2).add (hc.pow 2)
  have hzero : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
      Filter.atTop (nhds 0) := by
    have hfun : (fun _ : ℕ => (1 : ℝ)) =
        (fun n : ℕ => Real.sin (n * x) ^ 2 + Real.cos (n * x) ^ 2) := by
      funext n
      exact gap10 x n
    rw [hfun]
    simpa using hsq
  have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
      Filter.atTop (nhds 1) := tendsto_const_nhds
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique hone hzero
  exact one_ne_zero h10
theorem gap12 (k x : ℝ) (hx : x = k * Real.pi) (hk : ¬ IsInteger k)
    (hs : Filter.Tendsto (fun n : ℕ => Real.sin (n * x))
      Filter.atTop (nhds 0)) :
    False := by
  have hprod := gap5 x hs
  have hsin : Real.sin x ≠ 0 := gap8 k x hx hk
  have hc := gap9 x hsin hprod
  exact gap11 x hs hc
theorem gap13 (k x : ℝ) (hx : x = k * Real.pi) (hk : ¬ IsInteger k) :
    ¬ Filter.Tendsto (fun n : ℕ => Real.sin (n * x))
      Filter.atTop (nhds 0) := by
  intro hs
  exact gap12 k x hx hk hs
theorem gap14 (k x : ℝ) (hx : x = k * Real.pi) (hk : ¬ IsInteger k) :
    ¬ Summable (sineTerm x) := by
  intro hsum
  have ht : Filter.Tendsto
      (fun n : ℕ => Real.sin ((n + 1) * x))
      Filter.atTop (nhds 0) := by
    simpa [sineTerm] using hsum.tendsto_atTop_zero
  have hbase : Filter.Tendsto
      (fun n : ℕ => Real.sin (n * x))
      Filter.atTop (nhds 0) := by
    rw [Filter.tendsto_def]
    intro s hs
    have he : ∀ᶠ n : ℕ in Filter.atTop,
        Real.sin ((n + 1) * x) ∈ s := ht hs
    rcases Filter.eventually_atTop.1 he with ⟨N, hN⟩
    refine Filter.eventually_atTop.2 ⟨N + 1, ?_⟩
    intro b hb
    have hb1 : 1 ≤ b := by omega
    have hNb : N ≤ b - 1 := by omega
    have hnat : b - 1 + 1 = b := Nat.sub_add_cancel hb1
    have hcastNat : (((b - 1 + 1 : ℕ) : ℝ)) = (b : ℝ) :=
      congrArg (fun m : ℕ => (m : ℝ)) hnat
    have hcast : ((b - 1 : ℕ) : ℝ) + 1 = (b : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hcastNat
    simpa only [hcast] using hN (b - 1) hNb
  exact gap13 k x hx hk hbase

end

end ProofGap.Exercise2553
