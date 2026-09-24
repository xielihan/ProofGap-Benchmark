import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ProofGap.Exercise1399

noncomputable section
open Filter
open scoped Topology

def punctured (x₀ : ℝ) := nhdsWithin x₀ ({x₀} : Set ℝ)ᶜ
def original (x : ℝ) :=
  (Real.exp x * Real.sin x - x * (1 + x)) / x ^ 3
def leadingStage (x : ℝ) := ((1 / 3 : ℝ) * x ^ 3) / x ^ 3

theorem gap1 : Tendsto original (punctured 0) (nhds (1 / 3 : ℝ)) := by
  unfold punctured
  have hset : ({0} : Set ℝ)ᶜ = Set.Iio 0 ∪ Set.Ioi 0 := by
    ext x
    constructor
    · intro hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
      simp only [Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
      exact lt_or_gt_of_ne hx
    · intro hx
      simp only [Set.mem_union, Set.mem_Iio, Set.mem_Ioi] at hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact hx.elim ne_of_lt ne_of_gt
  rw [hset, nhdsWithin_union]
  change map original (𝓝[<] 0 ⊔ 𝓝[>] 0) ≤ 𝓝 (1 / 3 : ℝ)
  rw [Filter.map_sup, sup_le_iff]
  constructor
  · change Tendsto original (𝓝[<] 0) (𝓝 (1 / 3 : ℝ))
    unfold original
    apply HasDerivAt.lhopital_zero_nhdsLT
      (f' := fun x : ℝ => Real.exp x * Real.sin x + Real.exp x * Real.cos x - (1 + 2 * x))
      (g' := fun x : ℝ => 3 * x ^ 2)
    · filter_upwards with x
      convert (((Real.hasDerivAt_exp x).mul (Real.hasDerivAt_sin x)).sub
        ((hasDerivAt_id x).mul
          ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)))) using 1 <;>
        simp [id_eq] <;> ring
    · filter_upwards with x
      convert (hasDerivAt_id x).pow 3 using 1 <;> simp [id_eq] <;> ring
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := ne_of_lt hx
      simp [hx0]
    · have hcont : ContinuousAt
          (fun x : ℝ => Real.exp x * Real.sin x - x * (1 + x)) 0 := by
        fun_prop
      convert hcont.tendsto.mono_left inf_le_left using 1 <;> norm_num
    · have hcont : ContinuousAt (fun x : ℝ => x ^ 3) 0 := by
        fun_prop
      convert hcont.tendsto.mono_left inf_le_left using 1 <;> norm_num
    · apply HasDerivAt.lhopital_zero_nhdsLT
        (f' := fun x : ℝ => 2 * Real.exp x * Real.cos x - 2)
        (g' := fun x : ℝ => 6 * x)
      · filter_upwards with x
        convert
          ((((Real.hasDerivAt_exp x).mul (Real.hasDerivAt_sin x)).add
            ((Real.hasDerivAt_exp x).mul (Real.hasDerivAt_cos x))).sub
            ((hasDerivAt_const x (1 : ℝ)).add
              ((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)))) using 1 <;>
          simp [id_eq] <;> ring
      · filter_upwards with x
        convert ((hasDerivAt_const x (3 : ℝ)).mul
          ((hasDerivAt_id x).pow 2)) using 1 <;> simp [id_eq] <;> ring
      · filter_upwards [self_mem_nhdsWithin] with x hx
        have hx0 : x ≠ 0 := ne_of_lt hx
        simp [hx0]
      · have hcont : ContinuousAt
            (fun x : ℝ => Real.exp x * Real.sin x + Real.exp x * Real.cos x -
              (1 + 2 * x)) 0 := by
          fun_prop
        convert hcont.tendsto.mono_left inf_le_left using 1 <;> norm_num
      · have hcont : ContinuousAt (fun x : ℝ => 3 * x ^ 2) 0 := by
          fun_prop
        convert hcont.tendsto.mono_left inf_le_left using 1 <;> norm_num
      · apply HasDerivAt.lhopital_zero_nhdsLT
          (f' := fun x : ℝ => 2 * Real.exp x * (Real.cos x - Real.sin x))
          (g' := fun _ : ℝ => 6)
        · filter_upwards with x
          convert
            (((((hasDerivAt_const x (2 : ℝ)).mul (Real.hasDerivAt_exp x)).mul
              (Real.hasDerivAt_cos x))).sub (hasDerivAt_const x (2 : ℝ))) using 1 <;>
            simp [id_eq] <;> ring
        · filter_upwards with x
          convert ((hasDerivAt_const x (6 : ℝ)).mul (hasDerivAt_id x)) using 1 <;>
            simp [id_eq] <;> ring
        · norm_num
        · have hcont : ContinuousAt
              (fun x : ℝ => 2 * Real.exp x * Real.cos x - 2) 0 := by
            fun_prop
          convert hcont.tendsto.mono_left inf_le_left using 1 <;> norm_num
        · have hcont : ContinuousAt (fun x : ℝ => 6 * x) 0 := by
            fun_prop
          convert hcont.tendsto.mono_left inf_le_left using 1 <;> norm_num
        · have hcont : ContinuousAt
              (fun x : ℝ => 2 * Real.exp x * (Real.cos x - Real.sin x) / 6) 0 := by
            fun_prop
          convert hcont.tendsto.mono_left inf_le_left using 1 <;> norm_num
  · change Tendsto original (𝓝[>] 0) (𝓝 (1 / 3 : ℝ))
    unfold original
    apply HasDerivAt.lhopital_zero_nhdsGT
      (f' := fun x : ℝ => Real.exp x * Real.sin x + Real.exp x * Real.cos x - (1 + 2 * x))
      (g' := fun x : ℝ => 3 * x ^ 2)
    · filter_upwards with x
      convert (((Real.hasDerivAt_exp x).mul (Real.hasDerivAt_sin x)).sub
        ((hasDerivAt_id x).mul
          ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)))) using 1 <;>
        simp [id_eq] <;> ring
    · filter_upwards with x
      convert (hasDerivAt_id x).pow 3 using 1 <;> simp [id_eq] <;> ring
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      simp [hx0]
    · have hcont : ContinuousAt
          (fun x : ℝ => Real.exp x * Real.sin x - x * (1 + x)) 0 := by
        fun_prop
      convert hcont.tendsto.mono_left inf_le_left using 1 <;> norm_num
    · have hcont : ContinuousAt (fun x : ℝ => x ^ 3) 0 := by
        fun_prop
      convert hcont.tendsto.mono_left inf_le_left using 1 <;> norm_num
    · apply HasDerivAt.lhopital_zero_nhdsGT
        (f' := fun x : ℝ => 2 * Real.exp x * Real.cos x - 2)
        (g' := fun x : ℝ => 6 * x)
      · filter_upwards with x
        convert
          ((((Real.hasDerivAt_exp x).mul (Real.hasDerivAt_sin x)).add
            ((Real.hasDerivAt_exp x).mul (Real.hasDerivAt_cos x))).sub
            ((hasDerivAt_const x (1 : ℝ)).add
              ((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)))) using 1 <;>
          simp [id_eq] <;> ring
      · filter_upwards with x
        convert ((hasDerivAt_const x (3 : ℝ)).mul
          ((hasDerivAt_id x).pow 2)) using 1 <;> simp [id_eq] <;> ring
      · filter_upwards [self_mem_nhdsWithin] with x hx
        have hx0 : x ≠ 0 := ne_of_gt hx
        simp [hx0]
      · have hcont : ContinuousAt
            (fun x : ℝ => Real.exp x * Real.sin x + Real.exp x * Real.cos x -
              (1 + 2 * x)) 0 := by
          fun_prop
        convert hcont.tendsto.mono_left inf_le_left using 1 <;> norm_num
      · have hcont : ContinuousAt (fun x : ℝ => 3 * x ^ 2) 0 := by
          fun_prop
        convert hcont.tendsto.mono_left inf_le_left using 1 <;> norm_num
      · apply HasDerivAt.lhopital_zero_nhdsGT
          (f' := fun x : ℝ => 2 * Real.exp x * (Real.cos x - Real.sin x))
          (g' := fun _ : ℝ => 6)
        · filter_upwards with x
          convert
            (((((hasDerivAt_const x (2 : ℝ)).mul (Real.hasDerivAt_exp x)).mul
              (Real.hasDerivAt_cos x))).sub (hasDerivAt_const x (2 : ℝ))) using 1 <;>
            simp [id_eq] <;> ring
        · filter_upwards with x
          convert ((hasDerivAt_const x (6 : ℝ)).mul (hasDerivAt_id x)) using 1 <;>
            simp [id_eq] <;> ring
        · norm_num
        · have hcont : ContinuousAt
              (fun x : ℝ => 2 * Real.exp x * Real.cos x - 2) 0 := by
            fun_prop
          convert hcont.tendsto.mono_left inf_le_left using 1 <;> norm_num
        · have hcont : ContinuousAt (fun x : ℝ => 6 * x) 0 := by
            fun_prop
          convert hcont.tendsto.mono_left inf_le_left using 1 <;> norm_num
        · have hcont : ContinuousAt
              (fun x : ℝ => 2 * Real.exp x * (Real.cos x - Real.sin x) / 6) 0 := by
            fun_prop
          convert hcont.tendsto.mono_left inf_le_left using 1 <;> norm_num
theorem gap2 : Tendsto leadingStage (punctured 0) (nhds (1 / 3 : ℝ)) := by
  unfold punctured
  refine (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  simp [leadingStage, hx]
theorem gap3 : Tendsto leadingStage (punctured 0) (nhds (1 / 3 : ℝ)) := by
  exact gap2
theorem gap4 : Tendsto original (punctured 0) (nhds (1 / 3 : ℝ)) := by
  exact gap1

end
end ProofGap.Exercise1399
