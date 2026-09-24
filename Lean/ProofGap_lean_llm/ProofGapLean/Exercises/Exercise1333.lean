import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1333

noncomputable section
open Filter
open scoped Topology

def punctured (x₀ : ℝ) := nhdsWithin x₀ ({x₀} : Set ℝ)ᶜ
def original (x : ℝ) := (Real.cos (Real.sin x) - Real.cos x) / x ^ 4
def firstStage (x : ℝ) :=
  (-Real.cos x * Real.sin (Real.sin x) + Real.sin x) / (4 * x ^ 3)
def secondStage (x : ℝ) :=
  (Real.sin x * Real.sin (Real.sin x) -
    Real.cos x ^ 2 * Real.cos (Real.sin x) + Real.cos x) / (12 * x ^ 2)
def thirdStage (x : ℝ) :=
  (Real.cos x * Real.sin (Real.sin x) +
    (1 / 2 : ℝ) * Real.sin (2 * x) * Real.cos (Real.sin x) +
    Real.sin (2 * x) * Real.cos (Real.sin x) +
    Real.cos x ^ 3 * Real.sin (Real.sin x) - Real.sin x) / (24 * x)

private def num0 (x : ℝ) := Real.cos (Real.sin x) - Real.cos x

private def num1 (x : ℝ) :=
  -Real.cos x * Real.sin (Real.sin x) + Real.sin x

private def num2 (x : ℝ) :=
  Real.sin x * Real.sin (Real.sin x) -
    Real.cos x ^ 2 * Real.cos (Real.sin x) + Real.cos x

private def num3 (x : ℝ) :=
  Real.cos x * Real.sin (Real.sin x) +
    (1 / 2 : ℝ) * Real.sin (2 * x) * Real.cos (Real.sin x) +
    Real.sin (2 * x) * Real.cos (Real.sin x) +
    Real.cos x ^ 3 * Real.sin (Real.sin x) - Real.sin x

private def num3s (x : ℝ) :=
  Real.cos x * Real.sin (Real.sin x) +
    3 * (Real.sin x * Real.cos x * Real.cos (Real.sin x)) +
    Real.cos x ^ 3 * Real.sin (Real.sin x) - Real.sin x

private lemma num3_eq_num3s : num3 = num3s := by
  funext x
  unfold num3 num3s
  rw [Real.sin_two_mul]
  ring

private lemma num0_hasDerivAt (x : ℝ) : HasDerivAt num0 (num1 x) x := by
  unfold num0 num1
  convert (((Real.hasDerivAt_cos (Real.sin x)).scomp x
    (Real.hasDerivAt_sin x)).sub (Real.hasDerivAt_cos x)) using 1 <;>
    simp [Function.comp_apply, smul_eq_mul] <;> ring_nf

private lemma num1_hasDerivAt (x : ℝ) : HasDerivAt num1 (num2 x) x := by
  unfold num1 num2
  have hs := (Real.hasDerivAt_sin (Real.sin x)).scomp x
    (Real.hasDerivAt_sin x)
  convert ((((Real.hasDerivAt_cos x).neg.mul hs).add
    (Real.hasDerivAt_sin x))) using 1 <;>
    simp [Function.comp_apply, smul_eq_mul] <;> ring_nf

private lemma num2_hasDerivAt (x : ℝ) : HasDerivAt num2 (num3 x) x := by
  rw [num3_eq_num3s]
  unfold num2 num3s
  have hs := (Real.hasDerivAt_sin (Real.sin x)).scomp x
    (Real.hasDerivAt_sin x)
  have hc := (Real.hasDerivAt_cos (Real.sin x)).scomp x
    (Real.hasDerivAt_sin x)
  have hcosSq := (Real.hasDerivAt_cos x).pow 2
  convert ((((Real.hasDerivAt_sin x).mul hs).sub
    (hcosSq.mul hc)).add (Real.hasDerivAt_cos x)) using 1 <;>
    simp [Function.comp_apply, smul_eq_mul] <;> ring

private lemma num3s_hasDerivAt_zero : HasDerivAt num3s 4 0 := by
  have hsin : HasDerivAt (fun x : ℝ => Real.sin x) 1 0 := by
    simpa using Real.hasDerivAt_sin 0
  have hcos : HasDerivAt (fun x : ℝ => Real.cos x) 0 0 := by
    simpa using Real.hasDerivAt_cos 0
  have hsinSin : HasDerivAt (fun x : ℝ => Real.sin (Real.sin x)) 1 0 := by
    convert (Real.hasDerivAt_sin (Real.sin 0)).scomp 0
      (Real.hasDerivAt_sin 0) using 1 <;> norm_num
  have hcosSin : HasDerivAt (fun x : ℝ => Real.cos (Real.sin x)) 0 0 := by
    convert (Real.hasDerivAt_cos (Real.sin 0)).scomp 0
      (Real.hasDerivAt_sin 0) using 1 <;> norm_num
  have hall := (((hcos.mul hsinSin).add
    (((hsin.mul hcos).mul hcosSin).const_mul (3 : ℝ))).add
      ((hcos.pow 3).mul hsinSin)).sub hsin
  change HasDerivAt
    (fun x : ℝ =>
      Real.cos x * Real.sin (Real.sin x) +
        3 * (Real.sin x * Real.cos x * Real.cos (Real.sin x)) +
        Real.cos x ^ 3 * Real.sin (Real.sin x) - Real.sin x)
    4 0
  convert hall using 1 <;> norm_num

private lemma num3_hasDerivAt_zero : HasDerivAt num3 4 0 := by
  rw [num3_eq_num3s]
  exact num3s_hasDerivAt_zero

private lemma lhopital_at_zero
    {f g f' g' : ℝ → ℝ} {L : ℝ}
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hgne : ∀ x, x ≠ 0 → g' x ≠ 0)
    (hlim : Tendsto (fun x => f' x / g' x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)) :
    Tendsto (fun x => f x / g x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L) := by
  have hf_full : Tendsto f (nhds 0) (nhds 0) := by
    have hcont := (hf 0).continuousAt
    change Tendsto f (nhds 0) (nhds (f 0)) at hcont
    rw [hf0] at hcont
    exact hcont
  have hg_full : Tendsto g (nhds 0) (nhds 0) := by
    have hcont := (hg 0).continuousAt
    change Tendsto g (nhds 0) (nhds (g 0)) at hcont
    rw [hg0] at hcont
    exact hcont
  have hIoi : Set.Ioi (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ := by
    intro x hx
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ne_of_gt hx
  have hIio : Set.Iio (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ := by
    intro x hx
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ne_of_lt hx
  have hfGT : Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    hf_full.mono_left inf_le_left
  have hgGT : Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    hg_full.mono_left inf_le_left
  have hdfGT : ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0),
      HasDerivAt f (f' x) x := Filter.Eventually.of_forall hf
  have hdgGT : ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0),
      HasDerivAt g (g' x) x := Filter.Eventually.of_forall hg
  have hneGT : ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0), g' x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hgne x (ne_of_gt hx)
  have hlimGT : Tendsto (fun x => f' x / g' x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) :=
    hlim.mono_left (nhdsWithin_mono 0 hIoi)
  have hGT : Tendsto (fun x => f x / g x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
    exact HasDerivAt.lhopital_zero_nhdsGT
      (f' := f') (g' := g') hdfGT hdgGT hneGT hfGT hgGT hlimGT
  have hfLT : Tendsto f (nhdsWithin 0 (Set.Iio 0)) (nhds 0) :=
    hf_full.mono_left inf_le_left
  have hgLT : Tendsto g (nhdsWithin 0 (Set.Iio 0)) (nhds 0) :=
    hg_full.mono_left inf_le_left
  have hdfLT : ∀ᶠ x in nhdsWithin 0 (Set.Iio 0),
      HasDerivAt f (f' x) x := Filter.Eventually.of_forall hf
  have hdgLT : ∀ᶠ x in nhdsWithin 0 (Set.Iio 0),
      HasDerivAt g (g' x) x := Filter.Eventually.of_forall hg
  have hneLT : ∀ᶠ x in nhdsWithin 0 (Set.Iio 0), g' x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hgne x (ne_of_lt hx)
  have hlimLT : Tendsto (fun x => f' x / g' x)
      (nhdsWithin 0 (Set.Iio 0)) (nhds L) :=
    hlim.mono_left (nhdsWithin_mono 0 hIio)
  have hLT : Tendsto (fun x => f x / g x)
      (nhdsWithin 0 (Set.Iio 0)) (nhds L) := by
    exact HasDerivAt.lhopital_zero_nhdsLT
      (f' := f') (g' := g') hdfLT hdgLT hneLT hfLT hgLT hlimLT
  have hsets : ({0} : Set ℝ)ᶜ = Set.Iio 0 ∪ Set.Ioi 0 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro hx
      exact lt_or_gt_of_ne hx
    · rintro (hx | hx)
      · exact ne_of_lt hx
      · exact ne_of_gt hx
  rw [hsets, nhdsWithin_union]
  exact hLT.sup hGT

private lemma third_stage_limit :
    Tendsto (fun x => num3 x / (24 * x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 6 : ℝ)) := by
  have h : Tendsto (fun x => num3 x / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 4) := by
    simpa [num3, div_eq_mul_inv, mul_comm] using
      num3_hasDerivAt_zero.tendsto_slope_zero
  have hs : Tendsto (fun x => (1 / 24 : ℝ) * (num3 x / x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 6 : ℝ)) := by
    have hc : Tendsto (fun _ : ℝ => (1 / 24 : ℝ))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 24 : ℝ)) :=
      tendsto_const_nhds
    convert hc.mul h using 1 <;> norm_num
  refine hs.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  field_simp [hx0]

private lemma second_stage_limit :
    Tendsto (fun x => num2 x / (12 * x ^ 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 6 : ℝ)) := by
  apply lhopital_at_zero
    (f := num2) (g := fun x : ℝ => 12 * x ^ 2)
    (f' := num3) (g' := fun x : ℝ => 24 * x)
  · norm_num [num2]
  · norm_num
  · exact num2_hasDerivAt
  · intro x
    convert ((hasDerivAt_id x).pow 2).const_mul (12 : ℝ) using 1 <;>
      simp only [id_eq] <;> ring
  · intro x hx
    exact mul_ne_zero (by norm_num) hx
  · simpa using third_stage_limit

private lemma first_stage_limit :
    Tendsto (fun x => num1 x / (4 * x ^ 3))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 6 : ℝ)) := by
  apply lhopital_at_zero
    (f := num1) (g := fun x : ℝ => 4 * x ^ 3)
    (f' := num2) (g' := fun x : ℝ => 12 * x ^ 2)
  · norm_num [num1]
  · norm_num
  · exact num1_hasDerivAt
  · intro x
    convert ((hasDerivAt_id x).pow 3).const_mul (4 : ℝ) using 1 <;>
      simp only [id_eq] <;> ring
  · intro x hx
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)
  · simpa using second_stage_limit

private lemma original_limit :
    Tendsto (fun x => num0 x / x ^ 4)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 6 : ℝ)) := by
  apply lhopital_at_zero
    (f := num0) (g := fun x : ℝ => x ^ 4)
    (f' := num1) (g' := fun x : ℝ => 4 * x ^ 3)
  · norm_num [num0]
  · norm_num
  · exact num0_hasDerivAt
  · intro x
    convert (hasDerivAt_id x).pow 4 using 1 <;>
      simp only [id_eq] <;> ring
  · intro x hx
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hx)
  · simpa using first_stage_limit

theorem gap1 : Tendsto original (punctured 0) (nhds (1 / 6 : ℝ)) := by
  simpa [original, punctured, num0] using original_limit
theorem gap2 : Tendsto firstStage (punctured 0) (nhds (1 / 6 : ℝ)) := by
  change Tendsto (fun x : ℝ => num1 x / (4 * x ^ 3))
    (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 6 : ℝ))
  exact first_stage_limit
theorem gap3 : Tendsto secondStage (punctured 0) (nhds (1 / 6 : ℝ)) := by
  simpa [secondStage, punctured, num2] using second_stage_limit
theorem gap4 : Tendsto thirdStage (punctured 0) (nhds (1 / 6 : ℝ)) := by
  change Tendsto (fun x : ℝ => num3 x / (24 * x))
    (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 6 : ℝ))
  exact third_stage_limit
theorem gap5 : Tendsto thirdStage (punctured 0) (nhds (1 / 6 : ℝ)) := by
  exact gap4
theorem gap6 : Tendsto original (punctured 0) (nhds (1 / 6 : ℝ)) := by
  exact gap1

end
end ProofGap.Exercise1333
