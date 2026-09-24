import ProofGapLean.Prelude.Analysis
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise3203

noncomputable section

open Filter
open scoped Topology

def f (x y : ℝ) : ℝ :=
  if x ^ 2 + y ^ 2 = 0 then 0 else x ^ 2 * y / (x ^ 4 + y ^ 2)

def jointFunction (p : ℝ × ℝ) : ℝ :=
  f p.1 p.2

def radialPath (α t : ℝ) : ℝ :=
  f (t * Real.cos α) (t * Real.sin α)

def rawPolarExpression (α t : ℝ) : ℝ :=
  t ^ 3 * Real.cos α ^ 2 * Real.sin α /
    (t ^ 4 * Real.cos α ^ 4 + t ^ 2 * Real.sin α ^ 2)

def cancelledPolarExpression (α t : ℝ) : ℝ :=
  t * Real.cos α ^ 2 * Real.sin α /
    (t ^ 2 * Real.cos α ^ 4 + Real.sin α ^ 2)

def parabolaExpression (x : ℝ) : ℝ :=
  x ^ 4 / (x ^ 4 + x ^ 4)

def puncturedOrigin : Filter (ℝ × ℝ) :=
  nhdsWithin ((0, 0) : ℝ × ℝ)
    (({((0, 0) : ℝ × ℝ)} : Set (ℝ × ℝ))ᶜ)

def puncturedZero : Filter ℝ :=
  nhdsWithin (0 : ℝ) (({(0 : ℝ)} : Set ℝ)ᶜ)

theorem gap1 :
    ∀ α : ℝ, Real.sin α = 0 →
      Real.cos α = 1 ∨ Real.cos α = -1 := by
  intro α hsin
  have htrig := Real.sin_sq_add_cos_sq α
  rw [hsin] at htrig
  norm_num at htrig
  exact htrig

theorem gap2 :
    ∀ α t : ℝ, Real.sin α = 0 → t ≠ 0 →
      radialPath α t = t ^ 2 * 0 / (t ^ 4 + 0) := by
  intros α t hsin ht
  simp [radialPath, f, hsin]

theorem gap3 :
    ∀ α t : ℝ, Real.sin α = 0 → t ≠ 0 →
      t ^ 2 * 0 / (t ^ 4 + 0) = (0 : ℝ) := by
  intros α t hsin ht
  simp

theorem gap4 :
    ∀ α t : ℝ, Real.sin α = 0 → t ≠ 0 →
      radialPath α t = 0 := by
  intros α t hsin ht
  calc
    radialPath α t = t ^ 2 * 0 / (t ^ 4 + 0) := gap2 α t hsin ht
    _ = 0 := gap3 α t hsin ht

theorem gap5 :
    f 0 0 = 0 := by
  simp [f]

theorem gap6 :
    ∀ α : ℝ, Real.sin α = 0 →
      Tendsto (radialPath α) puncturedZero (𝓝 (f 0 0)) := by
  intro α hsin
  rw [gap5]
  have heq : radialPath α =ᶠ[puncturedZero] (fun _ : ℝ => 0) := by
    filter_upwards [show ∀ᶠ t in puncturedZero,
        t ∈ (({0} : Set ℝ)ᶜ) from self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    exact gap4 α t hsin ht0
  exact (tendsto_congr' heq).2 tendsto_const_nhds

theorem gap7 :
    ∀ α : ℝ, Real.sin α ≠ 0 →
      ∀ L : ℝ,
        Tendsto (radialPath α) puncturedZero (𝓝 L) ↔
          Tendsto (rawPolarExpression α) puncturedZero (𝓝 L) := by
  intro α hsin L
  have heq : radialPath α =ᶠ[puncturedZero] rawPolarExpression α := by
    filter_upwards [show ∀ᶠ t in puncturedZero,
        t ∈ (({0} : Set ℝ)ᶜ) from self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    have hy : t * Real.sin α ≠ 0 := mul_ne_zero ht0 hsin
    have hypos : 0 < (t * Real.sin α) ^ 2 := sq_pos_of_ne_zero hy
    have hsum :
        (t * Real.cos α) ^ 2 + (t * Real.sin α) ^ 2 ≠ 0 := by
      intro hzero
      nlinarith [sq_nonneg (t * Real.cos α)]
    rw [radialPath, f, if_neg hsum]
    unfold rawPolarExpression
    congr 1 <;> ring
  exact tendsto_congr' heq

theorem gap8 :
    ∀ α : ℝ, Real.sin α ≠ 0 →
      ∀ L : ℝ,
        Tendsto (rawPolarExpression α) puncturedZero (𝓝 L) ↔
          Tendsto (cancelledPolarExpression α) puncturedZero (𝓝 L) := by
  intro α hsin L
  have heq :
      rawPolarExpression α =ᶠ[puncturedZero]
        cancelledPolarExpression α := by
    filter_upwards [show ∀ᶠ t in puncturedZero,
        t ∈ (({0} : Set ℝ)ᶜ) from self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    have hden :
        t ^ 2 * Real.cos α ^ 4 + Real.sin α ^ 2 ≠ 0 := by
      positivity
    have hraw :
        t ^ 4 * Real.cos α ^ 4 + t ^ 2 * Real.sin α ^ 2 ≠ 0 := by
      positivity
    unfold rawPolarExpression cancelledPolarExpression
    field_simp [hraw, hden]
    <;> ring
  exact tendsto_congr' heq

theorem gap9 :
    ∀ α : ℝ, Real.sin α ≠ 0 →
      Tendsto (cancelledPolarExpression α) puncturedZero
        (𝓝 (0 / (0 + Real.sin α ^ 2))) := by
  intro α hsin
  have hle : puncturedZero ≤ 𝓝 (0 : ℝ) := by
    change nhds (0 : ℝ) ⊓ Filter.principal (({0} : Set ℝ)ᶜ) ≤ nhds 0
    exact inf_le_left
  have ht : Tendsto (fun t : ℝ => t) puncturedZero (𝓝 0) :=
    tendsto_id.mono_left hle
  have hnum :
      Tendsto (fun t : ℝ => t * Real.cos α ^ 2 * Real.sin α)
        puncturedZero
        (𝓝 (0 * Real.cos α ^ 2 * Real.sin α)) := by
    exact (ht.mul tendsto_const_nhds).mul tendsto_const_nhds
  have hden :
      Tendsto
        (fun t : ℝ => t ^ 2 * Real.cos α ^ 4 + Real.sin α ^ 2)
        puncturedZero
        (𝓝 (0 ^ 2 * Real.cos α ^ 4 + Real.sin α ^ 2)) := by
    exact ((ht.pow 2).mul tendsto_const_nhds).add tendsto_const_nhds
  have hden0 :
      0 ^ 2 * Real.cos α ^ 4 + Real.sin α ^ 2 ≠ 0 := by
    simpa using (pow_ne_zero 2 hsin)
  have hquot := hnum.div hden hden0
  simpa [cancelledPolarExpression] using hquot

theorem gap10 :
    ∀ α : ℝ, Real.sin α ≠ 0 →
      0 / (0 + Real.sin α ^ 2) = (0 : ℝ) := by
  intros α hsin
  simp

theorem gap11 :
    ∀ α : ℝ, Real.sin α ≠ 0 →
      Tendsto (radialPath α) puncturedZero (𝓝 0) := by
  intro α hsin
  apply (gap7 α hsin 0).2
  apply (gap8 α hsin 0).2
  simpa [gap10 α hsin] using gap9 α hsin

theorem gap12 :
    ∀ α : ℝ, Real.sin α ≠ 0 →
      Tendsto (radialPath α) puncturedZero (𝓝 (f 0 0)) := by
  intro α hsin
  rw [gap5]
  exact gap11 α hsin

theorem gap13 :
    ∀ α : ℝ,
      Tendsto (radialPath α) puncturedZero (𝓝 (f 0 0)) := by
  intro α
  by_cases hsin : Real.sin α = 0
  · exact gap6 α hsin
  · exact gap12 α hsin

theorem gap14 :
    ∀ L : ℝ,
      Tendsto jointFunction puncturedOrigin (𝓝 L) →
        Tendsto parabolaExpression puncturedZero (𝓝 L) := by
  intro L hL
  have hle : puncturedZero ≤ 𝓝 (0 : ℝ) := by
    change nhds (0 : ℝ) ⊓ Filter.principal (({0} : Set ℝ)ᶜ) ≤ nhds 0
    exact inf_le_left
  have ht : Tendsto (fun x : ℝ => x) puncturedZero (𝓝 0) :=
    tendsto_id.mono_left hle
  have hpair :
      Tendsto (fun x : ℝ => (x, x ^ 2)) puncturedZero
        (𝓝 ((0, 0) : ℝ × ℝ)) := by
    have hid : ContinuousAt (fun x : ℝ => x) (0 : ℝ) := continuousAt_id
    have hsq : ContinuousAt (fun x : ℝ => x ^ 2) (0 : ℝ) := hid.pow 2
    have hp : ContinuousAt (fun x : ℝ => (x, x ^ 2)) (0 : ℝ) :=
      hid.prodMk hsq
    simpa using hp.mono_left hle
  have hpath :
      Tendsto (fun x : ℝ => (x, x ^ 2)) puncturedZero
        puncturedOrigin := by
    rw [puncturedOrigin, tendsto_nhdsWithin_iff]
    refine ⟨hpair, ?_⟩
    filter_upwards [show ∀ᶠ x in puncturedZero,
        x ∈ (({0} : Set ℝ)ᶜ) from self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hp
    exact hx0 (congrArg Prod.fst hp)
  have hcomp :
      Tendsto (fun x : ℝ => jointFunction (x, x ^ 2))
        puncturedZero (𝓝 L) := by
    simpa only [Function.comp_apply] using hL.comp hpath
  have heq :
      (fun x : ℝ => jointFunction (x, x ^ 2)) =ᶠ[puncturedZero]
        parabolaExpression := by
    filter_upwards [show ∀ᶠ x in puncturedZero,
        x ∈ (({0} : Set ℝ)ᶜ) from self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    have hcond : x ^ 2 + (x ^ 2) ^ 2 ≠ 0 := by
      positivity
    unfold jointFunction f parabolaExpression
    simp only [hcond, if_false]
    congr 1 <;> ring
  exact (tendsto_congr' heq).1 hcomp

theorem gap15 :
    Tendsto parabolaExpression puncturedZero (𝓝 (1 / 2 : ℝ)) := by
  have heq :
      parabolaExpression =ᶠ[puncturedZero] (fun _ : ℝ => (1 / 2 : ℝ)) := by
    filter_upwards [show ∀ᶠ x in puncturedZero,
        x ∈ (({0} : Set ℝ)ᶜ) from self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    have hx4 : x ^ 4 ≠ 0 := pow_ne_zero 4 hx0
    unfold parabolaExpression
    field_simp [hx4]
    <;> ring
  exact (tendsto_congr' heq).2 tendsto_const_nhds

theorem gap16 :
    (1 / 2 : ℝ) ≠ f 0 0 := by
  rw [gap5]
  norm_num

theorem gap17 :
    ¬ Tendsto jointFunction puncturedOrigin (𝓝 (f 0 0)) := by
  intro hjoint
  have hpar :
      Tendsto parabolaExpression puncturedZero (𝓝 (f 0 0)) :=
    gap14 (f 0 0) hjoint
  have hsubset :
      Set.Ioi (0 : ℝ) ⊆ (({0} : Set ℝ)ᶜ) := by
    intro x hx
    simp only [Set.mem_Ioi] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  have hle :
      nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ puncturedZero := by
    rw [puncturedZero]
    exact nhdsWithin_mono 0 hsubset
  have heq : f 0 0 = (1 / 2 : ℝ) :=
    tendsto_nhds_unique (hpar.mono_left hle) (gap15.mono_left hle)
  exact gap16 heq.symm

theorem gap18 :
    ¬ ContinuousAt jointFunction ((0, 0) : ℝ × ℝ) := by
  intro hcont
  apply gap17
  have hle : puncturedOrigin ≤ 𝓝 ((0, 0) : ℝ × ℝ) := by
    change
      nhds ((0, 0) : ℝ × ℝ) ⊓
          Filter.principal (({((0, 0) : ℝ × ℝ)} : Set (ℝ × ℝ))ᶜ) ≤
        nhds ((0, 0) : ℝ × ℝ)
    exact inf_le_left
  simpa [jointFunction] using hcont.mono_left hle

theorem gap19 :
    (∀ α : ℝ,
      Tendsto (radialPath α) puncturedZero (𝓝 (f 0 0))) ∧
      ¬ ContinuousAt jointFunction ((0, 0) : ℝ × ℝ) := by
  exact ⟨gap13, gap18⟩

end

end ProofGap.Exercise3203
