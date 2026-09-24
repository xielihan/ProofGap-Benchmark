import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1248

noncomputable section

def f (x : ℝ) : ℝ :=
  if x ≤ 1 then (3 - x ^ 2) / 2 else 1 / x

def mvtCondition (c : ℝ) : Prop :=
  f 2 - f 0 = deriv f c * (2 - 0) ∧ c ∈ Set.Ioo (0 : ℝ) 2

theorem gap1 :
    f 0 = 3 / 2 := by
  norm_num [f]

theorem gap2 :
    f 2 = 1 / 2 := by
  norm_num [f]

theorem gap3 (x : ℝ) (hx : 0 < x) :
    deriv f x = if x ≤ 1 then -x else -(1 / x ^ 2) := by
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa [pow_two, two_mul] using
      ((hasDerivAt_id x).mul (hasDerivAt_id x))
  have hp : HasDerivAt (fun y : ℝ => (3 - y ^ 2) / 2) (-x) x := by
    convert (((hasDerivAt_const x (3 : ℝ)).sub hsq).div_const 2) using 1 <;> ring
  have hraw : HasDerivAt ((fun _ : ℝ => (1 : ℝ)) / id) (-1 / x ^ 2) x := by
    simpa using
      ((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx.ne')
  have hfun : ((fun _ : ℝ => (1 : ℝ)) / id) = (fun y : ℝ => 1 / y) := by
    funext y
    rfl
  have hcoef : (-1 / x ^ 2 : ℝ) = -(1 / x ^ 2) := by
    rw [neg_div]
  have hq : HasDerivAt (fun y : ℝ => 1 / y) (-(1 / x ^ 2)) x := by
    rw [hfun, hcoef] at hraw
    exact hraw
  by_cases hle : x ≤ 1
  · rw [if_pos hle]
    by_cases hlt : x < 1
    · have he : f =ᶠ[nhds x] (fun y : ℝ => (3 - y ^ 2) / 2) := by
        filter_upwards [Iio_mem_nhds hlt] with y hy
        change y < (1 : ℝ) at hy
        simp only [f, if_pos (le_of_lt hy)]
      calc
        deriv f x = deriv (fun y : ℝ => (3 - y ^ 2) / 2) x := he.deriv_eq
        _ = -x := hp.deriv
    · have hx1 : x = 1 := le_antisymm hle (le_of_not_gt hlt)
      subst x
      have hp1 : HasDerivAt (fun y : ℝ => (3 - y ^ 2) / 2) (-1) 1 := by
        simpa using hp
      have hq1 : HasDerivAt (fun y : ℝ => 1 / y) (-1) 1 := by
        simpa using hq
      have hpw : HasDerivWithinAt f (-1) (Set.Iic 1) 1 := by
        apply hp1.hasDerivWithinAt.congr
        · intro y hy
          change y ≤ (1 : ℝ) at hy
          simp only [f, if_pos hy]
        · norm_num [f]
      have hqw : HasDerivWithinAt f (-1) (Set.Ici 1) 1 := by
        apply hq1.hasDerivWithinAt.congr
        · intro y hy
          change (1 : ℝ) ≤ y at hy
          rcases eq_or_lt_of_le hy with h | h
          · subst y
            norm_num [f]
          · simp only [f, if_neg (not_le_of_gt h)]
        · norm_num [f]
      have hu : Set.Iic (1 : ℝ) ∪ Set.Ici 1 = Set.univ := by
        ext y
        simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_univ, iff_true]
        exact le_total y 1
      have hboth : HasDerivWithinAt f (-1) (Set.Iic 1 ∪ Set.Ici 1) 1 := hpw.union hqw
      have hpiece : HasDerivAt f (-1) 1 := by
        apply hboth.hasDerivAt
        rw [hu]
        exact Filter.univ_mem
      exact hpiece.deriv
  · rw [if_neg hle]
    have hgt : 1 < x := lt_of_not_ge hle
    have he : f =ᶠ[nhds x] (fun y : ℝ => 1 / y) := by
      filter_upwards [Ioi_mem_nhds hgt] with y hy
      change (1 : ℝ) < y at hy
      simp only [f, if_neg (not_le_of_gt hy)]
    calc
      deriv f x = deriv (fun y : ℝ => 1 / y) x := he.deriv_eq
      _ = -(1 / x ^ 2) := hq.deriv

theorem gap4 (c : ℝ) :
    mvtCondition c ↔
      f 2 - f 0 = deriv f c * (2 - 0) ∧ c ∈ Set.Ioo (0 : ℝ) 2 := by
  rfl

theorem gap5 (c : ℝ) (hc : c ∈ Set.Ioo (0 : ℝ) 2) :
    f 2 - f 0 = deriv f c * 2 ↔
      ((c ≤ 1 ∧ (1 / 2 : ℝ) - 3 / 2 = -c * 2) ∨
       (1 < c ∧ (1 / 2 : ℝ) - 3 / 2 = -(1 / c ^ 2) * 2)) := by
  rw [gap2, gap1, gap3 c hc.1]
  by_cases hc1 : c ≤ 1
  · simp [hc1, not_lt_of_ge hc1]
  · have h1 : 1 < c := lt_of_not_ge hc1
    simp [hc1, h1]

theorem gap6 (c : ℝ) :
    mvtCondition c ↔
      c = 1 / 2 ∨ c = Real.sqrt 2 := by
  constructor
  · intro hm
    have hm' := (gap4 c).1 hm
    have heq : f 2 - f 0 = deriv f c * 2 := by
      simpa only [sub_zero] using hm'.1
    rcases (gap5 c hm'.2).1 heq with ⟨hc1, he⟩ | ⟨hc1, he⟩
    · left
      norm_num at he
      linarith
    · right
      have hc0 : c ≠ 0 := ne_of_gt hm'.2.1
      have hc_sq : c ^ 2 = 2 := by
        field_simp [hc0] at he
        nlinarith
      have hs_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
      have hs_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      have hprod : (c - Real.sqrt 2) * (c + Real.sqrt 2) = 0 := by
        calc
          (c - Real.sqrt 2) * (c + Real.sqrt 2) = c ^ 2 - (Real.sqrt 2) ^ 2 := by ring
          _ = 0 := by rw [hc_sq, hs_sq]; norm_num
      have hsum_ne : c + Real.sqrt 2 ≠ 0 := by
        apply ne_of_gt
        linarith [hm'.2.1, hs_nonneg]
      have hdiff : c - Real.sqrt 2 = 0 :=
        (mul_eq_zero.mp hprod).resolve_right hsum_ne
      linarith
  · rintro (rfl | rfl)
    · have hI : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 2 := by
        constructor <;> norm_num
      have heq : f 2 - f 0 = deriv f (1 / 2) * 2 :=
        (gap5 (1 / 2) hI).2 (Or.inl ⟨by norm_num, by norm_num⟩)
      apply (gap4 (1 / 2)).2
      exact ⟨by simpa only [sub_zero] using heq, hI⟩
    · have hs_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
      have hs_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      have hs_gt_one : 1 < Real.sqrt 2 := by
        nlinarith
      have hs_lt_two : Real.sqrt 2 < 2 := by
        nlinarith
      have hI : Real.sqrt 2 ∈ Set.Ioo (0 : ℝ) 2 := by
        constructor <;> linarith
      have heq : f 2 - f 0 = deriv f (Real.sqrt 2) * 2 := by
        apply (gap5 (Real.sqrt 2) hI).2
        apply Or.inr
        refine ⟨hs_gt_one, ?_⟩
        rw [hs_sq]
        norm_num
      apply (gap4 (Real.sqrt 2)).2
      exact ⟨by simpa only [sub_zero] using heq, hI⟩

theorem gap7 :
    -Real.sqrt 2 ∉ Set.Ioo (0 : ℝ) 2 := by
  intro h
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  linarith [h.1]

theorem gap8 (c : ℝ) :
    c ∈ ({(1 / 2 : ℝ), Real.sqrt 2} : Set ℝ) ↔
      mvtCondition c := by
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, gap6]

end

end ProofGap.Exercise1248
