import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise546

noncomputable section

def seq (n : ℕ) : ℝ := Real.tan (Real.pi / 4 + 1 / (n : ℝ)) ^ n
def tangentForm (n : ℕ) : ℝ :=
  ((1 + Real.tan (1 / (n : ℝ))) / (1 - Real.tan (1 / (n : ℝ)))) ^ n
def exponentialForm (n : ℕ) : ℝ :=
  Real.rpow (1 + 1 / ((1 - Real.tan (1 / (n : ℝ))) /
    (2 * Real.tan (1 / (n : ℝ)))))
    (((1 - Real.tan (1 / (n : ℝ))) / (2 * Real.tan (1 / (n : ℝ)))) *
      ((2 * Real.tan (1 / (n : ℝ))) / (1 / (n : ℝ))) *
      (1 / (1 - Real.tan (1 / (n : ℝ)))))

/-- Exercise 546, gap 1. -/
theorem gap1 (L : ℝ) :
    Filter.Tendsto seq Filter.atTop (nhds L) ↔
      Filter.Tendsto tangentForm Filter.atTop (nhds L) := by
  have heq : seq =ᶠ[Filter.atTop] tangentForm := by
    filter_upwards [Filter.eventually_atTop.2 ⟨2, fun _ hn => hn⟩] with n hn
    have hnreal : (2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hxpos : (0 : ℝ) < 1 / (n : ℝ) := one_div_pos.mpr hnpos
    have hxle : 1 / (n : ℝ) ≤ (1 : ℝ) / 2 := by
      apply (div_le_iff₀ hnpos).2
      nlinarith
    have hxlt : 1 / (n : ℝ) < Real.pi / 2 := by
      nlinarith [Real.two_le_pi]
    have hcosx : 0 < Real.cos (1 / (n : ℝ)) :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hxlt⟩
    have hcosp : 0 < Real.cos (Real.pi / 4) :=
      Real.cos_pos_of_mem_Ioo
        ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    have hpi4 : ∀ k : ℤ,
        Real.pi / 4 ≠ (2 * (k : ℝ) + 1) * Real.pi / 2 := by
      intro k hk
      apply hcosp.ne'
      rw [Real.cos_eq_zero_iff]
      exact ⟨k, hk⟩
    have hxnp : ∀ k : ℤ,
        1 / (n : ℝ) ≠ (2 * (k : ℝ) + 1) * Real.pi / 2 := by
      intro k hk
      apply hcosx.ne'
      rw [Real.cos_eq_zero_iff]
      exact ⟨k, hk⟩
    unfold seq tangentForm
    rw [Real.tan_add (Or.inl ⟨hpi4, hxnp⟩), Real.tan_pi_div_four]
    simp
  change Filter.map seq Filter.atTop ≤ nhds L ↔
    Filter.map tangentForm Filter.atTop ≤ nhds L
  rw [Filter.map_congr heq]

/-- Exercise 546, gap 2. -/
theorem gap2 :
    Filter.Tendsto exponentialForm Filter.atTop (nhds (Real.exp 2)) := by
  let x : ℕ → ℝ := fun n => 1 / (n : ℝ)
  let t : ℕ → ℝ := fun n => Real.tan (x n)
  let A : ℕ → ℝ := fun n => (1 - t n) / (2 * t n)
  let B : ℕ → ℝ := fun n => (2 * t n) / x n
  let C : ℕ → ℝ := fun n => 1 / (1 - t n)
  change Filter.Tendsto
    (fun n => Real.rpow (1 + 1 / A n) (A n * B n * C n))
    Filter.atTop (nhds (Real.exp 2))

  have hninf : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hx : Filter.Tendsto x Filter.atTop (nhds 0) := by
    simpa [x, one_div] using
      (tendsto_inv_atTop_zero.comp hninf)
  have hxne : ∀ᶠ n : ℕ in Filter.atTop, x n ≠ 0 := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)
    simp [x, hn0]
  have hxpunct : Filter.Tendsto x Filter.atTop
      (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) := by
    have hmem : ∀ᶠ n : ℕ in Filter.atTop, x n ∈ ({0}ᶜ : Set ℝ) := by
      filter_upwards [hxne] with n hn
      exact hn
    change Filter.Tendsto x Filter.atTop
      (nhds (0 : ℝ) ⊓ Filter.principal ({0}ᶜ : Set ℝ))
    simpa only [inf_idem] using
      hx.inf (Filter.tendsto_principal.2 hmem)

  have hslope0 := (Real.hasDerivAt_sin (0 : ℝ)).tendsto_slope
  change Filter.Tendsto
      (fun y : ℝ => (y - 0)⁻¹ * (Real.sin y - Real.sin 0))
      (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ))
      (nhds (Real.cos 0)) at hslope0
  have hslope : Filter.Tendsto
      (fun y : ℝ => (Real.sin y - Real.sin 0) / (y - 0))
      (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using hslope0
  have hsratio : Filter.Tendsto (fun n => Real.sin (x n) / x n)
      Filter.atTop (nhds 1) := by
    simpa [Function.comp_def] using hslope.comp hxpunct
  have hcos : Filter.Tendsto (fun n => Real.cos (x n))
      Filter.atTop (nhds 1) := by
    simpa using Real.continuous_cos.continuousAt.tendsto.comp hx
  have hratio : Filter.Tendsto (fun n => t n / x n)
      Filter.atTop (nhds 1) := by
    have hquot : Filter.Tendsto
        (fun n => (Real.sin (x n) / x n) / Real.cos (x n))
        Filter.atTop (nhds 1) := by
      simpa using hsratio.div hcos (by norm_num)
    have heq :
        (fun n => (Real.sin (x n) / x n) / Real.cos (x n)) =
          (fun n => t n / x n) := by
      funext n
      simp only [t, Real.tan_eq_sin_div_cos]
      ring
    rw [← heq]
    exact hquot
  have htprod : Filter.Tendsto (fun n => (t n / x n) * x n)
      Filter.atTop (nhds 0) := by
    simpa using hratio.mul hx
  have htx : (fun n => (t n / x n) * x n) =ᶠ[Filter.atTop] t := by
    filter_upwards [hxne] with n hxn
    field_simp
  have ht : Filter.Tendsto t Filter.atTop (nhds 0) := by
    change Filter.map t Filter.atTop ≤ nhds 0
    calc
      Filter.map t Filter.atTop =
          Filter.map (fun n => (t n / x n) * x n) Filter.atTop :=
        (Filter.map_congr htx).symm
      _ ≤ nhds 0 := htprod

  have htwo : Filter.Tendsto (fun _ : ℕ => (2 : ℝ)) Filter.atTop (nhds 2) :=
    tendsto_const_nhds
  have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have hB : Filter.Tendsto B Filter.atTop (nhds 2) := by
    simpa [B, mul_div_assoc] using htwo.mul hratio
  have hC : Filter.Tendsto C Filter.atTop (nhds 1) := by
    simpa only [C, one_div, sub_zero, inv_one] using
      (hone.sub ht).inv₀ (by norm_num)
  have hBC : Filter.Tendsto (fun n => B n * C n)
      Filter.atTop (nhds 2) := by
    simpa using hB.mul hC

  have htne : ∀ᶠ n in Filter.atTop, t n ≠ 0 := by
    have hrpos : ∀ᶠ n in Filter.atTop, 0 < t n / x n :=
      hratio.eventually (Ioi_mem_nhds (by norm_num))
    filter_upwards [hrpos] with n hn
    intro hzero
    rw [hzero] at hn
    norm_num at hn
  have hdenpos : ∀ᶠ n in Filter.atTop, 0 < 1 - t n := by
    have hzero : (0 : ℝ) < 1 - 0 := by norm_num
    have h := (hone.sub ht).eventually (Ioi_mem_nhds hzero)
    simpa using h
  have hAne : ∀ᶠ n in Filter.atTop, A n ≠ 0 := by
    filter_upwards [htne, hdenpos] with n htn hden
    have hnum : 1 - t n ≠ 0 := hden.ne'
    have hdenom : 2 * t n ≠ 0 := mul_ne_zero (by norm_num) htn
    simpa only [A] using div_ne_zero hnum hdenom

  have hdeltaeq :
      (fun n => 1 / A n) =ᶠ[Filter.atTop]
        (fun n => (2 * t n) / (1 - t n)) := by
    filter_upwards [htne, hdenpos] with n htn hden
    simp only [A]
    field_simp [htn, hden.ne'] <;> ring
  have hdalt : Filter.Tendsto (fun n => (2 * t n) / (1 - t n))
      Filter.atTop (nhds 0) := by
    simpa using (htwo.mul ht).div (hone.sub ht) (by norm_num)
  have hdelta : Filter.Tendsto (fun n => 1 / A n)
      Filter.atTop (nhds 0) := by
    change Filter.map (fun n => 1 / A n) Filter.atTop ≤ nhds 0
    calc
      Filter.map (fun n => 1 / A n) Filter.atTop =
          Filter.map (fun n => (2 * t n) / (1 - t n)) Filter.atTop :=
        Filter.map_congr hdeltaeq
      _ ≤ nhds 0 := hdalt
  have hbase : Filter.Tendsto (fun n => 1 + 1 / A n)
      Filter.atTop (nhds 1) := by
    simpa using hone.add hdelta
  have hbasene : ∀ᶠ n in Filter.atTop, 1 + 1 / A n ≠ 1 := by
    filter_upwards [hAne] with n hAn
    simp [hAn]
  have hbasepunct : Filter.Tendsto (fun n => 1 + 1 / A n)
      Filter.atTop (nhdsWithin (1 : ℝ) ({1}ᶜ : Set ℝ)) := by
    have hmem : ∀ᶠ n in Filter.atTop,
        1 + 1 / A n ∈ ({1}ᶜ : Set ℝ) := by
      filter_upwards [hbasene] with n hn
      exact hn
    change Filter.Tendsto (fun n => 1 + 1 / A n) Filter.atTop
      (nhds (1 : ℝ) ⊓ Filter.principal ({1}ᶜ : Set ℝ))
    simpa only [inf_idem] using
      hbase.inf (Filter.tendsto_principal.2 hmem)

  have hlogslope0 :=
    (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope
  change Filter.Tendsto
      (fun y : ℝ => (y - 1)⁻¹ * (Real.log y - Real.log 1))
      (nhdsWithin (1 : ℝ) ({1}ᶜ : Set ℝ))
      (nhds ((1 : ℝ)⁻¹)) at hlogslope0
  have hlogslope : Filter.Tendsto
      (fun y : ℝ => Real.log y / (y - 1))
      (nhdsWithin (1 : ℝ) ({1}ᶜ : Set ℝ)) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using hlogslope0
  have hlogratio : Filter.Tendsto
      (fun n => Real.log (1 + 1 / A n) / (1 / A n))
      Filter.atTop (nhds 1) := by
    simpa [Function.comp_def] using hlogslope.comp hbasepunct

  have hscaledEq :
      (fun n => (1 / A n) * (A n * B n * C n)) =ᶠ[Filter.atTop]
        (fun n => B n * C n) := by
    filter_upwards [hAne] with n hAn
    field_simp [hAn] <;> ring
  have hscaled : Filter.Tendsto
      (fun n => (1 / A n) * (A n * B n * C n))
      Filter.atTop (nhds 2) := by
    change Filter.map
      (fun n => (1 / A n) * (A n * B n * C n)) Filter.atTop ≤ nhds 2
    calc
      Filter.map (fun n => (1 / A n) * (A n * B n * C n))
          Filter.atTop = Filter.map (fun n => B n * C n) Filter.atTop :=
        Filter.map_congr hscaledEq
      _ ≤ nhds 2 := hBC
  have hproduct : Filter.Tendsto
      (fun n =>
        (Real.log (1 + 1 / A n) / (1 / A n)) *
          ((1 / A n) * (A n * B n * C n)))
      Filter.atTop (nhds 2) := by
    simpa using hlogratio.mul hscaled
  have hproductEq :
      (fun n =>
        (Real.log (1 + 1 / A n) / (1 / A n)) *
          ((1 / A n) * (A n * B n * C n))) =ᶠ[Filter.atTop]
        (fun n => Real.log (1 + 1 / A n) * (A n * B n * C n)) := by
    filter_upwards [hAne] with n hAn
    field_simp [hAn] <;> ring
  have hlogexp : Filter.Tendsto
      (fun n => Real.log (1 + 1 / A n) * (A n * B n * C n))
      Filter.atTop (nhds 2) := by
    change Filter.map
      (fun n => Real.log (1 + 1 / A n) * (A n * B n * C n))
      Filter.atTop ≤ nhds 2
    calc
      Filter.map
          (fun n => Real.log (1 + 1 / A n) * (A n * B n * C n))
          Filter.atTop =
        Filter.map
          (fun n =>
            (Real.log (1 + 1 / A n) / (1 / A n)) *
              ((1 / A n) * (A n * B n * C n)))
          Filter.atTop := (Filter.map_congr hproductEq).symm
      _ ≤ nhds 2 := hproduct
  have hexp : Filter.Tendsto
      (fun n => Real.exp
        (Real.log (1 + 1 / A n) * (A n * B n * C n)))
      Filter.atTop (nhds (Real.exp 2)) := by
    simpa using Real.continuous_exp.continuousAt.tendsto.comp hlogexp
  have hbasepos : ∀ᶠ n in Filter.atTop, 0 < 1 + 1 / A n :=
    hbase.eventually (Ioi_mem_nhds (by norm_num))
  have hrpowEq :
      (fun n => Real.rpow (1 + 1 / A n) (A n * B n * C n)) =ᶠ[Filter.atTop]
        (fun n => Real.exp
          (Real.log (1 + 1 / A n) * (A n * B n * C n))) := by
    filter_upwards [hbasepos] with n hpos
    exact Real.rpow_def_of_pos hpos (A n * B n * C n)
  change Filter.map
      (fun n => Real.rpow (1 + 1 / A n) (A n * B n * C n))
      Filter.atTop ≤ nhds (Real.exp 2)
  calc
    Filter.map
        (fun n => Real.rpow (1 + 1 / A n) (A n * B n * C n))
        Filter.atTop =
      Filter.map
        (fun n => Real.exp
          (Real.log (1 + 1 / A n) * (A n * B n * C n)))
        Filter.atTop := Filter.map_congr hrpowEq
    _ ≤ nhds (Real.exp 2) := hexp

end

end ProofGap.Exercise546
