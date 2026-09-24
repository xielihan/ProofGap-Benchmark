import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise572

noncomputable section

def original (x : ℝ) : ℝ :=
  (Real.cos (x * Real.exp x) - Real.cos (x * Real.exp (-x))) / x ^ 3
def productForm (x : ℝ) : ℝ :=
  (-2 * Real.sin (x * (Real.exp x + Real.exp (-x)) / 2) *
    Real.sin (x * (Real.exp x - Real.exp (-x)) / 2)) / x ^ 3
def normalized (x : ℝ) : ℝ :=
  -2 * (Real.sin (x * (Real.exp x + Real.exp (-x)) / 2) /
      (x * (Real.exp x + Real.exp (-x)) / 2)) *
    (Real.sin (x * (Real.exp x - Real.exp (-x)) / 2) /
      (x * (Real.exp x - Real.exp (-x)) / 2)) *
    (x ^ 2 * (Real.exp (4 * x) - 1) / (4 * x ^ 3 * Real.exp (2 * x)))
def reduced (x : ℝ) : ℝ :=
  -2 * ((Real.exp (4 * x) - 1) / (4 * x)) * (1 / Real.exp (2 * x))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 572, gap 1. -/
private theorem tendsto_punctured_comp
    {f g : ℝ → ℝ} {L : ℝ}
    (hf : Filter.Tendsto f
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L))
    (hg : Filter.Tendsto g
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0))
    (hgne : ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ, g x ≠ 0) :
    Filter.Tendsto (fun x => f (g x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L) := by
  apply hf.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨hg, by simpa using hgne⟩

private theorem tendsto_sin_div_zero :
    Filter.Tendsto (fun x : ℝ => Real.sin x / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  simpa [div_eq_mul_inv, mul_comm] using
    (Real.hasDerivAt_sin 0).tendsto_slope_zero

theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero productForm L := by
  have hfun : original = productForm := by
    funext x
    simp only [original, productForm]
    have hadd :
        x * Real.exp x + x * Real.exp (-x) =
          x * (Real.exp x + Real.exp (-x)) := by
      ring
    have hsub :
        x * Real.exp x - x * Real.exp (-x) =
          x * (Real.exp x - Real.exp (-x)) := by
      ring
    rw [Real.cos_sub_cos, hadd, hsub]
  rw [hfun]

/-- Exercise 572, gap 2. -/
theorem gap2 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero normalized L := by
  rw [gap1]
  have heq :
      productForm =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] normalized := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    have he : Real.exp x ≠ 0 := ne_of_gt (Real.exp_pos x)
    have hsum : Real.exp x + Real.exp (-x) ≠ 0 :=
      ne_of_gt (add_pos (Real.exp_pos x) (Real.exp_pos (-x)))
    have hdiff : Real.exp x - Real.exp (-x) ≠ 0 := by
      apply sub_ne_zero.mpr
      intro h
      have heq' : x = -x := Real.exp_injective h
      apply hx0
      linarith
    have hexp2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
      calc
        Real.exp (2 * x) = Real.exp (x + x) := by congr 1 <;> ring
        _ = Real.exp x * Real.exp x := Real.exp_add x x
    have hexp4 :
        Real.exp (4 * x) =
          (Real.exp x * Real.exp x) * (Real.exp x * Real.exp x) := by
      calc
        Real.exp (4 * x) = Real.exp (2 * x + 2 * x) := by congr 1 <;> ring
        _ = Real.exp (2 * x) * Real.exp (2 * x) :=
          Real.exp_add (2 * x) (2 * x)
        _ = (Real.exp x * Real.exp x) * (Real.exp x * Real.exp x) := by
          rw [hexp2]
    simp only [productForm, normalized]
    have hfactor :
        x ^ 2 * (Real.exp (4 * x) - 1) /
            (4 * x ^ 3 * Real.exp (2 * x)) =
          ((x * (Real.exp x + Real.exp (-x)) / 2) *
            (x * (Real.exp x - Real.exp (-x)) / 2)) / x ^ 3 := by
      rw [Real.exp_neg x, hexp2, hexp4]
      field_simp [hx0, he] <;> ring
    rw [hfactor]
    field_simp [hx0, hsum, hdiff] <;> ring
  change
    (Filter.map productForm (nhdsWithin 0 ({0} : Set ℝ)ᶜ) ≤ nhds L) ↔
      Filter.map normalized (nhdsWithin 0 ({0} : Set ℝ)ᶜ) ≤ nhds L
  rw [Filter.map_congr heq]

/-- Exercise 572, gap 3. -/
theorem gap3 (L : ℝ) :
    HasLimitAtZero normalized L ↔ HasLimitAtZero reduced L := by
  unfold HasLimitAtZero
  let a : ℝ → ℝ := fun x =>
    x * (Real.exp x + Real.exp (-x)) / 2
  let b : ℝ → ℝ := fun x =>
    x * (Real.exp x - Real.exp (-x)) / 2
  let p : ℝ → ℝ := fun x =>
    (Real.sin (a x) / a x) * (Real.sin (b x) / b x)
  have ha0 :
      Filter.Tendsto a (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have ha_cont : ContinuousAt a 0 := by
      dsimp [a]
      fun_prop
    simpa [a] using ha_cont.tendsto.mono_left inf_le_left
  have hb0 :
      Filter.Tendsto b (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have hb_cont : ContinuousAt b 0 := by
      dsimp [b]
      fun_prop
    simpa [b] using hb_cont.tendsto.mono_left inf_le_left
  have ha_ne :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ, a x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    dsimp [a]
    exact div_ne_zero
      (mul_ne_zero hx0
        (ne_of_gt (add_pos (Real.exp_pos x) (Real.exp_pos (-x)))))
      (by norm_num)
  have hb_ne :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ, b x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    have he : Real.exp x ≠ Real.exp (-x) := by
      intro h
      have heq : x = -x := Real.exp_injective h
      apply hx0
      linarith
    dsimp [b]
    exact div_ne_zero (mul_ne_zero hx0 (sub_ne_zero.mpr he)) (by norm_num)
  have ha_lim :
      Filter.Tendsto (fun x => Real.sin (a x) / a x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using
      (tendsto_punctured_comp tendsto_sin_div_zero ha0 ha_ne)
  have hb_lim :
      Filter.Tendsto (fun x => Real.sin (b x) / b x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using
      (tendsto_punctured_comp tendsto_sin_div_zero hb0 hb_ne)
  have hp :
      Filter.Tendsto p (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [p] using ha_lim.mul hb_lim
  have hp_ne :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ, p x ≠ 0 := by
    exact hp (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0))
  have hrel :
      (fun x => normalized x) =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
        fun x => p x * reduced x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    have hc :
        x ^ 2 * (Real.exp (4 * x) - 1) /
            (4 * x ^ 3 * Real.exp (2 * x)) =
          ((Real.exp (4 * x) - 1) / (4 * x)) *
            (1 / Real.exp (2 * x)) := by
      field_simp [hx0, Real.exp_ne_zero] <;> ring
    simp only [normalized, reduced, p, a, b]
    rw [hc]
    ring
  constructor
  · intro hn
    have hdiv :
        Filter.Tendsto (fun x => normalized x / p x)
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L) := by
      simpa using hn.div hp (by norm_num)
    have hdivrel :
        (fun x => normalized x / p x) =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
          reduced := by
      filter_upwards [hrel, hp_ne] with x hxp hp0
      rw [hxp]
      field_simp [hp0]
    change Filter.map reduced (nhdsWithin 0 ({0} : Set ℝ)ᶜ) ≤ nhds L
    rw [← Filter.map_congr hdivrel]
    exact hdiv
  · intro hr
    have hmul :
        Filter.Tendsto (fun x => p x * reduced x)
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L) := by
      simpa using hp.mul hr
    change Filter.map normalized (nhdsWithin 0 ({0} : Set ℝ)ᶜ) ≤ nhds L
    rw [Filter.map_congr hrel]
    exact hmul

/-- Exercise 572, gap 4. -/
theorem gap4 : HasLimitAtZero reduced (-2) := by
  unfold HasLimitAtZero
  have hbase :
      Filter.Tendsto (fun y : ℝ => (Real.exp y - 1) / y)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_exp 0).tendsto_slope_zero
  have hg0 :
      Filter.Tendsto (fun x : ℝ => 4 * x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have hc : ContinuousAt (fun x : ℝ => 4 * x) 0 := by
      fun_prop
    simpa using hc.tendsto.mono_left inf_le_left
  have hg_ne :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ, 4 * x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    exact mul_ne_zero (by norm_num) hx0
  have hquot :
      Filter.Tendsto
        (fun x : ℝ => (Real.exp (4 * x) - 1) / (4 * x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using
      (tendsto_punctured_comp hbase hg0 hg_ne)
  have hexp :
      Filter.Tendsto (fun x : ℝ => 1 / Real.exp (2 * x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have hcden : ContinuousAt (fun x : ℝ => Real.exp (2 * x)) 0 := by
      fun_prop
    have hcinv : ContinuousAt (fun x : ℝ => (Real.exp (2 * x))⁻¹) 0 :=
      hcden.inv₀ (Real.exp_ne_zero _)
    simpa [one_div] using hcinv.tendsto.mono_left inf_le_left
  have hconst :
      Filter.Tendsto (fun _ : ℝ => (-2 : ℝ))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-2)) :=
    tendsto_const_nhds
  change Filter.Tendsto
    (fun x : ℝ => (-2 : ℝ) *
      ((Real.exp (4 * x) - 1) / (4 * x)) *
      (1 / Real.exp (2 * x)))
    (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-2))
  simpa only [mul_one] using (hconst.mul hquot).mul hexp

/-- Exercise 572, gap 5. -/
theorem gap5 : HasLimitAtZero original (-2) := by
  exact (gap2 (-2)).2 ((gap3 (-2)).2 gap4)

end

end ProofGap.Exercise572
