import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise690

noncomputable section

def y (x : ℝ) : ℝ :=
  ((1 / x) - (1 / (x + 1))) / ((1 / (x - 1)) - (1 / x))

def SingularPoint (f : ℝ → ℝ) (a : ℝ) : Prop := ¬ ContinuousAt f a

/-- Exercise 690, gap 1; the signed one-sided limits at
`-1` disagree, so the corrected two-sided assertion uses absolute value. -/
private lemma y_eq_of_ne (x : ℝ) (hx0 : x ≠ 0) (hxm1 : x ≠ -1) (hx1 : x ≠ 1) :
    y x = (x - 1) / (x + 1) := by
  have hxp : x + 1 ≠ 0 := by
    intro h
    apply hxm1
    linarith
  have hxm : x - 1 ≠ 0 := by
    intro h
    apply hx1
    linarith
  have hn : (1 / x) - (1 / (x + 1)) = 1 / (x * (x + 1)) := by
    field_simp [hx0, hxp]
    ring
  have hd : (1 / (x - 1)) - (1 / x) = 1 / (x * (x - 1)) := by
    field_simp [hx0, hxm]
    ring
  unfold y
  rw [hn, hd]
  field_simp [hx0, hxp, hxm]

theorem gap1 :
    Filter.Tendsto (fun x => |y x|)
      (nhdsWithin (-1) ({-1} : Set ℝ)ᶜ) atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  have hbpos : 0 < |b| + 1 := by
    linarith [abs_nonneg b]
  have hdpos : 0 < 1 / (|b| + 1) := one_div_pos.mpr hbpos
  have hc : ContinuousAt (fun x : ℝ => |x + 1|) (-1) :=
    (continuousAt_id.add continuousAt_const).abs
  have ht0 :
      Filter.Tendsto (fun x : ℝ => |x + 1|)
        (nhdsWithin (-1) ({-1} : Set ℝ)ᶜ)
        (nhds |((-1 : ℝ) + 1)|) :=
    hc.continuousWithinAt
  norm_num at ht0
  have hclose :
      ∀ᶠ x in nhdsWithin (-1) ({-1} : Set ℝ)ᶜ,
        |x + 1| < 1 / (|b| + 1) := by
    exact ht0 (Iio_mem_nhds hdpos)
  have hid :
      Filter.Tendsto (fun x : ℝ => x)
        (nhdsWithin (-1) ({-1} : Set ℝ)ᶜ) (nhds (-1)) :=
    continuousAt_id.continuousWithinAt
  have hxneg :
      ∀ᶠ x in nhdsWithin (-1) ({-1} : Set ℝ)ᶜ, x < 0 := by
    exact hid (Iio_mem_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hxneg, hclose] with x hxmem hxneg' hxclose
  have hxm1 : x ≠ -1 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxmem
  have hx0 : x ≠ 0 := ne_of_lt hxneg'
  have hx1 : x ≠ 1 := by
    intro h
    linarith
  have hsum_ne : x + 1 ≠ 0 := by
    intro h
    apply hxm1
    linarith
  have hdenpos : 0 < |x + 1| := abs_pos.mpr hsum_ne
  have hnum : 1 ≤ |x - 1| := by
    rw [abs_of_neg (by linarith)]
    linarith
  have hprod : |x + 1| * (|b| + 1) < 1 :=
    (lt_div_iff₀ hbpos).mp hxclose
  have habsprod : |b| * |x + 1| < 1 := by
    calc
      |b| * |x + 1| < |b| * |x + 1| + |x + 1| := by linarith
      _ = |x + 1| * (|b| + 1) := by ring
      _ < 1 := hprod
  rw [y_eq_of_ne x hx0 hxm1 hx1, abs_div]
  apply (le_div_iff₀ hdenpos).2
  calc
    b * |x + 1| ≤ |b| * |x + 1| :=
      mul_le_mul_of_nonneg_right (le_abs_self b) hdenpos.le
    _ ≤ 1 := habsprod.le
    _ ≤ |x - 1| := hnum

/-- Exercise 690, gap 2; use the punctured limit, since the
totalized Lean division gives the original expression a different value at `0`. -/
theorem gap2 :
    Filter.Tendsto y (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-1)) := by
  have hlocal :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        x ∈ Set.Ioo (-(1 : ℝ) / 2) (1 / 2) := by
    have hid :
        Filter.Tendsto (fun x : ℝ => x)
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
      continuousAt_id.continuousWithinAt
    exact hid (Ioo_mem_nhds (by norm_num) (by norm_num))
  have heq :
      (fun x : ℝ => y x) =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
        (fun x : ℝ => (x - 1) / (x + 1)) := by
    filter_upwards [self_mem_nhdsWithin, hlocal] with x hxmem hxint
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxmem
    have hxm1 : x ≠ -1 := by
      intro h
      linarith [hxint.1]
    have hx1 : x ≠ 1 := by
      intro h
      linarith [hxint.2]
    exact y_eq_of_ne x hx0 hxm1 hx1
  have hc : ContinuousAt (fun x : ℝ => (x - 1) / (x + 1)) 0 :=
    (continuousAt_id.sub continuousAt_const).div
      (continuousAt_id.add continuousAt_const) (by norm_num)
  have hr :
      Filter.Tendsto (fun x : ℝ => (x - 1) / (x + 1))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds (((0 : ℝ) - 1) / ((0 : ℝ) + 1))) :=
    hc.continuousWithinAt
  norm_num at hr
  exact hr.congr' heq.symm

/-- Exercise 690, gap 3; use the punctured limit at `1`. -/
theorem gap3 :
    Filter.Tendsto y (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 0) := by
  have hlocal :
      ∀ᶠ x in nhdsWithin 1 ({1} : Set ℝ)ᶜ,
        x ∈ Set.Ioo ((1 : ℝ) / 2) (3 / 2) := by
    have hid :
        Filter.Tendsto (fun x : ℝ => x)
          (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 1) :=
      continuousAt_id.continuousWithinAt
    exact hid (Ioo_mem_nhds (by norm_num) (by norm_num))
  have heq :
      (fun x : ℝ => y x) =ᶠ[nhdsWithin 1 ({1} : Set ℝ)ᶜ]
        (fun x : ℝ => (x - 1) / (x + 1)) := by
    filter_upwards [self_mem_nhdsWithin, hlocal] with x hxmem hxint
    have hx1 : x ≠ 1 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxmem
    have hx0 : x ≠ 0 := by
      intro h
      linarith [hxint.1]
    have hxm1 : x ≠ -1 := by
      intro h
      linarith [hxint.1]
    exact y_eq_of_ne x hx0 hxm1 hx1
  have hc : ContinuousAt (fun x : ℝ => (x - 1) / (x + 1)) 1 :=
    (continuousAt_id.sub continuousAt_const).div
      (continuousAt_id.add continuousAt_const) (by norm_num)
  have hr :
      Filter.Tendsto (fun x : ℝ => (x - 1) / (x + 1))
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
        (nhds (((1 : ℝ) - 1) / ((1 : ℝ) + 1))) :=
    hc.continuousWithinAt
  norm_num at hr
  exact hr.congr' heq.symm

/-- Exercise 690, gap 4; bind the singular point. -/
theorem gap4 : SingularPoint y (-1) := by
  unfold SingularPoint
  intro hc
  have ht :
      Filter.Tendsto (fun x : ℝ => |y x|)
        (nhdsWithin (-1) ({-1} : Set ℝ)ᶜ) (nhds |y (-1)|) :=
    hc.abs.continuousWithinAt
  have hyval : |y (-1)| < (3 : ℝ) := by
    norm_num [y]
  have hsmall :
      ∀ᶠ x in nhdsWithin (-1) ({-1} : Set ℝ)ᶜ, |y x| < 3 :=
    ht (Iio_mem_nhds hyval)
  have hlarge :
      ∀ᶠ x in nhdsWithin (-1) ({-1} : Set ℝ)ᶜ, 3 ≤ |y x| :=
    (Filter.tendsto_atTop.1 gap1) 3
  rcases (hlarge.and hsmall).exists with ⟨x, hxlarge, hxsmall⟩
  exact (not_lt_of_ge hxlarge) hxsmall

/-- Exercise 690, gap 5; bind the singular point. -/
theorem gap5 : SingularPoint y 0 := by
  unfold SingularPoint
  intro hc
  have hwithin :
      Filter.Tendsto y (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (y 0)) :=
    hc.continuousWithinAt
  have heq : y 0 = -1 := tendsto_nhds_unique hwithin gap2
  norm_num [y] at heq

/-- Exercise 690, gap 6; bind the singular point. -/
theorem gap6 : SingularPoint y 1 := by
  unfold SingularPoint
  intro hc
  have hwithin :
      Filter.Tendsto y (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds (y 1)) :=
    hc.continuousWithinAt
  have heq : y 1 = 0 := tendsto_nhds_unique hwithin gap3
  norm_num [y] at heq

/-- Exercise 690, gap 7; state both finite punctured limits
with independently bound values. -/
theorem gap7 :
    (∃ L : ℝ, Filter.Tendsto y (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)) ∧
    (∃ L : ℝ, Filter.Tendsto y (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds L)) := by
  exact ⟨⟨-1, gap2⟩, ⟨0, gap3⟩⟩

/-- Exercise 690, gap 8. -/
theorem gap8 (x : ℝ) (hx : x ∈ ({-1, 0, 1} : Set ℝ)) :
    SingularPoint y x := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h
  · subst x
    exact gap4
  · subst x
    exact gap5
  · subst x
    exact gap6

end

end ProofGap.Exercise690
