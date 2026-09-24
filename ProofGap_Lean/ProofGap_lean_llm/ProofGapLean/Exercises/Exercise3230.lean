import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3230

noncomputable section

def f (x y : ℝ) : ℝ :=
  if x ^ 2 + y ^ 2 = 0 then
    0
  else
    x * y * ((x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2))

def differenceQuotient (y x : ℝ) : ℝ :=
  (f x y - f 0 y) / x

def explicitQuotient (y x : ℝ) : ℝ :=
  (x * y * ((x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2)) - 0) / x

def HasLimitAtZero (g : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto g (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => g t y) x

def partialY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => g x t) y

def mixedXY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX g x t) y

def mixedYX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY g t y) x

theorem gap1 :
    ∀ y L : ℝ,
      HasLimitAtZero (differenceQuotient y) L ↔
        HasLimitAtZero (explicitQuotient y) L := by
  intro y L
  have hfun : differenceQuotient y = explicitQuotient y := by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [differenceQuotient, explicitQuotient, f]
    · have hsum : x ^ 2 + y ^ 2 ≠ 0 :=
        ne_of_gt
          (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg y))
      simp [differenceQuotient, explicitQuotient, f, hsum]
  rw [hfun]

theorem gap2 :
    ∀ y : ℝ, HasLimitAtZero (explicitQuotient y) (-y) := by
  intro y
  unfold HasLimitAtZero
  by_cases hy : y = 0
  · subst y
    have hz : explicitQuotient 0 = (fun _ : ℝ => 0) := by
      funext x
      simp [explicitQuotient]
    rw [hz]
    have hc : ContinuousAt (fun _ : ℝ => (0 : ℝ)) 0 := continuousAt_const
    simpa using
      hc.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left)
  · have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
    have hden0 : (0 : ℝ) ^ 2 + y ^ 2 ≠ 0 := by
      simpa using ne_of_gt hy2
    have hc : ContinuousAt
        (fun x : ℝ => y * ((x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2))) 0 :=
      continuousAt_const.mul
        (((continuousAt_id.pow 2).sub continuousAt_const).div
          ((continuousAt_id.pow 2).add continuousAt_const) hden0)
    have heq :
        explicitQuotient y =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
          (fun x : ℝ => y * ((x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2))) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := by
        simpa using hx
      have hdenx : x ^ 2 + y ^ 2 ≠ 0 :=
        ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg x) hy2)
      unfold explicitQuotient
      field_simp [hx0, hdenx] <;> ring
    have hval :
        y * (((0 : ℝ) ^ 2 - y ^ 2) / ((0 : ℝ) ^ 2 + y ^ 2)) = -y := by
      field_simp [hy] <;> ring
    have ht : Filter.Tendsto
        (fun x : ℝ => y * ((x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2)))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds (y * (((0 : ℝ) ^ 2 - y ^ 2) / ((0 : ℝ) ^ 2 + y ^ 2)))) :=
      hc.tendsto.mono_left inf_le_left
    rw [hval] at ht
    exact (Filter.Tendsto.congr' heq.symm) ht

theorem gap3 :
    ∀ y : ℝ, HasLimitAtZero (differenceQuotient y) (-y) := by
  intro y
  exact (gap1 y (-y)).2 (gap2 y)

theorem gap4 :
    ∀ y : ℝ, partialX f 0 y = -y := by
  intro y
  unfold partialX
  have hderiv : HasDerivAt (fun t : ℝ => f t y) (-y) 0 := by
    apply (hasDerivAt_iff_tendsto_slope).2
    have hslope :
        slope (fun t : ℝ => f t y) 0 = differenceQuotient y := by
      funext t
      simp [slope, differenceQuotient, div_eq_mul_inv, mul_comm]
    rw [hslope]
    exact gap3 y
  exact hderiv.deriv

theorem gap5 :
    mixedXY f 0 0 = -1 := by
  unfold mixedXY
  have hfun :
      (fun t : ℝ => partialX f 0 t) = (fun t : ℝ => -t) := by
    funext t
    exact gap4 t
  rw [hfun]
  simpa [id] using (hasDerivAt_id (0 : ℝ)).neg.deriv

theorem gap6 :
    ∀ x : ℝ, partialY f x 0 = x := by
  intro x
  unfold partialY
  have hfun : (fun t : ℝ => f x t) = (fun t : ℝ => -(f t x)) := by
    funext t
    unfold f
    have hcomm : t ^ 2 + x ^ 2 = x ^ 2 + t ^ 2 := by
      ring
    rw [hcomm]
    by_cases h : x ^ 2 + t ^ 2 = 0
    · simp [h]
    · simp only [h, if_false]
      ring
  have hbase : HasDerivAt (fun t : ℝ => f t x) (-x) 0 := by
    apply (hasDerivAt_iff_tendsto_slope).2
    have hslope :
        slope (fun t : ℝ => f t x) 0 = differenceQuotient x := by
      funext t
      simp [slope, differenceQuotient, div_eq_mul_inv, mul_comm]
    rw [hslope]
    exact gap3 x
  have hneg : HasDerivAt (fun t : ℝ => -(f t x)) x 0 := by
    simpa using hbase.neg
  rw [hfun]
  exact hneg.deriv

theorem gap7 :
    mixedYX f 0 0 = 1 := by
  unfold mixedYX
  have hfun :
      (fun t : ℝ => partialY f t 0) = (fun t : ℝ => t) := by
    funext t
    exact gap6 t
  rw [hfun]
  simpa [id] using (hasDerivAt_id (0 : ℝ)).deriv

theorem gap8 :
    mixedXY f 0 0 ≠ mixedYX f 0 0 := by
  rw [gap5, gap7]
  norm_num

theorem gap9 :
    mixedXY f 0 0 ≠ mixedYX f 0 0 := by
  exact gap8

end

end ProofGap.Exercise3230
