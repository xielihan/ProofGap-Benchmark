import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Order.Filter.Tendsto

namespace ProofGap.Exercise3714

noncomputable section

open scoped Interval

def primitive (f : ℝ → ℝ) (a x : ℝ) : ℝ :=
  ∫ t in a..x, f t

def translatedDifferenceQuotient
    (f : ℝ → ℝ) (a x h : ℝ) : ℝ :=
  (1 / h) * ∫ t in a..x, (f (t + h) - f t)

def endpointDifferenceQuotient
    (f : ℝ → ℝ) (a x h : ℝ) : ℝ :=
  (primitive f a (x + h) - primitive f a x) / h -
    (primitive f a (a + h) - primitive f a a) / h

private theorem intervalIntegrable_between
    (f : ℝ → ℝ) (A B u v : ℝ)
    (hf : ContinuousOn f (Set.Icc A B))
    (hAu : A < u) (huB : u < B) (hAv : A < v) (hvB : v < B) :
    IntervalIntegrable f MeasureTheory.volume u v := by
  apply ContinuousOn.intervalIntegrable
  apply hf.mono
  intro z hz
  rcases Set.mem_uIcc.mp hz with hz | hz
  · exact ⟨le_trans (le_of_lt hAu) hz.1, le_trans hz.2 (le_of_lt hvB)⟩
  · exact ⟨le_trans (le_of_lt hAv) hz.1, le_trans hz.2 (le_of_lt huB)⟩

private theorem primitive_hasDerivAt
    (f : ℝ → ℝ) (A a y B : ℝ)
    (hf : ContinuousOn f (Set.Icc A B))
    (hAa : A < a) (haB : a < B) (hAy : A < y) (hyB : y < B) :
    HasDerivAt (primitive f a) (f y) y := by
  have hy_nhds : Set.Icc A B ∈ nhds y :=
    Filter.mem_of_superset (Ioo_mem_nhds hAy hyB) Set.Ioo_subset_Icc_self
  have hcont : ContinuousAt f y := hf.continuousAt hy_nhds
  have hmeas :
      StronglyMeasurableAtFilter f (nhds y) MeasureTheory.volume := by
    apply ContinuousAt.stronglyMeasurableAtFilter
    · exact (isOpen_Ioo : IsOpen (Set.Ioo A B))
    · intro z hz
      exact hf.continuousAt
        (Filter.mem_of_superset (Ioo_mem_nhds hz.1 hz.2)
          Set.Ioo_subset_Icc_self)
    · exact ⟨hAy, hyB⟩
  have hint : IntervalIntegrable f MeasureTheory.volume a y :=
    intervalIntegrable_between f A B a y hf hAa haB hAy hyB
  simpa [primitive] using
    (intervalIntegral.integral_hasDerivAt_right hint hmeas hcont)

private theorem tendsto_increment_quotient
    {F : ℝ → ℝ} {y d : ℝ} (h : HasDerivAt F d y) :
    Filter.Tendsto (fun z => (F (y + z) - F y) / z)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds d) := by
  have hle :
      nhdsWithin 0 (Set.Ioi 0) ≤ nhdsWithin 0 ({0}ᶜ : Set ℝ) := by
    apply nhdsWithin_mono
    intro z hz
    simp only [Set.mem_Ioi, Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
    exact ne_of_gt hz
  simpa only [div_eq_mul_inv, smul_eq_mul, mul_comm] using
    h.tendsto_slope_zero.mono_left hle

private theorem translatedDifferenceQuotient_eq_endpoint
    (f : ℝ → ℝ) (A a x B h : ℝ)
    (hf : ContinuousOn f (Set.Icc A B))
    (hAx : A < a) (hax : a < x) (hxB : x < B)
    (hh : 0 < h) (hsmall : h < B - x) :
    translatedDifferenceQuotient f a x h =
      endpointDifferenceQuotient f a x h := by
  have haB : a < B := by linarith
  have hAah : A < a + h := by linarith
  have hahB : a + h < B := by linarith
  have hAxh : A < x + h := by linarith
  have hxhB : x + h < B := by linarith
  have hbaseInt : IntervalIntegrable f MeasureTheory.volume a x :=
    intervalIntegrable_between f A B a x hf hAx haB (by linarith) hxB
  have hshiftCont : ContinuousOn (fun t : ℝ => f (t + h)) (Set.uIcc a x) := by
    apply hf.comp (continuous_id.add continuous_const).continuousOn
    intro t ht
    rw [Set.uIcc_of_le (le_of_lt hax)] at ht
    change A ≤ t + h ∧ t + h ≤ B
    constructor <;> linarith [ht.1, ht.2]
  have hshiftInt :
      IntervalIntegrable (fun t : ℝ => f (t + h)) MeasureTheory.volume a x :=
    hshiftCont.intervalIntegrable
  have htrans :
      (∫ t in a..x, f (t + h)) = ∫ t in a + h..x + h, f t := by
    simpa using
      (intervalIntegral.integral_comp_add h (f := f) (a := a) (b := x))
  have hint_a_ah : IntervalIntegrable f MeasureTheory.volume a (a + h) :=
    intervalIntegrable_between f A B a (a + h) hf hAx haB hAah hahB
  have hint_ah_xh : IntervalIntegrable f MeasureTheory.volume (a + h) (x + h) :=
    intervalIntegrable_between f A B (a + h) (x + h) hf hAah hahB hAxh hxhB
  have hint_ax : IntervalIntegrable f MeasureTheory.volume a x := hbaseInt
  have hint_x_xh : IntervalIntegrable f MeasureTheory.volume x (x + h) :=
    intervalIntegrable_between f A B x (x + h) hf (by linarith) hxB hAxh hxhB
  have hsplit1 :=
    intervalIntegral.integral_add_adjacent_intervals hint_a_ah hint_ah_xh
  have hsplit2 :=
    intervalIntegral.integral_add_adjacent_intervals hint_ax hint_x_xh
  have hsplit :
      (∫ t in a + h..x + h, f t) - (∫ t in a..x, f t) =
        (∫ t in x..x + h, f t) - (∫ t in a..a + h, f t) := by
    linarith [hsplit1, hsplit2]
  have hright :
      (∫ t in a..x + h, f t) - (∫ t in a..x, f t) =
        ∫ t in x..x + h, f t := by
    linarith [hsplit2]
  have hzero : (∫ t in a..a, f t) = 0 := intervalIntegral.integral_same
  unfold translatedDifferenceQuotient endpointDifferenceQuotient primitive
  rw [intervalIntegral.integral_sub hshiftInt hbaseInt, htrans, hsplit,
    hright, hzero]
  ring

theorem gap1 (f : ℝ → ℝ) (A a x B : ℝ)
    (hf : ContinuousOn f (Set.Icc A B))
    (hAx : A < a) (hax : a < x) (hxB : x < B) :
    HasDerivAt (primitive f a) (f x) x := by
  exact primitive_hasDerivAt f A a x B hf hAx (by linarith) (by linarith) hxB

theorem gap2 (f : ℝ → ℝ) (A a x B : ℝ)
    (hf : ContinuousOn f (Set.Icc A B))
    (hAx : A < a) (hax : a < x) (hxB : x < B) (L : ℝ) :
    Filter.Tendsto (translatedDifferenceQuotient f a x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ↔
      Filter.Tendsto (endpointDifferenceQuotient f a x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  have hsmall : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0), h < B - x := by
    refine Filter.Eventually.filter_mono ?_
      (eventually_lt_nhds (sub_pos.mpr hxB))
    exact (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds (0 : ℝ) from inf_le_left)
  have heq :
      translatedDifferenceQuotient f a x =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        endpointDifferenceQuotient f a x := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hsmallh
    exact translatedDifferenceQuotient_eq_endpoint f A a x B h hf hAx hax hxB
      (by simpa only [Set.mem_Ioi] using hh) hsmallh
  constructor
  · intro ht
    exact ht.congr' heq
  · intro ht
    exact ht.congr' heq.symm

theorem gap3 (f : ℝ → ℝ) (A a x B : ℝ)
    (hf : ContinuousOn f (Set.Icc A B))
    (hAx : A < a) (hax : a < x) (hxB : x < B) :
    Filter.Tendsto (endpointDifferenceQuotient f a x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (deriv (primitive f a) x - deriv (primitive f a) a)) := by
  have haB : a < B := by linarith
  have hxderiv : HasDerivAt (primitive f a) (f x) x :=
    primitive_hasDerivAt f A a x B hf hAx haB (by linarith) hxB
  have haderiv : HasDerivAt (primitive f a) (f a) a :=
    primitive_hasDerivAt f A a a B hf hAx haB hAx haB
  have hxq := tendsto_increment_quotient hxderiv
  have haq := tendsto_increment_quotient haderiv
  simpa [endpointDifferenceQuotient, hxderiv.deriv, haderiv.deriv] using hxq.sub haq

theorem gap4 (f : ℝ → ℝ) (A a x B : ℝ)
    (hf : ContinuousOn f (Set.Icc A B))
    (hAx : A < a) (hax : a < x) (hxB : x < B) :
    deriv (primitive f a) x = f x ∧ deriv (primitive f a) a = f a := by
  have haB : a < B := by linarith
  constructor
  · exact (primitive_hasDerivAt f A a x B hf hAx haB (by linarith) hxB).deriv
  · exact (primitive_hasDerivAt f A a a B hf hAx haB hAx haB).deriv

theorem gap5 (f : ℝ → ℝ) (A a x B : ℝ)
    (hf : ContinuousOn f (Set.Icc A B))
    (hAx : A < a) (hax : a < x) (hxB : x < B) :
    deriv (primitive f a) x - deriv (primitive f a) a = f x - f a := by
  rcases gap4 f A a x B hf hAx hax hxB with ⟨hx, ha⟩
  rw [hx, ha]

theorem gap6 (f : ℝ → ℝ) (A a x B : ℝ)
    (hf : ContinuousOn f (Set.Icc A B))
    (hAx : A < a) (hax : a < x) (hxB : x < B) :
    Filter.Tendsto (endpointDifferenceQuotient f a x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x - f a)) := by
  rw [← gap5 f A a x B hf hAx hax hxB]
  exact gap3 f A a x B hf hAx hax hxB

theorem gap7 (f : ℝ → ℝ) (A a x B : ℝ)
    (hf : ContinuousOn f (Set.Icc A B))
    (hAx : A < a) (hax : a < x) (hxB : x < B) :
    Filter.Tendsto (translatedDifferenceQuotient f a x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x - f a)) := by
  exact (gap2 f A a x B hf hAx hax hxB (f x - f a)).2
    (gap6 f A a x B hf hAx hax hxB)

end

end ProofGap.Exercise3714
