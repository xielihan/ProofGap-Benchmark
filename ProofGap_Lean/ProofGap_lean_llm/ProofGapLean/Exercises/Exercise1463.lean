import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise1463

noncomputable section

open Filter

def f (h x : ℝ) : ℝ := x ^ 3 - 3 * x ^ 2 - 9 * x + h

def UniqueRootOn (u : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ x ∈ s, u x = 0 ∧ ∀ y ∈ s, u y = 0 → y = x

private lemma hasDerivAt_f (h x : ℝ) :
    HasDerivAt (f h) (3 * x ^ 2 - 6 * x - 9) x := by
  unfold f
  convert ((((hasDerivAt_id x).pow 3).sub
    ((hasDerivAt_const x 3).mul ((hasDerivAt_id x).pow 2))).sub
      ((hasDerivAt_const x 9).mul (hasDerivAt_id x))).add_const h using 1 <;>
    simp [id] <;> ring

private lemma continuous_f (h : ℝ) : Continuous (f h) := by
  unfold f
  fun_prop

private lemma tendsto_f_atTop (h : ℝ) : Tendsto (f h) atTop atTop := by
  have hp3 : Tendsto (fun x : ℝ => x ^ 3) atTop atTop :=
    tendsto_pow_atTop (n := 3) (by norm_num)
  have hp2 : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
    tendsto_pow_atTop (n := 2) (by norm_num)
  have hfac : Tendsto
      (fun x : ℝ => 1 - 3 / x - 9 / x ^ 2 + h / x ^ 3) atTop (nhds 1) := by
    convert ((tendsto_const_nhds.sub (tendsto_id.const_div_atTop 3)).sub
      (hp2.const_div_atTop 9)).add (hp3.const_div_atTop h) using 1 <;> norm_num
  have ht := hp3.atTop_mul_pos zero_lt_one hfac
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold f
  field_simp [hx.ne']

private lemma tendsto_f_atBot (h : ℝ) : Tendsto (f h) atBot atBot := by
  have hp3top : Tendsto (fun x : ℝ => x ^ 3) atTop atTop :=
    tendsto_pow_atTop (n := 3) (by norm_num)
  have hp2top : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
    tendsto_pow_atTop (n := 2) (by norm_num)
  have hp3 : Tendsto (fun x : ℝ => x ^ 3) atBot atBot := by
    convert tendsto_neg_atTop_atBot.comp
      (hp3top.comp tendsto_neg_atBot_atTop) using 1
    funext x
    simp [Function.comp_apply]
    ring
  have hp2 : Tendsto (fun x : ℝ => x ^ 2) atBot atTop := by
    convert hp2top.comp tendsto_neg_atBot_atTop using 1
    funext x
    simp [Function.comp_apply]
  have hfac : Tendsto
      (fun x : ℝ => 1 - 3 / x - 9 / x ^ 2 + h / x ^ 3) atBot (nhds 1) := by
    convert ((tendsto_const_nhds.sub (tendsto_id.const_div_atBot 3)).sub
      (hp2.const_div_atTop 9)).add (hp3.const_div_atBot h) using 1 <;> norm_num
  have ht := hp3.atBot_mul_pos zero_lt_one hfac
  apply ht.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  unfold f
  field_simp [hx.ne]

private lemma deriv_f (h x : ℝ) :
    deriv (f h) x = 3 * x ^ 2 - 6 * x - 9 :=
  (hasDerivAt_f h x).deriv

private lemma deriv_pos_left (h x : ℝ) (hx : x < -1) :
    0 < deriv (f h) x := by
  rw [deriv_f]
  have hp : 0 < (x + 1) * (x - 3) :=
    mul_pos_of_neg_of_neg (by linarith) (by linarith)
  nlinarith

private lemma deriv_neg_middle (h x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 3) :
    deriv (f h) x < 0 := by
  rw [deriv_f]
  have hp : (x + 1) * (x - 3) < 0 :=
    mul_neg_of_pos_of_neg (by linarith [hx.1]) (by linarith [hx.2])
  nlinarith

private lemma deriv_pos_right (h x : ℝ) (hx : 3 < x) :
    0 < deriv (f h) x := by
  rw [deriv_f]
  have hp : 0 < (x + 1) * (x - 3) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

private lemma exists_root_right (h : ℝ) (h3 : f h 3 < 0) :
    ∃ x ∈ Set.Ioi (3 : ℝ), f h x = 0 := by
  rcases (((tendsto_f_atTop h).eventually_gt_atTop 0).and
    (eventually_gt_atTop (3 : ℝ))).exists with ⟨b, hfb, hb⟩
  have hiv := intermediate_value_Icc (le_of_lt hb) (continuous_f h).continuousOn
  rcases hiv ⟨h3.le, hfb.le⟩ with ⟨x, hx, hzero⟩
  refine ⟨x, ?_, hzero⟩
  exact lt_of_le_of_ne hx.1 (by
    intro heq
    subst x
    linarith)

private lemma exists_root_left (h : ℝ) (hm1 : 0 < f h (-1)) :
    ∃ x ∈ Set.Iio (-1 : ℝ), f h x = 0 := by
  rcases (((tendsto_f_atBot h).eventually_lt_atBot 0).and
    (eventually_lt_atBot (-1 : ℝ))).exists with ⟨b, hfb, hb⟩
  have hiv := intermediate_value_Icc (le_of_lt hb) (continuous_f h).continuousOn
  rcases hiv ⟨hfb.le, hm1.le⟩ with ⟨x, hx, hzero⟩
  refine ⟨x, ?_, hzero⟩
  exact lt_of_le_of_ne hx.2 (by
    intro heq
    subst x
    linarith)

private lemma exists_root_middle (h : ℝ) (hm1 : 0 < f h (-1)) (h3 : f h 3 < 0) :
    ∃ x ∈ Set.Ioo (-1 : ℝ) 3, f h x = 0 := by
  have hiv := intermediate_value_Icc' (by norm_num : (-1 : ℝ) ≤ 3)
    (continuous_f h).continuousOn
  rcases hiv ⟨h3.le, hm1.le⟩ with ⟨x, hx, hzero⟩
  refine ⟨x, ?_, hzero⟩
  constructor
  · exact lt_of_le_of_ne hx.1 (by
      intro heq
      subst x
      linarith)
  · exact lt_of_le_of_ne hx.2 (by
      intro heq
      subst x
      linarith)

private lemma unique_root_right (h : ℝ) (h3 : f h 3 < 0) :
    UniqueRootOn (f h) (Set.Ioi 3) := by
  rcases exists_root_right h h3 with ⟨x, hx, hzero⟩
  have hmono : StrictMonoOn (f h) (Set.Ici 3) :=
    strictMonoOn_of_deriv_pos (D := Set.Ici (3 : ℝ)) (convex_Ici 3)
      (continuous_f h).continuousOn (by
        intro y hy
        rw [interior_Ici] at hy
        exact deriv_pos_right h y hy)
  refine ⟨x, hx, hzero, ?_⟩
  intro y hy hyzero
  exact hmono.injOn (x₁ := y) (x₂ := x)
    (show 3 ≤ y from hy.le) (show 3 ≤ x from hx.le) (hyzero.trans hzero.symm)

private lemma unique_root_left (h : ℝ) (hm1 : 0 < f h (-1)) :
    UniqueRootOn (f h) (Set.Iio (-1)) := by
  rcases exists_root_left h hm1 with ⟨x, hx, hzero⟩
  have hmono : StrictMonoOn (f h) (Set.Iic (-1)) :=
    strictMonoOn_of_deriv_pos (D := Set.Iic (-1 : ℝ)) (convex_Iic (-1))
      (continuous_f h).continuousOn (by
        intro y hy
        rw [interior_Iic] at hy
        exact deriv_pos_left h y hy)
  refine ⟨x, hx, hzero, ?_⟩
  intro y hy hyzero
  exact hmono.injOn (x₁ := y) (x₂ := x)
    (show y ≤ -1 from hy.le) (show x ≤ -1 from hx.le) (hyzero.trans hzero.symm)

private lemma unique_root_middle (h : ℝ) (hm1 : 0 < f h (-1)) (h3 : f h 3 < 0) :
    UniqueRootOn (f h) (Set.Ioo (-1) 3) := by
  rcases exists_root_middle h hm1 h3 with ⟨x, hx, hzero⟩
  have hmono : StrictAntiOn (f h) (Set.Icc (-1) 3) :=
    strictAntiOn_of_deriv_neg (D := Set.Icc (-1 : ℝ) 3) (convex_Icc (-1) 3)
      (continuous_f h).continuousOn (by
        intro y hy
        rw [interior_Icc] at hy
        exact deriv_neg_middle h y hy)
  refine ⟨x, hx, hzero, ?_⟩
  intro y hy hyzero
  exact hmono.injOn (x₁ := y) (x₂ := x)
    ⟨hy.1.le, hy.2.le⟩ ⟨hx.1.le, hx.2.le⟩
    (hyzero.trans hzero.symm)

theorem gap1 (h x : ℝ) :
    deriv (f h) x = 3 * x ^ 2 - 6 * x - 9 := by
  exact deriv_f h x

theorem gap2 (h x : ℝ) (hzero : deriv (f h) x = 0) :
    x = -1 ∨ x = 3 := by
  rw [gap1] at hzero
  have hfac : 3 * (x + 1) * (x - 3) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfac with hfac | hfac
  · rcases mul_eq_zero.mp hfac with hthree | hleft
    · norm_num at hthree
    · left
      linarith
  · right
    linarith

theorem gap3 (h : ℝ) :
    f h (-1) = 5 + h := by
  norm_num [f]

theorem gap4 (h : ℝ) :
    f h 3 = -27 + h := by
  norm_num [f]

theorem gap5 (h : ℝ) :
    Tendsto (f h) atBot atBot := by
  exact tendsto_f_atBot h

theorem gap6 (h : ℝ) :
    Tendsto (f h) atTop atTop := by
  exact tendsto_f_atTop h

theorem gap7 (h x : ℝ) (hx : x < -1) :
    deriv (f h) x > 0 := by
  exact deriv_pos_left h x hx

theorem gap8 (h x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 3) :
    deriv (f h) x < 0 := by
  exact deriv_neg_middle h x hx

theorem gap9 (h x : ℝ) (hx : 3 < x) :
    deriv (f h) x > 0 := by
  exact deriv_pos_right h x hx

theorem gap10 (h : ℝ) (hh : h < -5) :
    f h (-1) < 0 := by
  rw [gap3]
  linarith

theorem gap11 (h : ℝ) (hh : h < -5) :
    f h 3 < 0 := by
  rw [gap4]
  linarith

theorem gap12 (h : ℝ) (hh : h < -5) :
    UniqueRootOn (f h) (Set.Ioi 3) := by
  exact unique_root_right h (gap11 h hh)

theorem gap13 (h : ℝ) (hl : -5 < h) (hu : h < 27) :
    f h (-1) > 0 := by
  rw [gap3]
  linarith

theorem gap14 (h : ℝ) (hl : -5 < h) (hu : h < 27) :
    f h 3 < 0 := by
  rw [gap4]
  linarith

theorem gap15 (h : ℝ) (hl : -5 < h) (hu : h < 27) :
    UniqueRootOn (f h) (Set.Iio (-1)) := by
  exact unique_root_left h (gap13 h hl hu)

theorem gap16 (h : ℝ) (hl : -5 < h) (hu : h < 27) :
    UniqueRootOn (f h) (Set.Ioo (-1) 3) := by
  exact unique_root_middle h (gap13 h hl hu) (gap14 h hl hu)

theorem gap17 (h : ℝ) (hl : -5 < h) (hu : h < 27) :
    UniqueRootOn (f h) (Set.Ioi 3) := by
  exact unique_root_right h (gap14 h hl hu)

theorem gap18 (h : ℝ) (hh : 27 < h) :
    f h 3 > 0 := by
  rw [gap4]
  linarith

theorem gap19 (h : ℝ) (hh : 27 < h) :
    f h (-1) > 0 := by
  rw [gap3]
  linarith

theorem gap20 (h : ℝ) (hh : 27 < h) :
    UniqueRootOn (f h) (Set.Iio (-1)) := by
  exact unique_root_left h (gap19 h hh)

theorem gap21 (h x : ℝ) :
    x ∈ {y : ℝ | f h y = 0} ↔
      x ^ 3 - 3 * x ^ 2 - 9 * x + h = 0 := by
  rfl

end

end ProofGap.Exercise1463
