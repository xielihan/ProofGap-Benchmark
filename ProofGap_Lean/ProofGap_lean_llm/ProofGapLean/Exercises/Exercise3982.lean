import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3982

noncomputable section

open MeasureTheory
open scoped Interval

def solution (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  1 / 2 *
    ∫ xi in (0 : ℝ)..x,
      ∫ eta in xi - x + y..x + y - xi, f xi eta

def partialX (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun z => u z y) x

def partialY (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun z => u x z) y

def partialXX (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun z => partialX u z y) x

def partialYY (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun z => partialY u x z) y

def partial₂ (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun z => f x z) y

private theorem hasDerivAt_interval_integral_compact
    {F F' : ℝ → ℝ → ℝ}
    (hF : Continuous F.uncurry)
    (hF' : Continuous F'.uncurry)
    (hd : ∀ s t, HasDerivAt (fun u => F u t) (F' s t) s)
    (a b x : ℝ) :
    HasDerivAt (fun s => ∫ t in a..b, F s t)
      (∫ t in a..b, F' x t) x := by
  let J : Set ℝ := Set.Icc (x - 1) (x + 1)
  have hJ : IsCompact J := isCompact_Icc
  have hK : IsCompact (Set.uIcc a b) := isCompact_uIcc
  obtain ⟨M, hM⟩ :=
    (hJ.prod hK).bddAbove_image hF'.norm.continuousOn
  have hJ_mem : J ∈ nhds x := by
    exact Icc_mem_nhds (sub_lt_self x zero_lt_one)
      (lt_add_of_pos_right x zero_lt_one)
  have hFi : IntervalIntegrable (F x) volume a b :=
    (hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hF'i :
      AEStronglyMeasurable (F' x) (volume.restrict (Ι a b)) :=
    (hF'.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hMi :
      IntervalIntegrable (fun _ : ℝ => M) volume a b :=
    continuous_const.intervalIntegrable _ _
  refine
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (bound := fun _ => M)
      hJ_mem ?_ hFi hF'i ?_ hMi ?_).2
  · filter_upwards with s
    exact
      (hF.comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards with t ht s hs
    exact hM ⟨(s, t), ⟨hs, Set.uIoc_subset_uIcc ht⟩, rfl⟩
  · filter_upwards with t ht s hs
    exact hd s t

private lemma inner_hasDerivAt_x
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (xi x y : ℝ) :
    HasDerivAt
      (fun z => ∫ eta in xi - z + y..z + y - xi, f xi eta)
      (f xi (x + y - xi) + f xi (xi - x + y)) x := by
  have hcont : Continuous (fun eta => f xi eta) :=
    hf.comp (continuous_const.prodMk continuous_id)
  have hupper : HasDerivAt (fun z => z + y - xi) 1 x := by
    convert (hasDerivAt_id x).add_const y |>.sub_const xi using 1 <;> ring
  have hlower : HasDerivAt (fun z => xi - z + y) (-1) x := by
    convert (hasDerivAt_const x xi).sub (hasDerivAt_id x) |>.add_const y using 1 <;> ring
  have hu :=
    (hcont.integral_hasStrictDerivAt 0 (x + y - xi)).hasDerivAt.comp x hupper
  have hl :=
    (hcont.integral_hasStrictDerivAt 0 (xi - x + y)).hasDerivAt.comp x hlower
  have h := hu.sub hl
  convert h using 1
  · funext z
    simpa [Function.comp_def] using
      (intervalIntegral.integral_interval_sub_left (μ := volume)
        (a := 0) (b := z + y - xi) (c := xi - z + y)
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  · ring

private lemma inner_hasDerivAt_y
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (xi x y : ℝ) :
    HasDerivAt
      (fun z => ∫ eta in xi - x + z..x + z - xi, f xi eta)
      (f xi (x + y - xi) - f xi (xi - x + y)) y := by
  have hcont : Continuous (fun eta => f xi eta) :=
    hf.comp (continuous_const.prodMk continuous_id)
  have hupper : HasDerivAt (fun z => x + z - xi) 1 y := by
    convert (hasDerivAt_const y x).add (hasDerivAt_id y) |>.sub_const xi using 1 <;> ring
  have hlower : HasDerivAt (fun z => xi - x + z) 1 y := by
    convert (hasDerivAt_const y (xi - x)).add (hasDerivAt_id y) using 1 <;> ring
  have hu :=
    (hcont.integral_hasStrictDerivAt 0 (x + y - xi)).hasDerivAt.comp y hupper
  have hl :=
    (hcont.integral_hasStrictDerivAt 0 (xi - x + y)).hasDerivAt.comp y hlower
  have h := hu.sub hl
  convert h using 1
  · funext z
    simpa [Function.comp_def] using
      (intervalIntegral.integral_interval_sub_left (μ := volume)
        (a := 0) (b := x + z - xi) (c := xi - x + z)
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  · ring

private lemma interval_integral_affine
    (g : ℝ → ℝ) (hg : Continuous g) (a b : ℝ) :
    (∫ eta in a..b, g eta) =
      ∫ t in (0 : ℝ)..1, g (a + (b - a) * t) * (b - a) := by
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun u : ℝ => a + (b - a) * u) (b - a) t := by
    intro t ht
    convert (hasDerivAt_const t a).add
      ((hasDerivAt_const t (b - a)).mul (hasDerivAt_id t)) using 1 <;> ring
  simpa [Function.comp_def] using
    (intervalIntegral.integral_comp_mul_deriv
      (a := (0 : ℝ)) (b := 1)
      (f := fun t : ℝ => a + (b - a) * t)
      (f' := fun _ : ℝ => b - a) (g := g)
      hderiv continuous_const.continuousOn hg).symm

private lemma continuous_inner_x
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (y : ℝ) :
    Continuous
      (Function.uncurry fun z xi =>
        ∫ eta in xi - z + y..z + y - xi, f xi eta) := by
  let Q : (ℝ × ℝ) → ℝ → ℝ := fun p t =>
    f p.2
      ((p.2 - p.1 + y) +
        ((p.1 + y - p.2) - (p.2 - p.1 + y)) * t) *
      ((p.1 + y - p.2) - (p.2 - p.1 + y))
  have hQ : Continuous Q.uncurry := by
    dsimp [Q, Function.uncurry]
    fun_prop
  have hI :
      Continuous (fun p : ℝ × ℝ =>
        ∫ t in (0 : ℝ)..1, Q p t) := by
    have hset :
        Continuous (fun p : ℝ × ℝ =>
          ∫ t in Set.Icc (0 : ℝ) 1, Q p t) :=
      continuous_parametric_integral_of_continuous hQ isCompact_Icc
    simpa [intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc] using hset
  apply hI.congr
  intro p
  dsimp [Q, Function.uncurry]
  exact (interval_integral_affine
    (fun eta => f p.2 eta)
    (hf.comp (continuous_const.prodMk continuous_id))
    (p.2 - p.1 + y) (p.1 + y - p.2)).symm

private lemma continuous_inner_y
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (x : ℝ) :
    Continuous
      (Function.uncurry fun y xi =>
        ∫ eta in xi - x + y..x + y - xi, f xi eta) := by
  let Q : (ℝ × ℝ) → ℝ → ℝ := fun p t =>
    f p.2
      ((p.2 - x + p.1) +
        ((x + p.1 - p.2) - (p.2 - x + p.1)) * t) *
      ((x + p.1 - p.2) - (p.2 - x + p.1))
  have hQ : Continuous Q.uncurry := by
    dsimp [Q, Function.uncurry]
    fun_prop
  have hI :
      Continuous (fun p : ℝ × ℝ =>
        ∫ t in (0 : ℝ)..1, Q p t) := by
    have hset :
        Continuous (fun p : ℝ × ℝ =>
          ∫ t in Set.Icc (0 : ℝ) 1, Q p t) :=
      continuous_parametric_integral_of_continuous hQ isCompact_Icc
    simpa [intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc] using hset
  apply hI.congr
  intro p
  dsimp [Q, Function.uncurry]
  exact (interval_integral_affine
    (fun eta => f p.2 eta)
    (hf.comp (continuous_const.prodMk continuous_id))
    (p.2 - x + p.1) (x + p.1 - p.2)).symm

private theorem moving_right_hasDerivAt_compact
    {F F' : ℝ → ℝ → ℝ}
    (hF : Continuous F.uncurry)
    (hF' : Continuous F'.uncurry)
    (hd : ∀ s t, HasDerivAt (fun u => F u t) (F' s t) s)
    (a x : ℝ) :
    HasDerivAt (fun s => ∫ t in a..s, F s t)
      ((∫ t in a..x, F' x t) + F x x) x := by
  have hfixed :
      HasDerivAt (fun s => ∫ t in a..x, F s t)
        (∫ t in a..x, F' x t) x :=
    hasDerivAt_interval_integral_compact hF hF' hd a x x
  have hFx : Continuous (F x) :=
    hF.comp (continuous_const.prodMk continuous_id)
  let R : ℝ → ℝ :=
    fun s => ∫ t in x..s, F s t - F x t
  have hrem : HasDerivAt R 0 x := by
    let J : Set ℝ := Set.Icc (x - 1) (x + 1)
    have hJ : IsCompact J := isCompact_Icc
    obtain ⟨M, hM⟩ :=
      (hJ.prod hJ).bddAbove_image hF'.norm.continuousOn
    have hxJ : x ∈ J := by
      constructor <;> dsimp [J] <;> linarith
    have hM0 : 0 ≤ M := by
      exact (norm_nonneg (F' x x)).trans
        (hM ⟨(x, x), ⟨hxJ, hxJ⟩, rfl⟩)
    have hLip :
        ∀ s ∈ J, ∀ t ∈ J,
          ‖F s t - F x t‖ ≤ M * ‖s - x‖ := by
      intro s hs t ht
      exact Convex.norm_image_sub_le_of_norm_deriv_le
        (s := J) (f := fun q => F q t)
        (fun q hq => (hd q t).differentiableAt)
        (fun q hq => by
          rw [(hd q t).deriv]
          exact hM ⟨(q, t), ⟨hq, ht⟩, rfl⟩)
        (convex_Icc _ _) hxJ hs
    rw [hasDerivAt_iff_tendsto]
    have hupper :
        Filter.Tendsto (fun s : ℝ => M * |s - x|)
          (nhds x) (nhds 0) := by
      have hc : ContinuousAt (fun s : ℝ => M * |s - x|) x := by
        fun_prop
      change Filter.Tendsto (fun s : ℝ => M * |s - x|)
        (nhds x) (nhds (M * |x - x|)) at hc
      simpa only [sub_self, abs_zero, mul_zero] using hc
    have hRx : R x = 0 := by simp [R]
    refine squeeze_zero'
      (Filter.Eventually.of_forall fun s =>
        mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
      ?_ hupper
    filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have hsJ : s ∈ J := by
      constructor <;> dsimp [J] <;>
        linarith [le_abs_self (s - x), neg_le_abs (s - x)]
    have hinterval : Set.uIcc x s ⊆ J :=
      Set.ordConnected_Icc.uIcc_subset hxJ hsJ
    have hR :
        ‖R s‖ ≤ (M * ‖s - x‖) * |s - x| := by
      unfold R
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      exact hLip s hsJ t (hinterval (Set.uIoc_subset_uIcc ht))
    rw [hRx]
    simp only [sub_zero, smul_zero]
    by_cases hsx : s = x
    · subst s
      simp
    · have habs : 0 < |s - x| :=
        abs_pos.mpr (sub_ne_zero.mpr hsx)
      rw [Real.norm_eq_abs] at hR ⊢
      calc
        |s - x|⁻¹ * ‖∫ t in x..s, F s t - F x t‖ ≤
            |s - x|⁻¹ * ((M * |s - x|) * |s - x|) :=
          mul_le_mul_of_nonneg_left hR
            (inv_nonneg.mpr (abs_nonneg _))
        _ = M * |s - x| := by
          field_simp [habs.ne']
  let B : ℝ → ℝ := fun s => ∫ t in x..s, F x t
  have hbase : HasDerivAt B (F x x) x := by
    dsimp [B]
    exact (hFx.integral_hasStrictDerivAt x x).hasDerivAt
  have hcorrection :
      HasDerivAt (fun s => ∫ t in x..s, F s t) (F x x) x := by
    have heq :
        (fun s => ∫ t in x..s, F s t) =
          fun s => B s + R s := by
      funext s
      dsimp [B, R]
      have hFs : Continuous (F s) :=
        hF.comp (continuous_const.prodMk continuous_id)
      rw [← intervalIntegral.integral_add
        (hFx.intervalIntegrable _ _)
        (hFs.sub hFx
          |>.intervalIntegrable _ _)]
      congr 1
      funext t
      ring
    rw [heq]
    convert hbase.add hrem using 1 <;> ring
  have heq :
      (fun s => ∫ t in a..s, F s t) =
        fun s => (∫ t in a..x, F s t) +
          ∫ t in x..s, F s t := by
    funext s
    exact (intervalIntegral.integral_add_adjacent_intervals
      ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
      ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)).symm
  rw [heq]
  exact hfixed.add hcorrection

theorem gap1 (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2)) (x y : ℝ) :
    partialX (solution f) x y =
      1 / 2 *
          (∫ xi in (0 : ℝ)..x,
            f xi (x + y - xi) + f xi (xi - x + y)) +
        1 / 2 * ∫ eta in x - x + y..x + y - x, f x eta := by
  unfold partialX solution
  have hF :
      Continuous
        (Function.uncurry fun z xi =>
          ∫ eta in xi - z + y..z + y - xi, f xi eta) :=
    continuous_inner_x f hf y
  have hF' :
      Continuous
        (Function.uncurry fun z xi =>
          f xi (z + y - xi) + f xi (xi - z + y)) := by
    dsimp [Function.uncurry]
    fun_prop
  have hd :
      ∀ z xi,
        HasDerivAt
          (fun u => ∫ eta in xi - u + y..u + y - xi, f xi eta)
          (f xi (z + y - xi) + f xi (xi - z + y)) z :=
    fun z xi => inner_hasDerivAt_x f hf xi z y
  have houter :=
    moving_right_hasDerivAt_compact hF hF' hd 0 x
  apply HasDerivAt.deriv
  convert houter.const_mul (1 / 2) using 1 <;> ring

theorem gap2 (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2)) (x y : ℝ) :
    1 / 2 *
          (∫ xi in (0 : ℝ)..x,
            f xi (x + y - xi) + f xi (xi - x + y)) +
        1 / 2 * (∫ eta in x - x + y..x + y - x, f x eta) =
      1 / 2 *
        ∫ xi in (0 : ℝ)..x,
          f xi (x + y - xi) + f xi (xi - x + y) := by
  have h₁ : x - x + y = y := by ring
  have h₂ : x + y - x = y := by ring
  rw [h₁, h₂]
  simp

theorem gap3 (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2)) (x y : ℝ) :
    partialX (solution f) x y =
      1 / 2 *
        ∫ xi in (0 : ℝ)..x,
          f xi (x + y - xi) + f xi (xi - x + y) := by
  calc
    partialX (solution f) x y =
        1 / 2 *
            (∫ xi in (0 : ℝ)..x,
              f xi (x + y - xi) + f xi (xi - x + y)) +
          1 / 2 * ∫ eta in x - x + y..x + y - x, f x eta :=
      gap1 f hf x y
    _ = 1 / 2 *
          ∫ xi in (0 : ℝ)..x,
            f xi (x + y - xi) + f xi (xi - x + y) :=
      gap2 f hf x y

theorem gap7 (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2)) (x y : ℝ) :
    partialY (solution f) x y =
      1 / 2 *
        ∫ xi in (0 : ℝ)..x,
          f xi (x + y - xi) - f xi (xi - x + y) := by
  unfold partialY solution
  have hF :
      Continuous
        (Function.uncurry fun z xi =>
          ∫ eta in xi - x + z..x + z - xi, f xi eta) :=
    continuous_inner_y f hf x
  have hF' :
      Continuous
        (Function.uncurry fun z xi =>
          f xi (x + z - xi) - f xi (xi - x + z)) := by
    dsimp [Function.uncurry]
    fun_prop
  have hd :
      ∀ z xi,
        HasDerivAt
          (fun u => ∫ eta in xi - x + u..x + u - xi, f xi eta)
          (f xi (x + z - xi) - f xi (xi - x + z)) z :=
    fun z xi => inner_hasDerivAt_y f hf xi x z
  have houter :=
    hasDerivAt_interval_integral_compact hF hF' hd 0 x y
  apply HasDerivAt.deriv
  convert houter.const_mul (1 / 2) using 1 <;> ring

private lemma partial₂_eq_fderiv
    (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    partial₂ f x y =
      fderiv ℝ (Function.uncurry f) (x, y) (0, 1) := by
  unfold partial₂
  have hp : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  have h := (hf.hasFDerivAt.comp y hp.hasFDerivAt).hasDerivAt.deriv
  simpa [Function.uncurry] using h

private lemma continuous_partial₂
    (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 1 (fun p : ℝ × ℝ => f p.1 p.2)) :
    Continuous (fun p : ℝ × ℝ => partial₂ f p.1 p.2) := by
  have hfd :
      Continuous (fun p : ℝ × ℝ =>
        fderiv ℝ (Function.uncurry f) p (0, 1)) := by
    have hall :=
      hf.continuous_fderiv_apply (by norm_num)
    exact hall.comp (continuous_id.prodMk continuous_const)
  apply hfd.congr
  intro p
  exact (partial₂_eq_fderiv f p.1 p.2
    (hf.differentiable (by norm_num)).differentiableAt).symm

private lemma hasDerivAt_f_second
    (f : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (fun p : ℝ × ℝ => f p.1 p.2))
    (x y : ℝ) :
    HasDerivAt (fun z => f x z) (partial₂ f x y) y := by
  have hp : HasDerivAt (fun z : ℝ => (x, z)) (0, 1) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  exact
    ((hf.differentiableAt.comp y hp.differentiableAt).hasDerivAt)

private lemma sum_hasDerivAt_x
    (f : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (fun p : ℝ × ℝ => f p.1 p.2))
    (xi x y : ℝ) :
    HasDerivAt
      (fun z => f xi (z + y - xi) + f xi (xi - z + y))
      (partial₂ f xi (x + y - xi) -
        partial₂ f xi (xi - x + y)) x := by
  have hu : HasDerivAt (fun z => z + y - xi) 1 x := by
    convert (hasDerivAt_id x).add_const y |>.sub_const xi using 1 <;> ring
  have hl : HasDerivAt (fun z => xi - z + y) (-1) x := by
    convert (hasDerivAt_const x xi).sub (hasDerivAt_id x)
      |>.add_const y using 1 <;> ring
  convert
    ((hasDerivAt_f_second f hf xi (x + y - xi)).comp x hu).add
      ((hasDerivAt_f_second f hf xi (xi - x + y)).comp x hl)
      using 1 <;> ring

private lemma difference_hasDerivAt_y
    (f : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (fun p : ℝ × ℝ => f p.1 p.2))
    (xi x y : ℝ) :
    HasDerivAt
      (fun z => f xi (x + z - xi) - f xi (xi - x + z))
      (partial₂ f xi (x + y - xi) -
        partial₂ f xi (xi - x + y)) y := by
  have hu : HasDerivAt (fun z => x + z - xi) 1 y := by
    convert (hasDerivAt_const y x).add (hasDerivAt_id y)
      |>.sub_const xi using 1 <;> ring
  have hl : HasDerivAt (fun z => xi - x + z) 1 y := by
    convert (hasDerivAt_const y (xi - x)).add
      (hasDerivAt_id y) using 1 <;> ring
  convert
    ((hasDerivAt_f_second f hf xi (x + y - xi)).comp y hu).sub
      ((hasDerivAt_f_second f hf xi (xi - x + y)).comp y hl)
      using 1 <;> ring

theorem gap4 (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 1 (fun p : ℝ × ℝ => f p.1 p.2)) (x y : ℝ) :
    partialXX (solution f) x y =
      1 / 2 *
          (∫ xi in (0 : ℝ)..x,
            partial₂ f xi (x + y - xi) -
              partial₂ f xi (xi - x + y)) +
        1 / 2 * (f x (x + y - x) + f x (x - x + y)) := by
  unfold partialXX
  have hfun :
      (fun z : ℝ => partialX (solution f) z y) =
        (fun z : ℝ =>
          1 / 2 *
            ∫ xi in (0 : ℝ)..z,
              f xi (z + y - xi) + f xi (xi - z + y)) := by
    funext z
    exact gap3 f hf.continuous z y
  rw [hfun]
  have hF :
      Continuous
        (Function.uncurry fun z xi =>
          f xi (z + y - xi) + f xi (xi - z + y)) := by
    dsimp [Function.uncurry]
    fun_prop
  have hp := continuous_partial₂ f hf
  have hF' :
      Continuous
        (Function.uncurry fun z xi =>
          partial₂ f xi (z + y - xi) -
            partial₂ f xi (xi - z + y)) := by
    dsimp [Function.uncurry]
    fun_prop
  have hdiff := hf.differentiable (by norm_num)
  have hd :
      ∀ z xi,
        HasDerivAt
          (fun u => f xi (u + y - xi) + f xi (xi - u + y))
          (partial₂ f xi (z + y - xi) -
            partial₂ f xi (xi - z + y)) z :=
    fun z xi => sum_hasDerivAt_x f hdiff xi z y
  have houter :=
    moving_right_hasDerivAt_compact hF hF' hd 0 x
  apply HasDerivAt.deriv
  convert houter.const_mul (1 / 2) using 1 <;> ring

theorem gap5 (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 1 (fun p : ℝ × ℝ => f p.1 p.2)) (x y : ℝ) :
    1 / 2 *
          (∫ xi in (0 : ℝ)..x,
            partial₂ f xi (x + y - xi) -
              partial₂ f xi (xi - x + y)) +
        1 / 2 * (f x (x + y - x) + f x (x - x + y)) =
      1 / 2 *
          (∫ xi in (0 : ℝ)..x,
            partial₂ f xi (x + y - xi) -
              partial₂ f xi (xi - x + y)) +
        f x y := by
  have h₁ : x + y - x = y := by ring
  have h₂ : x - x + y = y := by ring
  rw [h₁, h₂]
  ring

theorem gap6 (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 1 (fun p : ℝ × ℝ => f p.1 p.2)) (x y : ℝ) :
    partialXX (solution f) x y =
      1 / 2 *
          (∫ xi in (0 : ℝ)..x,
            partial₂ f xi (x + y - xi) -
              partial₂ f xi (xi - x + y)) +
        f x y := by
  calc
    partialXX (solution f) x y =
        1 / 2 *
            (∫ xi in (0 : ℝ)..x,
              partial₂ f xi (x + y - xi) -
                partial₂ f xi (xi - x + y)) +
          1 / 2 * (f x (x + y - x) + f x (x - x + y)) :=
      gap4 f hf x y
    _ = 1 / 2 *
            (∫ xi in (0 : ℝ)..x,
              partial₂ f xi (x + y - xi) -
                partial₂ f xi (xi - x + y)) +
          f x y :=
      gap5 f hf x y

theorem gap8 (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 1 (fun p : ℝ × ℝ => f p.1 p.2)) (x y : ℝ) :
    partialYY (solution f) x y =
      1 / 2 *
        ∫ xi in (0 : ℝ)..x,
          partial₂ f xi (x + y - xi) -
            partial₂ f xi (xi - x + y) := by
  unfold partialYY
  have hfun :
      (fun z : ℝ => partialY (solution f) x z) =
        (fun z : ℝ =>
          1 / 2 *
            ∫ xi in (0 : ℝ)..x,
              f xi (x + z - xi) - f xi (xi - x + z)) := by
    funext z
    exact gap7 f hf.continuous x z
  rw [hfun]
  have hF :
      Continuous
        (Function.uncurry fun z xi =>
          f xi (x + z - xi) - f xi (xi - x + z)) := by
    dsimp [Function.uncurry]
    fun_prop
  have hp := continuous_partial₂ f hf
  have hF' :
      Continuous
        (Function.uncurry fun z xi =>
          partial₂ f xi (x + z - xi) -
            partial₂ f xi (xi - x + z)) := by
    dsimp [Function.uncurry]
    fun_prop
  have hdiff := hf.differentiable (by norm_num)
  have hd :
      ∀ z xi,
        HasDerivAt
          (fun u => f xi (x + u - xi) - f xi (xi - x + u))
          (partial₂ f xi (x + z - xi) -
            partial₂ f xi (xi - x + z)) z :=
    fun z xi => difference_hasDerivAt_y f hdiff xi x z
  have houter :=
    hasDerivAt_interval_integral_compact hF hF' hd 0 x y
  apply HasDerivAt.deriv
  convert houter.const_mul (1 / 2) using 1 <;> ring

theorem gap9 (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 1 (fun p : ℝ × ℝ => f p.1 p.2)) (x y : ℝ) :
    partialXX (solution f) x y - partialYY (solution f) x y =
      f x y := by
  rw [gap6 f hf x y, gap8 f hf x y]
  ring

theorem gap10 (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 1 (fun p : ℝ × ℝ => f p.1 p.2)) (x y : ℝ) :
    partialXX (solution f) x y - partialYY (solution f) x y =
      f x y := by
  exact gap9 f hf x y

end

end ProofGap.Exercise3982
