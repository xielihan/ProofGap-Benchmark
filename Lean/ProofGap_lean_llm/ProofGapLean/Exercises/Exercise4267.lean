import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4267

noncomputable section

open scoped Interval

abbrev Point := ℝ × ℝ

def P (x y : ℝ) : ℝ :=
  -y / (x - y) ^ 2

def Q (x y : ℝ) : ℝ :=
  x / (x - y) ^ 2

def field (z : Point) : Point :=
  (P z.1 z.2, Q z.1 z.2)

def potential (z : Point) : ℝ :=
  z.2 / (z.1 - z.2)

def InDomain (z : Point) : Prop :=
  z.1 > z.2

def HasCoordinateGradientAt
    (U : Point → ℝ) (V : Point) (z : Point) : Prop :=
  HasDerivAt (fun x => U (x, z.2)) V.1 z.1 ∧
    HasDerivAt (fun y => U (z.1, y)) V.2 z.2

def coordinateDifferential (V v : Point) : ℝ :=
  V.1 * v.1 + V.2 * v.2

def differential (U : Point → ℝ) (z v : Point) : ℝ :=
  deriv (fun x => U (x, z.2)) z.1 * v.1 +
    deriv (fun y => U (z.1, y)) z.2 * v.2

def decomposedDifferential (z v : Point) : ℝ :=
  (z.1 - z.2) / (z.1 - z.2) ^ 2 * v.2 -
    z.2 / (z.1 - z.2) ^ 2 * (v.1 - v.2)

def AdmissiblePath (γ : ℝ → Point) (start finish : Point) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = start ∧ γ 1 = finish ∧
    ∀ t, t ∈ Set.Icc (0 : ℝ) 1 → InDomain (γ t)

def lineIntegral (γ : ℝ → Point) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    P (γ t).1 (γ t).2 * deriv (fun s => (γ s).1) t +
      Q (γ t).1 (γ t).2 * deriv (fun s => (γ s).2) t

def brokenPathIntegral : ℝ :=
  (∫ x in (0 : ℝ)..1, 1 / (x + 1) ^ 2) +
    ∫ y in (-1 : ℝ)..0, 1 / (1 - y) ^ 2

private theorem hasDerivAt_P_formula (x y : ℝ) (hxy : x > y) :
    HasDerivAt (fun t => P x t) (-(x + y) / (x - y) ^ 3) y := by
  have hne : x - y ≠ 0 := ne_of_gt (sub_pos.mpr hxy)
  have hd : HasDerivAt (fun t : ℝ => x - t) (-1) y := by
    simpa using (hasDerivAt_const y x).sub (hasDerivAt_id y)
  have hn : HasDerivAt (fun t : ℝ => -t) (-1) y := by
    simpa using (hasDerivAt_id y).neg
  have h := hn.div (hd.mul hd) (mul_ne_zero hne hne)
  have hfun :
      ((fun t : ℝ => -t) /
        ((fun t : ℝ => x - t) * (fun t : ℝ => x - t))) =
        (fun t : ℝ => P x t) := by
    funext t
    simp [P, pow_two]
  rw [hfun] at h
  convert h using 1 <;> simp <;> field_simp [hne] <;> ring_nf

private theorem hasDerivAt_Q_formula (x y : ℝ) (hxy : x > y) :
    HasDerivAt (fun s => Q s y) (-(x + y) / (x - y) ^ 3) x := by
  have hne : x - y ≠ 0 := ne_of_gt (sub_pos.mpr hxy)
  have hn : HasDerivAt (fun s : ℝ => s) 1 x :=
    hasDerivAt_id x
  have hd : HasDerivAt (fun s : ℝ => s - y) 1 x :=
    hn.sub_const y
  have h := hn.div (hd.mul hd) (mul_ne_zero hne hne)
  have hfun :
      ((fun s : ℝ => s) /
        ((fun s : ℝ => s - y) * (fun s : ℝ => s - y))) =
        (fun s : ℝ => Q s y) := by
    funext s
    simp [Q, pow_two]
  rw [hfun] at h
  convert h using 1 <;> simp <;> field_simp [hne] <;> ring_nf

private theorem potential_coordinate_gradient (z : Point) (hz : InDomain z) :
    HasCoordinateGradientAt potential (field z) z := by
  rcases z with ⟨x, y⟩
  have hne : x - y ≠ 0 := ne_of_gt (sub_pos.mpr hz)
  constructor
  · have h :=
      (hasDerivAt_const x y).div
        ((hasDerivAt_id x).sub (hasDerivAt_const x y)) hne
    convert h using 1 <;> simp [potential, field, P] <;>
      field_simp [hne] <;> ring
  · have h :=
      (hasDerivAt_id y).div
        ((hasDerivAt_const y x).sub (hasDerivAt_id y)) hne
    convert h using 1 <;> simp [potential, field, Q] <;>
      field_simp [hne] <;> ring

private theorem potential_along_path_hasDerivAt
    (γ : ℝ → Point) (t : ℝ) (hγ : DifferentiableAt ℝ γ t)
    (ht : InDomain (γ t)) :
    HasDerivAt (fun s => potential (γ s))
      (P (γ t).1 (γ t).2 * deriv (fun s => (γ s).1) t +
        Q (γ t).1 (γ t).2 * deriv (fun s => (γ s).2) t) t := by
  have hx : HasDerivAt (fun s => (γ s).1)
      (deriv (fun s => (γ s).1) t) t := hγ.fst.hasDerivAt
  have hy : HasDerivAt (fun s => (γ s).2)
      (deriv (fun s => (γ s).2) t) t := hγ.snd.hasDerivAt
  have hne : (γ t).1 - (γ t).2 ≠ 0 :=
    ne_of_gt (sub_pos.mpr ht)
  have h := hy.div (hx.sub hy) hne
  convert h using 1 <;> simp [potential, P, Q] <;>
    field_simp [hne] <;> ring

private theorem lineIntegral_eq_endpoint_potential
    (γ : ℝ → Point) (start finish : Point)
    (hγ : AdmissiblePath γ start finish) :
    lineIntegral γ = potential finish - potential start := by
  rcases hγ with ⟨hc, hstart, hfinish, hdomain⟩
  have hu : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 :=
    Set.uIcc_of_le (by norm_num)
  have hcont : Continuous γ := hc.continuous
  have hcx : Continuous (fun t => (γ t).1) := hcont.fst
  have hcy : Continuous (fun t => (γ t).2) := hcont.snd
  have hdx : Continuous (fun t => deriv (fun s => (γ s).1) t) := by
    simpa only [deriv] using
      (hc.fst.continuous_fderiv (by norm_num)).clm_apply
        (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
  have hdy : Continuous (fun t => deriv (fun s => (γ s).2) t) := by
    simpa only [deriv] using
      (hc.snd.continuous_fderiv (by norm_num)).clm_apply
        (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
  have hp : ContinuousOn (fun t => P (γ t).1 (γ t).2) (Set.Icc (0 : ℝ) 1) := by
    have hp' := hcy.continuousOn.neg.div
      ((hcx.continuousOn.sub hcy.continuousOn).pow 2)
      (by
        intro t ht
        exact pow_ne_zero 2
          (ne_of_gt (sub_pos.mpr (hdomain t ht))))
    simpa only [P] using hp'
  have hq : ContinuousOn (fun t => Q (γ t).1 (γ t).2) (Set.Icc (0 : ℝ) 1) := by
    have hq' := hcx.continuousOn.div
      ((hcx.continuousOn.sub hcy.continuousOn).pow 2)
      (by
        intro t ht
        exact pow_ne_zero 2
          (ne_of_gt (sub_pos.mpr (hdomain t ht))))
    simpa only [Q] using hq'
  have hint : ContinuousOn
      (fun t =>
        P (γ t).1 (γ t).2 * deriv (fun s => (γ s).1) t +
          Q (γ t).1 (γ t).2 * deriv (fun s => (γ s).2) t)
      (Set.uIcc (0 : ℝ) 1) := by
    rw [hu]
    exact (hp.mul hdx.continuousOn).add (hq.mul hdy.continuousOn)
  have hdiff : Differentiable ℝ γ := hc.differentiable (by norm_num)
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => potential (γ s))
        (P (γ t).1 (γ t).2 * deriv (fun s => (γ s).1) t +
          Q (γ t).1 (γ t).2 * deriv (fun s => (γ s).2) t) t := by
    intro t ht
    apply potential_along_path_hasDerivAt γ t (hdiff t)
    apply hdomain t
    rw [← hu]
    exact ht
  have hi :
      (∫ t in (0 : ℝ)..1,
        P (γ t).1 (γ t).2 * deriv (fun s => (γ s).1) t +
          Q (γ t).1 (γ t).2 * deriv (fun s => (γ s).2) t) =
        potential (γ 1) - potential (γ 0) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      hderiv hint.intervalIntegrable
  simpa [lineIntegral, hstart, hfinish] using hi

private theorem brokenPathIntegral_value :
    brokenPathIntegral = (1 : ℝ) / 2 + 1 / 2 := by
  have hu1 : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 :=
    Set.uIcc_of_le (by norm_num)
  have hu2 : Set.uIcc (-1 : ℝ) 0 = Set.Icc (-1) 0 :=
    Set.uIcc_of_le (by norm_num)
  have hc1 : ContinuousOn (fun x : ℝ => 1 / (x + 1) ^ 2)
      (Set.uIcc (0 : ℝ) 1) := by
    rw [hu1]
    apply ContinuousOn.div
    · exact continuousOn_const
    · exact ((continuous_id.add continuous_const).pow 2).continuousOn
    · intro x hx
      exact pow_ne_zero 2 (by linarith [hx.1])
  have hd1 : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ => (-1) / (x + 1)) (1 / (x + 1) ^ 2) x := by
    intro x hx
    rw [hu1] at hx
    have hne : x + 1 ≠ 0 := by linarith [hx.1]
    have h := (hasDerivAt_const x (-1 : ℝ)).div
      ((hasDerivAt_id x).add_const 1) hne
    convert h using 1 <;> norm_num <;> field_simp [hne] <;> ring
  have hi1 :
      (∫ x in (0 : ℝ)..1, 1 / (x + 1) ^ 2) =
        ((fun x : ℝ => (-1) / (x + 1)) 1 -
          (fun x : ℝ => (-1) / (x + 1)) 0) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      hd1 hc1.intervalIntegrable
  have hc2 : ContinuousOn (fun y : ℝ => 1 / (1 - y) ^ 2)
      (Set.uIcc (-1 : ℝ) 0) := by
    rw [hu2]
    apply ContinuousOn.div
    · exact continuousOn_const
    · exact ((continuous_const.sub continuous_id).pow 2).continuousOn
    · intro y hy
      exact pow_ne_zero 2 (by linarith [hy.2])
  have hd2 : ∀ y ∈ Set.uIcc (-1 : ℝ) 0,
      HasDerivAt (fun y : ℝ => 1 / (1 - y)) (1 / (1 - y) ^ 2) y := by
    intro y hy
    rw [hu2] at hy
    have hne : 1 - y ≠ 0 := by linarith [hy.2]
    have h := (hasDerivAt_const y (1 : ℝ)).div
      ((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)) hne
    convert h using 1 <;> norm_num <;> field_simp [hne] <;> ring
  have hi2 :
      (∫ y in (-1 : ℝ)..0, 1 / (1 - y) ^ 2) =
        ((fun y : ℝ => 1 / (1 - y)) 0 -
          (fun y : ℝ => 1 / (1 - y)) (-1)) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      hd2 hc2.intervalIntegrable
  unfold brokenPathIntegral
  rw [hi1, hi2]
  norm_num

theorem gap1 (x y : ℝ) (hxy : x > y) :
    deriv (fun s => Q s y) x = deriv (fun t => P x t) y := by
  calc
    deriv (fun s => Q s y) x = -(x + y) / (x - y) ^ 3 :=
      (hasDerivAt_Q_formula x y hxy).deriv
    _ = deriv (fun t => P x t) y :=
      ((hasDerivAt_P_formula x y hxy).deriv).symm

theorem gap2 (x y : ℝ) (hxy : x > y) :
    HasDerivAt (fun t => P x t) (-(x + y) / (x - y) ^ 3) y := by
  exact hasDerivAt_P_formula x y hxy

theorem gap3 (x y : ℝ) (hxy : x > y) :
    HasDerivAt (fun s => Q s y) (-(x + y) / (x - y) ^ 3) x := by
  exact hasDerivAt_Q_formula x y hxy

theorem gap4 :
    ∃ U : Point → ℝ, ∀ z, InDomain z →
      HasCoordinateGradientAt U (field z) z := by
  refine ⟨potential, ?_⟩
  intro z hz
  exact potential_coordinate_gradient z hz

theorem gap5 (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (0, -1) (1, 0)) :
    lineIntegral γ = brokenPathIntegral := by
  calc
    lineIntegral γ = potential (1, 0) - potential (0, -1) :=
      lineIntegral_eq_endpoint_potential γ (0, -1) (1, 0) hγ
    _ = 1 := by norm_num [potential]
    _ = brokenPathIntegral := by
      rw [brokenPathIntegral_value]
      norm_num

theorem gap6 :
    brokenPathIntegral = (1 : ℝ) / 2 + 1 / 2 := by
  exact brokenPathIntegral_value

theorem gap7 :
    (1 : ℝ) / 2 + 1 / 2 = 1 := by
  norm_num

theorem gap8 (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (0, -1) (1, 0)) :
    lineIntegral γ = 1 := by
  calc
    lineIntegral γ = brokenPathIntegral := gap5 γ hγ
    _ = (1 : ℝ) / 2 + 1 / 2 := gap6
    _ = 1 := gap7

theorem gap9 (z v : Point) (hz : InDomain z) :
    coordinateDifferential (field z) v = decomposedDifferential z v := by
  rcases z with ⟨x, y⟩
  rcases v with ⟨u, w⟩
  have hne : x - y ≠ 0 := ne_of_gt (sub_pos.mpr hz)
  simp only [coordinateDifferential, field, P, Q,
    decomposedDifferential]
  field_simp [hne]
  ring

theorem gap10 (z v : Point) (hz : InDomain z) :
    decomposedDifferential z v = differential potential z v := by
  have hg := potential_coordinate_gradient z hz
  rcases hg with ⟨hx, hy⟩
  rw [differential, hx.deriv, hy.deriv]
  simpa [coordinateDifferential] using (gap9 z v hz).symm

theorem gap11 (z v : Point) (hz : InDomain z) :
    coordinateDifferential (field z) v = differential potential z v := by
  exact (gap9 z v hz).trans (gap10 z v hz)

theorem gap12 (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (0, -1) (1, 0)) :
    lineIntegral γ = potential (1, 0) - potential (0, -1) := by
  exact lineIntegral_eq_endpoint_potential γ (0, -1) (1, 0) hγ

theorem gap13 :
    potential (1, 0) - potential (0, -1) = 1 := by
  norm_num [potential]

theorem gap14 (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (0, -1) (1, 0)) :
    lineIntegral γ = 1 := by
  calc
    lineIntegral γ = potential (1, 0) - potential (0, -1) := gap12 γ hγ
    _ = 1 := gap13

end

end ProofGap.Exercise4267
