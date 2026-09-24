import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Order.Filter.AtTopBot.Basic

namespace ProofGap.Exercise761

noncomputable section

def Iteration (ε : ℝ) (Y : ℕ → ℝ → ℝ) : Prop :=
  (∀ x, Y 0 x = x) ∧ ∀ n x, Y (n + 1) x = x + ε * Real.sin (Y n x)

def geomSum (ε : ℝ) (n : ℕ) : ℝ :=
  (Finset.range (n + 1)).sum (fun k => ε ^ k)

/-- Source: `proof_gap/exercise_761/1.txt`; represent the sequence limit by `Tendsto`. -/
theorem gap1 (ε : ℝ) (Y : ℕ → ℝ → ℝ) (y : ℝ → ℝ)
    (hlim : ∀ x, Filter.Tendsto (fun n => Y n x) Filter.atTop (nhds (y x))) :
    ∀ x, Filter.Tendsto (fun n => Y n x) Filter.atTop (nhds (y x)) := by
  exact hlim

/-- Source: `proof_gap/exercise_761/2.txt`. -/
theorem gap2 (ε x : ℝ) (Y : ℕ → ℝ → ℝ) (y : ℝ → ℝ)
    (hiter : Iteration ε Y)
    (hlim : Filter.Tendsto (fun n => Y n x) Filter.atTop (nhds (y x))) :
    y x - ε * Real.sin (y x) = x := by
  have hshift :
      Filter.Tendsto (fun n => Y (n + 1) x) Filter.atTop (nhds (y x)) :=
    hlim.comp (Filter.tendsto_add_atTop_nat 1)
  have hright :
      Filter.Tendsto (fun n => Y (n + 1) x) Filter.atTop
        (nhds (x + ε * Real.sin (y x))) := by
    have hsin :
        Filter.Tendsto (fun n => Real.sin (Y n x)) Filter.atTop
          (nhds (Real.sin (y x))) :=
      (Real.continuous_sin.tendsto (y x)).comp hlim
    have hc :
        Filter.Tendsto (fun _ : ℕ => x) Filter.atTop (nhds x) :=
      tendsto_const_nhds
    have h := hc.add (hsin.const_mul ε)
    convert h using 1
    ext n
    exact hiter.2 n x
  have heq := tendsto_nhds_unique hshift hright
  linarith

/-- Source: `proof_gap/exercise_761/3.txt`; bind the unique root rather than `existsUnique (y(x))`. -/
theorem gap3 (ε x : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    ∃! z : ℝ, z - ε * Real.sin z = x := by
  let f : ℝ → ℝ := fun z => z - ε * Real.sin z
  have hab : x - ε ≤ x + ε := by linarith
  have hcont : ContinuousOn f (Set.Icc (x - ε) (x + ε)) := by
    fun_prop
  have hxrange : x ∈ Set.Icc (f (x - ε)) (f (x + ε)) := by
    have hsinlo := Real.neg_one_le_sin (x - ε)
    have hsinhi := Real.sin_le_one (x + ε)
    dsimp [f]
    constructor <;> nlinarith
  obtain ⟨z, hzmem, hz⟩ := intermediate_value_Icc hab hcont hxrange
  refine ⟨z, by simpa [f] using hz, ?_⟩
  intro w hw
  have hz' : z - ε * Real.sin z = x := by simpa [f] using hz
  have hdiff : z - w = ε * (Real.sin z - Real.sin w) := by
    linarith
  have habs :
      |z - w| = ε * |Real.sin z - Real.sin w| := by
    calc
      |z - w| = |ε * (Real.sin z - Real.sin w)| := congrArg abs hdiff
      _ = ε * |Real.sin z - Real.sin w| := by rw [abs_mul, abs_of_nonneg hε0]
  have hsin := Real.abs_sin_sub_sin_le z w
  have hle : |z - w| ≤ ε * |z - w| := by
    calc
      |z - w| = ε * |Real.sin z - Real.sin w| := habs
      _ ≤ ε * |z - w| := mul_le_mul_of_nonneg_left hsin hε0
  have hzero : |z - w| = 0 := by
    nlinarith [abs_nonneg (z - w)]
  exact (sub_eq_zero.mp (abs_eq_zero.mp hzero)).symm

/-- Source: `proof_gap/exercise_761/4.txt`; add `n≥1` before using `n-1`. -/
theorem gap4 (ε x : ℝ) (Y : ℕ → ℝ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hiter : Iteration ε Y) :
    ∀ x₀, |Y n x - Y n x₀| =
      |x - x₀ + ε * (Real.sin (Y (n - 1) x) - Real.sin (Y (n - 1) x₀))| := by
  intro x₀
  have hYn (z : ℝ) :
      Y n z = z + ε * Real.sin (Y (n - 1) z) := by
    calc
      Y n z = Y ((n - 1) + 1) z := by rw [Nat.sub_add_cancel hn]
      _ = z + ε * Real.sin (Y (n - 1) z) := hiter.2 (n - 1) z
  rw [hYn x, hYn x₀]
  congr 1
  ring

/-- Source: `proof_gap/exercise_761/5.txt`; add `n≥1`. -/
theorem gap5 (ε x : ℝ) (Y : ℕ → ℝ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hε : 0 ≤ ε) (hiter : Iteration ε Y) :
    ∀ x₀, |Y n x - Y n x₀| ≤
      |x - x₀| + ε * |Y (n - 1) x - Y (n - 1) x₀| := by
  intro x₀
  rw [gap4 ε x Y n hn hiter x₀]
  calc
    |x - x₀ + ε * (Real.sin (Y (n - 1) x) - Real.sin (Y (n - 1) x₀))| ≤
        |x - x₀| +
          |ε * (Real.sin (Y (n - 1) x) - Real.sin (Y (n - 1) x₀))| :=
      abs_add_le _ _
    _ = |x - x₀| +
        ε * |Real.sin (Y (n - 1) x) - Real.sin (Y (n - 1) x₀)| := by
      rw [abs_mul, abs_of_nonneg hε]
    _ ≤ |x - x₀| + ε * |Y (n - 1) x - Y (n - 1) x₀| :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le _ _) hε)

/-- Source: `proof_gap/exercise_761/6.txt`; replace the ellipsis by a finite geometric sum. -/
theorem gap6 (ε x : ℝ) (Y : ℕ → ℝ → ℝ) (n : ℕ)
    (hε : 0 ≤ ε) (hiter : Iteration ε Y) :
    ∀ x₀, |Y n x - Y n x₀| ≤ |x - x₀| * geomSum ε n := by
  intro x₀
  induction n with
  | zero =>
      simp [geomSum, hiter.1]
  | succ n ih =>
      have hs := gap5 ε x Y (n + 1) (by omega) hε hiter x₀
      simp only [Nat.add_sub_cancel] at hs
      calc
        |Y (n + 1) x - Y (n + 1) x₀| ≤
            |x - x₀| + ε * |Y n x - Y n x₀| := hs
        _ ≤ |x - x₀| + ε * (|x - x₀| * geomSum ε n) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left ih hε)
        _ = |x - x₀| * geomSum ε (n + 1) := by
          simp only [geomSum, geom_sum_succ]
          ring

/-- Source: `proof_gap/exercise_761/7.txt`; correct the unsupported equality to the geometric-sum bound. -/
theorem gap7 (ε x : ℝ) (Y : ℕ → ℝ → ℝ) (n : ℕ)
    (hεne : ε ≠ 1)
    (hbound : ∀ x₀, |Y n x - Y n x₀| ≤ |x - x₀| * geomSum ε n) :
    ∀ x₀, |Y n x - Y n x₀| ≤
      |x - x₀| * ((1 - ε ^ (n + 1)) / (1 - ε)) := by
  intro x₀
  have hgeom :
      geomSum ε n = (1 - ε ^ (n + 1)) / (1 - ε) := by
    unfold geomSum
    rw [geom_sum_eq hεne]
    have hden : ε - 1 ≠ 0 := sub_ne_zero.mpr hεne
    have hden' : 1 - ε ≠ 0 := sub_ne_zero.mpr (Ne.symm hεne)
    field_simp
    ring
  simpa [hgeom] using hbound x₀

/-- Source: `proof_gap/exercise_761/8.txt`. -/
theorem gap8 (ε x x₀ : ℝ) (n : ℕ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    |x - x₀| * ((1 - ε ^ (n + 1)) / (1 - ε)) ≤
      (1 / (1 - ε)) * |x - x₀| := by
  have hden : 0 < 1 - ε := sub_pos.mpr hε1
  have hp : 0 ≤ ε ^ (n + 1) := pow_nonneg hε0 _
  have hfrac :
      (1 - ε ^ (n + 1)) / (1 - ε) ≤ 1 / (1 - ε) := by
    exact (div_le_div_iff_of_pos_right hden).2 (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hfrac (abs_nonneg (x - x₀))
  nlinarith

/-- Source: `proof_gap/exercise_761/9.txt`. -/
theorem gap9 (ε x : ℝ) (Y : ℕ → ℝ → ℝ) (n : ℕ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hbound : ∀ x₀, |Y n x - Y n x₀| ≤
      |x - x₀| * ((1 - ε ^ (n + 1)) / (1 - ε))) :
    ∀ x₀, |Y n x - Y n x₀| ≤ (1 / (1 - ε)) * |x - x₀| := by
  intro x₀
  exact (hbound x₀).trans (gap8 ε x x₀ n hε0 hε1)

/-- Source: `proof_gap/exercise_761/10.txt`; pass the uniform bound to the pointwise limit. -/
theorem gap10 (ε x : ℝ) (Y : ℕ → ℝ → ℝ) (y : ℝ → ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hlim : ∀ z, Filter.Tendsto (fun n => Y n z) Filter.atTop (nhds (y z)))
    (hbound : ∀ n x₀, |Y n x - Y n x₀| ≤ (1 / (1 - ε)) * |x - x₀|) :
    ∀ x₀, |y x - y x₀| ≤ (1 / (1 - ε)) * |x - x₀| := by
  intro x₀
  have hdiff :
      Filter.Tendsto (fun n => Y n x - Y n x₀) Filter.atTop
        (nhds (y x - y x₀)) :=
    (hlim x).sub (hlim x₀)
  apply le_of_tendsto hdiff.abs
  exact Filter.Eventually.of_forall fun n => hbound n x₀

/-- Source: `proof_gap/exercise_761/11.txt`. -/
theorem gap11 (ε : ℝ) (y : ℝ → ℝ) (hε : ε < 1)
    (hlip : ∀ x x₀, |y x - y x₀| ≤ (1 / (1 - ε)) * |x - x₀|) :
    ∀ x₀, Filter.Tendsto y (nhds x₀) (nhds (y x₀)) := by
  let K : NNReal :=
    ⟨1 / (1 - ε), one_div_nonneg.mpr (sub_nonneg.mpr (le_of_lt hε))⟩
  have hK : LipschitzWith K y :=
    LipschitzWith.of_dist_le_mul fun x x₀ => by
      simpa [K, Real.dist_eq] using hlip x x₀
  intro x₀
  exact hK.continuous.tendsto x₀

/-- Source: `proof_gap/exercise_761/12.txt`. -/
theorem gap12 (y : ℝ → ℝ)
    (hlim : ∀ x₀, Filter.Tendsto y (nhds x₀) (nhds (y x₀))) :
    Continuous y := by
  rw [continuous_iff_continuousAt]
  exact hlim

/-- Source: `proof_gap/exercise_761/13.txt`; make function typing and uniqueness explicit. -/
theorem gap13 (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    ∃! y : ℝ → ℝ, Continuous y ∧
      ∀ x, y x - ε * Real.sin (y x) = x := by
  let root (x : ℝ) := gap3 ε x hε0 hε1
  let y : ℝ → ℝ := fun x => Classical.choose (root x)
  have hy (x : ℝ) : y x - ε * Real.sin (y x) = x :=
    (Classical.choose_spec (root x)).1
  have hyunique (x z : ℝ) (hz : z - ε * Real.sin z = x) : z = y x :=
    (Classical.choose_spec (root x)).2 z hz
  have hlip : ∀ x x₀,
      |y x - y x₀| ≤ (1 / (1 - ε)) * |x - x₀| := by
    intro x x₀
    have hdiff :
        y x - y x₀ =
          (x - x₀) + ε * (Real.sin (y x) - Real.sin (y x₀)) := by
      linarith [hy x, hy x₀]
    have hstep :
        |y x - y x₀| ≤ |x - x₀| + ε * |y x - y x₀| := by
      calc
        |y x - y x₀| =
            |(x - x₀) + ε * (Real.sin (y x) - Real.sin (y x₀))| :=
          congrArg abs hdiff
        _ ≤ |x - x₀| +
            |ε * (Real.sin (y x) - Real.sin (y x₀))| := abs_add_le _ _
        _ = |x - x₀| +
            ε * |Real.sin (y x) - Real.sin (y x₀)| := by
          rw [abs_mul, abs_of_nonneg hε0]
        _ ≤ |x - x₀| + ε * |y x - y x₀| :=
          add_le_add le_rfl
            (mul_le_mul_of_nonneg_left
              (Real.abs_sin_sub_sin_le _ _) hε0)
    have hmul :
        (1 - ε) * |y x - y x₀| ≤ |x - x₀| := by
      linarith
    have hden : 1 - ε ≠ 0 := ne_of_gt (sub_pos.mpr hε1)
    calc
      |y x - y x₀| =
          (1 / (1 - ε)) * ((1 - ε) * |y x - y x₀|) := by
        field_simp
      _ ≤ (1 / (1 - ε)) * |x - x₀| :=
        mul_le_mul_of_nonneg_left hmul
          (le_of_lt (one_div_pos.mpr (sub_pos.mpr hε1)))
  have hcont : Continuous y :=
    gap12 y (gap11 ε y hε1 hlip)
  refine ⟨y, ⟨hcont, hy⟩, ?_⟩
  intro y' hy'
  funext x
  exact hyunique x (y' x) (hy'.2 x)

end

end ProofGap.Exercise761
