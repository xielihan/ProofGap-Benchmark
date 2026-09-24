import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.IsUniformGroup.Order
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

namespace ProofGap.Exercise3109

noncomputable section

open Filter
open scoped BigOperators Topology

def SummableFromOne (u : ℕ → ℝ) : Prop :=
  Summable (fun n : ℕ => u (n + 1))

def partialProduct (f : ℕ → ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∏ n ∈ Finset.Icc 1 N, (1 + f n x)

def HasProductFromOne (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, Tendsto (fun N => partialProduct f N x) atTop (𝓝 (F x))

def G (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.log |F x|

def absTerm (f : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  |f (n + 1) x|

def logTerm (f : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.log |1 + f (n + 1) x|

def derivativeLogTerm (f : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  deriv (fun y => Real.log |1 + f (n + 1) y|) x

def derivativeRatioTerm (f : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  deriv (f (n + 1)) x / (1 + f (n + 1) x)

def logSeries (f : ℕ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, logTerm f n x

def derivativeRatioSeries (f : ℕ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, derivativeRatioTerm f n x

def SufficientConditions (f : ℕ → ℝ → ℝ) (c : ℕ → ℝ)
    (F : ℝ → ℝ) (a b : ℝ) : Prop :=
  (∀ n : ℕ, 1 ≤ n → DifferentiableOn ℝ (f n) (Set.Ioo a b)) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ x ∈ Set.Ioo a b, 1 + f n x ≠ 0) ∧
  (∀ x ∈ Set.Ioo a b, SummableFromOne (fun n => |f n x|)) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ x ∈ Set.Ioo a b,
    |deriv (f n) x| ≤ c n) ∧
  (∀ n : ℕ, 1 ≤ n → 0 ≤ c n) ∧
  SummableFromOne c ∧
  HasProductFromOne f F (Set.Ioo a b)

/-- Source: `proof_gap/exercise_3109/1.txt`; logarithmic derivative. -/
theorem gap1 (F : ℝ → ℝ) (x : ℝ)
    (hF : DifferentiableAt ℝ F x) (hF0 : F x ≠ 0) :
    deriv (G F) x = deriv F x / F x := by
  have habs :
      HasDerivAt (fun y => |F y|)
        ((SignType.sign (F x) : ℝ) * deriv F x) x :=
    (hasDerivAt_abs hF0).comp x hF.hasDerivAt
  have hlog :=
    (Real.hasDerivAt_log (abs_ne_zero.mpr hF0)).comp x habs
  unfold G
  change deriv (Real.log ∘ fun y => |F y|) x = deriv F x / F x
  rw [hlog.deriv]
  rcases lt_or_gt_of_ne hF0 with hneg | hpos
  · rw [sign_neg hneg, abs_of_neg hneg]
    norm_num
    field_simp
  · rw [sign_pos hpos, abs_of_pos hpos]
    norm_num
    ring

/-- Source: `proof_gap/exercise_3109/2.txt`; rearrange. -/
theorem gap2 (F : ℝ → ℝ) (x : ℝ)
    (hF : DifferentiableAt ℝ F x) (hF0 : F x ≠ 0) :
    deriv F x = F x * deriv (G F) x := by
  rw [gap1 F x hF hF0]
  field_simp

/-- Source: `proof_gap/exercise_3109/3.txt`; definitional identity. -/
theorem gap3 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (a b x : ℝ)
    (hprod : HasProductFromOne f F (Set.Ioo a b))
    (hx : x ∈ Set.Ioo a b) :
    deriv (G F) x = deriv (fun y => Real.log |F y|) x := by
  rfl

/-- Source: `proof_gap/exercise_3109/4.txt`; equal on a neighborhood. -/
theorem gap4 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (a b x : ℝ)
    (hx : x ∈ Set.Ioo a b)
    (hseries : ∀ y ∈ Set.Ioo a b, G F y = logSeries f y) :
    deriv (G F) x = deriv (logSeries f) x := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact hseries y hy

/-- Source: `proof_gap/exercise_3109/5.txt`; termwise derivative sum. -/
theorem gap5 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (x : ℝ)
    (hG : deriv (G F) x = deriv (logSeries f) x)
    (htermwise :
      HasSum (fun n : ℕ => derivativeLogTerm f n x)
        (deriv (logSeries f) x)) :
    deriv (G F) x = ∑' n : ℕ, derivativeLogTerm f n x := by
  rw [hG, htermwise.tsum_eq]

/-- Source: `proof_gap/exercise_3109/6.txt`; differentiate each factor. -/
theorem gap6 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (x : ℝ)
    (hdiff : ∀ n : ℕ, DifferentiableAt ℝ (f (n + 1)) x)
    (hnz : ∀ n : ℕ, 1 + f (n + 1) x ≠ 0)
    (hGsum :
      deriv (G F) x = ∑' n : ℕ, derivativeLogTerm f n x) :
    deriv (G F) x = derivativeRatioSeries f x := by
  rw [hGsum]
  unfold derivativeRatioSeries
  congr 1
  funext n
  unfold derivativeLogTerm derivativeRatioTerm
  have hg : DifferentiableAt ℝ (fun y => 1 + f (n + 1) y) x :=
    (differentiableAt_const (c := (1 : ℝ))).add (hdiff n)
  rw [deriv.log (hg.abs (hnz n)) (abs_ne_zero.mpr (hnz n))]
  have habs :
      deriv (fun y => |1 + f (n + 1) y|) x =
        (SignType.sign (1 + f (n + 1) x) : ℝ) *
          deriv (f (n + 1)) x := by
    simpa using ((hasDerivAt_abs (hnz n)).comp x hg.hasDerivAt).deriv
  rw [habs]
  rcases lt_or_gt_of_ne (hnz n) with hneg | hpos
  · rw [sign_neg hneg, abs_of_neg hneg]
    norm_num
    rw [show -f (n + 1) x + -1 = -(1 + f (n + 1) x) by ring, div_neg]
    ring
  · rw [sign_pos hpos, abs_of_pos hpos]
    norm_num

/-- Source: `proof_gap/exercise_3109/7.txt`; left endpoint. -/
theorem gap7 (a b x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ioo a b) :
    ∃ a₁ : ℝ, a < a₁ ∧ a₁ < x₀ := by
  exact ⟨(a + x₀) / 2, by constructor <;> linarith [hx₀.1]⟩

/-- Source: `proof_gap/exercise_3109/8.txt`; same left endpoint. -/
theorem gap8 (a b x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ioo a b) :
    ∃ a₁ : ℝ, a < a₁ ∧ a₁ < x₀ := by
  exact gap7 a b x₀ hx₀

/-- Source: `proof_gap/exercise_3109/9.txt`; right endpoint. -/
theorem gap9 (a b x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ioo a b) :
    ∃ b₁ : ℝ, x₀ < b₁ ∧ b₁ < b := by
  exact ⟨(x₀ + b) / 2, by constructor <;> linarith [hx₀.2]⟩

/-- Source: `proof_gap/exercise_3109/10.txt`; same right endpoint. -/
theorem gap10 (a b x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ioo a b) :
    ∃ b₁ : ℝ, x₀ < b₁ ∧ b₁ < b := by
  exact gap9 a b x₀ hx₀

/-- Source: `proof_gap/exercise_3109/11.txt`. -/
theorem gap11 (a b x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ioo a b) :
    a < b := by
  exact hx₀.1.trans hx₀.2

private theorem inner_absTerm_le
    (f : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (a b x₀ a₁ b₁ : ℝ)
    (hx₀ : x₀ ∈ Set.Ioo a b)
    (hnest : a < a₁ ∧ a₁ < x₀ ∧ x₀ < b₁ ∧ b₁ < b)
    (hdiff : ∀ n : ℕ, 1 ≤ n → DifferentiableOn ℝ (f n) (Set.Ioo a b))
    (hderiv : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Set.Ioo a b,
      |deriv (f n) x| ≤ c n)
    (hc0 : ∀ n : ℕ, 1 ≤ n → 0 ≤ c n) :
    ∀ n : ℕ, ∀ x ∈ Set.Icc a₁ b₁,
      ‖absTerm f n x‖ ≤ absTerm f n x₀ + (b - a) * c (n + 1) := by
  intro n x hx
  have hsub : Set.Icc a₁ b₁ ⊆ Set.Ioo a b := by
    intro y hy
    exact ⟨hnest.1.trans_le hy.1, hy.2.trans_lt hnest.2.2.2⟩
  have hx' := hsub hx
  have hx₀' : x₀ ∈ Set.Icc a₁ b₁ :=
    ⟨hnest.2.1.le, hnest.2.2.1.le⟩
  have hdiffAt : ∀ y ∈ Set.Icc a₁ b₁,
      DifferentiableAt ℝ (f (n + 1)) y := by
    intro y hy
    have hy' := hsub hy
    exact (hdiff (n + 1) (by omega) y hy').differentiableAt
      (Ioo_mem_nhds hy'.1 hy'.2)
  have hmv :
      |f (n + 1) x - f (n + 1) x₀| ≤
        c (n + 1) * |x - x₀| := by
    simpa [Real.norm_eq_abs] using
      (Convex.norm_image_sub_le_of_norm_deriv_le
        hdiffAt
        (fun y hy => by
          simpa [Real.norm_eq_abs] using
            hderiv (n + 1) (by omega) y (hsub hy))
        (convex_Icc a₁ b₁) hx₀' hx)
  have hdist : |x - x₀| ≤ b - a := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hx₀.1, hx₀.2]
  have hc : 0 ≤ c (n + 1) := hc0 (n + 1) (by omega)
  have hmv' :
      |f (n + 1) x - f (n + 1) x₀| ≤
        (b - a) * c (n + 1) := by
    calc
      |f (n + 1) x - f (n + 1) x₀|
          ≤ c (n + 1) * |x - x₀| := hmv
      _ ≤ c (n + 1) * (b - a) :=
        mul_le_mul_of_nonneg_left hdist hc
      _ = (b - a) * c (n + 1) := by ring
  unfold absTerm
  rw [Real.norm_eq_abs, abs_abs]
  calc
    |f (n + 1) x|
        = |(f (n + 1) x - f (n + 1) x₀) + f (n + 1) x₀| := by
          congr 1
          ring
    _ ≤ |f (n + 1) x - f (n + 1) x₀| + |f (n + 1) x₀| :=
      abs_add_le _ _
    _ ≤ (b - a) * c (n + 1) + |f (n + 1) x₀| :=
      add_le_add hmv' le_rfl
    _ = |f (n + 1) x₀| + (b - a) * c (n + 1) := by ring

/-- Source: `proof_gap/exercise_3109/12.txt`; inner uniform absolute series. -/
theorem gap12 (f : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (F : ℝ → ℝ)
    (a b x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ioo a b)
    (h : SufficientConditions f c F a b) :
    ∃ a₁ b₁ : ℝ,
      a < a₁ ∧ a₁ < x₀ ∧ x₀ < b₁ ∧ b₁ < b ∧
      HasSumUniformlyOn (absTerm f)
        (fun x => ∑' n : ℕ, absTerm f n x) (Set.Ioo a₁ b₁) := by
  rcases h with ⟨hdiff, hnz, habs, hderiv, hc0, hcsum, hprod⟩
  let a₁ := (a + x₀) / 2
  let b₁ := (x₀ + b) / 2
  have hnest : a < a₁ ∧ a₁ < x₀ ∧ x₀ < b₁ ∧ b₁ < b := by
    dsimp [a₁, b₁]
    constructor
    · linarith [hx₀.1]
    constructor
    · linarith [hx₀.1]
    constructor <;> linarith [hx₀.2]
  refine ⟨a₁, b₁, hnest.1, hnest.2.1, hnest.2.2.1, hnest.2.2.2, ?_⟩
  have hu : Summable
      (fun n : ℕ => absTerm f n x₀ + (b - a) * c (n + 1)) := by
    exact (habs x₀ hx₀).add (hcsum.mul_left (b - a))
  apply HasSumUniformlyOn.of_norm_le_summable hu
  intro n x hx
  exact inner_absTerm_le f c a b x₀ a₁ b₁ hx₀ hnest
    hdiff hderiv hc0 n x ⟨hx.1.le, hx.2.le⟩

/-- Source: `proof_gap/exercise_3109/13.txt`; uniform small tail. -/
theorem gap13 (f : ℕ → ℝ → ℝ) (a₁ b₁ : ℝ)
    (huniform :
      HasSumUniformlyOn (absTerm f)
        (fun x => ∑' n : ℕ, absTerm f n x) (Set.Ioo a₁ b₁)) :
    ∃ N : ℕ, ∀ n : ℕ, N < n →
      ∀ x ∈ Set.Ioo a₁ b₁, |f n x| < 1 / 2 := by
  let s : Set ℝ := Set.Ioo a₁ b₁
  have hsumm :
      Summable (UniformOnFun.ofFun {s} ∘ absTerm f) :=
    huniform.summable
  have hzero :
      Tendsto (UniformOnFun.ofFun {s} ∘ absTerm f) atTop (𝓝 0) :=
    hsumm.tendsto_atTop_zero
  have hunifzero :
      TendstoUniformlyOn (absTerm f) (fun _ => 0) atTop s := by
    have H :=
      (UniformOnFun.tendsto_iff_tendstoUniformlyOn (𝔖 := {s})).mp hzero
    simpa [Function.comp_def] using H s (by simp)
  have hev : ∀ᶠ n in atTop, ∀ x ∈ s, absTerm f n x < 1 / 2 :=
    hunifzero.eventually_forall_lt (u := (0 : ℝ)) (v := 1 / 2) (by norm_num)
      (fun x hx => by simp)
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun n hn x hx => ?_⟩
  cases n with
  | zero => omega
  | succ k =>
      simpa [s, absTerm] using hN k (by omega) x hx

/-- Source: `proof_gap/exercise_3109/14.txt`; logarithm bound. -/
theorem gap14 (f : ℕ → ℝ → ℝ) (a₁ b₁ : ℝ) (N : ℕ)
    (hsmall :
      ∀ n : ℕ, N < n → ∀ x ∈ Set.Ioo a₁ b₁, |f n x| < 1 / 2) :
    ∀ n : ℕ, N < n → ∀ x ∈ Set.Ioo a₁ b₁,
      |Real.log (|1 + f n x|)| ≤ 2 * |f n x| := by
  intro n hn x hx
  let u := f n x
  have hu := hsmall n hn x hx
  have hu' : ‖(u : ℂ)‖ ≤ 1 / 2 := by
    simpa [u, Complex.norm_real] using hu.le
  have hlog := Complex.norm_log_one_add_half_le_self hu'
  have hpos : 0 < 1 + u := by
    have := (abs_lt.mp hu).1
    linarith
  have hre : Complex.log (1 + (u : ℂ)) = Real.log (1 + u) := by
    rw [show (1 : ℂ) + (u : ℂ) = ((1 + u : ℝ) : ℂ) by norm_num,
      Complex.ofReal_log hpos.le]
  rw [hre, Complex.norm_real, Real.norm_eq_abs] at hlog
  rw [abs_of_pos hpos]
  calc
    |Real.log (1 + f n x)| = |Real.log (1 + u)| := by rfl
    _ ≤ (3 / 2 : ℝ) * |u| := by
      simpa [Complex.norm_real] using hlog
    _ ≤ 2 * |u| := by gcongr <;> norm_num
    _ = 2 * |f n x| := by rfl

/-- Source: `proof_gap/exercise_3109/15.txt`; derivative ratio bound. -/
theorem gap15 (f : ℕ → ℝ → ℝ) (c : ℕ → ℝ)
    (a₁ b₁ : ℝ) (N : ℕ)
    (hsmall :
      ∀ n : ℕ, N < n → ∀ x ∈ Set.Ioo a₁ b₁, |f n x| < 1 / 2)
    (hderiv :
      ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Set.Ioo a₁ b₁,
        |deriv (f n) x| ≤ c n) :
    ∀ n : ℕ, N < n → ∀ x ∈ Set.Ioo a₁ b₁,
      |deriv (f n) x / (1 + f n x)| ≤ 2 * c n := by
  intro n hn x hx
  have hu := hsmall n hn x hx
  have hlow : -(1 / 2 : ℝ) < f n x := (abs_lt.mp hu).1
  have hpos : 0 < 1 + f n x := by linarith
  have hden : (1 / 2 : ℝ) < |1 + f n x| := by
    rw [abs_of_pos hpos]
    linarith
  have hnum := hderiv n (by omega) x hx
  have hc : 0 ≤ c n := (abs_nonneg (deriv (f n) x)).trans hnum
  rw [abs_div]
  apply (div_le_iff₀ (by linarith : 0 < |1 + f n x|)).2
  nlinarith [abs_nonneg (deriv (f n) x)]

/-- Source: `proof_gap/exercise_3109/16.txt`; uniform log series. -/
theorem gap16 (f : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (F : ℝ → ℝ)
    (a b x₀ a₁ b₁ : ℝ)
    (hx₀ : x₀ ∈ Set.Ioo a b)
    (hnest : a < a₁ ∧ a₁ < x₀ ∧ x₀ < b₁ ∧ b₁ < b)
    (h : SufficientConditions f c F a b) :
    HasSumUniformlyOn (logTerm f) (logSeries f) (Set.Ioo a₁ b₁) := by
  rcases h with ⟨hdiff, hnz, habs, hderiv, hc0, hcsum, hprod⟩
  have huAbs : Summable
      (fun n : ℕ => absTerm f n x₀ + (b - a) * c (n + 1)) :=
    (habs x₀ hx₀).add (hcsum.mul_left (b - a))
  have huniformAbs :
      HasSumUniformlyOn (absTerm f)
        (fun x => ∑' n : ℕ, absTerm f n x) (Set.Ioo a₁ b₁) := by
    apply HasSumUniformlyOn.of_norm_le_summable huAbs
    intro n x hx
    exact inner_absTerm_le f c a b x₀ a₁ b₁ hx₀ hnest
      hdiff hderiv hc0 n x ⟨hx.1.le, hx.2.le⟩
  obtain ⟨N, hsmall⟩ := gap13 f a₁ b₁ huniformAbs
  have hlog := gap14 f a₁ b₁ N hsmall
  have hu : Summable
      (fun n : ℕ => 2 *
        (absTerm f n x₀ + (b - a) * c (n + 1))) :=
    huAbs.mul_left 2
  unfold logSeries
  apply HasSumUniformlyOn.of_norm_le_summable_eventually hu
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_gt_atTop N] with n hn
  intro x hx
  have h1 := hlog (n + 1) (by omega) x hx
  have h2 := inner_absTerm_le f c a b x₀ a₁ b₁ hx₀ hnest
    hdiff hderiv hc0 n x ⟨hx.1.le, hx.2.le⟩
  have h2' :
      |f (n + 1) x| ≤
        |f (n + 1) x₀| + (b - a) * c (n + 1) := by
    simpa [absTerm, Real.norm_eq_abs] using h2
  simpa [logTerm, absTerm, Real.norm_eq_abs] using
    h1.trans (mul_le_mul_of_nonneg_left h2' (by norm_num))

/-- Source: `proof_gap/exercise_3109/17.txt`; derivative terms uniform. -/
theorem gap17 (f : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (F : ℝ → ℝ)
    (a b x₀ a₁ b₁ : ℝ)
    (hx₀ : x₀ ∈ Set.Ioo a b)
    (hnest : a < a₁ ∧ a₁ < x₀ ∧ x₀ < b₁ ∧ b₁ < b)
    (h : SufficientConditions f c F a b) :
    HasSumUniformlyOn (derivativeRatioTerm f)
      (derivativeRatioSeries f) (Set.Ioo a₁ b₁) := by
  rcases h with ⟨hdiff, hnz, habs, hderiv, hc0, hcsum, hprod⟩
  have huAbs : Summable
      (fun n : ℕ => absTerm f n x₀ + (b - a) * c (n + 1)) :=
    (habs x₀ hx₀).add (hcsum.mul_left (b - a))
  have huniformAbs :
      HasSumUniformlyOn (absTerm f)
        (fun x => ∑' n : ℕ, absTerm f n x) (Set.Ioo a₁ b₁) := by
    apply HasSumUniformlyOn.of_norm_le_summable huAbs
    intro n x hx
    exact inner_absTerm_le f c a b x₀ a₁ b₁ hx₀ hnest
      hdiff hderiv hc0 n x ⟨hx.1.le, hx.2.le⟩
  obtain ⟨N, hsmall⟩ := gap13 f a₁ b₁ huniformAbs
  have hratio := gap15 f c a₁ b₁ N hsmall
    (fun n hn x hx => hderiv n hn x
      ⟨hnest.1.trans hx.1, hx.2.trans hnest.2.2.2⟩)
  have hu : Summable (fun n : ℕ => 2 * c (n + 1)) :=
    hcsum.mul_left 2
  unfold derivativeRatioSeries
  apply HasSumUniformlyOn.of_norm_le_summable_eventually hu
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_gt_atTop N] with n hn
  intro x hx
  change ‖deriv (f (n + 1)) x / (1 + f (n + 1) x)‖ ≤
    2 * c (n + 1)
  rw [Real.norm_eq_abs]
  exact hratio (n + 1) (by omega) x hx

private theorem hasDerivAt_logTerm
    (f : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hdiff : DifferentiableAt ℝ (f (n + 1)) x)
    (hnz : 1 + f (n + 1) x ≠ 0) :
    HasDerivAt (logTerm f n) (derivativeRatioTerm f n x) x := by
  have hg : DifferentiableAt ℝ (fun y => 1 + f (n + 1) y) x :=
    (differentiableAt_const (c := (1 : ℝ))).add hdiff
  have habs :
      HasDerivAt (fun y => |1 + f (n + 1) y|)
        ((SignType.sign (1 + f (n + 1) x) : ℝ) *
          deriv (f (n + 1)) x) x :=
    by simpa using (hasDerivAt_abs hnz).comp x hg.hasDerivAt
  have hlog :=
    (Real.hasDerivAt_log (abs_ne_zero.mpr hnz)).comp x habs
  unfold logTerm derivativeRatioTerm
  convert hlog using 1
  rcases lt_or_gt_of_ne hnz with hneg | hpos
  · rw [sign_neg hneg, abs_of_neg hneg]
    norm_num
    rw [show -f (n + 1) x + -1 = -(1 + f (n + 1) x) by ring]
    rw [inv_neg]
    ring
  · rw [sign_pos hpos, abs_of_pos hpos]
    norm_num
    ring

private theorem partialProduct_eq_prod_range
    (f : ℕ → ℝ → ℝ) (N : ℕ) (x : ℝ) :
    partialProduct f N x =
      ∏ n ∈ Finset.range N, (1 + f (n + 1) x) := by
  induction N with
  | zero => simp [partialProduct]
  | succ N ih =>
      rw [partialProduct, Finset.prod_Icc_succ_top (by omega)]
      rw [← partialProduct, ih, Finset.prod_range_succ]

private theorem product_eq_tprod
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (a b x : ℝ)
    (habs : ∀ x ∈ Set.Ioo a b,
      SummableFromOne (fun n => |f n x|))
    (hprod : HasProductFromOne f F (Set.Ioo a b))
    (hx : x ∈ Set.Ioo a b) :
    F x = ∏' n : ℕ, (1 + f (n + 1) x) := by
  have hs : Summable (fun n : ℕ => ‖f (n + 1) x‖) := by
    simpa [SummableFromOne, Real.norm_eq_abs] using habs x hx
  have hm : Multipliable (fun n : ℕ => 1 + f (n + 1) x) :=
    multipliable_one_add_of_summable hs
  have hp := hprod x hx
  have hrange :
      Tendsto (fun N => ∏ n ∈ Finset.range N, (1 + f (n + 1) x))
        atTop (𝓝 (F x)) := by
    simpa only [← partialProduct_eq_prod_range f] using hp
  have htprod :
      Tendsto (fun N => ∏ n ∈ Finset.range N, (1 + f (n + 1) x))
        atTop (𝓝 (∏' n : ℕ, (1 + f (n + 1) x))) :=
    hm.hasProd.comp tendsto_finset_range
  exact tendsto_nhds_unique hrange htprod

private theorem G_eq_logSeries
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (a b x : ℝ)
    (hnz : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Set.Ioo a b,
      1 + f n x ≠ 0)
    (habs : ∀ x ∈ Set.Ioo a b,
      SummableFromOne (fun n => |f n x|))
    (hprod : HasProductFromOne f F (Set.Ioo a b))
    (hx : x ∈ Set.Ioo a b) :
    G F x = logSeries f x := by
  have hs : Summable (fun n : ℕ => ‖f (n + 1) x‖) := by
    simpa [SummableFromOne, Real.norm_eq_abs] using habs x hx
  have hfac : ∀ n : ℕ, 1 + f (n + 1) x ≠ 0 :=
    fun n => hnz (n + 1) (by omega) x hx
  have hm : Multipliable (fun n : ℕ => 1 + f (n + 1) x) :=
    multipliable_one_add_of_summable hs
  have hlogs :
      Summable (fun n : ℕ => Real.log ‖1 + f (n + 1) x‖) :=
    hs.summable_log_norm_one_add
  have hexp :
      Real.exp (∑' n : ℕ, Real.log ‖1 + f (n + 1) x‖) =
        ∏' n : ℕ, ‖1 + f (n + 1) x‖ :=
    Real.rexp_tsum_eq_tprod
      (fun n => norm_pos_iff.mpr (hfac n)) hlogs
  rw [G, logSeries, product_eq_tprod f F a b x habs hprod hx,
    ← Real.norm_eq_abs, hm.norm_tprod, ← hexp, Real.log_exp]
  congr 1

private theorem hasDerivAt_logSeries
    (f : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (F : ℝ → ℝ)
    (a b x₀ a₁ b₁ x : ℝ)
    (hx₀ : x₀ ∈ Set.Ioo a b)
    (hnest : a < a₁ ∧ a₁ < x₀ ∧ x₀ < b₁ ∧ b₁ < b)
    (h : SufficientConditions f c F a b)
    (hx : x ∈ Set.Ioo a₁ b₁) :
    HasDerivAt (logSeries f) (derivativeRatioSeries f x) x := by
  rcases h with ⟨hdiff, hnz, habs, hderiv, hc0, hcsum, hprod⟩
  have hratio :=
    (gap17 f c F a b x₀ a₁ b₁ hx₀ hnest
      ⟨hdiff, hnz, habs, hderiv, hc0, hcsum, hprod⟩).tendstoUniformlyOn_finsetRange
  have hlogs :=
    (gap16 f c F a b x₀ a₁ b₁ hx₀ hnest
      ⟨hdiff, hnz, habs, hderiv, hc0, hcsum, hprod⟩).tendstoUniformlyOn_finsetRange
  apply hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hratio
    (Eventually.of_forall fun N y hy => ?_)
    (fun y hy => hlogs.tendsto_at hy) hx
  apply HasDerivAt.fun_sum
  intro n hn
  have hy' : y ∈ Set.Ioo a b :=
    ⟨hnest.1.trans hy.1, hy.2.trans hnest.2.2.2⟩
  exact hasDerivAt_logTerm f n y
    ((hdiff (n + 1) (by omega) y hy').differentiableAt
      (Ioo_mem_nhds hy'.1 hy'.2))
    (hnz (n + 1) (by omega) y hy')

/-- Source: `proof_gap/exercise_3109/18.txt`; termwise differentiation. -/
theorem gap18 (f : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (F : ℝ → ℝ)
    (a b x₀ a₁ b₁ : ℝ)
    (hx₀ : x₀ ∈ Set.Ioo a b)
    (hnest : a < a₁ ∧ a₁ < x₀ ∧ x₀ < b₁ ∧ b₁ < b)
    (h : SufficientConditions f c F a b) :
    DifferentiableOn ℝ (G F) (Set.Ioo a₁ b₁) := by
  rcases h with ⟨hdiff, hnz, habs, hderiv, hc0, hcsum, hprod⟩
  intro x hx
  have hsum := hasDerivAt_logSeries f c F a b x₀ a₁ b₁ x hx₀ hnest
    ⟨hdiff, hnz, habs, hderiv, hc0, hcsum, hprod⟩ hx
  have heq : G F =ᶠ[𝓝 x] logSeries f := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact G_eq_logSeries f F a b y hnz habs hprod
      ⟨hnest.1.trans hy.1, hy.2.trans hnest.2.2.2⟩
  exact (hsum.differentiableAt.congr_of_eventuallyEq heq).differentiableWithinAt

/-- Source: `proof_gap/exercise_3109/19.txt`; product continuity. -/
theorem gap19 (f : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (F : ℝ → ℝ)
    (a b x₀ a₁ b₁ : ℝ)
    (hx₀ : x₀ ∈ Set.Ioo a b)
    (hnest : a < a₁ ∧ a₁ < x₀ ∧ x₀ < b₁ ∧ b₁ < b)
    (h : SufficientConditions f c F a b) :
    ContinuousOn F (Set.Ioo a₁ b₁) := by
  rcases h with ⟨hdiff, hnz, habs, hderiv, hc0, hcsum, hprod⟩
  let K : Set ℝ := Set.Icc a₁ b₁
  have hsub : K ⊆ Set.Ioo a b := by
    intro y hy
    exact ⟨hnest.1.trans_le hy.1, hy.2.trans_lt hnest.2.2.2⟩
  have hu : Summable
      (fun n : ℕ => absTerm f n x₀ + (b - a) * c (n + 1)) :=
    (habs x₀ hx₀).add (hcsum.mul_left (b - a))
  have hbound : ∀ n : ℕ, ∀ x ∈ K,
      ‖f (n + 1) x‖ ≤
        absTerm f n x₀ + (b - a) * c (n + 1) := by
    intro n x hx
    have H := inner_absTerm_le f c a b x₀ a₁ b₁ hx₀ hnest
      hdiff hderiv hc0 n x hx
    simpa [absTerm, Real.norm_eq_abs] using H
  have hcts : ∀ n : ℕ, ContinuousOn (fun x => f (n + 1) x) K := by
    intro n
    exact (hdiff (n + 1) (by omega)).continuousOn.mono hsub
  have hp :
      HasProdUniformlyOn (fun n : ℕ => fun x => 1 + f (n + 1) x)
        (fun x => ∏' n : ℕ, (1 + f (n + 1) x)) K :=
    Summable.hasProdUniformlyOn_nat_one_add isCompact_Icc hu
      (Eventually.of_forall hbound) hcts
  have hpF :
      HasProdUniformlyOn (fun n : ℕ => fun x => 1 + f (n + 1) x)
        F K := hp.congr_right fun x hx =>
      (product_eq_tprod f F a b x habs hprod (hsub hx)).symm
  have hfin : ∀ N : ℕ,
      ContinuousOn
        (fun x => ∏ n ∈ Finset.range N, (1 + f (n + 1) x)) K := by
    intro N
    apply continuousOn_finset_prod
    intro n hn
    exact (continuousOn_const.add (hcts n))
  exact (hpF.tendstoUniformlyOn_finsetRange.continuousOn
    (Eventually.of_forall hfin).frequently).mono
      (fun x hx => ⟨hx.1.le, hx.2.le⟩)

/-- Source: `proof_gap/exercise_3109/20.txt`; positive branch. -/
theorem gap20 (F : ℝ → ℝ) (x : ℝ) (hFpos : 0 < F x) :
    F x = Real.exp (G F x) := by
  rw [G, abs_of_pos hFpos, Real.exp_log hFpos]

/-- Source: `proof_gap/exercise_3109/21.txt`; positive derivative branch. -/
theorem gap21 (F : ℝ → ℝ) (a₁ b₁ x : ℝ)
    (hx : x ∈ Set.Ioo a₁ b₁)
    (hlocal : ∀ y ∈ Set.Ioo a₁ b₁, F y = Real.exp (G F y))
    (hG : DifferentiableOn ℝ (G F) (Set.Ioo a₁ b₁)) :
    deriv F x = Real.exp (G F x) * deriv (G F) x := by
  have heq : F =ᶠ[𝓝 x] fun y => Real.exp (G F y) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hlocal y hy
  calc
    deriv F x = deriv (fun y => Real.exp (G F y)) x := heq.deriv_eq
    _ = _ := ((Real.hasDerivAt_exp (G F x)).comp x
      ((hG x hx).differentiableAt
        (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt).deriv

/-- Source: `proof_gap/exercise_3109/22.txt`; substitute series. -/
theorem gap22 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (x : ℝ)
    (hFexp : F x = Real.exp (G F x))
    (hG : deriv (G F) x = derivativeRatioSeries f x) :
    Real.exp (G F x) * deriv (G F) x =
      F x * derivativeRatioSeries f x := by
  rw [hFexp, hG]

/-- Source: `proof_gap/exercise_3109/23.txt`; positive formula. -/
theorem gap23 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (x : ℝ)
    (hF : deriv F x = Real.exp (G F x) * deriv (G F) x)
    (hFexp : F x = Real.exp (G F x))
    (hG : deriv (G F) x = derivativeRatioSeries f x) :
    deriv F x = F x * derivativeRatioSeries f x := by
  rw [hF, ← hFexp, hG]

/-- Source: `proof_gap/exercise_3109/24.txt`; negative branch. -/
theorem gap24 (F : ℝ → ℝ) (x : ℝ) (hFneg : F x < 0) :
    F x = -Real.exp (G F x) := by
  rw [G, abs_of_neg hFneg, Real.exp_log (neg_pos.mpr hFneg)]
  ring

/-- Source: `proof_gap/exercise_3109/25.txt`; negative derivative branch. -/
theorem gap25 (F : ℝ → ℝ) (a₁ b₁ x : ℝ)
    (hx : x ∈ Set.Ioo a₁ b₁)
    (hlocal : ∀ y ∈ Set.Ioo a₁ b₁, F y = -Real.exp (G F y))
    (hG : DifferentiableOn ℝ (G F) (Set.Ioo a₁ b₁)) :
    deriv F x = -Real.exp (G F x) * deriv (G F) x := by
  have heq : F =ᶠ[𝓝 x] fun y => -Real.exp (G F y) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hlocal y hy
  have hd := ((Real.hasDerivAt_exp (G F x)).comp x
    ((hG x hx).differentiableAt
      (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt).neg
  calc
    deriv F x = deriv (fun y => -Real.exp (G F y)) x := heq.deriv_eq
    _ = _ := by simpa [neg_mul] using hd.deriv

/-- Source: `proof_gap/exercise_3109/26.txt`; substitute negative branch. -/
theorem gap26 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (x : ℝ)
    (hFexp : F x = -Real.exp (G F x))
    (hG : deriv (G F) x = derivativeRatioSeries f x) :
    -Real.exp (G F x) * deriv (G F) x =
      F x * derivativeRatioSeries f x := by
  rw [hFexp, hG]

/-- Source: `proof_gap/exercise_3109/27.txt`; negative formula. -/
theorem gap27 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (x : ℝ)
    (hF : deriv F x = -Real.exp (G F x) * deriv (G F) x)
    (hFexp : F x = -Real.exp (G F x))
    (hG : deriv (G F) x = derivativeRatioSeries f x) :
    deriv F x = F x * derivativeRatioSeries f x := by
  rw [hF, ← hFexp, hG]

/-- Source: `proof_gap/exercise_3109/28.txt`; final theorem. -/
theorem gap28 (f : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (F : ℝ → ℝ)
    (a b : ℝ) (h : SufficientConditions f c F a b) :
    ∀ x ∈ Set.Ioo a b,
      deriv F x =
        F x * ∑' n : ℕ,
          deriv (f (n + 1)) x / (1 + f (n + 1) x) := by
  rcases h with ⟨hdiff, hnz, habs, hderiv, hc0, hcsum, hprod⟩
  intro x hx
  let hcnd : SufficientConditions f c F a b :=
    ⟨hdiff, hnz, habs, hderiv, hc0, hcsum, hprod⟩
  obtain ⟨a₁, b₁, ha₁, ha₁x, hxb₁, hb₁, huniform⟩ :=
    gap12 f c F a b x hx hcnd
  have hnest : a < a₁ ∧ a₁ < x ∧ x < b₁ ∧ b₁ < b :=
    ⟨ha₁, ha₁x, hxb₁, hb₁⟩
  have hxInner : x ∈ Set.Ioo a₁ b₁ := ⟨ha₁x, hxb₁⟩
  have hGdiff :=
    gap18 f c F a b x a₁ b₁ hx hnest hcnd
  have hFcont :=
    gap19 f c F a b x a₁ b₁ hx hnest hcnd
  have hsum :=
    hasDerivAt_logSeries f c F a b x a₁ b₁ x hx hnest hcnd hxInner
  have heq : G F =ᶠ[𝓝 x] logSeries f := by
    filter_upwards [Ioo_mem_nhds ha₁x hxb₁] with y hy
    exact G_eq_logSeries f F a b y hnz habs hprod
      ⟨ha₁.trans hy.1, hy.2.trans hb₁⟩
  have hGderiv :
      deriv (G F) x = derivativeRatioSeries f x := by
    rw [heq.deriv_eq, hsum.deriv]
  have hs : Summable (fun n : ℕ => ‖f (n + 1) x‖) := by
    simpa [SummableFromOne, Real.norm_eq_abs] using habs x hx
  have hfac : ∀ n : ℕ, 1 + f (n + 1) x ≠ 0 :=
    fun n => hnz (n + 1) (by omega) x hx
  have hF0 : F x ≠ 0 := by
    rw [product_eq_tprod f F a b x habs hprod hx]
    exact tprod_one_add_ne_zero_of_summable hfac hs
  have hFcontAt : ContinuousAt F x :=
    (hFcont x hxInner).continuousAt
      (Ioo_mem_nhds hxInner.1 hxInner.2)
  rcases lt_or_gt_of_ne hF0 with hneg | hpos
  · have hevneg : ∀ᶠ y in 𝓝 x, F y < 0 :=
      hFcontAt (Iio_mem_nhds hneg)
    have hev : ∀ᶠ y in 𝓝 x,
        F y < 0 ∧ y ∈ Set.Ioo a₁ b₁ :=
      hevneg.and (Ioo_mem_nhds hxInner.1 hxInner.2)
    obtain ⟨l, u, hxl, hlu⟩ := Filter.Eventually.exists_Ioo_subset hev
    have hGsmall : DifferentiableOn ℝ (G F) (Set.Ioo l u) :=
      hGdiff.mono (fun y hy => (hlu hy).2)
    have hlocal : ∀ y ∈ Set.Ioo l u,
        F y = -Real.exp (G F y) :=
      fun y hy => gap24 F y (hlu hy).1
    have hbranch := gap25 F l u x hxl hlocal hGsmall
    have hformula :=
      gap27 f F x hbranch (gap24 F x hneg) hGderiv
    simpa [derivativeRatioSeries, derivativeRatioTerm] using hformula
  · have hevpos : ∀ᶠ y in 𝓝 x, 0 < F y :=
      hFcontAt (Ioi_mem_nhds hpos)
    have hev : ∀ᶠ y in 𝓝 x,
        0 < F y ∧ y ∈ Set.Ioo a₁ b₁ :=
      hevpos.and (Ioo_mem_nhds hxInner.1 hxInner.2)
    obtain ⟨l, u, hxl, hlu⟩ := Filter.Eventually.exists_Ioo_subset hev
    have hGsmall : DifferentiableOn ℝ (G F) (Set.Ioo l u) :=
      hGdiff.mono (fun y hy => (hlu hy).2)
    have hlocal : ∀ y ∈ Set.Ioo l u,
        F y = Real.exp (G F y) :=
      fun y hy => gap20 F y (hlu hy).1
    have hbranch := gap21 F l u x hxl hlocal hGsmall
    have hformula :=
      gap23 f F x hbranch (gap20 F x hpos) hGderiv
    simpa [derivativeRatioSeries, derivativeRatioTerm] using hformula

end

end ProofGap.Exercise3109
