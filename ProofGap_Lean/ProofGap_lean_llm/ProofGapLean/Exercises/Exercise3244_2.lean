import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3244_2

noncomputable section

def f (x y : ℝ) : ℝ :=
  Real.log (1 + x) * Real.log (1 + y)

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => g t y) x

def partialY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => g x t) y

def partialXX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX g t y) x

def partialXY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX g x t) y

def partialYY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY g x t) y

def quadraticTaylorFromPartials (x y : ℝ) : ℝ :=
  f 0 0 + partialX f 0 0 * x + partialY f 0 0 * y +
    (1 / (Nat.factorial 2 : ℝ)) *
      (partialXX f 0 0 * x ^ 2 +
        2 * partialXY f 0 0 * x * y +
        partialYY f 0 0 * y ^ 2)

def productTerm (x y : ℝ) : ℝ := x * y

def logRemainder (x : ℝ) : ℝ :=
  Real.log (1 + x) - x

def separatedExpansion (x y : ℝ) : ℝ :=
  (x + logRemainder x) * (y + logRemainder y)

def AgreesToSecondOrder (g p : ℝ × ℝ → ℝ) : Prop :=
  Asymptotics.IsLittleO (nhds (0, 0))
    (fun q => g q - p q)
    (fun q => ‖q‖ ^ 2)

private theorem hasDerivAt_log_one_add (x : ℝ) (hx : 1 + x ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + x)) x := by
  have hinner : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
    simpa only [Pi.add_apply, id_eq, zero_add] using
      (hasDerivAt_const (x := x) (c := (1 : ℝ))).add (hasDerivAt_id x)
  simpa [one_div] using (Real.hasDerivAt_log hx).comp x hinner

private theorem partialX_zero_all (y : ℝ) :
    partialX f 0 y = Real.log (1 + y) := by
  have hlog := hasDerivAt_log_one_add 0 (by norm_num)
  unfold partialX f
  simpa using (hlog.mul_const (Real.log (1 + y))).deriv

private theorem logRemainder_isLittleO :
    Asymptotics.IsLittleO (nhds 0) logRemainder (fun x : ℝ => x) := by
  have hlog := hasDerivAt_log_one_add 0 (by norm_num)
  simpa [logRemainder] using hlog.isLittleO

private theorem separated_agrees :
    AgreesToSecondOrder
      (fun q => separatedExpansion q.1 q.2)
      (fun q => productTerm q.1 q.2) := by
  unfold AgreesToSecondOrder
  have hxlim :
      Tendsto (fun q : ℝ × ℝ => q.1) (nhds (0, 0)) (nhds 0) :=
    (continuous_fst : Continuous (fun q : ℝ × ℝ => q.1)).continuousAt
  have hylim :
      Tendsto (fun q : ℝ × ℝ => q.2) (nhds (0, 0)) (nhds 0) :=
    (continuous_snd : Continuous (fun q : ℝ × ℝ => q.2)).continuousAt
  have hrxCoord :
      Asymptotics.IsLittleO (nhds (0, 0))
        (fun q : ℝ × ℝ => logRemainder q.1) (fun q => q.1) := by
    simpa [Function.comp_def] using logRemainder_isLittleO.comp_tendsto hxlim
  have hryCoord :
      Asymptotics.IsLittleO (nhds (0, 0))
        (fun q : ℝ × ℝ => logRemainder q.2) (fun q => q.2) := by
    simpa [Function.comp_def] using logRemainder_isLittleO.comp_tendsto hylim
  have hxO :
      Asymptotics.IsBigO (nhds (0, 0))
        (fun q : ℝ × ℝ => q.1) (fun q => ‖q‖) := by
    refine Asymptotics.isBigO_iff.2 ⟨1, Filter.Eventually.of_forall ?_⟩
    intro q
    simp only [one_mul]
    rw [Prod.norm_def]
    have hmax : 0 ≤ max ‖q.1‖ ‖q.2‖ := by
      exact (norm_nonneg q.1).trans (le_max_left _ _)
    calc
      ‖q.1‖ ≤ max ‖q.1‖ ‖q.2‖ := le_max_left _ _
      _ = ‖max ‖q.1‖ ‖q.2‖‖ := by
        symm
        rw [Real.norm_eq_abs, abs_of_nonneg hmax]
  have hyO :
      Asymptotics.IsBigO (nhds (0, 0))
        (fun q : ℝ × ℝ => q.2) (fun q => ‖q‖) := by
    refine Asymptotics.isBigO_iff.2 ⟨1, Filter.Eventually.of_forall ?_⟩
    intro q
    simp only [one_mul]
    rw [Prod.norm_def]
    have hmax : 0 ≤ max ‖q.1‖ ‖q.2‖ := by
      exact (norm_nonneg q.2).trans (le_max_right _ _)
    calc
      ‖q.2‖ ≤ max ‖q.1‖ ‖q.2‖ := le_max_right _ _
      _ = ‖max ‖q.1‖ ‖q.2‖‖ := by
        symm
        rw [Real.norm_eq_abs, abs_of_nonneg hmax]
  have hrx :
      Asymptotics.IsLittleO (nhds (0, 0))
        (fun q : ℝ × ℝ => logRemainder q.1) (fun q => ‖q‖) :=
    hrxCoord.trans_isBigO hxO
  have hry :
      Asymptotics.IsLittleO (nhds (0, 0))
        (fun q : ℝ × ℝ => logRemainder q.2) (fun q => ‖q‖) :=
    hryCoord.trans_isBigO hyO
  have hsum :=
    (hxO.mul_isLittleO hry).add
      ((hrx.mul_isBigO hyO).add (hrx.mul hry))
  have hnum :
      (fun q : ℝ × ℝ =>
        separatedExpansion q.1 q.2 - productTerm q.1 q.2) =
      (fun q : ℝ × ℝ =>
        q.1 * logRemainder q.2 +
          (logRemainder q.1 * q.2 +
            logRemainder q.1 * logRemainder q.2)) := by
    funext q
    simp only [separatedExpansion, productTerm]
    ring
  have hden :
      (fun q : ℝ × ℝ => ‖q‖ ^ 2) =
        (fun q : ℝ × ℝ => ‖q‖ * ‖q‖) := by
    funext q
    ring
  rw [hnum, hden]
  exact hsum

theorem gap1 (x : ℝ) (hx : |x| < 1) :
    partialX f x 0 = 0 := by
  simp [partialX, f]

theorem gap2 :
    partialX f 0 0 = 0 := by
  exact gap1 0 (by norm_num)

theorem gap3 (y : ℝ) (hy : |y| < 1) :
    partialY f 0 y = 0 := by
  simp [partialY, f]

theorem gap4 :
    partialY f 0 0 = 0 := by
  exact gap3 0 (by norm_num)

theorem gap5 (x : ℝ) (hx : |x| < 1) :
    partialXX f x 0 = 0 := by
  simp [partialXX, partialX, f]

theorem gap6 :
    partialXX f 0 0 = 0 := by
  exact gap5 0 (by norm_num)

theorem gap7 (y : ℝ) (hy : |y| < 1) :
    partialYY f 0 y = 0 := by
  simp [partialYY, partialY, f]

theorem gap8 :
    partialYY f 0 0 = 0 := by
  exact gap7 0 (by norm_num)

theorem gap9 (y : ℝ) (hy : |y| < 1) :
    partialX f 0 y = Real.log (1 + y) := by
  exact partialX_zero_all y

theorem gap10 (y : ℝ) (hy : |y| < 1) :
    partialXY f 0 y = 1 / (1 + y) := by
  have hpos : 0 < 1 + y := by
    rw [abs_lt] at hy
    linarith
  simpa [partialXY, partialX_zero_all] using
    (hasDerivAt_log_one_add y (ne_of_gt hpos)).deriv

theorem gap11 :
    partialXY f 0 0 = 1 := by
  simpa using (gap10 0 (by norm_num))

theorem gap12 :
    AgreesToSecondOrder
      (fun q => f q.1 q.2)
      (fun q => quadraticTaylorFromPartials q.1 q.2) := by
  have hfun :
      (fun q : ℝ × ℝ => f q.1 q.2) =
        (fun q : ℝ × ℝ => separatedExpansion q.1 q.2) := by
    funext q
    simp only [f, separatedExpansion, logRemainder]
    ring
  have hpoly :
      (fun q : ℝ × ℝ => quadraticTaylorFromPartials q.1 q.2) =
        (fun q : ℝ × ℝ => productTerm q.1 q.2) := by
    funext q
    norm_num [quadraticTaylorFromPartials, productTerm, f, gap2, gap4,
      gap6, gap8, gap11] <;> ring
  rw [hfun, hpoly]
  exact separated_agrees

theorem gap13 (x y : ℝ) :
    quadraticTaylorFromPartials x y = productTerm x y := by
  norm_num [quadraticTaylorFromPartials, productTerm, f, gap2, gap4,
    gap6, gap8, gap11] <;> ring

theorem gap14 :
    AgreesToSecondOrder
      (fun q => f q.1 q.2)
      (fun q => productTerm q.1 q.2) := by
  have hfun :
      (fun q : ℝ × ℝ => f q.1 q.2) =
        (fun q : ℝ × ℝ => separatedExpansion q.1 q.2) := by
    funext q
    simp only [f, separatedExpansion, logRemainder]
    ring
  rw [hfun]
  exact separated_agrees

theorem gap15 :
    Asymptotics.IsLittleO (nhds 0) logRemainder (fun x : ℝ => x) ∧
      ∀ x y, f x y = separatedExpansion x y := by
  constructor
  · exact logRemainder_isLittleO
  · intro x y
    simp only [f, separatedExpansion, logRemainder]
    ring

theorem gap16 :
    AgreesToSecondOrder
      (fun q => separatedExpansion q.1 q.2)
      (fun q => productTerm q.1 q.2) := by
  exact separated_agrees

theorem gap17 :
    AgreesToSecondOrder
      (fun q => Real.log (1 + q.1) * Real.log (1 + q.2))
      (fun q => q.1 * q.2) := by
  simpa only [f, productTerm] using gap14

end

end ProofGap.Exercise3244_2
