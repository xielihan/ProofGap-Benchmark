import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise3251

noncomputable section

def f (x y : ℝ) : ℝ :=
  Real.sqrt |x * y|

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => g t y) x

def partialY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => g x t) y

def radius (p : ℝ × ℝ) : ℝ :=
  Real.sqrt (p.1 ^ 2 + p.2 ^ 2)

def affineRemainder (p : ℝ × ℝ) : ℝ :=
  f p.1 p.2 - f 0 0 -
    partialX f 0 0 * p.1 -
    partialY f 0 0 * p.2

def remainderQuotient (p : ℝ × ℝ) : ℝ :=
  affineRemainder p / radius p

def radialRatio (p : ℝ × ℝ) : ℝ :=
  Real.sqrt |p.1 * p.2| / radius p

def LocallyBoundedAt (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∃ C : ℝ, ∀ q : ℝ × ℝ, dist q p < ε → |g q| ≤ C

def XPartialBehavior (x y : ℝ) : Prop :=
    (x ≠ 0 → partialX f x y = Real.sqrt |x * y| / (2 * x)) ∧
    (x = 0 ∧ y = 0 → partialX f x y = 0) ∧
    (x = 0 ∧ y ≠ 0 →
      ¬DifferentiableAt ℝ (fun t : ℝ => f t y) x)

def YPartialBehavior (x y : ℝ) : Prop :=
    (y ≠ 0 → partialY f x y = Real.sqrt |x * y| / (2 * y)) ∧
    (x = 0 ∧ y = 0 → partialY f x y = 0) ∧
    (x ≠ 0 ∧ y = 0 →
      ¬DifferentiableAt ℝ (fun t : ℝ => f x t) y)

private theorem partialX_formula {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    partialX f x y = Real.sqrt |x * y| / (2 * x) := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have hlin : HasDerivAt (fun t : ℝ => t * y) y x := by
    simpa using (hasDerivAt_id x).mul (hasDerivAt_const x y)
  have habs := (hasDerivAt_abs hxy).comp x hlin
  have hsqrt :=
    (Real.hasDerivAt_sqrt (abs_ne_zero.mpr hxy)).comp x habs
  change deriv (Real.sqrt ∘ (abs ∘ fun t : ℝ => t * y)) x =
    Real.sqrt |x * y| / (2 * x)
  rw [hsqrt.deriv]
  by_cases hp : 0 < x * y
  · have hsign : ((SignType.sign (x * y) : SignType) : ℝ) = 1 := by
      simp [SignType.sign, hp, ne_of_gt hp,
        not_lt_of_ge (le_of_lt hp)]
    have hspos : 0 < Real.sqrt (x * y) := Real.sqrt_pos.2 hp
    have hsquare : (Real.sqrt (x * y)) ^ 2 = x * y :=
      Real.sq_sqrt (le_of_lt hp)
    rw [abs_of_pos hp, hsign]
    field_simp [hx, hy, hxy, hp, ne_of_gt hspos]
    nlinarith
  · have hn : x * y < 0 := by
      rcases lt_or_eq_of_le (le_of_not_gt hp) with hn | hz
      · exact hn
      · exact (hxy hz).elim
    have hsign : ((SignType.sign (x * y) : SignType) : ℝ) = -1 := by
      simp [SignType.sign, hn, ne_of_lt hn,
        not_lt_of_ge (le_of_lt hn)]
    have hspos : 0 < Real.sqrt (-(x * y)) := Real.sqrt_pos.2 (neg_pos.mpr hn)
    have hsquare : (Real.sqrt (-(x * y))) ^ 2 = -(x * y) :=
      Real.sq_sqrt (le_of_lt (neg_pos.mpr hn))
    rw [abs_of_neg hn, hsign]
    field_simp [hx, hy, hxy, hn, ne_of_gt hspos]
    nlinarith

private theorem not_diff_x_zero {y : ℝ} (hy : y ≠ 0) :
    ¬DifferentiableAt ℝ (fun t : ℝ => f t y) 0 := by
  intro h
  have heq : (fun t : ℝ => (f t y) ^ 2) = (fun t : ℝ => |y| * |t|) := by
    funext t
    rw [f, Real.sq_sqrt (abs_nonneg (t * y)), abs_mul]
    ring
  have hsq : DifferentiableAt ℝ (fun t : ℝ => |y| * |t|) 0 := by
    rw [← heq]
    exact h.pow 2
  have hc : DifferentiableAt ℝ (fun _ : ℝ => |y|⁻¹) 0 :=
    differentiableAt_const (c := |y|⁻¹)
  have heqabs :
      (fun t : ℝ => |t|) =
        ((fun _ : ℝ => |y|⁻¹) * (fun t : ℝ => |y| * |t|)) := by
    funext t
    change |t| = |y|⁻¹ * (|y| * |t|)
    field_simp [abs_ne_zero.mpr hy]
  have habs : DifferentiableAt ℝ (fun t : ℝ => |t|) 0 := by
    rw [heqabs]
    exact hc.mul hsq
  exact not_differentiableAt_abs_zero habs

theorem gap1 :
    partialX f 0 0 = 0 := by
  simp [partialX, f]

theorem gap2 :
    partialY f 0 0 = 0 := by
  simp [partialY, f]

theorem gap3 :
    ∀ p : ℝ × ℝ, p ≠ (0, 0) →
      remainderQuotient p = radialRatio p := by
  intro p hp
  simp [remainderQuotient, affineRemainder, radialRatio, gap1, gap2, f]

theorem gap4 (k : ℝ) :
    Filter.Tendsto
      (fun x : ℝ => radialRatio (x, k * x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (Real.sqrt |k| / Real.sqrt (1 + k ^ 2))) := by
  have hpoint : ∀ x : ℝ, x ≠ 0 →
      radialRatio (x, k * x) =
        Real.sqrt |k| / Real.sqrt (1 + k ^ 2) := by
    intro x hx
    have hxabs : |x| ≠ 0 := abs_ne_zero.mpr hx
    have hkpos : 0 < Real.sqrt (1 + k ^ 2) := by
      exact Real.sqrt_pos.2 (by nlinarith [sq_nonneg k])
    have hnum : Real.sqrt |x * (k * x)| = Real.sqrt |k| * |x| := by
      rw [show x * (k * x) = k * x ^ 2 by ring]
      rw [abs_mul, abs_of_nonneg (sq_nonneg x)]
      rw [Real.sqrt_mul (abs_nonneg k), Real.sqrt_sq_eq_abs]
    have hden : Real.sqrt (x ^ 2 + (k * x) ^ 2) =
        Real.sqrt (1 + k ^ 2) * |x| := by
      rw [show x ^ 2 + (k * x) ^ 2 = (1 + k ^ 2) * x ^ 2 by ring]
      rw [Real.sqrt_mul (by nlinarith [sq_nonneg k] : 0 ≤ 1 + k ^ 2)]
      rw [Real.sqrt_sq_eq_abs]
    simp only [radialRatio, radius, hnum, hden]
    field_simp [hxabs, ne_of_gt hkpos]
  have heq :
      (fun x : ℝ => radialRatio (x, k * x)) =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
        (fun _ : ℝ => Real.sqrt |k| / Real.sqrt (1 + k ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    apply hpoint x
    simpa using hx
  exact tendsto_const_nhds.congr' heq.symm

theorem gap5 :
    ¬∃ L : ℝ,
      Filter.Tendsto radialRatio
        (nhdsWithin (0, 0) ({(0, 0)} : Set (ℝ × ℝ))ᶜ)
        (nhds L) := by
  rintro ⟨L, hL⟩
  have line_tendsto : ∀ k : ℝ,
      Filter.Tendsto (fun x : ℝ => (x, k * x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhdsWithin (0, 0) ({(0, 0)} : Set (ℝ × ℝ))ᶜ) := by
    intro k
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun x : ℝ => (x, k * x)) 0 :=
        continuousAt_id.prodMk (continuousAt_const.mul continuousAt_id)
      have ht := hc.tendsto.mono_left
        (show nhdsWithin 0 (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
      simpa only [mul_zero] using ht
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      simp [hx0]
  have hrestrict : ∀ k : ℝ,
      Filter.Tendsto (fun x : ℝ => radialRatio (x, k * x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Real.sqrt |k| / Real.sqrt (1 + k ^ 2))) := by
    intro k
    apply (gap4 k).mono_left
    apply nhdsWithin_mono
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    simpa using hx0
  have hL0 : Filter.Tendsto (fun x : ℝ => radialRatio (x, 0 * x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) :=
    hL.comp (line_tendsto 0)
  have hL1 : Filter.Tendsto (fun x : ℝ => radialRatio (x, 1 * x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) :=
    hL.comp (line_tendsto 1)
  have e0 := tendsto_nhds_unique hL0 (hrestrict 0)
  have e1 := tendsto_nhds_unique hL1 (hrestrict 1)
  norm_num at e0 e1
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  exact (inv_ne_zero (ne_of_gt hs)) (e1.symm.trans e0)

theorem gap6 :
    ¬DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) (0, 0) := by
  intro h
  have hdiag : DifferentiableAt ℝ (fun t : ℝ => (t, t)) 0 :=
    differentiableAt_id.prodMk differentiableAt_id
  have hc : DifferentiableAt ℝ
      ((fun p : ℝ × ℝ => f p.1 p.2) ∘ (fun t : ℝ => (t, t))) 0 := by
    exact DifferentiableAt.comp
      (f := fun t : ℝ => (t, t))
      (g := fun p : ℝ × ℝ => f p.1 p.2)
      (0 : ℝ) h hdiag
  have heq :
      ((fun p : ℝ × ℝ => f p.1 p.2) ∘ (fun t : ℝ => (t, t))) =
        (fun t : ℝ => |t|) := by
    funext t
    simp only [Function.comp_apply, f]
    rw [show t * t = t ^ 2 by ring]
    rw [abs_of_nonneg (sq_nonneg t), Real.sqrt_sq_eq_abs]
  rw [heq] at hc
  exact not_differentiableAt_abs_zero hc

theorem gap7 (x y : ℝ) :
    XPartialBehavior x y := by
  constructor
  · intro hx
    by_cases hy : y = 0
    · subst y
      simp [partialX, f]
    · exact partialX_formula hx hy
  constructor
  · rintro ⟨hx, hy⟩
    subst x
    subst y
    exact gap1
  · rintro ⟨hx, hy⟩
    subst x
    simpa using not_diff_x_zero hy

theorem gap8 :
    ¬LocallyBoundedAt (fun p => partialX f p.1 p.2) (0, 0) := by
  rintro ⟨ε, hε, C, hC⟩
  let A : ℝ := 2 * (|C| + 1)
  have hA : 0 < A := by
    dsimp [A]
    nlinarith [abs_nonneg C]
  let t : ℝ := ε / (2 * (1 + A ^ 2))
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hteq : t * (2 * (1 + A ^ 2)) = ε := by
    dsimp [t]
    field_simp
  have htlt : t < ε := by
    nlinarith [sq_nonneg A]
  have hAtlt : A ^ 2 * t < ε := by
    nlinarith [sq_nonneg A]
  have hdist : dist (t, A ^ 2 * t) (0, 0) < ε := by
    change max (dist t 0) (dist (A ^ 2 * t) 0) < ε
    rw [max_lt_iff]
    constructor
    · rw [Real.dist_eq, sub_zero, abs_of_pos ht]
      exact htlt
    · have hAt : 0 < A ^ 2 * t := mul_pos (sq_pos_of_pos hA) ht
      rw [Real.dist_eq, sub_zero, abs_of_pos hAt]
      exact hAtlt
  have hprod : 0 < t * (A ^ 2 * t) :=
    mul_pos ht (mul_pos (sq_pos_of_pos hA) ht)
  have hsqrt : Real.sqrt |t * (A ^ 2 * t)| = A * t := by
    rw [abs_of_pos hprod]
    rw [show t * (A ^ 2 * t) = (A * t) ^ 2 by ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hA ht)]
  have hformula := (gap7 t (A ^ 2 * t)).1 (ne_of_gt ht)
  have hval : partialX f t (A ^ 2 * t) = A / 2 := by
    rw [hformula, hsqrt]
    field_simp [ne_of_gt ht]
  have hb := hC (t, A ^ 2 * t) hdist
  change |partialX f t (A ^ 2 * t)| ≤ C at hb
  rw [hval, abs_of_pos (half_pos hA)] at hb
  dsimp [A] at hb
  nlinarith [le_abs_self C]

theorem gap9 (x y : ℝ) :
    XPartialBehavior x y := by
  exact gap7 x y

theorem gap10 :
    ¬LocallyBoundedAt (fun p => partialY f p.1 p.2) (0, 0) := by
  rintro ⟨ε, hε, C, hC⟩
  let A : ℝ := 2 * (|C| + 1)
  have hA : 0 < A := by
    dsimp [A]
    nlinarith [abs_nonneg C]
  let t : ℝ := ε / (2 * (1 + A ^ 2))
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hteq : t * (2 * (1 + A ^ 2)) = ε := by
    dsimp [t]
    field_simp
  have htlt : t < ε := by
    nlinarith [sq_nonneg A]
  have hAtlt : A ^ 2 * t < ε := by
    nlinarith [sq_nonneg A]
  have hdist : dist (A ^ 2 * t, t) (0, 0) < ε := by
    change max (dist (A ^ 2 * t) 0) (dist t 0) < ε
    rw [max_lt_iff]
    constructor
    · have hAt : 0 < A ^ 2 * t := mul_pos (sq_pos_of_pos hA) ht
      rw [Real.dist_eq, sub_zero, abs_of_pos hAt]
      exact hAtlt
    · rw [Real.dist_eq, sub_zero, abs_of_pos ht]
      exact htlt
  have hsym : partialY f (A ^ 2 * t) t = partialX f t (A ^ 2 * t) := by
    unfold partialY partialX
    congr 1
    funext z
    simp [f, mul_comm]
  have hprod : 0 < t * (A ^ 2 * t) :=
    mul_pos ht (mul_pos (sq_pos_of_pos hA) ht)
  have hsqrt : Real.sqrt |t * (A ^ 2 * t)| = A * t := by
    rw [abs_of_pos hprod]
    rw [show t * (A ^ 2 * t) = (A * t) ^ 2 by ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hA ht)]
  have hformula := (gap7 t (A ^ 2 * t)).1 (ne_of_gt ht)
  have hval : partialY f (A ^ 2 * t) t = A / 2 := by
    rw [hsym, hformula, hsqrt]
    field_simp [ne_of_gt ht]
  have hb := hC (A ^ 2 * t, t) hdist
  change |partialY f (A ^ 2 * t) t| ≤ C at hb
  rw [hval, abs_of_pos (half_pos hA)] at hb
  dsimp [A] at hb
  nlinarith [le_abs_self C]

theorem gap11 (x y : ℝ) :
    YPartialBehavior x y := by
  have hsym : partialY f x y = partialX f y x := by
    unfold partialY partialX
    congr 1
    funext t
    simp [f, mul_comm]
  constructor
  · intro hy
    rw [hsym]
    simpa [mul_comm] using (gap7 y x).1 hy
  constructor
  · rintro ⟨hx, hy⟩
    subst x
    subst y
    simpa [hsym] using gap2
  · rintro ⟨hx, hy⟩
    have hnd := (gap7 y x).2.2 ⟨hy, hx⟩
    simpa [f, mul_comm] using hnd

theorem gap12 :
    ContinuousAt (fun p : ℝ × ℝ => f p.1 p.2) (0, 0) ∧
      (∃ Lx : ℝ, partialX f 0 0 = Lx) ∧
      (∃ Ly : ℝ, partialY f 0 0 = Ly) ∧
      ¬DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) (0, 0) := by
  have hc : Continuous (fun p : ℝ × ℝ => f p.1 p.2) := by
    exact Real.continuous_sqrt.comp ((continuous_fst.mul continuous_snd).abs)
  exact ⟨hc.continuousAt, ⟨0, gap1⟩, ⟨0, gap2⟩, gap6⟩

end

end ProofGap.Exercise3251
