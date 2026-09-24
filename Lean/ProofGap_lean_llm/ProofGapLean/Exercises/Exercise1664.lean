import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Order.IntermediateValue

namespace ProofGap.Exercise1664

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / Real.sqrt (3 * x ^ 2 - 2)
def intermediate (x : ℝ) : ℝ :=
  1 / Real.sqrt 2 * Real.sqrt (2 / 3) *
    Real.log |x * Real.sqrt (3 / 2) + Real.sqrt (3 / 2 * x ^ 2 - 1)|
def primitive (x : ℝ) : ℝ :=
  1 / Real.sqrt 3 *
    Real.log |x * Real.sqrt 3 + Real.sqrt (3 * x ^ 2 - 2)|
def domain : Set ℝ := {x | 2 < 3 * x ^ 2}

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem intermediate_identity (x : ℝ) (hx : x ∈ domain) :
    intermediate x =
      primitive x - Real.log (Real.sqrt 2) / Real.sqrt 3 := by
  change 2 < 3 * x ^ 2 at hx
  have hr : 0 < (3 / 2 : ℝ) * x ^ 2 - 1 := by nlinarith
  have hb : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hc : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hbne : Real.sqrt 2 ≠ 0 := ne_of_gt hb
  have hcne : Real.sqrt 3 ≠ 0 := ne_of_gt hc
  have ha_sq : (Real.sqrt (3 / 2)) ^ 2 = (3 / 2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hr_sq : (Real.sqrt ((3 / 2 : ℝ) * x ^ 2 - 1)) ^ 2 =
      (3 / 2 : ℝ) * x ^ 2 - 1 :=
    Real.sq_sqrt (le_of_lt hr)
  have ha :
      Real.sqrt 3 = Real.sqrt (3 / 2) * Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    congr 1 <;> norm_num
  have hd :
      Real.sqrt (2 / 3) * Real.sqrt 3 = Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    congr 1 <;> norm_num
  have hcoef :
      1 / Real.sqrt 2 * Real.sqrt (2 / 3) = 1 / Real.sqrt 3 := by
    field_simp [hbne, hcne] <;> nlinarith [hd]
  have hroot :
      Real.sqrt (3 * x ^ 2 - 2) =
        Real.sqrt 2 * Real.sqrt ((3 / 2 : ℝ) * x ^ 2 - 1) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have harg :
      x * Real.sqrt 3 + Real.sqrt (3 * x ^ 2 - 2) =
        Real.sqrt 2 *
          (x * Real.sqrt (3 / 2) +
            Real.sqrt ((3 / 2 : ℝ) * x ^ 2 - 1)) := by
    rw [ha, hroot]
    ring
  have hxa_sq :
      (x * Real.sqrt (3 / 2)) ^ 2 = (3 / 2 : ℝ) * x ^ 2 := by
    calc
      (x * Real.sqrt (3 / 2)) ^ 2 =
          x ^ 2 * (Real.sqrt (3 / 2)) ^ 2 := by ring
      _ = (3 / 2 : ℝ) * x ^ 2 := by rw [ha_sq]; ring
  have harg_ne :
      x * Real.sqrt (3 / 2) +
          Real.sqrt ((3 / 2 : ℝ) * x ^ 2 - 1) ≠ 0 := by
    intro hzero
    have hneg :
        x * Real.sqrt (3 / 2) =
          -Real.sqrt ((3 / 2 : ℝ) * x ^ 2 - 1) := by
      linarith
    have heqsq := congrArg (fun z : ℝ => z ^ 2) hneg
    nlinarith [hxa_sq, hr_sq, heqsq]
  unfold intermediate primitive
  rw [hcoef, harg, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2),
    Real.log_mul hbne (abs_ne_zero.mpr harg_ne)]
  ring

private theorem primitive_derivative (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  change 2 < 3 * x ^ 2 at hx
  let c : ℝ := Real.sqrt 3
  let r : ℝ := Real.sqrt (3 * x ^ 2 - 2)
  have hq : 0 < 3 * x ^ 2 - 2 := by linarith
  have hc : 0 < c := by
    dsimp [c]
    exact Real.sqrt_pos.2 (by norm_num)
  have hr : 0 < r := by
    dsimp [r]
    exact Real.sqrt_pos.2 hq
  have hcne : c ≠ 0 := ne_of_gt hc
  have hrne : r ≠ 0 := ne_of_gt hr
  have hc_sq : c ^ 2 = 3 := by
    dsimp [c]
    exact Real.sq_sqrt (by norm_num)
  have hr_sq : r ^ 2 = 3 * x ^ 2 - 2 := by
    dsimp [r]
    exact Real.sq_sqrt (le_of_lt hq)
  have hu_ne : x * c + r ≠ 0 := by
    intro hzero
    have hxc_sq : (x * c) ^ 2 = 3 * x ^ 2 := by
      calc
        (x * c) ^ 2 = x ^ 2 * c ^ 2 := by ring
        _ = 3 * x ^ 2 := by rw [hc_sq]; ring
    have hneg : x * c = -r := by linarith
    have heqsq := congrArg (fun z : ℝ => z ^ 2) hneg
    nlinarith [hxc_sq, hr_sq, heqsq]
  have hqderiv :
      HasDerivAt (fun y : ℝ => 3 * y ^ 2 - 2) (6 * x) x := by
    convert (((hasDerivAt_id x).pow 2).const_mul 3).sub_const 2 using 1 <;>
      simp only [id_eq] <;> ring
  have huderiv :
      HasDerivAt
        (fun y : ℝ => y * c + Real.sqrt (3 * y ^ 2 - 2))
        (c + (1 / (2 * r)) * (6 * x)) x := by
    convert ((hasDerivAt_id x).mul_const c).add
      ((Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hqderiv) using 1 <;>
      dsimp [r] <;> ring
  have hlogbase :
      HasDerivAt Real.log (1 / (x * c + r)) (x * c + r) := by
    simpa only [one_div] using Real.hasDerivAt_log hu_ne
  have hlog :
      HasDerivAt
        (fun y : ℝ => Real.log (y * c + Real.sqrt (3 * y ^ 2 - 2)))
        ((1 / (x * c + r)) * (c + (1 / (2 * r)) * (6 * x))) x := by
    simpa [Function.comp_def, r] using hlogbase.comp x huderiv
  have hscaled := hlog.const_mul (1 / c)
  have hid : c * (x * c + r) = r * c + 3 * x := by
    calc
      c * (x * c + r) = x * c ^ 2 + r * c := by ring
      _ = r * c + 3 * x := by rw [hc_sq]; ring
  have hinner :
      c + (1 / (2 * r)) * (6 * x) = c * (x * c + r) / r := by
    field_simp [hrne]
    nlinarith [hid]
  have hu_ne' : c * x + r ≠ 0 := by
    simpa [mul_comm] using hu_ne
  have hval :
      (1 / c) *
          ((1 / (x * c + r)) * (c + (1 / (2 * r)) * (6 * x))) =
        1 / r := by
    rw [hinner]
    field_simp [hcne, hrne, hu_ne, hu_ne'] <;> ring
  rw [hval] at hscaled
  have hfun :
      (fun y : ℝ =>
        1 / c * Real.log (y * c + Real.sqrt (3 * y ^ 2 - 2))) = primitive := by
    funext y
    dsimp [primitive, c]
    rw [Real.log_abs]
  rw [hfun] at hscaled
  simpa [integrand, r] using hscaled

theorem gap1 (x : ℝ) :
    3 * x ^ 2 - 2 = 2 * ((Real.sqrt (3 / 2) * x) ^ 2 - 1) := by
  have h : (0 : ℝ) ≤ 3 / 2 := by norm_num
  rw [mul_pow, Real.sq_sqrt h]
  ring

theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt intermediate (integrand x) x := by
  have hopen : IsOpen domain := by
    unfold domain
    exact isOpen_lt continuous_const (continuous_const.mul (continuous_id.pow 2))
  let K : ℝ := Real.log (Real.sqrt 2) / Real.sqrt 3
  have heq :
      intermediate =ᶠ[nhds x] (fun y => primitive y - K) := by
    exact Filter.mem_of_superset (hopen.mem_nhds hx) (fun y hy => by
      simpa [K] using intermediate_identity y hy)
  have hp := primitive_derivative x hx
  have hshift : HasDerivAt (fun y => primitive y - K) (integrand x) x :=
    hp.sub_const K
  exact hshift.congr_of_eventuallyEq heq

theorem gap3 (x : ℝ) (hx : x ∈ domain) :
    intermediate x =
      primitive x - Real.log (Real.sqrt 2) / Real.sqrt 3 := by
  exact intermediate_identity x hx

theorem gap4 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  ext F
  change
    (∀ x ∈ s, HasDerivAt F (integrand x) x) ↔
      ∃ C, ∀ x ∈ s, F x = primitive x + C
  constructor
  · intro hF
    rcases s.eq_empty_or_nonempty with hsempty | ⟨x₀, hx₀⟩
    · refine ⟨0, ?_⟩
      intro x hx
      rw [hsempty] at hx
      exact False.elim (by simpa using hx)
    · let H : ℝ → ℝ := fun y => F y - primitive y
      have hH : ∀ y ∈ s, HasDerivAt H 0 y := by
        intro y hy
        have hsub := (hF y hy).sub (primitive_derivative y (hdom hy))
        simpa [H] using hsub
      have hdiff : DifferentiableOn ℝ H s := by
        intro y hy
        exact (hH y hy).differentiableAt.differentiableWithinAt
      have hzero : ∀ y ∈ s, deriv H y = 0 := by
        intro y hy
        exact (hH y hy).deriv
      have hord : Set.OrdConnected s :=
        isPreconnected_iff_ordConnected.mp hs
      have hpair_lt :
          ∀ ⦃y z : ℝ⦄, y ∈ s → z ∈ s → y < z → H y = H z := by
        intro y z hy hz hyz
        rcases Metric.isOpen_iff.mp hopen y hy with ⟨ε, hε, hεsub⟩
        rcases Metric.isOpen_iff.mp hopen z hz with ⟨δ, hδ, hδsub⟩
        let a : ℝ := y - ε / 2
        let b : ℝ := z + δ / 2
        have hεhalf : 0 < ε / 2 := by linarith
        have hδhalf : 0 < δ / 2 := by linarith
        have ha : a ∈ s := by
          apply hεsub
          rw [Metric.mem_ball, Real.dist_eq]
          change |y - ε / 2 - y| < ε
          rw [show y - ε / 2 - y = -(ε / 2) by ring, abs_neg,
            abs_of_pos hεhalf]
          linarith
        have hb : b ∈ s := by
          apply hδsub
          rw [Metric.mem_ball, Real.dist_eq]
          change |z + δ / 2 - z| < δ
          rw [show z + δ / 2 - z = δ / 2 by ring, abs_of_pos hδhalf]
          linarith
        have hay : a < y := by
          dsimp [a]
          linarith
        have hzb : z < b := by
          dsimp [b]
          linarith
        have hab : a < b := lt_trans hay (lt_trans hyz hzb)
        have hsub : Set.Ioo a b ⊆ s := by
          intro t ht
          exact hord.out ha hb ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        have hdiffI : DifferentiableOn ℝ H (Set.Ioo a b) :=
          hdiff.mono hsub
        have hzeroI : ∀ t ∈ Set.Ioo a b, deriv H t = 0 := by
          intro t ht
          exact hzero t (hsub ht)
        have hconstI :
            Set.Pairwise (Set.Ioo a b) (fun u v => H u = H v) := by
          intro u hu v hv huv
          exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
            hdiffI hzeroI hu hv
        have hyI : y ∈ Set.Ioo a b :=
          ⟨hay, lt_trans hyz hzb⟩
        have hzI : z ∈ Set.Ioo a b :=
          ⟨lt_trans hay hyz, hzb⟩
        exact hconstI hyI hzI (ne_of_lt hyz)
      have hconst : Set.Pairwise s (fun y z => H y = H z) := by
        intro y hy z hz hyne
        by_cases hyz : y < z
        · exact hpair_lt hy hz hyz
        · have hzy : z < y := lt_of_le_of_ne (le_of_not_gt hyz) (Ne.symm hyne)
          exact (hpair_lt hz hy hzy).symm
      refine ⟨F x₀ - primitive x₀, ?_⟩
      intro x hx
      by_cases hxx : x = x₀
      · subst x
        ring
      · have heq := hconst hx hx₀ hxx
        dsimp [H] at heq
        linarith
  · rintro ⟨C, hC⟩ x hx
    have heq : F =ᶠ[nhds x] (fun y => primitive y + C) := by
      exact Filter.mem_of_superset (hopen.mem_nhds hx) (fun y hy => hC y hy)
    have hp := primitive_derivative x (hdom hx)
    have htranslate :
        HasDerivAt (fun y => primitive y + C) (integrand x) x :=
      hp.add_const C
    exact htranslate.congr_of_eventuallyEq heq

end

end ProofGap.Exercise1664
