import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1619

noncomputable section

def f (x : ℝ) := x - 0.1 * Real.sin x - 2
def Approx (actual expected tolerance : ℝ) : Prop :=
  |actual - expected| < tolerance
def approximant : ℕ → ℝ
  | 1 => 2.075
  | 2 => 2.080
  | 3 => 2.083
  | 4 => 2.087
  | _ => 0
def ApproxRoot (sample tolerance : ℝ) : Prop :=
  ∃ r ∈ Set.Ioo (2 : ℝ) (2 * Real.pi / 3),
    f r = 0 ∧ |sample - r| < tolerance

private theorem hasDerivAt_f (x : ℝ) :
    HasDerivAt f (1 - 0.1 * Real.cos x) x := by
  simpa only [f] using
    (((hasDerivAt_id x).sub ((Real.hasDerivAt_sin x).const_mul 0.1)).sub_const 2)

private theorem continuous_f : Continuous f := by
  rw [continuous_iff_continuousAt]
  exact fun x => (hasDerivAt_f x).continuousAt

private theorem differentiable_f : Differentiable ℝ f :=
  fun x => (hasDerivAt_f x).differentiableAt

private theorem deriv_f (x : ℝ) : deriv f x = 1 - 0.1 * Real.cos x :=
  (hasDerivAt_f x).deriv

private theorem deriv_deriv_f (x : ℝ) : deriv (deriv f) x = 0.1 * Real.sin x := by
  have hfun : deriv f = fun y : ℝ => 1 - 0.1 * Real.cos y :=
    funext deriv_f
  rw [hfun]
  have h :=
    ((hasDerivAt_const x (1 : ℝ)).sub
      ((Real.hasDerivAt_cos x).const_mul 0.1))
  convert h.deriv using 1 <;> ring

private theorem cos_half_identity (x : ℝ) :
    Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
  have htrig := Real.sin_sq_add_cos_sq (x / 2)
  calc
    Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
      convert Real.cos_two_mul (x / 2) using 1 <;> ring
    _ = 1 - 2 * Real.sin (x / 2) ^ 2 := by
      nlinarith

private theorem sin_lower_cubic (x : ℝ) (hx : 0 < x) :
    x * (1 - x ^ 2 / 2) < Real.sin x := by
  set_option maxHeartbeats 2000000 in
    obtain ⟨c, hc, hcder⟩ :=
      exists_deriv_eq_slope (f := Real.sin) hx
        Real.continuous_sin.continuousOn Real.differentiable_sin.differentiableOn
    have hdc : deriv Real.sin c = Real.cos c :=
      (Real.hasDerivAt_sin c).deriv
    rw [hdc, Real.sin_zero, sub_zero, sub_zero] at hcder
    have hne : x ≠ 0 := ne_of_gt hx
    have hslope : Real.sin x = Real.cos c * x :=
      (div_eq_iff hne).mp hcder.symm
    have hhalfpos : 0 < c / 2 := by nlinarith [hc.1]
    have habs : |Real.sin (c / 2)| ≤ |c / 2| := Real.abs_sin_le_abs
    rw [abs_of_pos hhalfpos] at habs
    have hprod :
        0 ≤ (c / 2 - |Real.sin (c / 2)|) *
          (c / 2 + |Real.sin (c / 2)|) := by
      exact mul_nonneg (sub_nonneg.mpr habs)
        (add_nonneg hhalfpos.le (abs_nonneg _))
    have hsquare : Real.sin (c / 2) ^ 2 ≤ (c / 2) ^ 2 := by
      nlinarith [hprod, sq_abs (Real.sin (c / 2))]
    have hcosid : Real.cos c = 1 - 2 * Real.sin (c / 2) ^ 2 :=
      cos_half_identity c
    have hcoslower : 1 - c ^ 2 / 2 ≤ Real.cos c := by
      rw [hcosid]
      nlinarith
    have hcx : 0 < (x - c) * (x + c) := by
      exact mul_pos (sub_pos.mpr hc.2) (add_pos hx hc.1)
    have hstrict : 1 - x ^ 2 / 2 < Real.cos c := by
      nlinarith
    have hm : 0 < x * (Real.cos c - (1 - x ^ 2 / 2)) :=
      mul_pos hx (sub_pos.mpr hstrict)
    rw [hslope]
    nlinarith

private theorem sin_near_endpoint (x : ℝ) :
    Real.sin x =
      Real.sqrt 3 / 2 * Real.cos (2 * Real.pi / 3 - x) +
        (1 / 2 : ℝ) * Real.sin (2 * Real.pi / 3 - x) := by
  let d : ℝ := 2 * Real.pi / 3 - x
  have hx : x = 2 * Real.pi / 3 - d := by
    dsimp [d]
    ring
  have hs : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_three]
  have hc : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  rw [hx, Real.sin_sub, hs, hc]
  dsimp [d]
  ring

theorem gap1 : Approx (f 2) (-0.091) (1 / 10000) := by
  set_option maxHeartbeats 2000000 in
    let d : ℝ := 2 * Real.pi / 3 - 2
    have hdlo : (0.09439 : ℝ) < d := by
      dsimp [d]
      nlinarith [Real.pi_gt_d20]
    have hdhi : d < (0.09440 : ℝ) := by
      dsimp [d]
      nlinarith [Real.pi_lt_d20]
    have hdhi' : d < (0.0944 : ℝ) := by
      convert hdhi using 1 <;> norm_num
    have hdpos : 0 < d := by linarith
    have hsd := sin_lower_cubic d hdpos
    have hsdlo : (0.0939 : ℝ) < Real.sin d := by
      have hd2 : d ^ 2 < (0.09440 : ℝ) ^ 2 := by
        nlinarith [sq_nonneg d]
      nlinarith
    have hsdhi : Real.sin d < (0.0944 : ℝ) :=
      lt_of_le_of_lt (Real.sin_le hdpos.le) hdhi'
    let q : ℝ := Real.sin (d / 2)
    have hhalfpos : 0 < d / 2 := by linarith
    have hhalfhi : d / 2 < (0.0472 : ℝ) := by linarith
    have hqbound := sin_lower_cubic (d / 2) hhalfpos
    have hqlo : (0.047 : ℝ) < q := by
      dsimp [q]
      have hh2 : (d / 2) ^ 2 < (0.0472 : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (d / 2)]
      nlinarith
    have hqhi : q < (0.0472 : ℝ) := by
      dsimp [q]
      exact lt_of_le_of_lt (Real.sin_le hhalfpos.le) hhalfhi
    have hcos : Real.cos d = 1 - 2 * q ^ 2 := by
      simpa [q] using cos_half_identity d
    have hclo : (0.9955 : ℝ) < Real.cos d := by
      have hp : 0 < ((0.0472 : ℝ) - q) * (0.0472 + q) := by
        apply mul_pos <;> linarith
      nlinarith
    have hchi : Real.cos d < (0.996 : ℝ) := by
      have hp : 0 < (q - (0.047 : ℝ)) * (q + 0.047) := by
        apply mul_pos <;> linarith
      nlinarith
    have hs0 := Real.sqrt_nonneg 3
    have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hslo : (0.866 : ℝ) < Real.sqrt 3 / 2 := by nlinarith
    have hshi : Real.sqrt 3 / 2 < (0.867 : ℝ) := by nlinarith
    have hspos : 0 < Real.sqrt 3 / 2 := by nlinarith
    have hcpos : 0 < Real.cos d := by linarith
    have hpLo : (0.866 : ℝ) * 0.9955 <
        (Real.sqrt 3 / 2) * Real.cos d := by
      calc
        (0.866 : ℝ) * 0.9955 < (Real.sqrt 3 / 2) * 0.9955 :=
          mul_lt_mul_of_pos_right hslo (by norm_num)
        _ < (Real.sqrt 3 / 2) * Real.cos d :=
          mul_lt_mul_of_pos_left hclo hspos
    have hpHi : (Real.sqrt 3 / 2) * Real.cos d <
        (0.867 : ℝ) * 0.996 := by
      calc
        (Real.sqrt 3 / 2) * Real.cos d <
            (Real.sqrt 3 / 2) * 0.996 :=
          mul_lt_mul_of_pos_left hchi hspos
        _ < (0.867 : ℝ) * 0.996 :=
          mul_lt_mul_of_pos_right hshi (by norm_num)
    have hformula := sin_near_endpoint 2
    change Real.sin 2 =
      Real.sqrt 3 / 2 * Real.cos d + (1 / 2 : ℝ) * Real.sin d at hformula
    rw [Approx, f, abs_lt]
    norm_num
    constructor <;> linarith
theorem gap2 :
    Approx (f (2 * Real.pi / 3)) 0.0078 (1 / 10000) := by
  set_option maxHeartbeats 2000000 in
    have hs0 := Real.sqrt_nonneg 3
    have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hslo : (1.7320508075 : ℝ) < Real.sqrt 3 := by nlinarith
    have hshi : Real.sqrt 3 < (1.7320508076 : ℝ) := by nlinarith
    have hsin := sin_near_endpoint (2 * Real.pi / 3)
    norm_num at hsin
    rw [Approx, f, hsin, abs_lt]
    norm_num
    constructor <;> nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]
theorem gap3 (x : ℝ) (hx : x ∈ Set.Ioo (2 : ℝ) (2 * Real.pi / 3)) :
    deriv f x ≠ 0 := by
  rw [deriv_f]
  have hc := Real.cos_le_one x
  norm_num at hc ⊢
  nlinarith
theorem gap4 :
    ∃! ξ : ℝ, ξ ∈ Set.Ioo (2 : ℝ) (2 * Real.pi / 3) ∧ f ξ = 0 := by
  have hf2 : f 2 < 0 := by
    have h := gap1
    rw [Approx, abs_lt] at h
    norm_num [f] at h ⊢
    linarith
  have hfu : 0 < f (2 * Real.pi / 3) := by
    have h := gap2
    rw [Approx, abs_lt] at h
    norm_num at h ⊢
    linarith
  have horder : (2 : ℝ) < 2 * Real.pi / 3 := by
    nlinarith [Real.pi_gt_three]
  have hz : (0 : ℝ) ∈ Set.Icc (f 2) (f (2 * Real.pi / 3)) :=
    ⟨le_of_lt hf2, le_of_lt hfu⟩
  rcases (intermediate_value_Icc (f := f) (le_of_lt horder)
      continuous_f.continuousOn) hz with ⟨r, hr, hfr⟩
  have hr' : r ∈ Set.Ioo (2 : ℝ) (2 * Real.pi / 3) := by
    constructor
    · exact lt_of_not_ge fun h => by
        have : r = 2 := le_antisymm h hr.1
        subst r
        linarith
    · exact lt_of_not_ge fun h => by
        have : r = 2 * Real.pi / 3 := le_antisymm hr.2 h
        subst r
        linarith
  refine ⟨r, ⟨hr', hfr⟩, ?_⟩
  intro y hy
  have heq : r - y = 0.1 * (Real.sin r - Real.sin y) := by
    have hyr := hy.2.trans hfr.symm
    simp only [f] at hyr
    linarith
  have habs : |r - y| = 0.1 * |Real.sin r - Real.sin y| := by
    rw [heq, abs_mul]
    norm_num
  have hs := Real.abs_sin_sub_sin_le r y
  have hzabs : |r - y| = 0 := by
    nlinarith [abs_nonneg (r - y), abs_nonneg (Real.sin r - Real.sin y)]
  exact (sub_eq_zero.mp (abs_eq_zero.mp hzabs)).symm
theorem gap5 : approximant 1 = 2.075 := by
  rfl
theorem gap6 : approximant 2 = 2.080 := by
  rfl
theorem gap7 : approximant 3 = 2.083 := by
  rfl
theorem gap8 : approximant 4 = 2.087 := by
  rfl
theorem gap9 : Approx (f 2.087) 0.00003 (1 / 10000000) := by
  set_option maxHeartbeats 2000000 in
    let d : ℝ := 2 * Real.pi / 3 - 2.087
    have hdlo : (0.0073951 : ℝ) < d := by
      dsimp [d]
      nlinarith only [Real.pi_gt_d20]
    have hdhi : d < (0.0073952 : ℝ) := by
      dsimp [d]
      nlinarith only [Real.pi_lt_d20]
    have hdpos : 0 < d := by
      linarith only [hdlo]
    have hdcube : d ^ 3 / 2 < (0.000000203 : ℝ) := by
      have hp : 0 < ((0.0073952 : ℝ) - d) *
          ((0.0073952 : ℝ) ^ 2 + 0.0073952 * d + d ^ 2) := by
        apply mul_pos
        · linarith only [hdhi]
        · nlinarith only [sq_nonneg d, hdpos]
      nlinarith only [hp]
    have hsbound := sin_lower_cubic d hdpos
    have hsdlo : (0.0073948 : ℝ) < Real.sin d := by
      nlinarith only [hsbound, hdlo, hdcube]
    have hsdhi : Real.sin d < (0.0073952 : ℝ) :=
      lt_of_le_of_lt (Real.sin_le hdpos.le) hdhi
    have hhalfpos : 0 < d / 2 := by
      linarith only [hdpos]
    have hhalfhi : d / 2 < (0.0036976 : ℝ) := by
      linarith only [hdhi]
    have hhalfcube : (d / 2) ^ 3 / 2 < (0.000000026 : ℝ) := by
      have hp : 0 < ((0.0036976 : ℝ) - d / 2) *
          ((0.0036976 : ℝ) ^ 2 + 0.0036976 * (d / 2) +
            (d / 2) ^ 2) := by
        apply mul_pos
        · linarith only [hhalfhi]
        · nlinarith only [sq_nonneg (d / 2), hhalfpos]
      nlinarith only [hp]
    have hqbound := sin_lower_cubic (d / 2) hhalfpos
    have hqlo : (0.0036974 : ℝ) < Real.sin (d / 2) := by
      nlinarith only [hqbound, hdlo, hhalfcube]
    have hqhi : Real.sin (d / 2) < (0.0036976 : ℝ) :=
      lt_of_le_of_lt (Real.sin_le hhalfpos.le) hhalfhi
    have hcos : Real.cos d = 1 - 2 * Real.sin (d / 2) ^ 2 :=
      cos_half_identity d
    have hclo : (0.99997265 : ℝ) < Real.cos d := by
      have hp : 0 < ((0.0036976 : ℝ) - Real.sin (d / 2)) *
          (0.0036976 + Real.sin (d / 2)) := by
        apply mul_pos
        · linarith only [hqhi]
        · linarith only [hqlo]
      nlinarith only [hcos, hp]
    have hchi : Real.cos d < (0.99997266 : ℝ) := by
      have hp : 0 < (Real.sin (d / 2) - (0.0036974 : ℝ)) *
          (Real.sin (d / 2) + 0.0036974) := by
        apply mul_pos
        · linarith only [hqlo]
        · linarith only [hqlo]
      nlinarith only [hcos, hp]
    have hs0 := Real.sqrt_nonneg 3
    have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hslo : (0.8660254 : ℝ) < Real.sqrt 3 / 2 := by
      nlinarith only [hs0, hs2]
    have hshi : Real.sqrt 3 / 2 < (0.8660255 : ℝ) := by
      nlinarith only [hs0, hs2]
    have hspos : 0 < Real.sqrt 3 / 2 := by
      linarith only [hslo]
    have hpLo : (0.8660254 : ℝ) * 0.99997265 <
        (Real.sqrt 3 / 2) * Real.cos d := by
      calc
        (0.8660254 : ℝ) * 0.99997265 <
            (Real.sqrt 3 / 2) * 0.99997265 :=
          mul_lt_mul_of_pos_right hslo (by norm_num)
        _ < (Real.sqrt 3 / 2) * Real.cos d :=
          mul_lt_mul_of_pos_left hclo hspos
    have hpHi : (Real.sqrt 3 / 2) * Real.cos d <
        (0.8660255 : ℝ) * 0.99997266 := by
      calc
        (Real.sqrt 3 / 2) * Real.cos d <
            (Real.sqrt 3 / 2) * 0.99997266 :=
          mul_lt_mul_of_pos_left hchi hspos
        _ < (0.8660255 : ℝ) * 0.99997266 :=
          mul_lt_mul_of_pos_right hshi (by norm_num)
    have hpLo' : (0.8660017 : ℝ) <
        (Real.sqrt 3 / 2) * Real.cos d := by
      exact lt_trans (by norm_num) hpLo
    have hpHi' : (Real.sqrt 3 / 2) * Real.cos d <
        (0.8660019 : ℝ) := by
      exact lt_trans hpHi (by norm_num)
    have hformula := sin_near_endpoint 2.087
    change Real.sin 2.087 =
      Real.sqrt 3 / 2 * Real.cos d + (1 / 2 : ℝ) * Real.sin d at hformula
    rw [Approx, f, abs_lt]
    norm_num
    constructor <;>
      linarith only [hformula, hpLo', hpHi', hsdlo, hsdhi]
theorem gap10 (x : ℝ) :
    deriv f x = 1 - 0.1 * Real.cos x := by
  exact deriv_f x
theorem gap11 (x : ℝ) :
    deriv (deriv f) x = 0.1 * Real.sin x := by
  exact deriv_deriv_f x
theorem gap12 (x : ℝ) (hx : x ∈ Set.Ioo (2 : ℝ) (2 * Real.pi / 3)) :
    0.1 * Real.sin x > 0 := by
  have hxpos : 0 < x := lt_trans (by norm_num) hx.1
  have hxpi : x < Real.pi := by
    have hp := Real.pi_pos
    nlinarith [hx.2]
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hxpos hxpi
  norm_num
  nlinarith
theorem gap13 :
    ∃ m₁ : ℝ, m₁ = 1 - 0.1 * Real.cos 2 := by
  exact ⟨1 - 0.1 * Real.cos 2, rfl⟩
theorem gap14 :
    sInf
        ((fun x : ℝ => |deriv f x|) ''
          Set.Ioo (2 : ℝ) (2 * Real.pi / 3)) =
      1 - 0.1 * Real.cos 2 := by
  let S : Set ℝ :=
    (fun x : ℝ => |deriv f x|) '' Set.Ioo (2 : ℝ) (2 * Real.pi / 3)
  let a : ℝ := 1 - 0.1 * Real.cos 2
  have horder : (2 : ℝ) < 2 * Real.pi / 3 := by
    nlinarith [Real.pi_gt_three]
  have hBdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact abs_nonneg _
  have hnonempty : S.Nonempty := by
    let x := (2 + 2 * Real.pi / 3) / 2
    have hx : x ∈ Set.Ioo (2 : ℝ) (2 * Real.pi / 3) := by
      dsimp [x]
      constructor <;> linarith
    exact ⟨|deriv f x|, ⟨x, hx, rfl⟩⟩
  have hpi2 : (2 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor
    · norm_num
    · nlinarith [Real.pi_gt_three]
  have hminor : a ≤ sInf S := by
    apply le_csInf hnonempty
    rintro y ⟨x, hx, rfl⟩
    have hxpi : x < Real.pi := by
      nlinarith [hx.2, Real.pi_pos]
    have hxmem : x ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨le_of_lt (lt_trans (by norm_num) hx.1), le_of_lt hxpi⟩
    have hcos : Real.cos x ≤ Real.cos 2 :=
      (Real.strictAntiOn_cos hpi2 hxmem hx.1).le
    have hpos : 0 < 1 - 0.1 * Real.cos x := by
      nlinarith [Real.cos_le_one x]
    change a ≤ |deriv f x|
    rw [deriv_f, abs_of_pos hpos]
    dsimp [a]
    nlinarith
  have hmajor : sInf S ≤ a := by
    by_contra hn
    have has : a < sInf S := lt_of_not_ge hn
    let d : ℝ := min (5 * (sInf S - a)) ((2 * Real.pi / 3 - 2) / 2)
    have hdpos : 0 < d := by
      dsimp [d]
      apply lt_min
      · nlinarith
      · nlinarith
    have hd1 : d ≤ 5 * (sInf S - a) := by
      dsimp [d]
      exact min_le_left _ _
    have hd2 : d ≤ (2 * Real.pi / 3 - 2) / 2 := by
      dsimp [d]
      exact min_le_right _ _
    let x : ℝ := 2 + d
    have hx : x ∈ Set.Ioo (2 : ℝ) (2 * Real.pi / 3) := by
      dsimp [x]
      constructor <;> nlinarith
    have hsle : sInf S ≤ |deriv f x| :=
      csInf_le hBdd ⟨x, hx, rfl⟩
    have hclose := Real.abs_cos_sub_cos_le x 2
    have hxdiff : |x - 2| = d := by
      dsimp [x]
      rw [show (2 : ℝ) + d - 2 = d by ring, abs_of_pos hdpos]
    rw [hxdiff] at hclose
    have hxpos : 0 < 1 - 0.1 * Real.cos x := by
      nlinarith [Real.cos_le_one x]
    have hsmall : |deriv f x| < sInf S := by
      rw [deriv_f, abs_of_pos hxpos]
      dsimp [a] at has hd1 ⊢
      rw [abs_le] at hclose
      nlinarith
    linarith
  change sInf S = a
  exact le_antisymm hmajor hminor
theorem gap15 :
    Approx (1 - 0.1 * Real.cos 2) 1.042 (1 / 1000) := by
  have h := gap1
  rw [Approx, abs_lt] at h
  norm_num [f] at h
  have hslo : (0.909 : ℝ) < Real.sin 2 := by linarith
  have hshi : Real.sin 2 < (0.911 : ℝ) := by linarith
  have hcneg : Real.cos 2 < 0 := by
    apply Real.cos_neg_of_pi_div_two_lt_of_lt
    · nlinarith [Real.pi_lt_four]
    · nlinarith [Real.pi_gt_three]
  have htrig := Real.sin_sq_add_cos_sq 2
  have hclo : (-0.43 : ℝ) < Real.cos 2 := by
    by_contra hn
    have hc : Real.cos 2 ≤ -0.43 := le_of_not_gt hn
    nlinarith [sq_nonneg (Real.sin 2 - 0.909), sq_nonneg (Real.cos 2 + 0.43)]
  have hchi : Real.cos 2 < (-0.41 : ℝ) := by
    by_contra hn
    have hc : -0.41 ≤ Real.cos 2 := le_of_not_gt hn
    nlinarith [sq_nonneg (Real.sin 2 - 0.911), sq_nonneg (Real.cos 2 + 0.41)]
  rw [Approx, abs_lt]
  norm_num
  constructor <;> nlinarith
theorem gap16 :
    ∃ m₁ : ℝ, m₁ = 1 - 0.1 * Real.cos 2 ∧ Approx m₁ 1.042 (1 / 1000) := by
  exact ⟨1 - 0.1 * Real.cos 2, rfl, gap15⟩
theorem gap17 :
    ∃ ξ₁ : ℝ, ξ₁ ∈ Set.Ioo (2 : ℝ) (2 * Real.pi / 3) ∧ f ξ₁ = 0 ∧
      |2.087 - ξ₁| ≤ |f 2.087| / (1 - 0.1 * Real.cos 2) := by
  rcases gap4 with ⟨r, hr, huniq⟩
  refine ⟨r, hr.1, hr.2, ?_⟩
  let m : ℝ := 1 - 0.1 * Real.cos 2
  let S : Set ℝ :=
    (fun x : ℝ => |deriv f x|) '' Set.Ioo (2 : ℝ) (2 * Real.pi / 3)
  have hmpos : 0 < m := by
    dsimp [m]
    nlinarith [Real.cos_le_one 2]
  have hBdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact abs_nonneg _
  have hm (x : ℝ) (hx : x ∈ Set.Ioo (2 : ℝ) (2 * Real.pi / 3)) :
      m ≤ |deriv f x| := by
    have hs : sInf S ≤ |deriv f x| := csInf_le hBdd ⟨x, hx, rfl⟩
    rw [gap14] at hs
    exact hs
  have hsamp : (2.087 : ℝ) ∈ Set.Ioo (2 : ℝ) (2 * Real.pi / 3) := by
    constructor
    · norm_num
    · nlinarith [Real.pi_gt_d20]
  by_cases heq : (2.087 : ℝ) = r
  · subst r
    have hnonneg : 0 ≤ |f 2.087| / m :=
      div_nonneg (abs_nonneg _) hmpos.le
    simpa using hnonneg
  rcases lt_or_gt_of_ne heq with hlt | hgt
  · obtain ⟨c, hc, hcder⟩ :=
      exists_deriv_eq_slope (f := f) hlt
        continuous_f.continuousOn differentiable_f.differentiableOn
    have hcI : c ∈ Set.Ioo (2 : ℝ) (2 * Real.pi / 3) :=
      ⟨lt_trans hsamp.1 hc.1, lt_trans hc.2 hr.1.2⟩
    have hmc := hm c hcI
    have hne : r - (2.087 : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
    have he : f r - f 2.087 = deriv f c * (r - 2.087) := by
      rw [hcder]
      field_simp [hne]
    have habs : |f 2.087| = |deriv f c| * |2.087 - r| := by
      calc
        |f 2.087| = |f r - f 2.087| := by rw [hr.2]; simp
        _ = |deriv f c| * |2.087 - r| := by
          rw [he, abs_mul, abs_sub_comm]
    apply (le_div_iff₀ hmpos).2
    calc
      |2.087 - r| * m ≤ |2.087 - r| * |deriv f c| :=
        mul_le_mul_of_nonneg_left hmc (abs_nonneg _)
      _ = |f 2.087| := by rw [mul_comm, ← habs]
  · obtain ⟨c, hc, hcder⟩ :=
      exists_deriv_eq_slope (f := f) hgt
        continuous_f.continuousOn differentiable_f.differentiableOn
    have hcI : c ∈ Set.Ioo (2 : ℝ) (2 * Real.pi / 3) :=
      ⟨lt_trans hr.1.1 hc.1, lt_trans hc.2 hsamp.2⟩
    have hmc := hm c hcI
    have hne : (2.087 : ℝ) - r ≠ 0 := ne_of_gt (sub_pos.mpr hgt)
    have he : f 2.087 - f r = deriv f c * (2.087 - r) := by
      rw [hcder]
      field_simp [hne]
    have habs : |f 2.087| = |deriv f c| * |2.087 - r| := by
      calc
        |f 2.087| = |f 2.087 - f r| := by rw [hr.2, sub_zero]
        _ = |deriv f c| * |2.087 - r| := by rw [he, abs_mul]
    apply (le_div_iff₀ hmpos).2
    calc
      |2.087 - r| * m ≤ |2.087 - r| * |deriv f c| :=
        mul_le_mul_of_nonneg_left hmc (abs_nonneg _)
      _ = |f 2.087| := by rw [mul_comm, ← habs]
theorem gap18 :
    |f 2.087| / (1 - 0.1 * Real.cos 2) < 0.001 := by
  have h := gap9
  rw [Approx, abs_lt] at h
  norm_num at h
  have hfpos : 0 < f 2.087 := by linarith
  have hfsmall : |f 2.087| < (0.0000301 : ℝ) := by
    rw [abs_of_pos hfpos]
    linarith
  have hm : (0.9 : ℝ) ≤ 1 - 0.1 * Real.cos 2 := by
    nlinarith [Real.cos_le_one 2]
  have hmpos : 0 < 1 - 0.1 * Real.cos 2 := by linarith
  apply (div_lt_iff₀ hmpos).2
  nlinarith
theorem gap19 : ApproxRoot 2.087 0.001 := by
  rw [ApproxRoot]
  rcases gap17 with ⟨r, hr, hfr, herr⟩
  refine ⟨r, hr, hfr, ?_⟩
  exact lt_of_le_of_lt herr gap18
theorem gap20 : ApproxRoot 2.087 0.001 := by
  exact gap19

end
end ProofGap.Exercise1619
