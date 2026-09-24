import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise1626_3

noncomputable section

def f (x : ℝ) : ℝ := Real.tan x - x
def a : ℝ := 111 * Real.pi / 32
def b : ℝ := 223 * Real.pi / 64
def interval : Set ℝ := Set.Ioo a b
def newton (x : ℝ) : ℝ := x - f x / (Real.tan x) ^ 2
def x₁ : ℝ := newton b
def x₂ : ℝ := newton x₁
def x₃ : ℝ := newton x₂
def m : ℝ := (Real.tan a) ^ 2
def Approx (u v ε : ℝ) : Prop := |u - v| < ε

private lemma cos_ne_interval (x : ℝ) (hx : x ∈ interval) :
    Real.cos x ≠ 0 := by
  let y := x - 3 * Real.pi
  have hy0 : 0 < y := by
    have hbase : 3 * Real.pi < a := by
      dsimp [a]
      nlinarith [Real.pi_pos]
    dsimp [y]
    exact sub_pos.mpr (lt_trans hbase hx.1)
  have hypi2 : y < Real.pi / 2 := by
    have htop : b < 3 * Real.pi + Real.pi / 2 := by
      dsimp [b]
      nlinarith [Real.pi_pos]
    dsimp [y]
    nlinarith [hx.2]
  have hcy : 0 < Real.cos y :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hypi2⟩
  have heq : Real.cos x = -Real.cos y := by
    rw [show x = ((y + Real.pi) + Real.pi) + Real.pi by simp [y]; ring]
    rw [Real.cos_add_pi, Real.cos_add_pi, Real.cos_add_pi]
    ring
  rw [heq]
  exact neg_ne_zero.mpr hcy.ne'

private lemma cos_ne_closed_interval (x : ℝ) (hx : x ∈ Set.Icc a b) :
    Real.cos x ≠ 0 := by
  let y := x - 3 * Real.pi
  have hy0 : 0 < y := by
    have hbase : 3 * Real.pi < a := by
      dsimp [a]
      nlinarith [Real.pi_pos]
    dsimp [y]
    exact sub_pos.mpr (lt_of_lt_of_le hbase hx.1)
  have hypi2 : y < Real.pi / 2 := by
    have htop : b < 3 * Real.pi + Real.pi / 2 := by
      dsimp [b]
      nlinarith [Real.pi_pos]
    dsimp [y]
    nlinarith [hx.2]
  have hcy : 0 < Real.cos y :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hypi2⟩
  have heq : Real.cos x = -Real.cos y := by
    rw [show x = ((y + Real.pi) + Real.pi) + Real.pi by simp [y]; ring]
    rw [Real.cos_add_pi, Real.cos_add_pi, Real.cos_add_pi]
    ring
  rw [heq]
  exact neg_ne_zero.mpr hcy.ne'

private lemma tan_pos_interval (x : ℝ) (hx : x ∈ interval) :
    0 < Real.tan x := by
  let y := x - 3 * Real.pi
  have hy0 : 0 < y := by
    have hbase : 3 * Real.pi < a := by
      dsimp [a]
      nlinarith [Real.pi_pos]
    dsimp [y]
    exact sub_pos.mpr (lt_trans hbase hx.1)
  have hypi2 : y < Real.pi / 2 := by
    have htop : b < 3 * Real.pi + Real.pi / 2 := by
      dsimp [b]
      nlinarith [Real.pi_pos]
    dsimp [y]
    nlinarith [hx.2]
  have hsy : 0 < Real.sin y :=
    Real.sin_pos_of_pos_of_lt_pi hy0 (lt_trans hypi2 (by nlinarith [Real.pi_pos]))
  have hcy : 0 < Real.cos y :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hypi2⟩
  rw [show x = ((y + Real.pi) + Real.pi) + Real.pi by simp [y]; ring]
  rw [Real.tan_add_pi, Real.tan_add_pi, Real.tan_add_pi]
  rw [Real.tan_eq_sin_div_cos]
  positivity

private lemma tan_hasDerivAt (x : ℝ) (hx : Real.cos x ≠ 0) :
    HasDerivAt Real.tan (1 / (Real.cos x) ^ 2) x := by
  rw [show Real.tan = fun y => Real.sin y / Real.cos y by
    funext y
    exact Real.tan_eq_sin_div_cos y]
  convert (Real.hasDerivAt_sin x).div (Real.hasDerivAt_cos x) hx using 1
  field_simp [hx]
  nlinarith [Real.sin_sq_add_cos_sq x]

private lemma deriv_f_pos (x : ℝ) (hx : x ∈ interval) :
    0 < deriv f x := by
  have hc := cos_ne_interval x hx
  have h := (tan_hasDerivAt x hc).sub (hasDerivAt_id x)
  have hderiv : deriv f x = (Real.tan x) ^ 2 := by
    unfold f
    calc
      deriv (fun y => Real.tan y - y) x = 1 / (Real.cos x) ^ 2 - 1 := by
        simpa [Pi.sub_apply, id] using h.deriv
      _ = (Real.tan x) ^ 2 := by
        rw [Real.tan_eq_sin_div_cos]
        field_simp [hc]
        nlinarith [Real.sin_sq_add_cos_sq x]
  rw [hderiv]
  exact sq_pos_of_pos (tan_pos_interval x hx)

theorem gap1 : f a < 0 := by
  let δ : ℝ := Real.pi / 32
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    nlinarith [Real.pi_lt_four]
  have hs0 : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδ0 (by dsimp [δ]; nlinarith [Real.pi_pos])
  have hs :
      δ - δ ^ 3 / 4 < Real.sin δ :=
    Real.sin_gt_sub_cube hδ0 hδ1
  have hc : Real.cos δ ≤ 1 := Real.cos_le_one δ
  have hpoly : 1 < a * (δ - δ ^ 3 / 4) := by
    have hpi2lo : (3.14 : ℝ) ^ 2 < Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_d2, Real.pi_pos]
    have hpi2hi : Real.pi ^ 2 < (16 : ℝ) := by
      nlinarith [Real.pi_lt_four, Real.pi_pos]
    have hfactor :
        (1 : ℝ) - 16 / 4096 < 1 - Real.pi ^ 2 / 4096 := by
      linarith
    have hprod :
        (3.14 : ℝ) ^ 2 * (1 - 16 / 4096) <
          Real.pi ^ 2 * (1 - Real.pi ^ 2 / 4096) := by
      calc
        (3.14 : ℝ) ^ 2 * (1 - 16 / 4096) <
            Real.pi ^ 2 * (1 - 16 / 4096) :=
          mul_lt_mul_of_pos_right hpi2lo (by norm_num)
        _ < Real.pi ^ 2 * (1 - Real.pi ^ 2 / 4096) :=
          mul_lt_mul_of_pos_left hfactor (sq_pos_of_pos Real.pi_pos)
    rw [show
      a * (δ - δ ^ 3 / 4) =
        (111 / 1024 : ℝ) * (Real.pi ^ 2 * (1 - Real.pi ^ 2 / 4096)) by
          dsimp [a, δ]
          ring]
    calc
      1 < (111 / 1024 : ℝ) * ((3.14 : ℝ) ^ 2 * (1 - 16 / 4096)) := by
        norm_num
      _ < (111 / 1024 : ℝ) * (Real.pi ^ 2 * (1 - Real.pi ^ 2 / 4096)) :=
        mul_lt_mul_of_pos_left hprod (by norm_num)
  have hratio : Real.cos δ / Real.sin δ < a := by
    rw [div_lt_iff₀ hs0]
    have ha0 : 0 < a := by unfold a; positivity
    nlinarith [mul_lt_mul_of_pos_left hs ha0]
  have htan : Real.tan a = Real.cos δ / Real.sin δ := by
    rw [show a = (((Real.pi / 2 - δ) + Real.pi) + Real.pi) + Real.pi by
      dsimp [a, δ]
      ring]
    rw [Real.tan_add_pi, Real.tan_add_pi, Real.tan_add_pi,
      Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos, inv_div]
  unfold f
  rw [htan]
  linarith

theorem gap2 : 0 < f b := by
  let δ : ℝ := Real.pi / 64
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδpi2 : δ < Real.pi / 2 := by
    dsimp [δ]
    nlinarith [Real.pi_pos]
  have hs0 : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδ0 (lt_trans hδpi2 (by nlinarith [Real.pi_pos]))
  have hs : Real.sin δ < δ := Real.sin_lt hδ0
  have hc : 1 - δ ^ 2 / 2 < Real.cos δ :=
    Real.one_sub_sq_div_two_lt_cos hδ0.ne'
  have hpoly : b * δ < 1 - δ ^ 2 / 2 := by
    dsimp [b, δ]
    nlinarith [Real.pi_lt_four, Real.pi_pos, sq_nonneg (4 - Real.pi)]
  have hratio : b < Real.cos δ / Real.sin δ := by
    rw [lt_div_iff₀ hs0]
    have hb0 : 0 < b := by dsimp [b]; positivity
    nlinarith [mul_lt_mul_of_pos_left hs hb0]
  have htan : Real.tan b = Real.cos δ / Real.sin δ := by
    rw [show b = (((Real.pi / 2 - δ) + Real.pi) + Real.pi) + Real.pi by
      dsimp [b, δ]
      ring]
    rw [Real.tan_add_pi, Real.tan_add_pi, Real.tan_add_pi,
      Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos, inv_div]
  unfold f
  rw [htan]
  linarith

theorem gap3 :
    ∃! ξ : ℝ, ξ ∈ interval ∧ f ξ = 0 := by
  have hab : a < b := by
    dsimp [a, b]
    nlinarith [Real.pi_pos]
  have hcont : ContinuousOn f (Set.Icc a b) := by
    unfold f
    apply ContinuousOn.sub
    · exact Real.continuousOn_tan.mono (by
        intro x hx
        exact cos_ne_closed_interval x hx)
    · exact continuousOn_id
  have hz : (0 : ℝ) ∈ Set.Icc (f a) (f b) :=
    ⟨gap1.le, gap2.le⟩
  rcases intermediate_value_Icc hab.le hcont hz with ⟨ξ, hξ, hroot⟩
  have haξ : a < ξ := lt_of_le_of_ne hξ.1 (by
    intro ha
    subst ξ
    linarith [gap1])
  have hξb : ξ < b := lt_of_le_of_ne hξ.2 (by
    intro hb
    subst ξ
    linarith [gap2])
  have hmono : StrictMonoOn f interval :=
    strictMonoOn_of_deriv_pos (convex_Ioo a b)
      (hcont.mono Set.Ioo_subset_Icc_self)
      (fun x hx => deriv_f_pos x (interior_subset hx))
  refine ⟨ξ, ⟨⟨haξ, hξb⟩, hroot⟩, ?_⟩
  intro y hy
  exact (hmono.injOn ⟨haξ, hξb⟩ hy.1 (hroot.trans hy.2.symm)).symm

theorem gap4 (x : ℝ) (hx : x ∈ interval) :
    0 < deriv f x := by
  exact deriv_f_pos x hx

theorem gap5 (x : ℝ) (hx : x ∈ interval) :
    0 < deriv (deriv f) x := by
  have hlocal : deriv f =ᶠ[nhds x] fun y => (Real.tan y) ^ 2 := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    have hc := cos_ne_interval y hy
    have h := (tan_hasDerivAt y hc).sub (hasDerivAt_id y)
    unfold f
    calc
      deriv (fun z => Real.tan z - z) y = 1 / (Real.cos y) ^ 2 - 1 := by
        simpa [Pi.sub_apply, id] using h.deriv
      _ = (Real.tan y) ^ 2 := by
        rw [Real.tan_eq_sin_div_cos]
        field_simp [hc]
        nlinarith [Real.sin_sq_add_cos_sq y]
  rw [hlocal.deriv_eq]
  have hc := cos_ne_interval x hx
  have h := (tan_hasDerivAt x hc).pow 2
  have hderiv :
      deriv (fun y => (Real.tan y) ^ 2) x =
        2 * Real.tan x * (1 / (Real.cos x) ^ 2) := by
    simpa [Pi.pow_apply] using h.deriv
  rw [hderiv]
  have ht := tan_pos_interval x hx
  have hsec : 0 < 1 / (Real.cos x) ^ 2 := by positivity
  positivity

private def sinLower (l u : ℝ) : ℝ :=
  l - u ^ 3 / 6 - u ^ 4 * (5 / 96)

private def sinUpper (l u : ℝ) : ℝ :=
  u - l ^ 3 / 6 + u ^ 4 * (5 / 96)

private def sinLowerQuarter (l u : ℝ) : ℝ :=
  2 * sinLower (l / 2) (u / 2) *
    (1 - 2 * (sinUpper (l / 4) (u / 4)) ^ 2)

private def sinUpperQuarter (l u : ℝ) : ℝ :=
  2 * sinUpper (l / 2) (u / 2) *
    (1 - 2 * (sinLower (l / 4) (u / 4)) ^ 2)

private def cosLowerQuarter (l u : ℝ) : ℝ :=
  1 - 2 * (sinUpper (l / 2) (u / 2)) ^ 2

private def cosUpperQuarter (l u : ℝ) : ℝ :=
  1 - 2 * (sinLower (l / 2) (u / 2)) ^ 2

private lemma sin_interval {t l u : ℝ}
    (hl : 0 ≤ l) (hlt : l < t) (htu : t < u) (hu : u ≤ 1) :
    sinLower l u < Real.sin t ∧ Real.sin t < sinUpper l u := by
  have ht0 : 0 ≤ t := le_trans hl hlt.le
  have ht1 : t ≤ 1 := htu.le.trans hu
  have hs := Real.sin_bound (x := t)
    (by simpa [abs_of_nonneg ht0] using ht1)
  rw [abs_of_nonneg ht0, abs_le] at hs
  have h3lo : l ^ 3 < t ^ 3 := by gcongr
  have h3hi : t ^ 3 < u ^ 3 := by gcongr
  have h4 : t ^ 4 < u ^ 4 := by gcongr
  unfold sinLower sinUpper
  constructor <;> nlinarith [hs.1, hs.2]

private lemma sin_cos_bounds_quarter {z l u : ℝ}
    (hl : 0 ≤ l) (hlt : l < z) (htu : z < u) (hu : u ≤ 1)
    (hhalfLower : 0 < sinLower (l / 2) (u / 2))
    (hhalfUpper : 0 < sinUpper (l / 2) (u / 2))
    (hquarterLower : 0 < sinLower (l / 4) (u / 4))
    (hquarterUpper : 0 < sinUpper (l / 4) (u / 4))
    (hcosHalfLower :
      0 < 1 - 2 * (sinUpper (l / 4) (u / 4)) ^ 2) :
    sinLowerQuarter l u < Real.sin z ∧
      Real.sin z < sinUpperQuarter l u ∧
      cosLowerQuarter l u < Real.cos z ∧
      Real.cos z < cosUpperQuarter l u := by
  have hhalf :
      sinLower (l / 2) (u / 2) < Real.sin (z / 2) ∧
        Real.sin (z / 2) < sinUpper (l / 2) (u / 2) := by
    apply sin_interval (l := l / 2) (u := u / 2)
    · positivity
    · linarith
    · linarith
    · linarith
  have hquarter :
      sinLower (l / 4) (u / 4) < Real.sin (z / 4) ∧
        Real.sin (z / 4) < sinUpper (l / 4) (u / 4) := by
    apply sin_interval (l := l / 4) (u := u / 4)
    · positivity
    · linarith
    · linarith
    · linarith
  have hquarterSinPos : 0 < Real.sin (z / 4) :=
    lt_trans hquarterLower hquarter.1
  have hhalfSinPos : 0 < Real.sin (z / 2) :=
    lt_trans hhalfLower hhalf.1
  have hquarterLowerSq :
      (sinLower (l / 4) (u / 4)) ^ 2 <
        (Real.sin (z / 4)) ^ 2 :=
    pow_lt_pow_left₀ hquarter.1 hquarterLower.le (by norm_num)
  have hquarterUpperSq :
      (Real.sin (z / 4)) ^ 2 <
        (sinUpper (l / 4) (u / 4)) ^ 2 :=
    pow_lt_pow_left₀ hquarter.2 hquarterSinPos.le (by norm_num)
  have hcosHalf :
      1 - 2 * (sinUpper (l / 4) (u / 4)) ^ 2 <
          Real.cos (z / 2) ∧
        Real.cos (z / 2) <
          1 - 2 * (sinLower (l / 4) (u / 4)) ^ 2 := by
    rw [show Real.cos (z / 2) =
      1 - 2 * (Real.sin (z / 4)) ^ 2 by
        calc
          Real.cos (z / 2) =
              Real.cos (z / 4 + z / 4) := by congr 1 <;> ring
          _ = Real.cos (z / 4) * Real.cos (z / 4) -
              Real.sin (z / 4) * Real.sin (z / 4) := by
                rw [Real.cos_add]
          _ = 1 - 2 * (Real.sin (z / 4)) ^ 2 := by
                nlinarith [Real.sin_sq_add_cos_sq (z / 4)]]
    constructor <;> nlinarith
  have hcosHalfPos : 0 < Real.cos (z / 2) :=
    lt_trans hcosHalfLower hcosHalf.1
  have hsinLower :
      sinLowerQuarter l u < Real.sin z := by
    rw [show Real.sin z =
      2 * Real.sin (z / 2) * Real.cos (z / 2) by
        rw [show z = z / 2 + z / 2 by ring, Real.sin_add]
        ring]
    unfold sinLowerQuarter
    calc
      2 * sinLower (l / 2) (u / 2) *
          (1 - 2 * sinUpper (l / 4) (u / 4) ^ 2) <
          2 * Real.sin (z / 2) *
            (1 - 2 * sinUpper (l / 4) (u / 4) ^ 2) := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_left hhalf.1 (by norm_num))
          hcosHalfLower
      _ < 2 * Real.sin (z / 2) * Real.cos (z / 2) := by
        exact mul_lt_mul_of_pos_left hcosHalf.1
          (mul_pos (by norm_num) hhalfSinPos)
  have hsinUpper :
      Real.sin z < sinUpperQuarter l u := by
    rw [show Real.sin z =
      2 * Real.sin (z / 2) * Real.cos (z / 2) by
        rw [show z = z / 2 + z / 2 by ring, Real.sin_add]
        ring]
    unfold sinUpperQuarter
    calc
      2 * Real.sin (z / 2) * Real.cos (z / 2) <
          2 * sinUpper (l / 2) (u / 2) *
            Real.cos (z / 2) := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_left hhalf.2 (by norm_num))
          hcosHalfPos
      _ < 2 * sinUpper (l / 2) (u / 2) *
          (1 - 2 * sinLower (l / 4) (u / 4) ^ 2) := by
        exact mul_lt_mul_of_pos_left hcosHalf.2
          (mul_pos (by norm_num) hhalfUpper)
  have hhalfLowerSq :
      (sinLower (l / 2) (u / 2)) ^ 2 <
        (Real.sin (z / 2)) ^ 2 :=
    pow_lt_pow_left₀ hhalf.1 hhalfLower.le (by norm_num)
  have hhalfUpperSq :
      (Real.sin (z / 2)) ^ 2 <
        (sinUpper (l / 2) (u / 2)) ^ 2 :=
    pow_lt_pow_left₀ hhalf.2 hhalfSinPos.le (by norm_num)
  have hcos :
      cosLowerQuarter l u < Real.cos z ∧
        Real.cos z < cosUpperQuarter l u := by
    rw [show Real.cos z =
      1 - 2 * (Real.sin (z / 2)) ^ 2 by
        calc
          Real.cos z = Real.cos (z / 2 + z / 2) := by
            congr 1 <;> ring
          _ = Real.cos (z / 2) * Real.cos (z / 2) -
              Real.sin (z / 2) * Real.sin (z / 2) := by
                rw [Real.cos_add]
          _ = 1 - 2 * (Real.sin (z / 2)) ^ 2 := by
                nlinarith [Real.sin_sq_add_cos_sq (z / 2)]]
    unfold cosLowerQuarter cosUpperQuarter
    constructor <;> nlinarith
  exact ⟨hsinLower, hsinUpper, hcos.1, hcos.2⟩

private lemma tan_near_pole_bounds {x l u tl tu : ℝ}
    (hl : 0 ≤ l)
    (hdeltaLower : l < 7 * Real.pi / 2 - x)
    (hdeltaUpper : 7 * Real.pi / 2 - x < u)
    (hu : u ≤ 1)
    (htl : 0 ≤ tl)
    (htu : 0 ≤ tu)
    (hhalfLower : 0 < sinLower (l / 2) (u / 2))
    (hhalfUpper : 0 < sinUpper (l / 2) (u / 2))
    (hquarterLower : 0 < sinLower (l / 4) (u / 4))
    (hquarterUpper : 0 < sinUpper (l / 4) (u / 4))
    (hcosHalfLower :
      0 < 1 - 2 * (sinUpper (l / 4) (u / 4)) ^ 2)
    (hlower :
      tl * sinUpperQuarter l u < cosLowerQuarter l u)
    (hupper :
      cosUpperQuarter l u < tu * sinLowerQuarter l u) :
    tl < Real.tan x ∧ Real.tan x < tu := by
  let z := 7 * Real.pi / 2 - x
  have hsc := sin_cos_bounds_quarter hl
    (by simpa [z] using hdeltaLower)
    (by simpa [z] using hdeltaUpper) hu
    hhalfLower hhalfUpper hquarterLower hquarterUpper hcosHalfLower
  have hsinLowerPos : 0 < sinLowerQuarter l u := by
    unfold sinLowerQuarter
    positivity
  have hsinPos : 0 < Real.sin z :=
    lt_trans hsinLowerPos hsc.1
  have htan : Real.tan x = Real.cos z / Real.sin z := by
    rw [Real.tan_eq_sin_div_cos]
    have hsx : Real.sin x = -Real.cos z := by
      rw [show x =
        (((Real.pi / 2 - z) + Real.pi) + Real.pi) + Real.pi by
          dsimp [z]
          ring]
      rw [Real.sin_add_pi, Real.sin_add_pi, Real.sin_add_pi,
        Real.sin_pi_div_two_sub]
      ring
    have hcx : Real.cos x = -Real.sin z := by
      rw [show x =
        (((Real.pi / 2 - z) + Real.pi) + Real.pi) + Real.pi by
          dsimp [z]
          ring]
      rw [Real.cos_add_pi, Real.cos_add_pi, Real.cos_add_pi,
        Real.cos_pi_div_two_sub]
      ring
    rw [hsx, hcx]
    ring
  rw [htan]
  constructor
  · rw [lt_div_iff₀ hsinPos]
    calc
      tl * Real.sin z ≤ tl * sinUpperQuarter l u := by
        exact mul_le_mul_of_nonneg_left hsc.2.1.le htl
      _ < cosLowerQuarter l u := hlower
      _ < Real.cos z := hsc.2.2.1
  · rw [div_lt_iff₀ hsinPos]
    calc
      Real.cos z < cosUpperQuarter l u := hsc.2.2.2
      _ < tu * sinLowerQuarter l u := hupper
      _ ≤ tu * Real.sin z := by
        exact mul_le_mul_of_nonneg_left hsc.1.le htu

private def newtonAux (x t : ℝ) : ℝ :=
  x - (t - x) / t ^ 2

private lemma newtonAux_bounds_of_box
    {x xl xu t tl tu yl yu : ℝ}
    (hxl0 : 0 < xl) (hxlxu : xl < xu) (hxultl : xu < tl)
    (htltu : tl < tu) (htu2xl : tu < 2 * xl)
    (hxl : xl < x) (hxu : x < xu)
    (htl' : tl < t) (htu' : t < tu)
    (hcornerLower : yl < newtonAux xl tu)
    (hcornerUpper : newtonAux xu tl < yu) :
    yl < newtonAux x t ∧ newtonAux x t < yu := by
  have ht0 : 0 < t := lt_trans (lt_trans (lt_trans hxl0 hxlxu) hxultl) htl'
  have htl0 : 0 < tl := lt_trans (lt_trans hxl0 hxlxu) hxultl
  have htu0 : 0 < tu := lt_trans htl0 htltu
  have htne : t ≠ 0 := ne_of_gt ht0
  have htlne : tl ≠ 0 := ne_of_gt htl0
  have htune : tu ≠ 0 := ne_of_gt htu0
  have hmonoXLower :
      newtonAux xl t < newtonAux x t := by
    have hid :
        newtonAux x t - newtonAux xl t =
          (x - xl) * (1 + 1 / t ^ 2) := by
      unfold newtonAux
      field_simp [htne]
      ring
    have hp : 0 < newtonAux x t - newtonAux xl t := by
      rw [hid]
      exact mul_pos (sub_pos.mpr hxl) (by positivity)
    linarith
  have hmonoXUpper :
      newtonAux x t < newtonAux xu t := by
    have hid :
        newtonAux xu t - newtonAux x t =
          (xu - x) * (1 + 1 / t ^ 2) := by
      unfold newtonAux
      field_simp [htne]
      ring
    have hp : 0 < newtonAux xu t - newtonAux x t := by
      rw [hid]
      exact mul_pos (sub_pos.mpr hxu) (by positivity)
    linarith
  have htuX : xl < tu := lt_trans (lt_trans hxlxu hxultl) htltu
  have hcoefLower :
      0 < xl * (tu + t) - t * tu := by
    have hid :
        xl * (tu + t) - t * tu =
          tu * (2 * xl - tu) + (tu - t) * (tu - xl) := by ring
    rw [hid]
    exact add_pos
      (mul_pos htu0 (sub_pos.mpr htu2xl))
      (mul_pos (sub_pos.mpr htu') (sub_pos.mpr htuX))
  have hmonoTLower :
      newtonAux xl tu < newtonAux xl t := by
    have hid :
        newtonAux xl t - newtonAux xl tu =
          (tu - t) * (xl * (tu + t) - t * tu) /
            (t ^ 2 * tu ^ 2) := by
      unfold newtonAux
      field_simp [htne, htune]
      ring
    have hp : 0 < newtonAux xl t - newtonAux xl tu := by
      rw [hid]
      exact div_pos
        (mul_pos (sub_pos.mpr htu') hcoefLower)
        (mul_pos (sq_pos_of_pos ht0) (sq_pos_of_pos htu0))
    linarith
  have htxu : xu < t := lt_trans hxultl htl'
  have ht2xu : t < 2 * xu := by
    exact lt_trans htu' (lt_trans htu2xl (by linarith))
  have hcoefUpper :
      0 < xu * (t + tl) - tl * t := by
    have hid :
        xu * (t + tl) - tl * t =
          t * (2 * xu - t) + (t - tl) * (t - xu) := by ring
    rw [hid]
    exact add_pos
      (mul_pos ht0 (sub_pos.mpr ht2xu))
      (mul_pos (sub_pos.mpr htl') (sub_pos.mpr htxu))
  have hmonoTUpper :
      newtonAux xu t < newtonAux xu tl := by
    have hid :
        newtonAux xu tl - newtonAux xu t =
          (t - tl) * (xu * (t + tl) - tl * t) /
            (tl ^ 2 * t ^ 2) := by
      unfold newtonAux
      field_simp [htne, htlne]
      ring
    have hp : 0 < newtonAux xu tl - newtonAux xu t := by
      rw [hid]
      exact div_pos
        (mul_pos (sub_pos.mpr htl') hcoefUpper)
        (mul_pos (sq_pos_of_pos htl0) (sq_pos_of_pos ht0))
    linarith
  exact ⟨lt_trans hcornerLower (lt_trans hmonoTLower hmonoXLower),
    lt_trans hmonoXUpper (lt_trans hmonoTUpper hcornerUpper)⟩

private lemma tan_b_bounds :
    (20.3554 : ℝ) < Real.tan b ∧ Real.tan b < 20.3556 := by
  apply tan_near_pole_bounds
      (l := (0.04908738 : ℝ)) (u := (0.04908740 : ℝ))
  · norm_num
  · unfold b
    norm_num at ⊢
    nlinarith [Real.pi_gt_d20]
  · unfold b
    norm_num at ⊢
    nlinarith [Real.pi_lt_d20]
  · norm_num
  · norm_num
  · norm_num
  · norm_num [sinLower]
  · norm_num [sinUpper]
  · norm_num [sinLower]
  · norm_num [sinUpper]
  · norm_num [sinUpper]
  · norm_num [sinUpperQuarter, cosLowerQuarter, sinLower, sinUpper]
  · norm_num [sinLowerQuarter, cosUpperQuarter, sinLower, sinUpper]

private lemma x₁_bounds :
    (10.92375 : ℝ) < x₁ ∧ x₁ < 10.92381 := by
  have hb : (10.94648 : ℝ) < b ∧ b < 10.94649 := by
    constructor
    · unfold b
      nlinarith [Real.pi_gt_d20]
    · unfold b
      nlinarith [Real.pi_lt_d20]
  have ht := tan_b_bounds
  have hbox := newtonAux_bounds_of_box
    (x := b) (t := Real.tan b)
    (xl := (10.94648 : ℝ)) (xu := (10.94649 : ℝ))
    (tl := (20.3554 : ℝ)) (tu := (20.3556 : ℝ))
    (yl := (10.92375 : ℝ)) (yu := (10.92381 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hb.1 hb.2 ht.1 ht.2
    (by norm_num [newtonAux]) (by norm_num [newtonAux])
  simpa [x₁, newton, f, newtonAux] using hbox

private lemma tan_x₁_bounds :
    (13.898 : ℝ) < Real.tan x₁ ∧ Real.tan x₁ < 13.912 := by
  apply tan_near_pole_bounds
      (l := (0.07176428 : ℝ)) (u := (0.07182430 : ℝ))
  · norm_num
  · nlinarith [x₁_bounds.2, Real.pi_gt_d20]
  · nlinarith [x₁_bounds.1, Real.pi_lt_d20]
  · norm_num
  · norm_num
  · norm_num
  · norm_num [sinLower]
  · norm_num [sinUpper]
  · norm_num [sinLower]
  · norm_num [sinUpper]
  · norm_num [sinUpper]
  · norm_num [sinUpperQuarter, cosLowerQuarter, sinLower, sinUpper]
  · norm_num [sinLowerQuarter, cosUpperQuarter, sinLower, sinUpper]

private lemma x₂_bounds :
    (10.90830 : ℝ) < x₂ ∧ x₂ < 10.90843 := by
  have hbox := newtonAux_bounds_of_box
    (x := x₁) (t := Real.tan x₁)
    (xl := (10.92375 : ℝ)) (xu := (10.92381 : ℝ))
    (tl := (13.898 : ℝ)) (tu := (13.912 : ℝ))
    (yl := (10.90830 : ℝ)) (yu := (10.90843 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) x₁_bounds.1 x₁_bounds.2
    tan_x₁_bounds.1 tan_x₁_bounds.2
    (by norm_num [newtonAux]) (by norm_num [newtonAux])
  simpa [x₂, newton, f, newtonAux] using hbox

private lemma tan_x₂_bounds :
    (11.428 : ℝ) < Real.tan x₂ ∧ Real.tan x₂ < 11.447 := by
  apply tan_near_pole_bounds
      (l := (0.08714428 : ℝ)) (u := (0.08727430 : ℝ))
  · norm_num
  · nlinarith [x₂_bounds.2, Real.pi_gt_d20]
  · nlinarith [x₂_bounds.1, Real.pi_lt_d20]
  · norm_num
  · norm_num
  · norm_num
  · norm_num [sinLower]
  · norm_num [sinUpper]
  · norm_num [sinLower]
  · norm_num [sinUpper]
  · norm_num [sinUpper]
  · norm_num [sinUpperQuarter, cosLowerQuarter, sinLower, sinUpper]
  · norm_num [sinLowerQuarter, cosUpperQuarter, sinLower, sinUpper]

private lemma x₃_bounds :
    (10.90418 : ℝ) < x₃ ∧ x₃ < 10.90446 := by
  have hbox := newtonAux_bounds_of_box
    (x := x₂) (t := Real.tan x₂)
    (xl := (10.90830 : ℝ)) (xu := (10.90843 : ℝ))
    (tl := (11.428 : ℝ)) (tu := (11.447 : ℝ))
    (yl := (10.90418 : ℝ)) (yu := (10.90446 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) x₂_bounds.1 x₂_bounds.2
    tan_x₂_bounds.1 tan_x₂_bounds.2
    (by norm_num [newtonAux]) (by norm_num [newtonAux])
  simpa [x₃, newton, f, newtonAux] using hbox

theorem gap6 : Approx x₁ 10.9233 0.001 := by
  rw [Approx, abs_lt]
  constructor <;> nlinarith [x₁_bounds.1, x₁_bounds.2]

theorem gap7 : Approx x₂ 10.9086 0.001 := by
  rw [Approx, abs_lt]
  constructor <;> nlinarith [x₂_bounds.1, x₂_bounds.2]

theorem gap8 : Approx x₃ 10.9041 0.001 := by
  rw [Approx, abs_lt]
  constructor <;> nlinarith [x₃_bounds.1, x₃_bounds.2]

private lemma tan_109041_bounds :
    (10.9014 : ℝ) < Real.tan 10.9041 ∧
      Real.tan 10.9041 < 10.9017 := by
  apply tan_near_pole_bounds
      (l := (0.09147428 : ℝ)) (u := (0.09147430 : ℝ))
  · norm_num
  · norm_num at ⊢
    nlinarith [Real.pi_gt_d20]
  · norm_num at ⊢
    nlinarith [Real.pi_lt_d20]
  · norm_num
  · norm_num
  · norm_num
  · norm_num [sinLower]
  · norm_num [sinUpper]
  · norm_num [sinLower]
  · norm_num [sinUpper]
  · norm_num [sinUpper]
  · norm_num [sinUpperQuarter, cosLowerQuarter, sinLower, sinUpper]
  · norm_num [sinLowerQuarter, cosUpperQuarter, sinLower, sinUpper]

theorem gap9 : |f 10.9041| < 0.014 := by
  rw [abs_lt]
  unfold f
  constructor <;> nlinarith [tan_109041_bounds.1, tan_109041_bounds.2]

theorem gap10 : m = (Real.tan a) ^ 2 := by rfl

theorem gap11 : Approx m 102.78 1 := by
  let δ : ℝ := Real.pi / 32
  let lo : ℝ := (3.1415 : ℝ) / 32
  let hi : ℝ := (3.15 : ℝ) / 32
  let c : ℝ := (511 : ℝ) / 512
  let q : ℝ := 1 - hi ^ 2 / 6 - hi ^ 3 * (5 / 96)
  let L : ℝ := δ - δ ^ 3 / 6 - δ ^ 4 * (5 / 96)
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hloδ : lo < δ := by
    dsimp [lo, δ]
    linarith [Real.pi_gt_d4]
  have hδhi : δ < hi := by
    dsimp [δ, hi]
    linarith [Real.pi_lt_d2]
  have hδ1 : |δ| ≤ 1 := by
    rw [abs_of_pos hδ0]
    dsimp [δ]
    nlinarith [Real.pi_lt_four]
  have hδ2 : δ ^ 2 < hi ^ 2 :=
    pow_lt_pow_left₀ hδhi hδ0.le (by norm_num)
  have hδ3 : δ ^ 3 < hi ^ 3 :=
    pow_lt_pow_left₀ hδhi hδ0.le (by norm_num)
  have hqfactor : q < 1 - δ ^ 2 / 6 - δ ^ 3 * (5 / 96) := by
    have h2 : δ ^ 2 / 6 < hi ^ 2 / 6 :=
      div_lt_div_of_pos_right hδ2 (by norm_num)
    have h3 : δ ^ 3 * (5 / 96) < hi ^ 3 * (5 / 96) :=
      mul_lt_mul_of_pos_right hδ3 (by norm_num)
    dsimp [q]
    linarith
  have hq0 : 0 < q := by
    dsimp [q, hi]
    norm_num
  have hLlower : lo * q < L := by
    calc
      lo * q < δ * q := mul_lt_mul_of_pos_right hloδ hq0
      _ < δ * (1 - δ ^ 2 / 6 - δ ^ 3 * (5 / 96)) :=
        mul_lt_mul_of_pos_left hqfactor hδ0
      _ = L := by dsimp [L]; ring
  have hloq0 : 0 < lo * q := by
    apply mul_pos
    · dsimp [lo]; norm_num
    · exact hq0
  have hsinlower : L ≤ Real.sin δ := by
    have hb := Real.sin_bound hδ1
    rw [abs_of_pos hδ0] at hb
    have hb' := neg_le_of_abs_le hb
    dsimp [L]
    linarith
  have hs0 : 0 < Real.sin δ := by
    exact Real.sin_pos_of_pos_of_lt_pi hδ0 (by dsimp [δ]; nlinarith [Real.pi_pos])
  have hc0 : 0 < Real.cos δ :=
    Real.cos_pos_of_mem_Ioo ⟨by dsimp [δ]; nlinarith [Real.pi_pos],
      by dsimp [δ]; nlinarith [Real.pi_pos]⟩
  have hcupper : Real.cos δ ≤ c := by
    calc
      Real.cos δ ≤ 1 - 2 / Real.pi ^ 2 * δ ^ 2 :=
        Real.cos_le_one_sub_mul_cos_sq (by
          rw [abs_of_pos hδ0]
          dsimp [δ]
          nlinarith [Real.pi_pos])
      _ = c := by
        dsimp [δ, c]
        field_simp [Real.pi_ne_zero]
        ring
  have hnum : c ^ 2 < (103.78 : ℝ) * (lo * q) ^ 2 := by
    dsimp [c, lo, q, hi]
    norm_num
  have hloqL2 : (lo * q) ^ 2 < L ^ 2 :=
    pow_lt_pow_left₀ hLlower hloq0.le (by norm_num)
  have hLsin2 : L ^ 2 ≤ Real.sin δ ^ 2 :=
    pow_le_pow_left₀ (le_trans hloq0.le hLlower.le) hsinlower 2
  have hcos2 : Real.cos δ ^ 2 ≤ c ^ 2 :=
    pow_le_pow_left₀ hc0.le hcupper 2
  have hratio : (Real.cos δ / Real.sin δ) ^ 2 < (103.78 : ℝ) := by
    rw [div_pow, div_lt_iff₀ (sq_pos_of_pos hs0)]
    calc
      Real.cos δ ^ 2 ≤ c ^ 2 := hcos2
      _ < (103.78 : ℝ) * (lo * q) ^ 2 := hnum
      _ < (103.78 : ℝ) * L ^ 2 :=
        mul_lt_mul_of_pos_left hloqL2 (by norm_num)
      _ ≤ (103.78 : ℝ) * Real.sin δ ^ 2 :=
        mul_le_mul_of_nonneg_left hLsin2 (by norm_num)
  have hs2 : Real.sin δ ^ 2 < δ ^ 2 :=
    Real.sin_sq_lt_sq hδ0.ne'
  have hsmall : 103 * δ ^ 2 < 1 := by
    have hconst : 103 * hi ^ 2 < (1 : ℝ) := by
      dsimp [hi]
      norm_num
    exact lt_trans (mul_lt_mul_of_pos_left hδ2 (by norm_num)) hconst
  have hclower : 1 - δ ^ 2 / 2 < Real.cos δ :=
    Real.one_sub_sq_div_two_lt_cos hδ0.ne'
  have hclower0 : 0 < 1 - δ ^ 2 / 2 := by
    nlinarith [hsmall]
  have hclower2 : (1 - δ ^ 2 / 2) ^ 2 < Real.cos δ ^ 2 :=
    pow_lt_pow_left₀ hclower hclower0.le (by norm_num)
  have hpolyLower : 102 * δ ^ 2 < (1 - δ ^ 2 / 2) ^ 2 := by
    nlinarith [sq_nonneg (δ ^ 2 / 2)]
  have hratioLower : 102 < (Real.cos δ / Real.sin δ) ^ 2 := by
    rw [div_pow, lt_div_iff₀ (sq_pos_of_pos hs0)]
    calc
      102 * Real.sin δ ^ 2 < 102 * δ ^ 2 :=
        mul_lt_mul_of_pos_left hs2 (by norm_num)
      _ < (1 - δ ^ 2 / 2) ^ 2 := hpolyLower
      _ < Real.cos δ ^ 2 := hclower2
  have htan : Real.tan a = Real.cos δ / Real.sin δ := by
    rw [show a = (((Real.pi / 2 - δ) + Real.pi) + Real.pi) + Real.pi by
      dsimp [a, δ]
      ring]
    rw [Real.tan_add_pi, Real.tan_add_pi, Real.tan_add_pi,
      Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos, inv_div]
  rw [Approx, abs_lt]
  constructor
  · have hmlo : 102 < m := by
      unfold m
      rw [htan]
      exact hratioLower
    norm_num at ⊢
    linarith only [hmlo]
  · unfold m
    rw [htan]
    norm_num at ⊢
    linarith only [hratio]

theorem gap12 : 102 < m := by
  let δ : ℝ := Real.pi / 32
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδlt : δ < (3.15 : ℝ) / 32 := by
    dsimp [δ]
    linarith [Real.pi_lt_d2]
  have hδ2 : δ ^ 2 < ((3.15 : ℝ) / 32) ^ 2 :=
    pow_lt_pow_left₀ hδlt hδ0.le (by norm_num)
  have hsmall : 103 * δ ^ 2 < 1 := by
    nlinarith
  have hpoly : 102 * δ ^ 2 < (1 - δ ^ 2 / 2) ^ 2 := by
    nlinarith [sq_nonneg (δ ^ 2 / 2)]
  have hs0 : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδ0 (by dsimp [δ]; nlinarith [Real.pi_pos])
  have hs2 : Real.sin δ ^ 2 < δ ^ 2 :=
    Real.sin_sq_lt_sq hδ0.ne'
  have hclower : 1 - δ ^ 2 / 2 < Real.cos δ :=
    Real.one_sub_sq_div_two_lt_cos hδ0.ne'
  have hclower0 : 0 < 1 - δ ^ 2 / 2 := by
    nlinarith [hsmall]
  have hc2 : (1 - δ ^ 2 / 2) ^ 2 < Real.cos δ ^ 2 :=
    pow_lt_pow_left₀ hclower hclower0.le (by norm_num)
  have hsq : 102 * Real.sin δ ^ 2 < Real.cos δ ^ 2 := by
    nlinarith
  have hratio : 102 < (Real.cos δ / Real.sin δ) ^ 2 := by
    rw [div_pow, lt_div_iff₀ (sq_pos_of_pos hs0)]
    simpa only [mul_comm] using hsq
  have htan : Real.tan a = Real.cos δ / Real.sin δ := by
    rw [show a = (((Real.pi / 2 - δ) + Real.pi) + Real.pi) + Real.pi by
      dsimp [a, δ]
      ring]
    rw [Real.tan_add_pi, Real.tan_add_pi, Real.tan_add_pi,
      Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos, inv_div]
  unfold m
  rw [htan]
  exact hratio

private lemma m_le_deriv_f (x : ℝ) (hx : x ∈ interval) :
    m ≤ deriv f x := by
  let ya := a - 3 * Real.pi
  let yx := x - 3 * Real.pi
  have hya : ya = 15 * Real.pi / 32 := by
    dsimp [ya, a]
    ring
  have hyx0 : 0 < yx := by
    have hbase : 3 * Real.pi < a := by
      dsimp [a]
      nlinarith [Real.pi_pos]
    dsimp [yx]
    exact sub_pos.mpr (lt_trans hbase hx.1)
  have hyxpi2 : yx < Real.pi / 2 := by
    have htop : b < 3 * Real.pi + Real.pi / 2 := by
      dsimp [b]
      nlinarith [Real.pi_pos]
    dsimp [yx]
    nlinarith [hx.2]
  have hyamem : ya ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [hya]
    constructor <;> nlinarith [Real.pi_pos]
  have hyxmem : yx ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by nlinarith [Real.pi_pos], hyxpi2⟩
  have hayx : ya < yx := by
    dsimp [ya, yx]
    linarith [hx.1]
  have htanlt : Real.tan a < Real.tan x := by
    have h := Real.strictMonoOn_tan hyamem hyxmem hayx
    have hta : Real.tan a = Real.tan ya := by
      rw [show a = ((ya + Real.pi) + Real.pi) + Real.pi by simp [ya]; ring]
      rw [Real.tan_add_pi, Real.tan_add_pi, Real.tan_add_pi]
    have htx : Real.tan x = Real.tan yx := by
      rw [show x = ((yx + Real.pi) + Real.pi) + Real.pi by simp [yx]; ring]
      rw [Real.tan_add_pi, Real.tan_add_pi, Real.tan_add_pi]
    rwa [hta, htx]
  have hta0 : 0 < Real.tan a := by
    have hya0 : 0 < ya := by rw [hya]; positivity
    have hyapi2 : ya < Real.pi / 2 := by rw [hya]; nlinarith [Real.pi_pos]
    have htan : 0 < Real.tan ya :=
      Real.tan_pos_of_pos_of_lt_pi_div_two hya0 hyapi2
    have hta : Real.tan a = Real.tan ya := by
      rw [show a = ((ya + Real.pi) + Real.pi) + Real.pi by simp [ya]; ring]
      rw [Real.tan_add_pi, Real.tan_add_pi, Real.tan_add_pi]
    rwa [hta]
  have hsquares : (Real.tan a) ^ 2 ≤ (Real.tan x) ^ 2 :=
    (pow_lt_pow_left₀ htanlt hta0.le (by norm_num)).le
  have hc := cos_ne_interval x hx
  have h := (tan_hasDerivAt x hc).sub (hasDerivAt_id x)
  have hderiv : deriv f x = (Real.tan x) ^ 2 := by
    unfold f
    calc
      deriv (fun y => Real.tan y - y) x = 1 / (Real.cos x) ^ 2 - 1 := by
        simpa [Pi.sub_apply, id] using h.deriv
      _ = (Real.tan x) ^ 2 := by
        rw [Real.tan_eq_sin_div_cos]
        field_simp [hc]
        nlinarith [Real.sin_sq_add_cos_sq x]
  unfold m
  rw [hderiv]
  exact hsquares

theorem gap13 (ξ : ℝ) (hξ : ξ ∈ interval) (hroot : f ξ = 0) :
    |x₃ - ξ| ≤ |f x₃| / m := by
  have hx₃approx := gap8
  rw [Approx, abs_lt] at hx₃approx
  have hx₃ : x₃ ∈ interval := by
    unfold interval
    constructor
    · unfold a
      nlinarith [Real.pi_lt_d4]
    · unfold b
      nlinarith [Real.pi_gt_d4]
  have hcont : ContinuousOn f interval := by
    unfold f
    apply ContinuousOn.sub
    · exact Real.continuousOn_tan.mono (by
        intro x hx
        exact cos_ne_interval x hx)
    · exact continuousOn_id
  have hdiff : DifferentiableOn ℝ f (interior interval) := by
    intro x hx
    have hx' : x ∈ interval := interior_subset hx
    exact ((tan_hasDerivAt x (cos_ne_interval x hx')).sub
      (hasDerivAt_id x)).differentiableAt.differentiableWithinAt
  have hderiv : ∀ x ∈ interior interval, m ≤ deriv f x :=
    fun x hx => m_le_deriv_f x (interior_subset hx)
  have hgrow :=
    (convex_Ioo a b).mul_sub_le_image_sub_of_le_deriv hcont hdiff hderiv
  have hm0 : 0 < m := lt_trans (by norm_num) gap12
  rcases le_total x₃ ξ with hle | hle
  · have hg := hgrow x₃ hx₃ ξ hξ hle
    have hfx : f x₃ ≤ 0 := by
      simp only [hroot, zero_sub] at hg
      have hmprod : 0 ≤ m * (ξ - x₃) :=
        mul_nonneg hm0.le (sub_nonneg.mpr hle)
      linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hle), abs_of_nonpos hfx,
      le_div_iff₀ hm0]
    simp only [hroot, zero_sub] at hg
    simpa [mul_comm] using hg
  · have hg := hgrow ξ hξ x₃ hx₃ hle
    have hfx : 0 ≤ f x₃ := by
      simp only [hroot, sub_zero] at hg
      exact le_trans (mul_nonneg hm0.le (sub_nonneg.mpr hle)) hg
    rw [abs_of_nonneg (sub_nonneg.mpr hle), abs_of_nonneg hfx,
      le_div_iff₀ hm0]
    simp only [hroot, sub_zero] at hg
    simpa [mul_comm] using hg

private lemma tan_x₃_bounds :
    (10.9109 : ℝ) < Real.tan x₃ ∧ Real.tan x₃ < 10.9451 := by
  apply tan_near_pole_bounds
      (l := (0.09111428 : ℝ)) (u := (0.09139430 : ℝ))
  · norm_num
  · nlinarith [x₃_bounds.2, Real.pi_gt_d20]
  · nlinarith [x₃_bounds.1, Real.pi_lt_d20]
  · norm_num
  · norm_num
  · norm_num
  · norm_num [sinLower]
  · norm_num [sinUpper]
  · norm_num [sinLower]
  · norm_num [sinUpper]
  · norm_num [sinUpper]
  · norm_num [sinUpperQuarter, cosLowerQuarter, sinLower, sinUpper]
  · norm_num [sinLowerQuarter, cosUpperQuarter, sinLower, sinUpper]

theorem gap14 : |f x₃| / m < 0.001 := by
  have hfpos : 0 < f x₃ := by
    unfold f
    nlinarith [tan_x₃_bounds.1, x₃_bounds.2]
  have hfupper : f x₃ < (0.041 : ℝ) := by
    unfold f
    nlinarith [tan_x₃_bounds.2, x₃_bounds.1]
  have hm0 : 0 < m := lt_trans (by norm_num) gap12
  rw [abs_of_pos hfpos, div_lt_iff₀ hm0]
  nlinarith [gap12]

theorem gap15 (ξ : ℝ) (hξ : ξ ∈ interval) (hroot : f ξ = 0) :
    |x₃ - ξ| < 0.001 := by
  exact lt_of_le_of_lt (gap13 ξ hξ hroot) gap14

private lemma tan_10903_bounds :
    (10.7711 : ℝ) < Real.tan 10.903 ∧
      Real.tan 10.903 < 10.7714 := by
  apply tan_near_pole_bounds
      (l := (0.09257428 : ℝ)) (u := (0.09257430 : ℝ))
  · norm_num
  · norm_num at ⊢
    nlinarith [Real.pi_gt_d20]
  · norm_num at ⊢
    nlinarith [Real.pi_lt_d20]
  · norm_num
  · norm_num
  · norm_num
  · norm_num [sinLower]
  · norm_num [sinUpper]
  · norm_num [sinLower]
  · norm_num [sinUpper]
  · norm_num [sinUpper]
  · norm_num [sinUpperQuarter, cosLowerQuarter, sinLower, sinUpper]
  · norm_num [sinLowerQuarter, cosUpperQuarter, sinLower, sinUpper]

private lemma tan_10905_bounds :
    (11.0103 : ℝ) < Real.tan 10.905 ∧
      Real.tan 10.905 < 11.0106 := by
  apply tan_near_pole_bounds
      (l := (0.09057428 : ℝ)) (u := (0.09057430 : ℝ))
  · norm_num
  · norm_num at ⊢
    nlinarith [Real.pi_gt_d20]
  · norm_num at ⊢
    nlinarith [Real.pi_lt_d20]
  · norm_num
  · norm_num
  · norm_num
  · norm_num [sinLower]
  · norm_num [sinUpper]
  · norm_num [sinLower]
  · norm_num [sinUpper]
  · norm_num [sinUpper]
  · norm_num [sinUpperQuarter, cosLowerQuarter, sinLower, sinUpper]
  · norm_num [sinLowerQuarter, cosUpperQuarter, sinLower, sinUpper]

theorem gap16 (ξ : ℝ) (hξ : ξ ∈ interval) (hroot : f ξ = 0) :
    Approx ξ 10.904 0.001 ∧ Real.tan ξ = ξ := by
  have hloMem : (10.903 : ℝ) ∈ interval := by
    unfold interval a b
    constructor
    · nlinarith [Real.pi_lt_d20]
    · nlinarith [Real.pi_gt_d20]
  have hhiMem : (10.905 : ℝ) ∈ interval := by
    unfold interval a b
    constructor
    · nlinarith [Real.pi_lt_d20]
    · nlinarith [Real.pi_gt_d20]
  have hflo : f 10.903 < 0 := by
    unfold f
    nlinarith [tan_10903_bounds.2]
  have hfhi : 0 < f 10.905 := by
    unfold f
    nlinarith [tan_10905_bounds.1]
  have hcont : ContinuousOn f interval := by
    unfold f
    apply ContinuousOn.sub
    · exact Real.continuousOn_tan.mono (by
        intro x hx
        exact cos_ne_interval x hx)
    · exact continuousOn_id
  have hmono : StrictMonoOn f interval :=
    strictMonoOn_of_deriv_pos (convex_Ioo a b) hcont
      (fun x hx => deriv_f_pos x (interior_subset hx))
  have hloξ : (10.903 : ℝ) < ξ := by
    by_contra hnot
    have hle : ξ ≤ (10.903 : ℝ) := le_of_not_gt hnot
    rcases hle.eq_or_lt with heq | hlt
    · rw [heq] at hroot
      linarith
    · have hstrict := hmono hξ hloMem hlt
      linarith
  have hξhi : ξ < (10.905 : ℝ) := by
    by_contra hnot
    have hle : (10.905 : ℝ) ≤ ξ := le_of_not_gt hnot
    rcases hle.eq_or_lt with heq | hlt
    · rw [← heq] at hroot
      linarith
    · have hstrict := hmono hhiMem hξ hlt
      linarith
  constructor
  · rw [Approx, abs_lt]
    constructor <;> nlinarith
  · unfold f at hroot
    linarith

end
end ProofGap.Exercise1626_3
