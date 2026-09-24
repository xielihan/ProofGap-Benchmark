import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2134
noncomputable section

def AdmissibleBranch (U : Set ℝ) : Prop :=
  U = Set.Iio 0 ∨ U = Set.Ioo 0 1 ∨ U = Set.Ioi 1
def cubeRoot (y : ℝ) :=
  Real.sign y * Real.rpow |y| (1 / 3 : ℝ)
def t (x : ℝ) := cubeRoot ((1 - x) / x)
def integrand (x : ℝ) := 1 / cubeRoot (x ^ 2 * (1 - x))
def pulledBack (x : ℝ) := t x / (t x ^ 3 + 1) * deriv t x
def firstTerm (x : ℝ) := deriv t x / (t x + 1)
def secondTerm (x : ℝ) := (t x + 1) / (t x ^ 2 - t x + 1) * deriv t x
def logDerivative (x : ℝ) :=
  (2 * t x - 1) / (t x ^ 2 - t x + 1) * deriv t x
def quadraticReciprocal (x : ℝ) :=
  deriv t x / (t x ^ 2 - t x + 1)
def primitive (x : ℝ) :=
  (1 / 2 : ℝ) *
      Real.log ((t x + 1) ^ 2 / (t x ^ 2 - t x + 1)) -
    Real.sqrt 3 * Real.arctan ((2 * t x - 1) / Real.sqrt 3)

def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def MinusThreeFamily (U : Set ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family U pulledBack, ∀ x ∈ U, F x = -3 * A x}
def DifferenceFamily (U : Set ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family U firstTerm, ∃ B ∈ Family U secondTerm,
    ∀ x ∈ U, F x = A x - B x}
def ExpandedFamily (U : Set ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family U logDerivative,
    ∃ B ∈ Family U quadraticReciprocal, ∀ x ∈ U,
    F x = Real.log |t x + 1| - (1 / 2 : ℝ) * A x - (3 / 2 : ℝ) * B x}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ U, F x = p x + C}

private def firstPrimitive (x : ℝ) := Real.log |t x + 1|
private def logQuadraticPrimitive (x : ℝ) :=
  Real.log (t x ^ 2 - t x + 1)
private def reciprocalPrimitive (x : ℝ) :=
  (2 / Real.sqrt 3) *
    Real.arctan ((2 * t x - 1) / Real.sqrt 3)
private def secondPrimitive (x : ℝ) :=
  (1 / 2 : ℝ) * logQuadraticPrimitive x +
    (3 / 2 : ℝ) * reciprocalPrimitive x

private theorem admissible_isOpen {U : Set ℝ} (hU : AdmissibleBranch U) :
    IsOpen U := by
  rcases hU with rfl | rfl | rfl
  · exact isOpen_Iio
  · exact isOpen_Ioo
  · exact isOpen_Ioi

private theorem admissible_isPreconnected {U : Set ℝ}
    (hU : AdmissibleBranch U) : IsPreconnected U := by
  rcases hU with rfl | rfl | rfl
  · exact isPreconnected_Iio
  · exact isPreconnected_Ioo
  · exact isPreconnected_Ioi

private theorem admissible_nonempty {U : Set ℝ}
    (hU : AdmissibleBranch U) : U.Nonempty := by
  rcases hU with rfl | rfl | rfl
  · exact ⟨-1, by simp⟩
  · exact ⟨1 / 2, by norm_num⟩
  · exact ⟨2, by norm_num⟩

private theorem admissible_ne_zero {U : Set ℝ}
    (hU : AdmissibleBranch U) {x : ℝ} (hx : x ∈ U) : x ≠ 0 := by
  rcases hU with rfl | rfl | rfl
  · exact ne_of_lt hx
  · exact ne_of_gt hx.1
  · exact ne_of_gt (lt_trans zero_lt_one hx)

private theorem admissible_ne_one {U : Set ℝ}
    (hU : AdmissibleBranch U) {x : ℝ} (hx : x ∈ U) : x ≠ 1 := by
  rcases hU with rfl | rfl | rfl
  · exact ne_of_lt (lt_trans hx zero_lt_one)
  · exact ne_of_lt hx.2
  · exact ne_of_gt hx

private theorem cubeRoot_cubed (y : ℝ) : cubeRoot y ^ 3 = y := by
  rcases eq_or_ne y 0 with rfl | hy
  · norm_num [cubeRoot]
  rcases lt_or_gt_of_ne hy with hy | hy
  · have hpow :
        Real.rpow (-y) (1 / 3 : ℝ) ^ 3 = -y := by
      simpa [one_div] using
        (Real.rpow_inv_natCast_pow (x := -y) (n := 3)
          (le_of_lt (neg_pos.mpr hy)) (by norm_num))
    rw [cubeRoot, Real.sign_of_neg hy, abs_of_neg hy]
    norm_num
    change (-Real.rpow (-y) (1 / 3 : ℝ)) ^ 3 = y
    calc
      (-Real.rpow (-y) (1 / 3 : ℝ)) ^ 3 =
          -(Real.rpow (-y) (1 / 3 : ℝ) ^ 3) := by ring
      _ = -(-y) := by rw [hpow]
      _ = y := by ring
  · simpa [cubeRoot, Real.sign_of_pos hy, abs_of_pos hy, one_div] using
      (Real.rpow_inv_natCast_pow (x := y) (n := 3) hy.le
        (by norm_num))

private theorem cubeRoot_cube (y : ℝ) : cubeRoot (y ^ 3) = y := by
  apply (show Odd (3 : ℕ) by decide).strictMono_pow.injective
  exact cubeRoot_cubed (y ^ 3)

private theorem hasDerivAt_rpow_third_of_pos {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun z : ℝ => Real.rpow z (1 / 3 : ℝ))
      (Real.rpow y (1 / 3 : ℝ) / (3 * y)) y := by
  have h :=
    Real.hasDerivAt_rpow_const (x := y) (p := (1 / 3 : ℝ))
      (Or.inl hy.ne')
  convert h using 1
  rw [Real.rpow_sub hy]
  simp only [Real.rpow_one]
  field_simp [hy.ne']
  exact Real.rpow_eq_pow y (1 / 3 : ℝ)

private theorem hasDerivAt_cubeRoot {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt cubeRoot (cubeRoot y / (3 * y)) y := by
  rcases lt_or_gt_of_ne hy with hy | hy
  · have hpos := hasDerivAt_rpow_third_of_pos (neg_pos.mpr hy)
    have hcomp := hpos.comp y (hasDerivAt_id y).neg
    have hneg := hcomp.neg
    have heq :
        cubeRoot =ᶠ[nhds y]
          ((-(fun z : ℝ => Real.rpow z (1 / 3 : ℝ))) ∘ Neg.neg) := by
      filter_upwards [Iio_mem_nhds hy] with z hz
      have hz' : z < 0 := hz
      simp [cubeRoot, Real.sign_of_neg hz', abs_of_neg hz']
    have hfinal := hneg.congr_of_eventuallyEq heq
    convert hfinal using 1
    simp [cubeRoot, Real.sign_of_neg hy, abs_of_neg hy]
    field_simp [hy.ne]
  · have hpos := hasDerivAt_rpow_third_of_pos hy
    have heq :
        cubeRoot =ᶠ[nhds y]
          (fun z : ℝ => Real.rpow z (1 / 3 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      have hz' : 0 < z := hz
      simp [cubeRoot, Real.sign_of_pos hz', abs_of_pos hz']
    have hfinal := hpos.congr_of_eventuallyEq heq
    simpa [cubeRoot, Real.sign_of_pos hy, abs_of_pos hy] using hfinal

private theorem t_plus_one_ne (x : ℝ) : t x + 1 ≠ 0 := by
  intro h
  have ht : t x = -1 := by linarith
  have hc := cubeRoot_cubed ((1 - x) / x)
  change t x ^ 3 = (1 - x) / x at hc
  rw [ht] at hc
  norm_num at hc
  by_cases hx0 : x = 0
  · subst x
    norm_num at hc
  · field_simp [hx0] at hc
    linarith

private theorem quadratic_pos (x : ℝ) : 0 < t x ^ 2 - t x + 1 := by
  nlinarith [sq_nonneg (t x - 1 / 2)]

private theorem t_hasDerivAt {U : Set ℝ}
    (hU : AdmissibleBranch U) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt t (deriv t x) x := by
  have hx0 := admissible_ne_zero hU hx
  have hx1 := admissible_ne_one hU hx
  let u : ℝ → ℝ := fun y => (1 - y) / y
  have hu : u x ≠ 0 := by
    dsimp [u]
    exact div_ne_zero (sub_ne_zero.mpr hx1.symm) hx0
  have hnum : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x) using 1 <;>
      ring
  have hquot := hnum.div (hasDerivAt_id x) hx0
  have hinner : HasDerivAt u (-1 / x ^ 2) x := by
    dsimp only [u]
    convert hquot using 1 <;>
      simp only [id_eq] <;> field_simp [hx0] <;> ring
  have hout := hasDerivAt_cubeRoot hu
  have ht0 : DifferentiableAt ℝ t x := by
    unfold t
    simpa only [u] using (hout.comp x hinner).differentiableAt
  exact ht0.hasDerivAt

private theorem firstPrimitive_hasDerivAt {U : Set ℝ}
    (hU : AdmissibleBranch U) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt firstPrimitive (firstTerm x) x := by
  have ht := t_hasDerivAt hU hx
  have ht1 := t_plus_one_ne x
  have hraw :=
    (Real.hasDerivAt_log ht1).comp x (ht.add_const 1)
  unfold firstPrimitive firstTerm
  simpa only [Function.comp_def, Real.log_abs, one_div,
    div_eq_mul_inv, mul_comm] using hraw

private theorem logQuadraticPrimitive_hasDerivAt {U : Set ℝ}
    (hU : AdmissibleBranch U) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt logQuadraticPrimitive (logDerivative x) x := by
  have ht := t_hasDerivAt hU hx
  have hq := ne_of_gt (quadratic_pos x)
  have hquad :
      HasDerivAt (fun y : ℝ => t y ^ 2 - t y + 1)
        ((2 * t x - 1) * deriv t x) x := by
    convert ((ht.pow 2).sub ht).add_const 1 using 1 <;> ring
  have hraw := (Real.hasDerivAt_log hq).comp x hquad
  unfold logQuadraticPrimitive logDerivative
  convert hraw using 1 <;> field_simp [hq] <;> ring

private theorem reciprocalPrimitive_hasDerivAt {U : Set ℝ}
    (hU : AdmissibleBranch U) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt reciprocalPrimitive (quadraticReciprocal x) x := by
  have ht := t_hasDerivAt hU hx
  have hs : Real.sqrt 3 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs2 : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hq := ne_of_gt (quadratic_pos x)
  have harg :
      HasDerivAt (fun y : ℝ => (2 * t y - 1) / Real.sqrt 3)
        (2 * deriv t x / Real.sqrt 3) x := by
    convert ((ht.const_mul 2).sub_const 1).div_const (Real.sqrt 3)
      using 1 <;> ring
  have hatan :=
    (Real.hasDerivAt_arctan ((2 * t x - 1) / Real.sqrt 3)).comp x harg
  have hargden :
      1 + ((2 * t x - 1) / Real.sqrt 3) ^ 2 =
        4 * (t x ^ 2 - t x + 1) / 3 := by
    field_simp [hs]
    rw [hs2]
    ring
  have hraw := hatan.const_mul (2 / Real.sqrt 3)
  unfold reciprocalPrimitive quadraticReciprocal
  convert hraw using 1
  rw [hargden]
  field_simp [hs, hq]
  rw [hs2]
  ring

private theorem secondPrimitive_hasDerivAt {U : Set ℝ}
    (hU : AdmissibleBranch U) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt secondPrimitive (secondTerm x) x := by
  have hlog := logQuadraticPrimitive_hasDerivAt hU hx
  have hrec := reciprocalPrimitive_hasDerivAt hU hx
  have ht1 := t_plus_one_ne x
  have hq := ne_of_gt (quadratic_pos x)
  have hraw :=
    (hlog.const_mul (1 / 2 : ℝ)).add
      (hrec.const_mul (3 / 2 : ℝ))
  have hcoeff :
      (1 / 2 : ℝ) * logDerivative x +
          (3 / 2 : ℝ) * quadraticReciprocal x = secondTerm x := by
    unfold secondTerm logDerivative quadraticReciprocal
    field_simp [ht1, hq]
    ring
  simpa only [secondPrimitive, hcoeff] using hraw

private theorem secondTerm_decomposition (x : ℝ) :
    (1 / 2 : ℝ) * logDerivative x +
        (3 / 2 : ℝ) * quadraticReciprocal x = secondTerm x := by
  have ht1 := t_plus_one_ne x
  have hq := ne_of_gt (quadratic_pos x)
  unfold secondTerm logDerivative quadraticReciprocal
  field_simp [ht1, hq]
  ring

private theorem differential_identity (x : ℝ) :
    firstTerm x - secondTerm x = -3 * pulledBack x := by
  have ht1 := t_plus_one_ne x
  have hq := ne_of_gt (quadratic_pos x)
  have hq' : 1 - t x + t x ^ 2 ≠ 0 := by
    nlinarith [quadratic_pos x]
  unfold firstTerm secondTerm pulledBack
  rw [show t x ^ 3 + 1 =
    (t x + 1) * (t x ^ 2 - t x + 1) by ring]
  field_simp [ht1, hq, hq', mul_ne_zero ht1 hq]
  have hinv :
      (1 - t x + t x ^ 2) * (1 - t x + t x ^ 2)⁻¹ = 1 :=
    mul_inv_cancel₀ hq'
  linear_combination -(deriv t x) * hinv

private theorem primitive_eq_split (x : ℝ) :
    primitive x = firstPrimitive x - secondPrimitive x := by
  have ht1 := t_plus_one_ne x
  have hq := ne_of_gt (quadratic_pos x)
  have hs : Real.sqrt 3 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs2 : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hlog :
      Real.log ((t x + 1) ^ 2 / (t x ^ 2 - t x + 1)) =
        2 * Real.log |t x + 1| -
          Real.log (t x ^ 2 - t x + 1) := by
    rw [Real.log_div (pow_ne_zero 2 ht1) hq, Real.log_pow]
    simp only [Real.log_abs]
    norm_num
  have hcoef :
      (3 / 2 : ℝ) * (2 / Real.sqrt 3) = Real.sqrt 3 := by
    field_simp [hs]
    nlinarith
  unfold primitive firstPrimitive secondPrimitive
    logQuadraticPrimitive reciprocalPrimitive
  rw [hlog]
  rw [show
    (3 / 2 : ℝ) *
        ((2 / Real.sqrt 3) *
          Real.arctan ((2 * t x - 1) / Real.sqrt 3)) =
      Real.sqrt 3 * Real.arctan ((2 * t x - 1) / Real.sqrt 3) by
        rw [← mul_assoc, hcoef]]
  ring

private theorem primitive_hasDerivAt {U : Set ℝ}
    (hU : AdmissibleBranch U) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt primitive (firstTerm x - secondTerm x) x := by
  have hsplit :=
    (firstPrimitive_hasDerivAt hU hx).sub
      (secondPrimitive_hasDerivAt hU hx)
  have heq : primitive =ᶠ[nhds x]
      fun y => firstPrimitive y - secondPrimitive y :=
    Filter.Eventually.of_forall (fun y => primitive_eq_split y)
  exact hsplit.congr_of_eventuallyEq heq

private theorem family_eq_translates {U : Set ℝ}
    (hU : AdmissibleBranch U) (f p : ℝ → ℝ)
    (hp : ∀ x ∈ U, HasDerivAt p (f x) x) :
    Family U f = Translates U p := by
  ext F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    obtain ⟨x₀, hx₀⟩ := admissible_nonempty hU
    have hzero : ∀ x ∈ U, HasDerivAt (fun y => F y - p y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (hp x hx)
    have hdiff : DifferentiableOn ℝ (fun y => F y - p y) U :=
      fun x hx => (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ U, deriv (fun y => F y - p y) x = 0 :=
      fun x hx => (hzero x hx).deriv
    refine ⟨F x₀ - p x₀, fun x hx => ?_⟩
    have hconst : F x - p x = F x₀ - p x₀ :=
      (admissible_isOpen hU).is_const_of_deriv_eq_zero
        (admissible_isPreconnected hU) hdiff hderiv hx hx₀
    linarith
  · rintro ⟨C, hC⟩ x hx
    have heq : F =ᶠ[nhds x] fun y => p y + C :=
      Filter.Eventually.mono ((admissible_isOpen hU).mem_nhds hx)
        (fun y hy => hC y hy)
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq

theorem gap1 (U : Set ℝ) (hU : AdmissibleBranch U) (x : ℝ) (hx : x ∈ U) :
    x = 1 / (t x ^ 3 + 1) := by
  have hx0 := admissible_ne_zero hU hx
  have ht3 : t x ^ 3 = (1 - x) / x := by
    unfold t
    exact cubeRoot_cubed ((1 - x) / x)
  rw [ht3]
  field_simp [hx0]
  ring
theorem gap2 (U : Set ℝ) (hU : AdmissibleBranch U) (x : ℝ) (hx : x ∈ U) :
    1 = (-3 * t x ^ 2 / (t x ^ 3 + 1) ^ 2) * deriv t x := by
  have ht := t_hasDerivAt hU hx
  have hx0 := admissible_ne_zero hU hx
  have hden : t x ^ 3 + 1 ≠ 0 := by
    intro h
    have hgap := gap1 U hU x hx
    rw [h] at hgap
    norm_num at hgap
    exact hx0 hgap
  have hout :
      HasDerivAt (fun z : ℝ => 1 / (z ^ 3 + 1))
        (-3 * t x ^ 2 / (t x ^ 3 + 1) ^ 2) (t x) := by
    have hbase :
        HasDerivAt (fun z : ℝ => z ^ 3 + 1) (3 * t x ^ 2) (t x) := by
      convert ((hasDerivAt_id (t x)).pow 3).add_const 1 using 1 <;>
        simp only [id_eq] <;> ring
    have hinv := hbase.inv hden
    convert hinv using 1
    · funext z
      simp only [one_div, Pi.inv_apply]
    · ring
  have hcomp := hout.comp x ht
  have heq :
      (fun y : ℝ => 1 / (t y ^ 3 + 1)) =ᶠ[nhds x]
        (fun y : ℝ => y) := by
    filter_upwards [(admissible_isOpen hU).mem_nhds hx] with y hy
    exact (gap1 U hU y hy).symm
  have hid := hcomp.congr_of_eventuallyEq heq.symm
  exact (hasDerivAt_id x).unique hid

private theorem integrand_eq_minus_three_pulledBack
    (U : Set ℝ) (hU : AdmissibleBranch U) (x : ℝ) (hx : x ∈ U) :
    integrand x = -3 * pulledBack x := by
  have hx0 := admissible_ne_zero hU hx
  have hx1 := admissible_ne_one hU hx
  have hu : (1 - x) / x ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr hx1.symm) hx0
  have ht3 : t x ^ 3 = (1 - x) / x := by
    unfold t
    exact cubeRoot_cubed ((1 - x) / x)
  have htne : t x ≠ 0 := by
    intro ht
    apply hu
    rw [← ht3, ht]
    norm_num
  have hprod3 : (t x * x) ^ 3 = x ^ 2 * (1 - x) := by
    rw [mul_pow, ht3]
    field_simp [hx0]
  have hcuberoot :
      cubeRoot (x ^ 2 * (1 - x)) = t x * x := by
    rw [← hprod3, cubeRoot_cube]
  have hxval := gap1 U hU x hx
  have hden : t x ^ 3 + 1 ≠ 0 := by
    intro h
    rw [h] at hxval
    norm_num at hxval
    exact hx0 hxval
  have htx :
      t x * x = t x / (t x ^ 3 + 1) := by
    calc
      t x * x = t x * (1 / (t x ^ 3 + 1)) :=
        congrArg (fun z : ℝ => t x * z) hxval
      _ = t x / (t x ^ 3 + 1) := by ring
  have hder := gap2 U hU x hx
  unfold integrand pulledBack
  rw [hcuberoot, htx]
  field_simp [htne, hden] at hder ⊢
  linear_combination hder

theorem gap3 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = MinusThreeFamily U := by
  ext F
  simp only [Family, MinusThreeFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    let A : ℝ → ℝ := fun y => -(1 / 3 : ℝ) * F y
    refine ⟨A, ?_, ?_⟩
    · intro x hx
      have hscaled := (hF x hx).const_mul (-(1 / 3 : ℝ))
      have hrel := integrand_eq_minus_three_pulledBack U hU x hx
      have hcoeff :
          -(1 / 3 : ℝ) * integrand x = pulledBack x := by
        rw [hrel]
        ring
      rw [hcoeff] at hscaled
      simpa only [A] using hscaled
    · intro x hx
      dsimp [A]
      ring
  · rintro ⟨A, hA, hFA⟩
    intro x hx
    have hscaled := (hA x hx).const_mul (-3)
    have hrel := integrand_eq_minus_three_pulledBack U hU x hx
    rw [← hrel] at hscaled
    apply hscaled.congr_of_eventuallyEq
    exact Filter.Eventually.mono ((admissible_isOpen hU).mem_nhds hx)
      (fun y hy => hFA y hy)
theorem gap4 (U : Set ℝ) (hU : AdmissibleBranch U) :
    MinusThreeFamily U = DifferenceFamily U := by
  ext F
  simp only [MinusThreeFamily, DifferenceFamily, Family, Set.mem_setOf_eq]
  constructor
  · rintro ⟨A, hA, hFA⟩
    let B : ℝ → ℝ := secondPrimitive
    let A₁ : ℝ → ℝ := fun y => F y + B y
    refine ⟨A₁, ?_, B, ?_, ?_⟩
    · intro x hx
      have hscaled := (hA x hx).const_mul (-3)
      have hF : HasDerivAt F (-3 * pulledBack x) x := by
        apply hscaled.congr_of_eventuallyEq
        exact Filter.Eventually.mono ((admissible_isOpen hU).mem_nhds hx)
          (fun y hy => hFA y hy)
      have hsum := hF.add (secondPrimitive_hasDerivAt hU hx)
      have hcoeff : -3 * pulledBack x + secondTerm x = firstTerm x := by
        linarith [differential_identity x]
      rw [hcoeff] at hsum
      simpa only [A₁, B] using hsum
    · intro x hx
      exact secondPrimitive_hasDerivAt hU hx
    · intro x hx
      dsimp [A₁, B]
      ring
  · rintro ⟨A, hA, B, hB, hFAB⟩
    let P : ℝ → ℝ := fun y => -(1 / 3 : ℝ) * F y
    refine ⟨P, ?_, ?_⟩
    · intro x hx
      have hdiff := (hA x hx).sub (hB x hx)
      have hF : HasDerivAt F (firstTerm x - secondTerm x) x := by
        apply hdiff.congr_of_eventuallyEq
        exact Filter.Eventually.mono ((admissible_isOpen hU).mem_nhds hx)
          (fun y hy => hFAB y hy)
      have hscaled := hF.const_mul (-(1 / 3 : ℝ))
      have hcoeff :
          -(1 / 3 : ℝ) * (firstTerm x - secondTerm x) = pulledBack x := by
        rw [differential_identity]
        ring
      rw [hcoeff] at hscaled
      simpa only [P] using hscaled
    · intro x hx
      dsimp [P]
      ring
theorem gap5 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = DifferenceFamily U := by
  calc
    Family U integrand = MinusThreeFamily U := gap3 U hU
    _ = DifferenceFamily U := gap4 U hU

private theorem primitive_hasDerivAt_integrand {U : Set ℝ}
    (hU : AdmissibleBranch U) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt primitive (integrand x) x := by
  have hp := primitive_hasDerivAt hU hx
  rw [differential_identity x] at hp
  rw [← integrand_eq_minus_three_pulledBack U hU x hx] at hp
  exact hp

theorem gap7 (U : Set ℝ) (hU : AdmissibleBranch U) :
    ExpandedFamily U = Translates U primitive := by
  have hfamily :
      Family U (fun x => firstTerm x - secondTerm x) =
        Translates U primitive :=
    family_eq_translates hU _ _ (fun x hx => primitive_hasDerivAt hU hx)
  ext F
  constructor
  · intro hF
    rw [← hfamily]
    rcases hF with ⟨A, hA, B, hB, hFAB⟩
    intro x hx
    have hraw :=
      ((firstPrimitive_hasDerivAt hU hx).sub
        ((hA x hx).const_mul (1 / 2 : ℝ))).sub
          ((hB x hx).const_mul (3 / 2 : ℝ))
    have hder :
        HasDerivAt
          (fun y => firstPrimitive y - (1 / 2 : ℝ) * A y -
            (3 / 2 : ℝ) * B y)
          (firstTerm x - secondTerm x) x := by
      have hcoeff :
          firstTerm x - (1 / 2 : ℝ) * logDerivative x -
              (3 / 2 : ℝ) * quadraticReciprocal x =
            firstTerm x - secondTerm x := by
        rw [← secondTerm_decomposition x]
        ring
      rw [hcoeff] at hraw
      exact hraw
    apply hder.congr_of_eventuallyEq
    exact Filter.Eventually.mono ((admissible_isOpen hU).mem_nhds hx)
      (fun y hy => by simpa only [firstPrimitive] using hFAB y hy)
  · intro hF
    rcases hF with ⟨C, hFC⟩
    let A : ℝ → ℝ := fun y => logQuadraticPrimitive y - 2 * C
    let B : ℝ → ℝ := reciprocalPrimitive
    refine ⟨A, ?_, B, ?_, ?_⟩
    · intro x hx
      simpa only [A] using
        (logQuadraticPrimitive_hasDerivAt hU hx).sub_const (2 * C)
    · intro x hx
      exact reciprocalPrimitive_hasDerivAt hU hx
    · intro x hx
      rw [hFC x hx, primitive_eq_split]
      unfold firstPrimitive secondPrimitive
      dsimp [A, B]
      ring
theorem gap6 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = ExpandedFamily U := by
  calc
    Family U integrand = Translates U primitive :=
      family_eq_translates hU _ _
        (fun x hx => primitive_hasDerivAt_integrand hU hx)
    _ = ExpandedFamily U := (gap7 U hU).symm
theorem gap8 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Translates U primitive := by
  exact family_eq_translates hU _ _
    (fun x hx => primitive_hasDerivAt_integrand hU hx)
theorem gap9 (U : Set ℝ) (hU : AdmissibleBranch U) (x : ℝ) (hx : x ∈ U) :
    t x = cubeRoot ((1 - x) / x) := by
  rfl

end
end ProofGap.Exercise2134
