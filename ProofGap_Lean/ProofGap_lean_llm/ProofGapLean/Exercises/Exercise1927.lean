import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1927

noncomputable section

def root6 (x : ℝ) := Real.rpow x (1 / 6 : ℝ)
def cubeRoot (x : ℝ) := Real.sign x * Real.rpow |x| (1 / 3 : ℝ)
def t (x : ℝ) := root6 x
def positiveBranch : Set ℝ := {x | 0 < x}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def sourceIntegrand (x : ℝ) :=
  1 / (x * (1 + 2 * Real.sqrt x + cubeRoot x))
def q (u : ℝ) := 2 * u ^ 2 - u + 1
def transformed₁ (x : ℝ) :=
  1 / (t x * (1 + 2 * t x ^ 3 + t x ^ 2)) * deriv t x
def transformed₂ (x : ℝ) :=
  1 / (t x * (1 + t x) * q (t x)) * deriv t x
def transformed₃ (x : ℝ) :=
  (1 / t x - 1 / (4 * (1 + t x)) -
    (6 * t x - 1) / (4 * q (t x))) * deriv t x
def ScaledFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn positiveBranch p,
    ∀ x ∈ positiveBranch, F x = 6 * G x}
def AuxiliaryFamily : Set (ℝ → ℝ) :=
  {F | ∃ A ∈ AntiderivativesOn positiveBranch
      (fun x => (4 * t x - 1) / q (t x) * deriv t x),
    ∃ B ∈ AntiderivativesOn positiveBranch
      (fun x => 1 / ((t x - 1 / 4) ^ 2 + 7 / 16) *
        deriv (fun y => t y - 1 / 4) x),
    ∀ x ∈ positiveBranch,
      F x = 6 * (Real.log (t x) - 1 / 4 * Real.log |1 + t x| -
        3 / 8 * A x - 1 / 16 * B x)}
def primitive₁ (x : ℝ) :=
  6 * (Real.log |t x| - 1 / 4 * Real.log |1 + t x| -
    3 / 8 * Real.log (q (t x)) -
    1 / (4 * Real.sqrt 7) *
      Real.arctan ((4 * t x - 1) / Real.sqrt 7))
def primitive₂ (x : ℝ) :=
  3 / 4 * Real.log
      ((t x) ^ 8 / ((1 + t x) ^ 2 * (q (t x)) ^ 3)) -
    3 / (2 * Real.sqrt 7) *
      Real.arctan ((4 * t x - 1) / Real.sqrt 7)
def primitiveX (x : ℝ) :=
  3 / 4 * Real.log
      (x * cubeRoot x /
        ((1 + root6 x) ^ 2 * (2 * cubeRoot x - root6 x + 1) ^ 3)) -
    3 / (2 * Real.sqrt 7) *
      Real.arctan ((4 * root6 x - 1) / Real.sqrt 7)

private theorem positiveBranch_isOpen : IsOpen positiveBranch := by
  simpa [positiveBranch] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))

private theorem positiveBranch_isPreconnected : IsPreconnected positiveBranch := by
  simpa [positiveBranch] using (convex_Ioi (0 : ℝ)).isPreconnected

private theorem t_pos {x : ℝ} (hx : x ∈ positiveBranch) : 0 < t x := by
  have hxpos : 0 < x := hx
  exact Real.rpow_pos_of_pos hxpos _

private theorem t_pow_six (x : ℝ) (hx : 0 ≤ x) : x = t x ^ 6 := by
  symm
  simpa [t, root6] using
    (Real.rpow_inv_natCast_pow hx (by norm_num : (6 : ℕ) ≠ 0))

private theorem hasDerivAt_t {x : ℝ} (hx : x ∈ positiveBranch) :
    HasDerivAt t ((1 / 6 : ℝ) * x ^ ((1 / 6 : ℝ) - 1)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  change HasDerivAt (fun y : ℝ => y ^ (1 / 6 : ℝ))
    ((1 / 6 : ℝ) * x ^ ((1 / 6 : ℝ) - 1)) x
  exact Real.hasDerivAt_rpow_const (p := (1 / 6 : ℝ)) (Or.inl hx0)

private theorem cubeRoot_eq_t_sq {x : ℝ} (hx : x ∈ positiveBranch) :
    cubeRoot x = t x ^ 2 := by
  have hxpos : 0 < x := hx
  simp only [cubeRoot, Real.sign_of_pos hxpos, one_mul, abs_of_pos hxpos, t, root6]
  calc
    x ^ (1 / 3 : ℝ) = x ^ ((1 / 6 : ℝ) * 2) := by norm_num
    _ = (x ^ (1 / 6 : ℝ)) ^ (2 : ℝ) :=
      Real.rpow_mul hxpos.le _ _
    _ = (x ^ (1 / 6 : ℝ)) ^ (2 : ℕ) := Real.rpow_natCast _ _

private theorem sqrt_eq_t_cube {x : ℝ} (hx : x ∈ positiveBranch) :
    Real.sqrt x = t x ^ 3 := by
  have hxpos : 0 < x := hx
  rw [Real.sqrt_eq_rpow]
  simp only [t, root6]
  calc
    x ^ (1 / 2 : ℝ) = x ^ ((1 / 6 : ℝ) * 3) := by norm_num
    _ = (x ^ (1 / 6 : ℝ)) ^ (3 : ℝ) :=
      Real.rpow_mul hxpos.le _ _
    _ = (x ^ (1 / 6 : ℝ)) ^ (3 : ℕ) := Real.rpow_natCast _ _

private theorem q_pos (u : ℝ) : 0 < q u := by
  unfold q
  nlinarith [sq_nonneg (4 * u - 1)]

private theorem hasDerivAt_q_t {x : ℝ} (hx : x ∈ positiveBranch) :
    HasDerivAt (fun y => q (t y))
      ((4 * t x - 1) * deriv t x) x := by
  have ht := hasDerivAt_t hx
  have h :=
    ((((ht.pow 2).const_mul 2).sub ht).const_add 1)
  convert h using 1
  · funext u
    simp only [q, Pi.sub_apply, Pi.pow_apply]
    ring
  · rw [ht.deriv]
    ring

private theorem one_eq_six_t_pow_deriv
    (x : ℝ) (hx : x ∈ positiveBranch) :
    1 = 6 * t x ^ 5 * deriv t x := by
  have ht := hasDerivAt_t hx
  have hp := ht.pow 6
  have heq : (fun y => t y ^ 6) =ᶠ[nhds x] fun y => y := by
    filter_upwards [positiveBranch_isOpen.mem_nhds hx] with y hy
    exact (t_pow_six y (le_of_lt hy)).symm
  have hp' := hp.congr_of_eventuallyEq heq.symm
  have hid := hasDerivAt_id x
  have huniq := hp'.unique hid
  rw [← ht.deriv] at huniq
  simpa [mul_assoc] using huniq.symm

private theorem antiderivatives_scale
    (f g : ℝ → ℝ) (k : ℝ) (hk : k ≠ 0)
    (hfg : ∀ x ∈ positiveBranch, f x = k * g x) :
    AntiderivativesOn positiveBranch f =
      {F | ∃ G ∈ AntiderivativesOn positiveBranch g,
        ∀ x ∈ positiveBranch, F x = k * G x} := by
  ext F
  constructor
  · intro hF
    refine ⟨fun x => F x / k, ?_, ?_⟩
    · intro x hx
      have h := (hF x hx).div_const k
      convert h using 1
      rw [hfg x hx]
      field_simp [hk]
    · intro x hx
      field_simp [hk]
  · rintro ⟨G, hG, hEq⟩
    intro x hx
    have heq : F =ᶠ[nhds x] fun y => k * G y := by
      filter_upwards [positiveBranch_isOpen.mem_nhds hx] with y hy
      exact hEq y hy
    have h := (hG x hx).const_mul k
    rw [← hfg x hx] at h
    exact h.congr_of_eventuallyEq heq

private theorem antiderivatives_eq_translates
    (f p : ℝ → ℝ)
    (hp : ∀ x ∈ positiveBranch, HasDerivAt p (f x) x) :
    AntiderivativesOn positiveBranch f =
      PrimitiveFamilyOn positiveBranch p := by
  ext F
  constructor
  · intro hF
    have hz : ∀ x ∈ positiveBranch,
        HasDerivAt (fun y => F y - p y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (hp x hx)
    have hdiff : DifferentiableOn ℝ (fun y => F y - p y) positiveBranch := by
      intro x hx
      exact (hz x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ positiveBranch,
        deriv (fun y => F y - p y) x = 0 := by
      intro x hx
      exact (hz x hx).deriv
    refine ⟨F 1 - p 1, ?_⟩
    intro x hx
    have hone : (1 : ℝ) ∈ positiveBranch := by norm_num [positiveBranch]
    have heq : F x - p x = F 1 - p 1 :=
      positiveBranch_isOpen.is_const_of_deriv_eq_zero
        positiveBranch_isPreconnected hdiff hderiv hx hone
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have heq : F =ᶠ[nhds x] fun y => p y + C := by
      filter_upwards [positiveBranch_isOpen.mem_nhds hx] with y hy
      exact hC y hy
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq

private theorem source_eq_six_transformed₁
    (x : ℝ) (hx : x ∈ positiveBranch) :
    sourceIntegrand x = 6 * transformed₁ x := by
  have hxpos : 0 < x := hx
  have htpos := t_pos hx
  have ht0 : t x ≠ 0 := htpos.ne'
  have hd := (hasDerivAt_t hx).deriv
  have hsqrt := sqrt_eq_t_cube hx
  have hcbrt := cubeRoot_eq_t_sq hx
  have hder := one_eq_six_t_pow_deriv x hx
  unfold sourceIntegrand transformed₁
  rw [hsqrt, hcbrt]
  have hxden :
      x * (1 + 2 * t x ^ 3 + t x ^ 2) =
        t x ^ 6 * (1 + 2 * t x ^ 3 + t x ^ 2) := by
    nth_rewrite 1 [t_pow_six x hxpos.le]
    rfl
  rw [hxden]
  field_simp [ht0]
  nlinarith

private theorem transformed₁_eq_transformed₂
    (x : ℝ) (hx : x ∈ positiveBranch) :
    transformed₁ x = transformed₂ x := by
  have htpos := t_pos hx
  have ht0 : t x ≠ 0 := htpos.ne'
  unfold transformed₁ transformed₂
  have hden :
      t x * (1 + t x) * q (t x) =
        t x * (1 + 2 * t x ^ 3 + t x ^ 2) := by
    unfold q
    ring
  rw [hden]

private theorem transformed₂_eq_transformed₃
    (x : ℝ) (hx : x ∈ positiveBranch) :
    transformed₂ x = transformed₃ x := by
  have htpos := t_pos hx
  have ht0 : t x ≠ 0 := htpos.ne'
  have hq0 : q (t x) ≠ 0 := (q_pos (t x)).ne'
  have ht1 : 1 + t x ≠ 0 := by positivity
  unfold transformed₂ transformed₃
  congr 1
  field_simp [ht0, hq0, ht1]
  unfold q
  ring

private theorem hasDerivAt_primitive₁
    (x : ℝ) (hx : x ∈ positiveBranch) :
    HasDerivAt primitive₁ (sourceIntegrand x) x := by
  have ht := hasDerivAt_t hx
  have htpos := t_pos hx
  have ht0 : t x ≠ 0 := htpos.ne'
  have ht1pos : 0 < 1 + t x := by positivity
  have ht1 : 1 + t x ≠ 0 := ht1pos.ne'
  have hqpos := q_pos (t x)
  have hq0 : q (t x) ≠ 0 := hqpos.ne'
  have hqpoly : 1 - t x + 2 * t x ^ 2 ≠ 0 := by
    intro hzero
    apply hq0
    unfold q
    linarith
  have hqpoly' : 1 - t x + t x ^ 2 * 2 ≠ 0 := by
    intro hzero
    apply hqpoly
    linarith
  have hs7pos : 0 < Real.sqrt 7 := Real.sqrt_pos.2 (by norm_num)
  have hs70 : Real.sqrt 7 ≠ 0 := hs7pos.ne'
  have hs7sq : (Real.sqrt 7) ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have hlogt : HasDerivAt (fun y => Real.log |t y|)
      (deriv t x / t x) x := by
    have h := ht.log ht0
    rw [ht.deriv]
    simpa only [Real.log_abs] using h
  have ht1deriv : HasDerivAt (fun y => 1 + t y) (deriv t x) x := by
    convert ht.const_add 1 using 1
    rw [ht.deriv]
  have hlogt1 : HasDerivAt (fun y => Real.log |1 + t y|)
      (deriv t x / (1 + t x)) x := by
    have h := ht1deriv.log ht1
    simpa only [Real.log_abs] using h
  have hqt := hasDerivAt_q_t hx
  have hlogq : HasDerivAt (fun y => Real.log (q (t y)))
      ((4 * t x - 1) * deriv t x / q (t x)) x :=
    hqt.log hq0
  have harg : HasDerivAt
      (fun y => (4 * t y - 1) / Real.sqrt 7)
      ((4 * deriv t x) / Real.sqrt 7) x := by
    have hnum : HasDerivAt (fun y => 4 * t y - 1)
        (4 * deriv t x) x := by
      convert (ht.const_mul 4).sub_const 1 using 1
      rw [ht.deriv]
    exact hnum.div_const _
  have hatan : HasDerivAt
      (fun y => Real.arctan ((4 * t y - 1) / Real.sqrt 7))
      (((4 * deriv t x) / Real.sqrt 7) /
        (1 + ((4 * t x - 1) / Real.sqrt 7) ^ 2)) x := by
    convert (Real.hasDerivAt_arctan _).comp x harg using 1 <;> ring
  have hatan_scaled :
      1 / (4 * Real.sqrt 7) *
          (((4 * deriv t x) / Real.sqrt 7) /
            (1 + ((4 * t x - 1) / Real.sqrt 7) ^ 2)) =
        deriv t x / (8 * q (t x)) := by
    field_simp [hs70, hq0]
    rw [hs7sq]
    unfold q
    ring
  unfold primitive₁
  have h :=
    (((hlogt.sub (hlogt1.const_mul (1 / 4 : ℝ))).sub
      (hlogq.const_mul (3 / 8 : ℝ))).sub
      (hatan.const_mul (1 / (4 * Real.sqrt 7)))).const_mul 6
  convert h using 1
  rw [hatan_scaled]
  rw [source_eq_six_transformed₁ x hx,
    transformed₁_eq_transformed₂ x hx,
    transformed₂_eq_transformed₃ x hx]
  unfold transformed₃
  field_simp [ht0, ht1, hq0]
  unfold q
  ring

private def auxiliaryA (x : ℝ) := Real.log (q (t x))

private def auxiliaryB (x : ℝ) :=
  4 / Real.sqrt 7 *
    Real.arctan ((4 * t x - 1) / Real.sqrt 7)

private theorem hasDerivAt_auxiliaryA
    (x : ℝ) (hx : x ∈ positiveBranch) :
    HasDerivAt auxiliaryA
      ((4 * t x - 1) / q (t x) * deriv t x) x := by
  have hq := hasDerivAt_q_t hx
  have hq0 : q (t x) ≠ 0 := (q_pos (t x)).ne'
  unfold auxiliaryA
  convert hq.log hq0 using 1 <;> ring

private theorem hasDerivAt_auxiliaryB
    (x : ℝ) (hx : x ∈ positiveBranch) :
    HasDerivAt auxiliaryB
      (1 / ((t x - 1 / 4) ^ 2 + 7 / 16) *
        deriv (fun y => t y - 1 / 4) x) x := by
  have ht := hasDerivAt_t hx
  have hs7pos : 0 < Real.sqrt 7 := Real.sqrt_pos.2 (by norm_num)
  have hs70 : Real.sqrt 7 ≠ 0 := hs7pos.ne'
  have hs7sq : (Real.sqrt 7) ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have hnum : HasDerivAt (fun y => 4 * t y - 1)
      (4 * deriv t x) x := by
    convert (ht.const_mul 4).sub_const 1 using 1
    rw [ht.deriv]
  have harg := hnum.div_const (Real.sqrt 7)
  have hatan :=
    (Real.hasDerivAt_arctan ((4 * t x - 1) / Real.sqrt 7)).comp x harg
  unfold auxiliaryB
  have h := hatan.const_mul (4 / Real.sqrt 7)
  have hdsub :
      deriv (fun y => t y - 1 / 4) x = deriv t x := by
    rw [(ht.sub_const (1 / 4)).deriv, ht.deriv]
  have hcoef :
      1 / ((t x - 1 / 4) ^ 2 + 7 / 16) *
          deriv (fun y => t y - 1 / 4) x =
        4 / Real.sqrt 7 *
          (1 / (1 + ((4 * t x - 1) / Real.sqrt 7) ^ 2) *
            (4 * deriv t x / Real.sqrt 7)) := by
    rw [hdsub]
    field_simp [hs70]
    ring_nf
    rw [hs7sq]
    ring
  rw [hcoef]
  convert h using 1

private theorem auxiliary_base_identity
    (x : ℝ) (hx : x ∈ positiveBranch) :
    6 * (Real.log (t x) - 1 / 4 * Real.log |1 + t x| -
        3 / 8 * auxiliaryA x - 1 / 16 * auxiliaryB x) =
      primitive₁ x := by
  have htpos := t_pos hx
  unfold auxiliaryA auxiliaryB primitive₁
  rw [abs_of_pos htpos]
  ring

private theorem auxiliaryFamily_eq_primitiveFamily :
    AuxiliaryFamily = PrimitiveFamilyOn positiveBranch primitive₁ := by
  have hAeq := antiderivatives_eq_translates
    (fun x => (4 * t x - 1) / q (t x) * deriv t x) auxiliaryA
    hasDerivAt_auxiliaryA
  have hBeq := antiderivatives_eq_translates
    (fun x => 1 / ((t x - 1 / 4) ^ 2 + 7 / 16) *
      deriv (fun y => t y - 1 / 4) x) auxiliaryB
    hasDerivAt_auxiliaryB
  ext F
  constructor
  · rintro ⟨A, hA, B, hB, hF⟩
    rw [hAeq] at hA
    rw [hBeq] at hB
    rcases hA with ⟨CA, hCA⟩
    rcases hB with ⟨CB, hCB⟩
    refine ⟨6 * (-(3 / 8) * CA - (1 / 16) * CB), ?_⟩
    intro x hx
    rw [hF x hx, hCA x hx, hCB x hx,
      ← auxiliary_base_identity x hx]
    ring
  · rintro ⟨C, hC⟩
    let A : ℝ → ℝ := fun x => auxiliaryA x - (4 / 9) * C
    refine ⟨A, ?_, auxiliaryB, ?_, ?_⟩
    · intro x hx
      exact (hasDerivAt_auxiliaryA x hx).sub_const _
    · intro x hx
      exact hasDerivAt_auxiliaryB x hx
    · intro x hx
      rw [hC x hx, ← auxiliary_base_identity x hx]
      dsimp [A]
      ring

private theorem primitive₁_eq_primitive₂
    (x : ℝ) (hx : x ∈ positiveBranch) :
    primitive₁ x = primitive₂ x := by
  have htpos := t_pos hx
  have ht0 : t x ≠ 0 := htpos.ne'
  have ht1pos : 0 < 1 + t x := by positivity
  have ht1 : 1 + t x ≠ 0 := ht1pos.ne'
  have hqpos := q_pos (t x)
  have hq0 : q (t x) ≠ 0 := hqpos.ne'
  unfold primitive₁ primitive₂
  rw [abs_of_pos htpos, abs_of_pos ht1pos,
    Real.log_div (pow_ne_zero 8 ht0)
      (mul_ne_zero (pow_ne_zero 2 ht1) (pow_ne_zero 3 hq0)),
    Real.log_mul (pow_ne_zero 2 ht1) (pow_ne_zero 3 hq0),
    Real.log_pow, Real.log_pow, Real.log_pow]
  ring

private theorem primitive₂_eq_primitiveX
    (x : ℝ) (hx : x ∈ positiveBranch) :
    primitive₂ x = primitiveX x := by
  have hp6 := t_pow_six x (le_of_lt hx)
  have hcbrt := cubeRoot_eq_t_sq hx
  unfold primitive₂ primitiveX
  change
    3 / 4 * Real.log
        (t x ^ 8 / ((1 + t x) ^ 2 * q (t x) ^ 3)) -
          3 / (2 * Real.sqrt 7) *
            Real.arctan ((4 * t x - 1) / Real.sqrt 7) =
      3 / 4 * Real.log
        (x * cubeRoot x /
          ((1 + t x) ^ 2 * (2 * cubeRoot x - t x + 1) ^ 3)) -
          3 / (2 * Real.sqrt 7) *
            Real.arctan ((4 * t x - 1) / Real.sqrt 7)
  rw [hcbrt]
  have hpow : t x ^ 8 = x * t x ^ 2 := by
    calc
      t x ^ 8 = t x ^ 6 * t x ^ 2 := by ring
      _ = x * t x ^ 2 := by rw [← hp6]
  rw [hpow]
  unfold q
  rfl

theorem gap1 (x : ℝ) (hx : 0 ≤ x) :
    x = t x ^ 6 := by
  exact t_pow_six x hx
theorem gap2 (x : ℝ) (hx : 0 < x) :
    1 = 6 * t x ^ 5 * deriv t x := by
  have hmem : x ∈ positiveBranch := hx
  have htpos := t_pos hmem
  exact one_eq_six_t_pow_deriv x hmem
theorem gap3 :
    AntiderivativesOn positiveBranch sourceIntegrand =
      ScaledFamily transformed₁ := by
  unfold ScaledFamily
  exact antiderivatives_scale sourceIntegrand transformed₁ 6
    (by norm_num) source_eq_six_transformed₁
theorem gap4 :
    AntiderivativesOn positiveBranch sourceIntegrand =
      ScaledFamily transformed₂ := by
  unfold ScaledFamily
  apply antiderivatives_scale sourceIntegrand transformed₂ 6 (by norm_num)
  intro x hx
  rw [source_eq_six_transformed₁ x hx,
    transformed₁_eq_transformed₂ x hx]
theorem gap5 :
    AntiderivativesOn positiveBranch sourceIntegrand =
      ScaledFamily transformed₃ := by
  unfold ScaledFamily
  apply antiderivatives_scale sourceIntegrand transformed₃ 6 (by norm_num)
  intro x hx
  rw [source_eq_six_transformed₁ x hx,
    transformed₁_eq_transformed₂ x hx,
    transformed₂_eq_transformed₃ x hx]
theorem gap6 :
    AntiderivativesOn positiveBranch sourceIntegrand = AuxiliaryFamily := by
  rw [antiderivatives_eq_translates sourceIntegrand primitive₁
    hasDerivAt_primitive₁, auxiliaryFamily_eq_primitiveFamily]
theorem gap7 :
    AntiderivativesOn positiveBranch sourceIntegrand =
      PrimitiveFamilyOn positiveBranch primitive₁ := by
  exact antiderivatives_eq_translates sourceIntegrand primitive₁
    hasDerivAt_primitive₁
theorem gap8 :
    AntiderivativesOn positiveBranch sourceIntegrand =
      PrimitiveFamilyOn positiveBranch primitive₂ := by
  rw [gap7]
  ext F
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun x hx => by rw [hC x hx, primitive₁_eq_primitive₂ x hx]⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun x hx => by rw [hC x hx, primitive₁_eq_primitive₂ x hx]⟩
theorem gap9 :
    AntiderivativesOn positiveBranch sourceIntegrand =
      PrimitiveFamilyOn positiveBranch primitiveX := by
  rw [gap8]
  ext F
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun x hx => by rw [hC x hx, primitive₂_eq_primitiveX x hx]⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun x hx => by rw [hC x hx, primitive₂_eq_primitiveX x hx]⟩

end
end ProofGap.Exercise1927
