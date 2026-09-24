import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise906

noncomputable section

def rootTerm (a b : ℝ) : ℝ := Real.sqrt (b ^ 2 - a ^ 2)

def originalRatio (a b x : ℝ) : ℝ :=
  (b + a * Real.cos x + rootTerm a b * Real.sin x) /
    (a + b * Real.cos x)

def y (a b x : ℝ) : ℝ := Real.log (originalRatio a b x)

def normalizedU (a b x : ℝ) : ℝ :=
  (1 + (a / b) * Real.cos x + (rootTerm a b / b) * Real.sin x) /
    (a / b + Real.cos x)

def phaseU (φ x : ℝ) : ℝ :=
  (1 + Real.cos φ * Real.cos x + Real.sin φ * Real.sin x) /
    (Real.cos φ + Real.cos x)

def shiftedU (φ x : ℝ) : ℝ :=
  (1 + Real.cos (x - φ)) / (Real.cos x + Real.cos φ)

def v1 (φ x : ℝ) : ℝ := 1 + Real.cos (x - φ)
def v2 (φ x : ℝ) : ℝ := Real.cos x + Real.cos φ

def R (φ : ℝ) : Set ℝ :=
  {x | v1 φ x ≠ 0 ∧ 0 < v2 φ x}

def describedDomain (φ : ℝ) : Set ℝ :=
  {x | 0 < Real.cos x + Real.cos φ ∧
    ∀ k : ℤ, x ≠ (2 * (k : ℝ) + 1) * Real.pi + φ}

def phaseDerivative (φ x : ℝ) : ℝ :=
  -Real.sin (x - φ) / (1 + Real.cos (x - φ)) +
    Real.sin x / (Real.cos x + Real.cos φ)

def expandedPhaseDerivative (φ x : ℝ) : ℝ :=
  (-Real.sin x * Real.cos φ + Real.cos x * Real.sin φ) /
      (1 + Real.cos x * Real.cos φ + Real.sin x * Real.sin φ) +
    Real.sin x / (Real.cos x + Real.cos φ)

def normalizedDerivative (a b x : ℝ) : ℝ :=
  (-(a / b) * Real.sin x + (rootTerm a b / b) * Real.cos x) /
      (1 + (a / b) * Real.cos x + (rootTerm a b / b) * Real.sin x) +
    Real.sin x / (Real.cos x + a / b)

def finalDerivative (a b x : ℝ) : ℝ :=
  rootTerm a b / (a + b * Real.cos x)

private theorem originalRatio_eq_normalized (a b x : ℝ) (hb : b ≠ 0) :
    originalRatio a b x = normalizedU a b x := by
  unfold originalRatio normalizedU
  field_simp [hb]

private theorem deriv_log_div_algebra
    (u u' v v' : ℝ) (hu : u ≠ 0) (hv : v ≠ 0) :
    ((u' * v - u * v') / v ^ 2) / (u / v) =
      u' / u - v' / v := by
  field_simp [hu, hv]

private theorem normalized_derivative_algebra
    (A Q s c : ℝ)
    (hN : 1 + A * c + Q * s ≠ 0)
    (hD : A + c ≠ 0)
    (hunit : A ^ 2 + Q ^ 2 = 1)
    (htrig : s ^ 2 + c ^ 2 = 1) :
    (-A * s + Q * c) / (1 + A * c + Q * s) +
        s / (c + A) = Q / (A + c) := by
  have hp :
      (-A * s + Q * c) / (1 + A * c + Q * s) =
        (Q - s) / (A + c) := by
    apply (div_eq_div_iff hN hD).2
    calc
      (-A * s + Q * c) * (A + c) =
          (Q - s) * (1 + A * c + Q * s) +
            s * (1 - (A ^ 2 + Q ^ 2)) +
            Q * ((s ^ 2 + c ^ 2) - 1) := by ring
      _ = (Q - s) * (1 + A * c + Q * s) := by
        rw [hunit, htrig]
        ring
  rw [show c + A = A + c by ring, hp]
  ring

private theorem original_derivative_algebra
    (a b Q s c : ℝ)
    (hN : b + a * c + Q * s ≠ 0)
    (hD : a + b * c ≠ 0)
    (hQ : Q ^ 2 = b ^ 2 - a ^ 2)
    (htrig : s ^ 2 + c ^ 2 = 1) :
    (-a * s + Q * c) / (b + a * c + Q * s) +
        b * s / (a + b * c) = Q / (a + b * c) := by
  have hp :
      (-a * s + Q * c) / (b + a * c + Q * s) =
        (Q - b * s) / (a + b * c) := by
    apply (div_eq_div_iff hN hD).2
    calc
      (-a * s + Q * c) * (a + b * c) =
          (Q - b * s) * (b + a * c + Q * s) +
            s * (b ^ 2 - a ^ 2 - Q ^ 2) +
            b * Q * ((s ^ 2 + c ^ 2) - 1) := by ring
      _ = (Q - b * s) * (b + a * c + Q * s) := by
        rw [hQ, htrig]
        ring
  rw [hp]
  ring

theorem gap1 (a b x : ℝ) (ha : a = 0) (hb : 0 < b) :
    y a b x =
      Real.log ((1 + Real.sin x) / Real.cos x) := by
  subst a
  have hsqrt : Real.sqrt (b ^ 2 - 0 ^ 2) = b := by
    simp [Real.sqrt_sq_eq_abs, abs_of_pos hb]
  unfold y originalRatio rootTerm
  rw [hsqrt]
  apply congrArg Real.log
  simp only [zero_mul, zero_add]
  rw [show b + 0 + b * Real.sin x = b * (1 + Real.sin x) by ring]
  exact mul_div_mul_left (1 + Real.sin x) (Real.cos x) hb.ne'

theorem gap2 (a x : ℝ) (ha : a = 0) (hcos : 0 < Real.cos x) :
    0 < 1 + Real.sin x := by
  have hc2 : 0 < Real.cos x * Real.cos x := mul_pos hcos hcos
  nlinarith [Real.sin_sq_add_cos_sq x]

theorem gap3 (a x : ℝ) (k : ℤ) (ha : a = 0)
    (hlower : (2 * (k : ℝ) - 1 / 2) * Real.pi < x)
    (hupper : x < (2 * (k : ℝ) + 1 / 2) * Real.pi) :
    0 < Real.cos x := by
  let z : ℝ := x - (k : ℝ) * (2 * Real.pi)
  have hzlower : -(Real.pi / 2) < z := by
    dsimp [z]
    nlinarith [Real.pi_pos]
  have hzupper : z < Real.pi / 2 := by
    dsimp [z]
    nlinarith [Real.pi_pos]
  have hz : 0 < Real.cos z :=
    Real.cos_pos_of_mem_Ioo ⟨hzlower, hzupper⟩
  calc
    0 < Real.cos z := hz
    _ = Real.cos (z + (k : ℝ) * (2 * Real.pi)) :=
      (Real.cos_add_int_mul_two_pi z k).symm
    _ = Real.cos x := by
      congr 1
      dsimp [z]
      ring

theorem gap4 (a b x : ℝ) (k : ℤ) (ha : a = 0) (hb : 0 < b)
    (hlower : (2 * (k : ℝ) - 1 / 2) * Real.pi < x)
    (hupper : x < (2 * (k : ℝ) + 1 / 2) * Real.pi) :
    deriv (y a b) x =
      Real.cos x / (1 + Real.sin x) +
        Real.sin x / Real.cos x := by
  have hcpos : 0 < Real.cos x := gap3 a x k ha hlower hupper
  have hc : Real.cos x ≠ 0 := ne_of_gt hcpos
  have hnpos : 0 < 1 + Real.sin x := gap2 a x ha hcpos
  have hn : 1 + Real.sin x ≠ 0 := ne_of_gt hnpos
  have hy : y a b = fun t : ℝ =>
      Real.log ((1 + Real.sin t) / Real.cos t) := by
    funext t
    exact gap1 a b t ha hb
  have hnum : HasDerivAt (fun t : ℝ => 1 + Real.sin t)
      (Real.cos x) x := by
    convert (hasDerivAt_const (x := x) (c := (1 : ℝ))).add
      (Real.hasDerivAt_sin x) using 1 <;> ring
  have hquot := hnum.div (Real.hasDerivAt_cos x) hc
  have hlog := hquot.log (div_ne_zero hn hc)
  rw [hy]
  calc
    deriv (fun t : ℝ => Real.log ((1 + Real.sin t) / Real.cos t)) x =
        ((Real.cos x * Real.cos x -
            (1 + Real.sin x) * (-Real.sin x)) / Real.cos x ^ 2) /
          ((1 + Real.sin x) / Real.cos x) := by
      simpa only [Pi.div_apply] using hlog.deriv
    _ = Real.cos x / (1 + Real.sin x) -
        (-Real.sin x) / Real.cos x :=
      deriv_log_div_algebra
        (1 + Real.sin x) (Real.cos x)
        (Real.cos x) (-Real.sin x) hn hc
    _ = Real.cos x / (1 + Real.sin x) +
        Real.sin x / Real.cos x := by ring

theorem gap5 (x : ℝ) (k : ℤ)
    (hlower : (2 * (k : ℝ) - 1 / 2) * Real.pi < x)
    (hupper : x < (2 * (k : ℝ) + 1 / 2) * Real.pi) :
    Real.cos x / (1 + Real.sin x) +
        Real.sin x / Real.cos x =
      1 / Real.cos x := by
  have hcpos : 0 < Real.cos x := gap3 0 x k rfl hlower hupper
  have hc : Real.cos x ≠ 0 := ne_of_gt hcpos
  have hnpos : 0 < 1 + Real.sin x := gap2 0 x rfl hcpos
  have hn : 1 + Real.sin x ≠ 0 := ne_of_gt hnpos
  field_simp [hc, hn]
  nlinarith [Real.sin_sq_add_cos_sq x]

theorem gap6 (a b x : ℝ) (k : ℤ) (ha : a = 0) (hb : 0 < b)
    (hlower : (2 * (k : ℝ) - 1 / 2) * Real.pi < x)
    (hupper : x < (2 * (k : ℝ) + 1 / 2) * Real.pi) :
    deriv (y a b) x = 1 / Real.cos x := by
  rw [gap4 a b x k ha hb hlower hupper]
  exact gap5 x k hlower hupper

theorem gap7 (a b φ x : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcosφ : Real.cos φ = a / b)
    (hsinφ : Real.sin φ = rootTerm a b / b)
    (hden : a / b + Real.cos x ≠ 0) :
    normalizedU a b x = phaseU φ x := by
  unfold normalizedU phaseU
  rw [← hcosφ, ← hsinφ]

theorem gap8 (a φ x : ℝ) (ha : a ≠ 0)
    (hden : Real.cos φ + Real.cos x ≠ 0) :
    phaseU φ x = shiftedU φ x := by
  unfold phaseU shiftedU
  rw [Real.cos_sub]
  congr 1 <;> ring

theorem gap9 (a φ : ℝ) :
    ∃ w1 w2 : ℝ → ℝ, ∀ x, a ≠ 0 →
      w1 x = v1 φ x ∧ w2 x = v2 φ x ∧
        shiftedU φ x = w1 x / w2 x := by
  refine ⟨v1 φ, v2 φ, ?_⟩
  intro x hx
  exact ⟨rfl, rfl, rfl⟩

theorem gap10 (a b φ : ℝ) (hb : b ≠ 0)
    (hcosφ : Real.cos φ = a / b)
    (hsinφ : Real.sin φ = rootTerm a b / b) :
    ∃ w1 w2 : ℝ → ℝ, ∀ x, a ≠ 0 →
      w1 x = v1 φ x ∧ w2 x = v2 φ x ∧
        normalizedU a b x = w1 x / w2 x := by
  refine ⟨v1 φ, v2 φ, ?_⟩
  intro x ha
  refine ⟨rfl, rfl, ?_⟩
  unfold normalizedU v1 v2
  rw [← hcosφ, ← hsinφ, Real.cos_sub]
  congr 1 <;> ring

theorem gap11 (a φ x : ℝ) (ha : a ≠ 0) :
    0 ≤ v1 φ x := by
  unfold v1
  linarith [Real.neg_one_le_cos (x - φ)]

theorem gap12 (a b φ x : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcosφ : Real.cos φ = a / b)
    (hsinφ : Real.sin φ = rootTerm a b / b)
    (hx : x ∈ R φ) :
    0 < normalizedU a b x := by
  rcases hx with ⟨hv1, hv2⟩
  have hv1nonneg : 0 ≤ v1 φ x := gap11 a φ x ha
  have hv1pos : 0 < v1 φ x :=
    lt_of_le_of_ne hv1nonneg (Ne.symm hv1)
  rcases gap10 a b φ hb hcosφ hsinφ with ⟨w1, w2, hw⟩
  rcases hw x ha with ⟨hw1, hw2, hu⟩
  rw [hu, hw1, hw2]
  exact div_pos hv1pos hv2

theorem gap13 (a φ x : ℝ) (ha : a ≠ 0)
    (hx : ∀ k : ℤ, x ≠ (2 * (k : ℝ) + 1) * Real.pi + φ) :
    v1 φ x ≠ 0 := by
  intro hv
  have hc : Real.cos (x - φ) = -1 := by
    unfold v1 at hv
    linarith
  rcases (Real.cos_eq_neg_one_iff.mp hc) with ⟨k, hk⟩
  apply hx k
  nlinarith [hk]

theorem gap14 (a φ x : ℝ) (ha : a ≠ 0) :
    0 < v2 φ x ↔ 0 < Real.cos x + Real.cos φ := by
  rfl

theorem gap15 (a φ : ℝ) (ha : a ≠ 0) :
    R φ = describedDomain φ := by
  ext x
  simp only [R, describedDomain, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hv1, hv2⟩
    refine ⟨?_, ?_⟩
    · simpa [v2, add_comm] using hv2
    · intro k hk
      apply hv1
      subst x
      unfold v1
      rw [show
        ((2 * (k : ℝ) + 1) * Real.pi + φ) - φ =
          Real.pi + (k : ℝ) * (2 * Real.pi) by ring]
      rw [Real.cos_add_int_mul_two_pi, Real.cos_pi]
      ring
  · rintro ⟨hv2, hodd⟩
    refine ⟨gap13 a φ x ha hodd, ?_⟩
    simpa [v2, add_comm] using hv2

theorem gap16 (a b φ x : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcosφ : Real.cos φ = a / b)
    (hsinφ : Real.sin φ = rootTerm a b / b)
    (hx : x ∈ R φ) :
    deriv (y a b) x = phaseDerivative φ x := by
  rcases hx with ⟨hv1, hv2⟩
  have hy : y a b = fun t : ℝ =>
      Real.log
        ((1 + Real.cos φ * Real.cos t + Real.sin φ * Real.sin t) /
          (Real.cos φ + Real.cos t)) := by
    funext t
    unfold y
    congr 1
    calc
      originalRatio a b t = normalizedU a b t :=
        originalRatio_eq_normalized a b t hb
      _ = (1 + Real.cos φ * Real.cos t + Real.sin φ * Real.sin t) /
          (Real.cos φ + Real.cos t) := by
        unfold normalizedU
        rw [← hcosφ, ← hsinφ]
  have hf : HasDerivAt
      (fun t : ℝ =>
        1 + Real.cos φ * Real.cos t + Real.sin φ * Real.sin t)
      (-Real.cos φ * Real.sin x + Real.sin φ * Real.cos x) x := by
    convert
      ((hasDerivAt_const (x := x) (c := (1 : ℝ))).add
        ((Real.hasDerivAt_cos x).const_mul (Real.cos φ))).add
          ((Real.hasDerivAt_sin x).const_mul (Real.sin φ)) using 1 <;> ring
  have hg : HasDerivAt
      (fun t : ℝ => Real.cos φ + Real.cos t)
      (-Real.sin x) x := by
    convert (hasDerivAt_const (x := x) (c := Real.cos φ)).add
      (Real.hasDerivAt_cos x) using 1 <;> ring
  have hfeq :
      1 + Real.cos φ * Real.cos x + Real.sin φ * Real.sin x =
        v1 φ x := by
    unfold v1
    rw [Real.cos_sub]
    ring
  have hfne :
      1 + Real.cos φ * Real.cos x + Real.sin φ * Real.sin x ≠ 0 := by
    rw [hfeq]
    exact hv1
  have hgne : Real.cos φ + Real.cos x ≠ 0 := by
    have : 0 < Real.cos φ + Real.cos x := by
      simpa [v2, add_comm] using hv2
    exact ne_of_gt this
  have hlog := (hf.div hg hgne).log (div_ne_zero hfne hgne)
  rw [hy]
  calc
    deriv
        (fun t : ℝ =>
          Real.log
            ((1 + Real.cos φ * Real.cos t + Real.sin φ * Real.sin t) /
              (Real.cos φ + Real.cos t))) x =
      (((-Real.cos φ * Real.sin x + Real.sin φ * Real.cos x) *
            (Real.cos φ + Real.cos x) -
          (1 + Real.cos φ * Real.cos x + Real.sin φ * Real.sin x) *
            (-Real.sin x)) /
        (Real.cos φ + Real.cos x) ^ 2) /
          ((1 + Real.cos φ * Real.cos x + Real.sin φ * Real.sin x) /
            (Real.cos φ + Real.cos x)) := by
      simpa only [Pi.div_apply] using hlog.deriv
    _ = (-Real.cos φ * Real.sin x + Real.sin φ * Real.cos x) /
          (1 + Real.cos φ * Real.cos x + Real.sin φ * Real.sin x) -
        (-Real.sin x) / (Real.cos φ + Real.cos x) :=
      deriv_log_div_algebra
        (1 + Real.cos φ * Real.cos x + Real.sin φ * Real.sin x)
        (-Real.cos φ * Real.sin x + Real.sin φ * Real.cos x)
        (Real.cos φ + Real.cos x) (-Real.sin x) hfne hgne
    _ = phaseDerivative φ x := by
      unfold phaseDerivative
      rw [Real.sin_sub, Real.cos_sub]
      ring

theorem gap17 (a φ x : ℝ) (ha : a ≠ 0) (hx : x ∈ R φ) :
    phaseDerivative φ x = expandedPhaseDerivative φ x := by
  unfold phaseDerivative expandedPhaseDerivative
  rw [Real.sin_sub, Real.cos_sub]
  ring

theorem gap18 (a b φ x : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcosφ : Real.cos φ = a / b)
    (hsinφ : Real.sin φ = rootTerm a b / b)
    (hx : x ∈ R φ) :
    deriv (y a b) x = expandedPhaseDerivative φ x := by
  calc
    deriv (y a b) x = phaseDerivative φ x :=
      gap16 a b φ x ha hb hcosφ hsinφ hx
    _ = expandedPhaseDerivative φ x := gap17 a φ x ha hx

theorem gap19 (a b φ x : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcosφ : Real.cos φ = a / b)
    (hsinφ : Real.sin φ = rootTerm a b / b)
    (hx : x ∈ R φ) :
    deriv (y a b) x = normalizedDerivative a b x := by
  calc
    deriv (y a b) x = expandedPhaseDerivative φ x :=
      gap18 a b φ x ha hb hcosφ hsinφ hx
    _ = normalizedDerivative a b x := by
      unfold expandedPhaseDerivative normalizedDerivative
      rw [hcosφ, hsinφ]
      ring

theorem gap20 (a b φ x : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcosφ : Real.cos φ = a / b)
    (hsinφ : Real.sin φ = rootTerm a b / b)
    (hx : x ∈ R φ) :
    normalizedDerivative a b x = finalDerivative a b x := by
  have hNeq :
      1 + (a / b) * Real.cos x +
          (rootTerm a b / b) * Real.sin x = v1 φ x := by
    unfold v1
    rw [Real.cos_sub, hcosφ, hsinφ]
    ring
  have hN :
      1 + (a / b) * Real.cos x +
          (rootTerm a b / b) * Real.sin x ≠ 0 := by
    rw [hNeq]
    exact hx.1
  have hDpos : 0 < a / b + Real.cos x := by
    simpa [v2, hcosφ, add_comm] using hx.2
  have hD : a / b + Real.cos x ≠ 0 := ne_of_gt hDpos
  have hunit0 := Real.sin_sq_add_cos_sq φ
  rw [hsinφ, hcosφ] at hunit0
  have hunit :
      (a / b) ^ 2 + (rootTerm a b / b) ^ 2 = 1 := by
    nlinarith [hunit0]
  have hscale :
      a + b * Real.cos x = b * (a / b + Real.cos x) := by
    field_simp [hb]
  have hfinal : a + b * Real.cos x ≠ 0 := by
    rw [hscale]
    exact mul_ne_zero hb hD
  unfold normalizedDerivative finalDerivative
  calc
    (-(a / b) * Real.sin x + (rootTerm a b / b) * Real.cos x) /
          (1 + (a / b) * Real.cos x +
            (rootTerm a b / b) * Real.sin x) +
        Real.sin x / (Real.cos x + a / b) =
      (rootTerm a b / b) / (a / b + Real.cos x) :=
        normalized_derivative_algebra
          (a / b) (rootTerm a b / b) (Real.sin x) (Real.cos x)
          hN hD hunit (Real.sin_sq_add_cos_sq x)
    _ = rootTerm a b / (a + b * Real.cos x) := by
      field_simp [hb, hD, hfinal]

theorem gap21 (a b φ x : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcosφ : Real.cos φ = a / b)
    (hsinφ : Real.sin φ = rootTerm a b / b)
    (hx : x ∈ R φ) :
    deriv (y a b) x = finalDerivative a b x := by
  calc
    deriv (y a b) x = normalizedDerivative a b x :=
      gap19 a b φ x ha hb hcosφ hsinφ hx
    _ = finalDerivative a b x :=
      gap20 a b φ x ha hb hcosφ hsinφ hx

theorem gap22 (a b x : ℝ) (hb : 0 < b) (habs : |a| < b)
    (hratio : 0 < originalRatio a b x)
    (hden : a + b * Real.cos x ≠ 0) :
    deriv (y a b) x = finalDerivative a b x := by
  rcases abs_lt.mp habs with ⟨halower, haupper⟩
  have hprod : 0 < (b - a) * (b + a) := by
    apply mul_pos
    · exact sub_pos.mpr haupper
    · linarith
  have hrad : 0 ≤ b ^ 2 - a ^ 2 := by
    nlinarith [hprod]
  have hrsq : (rootTerm a b) ^ 2 = b ^ 2 - a ^ 2 := by
    unfold rootTerm
    exact Real.sq_sqrt hrad
  have hnum :
      b + a * Real.cos x + rootTerm a b * Real.sin x ≠ 0 := by
    intro hn
    have hz : originalRatio a b x = 0 := by
      unfold originalRatio
      rw [hn]
      simp
    exact (ne_of_gt hratio) hz
  have hnDeriv : HasDerivAt
      (fun t : ℝ =>
        b + a * Real.cos t + rootTerm a b * Real.sin t)
      (-a * Real.sin x + rootTerm a b * Real.cos x) x := by
    convert
      ((hasDerivAt_const (x := x) (c := b)).add
        ((Real.hasDerivAt_cos x).const_mul a)).add
          ((Real.hasDerivAt_sin x).const_mul (rootTerm a b)) using 1 <;> ring
  have hdDeriv : HasDerivAt
      (fun t : ℝ => a + b * Real.cos t)
      (-b * Real.sin x) x := by
    convert (hasDerivAt_const (x := x) (c := a)).add
      ((Real.hasDerivAt_cos x).const_mul b) using 1 <;> ring
  have hlog := (hnDeriv.div hdDeriv hden).log
    (div_ne_zero hnum hden)
  change deriv
      (fun t : ℝ =>
        Real.log
          ((b + a * Real.cos t + rootTerm a b * Real.sin t) /
            (a + b * Real.cos t))) x =
      rootTerm a b / (a + b * Real.cos x)
  calc
    deriv
        (fun t : ℝ =>
          Real.log
            ((b + a * Real.cos t + rootTerm a b * Real.sin t) /
              (a + b * Real.cos t))) x =
      (((-a * Real.sin x + rootTerm a b * Real.cos x) *
            (a + b * Real.cos x) -
          (b + a * Real.cos x + rootTerm a b * Real.sin x) *
            (-b * Real.sin x)) /
        (a + b * Real.cos x) ^ 2) /
          ((b + a * Real.cos x + rootTerm a b * Real.sin x) /
            (a + b * Real.cos x)) := by
      simpa only [Pi.div_apply] using hlog.deriv
    _ = (-a * Real.sin x + rootTerm a b * Real.cos x) /
          (b + a * Real.cos x + rootTerm a b * Real.sin x) +
        b * Real.sin x / (a + b * Real.cos x) := by
      calc
        _ = (-a * Real.sin x + rootTerm a b * Real.cos x) /
              (b + a * Real.cos x + rootTerm a b * Real.sin x) -
            (-b * Real.sin x) / (a + b * Real.cos x) :=
          deriv_log_div_algebra
            (b + a * Real.cos x + rootTerm a b * Real.sin x)
            (-a * Real.sin x + rootTerm a b * Real.cos x)
            (a + b * Real.cos x) (-b * Real.sin x) hnum hden
        _ = _ := by ring
    _ = rootTerm a b / (a + b * Real.cos x) :=
      original_derivative_algebra
        a b (rootTerm a b) (Real.sin x) (Real.cos x)
        hnum hden hrsq (Real.sin_sq_add_cos_sq x)

end

end ProofGap.Exercise906
