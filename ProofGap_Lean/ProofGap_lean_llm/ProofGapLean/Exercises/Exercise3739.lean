import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3739

noncomputable section

open Filter Set MeasureTheory
open scoped Interval Topology

def radicand (k φ : ℝ) : ℝ :=
  1 - k ^ 2 * Real.sin φ ^ 2

def ellipticE (k : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..Real.pi / 2, Real.sqrt (radicand k φ)

def ellipticK (k : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..Real.pi / 2, 1 / Real.sqrt (radicand k φ)

def firstPrimitive (k : ℝ) : ℝ :=
  ellipticE k - (1 - k ^ 2) * ellipticK k

def secondPrimitive (k : ℝ) : ℝ :=
  (1 / 3 : ℝ) *
    ((1 + k ^ 2) * ellipticE k - (1 - k ^ 2) * ellipticK k)

def firstConstant : ℝ := 0
def secondConstant : ℝ := 0

private lemma sin_sq_le_one (x : ℝ) : Real.sin x ^ 2 ≤ 1 := by
  nlinarith [Real.neg_one_le_sin x, Real.sin_le_one x]

private lemma radicand_lower {q r θ : ℝ} (hr : 0 ≤ r)
    (hq : q ∈ Ioo (-r) r) :
    1 - r ^ 2 ≤ 1 - q ^ 2 * Real.sin θ ^ 2 := by
  have hq2 : q ^ 2 ≤ r ^ 2 := by nlinarith [hq.1, hq.2]
  have hs0 : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  have hs1 := sin_sq_le_one θ
  have hmul : q ^ 2 * Real.sin θ ^ 2 ≤ r ^ 2 := calc
    q ^ 2 * Real.sin θ ^ 2 ≤ r ^ 2 * Real.sin θ ^ 2 :=
      mul_le_mul_of_nonneg_right hq2 hs0
    _ ≤ r ^ 2 * 1 := mul_le_mul_of_nonneg_left hs1 (sq_nonneg r)
    _ = r ^ 2 := by ring
  linarith

private lemma hasDerivAt_E_integrand (p θ : ℝ)
    (hpos : 0 < 1 - p ^ 2 * Real.sin θ ^ 2) :
    HasDerivAt
      (fun q : ℝ => Real.sqrt (1 - q ^ 2 * Real.sin θ ^ 2))
      (-p * Real.sin θ ^ 2 /
        Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2)) p := by
  have hinner :
      HasDerivAt
        (fun q : ℝ => 1 - q ^ 2 * Real.sin θ ^ 2)
        (-2 * p * Real.sin θ ^ 2) p := by
    convert (hasDerivAt_const p (1 : ℝ)).sub
      (((hasDerivAt_id p).pow 2).mul_const (Real.sin θ ^ 2)) using 1 <;>
        simp only [id_eq] <;> ring
  convert hinner.sqrt (ne_of_gt hpos) using 1
  field_simp [ne_of_gt (Real.sqrt_pos.2 hpos)]

private lemma hasDerivAt_K_integrand (p θ : ℝ)
    (hpos : 0 < 1 - p ^ 2 * Real.sin θ ^ 2) :
    HasDerivAt
      (fun q : ℝ => (Real.sqrt (1 - q ^ 2 * Real.sin θ ^ 2))⁻¹)
      (p * Real.sin θ ^ 2 /
        (Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2)) ^ 3) p := by
  have hsqrt := hasDerivAt_E_integrand p θ hpos
  have hne : Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  convert hsqrt.inv hne using 1
  field_simp [hne]

private lemma hasDerivAt_eE (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    HasDerivAt ellipticE
      (∫ θ in (0 : ℝ)..Real.pi / 2,
        -p * Real.sin θ ^ 2 /
          Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2)) p := by
  let r : ℝ := (p + 1) / 2
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hpr : p < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hδ : 0 < 1 - r ^ 2 := by nlinarith
  let s : Set ℝ := Ioo (-r) r
  have hs : s ∈ 𝓝 p := by
    apply Ioo_mem_nhds
    · dsimp [s]
      linarith
    · exact hpr
  let F : ℝ → ℝ → ℝ :=
    fun q θ => Real.sqrt (1 - q ^ 2 * Real.sin θ ^ 2)
  let F' : ℝ → ℝ → ℝ :=
    fun q θ => -q * Real.sin θ ^ 2 /
      Real.sqrt (1 - q ^ 2 * Real.sin θ ^ 2)
  let bound : ℝ → ℝ := fun _ => r / Real.sqrt (1 - r ^ 2)
  have hF_meas :
      ∀ᶠ q in 𝓝 p,
        AEStronglyMeasurable (F q)
          (volume.restrict (Ι (0 : ℝ) (Real.pi / 2))) := by
    filter_upwards with q
    exact (by
      dsimp [F]
      fun_prop : Continuous (F q)).aestronglyMeasurable
  have hF_int : IntervalIntegrable (F p) volume 0 (Real.pi / 2) := by
    apply Continuous.intervalIntegrable
    dsimp [F]
    fun_prop
  have hF'_meas :
      AEStronglyMeasurable (F' p)
        (volume.restrict (Ι (0 : ℝ) (Real.pi / 2))) := by
    have hp_mem : p ∈ s := by
      change p ∈ Ioo (-r) r
      exact ⟨by linarith, hpr⟩
    have hpos : ∀ θ : ℝ, 0 < 1 - p ^ 2 * Real.sin θ ^ 2 := by
      intro θ
      have := radicand_lower hr0.le hp_mem (θ := θ)
      linarith
    have hcont : Continuous (F' p) := by
      dsimp [F']
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro θ
        exact ne_of_gt (Real.sqrt_pos.2 (hpos θ))
    exact hcont.aestronglyMeasurable
  have h_bound :
      ∀ᵐ θ ∂volume, θ ∈ Ι (0 : ℝ) (Real.pi / 2) →
        ∀ q ∈ s, ‖F' q θ‖ ≤ bound θ := by
    filter_upwards with θ hθ q hq
    have hlow := radicand_lower hr0.le hq (θ := θ)
    have hpos : 0 < 1 - q ^ 2 * Real.sin θ ^ 2 := hδ.trans_le hlow
    have hs0 : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
    have hs1 := sin_sq_le_one θ
    have hqabs : |q| ≤ r := by
      rw [abs_le]
      exact ⟨hq.1.le, hq.2.le⟩
    have hsqrt :
        Real.sqrt (1 - r ^ 2) ≤
          Real.sqrt (1 - q ^ 2 * Real.sin θ ^ 2) :=
      Real.sqrt_le_sqrt hlow
    have hsqrt0 : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.2 hδ
    have hden0 :
        0 < Real.sqrt (1 - q ^ 2 * Real.sin θ ^ 2) :=
      Real.sqrt_pos.2 hpos
    dsimp [F', bound]
    simp only [Real.norm_eq_abs, abs_div, abs_of_pos hden0,
      abs_mul, abs_neg, abs_of_nonneg hs0]
    apply (div_le_iff₀ hden0).2
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hsqrt0).2
    calc
      |q| * Real.sin θ ^ 2 * Real.sqrt (1 - r ^ 2) ≤
          r * 1 * Real.sqrt (1 - r ^ 2) := by
            gcongr
      _ ≤ r * Real.sqrt (1 - q ^ 2 * Real.sin θ ^ 2) := by
            nlinarith
  have hbound_int :
      IntervalIntegrable bound volume 0 (Real.pi / 2) := by
    have : Continuous bound := by
      dsimp [bound]
      fun_prop
    exact this.intervalIntegrable 0 (Real.pi / 2)
  have hdiff :
      ∀ᵐ θ ∂volume, θ ∈ Ι (0 : ℝ) (Real.pi / 2) →
        ∀ q ∈ s, HasDerivAt (fun q => F q θ) (F' q θ) q := by
    filter_upwards with θ hθ q hq
    have hlow := radicand_lower hr0.le hq (θ := θ)
    have hpos : 0 < 1 - q ^ 2 * Real.sin θ ^ 2 := hδ.trans_le hlow
    exact hasDerivAt_E_integrand q θ hpos
  have main :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)
      (x₀ := p) (s := s) (bound := bound)
      hs hF_meas hF_int hF'_meas h_bound hbound_int hdiff
  simpa [ellipticE, radicand, F, F'] using main.2

private lemma hasDerivAt_eK (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    HasDerivAt ellipticK
      (∫ θ in (0 : ℝ)..Real.pi / 2,
        p * Real.sin θ ^ 2 /
          (Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2)) ^ 3) p := by
  let r : ℝ := (p + 1) / 2
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hpr : p < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hδ : 0 < 1 - r ^ 2 := by nlinarith
  let s : Set ℝ := Ioo (-r) r
  have hs : s ∈ 𝓝 p := by
    apply Ioo_mem_nhds
    · dsimp [s]
      linarith
    · exact hpr
  let F : ℝ → ℝ → ℝ :=
    fun q θ => (Real.sqrt (1 - q ^ 2 * Real.sin θ ^ 2))⁻¹
  let F' : ℝ → ℝ → ℝ :=
    fun q θ => q * Real.sin θ ^ 2 /
      (Real.sqrt (1 - q ^ 2 * Real.sin θ ^ 2)) ^ 3
  let bound : ℝ → ℝ :=
    fun _ => r / (Real.sqrt (1 - r ^ 2)) ^ 3
  have hF_meas :
      ∀ᶠ q in 𝓝 p,
        AEStronglyMeasurable (F q)
          (volume.restrict (Ι (0 : ℝ) (Real.pi / 2))) := by
    filter_upwards [hs] with q hq
    have hpos : ∀ θ : ℝ, 0 < 1 - q ^ 2 * Real.sin θ ^ 2 := by
      intro θ
      have hlow := radicand_lower hr0.le hq (θ := θ)
      exact hδ.trans_le hlow
    have hcont : Continuous (F q) := by
      dsimp [F]
      apply Continuous.inv₀
      · fun_prop
      · intro θ
        exact ne_of_gt (Real.sqrt_pos.2 (hpos θ))
    exact hcont.aestronglyMeasurable
  have hF_int : IntervalIntegrable (F p) volume 0 (Real.pi / 2) := by
    have hp_mem : p ∈ s := by
      change p ∈ Ioo (-r) r
      exact ⟨by linarith, hpr⟩
    have hpos : ∀ θ : ℝ, 0 < 1 - p ^ 2 * Real.sin θ ^ 2 := by
      intro θ
      have hlow := radicand_lower hr0.le hp_mem (θ := θ)
      exact hδ.trans_le hlow
    apply Continuous.intervalIntegrable
    dsimp [F]
    apply Continuous.inv₀
    · fun_prop
    · intro θ
      exact ne_of_gt (Real.sqrt_pos.2 (hpos θ))
  have hF'_meas :
      AEStronglyMeasurable (F' p)
        (volume.restrict (Ι (0 : ℝ) (Real.pi / 2))) := by
    have hp_mem : p ∈ s := by
      change p ∈ Ioo (-r) r
      exact ⟨by linarith, hpr⟩
    have hpos : ∀ θ : ℝ, 0 < 1 - p ^ 2 * Real.sin θ ^ 2 := by
      intro θ
      have hlow := radicand_lower hr0.le hp_mem (θ := θ)
      exact hδ.trans_le hlow
    have hcont : Continuous (F' p) := by
      dsimp [F']
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro θ
        exact pow_ne_zero 3 (ne_of_gt (Real.sqrt_pos.2 (hpos θ)))
    exact hcont.aestronglyMeasurable
  have h_bound :
      ∀ᵐ θ ∂volume, θ ∈ Ι (0 : ℝ) (Real.pi / 2) →
        ∀ q ∈ s, ‖F' q θ‖ ≤ bound θ := by
    filter_upwards with θ hθ q hq
    have hlow := radicand_lower hr0.le hq (θ := θ)
    have hpos : 0 < 1 - q ^ 2 * Real.sin θ ^ 2 := hδ.trans_le hlow
    have hs0 : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
    have hs1 := sin_sq_le_one θ
    have hqabs : |q| ≤ r := by
      rw [abs_le]
      exact ⟨hq.1.le, hq.2.le⟩
    have hnum : |q| * Real.sin θ ^ 2 ≤ r := calc
      |q| * Real.sin θ ^ 2 ≤ r * 1 := by gcongr
      _ = r := by ring
    have hsqrt :
        Real.sqrt (1 - r ^ 2) ≤
          Real.sqrt (1 - q ^ 2 * Real.sin θ ^ 2) :=
      Real.sqrt_le_sqrt hlow
    have hsqrt0 : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.2 hδ
    have hden0 :
        0 < Real.sqrt (1 - q ^ 2 * Real.sin θ ^ 2) :=
      Real.sqrt_pos.2 hpos
    have hpow :
        (Real.sqrt (1 - r ^ 2)) ^ 3 ≤
          (Real.sqrt (1 - q ^ 2 * Real.sin θ ^ 2)) ^ 3 := by
      gcongr
    dsimp [F', bound]
    simp only [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hden0 3),
      abs_mul, abs_of_nonneg hs0]
    apply (div_le_div_iff₀ (pow_pos hden0 3) (pow_pos hsqrt0 3)).2
    exact mul_le_mul hnum hpow (pow_nonneg (Real.sqrt_nonneg _) 3) hr0.le
  have hbound_int :
      IntervalIntegrable bound volume 0 (Real.pi / 2) := by
    have : Continuous bound := by
      dsimp [bound]
      fun_prop
    exact this.intervalIntegrable 0 (Real.pi / 2)
  have hdiff :
      ∀ᵐ θ ∂volume, θ ∈ Ι (0 : ℝ) (Real.pi / 2) →
        ∀ q ∈ s, HasDerivAt (fun q => F q θ) (F' q θ) q := by
    filter_upwards with θ hθ q hq
    have hlow := radicand_lower hr0.le hq (θ := θ)
    have hpos : 0 < 1 - q ^ 2 * Real.sin θ ^ 2 := hδ.trans_le hlow
    exact hasDerivAt_K_integrand q θ hpos
  have main :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)
      (x₀ := p) (s := s) (bound := bound)
      hs hF_meas hF_int hF'_meas h_bound hbound_int hdiff
  have heK : ellipticK =
      (fun k : ℝ => ∫ θ in (0 : ℝ)..Real.pi / 2,
        (Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))⁻¹) := by
    funext k
    simp [ellipticK, radicand, one_div]
  rw [heK]
  simpa [F, F'] using main.2

private lemma radicand_pos_of_lt_one {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p < 1) (θ : ℝ) :
    0 < 1 - p ^ 2 * Real.sin θ ^ 2 := by
  have hs0 : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  have hs1 := sin_sq_le_one θ
  have hp2 : p ^ 2 < 1 := by nlinarith
  have hmul : p ^ 2 * Real.sin θ ^ 2 < 1 := calc
    p ^ 2 * Real.sin θ ^ 2 ≤ p ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hs1 (sq_nonneg p)
    _ < 1 := by simpa using hp2
  linarith

private lemma hasDerivAt_theta_aux (p θ : ℝ)
    (hpos : 0 < 1 - p ^ 2 * Real.sin θ ^ 2) :
    HasDerivAt
      (fun x : ℝ =>
        Real.sin x * Real.cos x /
          Real.sqrt (1 - p ^ 2 * Real.sin x ^ 2))
      (Real.cos θ ^ 2 /
          Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2) -
        (1 - p ^ 2) * Real.sin θ ^ 2 /
          (Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2)) ^ 3) θ := by
  have hinner :
      HasDerivAt
        (fun x : ℝ => 1 - p ^ 2 * Real.sin x ^ 2)
        (-2 * p ^ 2 * Real.sin θ * Real.cos θ) θ := by
    convert (hasDerivAt_const θ (1 : ℝ)).sub
      (((Real.hasDerivAt_sin θ).pow 2).const_mul (p ^ 2)) using 1 <;> ring
  have hsqrt :
      HasDerivAt
        (fun x : ℝ => Real.sqrt (1 - p ^ 2 * Real.sin x ^ 2))
        (-p ^ 2 * Real.sin θ * Real.cos θ /
          Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2)) θ := by
    convert hinner.sqrt (ne_of_gt hpos) using 1
    field_simp [ne_of_gt (Real.sqrt_pos.2 hpos)]
  have hden : Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  have hinv :
      HasDerivAt
        (fun x : ℝ =>
          (Real.sqrt (1 - p ^ 2 * Real.sin x ^ 2))⁻¹)
        (p ^ 2 * Real.sin θ * Real.cos θ /
          (Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2)) ^ 3) θ := by
    convert hsqrt.inv hden using 1
    field_simp [hden]
  have htrig :
      HasDerivAt (fun x : ℝ => Real.sin x * Real.cos x)
        (Real.cos θ ^ 2 - Real.sin θ ^ 2) θ := by
    convert (Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_cos θ) using 1
    ring
  have hmul := htrig.mul hinv
  convert hmul using 1
  have hsquare :
      (Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2)) ^ 2 =
        1 - p ^ 2 * Real.sin θ ^ 2 :=
    Real.sq_sqrt hpos.le
  field_simp [hden]
  rw [hsquare]
  have htrig_sq : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [htrig_sq]
  ring

private lemma theta_aux_integral_zero (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    (∫ θ in (0 : ℝ)..Real.pi / 2,
      Real.cos θ ^ 2 /
          Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2) -
        (1 - p ^ 2) * Real.sin θ ^ 2 /
          (Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2)) ^ 3) = 0 := by
  let D : ℝ → ℝ := fun θ =>
    Real.cos θ ^ 2 /
        Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2) -
      (1 - p ^ 2) * Real.sin θ ^ 2 /
        (Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2)) ^ 3
  have hD : Continuous D := by
    dsimp [D]
    apply Continuous.sub
    · apply Continuous.div
      · fun_prop
      · fun_prop
      · intro θ
        exact ne_of_gt (Real.sqrt_pos.2 (radicand_pos_of_lt_one hp0 hp1 θ))
    · apply Continuous.div
      · fun_prop
      · fun_prop
      · intro θ
        exact pow_ne_zero 3
          (ne_of_gt (Real.sqrt_pos.2 (radicand_pos_of_lt_one hp0 hp1 θ)))
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := Real.pi / 2)
      (f := fun θ : ℝ =>
        Real.sin θ * Real.cos θ /
          Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2))
      (f' := D)
      (fun θ _ => hasDerivAt_theta_aux p θ
        (radicand_pos_of_lt_one hp0 hp1 θ))
      (hD.intervalIntegrable 0 (Real.pi / 2))
  simpa [D] using hFTC

private lemma intervalIntegrable_E_integrand (p : ℝ) :
    IntervalIntegrable
      (fun θ : ℝ => Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2))
      volume 0 (Real.pi / 2) := by
  apply Continuous.intervalIntegrable
  fun_prop

private lemma intervalIntegrable_K_integrand (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p < 1) :
    IntervalIntegrable
      (fun θ : ℝ => (Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2))⁻¹)
      volume 0 (Real.pi / 2) := by
  apply Continuous.intervalIntegrable
  apply Continuous.inv₀
  · fun_prop
  · intro θ
    exact ne_of_gt (Real.sqrt_pos.2 (radicand_pos_of_lt_one hp0 hp1 θ))

private lemma hasDerivAt_eE_formula (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt ellipticE ((ellipticE p - ellipticK p) / p) p := by
  have hraw := hasDerivAt_eE p hp0.le hp1
  convert hraw using 1
  have hEint := intervalIntegrable_E_integrand p
  have hKint := intervalIntegrable_K_integrand p hp0.le hp1
  have hpos := radicand_pos_of_lt_one hp0.le hp1
  rw [ellipticE, ellipticK]
  have hpoint :
      (fun θ : ℝ =>
        -p * Real.sin θ ^ 2 /
          Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2)) =
      (fun θ : ℝ =>
        Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2) / p -
          (Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2))⁻¹ / p) := by
    funext θ
    have hden := ne_of_gt (Real.sqrt_pos.2 (hpos θ))
    have hsquare := Real.sq_sqrt (hpos θ).le
    field_simp [hden, ne_of_gt hp0]
    nlinarith
  rw [hpoint, intervalIntegral.integral_sub
    (hEint.div_const p) (hKint.div_const p)]
  simp only [radicand, one_div, div_eq_mul_inv,
    intervalIntegral.integral_mul_const]
  ring

private lemma hasDerivAt_eK_formula (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt ellipticK
      (ellipticE p / (p * (1 - p ^ 2)) - ellipticK p / p) p := by
  have hraw := hasDerivAt_eK p hp0.le hp1
  convert hraw using 1
  have hEint := intervalIntegrable_E_integrand p
  have hKint := intervalIntegrable_K_integrand p hp0.le hp1
  have hpos := radicand_pos_of_lt_one hp0.le hp1
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hone : 1 - p ^ 2 ≠ 0 := by nlinarith
  let D : ℝ → ℝ := fun θ =>
    Real.cos θ ^ 2 /
        Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2) -
      (1 - p ^ 2) * Real.sin θ ^ 2 /
        (Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2)) ^ 3
  let R : ℝ → ℝ := fun θ =>
    Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2) /
        (p * (1 - p ^ 2)) -
      (Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2))⁻¹ / p
  have hDint : IntervalIntegrable D volume 0 (Real.pi / 2) := by
    dsimp [D]
    apply Continuous.intervalIntegrable
    apply Continuous.sub
    · apply Continuous.div
      · fun_prop
      · fun_prop
      · intro θ
        exact ne_of_gt (Real.sqrt_pos.2 (hpos θ))
    · apply Continuous.div
      · fun_prop
      · fun_prop
      · intro θ
        exact pow_ne_zero 3 (ne_of_gt (Real.sqrt_pos.2 (hpos θ)))
  have hRint : IntervalIntegrable R volume 0 (Real.pi / 2) := by
    dsimp [R]
    exact (hEint.div_const (p * (1 - p ^ 2))).sub (hKint.div_const p)
  have hpoint :
      (fun θ : ℝ =>
        p * Real.sin θ ^ 2 /
          (Real.sqrt (1 - p ^ 2 * Real.sin θ ^ 2)) ^ 3) =
      (fun θ : ℝ => R θ - (p / (1 - p ^ 2)) * D θ) := by
    funext θ
    have hden := ne_of_gt (Real.sqrt_pos.2 (hpos θ))
    have hsquare := Real.sq_sqrt (hpos θ).le
    dsimp [R, D]
    field_simp [hden, hpne, hone]
    rw [hsquare]
    have htrig_sq : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [htrig_sq]
    ring
  rw [hpoint, intervalIntegral.integral_sub hRint
    (hDint.const_mul (p / (1 - p ^ 2))),
    intervalIntegral.integral_const_mul,
    theta_aux_integral_zero p hp0.le hp1]
  dsimp [R]
  rw [intervalIntegral.integral_sub
    (hEint.div_const (p * (1 - p ^ 2))) (hKint.div_const p)]
  simp only [div_eq_mul_inv, intervalIntegral.integral_mul_const]
  rw [ellipticE, ellipticK]
  simp only [radicand, one_div]
  ring

private lemma hasDerivAt_one_sub_sq (p : ℝ) :
    HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * p) p := by
  convert (hasDerivAt_const p (1 : ℝ)).sub ((hasDerivAt_id p).pow 2) using 1 <;>
    simp only [id_eq] <;> ring

private lemma hasDerivAt_one_add_sq (p : ℝ) :
    HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * p) p := by
  convert (hasDerivAt_const p (1 : ℝ)).add ((hasDerivAt_id p).pow 2) using 1 <;>
    simp only [id_eq] <;> ring

private lemma hasDerivAt_firstPrimitive
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    HasDerivAt firstPrimitive (ellipticK p * p) p := by
  by_cases hp : p = 0
  · subst p
    have hEraw := hasDerivAt_eE 0 le_rfl zero_lt_one
    have hKraw := hasDerivAt_eK 0 le_rfl zero_lt_one
    have hE : HasDerivAt ellipticE 0 0 := by simpa using hEraw
    have hK : HasDerivAt ellipticK 0 0 := by simpa using hKraw
    have h := hE.sub ((hasDerivAt_one_sub_sq 0).mul hK)
    convert h using 1 <;> simp [firstPrimitive]
  · have hp_pos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hp)
    have hE := hasDerivAt_eE_formula p hp_pos hp1
    have hK := hasDerivAt_eK_formula p hp_pos hp1
    have h := hE.sub ((hasDerivAt_one_sub_sq p).mul hK)
    convert h using 1
    field_simp [hp, show 1 - p ^ 2 ≠ 0 by nlinarith]
    ring

private lemma hasDerivAt_secondPrimitive
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    HasDerivAt secondPrimitive (ellipticE p * p) p := by
  by_cases hp : p = 0
  · subst p
    have hEraw := hasDerivAt_eE 0 le_rfl zero_lt_one
    have hKraw := hasDerivAt_eK 0 le_rfl zero_lt_one
    have hE : HasDerivAt ellipticE 0 0 := by simpa using hEraw
    have hK : HasDerivAt ellipticK 0 0 := by simpa using hKraw
    have hcore :=
      ((hasDerivAt_one_add_sq 0).mul hE).sub
        ((hasDerivAt_one_sub_sq 0).mul hK)
    have h := hcore.const_mul (1 / 3 : ℝ)
    convert h using 1 <;> simp [secondPrimitive]
  · have hp_pos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hp)
    have hE := hasDerivAt_eE_formula p hp_pos hp1
    have hK := hasDerivAt_eK_formula p hp_pos hp1
    have hcore :=
      ((hasDerivAt_one_add_sq p).mul hE).sub
        ((hasDerivAt_one_sub_sq p).mul hK)
    have h := hcore.const_mul (1 / 3 : ℝ)
    convert h using 1
    field_simp [hp, show 1 - p ^ 2 ≠ 0 by nlinarith]
    ring

private lemma eE_zero_eq_eK_zero : ellipticE 0 = ellipticK 0 := by
  simp [ellipticE, ellipticK, radicand]

theorem gap1 (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    deriv firstPrimitive k =
      deriv ellipticE k + 2 * k * ellipticK k -
        (1 - k ^ 2) * deriv ellipticK k := by
  have hE := hasDerivAt_eE_formula k hk0 hk1
  have hK := hasDerivAt_eK_formula k hk0 hk1
  have h :=
    hE.sub ((hasDerivAt_one_sub_sq k).mul hK)
  rw [hE.deriv, hK.deriv]
  convert h.deriv using 1
  ring

theorem gap2 (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    deriv firstPrimitive k =
      (ellipticE k - ellipticK k) / k + 2 * k * ellipticK k -
        (1 - k ^ 2) *
          (ellipticE k / (k * (1 - k ^ 2)) - ellipticK k / k) := by
  rw [gap1 k hk0 hk1]
  rw [(hasDerivAt_eE_formula k hk0 hk1).deriv]
  rw [(hasDerivAt_eK_formula k hk0 hk1).deriv]

theorem gap3 (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    (ellipticE k - ellipticK k) / k + 2 * k * ellipticK k -
        (1 - k ^ 2) *
          (ellipticE k / (k * (1 - k ^ 2)) - ellipticK k / k) =
      k * ellipticK k := by
  have hk : k ≠ 0 := ne_of_gt hk0
  have hone : 1 - k ^ 2 ≠ 0 := by nlinarith
  field_simp [hk, hone]
  ring

theorem gap4 (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    deriv firstPrimitive k = k * ellipticK k := by
  rw [gap2 k hk0 hk1]
  exact gap3 k hk0 hk1

private lemma first_integral_eq
    (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    (∫ t in (0 : ℝ)..k, ellipticK t * t) = firstPrimitive k := by
  have hKcont : ContinuousOn ellipticK [[(0 : ℝ), k]] := by
    intro p hp
    have hp_bounds : p ∈ Icc 0 k := by
      rwa [uIcc_of_le hk0] at hp
    exact (hasDerivAt_eK p hp_bounds.1
      (hp_bounds.2.trans_lt hk1)).continuousAt.continuousWithinAt
  have hintK :
      IntervalIntegrable (fun p : ℝ => ellipticK p * p) volume 0 k :=
    (hKcont.mul continuousOn_id).intervalIntegrable
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := k) (f := firstPrimitive)
      (f' := fun p : ℝ => ellipticK p * p)
      (fun p hp => by
        have hp_bounds : p ∈ Icc 0 k := by
          rwa [uIcc_of_le hk0] at hp
        exact hasDerivAt_firstPrimitive p hp_bounds.1
          (hp_bounds.2.trans_lt hk1))
      hintK
  simpa [firstPrimitive, eE_zero_eq_eK_zero] using hFTC

theorem gap5 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    firstPrimitive k =
      (∫ t in (0 : ℝ)..k, t * ellipticK t) + firstConstant := by
  rw [show (∫ t in (0 : ℝ)..k, t * ellipticK t) =
      ∫ t in (0 : ℝ)..k, ellipticK t * t by
    apply intervalIntegral.integral_congr
    intro t ht
    ring]
  rw [first_integral_eq k hk0 hk1]
  simp [firstConstant]

theorem gap6 :
    ellipticE 0 - ellipticK 0 = Real.pi / 2 - Real.pi / 2 := by
  simp [ellipticE, ellipticK, radicand]

theorem gap7 :
    Real.pi / 2 - Real.pi / 2 = 0 := by
  ring

theorem gap8 :
    firstConstant = 0 := by
  rfl

theorem gap9 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    (∫ t in (0 : ℝ)..k, t * ellipticK t) = firstPrimitive k := by
  rw [show (∫ t in (0 : ℝ)..k, t * ellipticK t) =
      ∫ t in (0 : ℝ)..k, ellipticK t * t by
    apply intervalIntegral.integral_congr
    intro t ht
    ring]
  exact first_integral_eq k hk0 hk1

theorem gap10 (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    (1 / 3 : ℝ) *
        deriv (fun t =>
          (1 + t ^ 2) * ellipticE t - (1 - t ^ 2) * ellipticK t) k =
      (1 / 3 : ℝ) *
        (2 * k * ellipticE k + (1 + k ^ 2) * deriv ellipticE k +
          2 * k * ellipticK k - (1 - k ^ 2) * deriv ellipticK k) := by
  have hE := hasDerivAt_eE_formula k hk0 hk1
  have hK := hasDerivAt_eK_formula k hk0 hk1
  have hcore :=
    ((hasDerivAt_one_add_sq k).mul hE).sub
      ((hasDerivAt_one_sub_sq k).mul hK)
  have hcore' :
      HasDerivAt
        (fun t : ℝ =>
          (1 + t ^ 2) * ellipticE t - (1 - t ^ 2) * ellipticK t)
        (2 * k * ellipticE k + (1 + k ^ 2) * ((ellipticE k - ellipticK k) / k) -
          ((-2 * k) * ellipticK k +
            (1 - k ^ 2) *
              (ellipticE k / (k * (1 - k ^ 2)) - ellipticK k / k))) k := by
    simpa only [Pi.mul_apply, Pi.sub_apply] using hcore
  rw [hE.deriv, hK.deriv]
  rw [hcore'.deriv]
  ring

theorem gap11 (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    (1 / 3 : ℝ) *
        deriv (fun t =>
          (1 + t ^ 2) * ellipticE t - (1 - t ^ 2) * ellipticK t) k =
      (1 / 3 : ℝ) *
        (2 * k * ellipticE k +
          (1 + k ^ 2) * ((ellipticE k - ellipticK k) / k) +
          2 * k * ellipticK k -
          (1 - k ^ 2) *
            (ellipticE k / (k * (1 - k ^ 2)) - ellipticK k / k)) := by
  rw [gap10 k hk0 hk1]
  rw [(hasDerivAt_eE_formula k hk0 hk1).deriv]
  rw [(hasDerivAt_eK_formula k hk0 hk1).deriv]

theorem gap12 (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    (1 / 3 : ℝ) *
        (2 * k * ellipticE k +
          (1 + k ^ 2) * ((ellipticE k - ellipticK k) / k) +
          2 * k * ellipticK k -
          (1 - k ^ 2) *
            (ellipticE k / (k * (1 - k ^ 2)) - ellipticK k / k)) =
      k * ellipticE k := by
  have hk : k ≠ 0 := ne_of_gt hk0
  have hone : 1 - k ^ 2 ≠ 0 := by nlinarith
  field_simp [hk, hone]
  ring

theorem gap13 (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    deriv secondPrimitive k = k * ellipticE k := by
  rw [(hasDerivAt_secondPrimitive k hk0.le hk1).deriv]
  ring

private lemma second_integral_eq
    (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    (∫ t in (0 : ℝ)..k, ellipticE t * t) = secondPrimitive k := by
  have hEcont : ContinuousOn ellipticE [[(0 : ℝ), k]] := by
    intro p hp
    have hp_bounds : p ∈ Icc 0 k := by
      rwa [uIcc_of_le hk0] at hp
    exact (hasDerivAt_eE p hp_bounds.1
      (hp_bounds.2.trans_lt hk1)).continuousAt.continuousWithinAt
  have hintE :
      IntervalIntegrable (fun p : ℝ => ellipticE p * p) volume 0 k :=
    (hEcont.mul continuousOn_id).intervalIntegrable
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := k) (f := secondPrimitive)
      (f' := fun p : ℝ => ellipticE p * p)
      (fun p hp => by
        have hp_bounds : p ∈ Icc 0 k := by
          rwa [uIcc_of_le hk0] at hp
        exact hasDerivAt_secondPrimitive p hp_bounds.1
          (hp_bounds.2.trans_lt hk1))
      hintE
  simpa [secondPrimitive, eE_zero_eq_eK_zero] using hFTC

theorem gap14 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    secondPrimitive k =
      (∫ t in (0 : ℝ)..k, t * ellipticE t) + secondConstant := by
  rw [show (∫ t in (0 : ℝ)..k, t * ellipticE t) =
      ∫ t in (0 : ℝ)..k, ellipticE t * t by
    apply intervalIntegral.integral_congr
    intro t ht
    ring]
  rw [second_integral_eq k hk0 hk1]
  simp [secondConstant]

theorem gap15 :
    secondConstant = 0 := by
  rfl

theorem gap16 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    (∫ t in (0 : ℝ)..k, t * ellipticE t) = secondPrimitive k := by
  rw [show (∫ t in (0 : ℝ)..k, t * ellipticE t) =
      ∫ t in (0 : ℝ)..k, ellipticE t * t by
    apply intervalIntegral.integral_congr
    intro t ht
    ring]
  exact second_integral_eq k hk0 hk1

theorem gap17 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    (∫ t in (0 : ℝ)..k, ellipticK t * t) = firstPrimitive k ∧
      (∫ t in (0 : ℝ)..k, ellipticE t * t) = secondPrimitive k := by
  exact ⟨first_integral_eq k hk0 hk1, second_integral_eq k hk0 hk1⟩

end

end ProofGap.Exercise3739
