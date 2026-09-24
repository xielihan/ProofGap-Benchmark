import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Instances.EReal.Lemmas

namespace ProofGap.Exercise4165

noncomputable section

open MeasureTheory Filter
open scoped Interval

abbrev Point := ℝ × ℝ

def integrand (p : ℝ) (z : Point) : ℝ :=
  Real.sin z.1 * Real.sin z.2 /
    Real.rpow (z.1 + z.2) p

def areaIntegral (A : Set Point) (p : ℝ) : ℝ :=
  ∫ z in A, integrand p z

def halfPlane : Set Point :=
  {z | 1 ≤ z.1 + z.2}

def ExhaustsHalfPlane (A : ℕ → Set Point) : Prop :=
  Monotone A ∧ ⋃ n, A n = halfPlane

def IsImproperIntegral (p I : ℝ) : Prop :=
  ∀ A : ℕ → Set Point,
    ExhaustsHalfPlane A →
      Tendsto (fun n => areaIntegral (A n) p) atTop (nhds I)

def omega (n : ℕ) : Set Point :=
  {z |
    1 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ 2 * n * Real.pi ∧
      -2 * n * Real.pi ≤ z.1 - z.2 ∧
        z.1 - z.2 ≤ 2 * n * Real.pi}

def omegaCore (n : ℕ) : Set Point :=
  {z |
    1 ≤ z.1 + z.2 ∧
      z.1 + z.2 ≤ 2 * n * Real.pi - Real.pi / 4 ∧
        -2 * n * Real.pi ≤ z.1 - z.2 ∧
          z.1 - z.2 ≤ 2 * n * Real.pi}

def omegaStrip (n : ℕ) : Set Point :=
  {z |
    2 * n * Real.pi - Real.pi / 4 ≤ z.1 + z.2 ∧
      z.1 + z.2 ≤ 2 * n * Real.pi ∧
        -2 * n * Real.pi ≤ z.1 - z.2 ∧
          z.1 - z.2 ≤ 2 * n * Real.pi}

def thinHalfWidth (p : ℝ) (n : ℕ) : ℝ :=
  2 * Real.pi * Real.rpow n (-(p + 2))

def thinStrip (p : ℝ) (n : ℕ) : Set Point :=
  {z |
    2 * n * Real.pi - Real.pi / 4 ≤ z.1 + z.2 ∧
      z.1 + z.2 ≤ 2 * n * Real.pi ∧
        -thinHalfWidth p n ≤ z.1 - z.2 ∧
          z.1 - z.2 ≤ thinHalfWidth p n}

def radialPiece (p : ℝ) (n : ℕ) : ℝ :=
  ∫ u in 2 * n * Real.pi - Real.pi / 4..2 * n * Real.pi,
    Real.cos u / Real.rpow u p

theorem gap1 (p I : ℝ)
    (hp : p < 1)
    (hCandidate : IsImproperIntegral p I)
    (hOmega : ExhaustsHalfPlane omega) :
    Tendsto
      (fun n : ℕ => areaIntegral (omega n) p)
      atTop (nhds I) := by
  exact hCandidate omega hOmega

theorem gap2 (p I : ℝ)
    (hp : p < 1)
    (hCandidate : IsImproperIntegral p I)
    (hCore : ExhaustsHalfPlane omegaCore) :
    Tendsto
      (fun n : ℕ => areaIntegral (omegaCore n) p)
      atTop (nhds I) := by
  exact hCandidate omegaCore hCore

theorem gap3 (p I : ℝ)
    (hp : p < 1)
    (hOmegaLimit :
      Tendsto (fun n : ℕ => areaIntegral (omega n) p) atTop (nhds I))
    (hCoreLimit :
      Tendsto (fun n : ℕ => areaIntegral (omegaCore n) p) atTop (nhds I))
    (hDecomposition :
      ∀ n, areaIntegral (omega n) p =
        areaIntegral (omegaCore n) p + areaIntegral (omegaStrip n) p) :
    Tendsto
      (fun n : ℕ => areaIntegral (omegaStrip n) p)
      atTop (nhds 0) := by
  have hsub := hOmegaLimit.sub hCoreLimit
  convert hsub using 1
  · ext n
    rw [hDecomposition n]
    ring
  · ring

theorem gap4 (x y : ℝ) :
    Real.sin x * Real.sin y =
      (1 / 2 : ℝ) * (Real.cos (x - y) - Real.cos (x + y)) := by
  rw [Real.cos_sub, Real.cos_add]
  ring

private def sumDiff (z : Point) : Point :=
  (z.1 + z.2, z.1 - z.2)

private theorem sumDiff_measurable : Measurable sumDiff := by
  unfold sumDiff
  fun_prop

private theorem map_sumDiff_volume :
    Measure.map sumDiff (volume : Measure Point) =
      ENNReal.ofReal (1 / 2 : ℝ) • (volume : Measure Point) := by
  let f₁ : Point → Point := fun z => (z.1 + z.2, z.2)
  let f₂ : Point → Point := fun z => (z.1, (-2 : ℝ) * z.2)
  let f₃ : Point → Point := fun z => (z.1, z.1 + z.2)
  have hf₁ : Measurable f₁ := by
    unfold f₁
    fun_prop
  have hf₂ : Measurable f₂ := by
    unfold f₂
    fun_prop
  have hf₃ : Measurable f₃ := by
    unfold f₃
    fun_prop
  have hcomp : sumDiff = f₃ ∘ f₂ ∘ f₁ := by
    funext z
    simp only [sumDiff, f₁, f₂, f₃, Function.comp_apply]
    ext <;> ring
  have hf₁map :
      Measure.map f₁ (volume : Measure Point) = volume := by
    rw [Measure.volume_eq_prod]
    exact (measurePreserving_add_prod (volume : Measure ℝ) volume).map_eq
  have hf₃map :
      Measure.map f₃ (volume : Measure Point) = volume := by
    rw [Measure.volume_eq_prod]
    exact (measurePreserving_prod_add (volume : Measure ℝ) volume).map_eq
  have hf₂map :
      Measure.map f₂ (volume : Measure Point) =
        ENNReal.ofReal (1 / 2 : ℝ) • volume := by
    rw [Measure.volume_eq_prod]
    change
      Measure.map (Prod.map id ((-2 : ℝ) * ·))
          ((volume : Measure ℝ).prod volume) =
        ENNReal.ofReal (1 / 2 : ℝ) •
          ((volume : Measure ℝ).prod volume)
    calc
      Measure.map (Prod.map id ((-2 : ℝ) * ·))
          ((volume : Measure ℝ).prod volume) =
          (Measure.map id volume).prod
            (Measure.map ((-2 : ℝ) * ·) volume) :=
        (Measure.map_prod_map volume volume measurable_id
          (measurable_const_mul (-2))).symm
      _ = (volume : Measure ℝ).prod
          (ENNReal.ofReal (1 / 2 : ℝ) • volume) := by
        rw [Measure.map_id,
          Real.map_volume_mul_left (by norm_num : (-2 : ℝ) ≠ 0)]
        norm_num
      _ = ENNReal.ofReal (1 / 2 : ℝ) •
          ((volume : Measure ℝ).prod volume) := by
        rw [Measure.prod_smul_right]
  rw [hcomp]
  calc
    Measure.map (f₃ ∘ f₂ ∘ f₁) (volume : Measure Point) =
        Measure.map f₃
          (Measure.map f₂ (Measure.map f₁ (volume : Measure Point))) := by
      rw [Measure.map_map hf₂ hf₁, Measure.map_map hf₃ (hf₂.comp hf₁)]
    _ = Measure.map f₃ (Measure.map f₂ (volume : Measure Point)) := by
      rw [hf₁map]
    _ = Measure.map f₃
        (ENNReal.ofReal (1 / 2 : ℝ) • (volume : Measure Point)) := by
      rw [hf₂map]
    _ = ENNReal.ofReal (1 / 2 : ℝ) •
        Measure.map f₃ (volume : Measure Point) := by
      rw [Measure.map_smul]
    _ = ENNReal.ofReal (1 / 2 : ℝ) • (volume : Measure Point) := by
      rw [hf₃map]

private theorem integral_sumDiff_preimage
    (F : Point → ℝ) (hF : Measurable F)
    (R : Set Point) (hR : MeasurableSet R) :
    (∫ z in sumDiff ⁻¹' R, F (sumDiff z)) =
      (1 / 2 : ℝ) * ∫ w in R, F w := by
  let g : Point → ℝ := R.indicator F
  have hg : Measurable g := hF.indicator hR
  have hmap :=
    integral_map (μ := (volume : Measure Point))
      sumDiff_measurable.aemeasurable
      (hg.aestronglyMeasurable :
        AEStronglyMeasurable g
          (Measure.map sumDiff (volume : Measure Point)))
  rw [map_sumDiff_volume] at hmap
  have hc :
      (ENNReal.ofReal (1 / 2 : ℝ)).toReal = (1 / 2 : ℝ) :=
    ENNReal.toReal_ofReal (by norm_num)
  rw [integral_smul_measure, hc] at hmap
  have hcomp :
      (fun z => g (sumDiff z)) =
        (sumDiff ⁻¹' R).indicator (fun z => F (sumDiff z)) := by
    funext z
    by_cases hz : sumDiff z ∈ R <;> simp [g, hz]
  rw [hcomp, integral_indicator (sumDiff_measurable hR)] at hmap
  rw [integral_indicator hR] at hmap
  simpa [smul_eq_mul] using hmap.symm

private theorem measurable_rpow (s : ℝ) :
    Measurable (fun x : ℝ => Real.rpow x s) := by
  apply measurable_of_continuousOn_compl_singleton 0
  exact continuousOn_id.rpow_const
    (fun x hx => Or.inl (by simpa using hx))

private def uvIntegrand (p : ℝ) (w : Point) : ℝ :=
  (1 / 2 : ℝ) *
    (Real.cos w.2 - Real.cos w.1) / Real.rpow w.1 p

private theorem uvIntegrand_measurable (p : ℝ) :
    Measurable (uvIntegrand p) := by
  unfold uvIntegrand
  exact measurable_const.mul
    ((Real.continuous_cos.measurable.comp measurable_snd).sub
      (Real.continuous_cos.measurable.comp measurable_fst))
    |>.div ((measurable_rpow p).comp measurable_fst)

private theorem integrand_eq_uvIntegrand (p : ℝ) (z : Point) :
    integrand p z = uvIntegrand p (sumDiff z) := by
  unfold integrand uvIntegrand sumDiff
  rw [gap4]

private theorem uvIntegrand_integrableOn_rectangle
    (p a b c d : ℝ) (ha : 0 < a) :
    IntegrableOn (uvIntegrand p)
      (Set.Icc a b ×ˢ Set.Icc c d) := by
  have hcont :
      ContinuousOn (uvIntegrand p)
        (Set.Icc a b ×ˢ Set.Icc c d) := by
    unfold uvIntegrand
    apply ContinuousOn.div
    · fun_prop
    · apply ContinuousOn.rpow_const continuousOn_fst
      intro z hz
      exact Or.inl (ne_of_gt (ha.trans_le hz.1.1))
    · intro z hz
      exact ne_of_gt (Real.rpow_pos_of_pos (ha.trans_le hz.1.1) p)
  exact hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

private theorem areaIntegral_sumDiff_rectangle
    (p a b c d : ℝ) (ha : 0 < a) :
    areaIntegral
        (sumDiff ⁻¹' (Set.Icc a b ×ˢ Set.Icc c d)) p =
      (1 / 2 : ℝ) *
        ∫ u in Set.Icc a b,
          ∫ v in Set.Icc c d, uvIntegrand p (u, v) := by
  unfold areaIntegral
  calc
    (∫ z in sumDiff ⁻¹' (Set.Icc a b ×ˢ Set.Icc c d),
        integrand p z) =
        ∫ z in sumDiff ⁻¹' (Set.Icc a b ×ˢ Set.Icc c d),
          uvIntegrand p (sumDiff z) := by
      apply integral_congr_ae
      exact ae_of_all _ (integrand_eq_uvIntegrand p)
    _ = (1 / 2 : ℝ) *
        ∫ w in Set.Icc a b ×ˢ Set.Icc c d,
          uvIntegrand p w :=
      integral_sumDiff_preimage _ (uvIntegrand_measurable p) _
        (measurableSet_Icc.prod measurableSet_Icc)
    _ = (1 / 2 : ℝ) *
        ∫ u in Set.Icc a b,
          ∫ v in Set.Icc c d, uvIntegrand p (u, v) := by
      congr 1
      rw [Measure.volume_eq_prod]
      exact setIntegral_prod _ (uvIntegrand_integrableOn_rectangle p a b c d ha)

private theorem setIntegral_Icc_eq_interval
    (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) :
    (∫ x in Set.Icc a b, f x) = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_congr_set Ioc_ae_eq_Icc.symm

private theorem uvIntegrand_inner_symmetric
    (p u B : ℝ) (hB : 0 ≤ B) :
    (∫ v in Set.Icc (-B) B, uvIntegrand p (u, v)) =
      (Real.sin B - B * Real.cos u) / Real.rpow u p := by
  rw [setIntegral_Icc_eq_interval _ _ _ (by linarith)]
  unfold uvIntegrand
  have hfactor :
      (fun v : ℝ =>
        (1 / 2 : ℝ) * (Real.cos v - Real.cos u) /
          Real.rpow u p) =
        fun v =>
          (1 / 2 / Real.rpow u p) *
            (Real.cos v - Real.cos u) := by
    funext v
    ring
  rw [hfactor]
  calc
    (∫ v in -B..B,
        (1 / 2 / Real.rpow u p) *
          (Real.cos v - Real.cos u)) =
        (1 / 2 / Real.rpow u p) *
          ∫ v in -B..B, (Real.cos v - Real.cos u) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (1 / 2 / Real.rpow u p) *
        ((Real.sin B - Real.sin (-B)) -
          (B - (-B)) * Real.cos u) := by
      rw [intervalIntegral.integral_sub
        intervalIntegral.intervalIntegrable_cos
        intervalIntegral.intervalIntegrable_const,
        integral_cos, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
    _ = (Real.sin B - B * Real.cos u) / Real.rpow u p := by
      rw [Real.sin_neg]
      ring

theorem gap10 (p : ℝ) (n : ℕ) (hn : 1 ≤ n) (hp : 1 ≤ p) :
    areaIntegral (thinStrip p n) p =
      (1 / 2 : ℝ) *
        ∫ u in 2 * n * Real.pi - Real.pi / 4..2 * n * Real.pi,
          (Real.sin (thinHalfWidth p n) -
              thinHalfWidth p n * Real.cos u) /
            Real.rpow u p := by
  let a : ℝ := 2 * n * Real.pi - Real.pi / 4
  let b : ℝ := 2 * n * Real.pi
  let B : ℝ := thinHalfWidth p n
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < a := by
    unfold a
    nlinarith [Real.pi_pos]
  have hab : a ≤ b := by
    unfold a b
    linarith [Real.pi_pos]
  have hB : 0 ≤ B := by
    unfold B thinHalfWidth
    exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (Real.rpow_nonneg (by positivity) _)
  have hregion :
      thinStrip p n =
        sumDiff ⁻¹' (Set.Icc a b ×ˢ Set.Icc (-B) B) := by
    ext z
    simp only [thinStrip, sumDiff, a, b, B, Set.mem_setOf_eq,
      Set.mem_preimage, Set.mem_prod, Set.mem_Icc]
    tauto
  rw [hregion, areaIntegral_sumDiff_rectangle p a b (-B) B ha]
  simp_rw [uvIntegrand_inner_symmetric p _ B hB]
  rw [setIntegral_Icc_eq_interval _ a b hab]

theorem gap5 (p : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    areaIntegral (omegaStrip n) p =
      -(n : ℝ) * Real.pi * radialPiece p n := by
  let a : ℝ := 2 * n * Real.pi - Real.pi / 4
  let b : ℝ := 2 * n * Real.pi
  let B : ℝ := 2 * n * Real.pi
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < a := by
    unfold a
    nlinarith [Real.pi_pos]
  have hab : a ≤ b := by
    unfold a b
    linarith [Real.pi_pos]
  have hB : 0 ≤ B := by
    unfold B
    positivity
  have hregion :
      omegaStrip n =
        sumDiff ⁻¹' (Set.Icc a b ×ˢ Set.Icc (-B) B) := by
    ext z
    simp only [omegaStrip, sumDiff, a, b, B, Set.mem_setOf_eq,
      Set.mem_preimage, Set.mem_prod, Set.mem_Icc]
    ring_nf
    tauto
  have hsin : Real.sin B = 0 := by
    calc
      Real.sin B = Real.sin ((2 * n : ℕ) * Real.pi) := by
        congr 1
        unfold B
        push_cast
        ring
      _ = 0 := Real.sin_nat_mul_pi (2 * n)
  rw [hregion, areaIntegral_sumDiff_rectangle p a b (-B) B ha]
  simp_rw [uvIntegrand_inner_symmetric p _ B hB]
  rw [setIntegral_Icc_eq_interval _ a b hab]
  have hfun :
      (fun u : ℝ =>
        (Real.sin B - B * Real.cos u) / Real.rpow u p) =
        fun u => -B * (Real.cos u / Real.rpow u p) := by
    funext u
    rw [hsin]
    ring
  rw [hfun, intervalIntegral.integral_const_mul]
  unfold radialPiece a b B
  ring

private theorem radial_intervalIntegrable
    (p a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun u : ℝ => Real.cos u / Real.rpow u p) volume a b := by
  have hcont :
      ContinuousOn
        (fun u : ℝ => Real.cos u / Real.rpow u p)
        (Set.Icc a b) := by
    apply ContinuousOn.div Real.continuous_cos.continuousOn
    · apply ContinuousOn.rpow_const continuousOn_id
      intro u hu
      exact Or.inl (ne_of_gt (ha.trans_le hu.1))
    · intro u hu
      exact ne_of_gt (Real.rpow_pos_of_pos (ha.trans_le hu.1) p)
  apply ContinuousOn.intervalIntegrable
  simpa [Set.uIcc_of_le hab] using hcont

private theorem sqrt_two_half_eq_inv :
    Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp [hs]
  norm_num [Real.sq_sqrt]

theorem gap6 (p : ℝ) (n : ℕ) (hn : 1 ≤ n) (hp : p < 1) :
    radialPiece p n ≥
      if 0 < p then
        Real.pi / (4 * Real.sqrt 2) *
          (1 / Real.rpow (2 * n * Real.pi) p)
      else
        Real.pi / (4 * Real.sqrt 2) := by
  let a : ℝ := 2 * n * Real.pi - Real.pi / 4
  let b : ℝ := 2 * n * Real.pi
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi_n : Real.pi ≤ (n : ℝ) * Real.pi :=
    by simpa using (mul_le_mul_of_nonneg_right hnR Real.pi_pos.le)
  have ha : 0 < a := by
    unfold a
    nlinarith [Real.pi_pos]
  have ha1 : 1 ≤ a := by
    unfold a
    nlinarith [Real.two_le_pi]
  have hab : a ≤ b := by
    unfold a b
    linarith [Real.pi_pos]
  have hrad :
      IntervalIntegrable
        (fun u : ℝ => Real.cos u / Real.rpow u p)
        volume a b :=
    radial_intervalIntegrable p a b ha hab
  have hcos :
      ∀ u ∈ Set.Icc a b, Real.sqrt 2 / 2 ≤ Real.cos u := by
    intro u hu
    have ht0 : 0 ≤ b - u := sub_nonneg.2 hu.2
    have ht4 : b - u ≤ Real.pi / 4 := by
      unfold a b at hu
      unfold b
      linarith [hu.1]
    have hperiod : Real.cos u = Real.cos (b - u) := by
      calc
        Real.cos u =
            Real.cos ((n : ℝ) * (2 * Real.pi) - (b - u)) := by
          congr 1
          unfold b
          ring
        _ = Real.cos (b - u) :=
          Real.cos_nat_mul_two_pi_sub (b - u) n
    calc
      Real.sqrt 2 / 2 = Real.cos (Real.pi / 4) :=
        Real.cos_pi_div_four.symm
      _ ≤ Real.cos (b - u) :=
        Real.cos_le_cos_of_nonneg_of_le_pi ht0
          (by linarith [Real.pi_pos]) ht4
      _ = Real.cos u := hperiod.symm
  unfold radialPiece
  change
    (∫ u in a..b, Real.cos u / Real.rpow u p) ≥
      if 0 < p then
        Real.pi / (4 * Real.sqrt 2) *
          (1 / Real.rpow b p)
      else Real.pi / (4 * Real.sqrt 2)
  by_cases hp0 : 0 < p
  · rw [if_pos hp0]
    have hpoint :
        ∀ u ∈ Set.Icc a b,
          (Real.sqrt 2 / 2) / Real.rpow b p ≤
            Real.cos u / Real.rpow u p := by
      intro u hu
      have hup : 0 < Real.rpow u p :=
        Real.rpow_pos_of_pos (ha.trans_le hu.1) p
      have hr :
          Real.rpow u p ≤ Real.rpow b p :=
        Real.rpow_le_rpow (ha.le.trans hu.1) hu.2 hp0.le
      exact
        (div_le_div_of_nonneg_right (hcos u hu) hup.le).trans'
          (div_le_div_of_nonneg_left
            (by positivity : 0 ≤ Real.sqrt 2 / 2)
            hup hr)
    have hmono :=
      intervalIntegral.integral_mono_on hab
        intervalIntegral.intervalIntegrable_const hrad hpoint
    rw [intervalIntegral.integral_const] at hmono
    have hlen : b - a = Real.pi / 4 := by
      unfold a b
      ring
    rw [hlen, smul_eq_mul] at hmono
    calc
      Real.pi / (4 * Real.sqrt 2) *
          (1 / Real.rpow b p) =
          (Real.pi / 4) *
            ((Real.sqrt 2 / 2) / Real.rpow b p) := by
        rw [sqrt_two_half_eq_inv]
        ring
      _ ≤ ∫ u in a..b, Real.cos u / Real.rpow u p := hmono
  · rw [if_neg hp0]
    have hpnonpos : p ≤ 0 := le_of_not_gt hp0
    have hpoint :
        ∀ u ∈ Set.Icc a b,
          Real.sqrt 2 / 2 ≤
            Real.cos u / Real.rpow u p := by
      intro u hu
      have hu1 : 1 ≤ u := ha1.trans hu.1
      have hrpos : 0 < Real.rpow u p :=
        Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hu1) p
      have hrle : Real.rpow u p ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hu1 hpnonpos
      have hcnonneg : 0 ≤ Real.cos u :=
        (by positivity : 0 < Real.sqrt 2 / 2).le.trans (hcos u hu)
      calc
        Real.sqrt 2 / 2 ≤ Real.cos u := hcos u hu
        _ ≤ Real.cos u / Real.rpow u p := by
          rw [le_div_iff₀ hrpos]
          exact mul_le_of_le_one_right hcnonneg hrle
    have hmono :=
      intervalIntegral.integral_mono_on hab
        intervalIntegral.intervalIntegrable_const hrad hpoint
    rw [intervalIntegral.integral_const] at hmono
    have hlen : b - a = Real.pi / 4 := by
      unfold a b
      ring
    rw [hlen, smul_eq_mul] at hmono
    calc
      Real.pi / (4 * Real.sqrt 2) =
          (Real.pi / 4) * (Real.sqrt 2 / 2) := by
        rw [sqrt_two_half_eq_inv]
        ring
      _ ≤ ∫ u in a..b, Real.cos u / Real.rpow u p := hmono

theorem gap7 (p : ℝ) (hp : p < 1) :
    Tendsto
      (fun n : ℕ => (areaIntegral (omegaStrip n) p : EReal))
      atTop (nhds ⊥) := by
  apply EReal.tendsto_coe_nhds_bot_iff.2
  let K : ℝ := Real.pi / (4 * Real.sqrt 2)
  have hK : 0 < K := by
    unfold K
    positivity
  by_cases hp0 : 0 < p
  · let A : ℝ := Real.rpow (2 * Real.pi) p
    let D : ℝ := Real.pi * K / A
    have hA : 0 < A := by
      unfold A
      exact Real.rpow_pos_of_pos (by positivity) p
    have hD : 0 < D := by
      unfold D
      positivity
    have hgrow :
        Tendsto
          (fun n : ℕ => D * Real.rpow n (1 - p))
          atTop atTop := by
      exact
        ((tendsto_rpow_atTop (sub_pos.2 hp)).comp
          tendsto_natCast_atTop_atTop).const_mul_atTop hD
    have hneg :
        Tendsto
          (fun n : ℕ => -(D * Real.rpow n (1 - p)))
          atTop atBot :=
      tendsto_neg_atBot_iff.mpr hgrow
    apply tendsto_atBot_mono' atTop _ hneg
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hlower := gap6 p n hn hp
    rw [if_pos hp0] at hlower
    have hcoeff : -(n : ℝ) * Real.pi ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.2 (Nat.cast_nonneg n)) Real.pi_pos.le
    rw [gap5 p n hn]
    calc
      -(n : ℝ) * Real.pi * radialPiece p n ≤
          -(n : ℝ) * Real.pi *
            (K * (1 / Real.rpow (2 * n * Real.pi) p)) := by
        exact mul_le_mul_of_nonpos_left
          (by simpa [K] using hlower) hcoeff
      _ = -(D * Real.rpow n (1 - p)) := by
        have hbpow :
            Real.rpow (2 * (n : ℝ) * Real.pi) p =
              Real.rpow n p * A := by
          unfold A
          rw [show 2 * (n : ℝ) * Real.pi =
            (n : ℝ) * (2 * Real.pi) by ring]
          exact Real.mul_rpow (by positivity) (by positivity)
        have hnsub :
            Real.rpow n (1 - p) =
              (n : ℝ) / Real.rpow n p := by
          simpa only [Real.rpow_one] using
            (Real.rpow_sub hnpos 1 p)
        rw [hbpow, hnsub]
        have hnpow : Real.rpow (n : ℝ) p ≠ 0 :=
          ne_of_gt (Real.rpow_pos_of_pos hnpos p)
        unfold D
        field_simp [hA.ne', hnpow]
  · have hpnonpos : p ≤ 0 := le_of_not_gt hp0
    let D : ℝ := Real.pi * K
    have hD : 0 < D := by
      unfold D
      positivity
    have hgrow :
        Tendsto (fun n : ℕ => D * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hD
    have hneg :
        Tendsto (fun n : ℕ => -(D * (n : ℝ))) atTop atBot :=
      tendsto_neg_atBot_iff.mpr hgrow
    apply tendsto_atBot_mono' atTop _ hneg
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hlower := gap6 p n hn hp
    rw [if_neg hp0] at hlower
    have hcoeff : -(n : ℝ) * Real.pi ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.2 (Nat.cast_nonneg n)) Real.pi_pos.le
    rw [gap5 p n hn]
    calc
      -(n : ℝ) * Real.pi * radialPiece p n ≤
          -(n : ℝ) * Real.pi * K := by
        exact mul_le_mul_of_nonpos_left
          (by simpa [K] using hlower) hcoeff
      _ = -(D * (n : ℝ)) := by
        unfold D
        ring

private theorem thinStrip_norm_bound
    (p : ℝ) (hp : 1 ≤ p) (n : ℕ) (hn : 1 ≤ n) :
    ‖areaIntegral (thinStrip p n) p‖ ≤
      thinHalfWidth p n * (Real.pi / 4) := by
  let a : ℝ := 2 * n * Real.pi - Real.pi / 4
  let b : ℝ := 2 * n * Real.pi
  let B : ℝ := thinHalfWidth p n
  let q : ℝ → ℝ := fun u =>
    (Real.sin B - B * Real.cos u) / Real.rpow u p
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi_n : Real.pi ≤ (n : ℝ) * Real.pi := by
    simpa using (mul_le_mul_of_nonneg_right hnR Real.pi_pos.le)
  have ha1 : 1 ≤ a := by
    unfold a
    nlinarith [Real.two_le_pi]
  have hab : a ≤ b := by
    unfold a b
    linarith [Real.pi_pos]
  have hB : 0 ≤ B := by
    unfold B thinHalfWidth
    exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (Real.rpow_nonneg (by positivity) _)
  have hq :
      ∀ u ∈ Set.uIoc a b, ‖q u‖ ≤ 2 * B := by
    intro u hu
    have huIoc : u ∈ Set.Ioc a b := by
      simpa [Set.uIoc_of_le hab] using hu
    have huIcc : u ∈ Set.Icc a b := Set.Ioc_subset_Icc_self huIoc
    have hu1 : 1 ≤ u := ha1.trans huIcc.1
    have hdenpos : 0 < Real.rpow u p :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hu1) p
    have hdenone : 1 ≤ Real.rpow u p :=
      Real.one_le_rpow hu1 (by linarith)
    have hsin : |Real.sin B| ≤ B := by
      simpa [abs_of_nonneg hB] using
        (Real.abs_sin_le_abs : |Real.sin B| ≤ |B|)
    have hcos : |Real.cos u| ≤ 1 := Real.abs_cos_le_one u
    have hBcos : |B * Real.cos u| ≤ B := by
      rw [abs_mul, abs_of_nonneg hB]
      exact mul_le_of_le_one_right hB hcos
    have hnum :
        |Real.sin B - B * Real.cos u| ≤ 2 * B := by
      calc
        |Real.sin B - B * Real.cos u| ≤
            |Real.sin B| + |B * Real.cos u| := abs_sub _ _
        _ ≤ B + B := add_le_add hsin hBcos
        _ = 2 * B := by ring
    unfold q
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hdenpos]
    calc
      |Real.sin B - B * Real.cos u| / Real.rpow u p ≤
          (2 * B) / Real.rpow u p :=
        div_le_div_of_nonneg_right hnum hdenpos.le
      _ ≤ 2 * B := by
        exact div_le_self (by positivity) hdenone
  have hint :=
    intervalIntegral.norm_integral_le_of_norm_le_const hq
  have hlen : |b - a| = Real.pi / 4 := by
    have : b - a = Real.pi / 4 := by
      unfold a b
      ring
    rw [this, abs_of_pos (by positivity)]
  rw [hlen] at hint
  have hformula := gap10 p n hn hp
  change
    ‖areaIntegral (thinStrip p n) p‖ ≤ B * (Real.pi / 4)
  rw [hformula]
  change ‖(1 / 2 : ℝ) * ∫ u in a..b, q u‖ ≤ B * (Real.pi / 4)
  rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    (1 / 2 : ℝ) * ‖∫ u in a..b, q u‖ ≤
        (1 / 2 : ℝ) * ((2 * B) * (Real.pi / 4)) :=
      mul_le_mul_of_nonneg_left hint (by norm_num)
    _ = B * (Real.pi / 4) := by ring

theorem gap9 (p : ℝ) (hp : 1 ≤ p) :
    Tendsto
      (fun n : ℕ => areaIntegral (thinStrip p n) p)
      atTop (nhds 0) := by
  have hrpow :
      Tendsto (fun n : ℕ => Real.rpow n (-(p + 2)))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp
      tendsto_natCast_atTop_atTop
  have hbound :
      Tendsto
        (fun n : ℕ => thinHalfWidth p n * (Real.pi / 4))
        atTop (nhds 0) := by
    simpa [thinHalfWidth, mul_assoc] using
      (hrpow.const_mul (2 * Real.pi)).mul_const (Real.pi / 4)
  apply squeeze_zero_norm'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact thinStrip_norm_bound p hp n hn
  · exact hbound

theorem gap11 (p : ℝ) (hp : 1 ≤ p) :
    Tendsto
      (fun n : ℕ => areaIntegral (thinStrip p n) p)
      atTop (nhds 0) := by
  exact gap9 p hp

theorem gap8 (p : ℝ) (I : EReal)
    (hp : p < 1) (hI : I ≠ ⊤)
    (hzero :
      Tendsto
        (fun n : ℕ => (areaIntegral (omegaStrip n) p : EReal))
        atTop (nhds 0))
    (hbot :
      Tendsto
        (fun n : ℕ => (areaIntegral (omegaStrip n) p : EReal))
        atTop (nhds ⊥)) :
    False := by
  have heq : (0 : EReal) = ⊥ := tendsto_nhds_unique hzero hbot
  simpa using heq

theorem gap12 (p : ℝ) (I : EReal)
    (hp : 1 ≤ p) (hI : I ≠ ⊤)
    (hzeroActual :
      Tendsto
        (fun n : ℕ => (areaIntegral (thinStrip p n) p : EReal))
        atTop (nhds 0))
    (hbotHypothesis :
      Tendsto
        (fun n : ℕ => (areaIntegral (thinStrip p n) p : EReal))
        atTop (nhds ⊥)) :
    False := by
  have heq : (0 : EReal) = ⊥ :=
    tendsto_nhds_unique hzeroActual hbotHypothesis
  simpa using heq

theorem gap13 (p : ℝ) (I : EReal)
    (hBelowOneContradiction : p < 1 → I ≠ ⊤ → False)
    (hAtLeastOneContradiction : 1 ≤ p → I ≠ ⊤ → False) :
    I = ⊤ := by
  by_contra hne
  rcases lt_or_ge p 1 with hp | hp
  · exact hBelowOneContradiction hp hne
  · exact hAtLeastOneContradiction hp hne

end

end ProofGap.Exercise4165
