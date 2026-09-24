import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3962

noncomputable section

open MeasureTheory
open scoped Interval

local instance : Measure.IsAddHaarMeasure volume (G := ℝ × ℝ) :=
  Measure.prod.instIsAddHaarMeasure _ _

def diamond : Set (ℝ × ℝ) :=
  {p | |p.1| + |p.2| ≤ 1}

def parameterSquare : Set (ℝ × ℝ) :=
  Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1

def forwardMap (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 + p.2, p.1 - p.2)

def inverseMap (q : ℝ × ℝ) : ℝ × ℝ :=
  ((q.1 + q.2) / 2, (q.1 - q.2) / 2)

def jacobianAbs : ℝ :=
  1 / 2

def diamondIntegral (f : ℝ → ℝ) : ℝ :=
  ∫ p in diamond, f (p.1 + p.2)

private def inverseDerivative : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![(1 / 2 : ℝ), 1 / 2; 1 / 2, -(1 / 2)]).toContinuousLinearMap

private theorem forward_inverse (q : ℝ × ℝ) :
    forwardMap (inverseMap q) = q := by
  ext <;> simp [forwardMap, inverseMap] <;> ring

private theorem inverse_forward (p : ℝ × ℝ) :
    inverseMap (forwardMap p) = p := by
  ext <;> simp [forwardMap, inverseMap] <;> ring

private theorem inverse_image_square :
    inverseMap '' parameterSquare = diamond := by
  ext p
  constructor
  · rintro ⟨⟨u, v⟩, huv, rfl⟩
    simp only [parameterSquare, Set.mem_prod, Set.mem_Icc] at huv
    rcases huv with ⟨⟨hu0, hu1⟩, ⟨hv0, hv1⟩⟩
    change |(u + v) / 2| + |(u - v) / 2| ≤ 1
    rw [abs_div, abs_div]
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    by_cases h₁ : 0 ≤ u + v
    · rw [abs_of_nonneg h₁]
      by_cases h₂ : 0 ≤ u - v
      · rw [abs_of_nonneg h₂]
        linarith
      · rw [abs_of_nonpos (le_of_not_ge h₂)]
        linarith
    · rw [abs_of_nonpos (le_of_not_ge h₁)]
      by_cases h₂ : 0 ≤ u - v
      · rw [abs_of_nonneg h₂]
        linarith
      · rw [abs_of_nonpos (le_of_not_ge h₂)]
        linarith
  · intro hp
    refine ⟨forwardMap p, ?_, inverse_forward p⟩
    change forwardMap p ∈ parameterSquare
    simp only [parameterSquare, forwardMap, Set.mem_prod, Set.mem_Icc]
    change
      ((-1 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 1) ∧
        (-1 ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ 1))
    change |p.1| + |p.2| ≤ 1 at hp
    have hplus : |p.1 + p.2| ≤ 1 :=
      (abs_add_le p.1 p.2).trans hp
    have hminus : |p.1 - p.2| ≤ 1 := by
      rw [sub_eq_add_neg]
      exact (abs_add_le p.1 (-p.2)).trans (by simpa using hp)
    exact ⟨abs_le.mp hplus, abs_le.mp hminus⟩

private theorem inverse_injective :
    Set.InjOn inverseMap parameterSquare := by
  intro p hp q hq hpq
  have h := congrArg forwardMap hpq
  simpa only [forward_inverse] using h

private theorem inverse_hasFDerivAt (q : ℝ × ℝ) :
    HasFDerivAt inverseMap inverseDerivative q := by
  have hfst :
      HasFDerivAt (fun p : ℝ × ℝ => p.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) q :=
    hasFDerivAt_fst
  have hsnd :
      HasFDerivAt (fun p : ℝ × ℝ => p.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) q :=
    hasFDerivAt_snd
  unfold inverseMap inverseDerivative
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert HasFDerivAt.prodMk
    ((hfst.add hsnd).const_smul (1 / 2 : ℝ))
    ((hfst.sub hsnd).const_smul (1 / 2 : ℝ)) using 1 <;>
    ext <;> simp <;> ring

private theorem inverseDerivative_abs_det :
    |inverseDerivative.det| = (1 / 2 : ℝ) := by
  have hdet : inverseDerivative.det = (-1 / 2 : ℝ) := by
    unfold inverseDerivative
    rw [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
      Matrix.det_fin_two_of]
    ring
  rw [hdet, abs_of_nonpos]
  · ring
  · norm_num

private theorem interval_set_integral_eq (f : ℝ → ℝ) :
    (∫ x in Set.Icc (-1 : ℝ) 1, f x) =
      ∫ x in (-1 : ℝ)..1, f x := by
  rw [intervalIntegral.integral_of_le
    (by norm_num : (-1 : ℝ) ≤ 1)]
  exact setIntegral_congr_set
    (Ioc_ae_eq_Icc' (measure_singleton (-1 : ℝ))).symm

private theorem square_integral_eq_iterated (f : ℝ → ℝ) :
    (∫ q in parameterSquare, (1 / 2 : ℝ) * f q.1) =
      1 / 2 *
        ∫ v in (-1 : ℝ)..1, ∫ u in (-1 : ℝ)..1, f u := by
  unfold parameterSquare
  have hprod :
      (∫ q : ℝ × ℝ in
          Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1,
          (1 / 2 : ℝ) * f q.1) =
        (∫ u in Set.Icc (-1 : ℝ) 1, (1 / 2 : ℝ) * f u) *
          ∫ v in Set.Icc (-1 : ℝ) 1, (1 : ℝ) := by
    change
      (∫ q : ℝ × ℝ in
          Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1,
          (1 / 2 : ℝ) * f q.1 ∂volume.prod volume) = _
    simpa only [mul_one] using
      (MeasureTheory.setIntegral_prod_mul
        (μ := volume) (ν := volume)
        (fun u : ℝ => (1 / 2 : ℝ) * f u)
        (fun _v : ℝ => (1 : ℝ))
        (Set.Icc (-1 : ℝ) 1) (Set.Icc (-1 : ℝ) 1))
  rw [hprod]
  rw [show (fun u : ℝ => (1 / 2 : ℝ) * f u) =
      fun u => (1 / 2 : ℝ) • f u by rfl]
  rw [MeasureTheory.integral_smul]
  rw [interval_set_integral_eq]
  rw [MeasureTheory.setIntegral_one_eq_measureReal]
  rw [Real.volume_real_Icc_of_le
    (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_const]
  norm_num [smul_eq_mul]
  ring

theorem gap1 (u v : ℝ) :
    (inverseMap (u, v)).1 = (u + v) / 2 := by
  rfl

theorem gap2 (u v : ℝ) :
    (inverseMap (u, v)).2 = (u - v) / 2 := by
  rfl

theorem gap3 :
    jacobianAbs = 1 / 2 := by
  rfl

theorem gap4 (p : ℝ × ℝ) (hp : p ∈ diamond) :
    -1 ≤ (forwardMap p).1 := by
  change |p.1| + |p.2| ≤ 1 at hp
  have hplus : |p.1 + p.2| ≤ 1 :=
    (abs_add_le p.1 p.2).trans hp
  exact (abs_le.mp hplus).1

theorem gap5 (p : ℝ × ℝ) (hp : p ∈ diamond) :
    (forwardMap p).1 ≤ 1 := by
  change |p.1| + |p.2| ≤ 1 at hp
  have hplus : |p.1 + p.2| ≤ 1 :=
    (abs_add_le p.1 p.2).trans hp
  exact (abs_le.mp hplus).2

theorem gap6 (p : ℝ × ℝ) (hp : p ∈ diamond) :
    -1 ≤ (forwardMap p).2 := by
  change |p.1| + |p.2| ≤ 1 at hp
  have hminus : |p.1 - p.2| ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (abs_add_le p.1 (-p.2)).trans (by simpa using hp)
  exact (abs_le.mp hminus).1

theorem gap7 (p : ℝ × ℝ) (hp : p ∈ diamond) :
    (forwardMap p).2 ≤ 1 := by
  change |p.1| + |p.2| ≤ 1 at hp
  have hminus : |p.1 - p.2| ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (abs_add_le p.1 (-p.2)).trans (by simpa using hp)
  exact (abs_le.mp hminus).2

theorem gap8 (f : ℝ → ℝ)
    (hf : IntegrableOn
      (fun p : ℝ × ℝ => f (p.1 + p.2)) diamond) :
    diamondIntegral f =
      1 / 2 *
        ∫ v in (-1 : ℝ)..1, ∫ u in (-1 : ℝ)..1, f u := by
  have hchange :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (μ := volume) (s := parameterSquare)
      (measurableSet_Icc.prod measurableSet_Icc)
      (fun q _ => (inverse_hasFDerivAt q).hasFDerivWithinAt)
      inverse_injective
      (fun p : ℝ × ℝ => f (p.1 + p.2))
  rw [inverse_image_square] at hchange
  calc
    diamondIntegral f =
        ∫ q in parameterSquare,
          |inverseDerivative.det| •
            f ((inverseMap q).1 + (inverseMap q).2) := by
      exact hchange
    _ = ∫ q in parameterSquare, (1 / 2 : ℝ) * f q.1 := by
      apply setIntegral_congr_fun
        (measurableSet_Icc.prod measurableSet_Icc)
      intro q hq
      rw [inverseDerivative_abs_det]
      simp only [inverseMap, smul_eq_mul]
      congr 1
      ring
    _ = _ := square_integral_eq_iterated f

theorem gap9 (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (-1) 1) :
    1 / 2 *
        (∫ v in (-1 : ℝ)..1, ∫ u in (-1 : ℝ)..1, f u) =
      ∫ u in (-1 : ℝ)..1, f u := by
  rw [intervalIntegral.integral_const]
  norm_num [smul_eq_mul]
  ring

theorem gap10 (f : ℝ → ℝ)
    (hf : IntegrableOn
      (fun p : ℝ × ℝ => f (p.1 + p.2)) diamond) :
    diamondIntegral f =
      ∫ u in (-1 : ℝ)..1, f u := by
  rw [gap8 f hf]
  rw [intervalIntegral.integral_const]
  norm_num [smul_eq_mul]
  ring

end

end ProofGap.Exercise3962
