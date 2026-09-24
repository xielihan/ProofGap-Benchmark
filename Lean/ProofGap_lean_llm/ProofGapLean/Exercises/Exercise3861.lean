import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3861

noncomputable section

open Filter MeasureTheory
open scoped Interval

def HasImproperIntegral (a : ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds L)

def improperIntegral (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  sInf {L : ℝ | HasImproperIntegral a f L}

def HasReverseImproperIntegral (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun A : ℝ => ∫ t in A..0, f t) atTop (nhds L)

def reverseImproperIntegral (f : ℝ → ℝ) : ℝ :=
  sInf {L : ℝ | HasReverseImproperIntegral f L}

def gammaIntegrand (p t : ℝ) : ℝ :=
  Real.rpow t p * Real.exp (-t)

def logIntegrand (p x : ℝ) : ℝ :=
  Real.rpow (Real.log (1 / x)) p

private theorem improperIntegral_eq_of_has
    {a L : ℝ} {f : ℝ → ℝ} (h : HasImproperIntegral a f L) :
    improperIntegral a f = L := by
  have hset : {K : ℝ | HasImproperIntegral a f K} = {L} := by
    ext K
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hK
      exact tendsto_nhds_unique hK h
    · rintro rfl
      exact h
  unfold improperIntegral
  rw [hset]
  simp

private theorem reverseImproperIntegral_eq_of_has
    {L : ℝ} {f : ℝ → ℝ} (h : HasReverseImproperIntegral f L) :
    reverseImproperIntegral f = L := by
  have hset : {K : ℝ | HasReverseImproperIntegral f K} = {L} := by
    ext K
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hK
      exact tendsto_nhds_unique hK h
    · rintro rfl
      exact h
  unfold reverseImproperIntegral
  rw [hset]
  simp

private theorem gamma_set_integral (p : ℝ) (hp : -1 < p) :
    (∫ t in Set.Ioi (0 : ℝ), gammaIntegrand p t) =
      Real.Gamma (p + 1) := by
  have hp1 : 0 < p + 1 := by linarith
  symm
  simpa [gammaIntegrand, mul_comm] using
    (Real.Gamma_eq_integral hp1)

private theorem gamma_integrable (p : ℝ) (hp : -1 < p) :
    IntegrableOn (gammaIntegrand p) (Set.Ioi 0) := by
  have hp1 : 0 < p + 1 := by linarith
  by_contra h
  have hzero :
      (∫ t in Set.Ioi (0 : ℝ), gammaIntegrand p t) = 0 := by
    exact integral_undef h
  apply ne_of_gt (Real.Gamma_pos_of_pos hp1)
  rw [← gamma_set_integral p hp]
  exact hzero

private theorem gamma_has_improper_integral (p : ℝ) (hp : -1 < p) :
    HasImproperIntegral 0 (gammaIntegrand p)
      (Real.Gamma (p + 1)) := by
  unfold HasImproperIntegral
  rw [← gamma_set_integral p hp]
  apply intervalIntegral_tendsto_integral_Ioi
  · exact gamma_integrable p hp
  · exact (tendsto_id :
      Tendsto (fun i : ℝ => i) atTop atTop)

private theorem gamma_has_reverse_improper_integral
    (p : ℝ) (hp : -1 < p) :
    HasReverseImproperIntegral (gammaIntegrand p)
      (-Real.Gamma (p + 1)) := by
  unfold HasReverseImproperIntegral
  have h :
      Tendsto
        (fun A : ℝ => ∫ t in (0 : ℝ)..A, gammaIntegrand p t)
        atTop (nhds (Real.Gamma (p + 1))) :=
    gamma_has_improper_integral p hp
  have hneg :
      Tendsto
        (fun A : ℝ =>
          -(∫ t in (0 : ℝ)..A, gammaIntegrand p t))
        atTop (nhds (-Real.Gamma (p + 1))) :=
    h.neg
  have hfun :
      (fun A : ℝ => ∫ t in A..(0 : ℝ), gammaIntegrand p t) =
        (fun A : ℝ =>
          -(∫ t in (0 : ℝ)..A, gammaIntegrand p t)) := by
    funext A
    exact intervalIntegral.integral_symm
      (f := fun t : ℝ => gammaIntegrand p t) (0 : ℝ) A
  rw [hfun]
  exact hneg

private theorem log_interval_eq_gamma (p : ℝ) (hp : -1 < p) :
    (∫ x in (0 : ℝ)..1, logIntegrand p x) =
      Real.Gamma (p + 1) := by
  rw [← gamma_set_integral p hp]
  rw [intervalIntegral.integral_of_le
    (zero_le_one : (0 : ℝ) ≤ 1)]
  simp only [logIntegrand, gammaIntegrand, one_div, Real.log_inv]
  let e : ℝ → ℝ := fun t => Real.exp (-t)
  have he (t : ℝ) :
      HasDerivAt e (-Real.exp (-t)) t := by
    dsimp [e]
    convert (Real.hasDerivAt_exp (-t)).comp t
      (hasDerivAt_neg t) using 1 <;> ring
  have hinj : Set.InjOn e (Set.Ici (0 : ℝ)) := by
    intro x hx y hy hxy
    dsimp [e] at hxy
    have hneg : -x = -y := Real.exp_injective hxy
    linarith
  have himage : e '' Set.Ici (0 : ℝ) = Set.Ioc (0 : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      constructor
      · exact Real.exp_pos _
      · rw [Real.exp_le_one_iff]
        exact neg_nonpos.mpr ht
    · intro hx
      refine ⟨-Real.log x, ?_, ?_⟩
      · exact neg_nonneg.mpr (Real.log_nonpos hx.1.le hx.2)
      · dsimp [e]
        rw [neg_neg, Real.exp_log hx.1]
  have hchange :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := Set.Ici (0 : ℝ)) measurableSet_Ici
      (fun t _ => (he t).hasDerivWithinAt) hinj
      (fun x : ℝ => Real.rpow (-Real.log x) p)
  rw [himage] at hchange
  calc
    (∫ x in Set.Ioc (0 : ℝ) 1,
        Real.rpow (-Real.log x) p) =
        ∫ t in Set.Ici (0 : ℝ),
          |-Real.exp (-t)| •
            Real.rpow (-Real.log (Real.exp (-t))) p := hchange
    _ = ∫ t in Set.Ici (0 : ℝ),
          Real.rpow t p * Real.exp (-t) := by
      apply setIntegral_congr_fun measurableSet_Ici
      intro t ht
      simp only [Real.log_exp, neg_neg, abs_neg,
        abs_of_pos (Real.exp_pos _), smul_eq_mul]
      ring
    _ = ∫ t in Set.Ioi (0 : ℝ),
          Real.rpow t p * Real.exp (-t) := by
      exact setIntegral_congr_set Ioi_ae_eq_Ici.symm

theorem gap1 (p : ℝ) (hp : -1 < p) :
    (∫ x in (0 : ℝ)..1, logIntegrand p x) =
      -reverseImproperIntegral (gammaIntegrand p) := by
  rw [reverseImproperIntegral_eq_of_has
    (gamma_has_reverse_improper_integral p hp)]
  simpa using (log_interval_eq_gamma p hp)

theorem gap2 (p : ℝ) (hp : -1 < p) :
    -reverseImproperIntegral (gammaIntegrand p) =
      improperIntegral 0 (gammaIntegrand p) := by
  rw [reverseImproperIntegral_eq_of_has
    (gamma_has_reverse_improper_integral p hp)]
  rw [improperIntegral_eq_of_has
    (gamma_has_improper_integral p hp)]
  simp

theorem gap3 (p : ℝ) (hp : -1 < p) :
    improperIntegral 0 (gammaIntegrand p) =
      Real.Gamma (p + 1) := by
  exact improperIntegral_eq_of_has
    (gamma_has_improper_integral p hp)

theorem gap4 (p : ℝ) (hp : -1 < p) :
    (∫ x in (0 : ℝ)..1, logIntegrand p x) =
      Real.Gamma (p + 1) := by
  rw [gap1 p hp, gap2 p hp, gap3 p hp]

theorem gap5 (p : ℝ) (hp : -1 < p) :
    -1 < p := by
  exact hp

end

end ProofGap.Exercise3861
