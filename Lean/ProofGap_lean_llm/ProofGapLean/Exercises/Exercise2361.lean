import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise2361
noncomputable section

open Filter MeasureTheory

def integrand (p x : ℝ) : ℝ :=
  Real.rpow x (p - 1) * Real.exp (-x)

def NearZeroIntegrable (p : ℝ) : Prop :=
  IntegrableOn (integrand p) (Set.Ioc (0 : ℝ) 1)

def TailIntegrable (p : ℝ) : Prop :=
  IntegrableOn (integrand p) (Set.Ioi (1 : ℝ))

def GammaIntegrable (p : ℝ) : Prop :=
  IntegrableOn (integrand p) (Set.Ioi (0 : ℝ))

theorem gap1 (p : ℝ) :
    GammaIntegrable p ↔ NearZeroIntegrable p ∧ TailIntegrable p := by
  unfold GammaIntegrable NearZeroIntegrable TailIntegrable
  rw [(Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm,
    MeasureTheory.integrableOn_union]

theorem gap2 (p : ℝ) :
    NearZeroIntegrable p ↔ 0 < p := by
  have hIcc : IntegrableOn (integrand p) (Set.Icc (0 : ℝ) 1) ↔
      IntegrableOn (fun x : ℝ => x ^ (p - 1 : ℝ)) (Set.Icc (0 : ℝ) 1) := by
    constructor
    case mp =>
      intro h
      have hm := h.mul_continuousOn continuousOn_id.rexp isCompact_Icc
      exact hm.congr_fun (fun x _ => by
        simp [integrand, Real.exp_neg]) measurableSet_Icc
    case mpr =>
      intro h
      have hm := h.mul_continuousOn continuousOn_id.neg.rexp isCompact_Icc
      exact hm.congr_fun (fun x _ => by rfl) measurableSet_Icc
  unfold NearZeroIntegrable
  rw [(integrableOn_Icc_iff_integrableOn_Ioc (f := integrand p)).symm]
  rw [hIcc]
  rw [integrableOn_Icc_iff_integrableOn_Ioo]
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
  constructor <;> intro h <;> linarith

theorem gap3 (p : ℝ) (hp : 0 < p) :
    1 - p < 1 := by
  linarith

theorem gap4 (p : ℝ) (hp : 0 < p) :
    NearZeroIntegrable p := by
  exact (gap2 p).2 hp

theorem gap5 (p x : ℝ) (hx : 0 < x) :
    x ^ 2 * integrand p x =
      Real.rpow x (p + 1) / Real.exp x := by
  have hpow : x ^ 2 * Real.rpow x (p - 1) = Real.rpow x (p + 1) := by
    calc
      x ^ 2 * Real.rpow x (p - 1) =
          Real.rpow x (2 : ℝ) * Real.rpow x (p - 1) := by
            exact congrArg (fun z : ℝ => z * Real.rpow x (p - 1))
              (Real.rpow_natCast x 2).symm
      _ = Real.rpow x ((2 : ℝ) + (p - 1)) :=
        (Real.rpow_add hx _ _).symm
      _ = Real.rpow x (p + 1) := by
        congr 1
        ring
  unfold integrand
  rw [Real.exp_neg]
  simp only [div_eq_mul_inv]
  rw [(mul_assoc _ _ _).symm, hpow]

theorem gap6 (p : ℝ) :
    Tendsto (fun x => Real.rpow x (p + 1) / Real.exp x)
      atTop (nhds 0) := by
  exact Asymptotics.IsLittleO.tendsto_div_nhds_zero
    (isLittleO_rpow_exp_atTop (p + 1))

theorem gap7 (p : ℝ) :
    Tendsto (fun x => x ^ 2 * integrand p x)
      atTop (nhds 0) := by
  apply (gap6 p).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (gap5 p x hx).symm

theorem gap8 :
    ∀ p : ℝ, TailIntegrable p := by
  intro p
  unfold TailIntegrable
  have h : IntegrableOn (fun x : ℝ => Real.exp (-x) * Real.rpow x (p - 1))
      (Set.Ioi (1 : ℝ)) := by
    refine integrable_of_isBigO_exp_neg one_half_pos ?_
      (Real.Gamma_integrand_isLittleO (p - 1)).isBigO
    refine continuousOn_id.neg.rexp.mul (continuousOn_id.rpow_const ?_)
    intro x hx
    exact Or.inl ((zero_lt_one : (0 : ℝ) < 1).trans_le hx).ne'
  simpa [integrand, mul_comm] using h

theorem gap9 (p : ℝ) :
    0 < p ↔ GammaIntegrable p := by
  constructor
  case mp =>
    intro hp
    exact (gap1 p).2 ⟨gap4 p hp, gap8 p⟩
  case mpr =>
    intro hgamma
    exact (gap2 p).1 ((gap1 p).1 hgamma).1

end
end ProofGap.Exercise2361
