import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise1372

noncomputable section

open Filter

def rightZero : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)

def smallEnough (x : ℝ) : Prop := 0 < x ∧ x < 1

def realPowerValue (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (f x * Real.log x)

theorem gap1 :
    Tendsto (fun x : ℝ => x * Real.log x) rightZero (nhds 0) := by
  have hsqrt :
      Tendsto (fun x : ℝ => -2 * Real.sqrt x) rightZero (nhds 0) := by
    have hs : Tendsto Real.sqrt rightZero (nhds (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.mono_left inf_le_left
    have hc :
        Tendsto (fun _ : ℝ => (-2 : ℝ)) rightZero (nhds (-2)) :=
      tendsto_const_nhds
    simpa using hc.mul hs
  have hzero :
      Tendsto (fun _ : ℝ => (0 : ℝ)) rightZero (nhds 0) :=
    tendsto_const_nhds
  have hsmall : ∀ᶠ x : ℝ in rightZero, smallEnough x := by
    change ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), smallEnough x
    have hpos :
        ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < x :=
      self_mem_nhdsWithin
    have hlt : ∀ᶠ x : ℝ in nhds (0 : ℝ), x < 1 :=
      isOpen_Iio.mem_nhds (show (0 : ℝ) < 1 from zero_lt_one)
    have hltWithin :
        ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), x < 1 :=
      hlt.filter_mono inf_le_left
    filter_upwards [hpos, hltWithin] with x hx0 hx1
    exact ⟨hx0, hx1⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hsqrt hzero ?_ ?_
  · filter_upwards [hsmall] with x hx
    have hspos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx.1
    have hsq : (Real.sqrt x) ^ 2 = x :=
      Real.sq_sqrt (le_of_lt hx.1)
    have hinv :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr hspos)
    rw [Real.log_inv] at hinv
    have hlogs : -Real.log (Real.sqrt x) ≤ (Real.sqrt x)⁻¹ := by
      linarith
    have hlogx : Real.log x = 2 * Real.log (Real.sqrt x) := by
      calc
        Real.log x = Real.log ((Real.sqrt x) ^ 2) :=
          congrArg Real.log hsq.symm
        _ = 2 * Real.log (Real.sqrt x) := by
          norm_num [Real.log_pow]
    have hneglog : -Real.log x ≤ 2 / Real.sqrt x := by
      rw [hlogx, div_eq_mul_inv]
      linarith
    have hmul :=
      mul_le_mul_of_nonneg_left hneglog (le_of_lt hx.1)
    have hcancel : x * (2 / Real.sqrt x) = 2 * Real.sqrt x := by
      calc
        x * (2 / Real.sqrt x) =
            (Real.sqrt x) ^ 2 * (2 / Real.sqrt x) :=
          congrArg (fun y : ℝ => y * (2 / Real.sqrt x)) hsq.symm
        _ = 2 * Real.sqrt x := by
          field_simp [ne_of_gt hspos]
          <;> ring
    have hbound : x * (-Real.log x) ≤ 2 * Real.sqrt x := by
      calc
        x * (-Real.log x) ≤ x * (2 / Real.sqrt x) := hmul
        _ = 2 * Real.sqrt x := hcancel
    nlinarith [hbound]
  · filter_upwards [hsmall] with x hx
    exact mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt hx.1) (le_of_lt (Real.log_neg hx.1 hx.2))

theorem gap2 (f : ℝ → ℝ) (k : ℝ)
    (hlower : ∀ x, -k * x ≤ f x) :
    ∀ x, -k * x ≤ f x := by
  exact hlower

theorem gap3 (f : ℝ → ℝ) (k : ℝ)
    (hupper : ∀ x, f x ≤ k * x) :
    ∀ x, f x ≤ k * x := by
  exact hupper

theorem gap4 (k x : ℝ) (hk : 0 ≤ k) (hx : 0 ≤ x) :
    -k * x ≤ k * x := by
  calc
    -k * x = -(k * x) := by rw [neg_mul]
    _ ≤ 0 := neg_nonpos.mpr (mul_nonneg hk hx)
    _ ≤ k * x := mul_nonneg hk hx

theorem gap5 (x : ℝ) (hx : smallEnough x) :
    Real.log x < 0 := by
  exact Real.log_neg hx.1 hx.2

theorem gap6 (f : ℝ → ℝ) (k x : ℝ)
    (hupper : f x ≤ k * x) (hlog : Real.log x < 0) :
    k * x * Real.log x ≤ f x * Real.log x := by
  exact mul_le_mul_of_nonpos_right hupper (le_of_lt hlog)

theorem gap7 (f : ℝ → ℝ) (k x : ℝ)
    (hlower : -k * x ≤ f x) (hlog : Real.log x < 0) :
    f x * Real.log x ≤ -k * x * Real.log x := by
  exact mul_le_mul_of_nonpos_right hlower (le_of_lt hlog)

theorem gap8 (k x : ℝ) (hk : 0 ≤ k) (hx : smallEnough x) :
    k * x * Real.log x ≤ -k * x * Real.log x := by
  exact mul_le_mul_of_nonpos_right
    (gap4 k x hk (le_of_lt hx.1))
    (le_of_lt (gap5 x hx))

theorem gap9 (f : ℝ → ℝ) (k x : ℝ)
    (h : k * x * Real.log x ≤ f x * Real.log x) :
    Real.exp (k * x * Real.log x) ≤ realPowerValue f x := by
  simpa only [realPowerValue] using Real.exp_le_exp.mpr h

theorem gap10 (f : ℝ → ℝ) (k x : ℝ)
    (h : f x * Real.log x ≤ -k * x * Real.log x) :
    realPowerValue f x ≤ Real.exp (-k * x * Real.log x) := by
  simpa only [realPowerValue] using Real.exp_le_exp.mpr h

theorem gap11 (k x : ℝ)
    (h : k * x * Real.log x ≤ -k * x * Real.log x) :
    Real.exp (k * x * Real.log x) ≤ Real.exp (-k * x * Real.log x) := by
  exact Real.exp_le_exp.mpr h

theorem gap12 (k : ℝ) :
    Tendsto (fun x : ℝ => Real.exp (k * x * Real.log x))
      rightZero (nhds (Real.exp 0)) := by
  have hmul :
      Tendsto (fun x : ℝ => k * (x * Real.log x)) rightZero (nhds 0) := by
    simpa using (tendsto_const_nhds.mul gap1)
  have hexp :
      Tendsto Real.exp (nhds (0 : ℝ)) (nhds (Real.exp 0)) :=
    (Real.hasDerivAt_exp 0).continuousAt
  simpa only [mul_assoc] using hexp.comp hmul

theorem gap13 :
    Real.exp 0 = 1 := by
  exact Real.exp_zero

theorem gap14 (k : ℝ) :
    Tendsto (fun x : ℝ => Real.exp (k * x * Real.log x))
      rightZero (nhds 1) := by
  simpa only [gap13] using (gap12 k)

theorem gap15 (k : ℝ) :
    Tendsto (fun x : ℝ => Real.exp (-k * x * Real.log x))
      rightZero (nhds (Real.exp 0)) := by
  exact gap12 (-k)

theorem gap16 :
    Real.exp 0 = 1 := by
  exact gap13

theorem gap17 (k : ℝ) :
    Tendsto (fun x : ℝ => Real.exp (-k * x * Real.log x))
      rightZero (nhds 1) := by
  simpa only [gap16] using (gap15 k)

theorem gap18 (f : ℝ → ℝ) (x : ℝ) (hx : 0 < x) :
    realPowerValue f x = Real.rpow x (f x) := by
  unfold realPowerValue
  calc
    Real.exp (f x * Real.log x) =
        Real.exp (Real.log x * f x) := by rw [mul_comm]
    _ = Real.rpow x (f x) := (Real.rpow_def_of_pos hx (f x)).symm

theorem gap19 (f : ℝ → ℝ) (k : ℝ)
    (hk : 0 ≤ k)
    (hbound : ∀ x, 0 < x → -k * x ≤ f x ∧ f x ≤ k * x) :
    Tendsto (fun x : ℝ => Real.rpow x (f x)) rightZero (nhds 1) := by
  have hsmall : ∀ᶠ x : ℝ in rightZero, smallEnough x := by
    change ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), smallEnough x
    have hpos :
        ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < x :=
      self_mem_nhdsWithin
    have hlt : ∀ᶠ x : ℝ in nhds (0 : ℝ), x < 1 :=
      isOpen_Iio.mem_nhds (show (0 : ℝ) < 1 from zero_lt_one)
    have hltWithin :
        ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), x < 1 :=
      hlt.filter_mono inf_le_left
    filter_upwards [hpos, hltWithin] with x hx0 hx1
    exact ⟨hx0, hx1⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (gap14 k) (gap17 k) ?_ ?_
  · filter_upwards [hsmall] with x hx
    rw [← gap18 f x hx.1]
    exact gap9 f k x
      (gap6 f k x (hbound x hx.1).2 (gap5 x hx))
  · filter_upwards [hsmall] with x hx
    rw [← gap18 f x hx.1]
    exact gap10 f k x
      (gap7 f k x (hbound x hx.1).1 (gap5 x hx))

theorem gap20 (f : ℝ → ℝ) (k : ℝ)
    (hk : 0 ≤ k)
    (hbound : ∀ x, 0 < x → -k * x ≤ f x ∧ f x ≤ k * x) :
    Tendsto (fun x : ℝ => Real.rpow x (f x)) rightZero (nhds 1) := by
  exact gap19 f k hk hbound

end

end ProofGap.Exercise1372
