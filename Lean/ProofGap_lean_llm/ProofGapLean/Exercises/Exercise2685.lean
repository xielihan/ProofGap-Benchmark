import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2685

noncomputable section

open Filter

def rootTerm (n : ℕ) : ℝ :=
  Real.rpow n (2 / (n : ℝ))

def exponentTerm (n : ℕ) : ℝ :=
  2 * Real.log n / (n : ℝ)

def expForm (n : ℕ) : ℝ :=
  Real.exp (exponentTerm n)

def alternatingTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / rootTerm n

private theorem exponentTerm_tendsto_aux :
    Tendsto (fun n : ℕ => exponentTerm (n + 1)) atTop (nhds 0) := by
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    exact (eventually_ge_atTop b).mono (fun a ha => Nat.le.step ha)
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have harg :
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    hcast.comp hshift
  have hlogReal :
      Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlog :
      Tendsto
        (fun n : ℕ => Real.log (((n + 1 : ℕ) : ℝ)) /
          (((n + 1 : ℕ) : ℝ))) atTop (nhds 0) :=
    hlogReal.comp harg
  have hmul :
      Tendsto
        (fun n : ℕ => (2 : ℝ) *
          (Real.log (((n + 1 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ))))
        atTop (nhds ((2 : ℝ) * 0)) :=
    tendsto_const_nhds.mul hlog
  simpa [exponentTerm, mul_div_assoc] using hmul

theorem gap1 :
    ∀ n : ℕ, 1 ≤ n → rootTerm n = expForm n := by
  intro n hn
  have hnposNat : 0 < n :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hnposNat
  unfold rootTerm expForm exponentTerm
  calc
    Real.rpow (n : ℝ) (2 / (n : ℝ)) =
        Real.exp (Real.log (n : ℝ) * (2 / (n : ℝ))) := by
      change (n : ℝ) ^ (2 / (n : ℝ)) =
        Real.exp (Real.log (n : ℝ) * (2 / (n : ℝ)))
      exact Real.rpow_def_of_pos hnpos (2 / (n : ℝ))
    _ = Real.exp (2 * Real.log (n : ℝ) / (n : ℝ)) := by
      congr 1
      ring

theorem gap2 :
    Tendsto (fun n : ℕ => expForm (n + 1)) atTop (nhds (Real.exp 0)) := by
  exact (Real.continuous_exp.tendsto 0).comp exponentTerm_tendsto_aux

theorem gap3 :
    Tendsto (fun n : ℕ => exponentTerm (n + 1)) atTop (nhds 0) := by
  exact exponentTerm_tendsto_aux

theorem gap4 : Real.exp 0 = 1 := by
  exact Real.exp_zero

theorem gap5 :
    Tendsto (fun n : ℕ => rootTerm (n + 1)) atTop (nhds 1) := by
  have hExp :
      Tendsto (fun n : ℕ => expForm (n + 1)) atTop (nhds 1) := by
    simpa [gap4] using gap2
  apply hExp.congr'
  exact Filter.Eventually.of_forall (fun n =>
    (gap1 (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).symm)

theorem gap6 :
    ¬ Tendsto (fun n : ℕ => alternatingTerm (n + 1)) atTop (nhds 0) := by
  intro hzero
  have habs0 :
      Tendsto (fun n : ℕ => |alternatingTerm (n + 1)|) atTop (nhds 0) := by
    simpa using ((continuous_abs.tendsto (0 : ℝ)).comp hzero)
  have habs_eq :
      (fun n : ℕ => |alternatingTerm (n + 1)|) =ᶠ[atTop]
        (fun n : ℕ => (rootTerm (n + 1))⁻¹) := by
    exact Filter.Eventually.of_forall (fun n => by
      have hn : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
      have hrootpos : 0 < rootTerm (n + 1) := by
        rw [gap1 (n + 1) hn]
        exact Real.exp_pos _
      simp [alternatingTerm, abs_div, abs_of_pos hrootpos])
  have hinv :
      Tendsto (fun n : ℕ => (rootTerm (n + 1))⁻¹) atTop
        (nhds ((1 : ℝ)⁻¹)) :=
    gap5.inv₀ one_ne_zero
  have habs1 :
      Tendsto (fun n : ℕ => |alternatingTerm (n + 1)|) atTop (nhds 1) := by
    simpa using hinv.congr' habs_eq.symm
  have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique habs0 habs1
  exact zero_ne_one h01

theorem gap7 :
    ¬ Summable (fun n : ℕ => alternatingTerm (n + 1)) := by
  intro hs
  apply gap6
  exact hs.tendsto_atTop_zero

end

end ProofGap.Exercise2685
