import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2626

noncomputable section

open Filter

def term (a : ℝ) (n : ℕ) : ℝ :=
  (Real.sqrt (n + 2) - Real.sqrt (n - 2)) / Real.rpow n a

def rewritten (a : ℝ) (n : ℕ) : ℝ :=
  4 / (Real.rpow n a * (Real.sqrt (n + 2) + Real.sqrt (n - 2)))

def comparison (a : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow n (a + 1 / 2)

def converges (a : ℝ) : Prop :=
  Summable (fun n : ℕ => term a (n + 2))

theorem gap1 (a : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    0 < term a n := by
  unfold term
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hm : 0 ≤ (n : ℝ) - 2 := by linarith
  have hp : 0 ≤ (n : ℝ) + 2 := by linarith
  have hsqrt :
      Real.sqrt ((n : ℝ) - 2) < Real.sqrt ((n : ℝ) + 2) := by
    have hs1 := Real.sq_sqrt hm
    have hs2 := Real.sq_sqrt hp
    have hsn1 := Real.sqrt_nonneg ((n : ℝ) - 2)
    have hsn2 := Real.sqrt_nonneg ((n : ℝ) + 2)
    nlinarith
  exact div_pos (sub_pos.mpr hsqrt) (Real.rpow_pos_of_pos hn_pos a)

theorem gap2 (a : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    term a n = rewritten a n := by
  unfold term rewritten
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hm : 0 ≤ (n : ℝ) - 2 := by linarith
  have hp : 0 ≤ (n : ℝ) + 2 := by linarith
  have hpow : Real.rpow (n : ℝ) a ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hn_pos a)
  have hsum :
      Real.sqrt ((n : ℝ) + 2) + Real.sqrt ((n : ℝ) - 2) ≠ 0 := by
    have hspos : 0 < Real.sqrt ((n : ℝ) + 2) :=
      Real.sqrt_pos.2 (by linarith)
    have hsnonneg := Real.sqrt_nonneg ((n : ℝ) - 2)
    positivity
  have hs1 := Real.sq_sqrt hp
  have hs2 := Real.sq_sqrt hm
  field_simp [hpow, hsum]
  nlinarith

theorem gap3 (a : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    0 < rewritten a n := by
  rw [← gap2 a n hn]
  exact gap1 a n hn

theorem gap4 (a : ℝ) :
    Tendsto
      (fun n : ℕ => rewritten a (n + 2) / comparison a (n + 2))
      atTop (nhds 2) := by
  have hinv :
      Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have htwo :
      Tendsto (fun n : ℕ => 1 + 2 * ((n : ℝ))⁻¹) atTop (nhds 1) := by
    convert tendsto_const_nhds.add (tendsto_const_nhds.mul hinv) using 1 <;>
      norm_num
  have hfour :
      Tendsto (fun n : ℕ => 1 + 4 * ((n : ℝ))⁻¹) atTop (nhds 1) := by
    convert tendsto_const_nhds.add (tendsto_const_nhds.mul hinv) using 1 <;>
      norm_num
  have hs2 :
      Tendsto
        (fun n : ℕ => Real.sqrt (1 + 2 * ((n : ℝ))⁻¹))
        atTop (nhds 1) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp htwo
  have hs4 :
      Tendsto
        (fun n : ℕ => Real.sqrt (1 + 4 * ((n : ℝ))⁻¹))
        atTop (nhds 1) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hfour
  have hnormalized :
      Tendsto
        (fun n : ℕ =>
          4 * Real.sqrt (1 + 2 * ((n : ℝ))⁻¹) /
            (Real.sqrt (1 + 4 * ((n : ℝ))⁻¹) + 1))
        atTop (nhds 2) := by
    convert (tendsto_const_nhds.mul hs2).div
      (hs4.add tendsto_const_nhds) (by norm_num : (1 : ℝ) + 1 ≠ 0) using 1 <;>
      norm_num
  refine (tendsto_congr' ?_).2 hnormalized
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by linarith
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hnR)
  have hrpow_ne : Real.rpow ((n : ℝ) + 2) a ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hn2 a)
  have hrpow_add :
      Real.rpow ((n : ℝ) + 2) (a + 1 / 2) =
        Real.rpow ((n : ℝ) + 2) a * Real.sqrt ((n : ℝ) + 2) := by
    simpa only [Real.sqrt_eq_rpow] using
      (Real.rpow_add hn2 a (1 / 2))
  have hsqrt2 :
      Real.sqrt ((n : ℝ) + 2) =
        Real.sqrt (n : ℝ) *
          Real.sqrt (1 + 2 * ((n : ℝ))⁻¹) := by
    rw [← Real.sqrt_mul (le_of_lt hnR)]
    congr 1
    field_simp [hn_ne]
  have hsqrt4 :
      Real.sqrt ((n : ℝ) + 2 + 2) =
        Real.sqrt (n : ℝ) *
          Real.sqrt (1 + 4 * ((n : ℝ))⁻¹) := by
    rw [← Real.sqrt_mul (le_of_lt hnR)]
    congr 1
    field_simp [hn_ne]
    ring
  simp only [rewritten, comparison, Nat.cast_add, Nat.cast_ofNat]
  rw [show (n : ℝ) + 2 - 2 = (n : ℝ) by ring]
  rw [hrpow_add, hsqrt2, hsqrt4]
  have hd1 :
      Real.sqrt (n : ℝ) *
            Real.sqrt (1 + 4 * ((n : ℝ))⁻¹) +
          Real.sqrt (n : ℝ) ≠ 0 := by
    have hq : 0 < 1 + 4 * ((n : ℝ))⁻¹ := by positivity
    have := Real.sqrt_pos.2 hq
    positivity
  have hd2 :
      Real.sqrt (1 + 4 * ((n : ℝ))⁻¹) + 1 ≠ 0 := by
    positivity
  field_simp [hrpow_ne, hsqrt_ne, hd1, hd2]

theorem gap5 (a : ℝ) :
    converges a ↔ 1 < a + 1 / 2 := by
  let f : ℕ → ℝ := fun n => rewritten a (n + 2)
  let g : ℕ → ℝ := fun n => comparison a (n + 2)
  have hf_pos (n : ℕ) : 0 < f n := by
    dsimp [f]
    exact gap3 a (n + 2) (by omega)
  have hg_pos (n : ℕ) : 0 < g n := by
    dsimp [g, comparison]
    positivity
  have hratio : Tendsto (fun n => f n / g n) atTop (nhds 2) := by
    simpa [f, g] using gap4 a
  have hlower : ∀ᶠ n in atTop, 1 < f n / g n :=
    (tendsto_order.1 hratio).1 1 (by norm_num)
  have hupper : ∀ᶠ n in atTop, f n / g n < 3 :=
    (tendsto_order.1 hratio).2 3 (by norm_num)
  have hlower' : ∀ᶠ n in cofinite, 1 < f n / g n := by
    simpa only [Nat.cofinite_eq_atTop] using hlower
  have hupper' : ∀ᶠ n in cofinite, f n / g n < 3 := by
    simpa only [Nat.cofinite_eq_atTop] using hupper
  have hsum_fg : Summable f ↔ Summable g := by
    constructor
    · intro hf
      apply hf.of_norm_bounded_eventually
      filter_upwards [hlower'] with n hn
      have hgf : g n ≤ f n := by
        have hlt : g n < f n := by
          have := (lt_div_iff₀ (hg_pos n)).mp hn
          simpa using this
        exact hlt.le
      simpa [Real.norm_eq_abs, abs_of_pos (hg_pos n), abs_of_pos (hf_pos n)]
        using hgf
    · intro hg
      have hmajor : Summable (fun n => (3 : ℝ) * g n) := hg.mul_left 3
      apply hmajor.of_norm_bounded_eventually
      filter_upwards [hupper'] with n hn
      have hle : f n ≤ 3 * g n := by
        exact ((div_lt_iff₀ (hg_pos n)).mp hn).le
      simpa [Real.norm_eq_abs, abs_of_pos (hf_pos n), abs_of_pos (hg_pos n)]
        using hle
  have hterm_f :
      Summable (fun n : ℕ => term a (n + 2)) ↔ Summable f := by
    constructor
    · intro h
      apply h.congr
      intro n
      exact gap2 a (n + 2) (by omega)
    · intro h
      apply h.congr
      intro n
      exact (gap2 a (n + 2) (by omega)).symm
  have hcomparison :
      (fun n : ℕ => comparison a n) =
        (fun n : ℕ => Real.rpow (n : ℝ) (-(a + 1 / 2))) := by
    funext n
    unfold comparison
    symm
    simpa only [one_div] using
      (Real.rpow_neg (Nat.cast_nonneg n) (a + 1 / 2))
  have hpseries :
      Summable (fun n : ℕ => comparison a n) ↔ 1 < a + 1 / 2 := by
    rw [hcomparison]
    constructor
    · intro hs
      have he : -(a + 1 / 2) < -1 :=
        Real.summable_nat_rpow.mp hs
      linarith
    · intro ha
      apply Real.summable_nat_rpow.mpr
      linarith
  unfold converges
  rw [hterm_f, hsum_fg]
  change Summable (fun n : ℕ => comparison a (n + 2)) ↔ _
  rw [summable_nat_add_iff]
  exact hpseries

theorem gap6 (a : ℝ) :
    1 < a + 1 / 2 ↔ 1 / 2 < a := by
  constructor <;> intro h <;> linarith

theorem gap7 (a : ℝ) :
    a ∈ {r : ℝ | 1 / 2 < r} ↔ converges a := by
  change 1 / 2 < a ↔ converges a
  rw [gap5, gap6]

end

end ProofGap.Exercise2626
