import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2751_2

noncomputable section

open Filter
open scoped Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  x ^ n / (1 + x ^ n)

def pointwiseLimit (x : ℝ) : ℝ :=
  if x < 1 then 0 else if x = 1 then 1 / 2 else 1

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < η

def witness (n : ℕ) : ℝ :=
  Real.rpow 2 (-(1 : ℝ) / n)

private theorem witness_tendsto_one :
    Tendsto witness atTop (nhds 1) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hnat
  have hexp : Tendsto (fun n : ℕ => -(1 : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinv.neg
  have hscaled :
      Tendsto (fun n : ℕ => Real.log 2 * (-(1 : ℝ) / (n : ℝ))) atTop
        (nhds 0) := by
    simpa using tendsto_const_nhds.mul hexp
  have hexponential :
      Tendsto
        (fun n : ℕ => Real.exp (Real.log 2 * (-(1 : ℝ) / (n : ℝ))))
        atTop (nhds 1) := by
    simpa using Real.continuous_exp.continuousAt.tendsto.comp hscaled
  refine hexponential.congr' (Filter.Eventually.of_forall ?_)
  intro n
  unfold witness
  symm
  exact Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)
    (-(1 : ℝ) / (n : ℝ))

theorem gap1 :
    ∀ (δ x : ℝ), 0 < δ → δ < 1 → x ∈ Set.Icc (1 - δ) (1 + δ) →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 (pointwiseLimit x)) := by
  intro δ x hδ hδ1 hx
  have hxpos : 0 < x := by
    linarith [hx.1]
  by_cases hlt : x < 1
  · have hpow : Tendsto (fun n : ℕ => x ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hxpos) hlt
    have hquot :
        Tendsto (fun n : ℕ => x ^ n / (1 + x ^ n)) atTop (nhds 0) := by
      simpa using
        hpow.div (tendsto_const_nhds.add hpow)
          (by norm_num : (1 : ℝ) + 0 ≠ 0)
    simpa [term, pointwiseLimit, hlt] using hquot
  · by_cases heq : x = 1
    · subst x
      have hpoint : pointwiseLimit 1 = (1 / 2 : ℝ) := by
        norm_num [pointwiseLimit]
      rw [hpoint]
      have hconst :
          Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2)) :=
        tendsto_const_nhds
      refine hconst.congr' (Filter.Eventually.of_forall ?_)
      intro n
      norm_num [term]
    · have hxgt : 1 < x :=
        lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      have hxne : x ≠ 0 := ne_of_gt hxpos
      have hxinvpos : 0 < x⁻¹ := inv_pos.mpr hxpos
      have hxinvlt : x⁻¹ < 1 := by
        have h := mul_lt_mul_of_pos_left hxgt hxinvpos
        simpa [hxne] using h
      have hpow : Tendsto (fun n : ℕ => (x⁻¹) ^ n) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hxinvpos) hxinvlt
      have hone :
          Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
        tendsto_const_nhds
      have hlim :
          Tendsto (fun n : ℕ => (1 : ℝ) / (1 + (x⁻¹) ^ n)) atTop
            (nhds 1) := by
        have h := hone.div (hone.add hpow)
          (by norm_num : (1 : ℝ) + 0 ≠ 0)
        convert h using 1 <;> norm_num
      have hterm : Tendsto (fun n : ℕ => term n x) atTop (nhds 1) := by
        refine hlim.congr' (Filter.Eventually.of_forall ?_)
        intro n
        unfold term
        rw [inv_pow]
        field_simp [pow_ne_zero n hxne] <;> ring
      simpa [pointwiseLimit, hlt, heq] using hterm

theorem gap2 :
    ∀ (δ x : ℝ), 0 < δ → δ < 1 → x ∈ Set.Icc (1 - δ) (1 + δ) →
      (if x < 1 then 0 else if x = 1 then 1 / 2 else 1) =
        pointwiseLimit x := by
  intros
  rfl

theorem gap3 :
    ∀ (δ x : ℝ), 0 < δ → δ < 1 → x ∈ Set.Icc (1 - δ) (1 + δ) →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 (pointwiseLimit x)) := by
  exact gap1

theorem gap4 :
    ∀ n : ℕ, 1 ≤ n →
      |term n (witness n) - pointwiseLimit (witness n)| = 1 / 3 := by
  intro n hn
  have hn0nat : n ≠ 0 := by omega
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0nat
  have hnpos : (0 : ℝ) < (n : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0nat)
  have hexpneg : -(1 : ℝ) / (n : ℝ) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) hnpos
  have hwlt : witness n < 1 := by
    unfold witness
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexpneg
  have hexp : (-(1 : ℝ) / (n : ℝ)) * (n : ℝ) = -1 := by
    field_simp [hn0] <;> ring
  have hp : witness n ^ n = (1 / 2 : ℝ) := by
    calc
      witness n ^ n = Real.rpow (witness n) (n : ℝ) := by
        symm
        exact Real.rpow_natCast (witness n) n
      _ = Real.rpow 2 ((-(1 : ℝ) / (n : ℝ)) * (n : ℝ)) := by
        unfold witness
        exact (Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))
          (-(1 : ℝ) / (n : ℝ)) (n : ℝ)).symm
      _ = Real.rpow 2 (-1) := by rw [hexp]
      _ = 1 / 2 := by
        have hneg :
            Real.rpow 2 (-(1 : ℝ)) =
              (Real.rpow 2 (1 : ℝ))⁻¹ := by
          exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (1 : ℝ)
        have hone : Real.rpow 2 (1 : ℝ) = 2 := by
          exact Real.rpow_one 2
        rw [hneg, hone]
        norm_num
  unfold pointwiseLimit
  rw [if_pos hwlt]
  unfold term
  rw [hp]
  norm_num

theorem gap5 :
    ∀ η₀ : ℝ, 0 < η₀ → η₀ < 1 / 3 → 1 / 3 > η₀ := by
  intro η₀ hη₀ hlt
  linarith

theorem gap6 :
    ∀ (n : ℕ) (η₀ : ℝ), 1 ≤ n → 0 < η₀ → η₀ < 1 / 3 →
      |term n (witness n) - pointwiseLimit (witness n)| > η₀ := by
  intro n η₀ hn hη₀ hlt
  rw [gap4 n hn]
  exact gap5 η₀ hη₀ hlt

theorem gap7 :
    ∀ δ : ℝ, 0 < δ → δ < 1 →
      ¬ UniformlyConvergesOn term pointwiseLimit
          (Set.Icc (1 - δ) (1 + δ)) := by
  intro δ hδ hδ1 hU
  obtain ⟨N, hN⟩ := hU (1 / 4) (by norm_num)
  have hevlow : ∀ᶠ n : ℕ in atTop, 1 - δ < witness n :=
    (tendsto_order.1 witness_tendsto_one).1 (1 - δ) (by linarith)
  rcases eventually_atTop.1 hevlow with ⟨K, hK⟩
  let n : ℕ := max K (N + 1)
  have hKn : K ≤ n := by simp [n]
  have hNn : N + 1 ≤ n := by simp [n]
  have hnN : N < n := by omega
  have hn1 : 1 ≤ n := by omega
  have hn0nat : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0nat)
  have hexpneg : -(1 : ℝ) / (n : ℝ) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) hnpos
  have hwtlt : witness n < 1 := by
    unfold witness
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexpneg
  have hmem : witness n ∈ Set.Icc (1 - δ) (1 + δ) := by
    constructor
    · exact le_of_lt (hK n hKn)
    · linarith
  have hsmall := hN n hnN (witness n) hmem
  have hlarge := gap6 n (1 / 4) hn1 (by norm_num) (by norm_num)
  linarith

theorem gap8 :
    ∀ δ : ℝ, 0 < δ → δ < 1 →
      ¬ UniformlyConvergesOn term pointwiseLimit
          (Set.Icc (1 - δ) (1 + δ)) := by
  exact gap7

end

end ProofGap.Exercise2751_2
