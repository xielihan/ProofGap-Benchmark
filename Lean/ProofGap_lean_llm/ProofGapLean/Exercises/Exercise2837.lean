import ProofGapLean.Prelude.Analysis
import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Order.Filter.AtTopBot.Defs

namespace ProofGap.Exercise2837

noncomputable section

open Filter
open scoped BigOperators Topology

def coefficient (n : ℕ) : ℝ :=
  ((3 : ℝ) ^ (3 * n) * (Nat.factorial n : ℝ) ^ 3) /
    Nat.factorial (3 * n)

def term (n : ℕ) (x : ℝ) : ℝ :=
  coefficient n * Real.tan x ^ n

def SeriesConvergesAt (x : ℝ) : Prop :=
  Real.cos x ≠ 0 ∧ Summable (fun k : ℕ => term (k + 1) x)

def ratioFormula (n : ℕ) : ℝ :=
  (((3 * n + 1 : ℕ) : ℝ) * ((3 * n + 2 : ℕ) : ℝ)) /
    (9 * ((n + 1 : ℕ) : ℝ) ^ 2)

private theorem coefficient_pos (n : ℕ) : 0 < coefficient n := by
  simp only [coefficient]
  positivity

private theorem coefficient_ne (n : ℕ) : coefficient n ≠ 0 :=
  (coefficient_pos n).ne'

private theorem coefficient_ratio (n : ℕ) :
    |coefficient n / coefficient (n + 1)| = ratioFormula n := by
  have hfac :
      Nat.factorial (3 * (n + 1)) =
        (3 * n + 3) * (3 * n + 2) * (3 * n + 1) * Nat.factorial (3 * n) := by
    rw [show 3 * (n + 1) = (3 * n + 2) + 1 by omega, Nat.factorial_succ]
    rw [show 3 * n + 2 = (3 * n + 1) + 1 by omega, Nat.factorial_succ]
    rw [show 3 * n + 1 = 3 * n + 1 by rfl, Nat.factorial_succ]
    ring
  rw [abs_of_pos (div_pos (coefficient_pos n) (coefficient_pos (n + 1)))]
  simp only [coefficient, ratioFormula]
  rw [hfac, Nat.factorial_succ]
  norm_num [Nat.cast_add, Nat.cast_mul, Nat.mul_add, pow_add]
  field_simp
  ring

private theorem coefficient_lower : ∀ n : ℕ, (n + 1 : ℝ) ≤ coefficient n := by
  intro n
  induction n with
  | zero => norm_num [coefficient]
  | succ n ih =>
      have hrev : coefficient (n + 1) / coefficient n = 1 / ratioFormula n := by
        rw [← coefficient_ratio n]
        rw [abs_of_pos (div_pos (coefficient_pos n) (coefficient_pos (n + 1)))]
        field_simp [coefficient_ne]
      have hstep : (n + 2 : ℝ) / (n + 1) ≤ coefficient (n + 1) / coefficient n := by
        rw [hrev]
        simp only [ratioFormula, one_div_div]
        norm_num [Nat.cast_add, Nat.cast_mul]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith
      have hs : ((n + 2 : ℝ) / (n + 1)) * coefficient n ≤ coefficient (n + 1) :=
        (le_div_iff₀ (coefficient_pos n)).mp hstep
      calc
        ((n + 1 : ℕ) : ℝ) + 1 = (n + 2 : ℝ) := by
          norm_num [Nat.cast_add] <;> ring
        _ = ((n + 2 : ℝ) / (n + 1)) * (n + 1) := by
          field_simp
        _ ≤ ((n + 2 : ℝ) / (n + 1)) * coefficient n :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ coefficient (n + 1) := hs

private theorem exists_centered_int_pi (x : ℝ) :
    ∃ k : ℤ,
      -(Real.pi / 2) ≤ x - (k : ℝ) * Real.pi ∧
        x - (k : ℝ) * Real.pi < Real.pi / 2 := by
  let k : ℤ := ⌊x / Real.pi + (1 : ℝ) / 2⌋
  have hk_le : (k : ℝ) ≤ x / Real.pi + (1 : ℝ) / 2 := Int.floor_le _
  have hx_lt : x / Real.pi + (1 : ℝ) / 2 < (k : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hp : 0 < Real.pi := Real.pi_pos
  have hle := mul_le_mul_of_nonneg_right hk_le hp.le
  have hlt := mul_lt_mul_of_pos_right hx_lt hp
  have hcancel : x / Real.pi * Real.pi = x := by
    field_simp [Real.pi_ne_zero]
  have hle' : (k : ℝ) * Real.pi ≤ x + Real.pi / 2 := by
    calc
      (k : ℝ) * Real.pi ≤ (x / Real.pi + (1 : ℝ) / 2) * Real.pi := hle
      _ = x + Real.pi / 2 := by
        rw [add_mul, hcancel]
        ring
  have hlt' : x + Real.pi / 2 < (k : ℝ) * Real.pi + Real.pi := by
    calc
      x + Real.pi / 2 = (x / Real.pi + (1 : ℝ) / 2) * Real.pi := by
        rw [add_mul, hcancel]
        ring
      _ < ((k : ℝ) + 1) * Real.pi := hlt
      _ = (k : ℝ) * Real.pi + Real.pi := by ring
  refine ⟨k, ?_, ?_⟩ <;> nlinarith

private theorem cos_ne_zero_and_abs_tan_lt_one_iff (x : ℝ) :
    Real.cos x ≠ 0 ∧ |Real.tan x| < 1 ↔
      ∃ k : ℤ, |x - (k : ℝ) * Real.pi| < Real.pi / 4 := by
  constructor
  · rintro ⟨hcos, htan⟩
    rcases exists_centered_int_pi x with ⟨k, hylo, hyhi⟩
    let y := x - (k : ℝ) * Real.pi
    have hxrepr : x = y + (k : ℝ) * Real.pi := by
      dsimp [y]
      ring
    have hycos : Real.cos y ≠ 0 := by
      intro h
      apply hcos
      rw [hxrepr, Real.cos_add]
      simp [h]
    have hylo_le : -(Real.pi / 2) ≤ y := by
      simpa [y] using hylo
    have hylo' : -(Real.pi / 2) < y := by
      apply lt_of_le_of_ne hylo_le
      intro h
      apply hycos
      rw [← h]
      simp
    have hymem : y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨hylo', hyhi⟩
    have htan_eq : Real.tan x = Real.tan y := by
      rw [hxrepr]
      exact Real.tan_add_int_mul_pi y k
    have hytan : |Real.tan y| < 1 := by
      rw [← htan_eq]
      exact htan
    have hnqmem : -(Real.pi / 4) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith [Real.pi_pos]
    have hqmem : Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith [Real.pi_pos]
    refine ⟨k, ?_⟩
    change |y| < Real.pi / 4
    apply abs_lt.mpr
    constructor
    · by_contra h
      have hyle : y ≤ -(Real.pi / 4) := le_of_not_gt h
      have htanle := Real.strictMonoOn_tan.monotoneOn hymem hnqmem hyle
      have htanle' : Real.tan y ≤ -1 := by
        simpa [Real.tan_pi_div_four] using htanle
      have hnonpos : Real.tan y ≤ 0 := le_trans htanle' (by norm_num)
      rw [abs_of_nonpos hnonpos] at hytan
      linarith
    · by_contra h
      have hyge : Real.pi / 4 ≤ y := le_of_not_gt h
      have htange := Real.strictMonoOn_tan.monotoneOn hqmem hymem hyge
      have htange' : 1 ≤ Real.tan y := by
        simpa [Real.tan_pi_div_four] using htange
      have hnonneg : 0 ≤ Real.tan y := le_trans (by norm_num) htange'
      rw [abs_of_nonneg hnonneg] at hytan
      linarith
  · rintro ⟨k, hk⟩
    let y := x - (k : ℝ) * Real.pi
    have hy : |y| < Real.pi / 4 := hk
    have hxrepr : x = y + (k : ℝ) * Real.pi := by
      dsimp [y]
      ring
    have hylo : -(Real.pi / 2) < y := by
      have h := (abs_lt.mp hy).1
      nlinarith [Real.pi_pos]
    have hyhi : y < Real.pi / 2 := by
      have h := (abs_lt.mp hy).2
      nlinarith [Real.pi_pos]
    have hymem : y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨hylo, hyhi⟩
    have hnqmem : -(Real.pi / 4) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith [Real.pi_pos]
    have hqmem : Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith [Real.pi_pos]
    have hycos : Real.cos y ≠ 0 :=
      (Real.cos_pos_of_mem_Ioo hymem).ne'
    have hsin : Real.sin ((k : ℝ) * Real.pi) = 0 := by
      simp
    have hkcos : Real.cos ((k : ℝ) * Real.pi) ≠ 0 := by
      intro hkzero
      have hsc := Real.sin_sq_add_cos_sq ((k : ℝ) * Real.pi)
      rw [hsin, hkzero] at hsc
      norm_num at hsc
    have hxcos : Real.cos x ≠ 0 := by
      rw [hxrepr, Real.cos_add, hsin]
      simpa using mul_ne_zero hycos hkcos
    have htan_eq : Real.tan x = Real.tan y := by
      rw [hxrepr]
      exact Real.tan_add_int_mul_pi y k
    have hlow := Real.strictMonoOn_tan hnqmem hymem (abs_lt.mp hy).1
    have hupp := Real.strictMonoOn_tan hymem hqmem (abs_lt.mp hy).2
    refine ⟨hxcos, ?_⟩
    rw [htan_eq]
    exact abs_lt.mpr ⟨by simpa [Real.tan_pi_div_four] using hlow,
      by simpa [Real.tan_pi_div_four] using hupp⟩

private theorem not_summable_terms_of_one_le_abs_tan {x : ℝ}
    (htan : 1 ≤ |Real.tan x|) :
    ¬ Summable (fun n : ℕ => term (n + 1) x) := by
  intro hs
  have hlower : ∀ n : ℕ, 1 ≤ |term (n + 1) x| := by
    intro n
    have hc : 1 ≤ |coefficient (n + 1)| := by
      rw [abs_of_pos (coefficient_pos (n + 1))]
      have hl := coefficient_lower (n + 1)
      have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      norm_num [Nat.cast_add] at hl
      linarith
    have hp : 1 ≤ |Real.tan x| ^ (n + 1) := one_le_pow₀ htan
    simpa [term, abs_mul, abs_pow] using
      (mul_le_mul hc hp (by norm_num : 0 ≤ (1 : ℝ))
        (abs_nonneg (coefficient (n + 1))))
  have ht : Tendsto (fun n : ℕ => |term (n + 1) x|) atTop (𝓝 0) := by
    simpa [Real.norm_eq_abs] using hs.tendsto_atTop_zero.norm
  have hevent : ∀ᶠ n : ℕ in atTop, |term (n + 1) x| < 1 :=
    (tendsto_order.1 ht).2 1 zero_lt_one
  rcases (eventually_atTop.1 hevent) with ⟨N, hN⟩
  exact (not_lt_of_ge (hlower N)) (hN N le_rfl)

private theorem abs_tan_eq_one_of_boundary (x : ℝ) (k : ℤ)
    (h : |x - (k : ℝ) * Real.pi| = Real.pi / 4) :
    |Real.tan x| = 1 := by
  let y := x - (k : ℝ) * Real.pi
  have hy : |y| = Real.pi / 4 := h
  have hxrepr : x = y + (k : ℝ) * Real.pi := by
    dsimp [y]
    ring
  have htan : Real.tan x = Real.tan y := by
    rw [hxrepr]
    exact Real.tan_add_int_mul_pi y k
  have hq : 0 ≤ Real.pi / 4 := by positivity
  rcases (abs_eq hq).mp hy with hy | hy
  · rw [htan, hy, Real.tan_pi_div_four]
    norm_num
  · rw [htan, hy]
    simp [Real.tan_pi_div_four]

theorem gap1 :
    (fun n : ℕ => |coefficient (n + 1) / coefficient (n + 2)|) =
      fun n : ℕ => ratioFormula (n + 1) := by
  funext n
  exact coefficient_ratio (n + 1)

theorem gap2 :
    Tendsto ratioFormula atTop (𝓝 1) := by
  have ha : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) := by
    simpa using tendsto_natCast_div_add_atTop 1
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hi : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) := by
    have hdiff := hconst.sub ha
    convert hdiff using 1
    · funext n
      field_simp [show (n : ℝ) + 1 ≠ 0 by positivity] <;> ring
    · norm_num
  have h := ha.add ((hi.mul hi).const_mul ((2 : ℝ) / 9))
  convert h using 1
  · funext n
    simp only [ratioFormula]
    norm_num [Nat.cast_add, Nat.cast_mul, Nat.mul_add]
    field_simp [show (n : ℝ) + 1 ≠ 0 by positivity] <;> ring
  · norm_num

theorem gap3 :
    Tendsto
      (fun n : ℕ => |coefficient (n + 1) / coefficient (n + 2)|)
      atTop (𝓝 1) := by
  rw [gap1]
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  exact gap2.comp hshift

theorem gap4 :
    ∀ x : ℝ, Real.cos x ≠ 0 → |Real.tan x| < 1 →
      ∃ k : ℤ, |x - (k : ℝ) * Real.pi| < Real.pi / 4 := by
  intro x hcos htan
  exact (cos_ne_zero_and_abs_tan_lt_one_iff x).mp ⟨hcos, htan⟩

theorem gap5 :
    ∀ x : ℝ, |Real.tan x| < 1 →
      ∃ k : ℤ, k ∈ Set.univ := by
  intro x hx
  exact ⟨0, Set.mem_univ 0⟩

theorem gap6 :
    ∀ x : ℝ, |Real.tan x| < 1 →
      Summable (fun k : ℕ => |term (k + 1) x|) := by
  intro x hx
  by_cases ht : Real.tan x = 0
  · simpa [term, ht]
  · have hc :
        Tendsto (fun n : ℕ => |coefficient (n + 2) / coefficient (n + 1)|)
          atTop (𝓝 1) := by
      have h := gap3.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
      convert h using 1
      · funext n
        rw [abs_div, abs_div]
        field_simp [coefficient_ne]
      · norm_num
    have hr :
        Tendsto (fun n : ℕ => |term (n + 2) x| / |term (n + 1) x|)
          atTop (𝓝 |Real.tan x|) := by
      have h := hc.mul
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => |Real.tan x|) atTop (𝓝 |Real.tan x|))
      convert h using 1
      · funext n
        simp only [term, abs_mul, abs_pow]
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, abs_div]
        field_simp [coefficient_ne, ht]
      · norm_num
    apply summable_of_ratio_test_tendsto_lt_one hx
    · exact Filter.Eventually.of_forall (fun n => by
        simp [term, coefficient_ne, ht])
    · simpa only [Real.norm_eq_abs, abs_abs, Nat.add_assoc] using hr

theorem gap7 :
    ∀ x : ℝ,
      (∀ k : ℤ, Real.pi / 4 < |x - (k : ℝ) * Real.pi|) →
        ¬ SeriesConvergesAt x := by
  intro x hdist hs
  have hnot : ¬ ∃ k : ℤ, |x - (k : ℝ) * Real.pi| < Real.pi / 4 := by
    rintro ⟨k, hk⟩
    exact (not_lt_of_ge (le_of_lt (hdist k))) hk
  have hpair : ¬ (Real.cos x ≠ 0 ∧ |Real.tan x| < 1) := by
    intro h
    exact hnot ((cos_ne_zero_and_abs_tan_lt_one_iff x).mp h)
  have hge : 1 ≤ |Real.tan x| := by
    apply le_of_not_gt
    intro ht
    exact hpair ⟨hs.1, ht⟩
  exact not_summable_terms_of_one_le_abs_tan hge hs.2

theorem gap8 :
    ∀ (x : ℝ) (k : ℤ),
      |x - (k : ℝ) * Real.pi| = Real.pi / 4 →
        (fun n : ℕ => term (n + 1) x) =
          fun n : ℕ =>
            coefficient (n + 1) * Real.tan x ^ (n + 1) := by
  intro x k hx
  rfl

theorem gap9 :
    ∀ n : ℕ,
      |coefficient n / coefficient (n + 1)| = ratioFormula n := by
  intro n
  exact coefficient_ratio n

theorem gap10 :
    ∀ n : ℕ, ratioFormula n < 1 := by
  intro n
  simp only [ratioFormula]
  norm_num [Nat.cast_add, Nat.cast_mul]
  apply (div_lt_one (by positivity)).2
  nlinarith

theorem gap11 :
    ∀ n : ℕ,
      |coefficient n / coefficient (n + 1)| < 1 := by
  intro n
  rw [gap9 n]
  exact gap10 n

theorem gap12 :
    ∀ n : ℕ, |coefficient n| < |coefficient (n + 1)| := by
  intro n
  have h := gap11 n
  rw [abs_div, div_lt_one (abs_pos.mpr (coefficient_ne (n + 1)))] at h
  exact h

theorem gap13 :
    Tendsto coefficient atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  obtain ⟨N, hN⟩ := exists_nat_ge b
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  calc
    b ≤ (N : ℝ) := hN
    _ ≤ (n : ℝ) := hcast
    _ ≤ (n + 1 : ℝ) := by norm_num
    _ ≤ coefficient n := coefficient_lower n

theorem gap14 :
    ∀ (x : ℝ) (k : ℤ),
      |x - (k : ℝ) * Real.pi| = Real.pi / 4 →
        ¬ SeriesConvergesAt x := by
  intro x k hx hs
  have ht : |Real.tan x| = 1 := abs_tan_eq_one_of_boundary x k hx
  have hge : 1 ≤ |Real.tan x| := le_of_eq ht.symm
  exact not_summable_terms_of_one_le_abs_tan hge hs.2

theorem gap15 :
    ∀ x : ℝ,
      x ∈ {y : ℝ |
        ∃ k : ℤ, |y - (k : ℝ) * Real.pi| < Real.pi / 4} ↔
          SeriesConvergesAt x := by
  intro x
  constructor
  · rintro ⟨k, hk⟩
    have hp := (cos_ne_zero_and_abs_tan_lt_one_iff x).mpr ⟨k, hk⟩
    have ha := gap6 x hp.2
    have hn : Summable (fun n : ℕ => ‖term (n + 1) x‖) := by
      simpa [Real.norm_eq_abs] using ha
    exact ⟨hp.1, hn.of_norm⟩
  · intro hs
    have ht : |Real.tan x| < 1 := by
      by_contra h
      have hge : 1 ≤ |Real.tan x| := le_of_not_gt h
      exact not_summable_terms_of_one_le_abs_tan hge hs.2
    exact (cos_ne_zero_and_abs_tan_lt_one_iff x).mp ⟨hs.1, ht⟩

end

end ProofGap.Exercise2837
