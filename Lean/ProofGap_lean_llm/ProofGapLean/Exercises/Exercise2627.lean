import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2627

noncomputable section

open Filter

def fourthRoot (x : ℝ) : ℝ := Real.rpow x (1 / 4 : ℝ)

def term (a b : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (n + a) - fourthRoot ((n : ℝ) ^ 2 + n + b)

def rationalized (a b : ℝ) (n : ℕ) : ℝ :=
  ((2 * a - 1) * n + a ^ 2 - b) /
    ((Real.sqrt (n + a) + fourthRoot ((n : ℝ) ^ 2 + n + b)) *
      (n + a + Real.sqrt ((n : ℝ) ^ 2 + n + b)))

def comparisonThreeHalves (n : ℕ) : ℝ :=
  1 / Real.rpow n (3 / 2 : ℝ)

def comparisonHalf (n : ℕ) : ℝ :=
  1 / Real.sqrt n

def converges (a b : ℝ) : Prop :=
  Summable (fun n : ℕ => term a b (n + 1))

theorem gap1 (a b : ℝ) (n : ℕ)
    (h₁ : 0 < (n : ℝ) + a)
    (h₂ : 0 < (n : ℝ) ^ 2 + n + b) :
    term a b n = rationalized a b n := by
  let A : ℝ := (n : ℝ) + a
  let Q : ℝ := (n : ℝ) ^ 2 + n + b
  have hQ : 0 < Q := by simpa [Q] using h₂
  have hsqrtA : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt h₁.le
  have hsqrtQ : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt hQ.le
  have hfourth : (fourthRoot Q) ^ 2 = Real.sqrt Q := by
    unfold fourthRoot
    calc
      (Real.rpow Q (1 / 4 : ℝ)) ^ 2 =
          Real.rpow (Real.rpow Q (1 / 4 : ℝ)) (2 : ℝ) := by
        simpa using
          (Real.rpow_natCast (Real.rpow Q (1 / 4 : ℝ)) 2).symm
      _ = Real.rpow Q ((1 / 4 : ℝ) * 2) := by
        exact (Real.rpow_mul hQ.le (1 / 4 : ℝ) (2 : ℝ)).symm
      _ = Real.sqrt Q := by
        norm_num [Real.sqrt_eq_rpow]
  have hsqrtApos : 0 < Real.sqrt A := Real.sqrt_pos.2 h₁
  have hfourthPos : 0 < fourthRoot Q :=
    Real.rpow_pos_of_pos h₂ (1 / 4 : ℝ)
  have hsqrtQpos : 0 < Real.sqrt Q := Real.sqrt_pos.2 h₂
  have hden : (Real.sqrt A + fourthRoot Q) * (A + Real.sqrt Q) ≠ 0 :=
    mul_ne_zero (add_pos hsqrtApos hfourthPos).ne'
      (add_pos h₁ hsqrtQpos).ne'
  unfold term rationalized
  change Real.sqrt A - fourthRoot Q =
    (((2 * a - 1) * n + a ^ 2 - b) /
      ((Real.sqrt A + fourthRoot Q) * (A + Real.sqrt Q)))
  rw [eq_div_iff hden]
  calc
    (Real.sqrt A - fourthRoot Q) *
        ((Real.sqrt A + fourthRoot Q) * (A + Real.sqrt Q)) =
        ((Real.sqrt A) ^ 2 - (fourthRoot Q) ^ 2) *
          (A + Real.sqrt Q) := by ring
    _ = (A - Real.sqrt Q) * (A + Real.sqrt Q) := by
      rw [hsqrtA, hfourth]
    _ = A ^ 2 - (Real.sqrt Q) ^ 2 := by ring
    _ = A ^ 2 - Q := by rw [hsqrtQ]
    _ = (2 * a - 1) * n + a ^ 2 - b := by
      dsimp only [A, Q]
      push_cast
      ring

theorem gap2 (a b : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N,
      0 < (n : ℝ) + a ∧ 0 < (n : ℝ) ^ 2 + n + b := by
  let R : ℝ := max (-a + 1) (max 1 (-b + 1))
  refine ⟨⌈R⌉₊, ?_⟩
  intro n hn
  have hRn : R ≤ (n : ℝ) :=
    (Nat.le_ceil R).trans (Nat.cast_le.mpr hn)
  have haLower : -a + 1 ≤ (n : ℝ) := (le_max_left _ _).trans hRn
  have hn1 : (1 : ℝ) ≤ n :=
    (le_max_left 1 (-b + 1)).trans ((le_max_right _ _).trans hRn)
  have hbLower : -b + 1 ≤ (n : ℝ) :=
    (le_max_right 1 (-b + 1)).trans ((le_max_right _ _).trans hRn)
  constructor
  · linarith
  · nlinarith [sq_nonneg (n : ℝ)]

private def denominator (a b x : ℝ) : ℝ :=
  (Real.sqrt (x + a) + fourthRoot (x ^ 2 + x + b)) *
    (x + a + Real.sqrt (x ^ 2 + x + b))

private theorem normalized_denominator_tendsto (a b : ℝ) :
    Tendsto (fun n : ℕ =>
      denominator a b ((n + 1 : ℕ) : ℝ) /
        Real.rpow (((n + 1 : ℕ) : ℝ)) (3 / 2 : ℝ))
      atTop (nhds 4) := by
  let x : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)
  let Q : ℕ → ℝ := fun n => (x n) ^ 2 + x n + b
  have hxpos : ∀ n, 0 < x n := by
    intro n
    dsimp only [x]
    positivity
  have hxtop : Tendsto x atTop atTop := by
    simpa [x, Nat.cast_add] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop)
  have hinv : Tendsto (fun n => (x n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hxtop
  have hA : Tendsto (fun n => (x n + a) / x n) atTop (nhds 1) := by
    have hsmall : Tendsto (fun n => a * (x n)⁻¹) atTop (nhds 0) :=
      by simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (nhds a)).mul hinv)
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have h := hone.add hsmall
    have h' : Tendsto (fun n => 1 + a * (x n)⁻¹) atTop (nhds 1) := by
      simpa using h
    apply h'.congr'
    filter_upwards [] with n
    have hxne := (hxpos n).ne'
    field_simp [hxne]
  have hQ : Tendsto (fun n => Q n / (x n) ^ 2) atTop (nhds 1) := by
    have hinv2 : Tendsto (fun n => ((x n)⁻¹) ^ 2) atTop (nhds 0) := by
      simpa using hinv.pow 2
    have hbsmall : Tendsto (fun n => b * ((x n)⁻¹) ^ 2) atTop (nhds 0) :=
      by simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => b) atTop (nhds b)).mul hinv2)
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have h := (hone.add hinv).add hbsmall
    have h' : Tendsto (fun n => 1 + (x n)⁻¹ + b * ((x n)⁻¹) ^ 2)
        atTop (nhds 1) := by
      simpa using h
    apply h'.congr'
    filter_upwards [] with n
    have hxne := (hxpos n).ne'
    dsimp only [Q]
    field_simp [hxne]
  obtain ⟨N, hgood⟩ := gap2 a b
  have hEventuallyGood : ∀ᶠ n : ℕ in atTop,
      0 < x n + a ∧ 0 < Q n := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hg := hgood (n + 1) (by omega)
    simpa [x, Q] using hg
  have hrootA : Tendsto (fun n => Real.sqrt (x n + a) / Real.sqrt (x n))
      atTop (nhds 1) := by
    have h := hA.rpow_const (p := (1 / 2 : ℝ)) (Or.inl one_ne_zero)
    have h' : Tendsto (fun n => Real.rpow ((x n + a) / x n) (1 / 2 : ℝ))
        atTop (nhds 1) := by
      norm_num at h ⊢
      exact h
    apply h'.congr'
    filter_upwards [hEventuallyGood] with n hn
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    exact Real.div_rpow hn.1.le (hxpos n).le (1 / 2 : ℝ)
  have hfourth : Tendsto (fun n => fourthRoot (Q n) / Real.sqrt (x n))
      atTop (nhds 1) := by
    have h := hQ.rpow_const (p := (1 / 4 : ℝ)) (Or.inl one_ne_zero)
    have h' : Tendsto (fun n => Real.rpow (Q n / (x n) ^ 2) (1 / 4 : ℝ))
        atTop (nhds 1) := by
      norm_num at h ⊢
      exact h
    apply h'.congr'
    filter_upwards [hEventuallyGood] with n hn
    have hx := hxpos n
    have hsq : Real.rpow ((x n) ^ 2) (1 / 4 : ℝ) = Real.sqrt (x n) := by
      calc
        Real.rpow ((x n) ^ 2) (1 / 4 : ℝ) =
            Real.rpow (Real.rpow (x n) (2 : ℝ)) (1 / 4 : ℝ) := by
          congr 1
          simpa using (Real.rpow_natCast (x n) 2).symm
        _ = Real.rpow (x n) ((2 : ℝ) * (1 / 4 : ℝ)) :=
          (Real.rpow_mul hx.le (2 : ℝ) (1 / 4 : ℝ)).symm
        _ = Real.sqrt (x n) := by norm_num [Real.sqrt_eq_rpow]
    unfold fourthRoot
    calc
      Real.rpow (Q n / (x n) ^ 2) (1 / 4 : ℝ) =
          Real.rpow (Q n) (1 / 4 : ℝ) /
            Real.rpow ((x n) ^ 2) (1 / 4 : ℝ) :=
        Real.div_rpow hn.2.le (sq_nonneg (x n)) (1 / 4 : ℝ)
      _ = Real.rpow (Q n) (1 / 4 : ℝ) / Real.sqrt (x n) := by
        rw [hsq]
  have hsqrtQ : Tendsto (fun n => Real.sqrt (Q n) / x n)
      atTop (nhds 1) := by
    have h := hQ.rpow_const (p := (1 / 2 : ℝ)) (Or.inl one_ne_zero)
    have h' : Tendsto (fun n => Real.rpow (Q n / (x n) ^ 2) (1 / 2 : ℝ))
        atTop (nhds 1) := by
      norm_num at h ⊢
      exact h
    apply h'.congr'
    filter_upwards [hEventuallyGood] with n hn
    have hx := hxpos n
    have hsq : Real.rpow ((x n) ^ 2) (1 / 2 : ℝ) = x n := by
      calc
        Real.rpow ((x n) ^ 2) (1 / 2 : ℝ) =
            Real.rpow (Real.rpow (x n) (2 : ℝ)) (1 / 2 : ℝ) := by
          congr 1
          simpa using (Real.rpow_natCast (x n) 2).symm
        _ = Real.rpow (x n) ((2 : ℝ) * (1 / 2 : ℝ)) :=
          (Real.rpow_mul hx.le (2 : ℝ) (1 / 2 : ℝ)).symm
        _ = x n := by norm_num
    rw [Real.sqrt_eq_rpow]
    calc
      Real.rpow (Q n / (x n) ^ 2) (1 / 2 : ℝ) =
          Real.rpow (Q n) (1 / 2 : ℝ) /
            Real.rpow ((x n) ^ 2) (1 / 2 : ℝ) :=
        Real.div_rpow hn.2.le (sq_nonneg (x n)) (1 / 2 : ℝ)
      _ = Real.rpow (Q n) (1 / 2 : ℝ) / x n := by rw [hsq]
  have hfirst : Tendsto (fun n =>
      (Real.sqrt (x n + a) + fourthRoot (Q n)) / Real.sqrt (x n))
      atTop (nhds 2) := by
    have h := hrootA.add hfourth
    convert h using 1
    · funext n
      have hsne : Real.sqrt (x n) ≠ 0 := (Real.sqrt_pos.2 (hxpos n)).ne'
      field_simp [hsne]
    · norm_num
  have hsecond : Tendsto (fun n =>
      (x n + a + Real.sqrt (Q n)) / x n) atTop (nhds 2) := by
    have h := hA.add hsqrtQ
    convert h using 1
    · funext n
      have hxne := (hxpos n).ne'
      field_simp [hxne]
    · norm_num
  have hprod := hfirst.mul hsecond
  have hprod' : Tendsto (fun n =>
      (Real.sqrt (x n + a) + fourthRoot (Q n)) / Real.sqrt (x n) *
        ((x n + a + Real.sqrt (Q n)) / x n)) atTop (nhds 4) := by
    norm_num at hprod ⊢
    exact hprod
  apply hprod'.congr'
  filter_upwards [hEventuallyGood] with n hn
  have hx := hxpos n
  have hsqrtne : Real.sqrt (x n) ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hrpow : Real.rpow (x n) (3 / 2 : ℝ) = Real.sqrt (x n) * x n := by
    calc
      Real.rpow (x n) (3 / 2 : ℝ) =
          Real.rpow (x n) ((1 / 2 : ℝ) + 1) := by norm_num
      _ = Real.rpow (x n) (1 / 2 : ℝ) * Real.rpow (x n) 1 :=
        Real.rpow_add hx (1 / 2 : ℝ) 1
      _ = Real.sqrt (x n) * x n := by
        rw [Real.sqrt_eq_rpow]
        congr 1
        exact Real.rpow_one (x n)
  dsimp only [denominator]
  rw [show (x n) ^ 2 + x n + b = Q n by rfl, hrpow]
  field_simp [hsqrtne, hx.ne']
  rfl

theorem gap3 (a b : ℝ) (ha : a = 1 / 2) :
    Tendsto
      (fun n : ℕ => term a b (n + 1) / comparisonThreeHalves (n + 1))
      atTop (nhds ((a ^ 2 - b) / 4)) := by
  have hD := normalized_denominator_tendsto a b
  have hlim : Tendsto (fun n : ℕ =>
      (a ^ 2 - b) /
        (denominator a b (((n + 1 : ℕ) : ℝ)) /
          Real.rpow (((n + 1 : ℕ) : ℝ)) (3 / 2 : ℝ)))
      atTop (nhds ((a ^ 2 - b) / 4)) := by
    exact tendsto_const_nhds.div hD (by norm_num)
  obtain ⟨N, hgood⟩ := gap2 a b
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have hg := hgood (n + 1) (by omega)
  have hxpos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hterm := gap1 a b (n + 1) (by simpa [Nat.cast_add] using hg.1)
    (by simpa [Nat.cast_add] using hg.2)
  have hDpos : 0 < denominator a b (((n + 1 : ℕ) : ℝ)) := by
    unfold denominator
    exact mul_pos
      (add_pos (Real.sqrt_pos.2 (by simpa [Nat.cast_add] using hg.1))
        (Real.rpow_pos_of_pos (by simpa [Nat.cast_add] using hg.2) _))
      (add_pos (by simpa [Nat.cast_add] using hg.1)
        (Real.sqrt_pos.2 (by simpa [Nat.cast_add] using hg.2)))
  have hrpowne : Real.rpow (((n + 1 : ℕ) : ℝ)) (3 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hxpos _).ne'
  rw [hterm]
  unfold comparisonThreeHalves rationalized
  rw [ha]
  change
    (((1 / 2 : ℝ) ^ 2 - b) /
        (denominator (1 / 2) b (((n + 1 : ℕ) : ℝ)) /
          Real.rpow (((n + 1 : ℕ) : ℝ)) (3 / 2 : ℝ))) =
      (((2 * (1 / 2 : ℝ) - 1) * (((n + 1 : ℕ) : ℝ)) +
          (1 / 2 : ℝ) ^ 2 - b) /
        denominator (1 / 2) b (((n + 1 : ℕ) : ℝ))) /
          (1 / Real.rpow (((n + 1 : ℕ) : ℝ)) (3 / 2 : ℝ))
  field_simp [hDpos.ne', hrpowne]
  ring

theorem gap4 :
    Summable (fun n : ℕ => comparisonThreeHalves (n + 1)) := by
  have hall : Summable (fun n : ℕ => 1 / Real.rpow n (3 / 2 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  exact (summable_nat_add_iff 1).mpr hall

theorem gap5 (a b : ℝ) (ha : a = 1 / 2) :
    converges a b := by
  have hratio := gap3 a b ha
  have hO : (fun n : ℕ => term a b (n + 1)) =O[atTop]
      (fun n : ℕ => comparisonThreeHalves (n + 1)) := by
    refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ ((a ^ 2 - b) / 4) hratio
    filter_upwards [] with n hzero
    unfold comparisonThreeHalves at hzero
    have hbase : 0 < (((n + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos n
    have hpos : 0 < Real.rpow (((n + 1 : ℕ) : ℝ)) (3 / 2 : ℝ) :=
      Real.rpow_pos_of_pos hbase _
    exact False.elim ((one_div_ne_zero hpos.ne') hzero)
  unfold converges
  exact summable_of_isBigO_nat gap4 hO

theorem gap6 (a b : ℝ) (ha : a ≠ 1 / 2) :
    Tendsto
      (fun n : ℕ => term a b (n + 1) / comparisonHalf (n + 1))
      atTop (nhds ((2 * a - 1) / 4)) := by
  let x : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)
  have hxtop : Tendsto x atTop atTop := by
    simpa [x, Nat.cast_add] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop)
  have hinv : Tendsto (fun n => (x n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hxtop
  have hsmall : Tendsto (fun n => (a ^ 2 - b) * (x n)⁻¹)
      atTop (nhds 0) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => a ^ 2 - b)
        atTop (nhds (a ^ 2 - b))).mul hinv)
  have hnum : Tendsto (fun n =>
      ((2 * a - 1) * x n + a ^ 2 - b) / x n)
      atTop (nhds (2 * a - 1)) := by
    have hc : Tendsto (fun _ : ℕ => 2 * a - 1) atTop (nhds (2 * a - 1)) :=
      tendsto_const_nhds
    have h := hc.add hsmall
    have h' : Tendsto (fun n => 2 * a - 1 + (a ^ 2 - b) * (x n)⁻¹)
        atTop (nhds (2 * a - 1)) := by
      simpa using h
    apply h'.congr'
    filter_upwards [] with n
    have hxpos : 0 < x n := by dsimp [x]; positivity
    field_simp [hxpos.ne']
    ring
  have hD := normalized_denominator_tendsto a b
  have hlim : Tendsto (fun n =>
      (((2 * a - 1) * x n + a ^ 2 - b) / x n) /
        (denominator a b (x n) / Real.rpow (x n) (3 / 2 : ℝ)))
      atTop (nhds ((2 * a - 1) / 4)) := by
    simpa [x] using hnum.div hD (by norm_num : (4 : ℝ) ≠ 0)
  obtain ⟨N, hgood⟩ := gap2 a b
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have hg := hgood (n + 1) (by omega)
  have hxpos : 0 < x n := by dsimp [x]; positivity
  have hterm := gap1 a b (n + 1) (by simpa [x, Nat.cast_add] using hg.1)
    (by simpa [x, Nat.cast_add] using hg.2)
  have hDpos : 0 < denominator a b (x n) := by
    unfold denominator
    exact mul_pos
      (add_pos (Real.sqrt_pos.2 (by simpa [x, Nat.cast_add] using hg.1))
        (Real.rpow_pos_of_pos (by simpa [x, Nat.cast_add] using hg.2) _))
      (add_pos (by simpa [x, Nat.cast_add] using hg.1)
        (Real.sqrt_pos.2 (by simpa [x, Nat.cast_add] using hg.2)))
  have hsqrtpos : 0 < Real.sqrt (x n) := Real.sqrt_pos.2 hxpos
  have hrpowne : Real.rpow (x n) (3 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hxpos _).ne'
  have hrpow : Real.rpow (x n) (3 / 2 : ℝ) = Real.sqrt (x n) * x n := by
    calc
      Real.rpow (x n) (3 / 2 : ℝ) =
          Real.rpow (x n) ((1 / 2 : ℝ) + 1) := by norm_num
      _ = Real.rpow (x n) (1 / 2 : ℝ) * Real.rpow (x n) 1 :=
        Real.rpow_add hxpos (1 / 2 : ℝ) 1
      _ = Real.sqrt (x n) * x n := by
        rw [Real.sqrt_eq_rpow]
        congr 1
        exact Real.rpow_one (x n)
  rw [hterm]
  unfold comparisonHalf rationalized
  change
    ((((2 * a - 1) * x n + a ^ 2 - b) / x n) /
        (denominator a b (x n) / Real.rpow (x n) (3 / 2 : ℝ))) =
      (((2 * a - 1) * x n + a ^ 2 - b) / denominator a b (x n)) /
        (1 / Real.sqrt (x n))
  rw [hrpow]
  field_simp [hDpos.ne', hsqrtpos.ne', hxpos.ne']

theorem gap7 (a : ℝ) (ha : a ≠ 1 / 2) :
    (2 * a - 1) / 4 ≠ 0 := by
  intro h
  have : 2 * a - 1 = 0 := by
    apply (div_eq_zero_iff).mp h |>.resolve_right
    norm_num
  apply ha
  linarith

theorem gap8 (a b : ℝ) (ha : a ≠ 1 / 2) :
    ∃ L ≠ 0,
      Tendsto
        (fun n : ℕ => term a b (n + 1) / comparisonHalf (n + 1))
        atTop (nhds L) := by
  exact ⟨(2 * a - 1) / 4, gap7 a ha, gap6 a b ha⟩

theorem gap9 :
    ¬ Summable (fun n : ℕ => comparisonHalf (n + 1)) := by
  intro hshift
  have hall : Summable comparisonHalf := (summable_nat_add_iff 1).mp hshift
  change Summable (fun n : ℕ => 1 / Real.sqrt (n : ℝ)) at hall
  have hrpow : Summable (fun n : ℕ => 1 / Real.rpow n (1 / 2 : ℝ)) := by
    simpa only [Real.sqrt_eq_rpow] using hall
  have hp := Real.summable_one_div_nat_rpow.mp hrpow
  norm_num at hp

theorem gap10 (a b : ℝ) (ha : a ≠ 1 / 2) :
    ¬ converges a b := by
  let L : ℝ := (2 * a - 1) / 4
  have hL : L ≠ 0 := gap7 a ha
  have hratio : Tendsto
      (fun n : ℕ => term a b (n + 1) / comparisonHalf (n + 1))
      atTop (nhds L) := by
    simpa [L] using gap6 a b ha
  have hratioNe : ∀ᶠ n : ℕ in atTop,
      term a b (n + 1) / comparisonHalf (n + 1) ≠ 0 :=
    hratio.eventually (eventually_ne_nhds hL)
  have hcompNe : ∀ n : ℕ, comparisonHalf (n + 1) ≠ 0 := by
    intro n
    unfold comparisonHalf
    have hbase : 0 < (((n + 1 : ℕ) : ℝ)) := by exact_mod_cast Nat.succ_pos n
    exact one_div_ne_zero (Real.sqrt_pos.2 hbase).ne'
  have htermNe : ∀ᶠ n : ℕ in atTop, term a b (n + 1) ≠ 0 := by
    filter_upwards [hratioNe] with n hn
    exact (div_ne_zero_iff.mp hn).1
  have hinv := hratio.inv₀ hL
  have hrev : Tendsto
      (fun n : ℕ => comparisonHalf (n + 1) / term a b (n + 1))
      atTop (nhds L⁻¹) := by
    apply hinv.congr'
    filter_upwards [htermNe] with n htn
    have hcn := hcompNe n
    field_simp [htn, hcn]
  have hO : (fun n : ℕ => comparisonHalf (n + 1)) =O[atTop]
      (fun n : ℕ => term a b (n + 1)) := by
    refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ L⁻¹ hrev
    filter_upwards [htermNe] with n htn hzero
    exact False.elim (htn hzero)
  intro hconv
  apply gap9
  unfold converges at hconv
  exact summable_of_isBigO_nat hconv hO

theorem gap11 (a b : ℝ) :
    (a, b) ∈ {z : ℝ × ℝ | z.1 = 1 / 2} ↔ converges a b := by
  simp only [Set.mem_setOf_eq, Prod.fst]
  constructor
  · intro ha
    exact gap5 a b ha
  · intro hconv
    by_contra ha
    exact (gap10 a b ha) hconv

end

end ProofGap.Exercise2627
