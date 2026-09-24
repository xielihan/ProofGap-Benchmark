import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Stirling

namespace ProofGap.Exercise2600

noncomputable section

def term (p : ℝ) (n : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) * Real.exp n /
    Real.rpow n ((n : ℝ) + p)

def rawRatio (p : ℝ) (n : ℕ) : ℝ :=
  term p n / term p (n + 1)

def simplifiedRatio (p : ℝ) (n : ℕ) : ℝ :=
  (1 / Real.exp 1) *
    Real.rpow (((n : ℝ) + 1) / n) ((n : ℝ) + p)

def raabeQuantity (p : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * (rawRatio p n - 1)

def normalizedIncrement (p : ℝ) (n : ℕ) : ℝ :=
  (simplifiedRatio p n - 1) / (1 / (n : ℝ))

def continuousQuotient (p x : ℝ) : ℝ :=
  ((1 / Real.exp 1) * Real.rpow (1 + x) (1 / x + p) - 1) / x

def exponentialQuotient (p x : ℝ) : ℝ :=
  ((1 / Real.exp 1) *
      Real.exp ((1 / x + p) * Real.log (1 + x)) - 1) / x

private theorem term_eq_stirling (p : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    term p n = Real.sqrt 2 * Stirling.stirlingSeq n *
      Real.rpow n (1 / 2 - p) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfactorial : (Nat.factorial n : ℝ) =
      Stirling.stirlingSeq n *
        (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) := by
    rw [Stirling.stirlingSeq]
    field_simp
  have hexp : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
    simpa using Real.exp_nat_mul 1 n
  have hden : Real.rpow n ((n : ℝ) + p) =
      (n : ℝ) ^ n * Real.rpow n p := by
    calc
      Real.rpow n ((n : ℝ) + p) =
          Real.rpow n (n : ℝ) * Real.rpow n p :=
        Real.rpow_add hnpos (n : ℝ) p
      _ = (n : ℝ) ^ n * Real.rpow n p := by
        congr 1
        exact Real.rpow_natCast (n : ℝ) n
  have hsqrt : Real.sqrt (2 * (n : ℝ)) =
      Real.sqrt 2 * Real.rpow n (1 / 2) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    exact Real.sqrt_eq_rpow (n : ℝ)
  have hrpow : Real.rpow n (1 / 2 - p) =
      Real.rpow n (1 / 2) / Real.rpow n p :=
    Real.rpow_sub hnpos (1 / 2) p
  unfold term
  rw [hfactorial, hexp, hden, hsqrt, hrpow]
  have hn_ne : (n : ℝ) ≠ 0 := hnpos.ne'
  have he_ne : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  rw [div_pow]
  field_simp

private theorem stirlingSeq_le_one_value (n : ℕ) (hn : 1 ≤ n) :
    Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
  have hanti := Stirling.stirlingSeq'_antitone (Nat.zero_le (n - 1))
  simpa [Function.comp_def, Nat.sub_add_cancel hn] using hanti

private theorem summable_term_of_three_halves_lt (p : ℝ) (hp : 3 / 2 < p) :
    Summable (term p) := by
  let e : ℝ := 1 / 2 - p
  let C : ℝ := Real.sqrt 2 * Stirling.stirlingSeq 1
  have hpseries : Summable (fun n : ℕ ↦ Real.rpow (n : ℝ) e) :=
    Real.summable_nat_rpow.mpr (by dsimp [e]; linarith)
  have hmajorant : Summable (fun n : ℕ ↦
      C * Real.rpow ((n + 1 : ℕ) : ℝ) e) :=
    ((summable_nat_add_iff 1).mpr hpseries).mul_left C
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_nonneg_of_le (f := fun n : ℕ ↦
    C * Real.rpow ((n + 1 : ℕ) : ℝ) e)
  · intro n
    unfold term
    apply div_nonneg
    · positivity
    · exact Real.rpow_nonneg (by positivity) _
  · intro n
    have hn : 1 ≤ n + 1 := by omega
    rw [term_eq_stirling p (n + 1) hn]
    dsimp [C, e]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (stirlingSeq_le_one_value (n + 1) hn)
        (Real.sqrt_nonneg 2))
      (Real.rpow_nonneg (by positivity) _)
  · exact hmajorant

private theorem three_halves_lt_of_summable (p : ℝ) (hsum : Summable (term p)) :
    3 / 2 < p := by
  by_contra hp
  have hp_le : p ≤ 3 / 2 := le_of_not_gt hp
  let e : ℝ := 1 / 2 - p
  let c : ℝ := Real.sqrt 2 * Real.sqrt Real.pi
  have hcpos : 0 < c := mul_pos (Real.sqrt_pos.2 (by norm_num))
    (Real.sqrt_pos.2 Real.pi_pos)
  have hshift : Summable (fun n : ℕ ↦ term p (n + 1)) :=
    (summable_nat_add_iff 1).mpr hsum
  have hminorant : Summable (fun n : ℕ ↦
      c * Real.rpow ((n + 1 : ℕ) : ℝ) e) := by
    apply Summable.of_nonneg_of_le (f := fun n : ℕ ↦ term p (n + 1))
    · intro n
      exact mul_nonneg hcpos.le (Real.rpow_nonneg (by positivity) _)
    · intro n
      have hn : 1 ≤ n + 1 := by omega
      rw [term_eq_stirling p (n + 1) hn]
      dsimp [c, e]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Stirling.sqrt_pi_le_stirlingSeq (by omega))
          (Real.sqrt_nonneg 2))
        (Real.rpow_nonneg (by positivity) _)
    · exact hshift
  have hpShift : Summable (fun n : ℕ ↦
      Real.rpow ((n + 1 : ℕ) : ℝ) e) :=
    (summable_mul_left_iff hcpos.ne').mp hminorant
  have hpAll : Summable (fun n : ℕ ↦ Real.rpow (n : ℝ) e) :=
    (summable_nat_add_iff 1).mp hpShift
  have hexponent := Real.summable_nat_rpow.mp hpAll
  dsimp [e] at hexponent
  linarith

theorem gap1
    (a : ℕ → ℝ) (p : ℝ)
    (ha : ∀ n, a n = term p n) :
    ∀ n, a n / a (n + 1) = rawRatio p n := by
  intro n
  simp [rawRatio, ha]

theorem gap2 (p : ℝ) :
    ∀ n : ℕ, 1 ≤ n → rawRatio p n = simplifiedRatio p n := by
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1pos : (0 : ℝ) < n + 1 := by positivity
  have hexp : Real.exp ((n : ℝ) + 1) = Real.exp n * Real.exp 1 := by
    rw [Real.exp_add]
  have hrpowSucc : Real.rpow ((n : ℝ) + 1) ((n : ℝ) + 1 + p) =
      ((n : ℝ) + 1) * Real.rpow ((n : ℝ) + 1) (n + p) := by
    convert Real.rpow_add hn1pos 1 ((n : ℝ) + p) using 1 <;>
      simp [Real.rpow_one, add_assoc, add_comm]
  have hrpowDiv : Real.rpow (((n : ℝ) + 1) / n) ((n : ℝ) + p) =
      Real.rpow ((n : ℝ) + 1) ((n : ℝ) + p) /
        Real.rpow n ((n : ℝ) + p) := by
    exact Real.div_rpow hn1pos.le hnpos.le _
  unfold rawRatio term simplifiedRatio
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    hexp, hrpowSucc, hrpowDiv]
  field_simp [hnpos.ne', hn1pos.ne', Real.exp_ne_zero]

theorem gap3
    (a : ℕ → ℝ) (p : ℝ)
    (ha : ∀ n, a n = term p n)
    (hsimplify : ∀ n : ℕ, 1 ≤ n →
      rawRatio p n = simplifiedRatio p n) :
    ∀ n : ℕ, 1 ≤ n →
      a n / a (n + 1) = simplifiedRatio p n := by
  intro n hn
  rw [ha n, ha (n + 1)]
  exact hsimplify n hn

theorem gap4 (p : ℝ) :
    ∀ n : ℕ, 1 ≤ n →
      raabeQuantity p n = normalizedIncrement p n := by
  intro n hn
  unfold raabeQuantity normalizedIncrement
  rw [gap2 p n hn]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp

theorem gap5
    (p L : ℝ)
    (hcontinuous : Tendsto (continuousQuotient p)
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds L)) :
    Tendsto (normalizedIncrement p) atTop (nhds L) := by
  have hinv : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_one_div_atTop_nhds_zero_nat,
      Filter.eventually_atTop.2 ⟨1, fun n hn ↦ by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using
          (show (1 / (n : ℝ)) ≠ 0 by positivity)⟩⟩
  apply (hcontinuous.comp hinv).congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  unfold normalizedIncrement continuousQuotient simplifiedRatio
  have hbase : ((n : ℝ) + 1) / n = 1 + 1 / (n : ℝ) := by
    field_simp
  have hexponent : (n : ℝ) + p = 1 / (1 / (n : ℝ)) + p := by
    field_simp
  rw [hbase, hexponent]
  rfl

theorem gap6
    (p L : ℝ)
    (hraabe : ∀ n : ℕ, 1 ≤ n →
      raabeQuantity p n = normalizedIncrement p n)
    (hcontinuous : Tendsto (continuousQuotient p)
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds L)) :
    Tendsto (raabeQuantity p) atTop (nhds L) := by
  apply (gap5 p L hcontinuous).congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact (hraabe n hn).symm

theorem gap7 (p : ℝ) :
    ∀ x : ℝ, -1 < x → x ≠ 0 →
      continuousQuotient p x = exponentialQuotient p x := by
  intro x hx hx0
  unfold continuousQuotient exponentialQuotient
  have hpow : Real.rpow (1 + x) (1 / x + p) =
      Real.exp ((1 / x + p) * Real.log (1 + x)) := by
    calc
      Real.rpow (1 + x) (1 / x + p) =
          Real.exp (Real.log (1 + x) * (1 / x + p)) :=
        Real.rpow_def_of_pos (by linarith : 0 < 1 + x) _
      _ = Real.exp ((1 / x + p) * Real.log (1 + x)) := by
        congr 1
        ring
  rw [hpow]

private theorem tendsto_log_remainder :
    Tendsto (fun x : ℝ =>
      (x - (1 + x) * Real.log (1 + x)) / (x ^ 2 * (1 + x)))
      (nhdsWithin 0 (Set.compl {0} : Set ℝ)) (nhds (-1 / 2)) := by
  have hsecondLimit :
      Tendsto (fun x : ℝ => (-1 / (1 + x)) / (2 + 6 * x))
        (nhdsWithin 0 (Set.compl {0} : Set ℝ)) (nhds (-1 / 2)) := by
    have h : ContinuousAt (fun x : ℝ =>
        (-1 / (1 + x)) / (2 + 6 * x)) 0 := by
      fun_prop (disch := norm_num)
    convert h.tendsto.mono_left inf_le_left using 1 <;> norm_num
  have hnum2Deriv :
      Filter.Eventually (fun x : ℝ =>
        HasDerivAt (fun y : ℝ => -Real.log (1 + y))
          (-1 / (1 + x)) x) (nhdsWithin 0 (Set.compl {0} : Set ℝ)) := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num))] with x hx
    have hx1 : Not (1 + x = 0) := by intro h; linarith
    convert (((hasDerivAt_const x 1).add (hasDerivAt_id x)).log hx1).neg using 1 <;>
      simp [id_eq, div_eq_mul_inv]
  have hden2Deriv :
      Filter.Eventually (fun x : ℝ =>
        HasDerivAt (fun y : ℝ => y * (2 + 3 * y)) (2 + 6 * x) x)
        (nhdsWithin 0 (Set.compl {0} : Set ℝ)) := by
    filter_upwards [] with x
    convert (hasDerivAt_id x).mul
      ((hasDerivAt_const x 2).add
        ((hasDerivAt_const x 3).mul (hasDerivAt_id x))) using 1 <;>
      simp [id_eq]
    ring
  have hden2Ne :
      Filter.Eventually (fun x : ℝ => Not (2 + 6 * x = 0))
        (nhdsWithin 0 (Set.compl {0} : Set ℝ)) := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (Ioi_mem_nhds (show (-1 / 4 : ℝ) < 0 by norm_num))] with x hx
    have hpos : 0 < 2 + 6 * x := by linarith
    exact hpos.ne'
  have hnum2Zero :
      Tendsto (fun x : ℝ => -Real.log (1 + x))
        (nhdsWithin 0 (Set.compl {0} : Set ℝ)) (nhds 0) := by
    have h : ContinuousAt (fun x : ℝ => -Real.log (1 + x)) 0 := by
      fun_prop (disch := norm_num)
    simpa using h.tendsto.mono_left inf_le_left
  have hden2Zero :
      Tendsto (fun x : ℝ => x * (2 + 3 * x))
        (nhdsWithin 0 (Set.compl {0} : Set ℝ)) (nhds 0) := by
    have h : ContinuousAt (fun x : ℝ => x * (2 + 3 * x)) 0 := by fun_prop
    simpa using h.tendsto.mono_left inf_le_left
  have hfirstLimit :
      Tendsto (fun x : ℝ =>
        (-Real.log (1 + x)) / (x * (2 + 3 * x)))
        (nhdsWithin 0 (Set.compl {0} : Set ℝ)) (nhds (-1 / 2)) :=
    HasDerivAt.lhopital_zero_nhdsNE hnum2Deriv hden2Deriv hden2Ne
      hnum2Zero hden2Zero hsecondLimit
  have hnum1Deriv :
      Filter.Eventually (fun x : ℝ =>
        HasDerivAt (fun y : ℝ =>
          y - (1 + y) * Real.log (1 + y)) (-Real.log (1 + x)) x)
        (nhdsWithin 0 (Set.compl {0} : Set ℝ)) := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num))] with x hx
    have hx1 : Not (1 + x = 0) := by intro h; linarith
    convert (hasDerivAt_id x).sub
      (((hasDerivAt_const x 1).add (hasDerivAt_id x)).mul
        (((hasDerivAt_const x 1).add (hasDerivAt_id x)).log hx1)) using 1 <;>
      simp [id_eq]
    field_simp [hx1]
    <;> ring
  have hden1Deriv :
      Filter.Eventually (fun x : ℝ =>
        HasDerivAt (fun y : ℝ => y ^ 2 * (1 + y))
          (x * (2 + 3 * x)) x)
        (nhdsWithin 0 (Set.compl {0} : Set ℝ)) := by
    filter_upwards [] with x
    convert ((hasDerivAt_id x).pow 2).mul
      ((hasDerivAt_const x 1).add (hasDerivAt_id x)) using 1 <;>
      simp [id_eq]
    ring
  have hden1Ne :
      Filter.Eventually (fun x : ℝ => Not (x * (2 + 3 * x) = 0))
        (nhdsWithin 0 (Set.compl {0} : Set ℝ)) := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (Ioi_mem_nhds (show (-1 / 2 : ℝ) < 0 by norm_num))] with x hx0 hx
    have hxne : Not (x = 0) := by
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hx0
    have hpos : 0 < 2 + 3 * x := by linarith
    exact mul_ne_zero hxne hpos.ne'
  have hnum1Zero :
      Tendsto (fun x : ℝ => x - (1 + x) * Real.log (1 + x))
        (nhdsWithin 0 (Set.compl {0} : Set ℝ)) (nhds 0) := by
    have h : ContinuousAt (fun x : ℝ =>
        x - (1 + x) * Real.log (1 + x)) 0 := by
      fun_prop (disch := norm_num)
    simpa using h.tendsto.mono_left inf_le_left
  have hden1Zero :
      Tendsto (fun x : ℝ => x ^ 2 * (1 + x))
        (nhdsWithin 0 (Set.compl {0} : Set ℝ)) (nhds 0) := by
    have h : ContinuousAt (fun x : ℝ => x ^ 2 * (1 + x)) 0 := by fun_prop
    simpa using h.tendsto.mono_left inf_le_left
  exact HasDerivAt.lhopital_zero_nhdsNE hnum1Deriv hden1Deriv hden1Ne
    hnum1Zero hden1Zero hfirstLimit

theorem gap8 (p : ℝ) :
    Tendsto (exponentialQuotient p)
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds (p - 1 / 2)) := by
  let S : Set ℝ := Set.compl {0}
  have hlogDeriv :
      Filter.Eventually (fun x : ℝ =>
        HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x)
        (nhdsWithin 0 S) := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num))] with x hx
    have hx1 : Not (1 + x = 0) := by intro h; linarith
    convert ((hasDerivAt_const x 1).add (hasDerivAt_id x)).log hx1 using 1 <;>
      simp [id_eq]
  have hidDeriv :
      Filter.Eventually (fun x : ℝ =>
        HasDerivAt (fun y : ℝ => y) 1 x) (nhdsWithin 0 S) := by
    filter_upwards [] with x
    simpa only [id_eq] using hasDerivAt_id x
  have honeNe : Filter.Eventually (fun _ : ℝ => Not ((1 : ℝ) = 0))
      (nhdsWithin 0 S) := Filter.Eventually.of_forall (fun _ => one_ne_zero)
  have hlogZero :
      Tendsto (fun x : ℝ => Real.log (1 + x))
        (nhdsWithin 0 S) (nhds 0) := by
    have h : ContinuousAt (fun x : ℝ => Real.log (1 + x)) 0 := by
      fun_prop (disch := norm_num)
    simpa using h.tendsto.mono_left inf_le_left
  have hidZero : Tendsto (fun x : ℝ => x) (nhdsWithin 0 S) (nhds 0) := by
    simpa only [id_eq] using (continuousAt_id.tendsto.mono_left inf_le_left)
  have hinvOneLimit : Tendsto (fun x : ℝ => 1 / (1 + x))
      (nhdsWithin 0 S) (nhds 1) := by
    have h : ContinuousAt (fun x : ℝ => 1 / (1 + x)) 0 := by
      fun_prop (disch := norm_num)
    convert h.tendsto.mono_left inf_le_left using 1 <;> norm_num
  have hlogDiv : Tendsto (fun x : ℝ => Real.log (1 + x) / x)
      (nhdsWithin 0 S) (nhds 1) :=
    HasDerivAt.lhopital_zero_nhdsNE hlogDeriv hidDeriv honeNe
      hlogZero hidZero (by simpa only [div_one] using hinvOneLimit)
  have hsum : Tendsto (fun x : ℝ =>
      Real.log (1 + x) / x + p * Real.log (1 + x))
      (nhdsWithin 0 S) (nhds 1) := by
    simpa using hlogDiv.add (Filter.Tendsto.const_mul p hlogZero)
  have hinner :
      Tendsto (fun x : ℝ => (1 / x + p) * Real.log (1 + x))
        (nhdsWithin 0 S) (nhds 1) := by
    apply hsum.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx0
    have hx : Not (x = 0) := by
      simpa [S, Set.mem_compl_iff, Set.mem_singleton_iff] using hx0
    field_simp [hx]
  have hpDivLimit :
      Tendsto (fun x : ℝ => p / (1 + x))
        (nhdsWithin 0 S) (nhds p) := by
    have h : ContinuousAt (fun x : ℝ => p / (1 + x)) 0 := by
      fun_prop (disch := norm_num)
    convert h.tendsto.mono_left inf_le_left using 1 <;> norm_num
  have hrem :
      Tendsto (fun x : ℝ =>
        (x - (1 + x) * Real.log (1 + x)) / (x ^ 2 * (1 + x)))
        (nhdsWithin 0 S) (nhds (-1 / 2)) := by
    simpa [S] using tendsto_log_remainder
  have hqDerivLimit :
      Tendsto (fun x : ℝ =>
        (x - (1 + x) * Real.log (1 + x)) / (x ^ 2 * (1 + x)) +
          p / (1 + x)) (nhdsWithin 0 S) (nhds (p - 1 / 2)) := by
    convert hrem.add hpDivLimit using 1 <;> ring
  have hqDeriv :
      Filter.Eventually (fun x : ℝ =>
        HasDerivAt (fun y : ℝ => (1 / y + p) * Real.log (1 + y))
          ((x - (1 + x) * Real.log (1 + x)) / (x ^ 2 * (1 + x)) +
            p / (1 + x)) x) (nhdsWithin 0 S) := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num))] with x hx0 hxLower
    have hx : Not (x = 0) := by
      simpa [S, Set.mem_compl_iff, Set.mem_singleton_iff] using hx0
    have hx1 : Not (1 + x = 0) := by intro h; linarith
    have hleft : HasDerivAt (fun y : ℝ => 1 / y + p) (-1 / x ^ 2) x := by
      convert ((hasDerivAt_id x).inv hx).add_const p using 1 <;>
        simp [one_div, id_eq]
    have hright : HasDerivAt (fun y : ℝ => Real.log (1 + y))
        (1 / (1 + x)) x := by
      convert ((hasDerivAt_const x 1).add (hasDerivAt_id x)).log hx1 using 1 <;>
        simp [id_eq]
    convert hleft.mul hright using 1
    field_simp [hx, hx1]
    <;> ring
  have hexpInner :
      Tendsto (fun x : ℝ =>
        Real.exp ((1 / x + p) * Real.log (1 + x)))
        (nhdsWithin 0 S) (nhds (Real.exp 1)) :=
    (Real.continuous_exp.tendsto 1).comp hinner
  have hprefactor :
      Tendsto (fun x : ℝ =>
        (1 / Real.exp 1) * Real.exp ((1 / x + p) * Real.log (1 + x)))
        (nhdsWithin 0 S) (nhds 1) := by
    simpa [Real.exp_ne_zero] using
      Filter.Tendsto.const_mul (1 / Real.exp 1) hexpInner
  have hnumDeriv :
      Filter.Eventually (fun x : ℝ =>
        HasDerivAt (fun y : ℝ =>
          (1 / Real.exp 1) *
            Real.exp ((1 / y + p) * Real.log (1 + y)) - 1)
          (((1 / Real.exp 1) *
              Real.exp ((1 / x + p) * Real.log (1 + x))) *
            ((x - (1 + x) * Real.log (1 + x)) / (x ^ 2 * (1 + x)) +
              p / (1 + x))) x) (nhdsWithin 0 S) := by
    filter_upwards [hqDeriv] with x hx
    convert (hx.exp.const_mul (1 / Real.exp 1)).sub_const 1 using 1 <;> ring
  have hnumDerivLimit :
      Tendsto (fun x : ℝ =>
        ((1 / Real.exp 1) *
            Real.exp ((1 / x + p) * Real.log (1 + x))) *
          ((x - (1 + x) * Real.log (1 + x)) / (x ^ 2 * (1 + x)) +
            p / (1 + x))) (nhdsWithin 0 S) (nhds (p - 1 / 2)) := by
    simpa using hprefactor.mul hqDerivLimit
  have hnumZero :
      Tendsto (fun x : ℝ =>
        (1 / Real.exp 1) *
          Real.exp ((1 / x + p) * Real.log (1 + x)) - 1)
        (nhdsWithin 0 S) (nhds 0) := by
    convert hprefactor.sub_const 1 using 1 <;> norm_num
  have hquotientDerivLimit :
      Tendsto (fun x : ℝ =>
        (((1 / Real.exp 1) *
            Real.exp ((1 / x + p) * Real.log (1 + x))) *
          ((x - (1 + x) * Real.log (1 + x)) / (x ^ 2 * (1 + x)) +
            p / (1 + x))) / 1) (nhdsWithin 0 S) (nhds (p - 1 / 2)) := by
    simpa only [div_one] using hnumDerivLimit
  unfold exponentialQuotient
  exact HasDerivAt.lhopital_zero_nhdsNE hnumDeriv hidDeriv honeNe
    hnumZero hidZero hquotientDerivLimit

theorem gap9
    (p : ℝ)
    (hequality : ∀ x : ℝ, -1 < x → x ≠ 0 →
      continuousQuotient p x = exponentialQuotient p x)
    (hexp : Tendsto (exponentialQuotient p)
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds (p - 1 / 2))) :
    Tendsto (continuousQuotient p)
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds (p - 1 / 2)) := by
  apply hexp.congr'
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds (by norm_num : -1 < (0 : ℝ)))]
      with x hx0 hx
  exact (hequality x hx (by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hx0)).symm

theorem gap10
    (p : ℝ)
    (hraabe : Tendsto (raabeQuantity p) atTop (nhds (p - 1 / 2))) :
    p - 1 / 2 > 1 → Summable (term p) := by
  intro hp
  exact summable_term_of_three_halves_lt p (by linarith)

theorem gap11 (p : ℝ) :
    p - 1 / 2 > 1 ↔ p > 3 / 2 := by constructor <;> intro h <;> linarith

theorem gap12 (p : ℝ) :
    p > 3 / 2 ↔ Summable (term p) :=
  ⟨summable_term_of_three_halves_lt p, three_halves_lt_of_summable p⟩

end

end ProofGap.Exercise2600
