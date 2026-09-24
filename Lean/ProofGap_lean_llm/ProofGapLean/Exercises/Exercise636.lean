import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise636

noncomputable section

def angle (a : ℝ) (n k : ℕ) : ℝ :=
  (k : ℝ) * a / ((n : ℝ) * Real.sqrt n)
def productSeq (a : ℝ) (n : ℕ) : ℝ :=
  (Finset.Icc 1 n).prod (fun k => Real.cos (angle a n k))
def logProductSum (a : ℝ) (n : ℕ) : ℝ :=
  (Finset.Icc 1 n).sum (fun k => Real.log (Real.cos (angle a n k)))
def logTangentSum (a : ℝ) (n : ℕ) : ℝ :=
  (Finset.Icc 1 n).sum (fun k =>
    Real.log (1 + Real.tan (angle a n k) ^ 2))
def squareSum (a : ℝ) (n : ℕ) : ℝ :=
  (Finset.Icc 1 n).sum (fun k =>
    (k : ℝ) ^ 2 * a ^ 2 / (n : ℝ) ^ 3)

/-- Exercise 636, gap 1; restrict `k` to the product range. -/
private theorem sum_Icc_sq_real (n : ℕ) :
    (Finset.Icc 1 n).sum (fun k => (k : ℝ) ^ 2) =
      (n : ℝ) * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hset : Finset.Icc 1 (n + 1) =
          insert (n + 1) (Finset.Icc 1 n) := by
        ext k
        simp
        omega
      have hnot : n + 1 ∉ Finset.Icc 1 n := by simp
      rw [hset, Finset.sum_insert hnot, ih]
      push_cast
      ring

theorem gap1 (a : ℝ) :
    ∃ N, ∀ n ≥ N, ∀ k ∈ Finset.Icc 1 n,
      0 < Real.cos (angle a n k) := by
  obtain ⟨N, hN⟩ :=
    exists_nat_gt ((2 * |a| / Real.pi) ^ 2)
  refine ⟨N, ?_⟩
  intro n hn k hk
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnlarge : (2 * |a| / Real.pi) ^ 2 < (n : ℝ) :=
    lt_of_lt_of_le hN hNn
  have hn0 : 0 < (n : ℝ) := by
    nlinarith [sq_nonneg (2 * |a| / Real.pi)]
  have hsqrt0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hsqrt_sq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (le_of_lt hn0)
  have hb0 : 0 ≤ 2 * |a| / Real.pi := by
    exact div_nonneg
      (mul_nonneg (by norm_num) (abs_nonneg a))
      (le_of_lt Real.pi_pos)
  have hb_lt : 2 * |a| / Real.pi < Real.sqrt (n : ℝ) := by
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have habs_ratio : |a| / Real.sqrt (n : ℝ) < Real.pi / 2 := by
    apply (div_lt_iff₀ hsqrt0).2
    calc
      |a| = (Real.pi / 2) * (2 * |a| / Real.pi) := by
        field_simp [ne_of_gt Real.pi_pos]
      _ < (Real.pi / 2) * Real.sqrt (n : ℝ) := by
        exact mul_lt_mul_of_pos_left hb_lt (by positivity)
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hkn : (k : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hk).2
  have hangle : |angle a n k| ≤ |a| / Real.sqrt (n : ℝ) := by
    rw [angle, abs_div, abs_mul, abs_mul, abs_of_nonneg hk0,
      abs_of_pos hn0, abs_of_pos hsqrt0]
    calc
      (k : ℝ) * |a| / ((n : ℝ) * Real.sqrt (n : ℝ)) ≤
          (n : ℝ) * |a| / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hkn (abs_nonneg a))
          (mul_nonneg (le_of_lt hn0) (Real.sqrt_nonneg _))
      _ = |a| / Real.sqrt (n : ℝ) := by field_simp
  have habs : |angle a n k| < Real.pi / 2 :=
    lt_of_le_of_lt hangle habs_ratio
  apply Real.cos_pos_of_mem_Ioo
  exact abs_lt.mp habs

/-- Exercise 636, gap 2; replace `BigEnough` and the product ellipsis explicitly. -/
theorem gap2 (a : ℝ)
    (hpos : ∃ N, ∀ n ≥ N, ∀ k ∈ Finset.Icc 1 n,
      0 < Real.cos (angle a n k)) :
    ∃ N, ∀ n ≥ N, Real.log (productSeq a n) = logProductSum a n := by
  rcases hpos with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  classical
  have hlog : ∀ s : Finset ℕ,
      (∀ k ∈ s, Real.cos (angle a n k) ≠ 0) →
      Real.log (s.prod (fun k => Real.cos (angle a n k))) =
        s.sum (fun k => Real.log (Real.cos (angle a n k))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hks ih =>
        intro hs
        have hk : Real.cos (angle a n k) ≠ 0 :=
          hs k (by simp)
        have hs' : ∀ j ∈ s, Real.cos (angle a n j) ≠ 0 := by
          intro j hj
          exact hs j (by simp [hj])
        have hp : s.prod (fun j => Real.cos (angle a n j)) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr hs'
        rw [Finset.prod_insert hks, Finset.sum_insert hks,
          Real.log_mul hk hp, ih hs']
  unfold productSeq logProductSum
  apply hlog
  intro k hk
  exact ne_of_gt (hN n hn k hk)

/-- Exercise 636, gap 3. -/
theorem gap3 (a : ℝ)
    (hpos : ∃ N, ∀ n ≥ N, ∀ k ∈ Finset.Icc 1 n,
      0 < Real.cos (angle a n k)) :
    ∃ N, ∀ n ≥ N,
      logProductSum a n = -(1 / 2 : ℝ) * logTangentSum a n := by
  rcases hpos with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  unfold logProductSum logTangentSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  let x := angle a n k
  have hcpos : 0 < Real.cos x := hN n hn k hk
  have hcne : Real.cos x ≠ 0 := ne_of_gt hcpos
  have htan : 1 + Real.tan x ^ 2 = 1 / Real.cos x ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcne]
    nlinarith [Real.sin_sq_add_cos_sq x]
  change Real.log (Real.cos x) =
    -(1 / 2 : ℝ) * Real.log (1 + Real.tan x ^ 2)
  rw [htan,
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (pow_ne_zero 2 hcne),
    Real.log_one, Real.log_pow]
  ring

/-- Exercise 636, gap 4. -/
theorem gap4 (a : ℝ)
    (hpos : ∃ N, ∀ n ≥ N, ∀ k ∈ Finset.Icc 1 n,
      0 < Real.cos (angle a n k)) :
    ∃ N, ∀ n ≥ N,
      Real.log (productSeq a n) = -(1 / 2 : ℝ) * logTangentSum a n := by
  rcases gap2 a hpos with ⟨N₁, h₁⟩
  rcases gap3 a hpos with ⟨N₂, h₂⟩
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : n ≥ N₁ := le_trans (le_max_left _ _) hn
  have hn₂ : n ≥ N₂ := le_trans (le_max_right _ _) hn
  rw [h₁ n hn₁, h₂ n hn₂]

/-- Exercise 636, gap 5. -/
theorem gap5 :
    Filter.Tendsto (fun x : ℝ => Real.log (1 + Real.tan x ^ 2) / x ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  let F : ℝ → ℝ := fun u => Real.log (1 + u) / u
  have htanDeriv : HasDerivAt Real.tan 1 0 := by
    have h := (Real.hasDerivAt_sin 0).div (Real.hasDerivAt_cos 0)
      (by norm_num : Real.cos 0 ≠ 0)
    have htanEq : Real.tan = Real.sin / Real.cos := by
      funext x
      exact Real.tan_eq_sin_div_cos x
    rw [htanEq]
    convert h using 1 <;> norm_num
  have htan : Filter.Tendsto (fun x : ℝ => Real.tan x / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using htanDeriv.tendsto_slope_zero
  have hadd : HasDerivAt (fun u : ℝ => 1 + u) 1 0 := by
    simpa using
      (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
        (hasDerivAt_id (0 : ℝ))
  have hlogAt : HasDerivAt Real.log 1 1 := by
    simpa using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
  have hlogAt' : HasDerivAt Real.log 1 (1 + (0 : ℝ)) := by
    simpa only [add_zero] using hlogAt
  have hlogDeriv :
      HasDerivAt (fun u : ℝ => Real.log (1 + u)) 1 0 := by
    have h := hlogAt'.comp 0 hadd
    simpa [Function.comp_def] using h
  have hlogBase : Filter.Tendsto
      (fun u : ℝ => Real.log (1 + u) / u)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using
      hlogDeriv.tendsto_slope_zero
  have hxne : ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  have htan0 : Filter.Tendsto Real.tan
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using htanDeriv.continuousAt.tendsto.mono_left inf_le_left
  have hu0 : Filter.Tendsto (fun x : ℝ => Real.tan x ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using htan0.pow 2
  have hratioPos : ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      0 < Real.tan x / x :=
    htan.eventually (Ioi_mem_nhds zero_lt_one)
  have htanNe : ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      Real.tan x ≠ 0 := by
    filter_upwards [hxne, hratioPos] with x hx0 hp
    intro ht
    simp [ht] at hp
  have hu : Filter.Tendsto (fun x : ℝ => Real.tan x ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hu0, ?_⟩
    filter_upwards [htanNe] with x hx0
    simp [hx0]
  have hlog : Filter.Tendsto
      (fun x : ℝ => F (Real.tan x ^ 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [F, Function.comp_def] using hlogBase.comp hu
  have hprod := hlog.mul (htan.pow 2)
  have heq : ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      F (Real.tan x ^ 2) * (Real.tan x / x) ^ 2 =
        Real.log (1 + Real.tan x ^ 2) / x ^ 2 := by
    filter_upwards [hxne, htanNe] with x hx0 ht0
    dsimp [F]
    field_simp [hx0, ht0] <;> ring
  simpa using hprod.congr' heq

/-- Exercise 636, gap 6. -/
theorem gap6 (a : ℝ) (k : ℕ) :
    Filter.Tendsto (fun n : ℕ => angle a n k)
      Filter.atTop (nhds 0) := by
  have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hinv : Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹))
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have hsqrt : Filter.Tendsto (fun n : ℕ => Real.sqrt (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp hcast
  have hsqrtInv : Filter.Tendsto
      (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hc : Filter.Tendsto (fun _ : ℕ => (k : ℝ) * a)
      Filter.atTop (nhds ((k : ℝ) * a)) := tendsto_const_nhds
  simpa [angle, div_eq_mul_inv, mul_inv, mul_assoc] using
    (hc.mul hsqrtInv).mul hinv

/-- Exercise 636, gap 7; replace the sum ellipsis by `squareSum`. -/
theorem gap7 (a : ℝ) (L : ℝ) :
    Filter.Tendsto (squareSum a) Filter.atTop (nhds L) ↔
      Filter.Tendsto (fun n : ℕ =>
        (n : ℝ) * (n + 1) * (2 * n + 1) * a ^ 2 /
          (6 * (n : ℝ) ^ 3)) Filter.atTop (nhds L) := by
  have heq : squareSum a = fun n : ℕ =>
      (n : ℝ) * (n + 1) * (2 * n + 1) * a ^ 2 /
        (6 * (n : ℝ) ^ 3) := by
    funext n
    unfold squareSum
    calc
      (Finset.Icc 1 n).sum (fun k =>
          (k : ℝ) ^ 2 * a ^ 2 / (n : ℝ) ^ 3) =
          ((Finset.Icc 1 n).sum (fun k => (k : ℝ) ^ 2)) *
            (a ^ 2 / (n : ℝ) ^ 3) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = (n : ℝ) * (n + 1) * (2 * n + 1) * a ^ 2 /
          (6 * (n : ℝ) ^ 3) := by
        rw [sum_Icc_sq_real]
        ring
  rw [heq]

/-- Exercise 636, gap 8. -/
theorem gap8 (a : ℝ) :
    Filter.Tendsto (fun n : ℕ =>
      (n : ℝ) * (n + 1) * (2 * n + 1) * a ^ 2 /
        (6 * (n : ℝ) ^ 3)) Filter.atTop (nhds (a ^ 2 / 3)) := by
  have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hinv : Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹))
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have h₁ : Filter.Tendsto (fun n : ℕ => 1 + (n : ℝ)⁻¹)
      Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hinv
  have h₂ : Filter.Tendsto (fun n : ℕ => 2 + (n : ℝ)⁻¹)
      Filter.atTop (nhds 2) := by
    simpa using tendsto_const_nhds.add hinv
  have hmodel : Filter.Tendsto (fun n : ℕ =>
      (1 + (n : ℝ)⁻¹) * (2 + (n : ℝ)⁻¹) * a ^ 2 / 6)
      Filter.atTop (nhds (a ^ 2 / 3)) := by
    convert ((h₁.mul h₂).mul tendsto_const_nhds).div_const 6 using 1 <;> ring
  apply hmodel.congr'
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    positivity
  field_simp [hn0]

/-- Exercise 636, gap 9. -/
theorem gap9 (a : ℝ) :
    Filter.Tendsto (squareSum a) Filter.atTop (nhds (a ^ 2 / 3)) := by
  exact (gap7 a (a ^ 2 / 3)).2 (gap8 a)

/-- Exercise 636, gap 10. -/
theorem gap10 (a : ℝ) :
    Filter.Tendsto (fun n => Real.log (productSeq a n))
      Filter.atTop (nhds (-(a ^ 2 / 6))) := by
  by_cases ha : a = 0
  · subst a
    simpa [productSeq, angle]
  let L : ℝ := a ^ 2 / 3
  let C : ℝ := L + 1
  have hC : 0 < C := by
    dsimp [C, L]
    nlinarith [sq_nonneg a]
  have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hsqrt : Filter.Tendsto (fun n : ℕ => Real.sqrt (n : ℝ))
      Filter.atTop Filter.atTop := Real.tendsto_sqrt_atTop.comp hcast
  have hsqrtInv : Filter.Tendsto
      (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero.comp hsqrt
  have hmax : Filter.Tendsto
      (fun n : ℕ => |a| / Real.sqrt (n : ℝ))
      Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hsqrtInv
  have hdiff : Filter.Tendsto
      (fun n : ℕ => logTangentSum a n - squareSum a n)
      Filter.atTop (nhds 0) := by
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    let η : ℝ := ε / (2 * C)
    have hη : 0 < η := by
      dsimp [η]
      positivity
    let R : ℝ → ℝ := fun x =>
      Real.log (1 + Real.tan x ^ 2) / x ^ 2
    have hrEvent : {x : ℝ | |R x - 1| < η} ∈
        nhdsWithin 0 ({0} : Set ℝ)ᶜ := by
      have h := gap5.eventually (Metric.ball_mem_nhds (1 : ℝ) hη)
      simpa [R, Real.dist_eq] using h
    rcases Metric.mem_nhdsWithin_iff.mp hrEvent with
      ⟨δ, hδ, hδsub⟩
    have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
        |a| / Real.sqrt (n : ℝ) < δ :=
      hmax.eventually (Iio_mem_nhds hδ)
    have hbound : ∀ᶠ n : ℕ in Filter.atTop, squareSum a n < C := by
      have h := (gap9 a).eventually (Iio_mem_nhds (lt_add_one L))
      simpa [C, L] using h
    filter_upwards [hsmall, hbound,
      Filter.eventually_ge_atTop (1 : ℕ)] with n hnsmall hnbound hn
    have hn0 : 0 < (n : ℝ) := by positivity
    have hsqrt0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
    have hsqrtSq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
      Real.sq_sqrt (le_of_lt hn0)
    have hden :
        ((n : ℝ) * Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) ^ 3 := by
      calc
        ((n : ℝ) * Real.sqrt (n : ℝ)) ^ 2 =
            (n : ℝ) ^ 2 * (Real.sqrt (n : ℝ)) ^ 2 := by ring
        _ = (n : ℝ) ^ 2 * (n : ℝ) := by rw [hsqrtSq]
        _ = (n : ℝ) ^ 3 := by ring
    have hangleSq : ∀ k ∈ Finset.Icc 1 n,
        angle a n k ^ 2 =
          (k : ℝ) ^ 2 * a ^ 2 / (n : ℝ) ^ 3 := by
      intro k hk
      rw [angle, div_pow, mul_pow, hden]
    have hangleNe : ∀ k ∈ Finset.Icc 1 n, angle a n k ≠ 0 := by
      intro k hk
      have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
      have hkneNat : k ≠ 0 := Nat.ne_of_gt hkpos
      have hkne : (k : ℝ) ≠ 0 := by
        exact_mod_cast hkneNat
      unfold angle
      apply div_ne_zero
      · exact mul_ne_zero hkne ha
      · exact mul_ne_zero (ne_of_gt hn0) (ne_of_gt hsqrt0)
    have hangleSmall : ∀ k ∈ Finset.Icc 1 n,
        |angle a n k| < δ := by
      intro k hk
      have hk0 : 0 ≤ (k : ℝ) := by positivity
      have hkn : (k : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp hk).2
      have hle : |angle a n k| ≤ |a| / Real.sqrt (n : ℝ) := by
        rw [angle, abs_div, abs_mul, abs_mul, abs_of_nonneg hk0,
          abs_of_pos hn0, abs_of_pos hsqrt0]
        calc
          (k : ℝ) * |a| / ((n : ℝ) * Real.sqrt (n : ℝ)) ≤
              (n : ℝ) * |a| /
                ((n : ℝ) * Real.sqrt (n : ℝ)) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hkn (abs_nonneg a))
              (mul_nonneg (le_of_lt hn0) (Real.sqrt_nonneg _))
          _ = |a| / Real.sqrt (n : ℝ) := by field_simp
      exact lt_of_le_of_lt hle hnsmall
    have hratio : ∀ k ∈ Finset.Icc 1 n,
        |R (angle a n k) - 1| < η := by
      intro k hk
      apply hδsub
      constructor
      · simpa [Metric.mem_ball, Real.dist_eq] using hangleSmall k hk
      · simpa using hangleNe k hk
    have hsumSq : (Finset.Icc 1 n).sum
        (fun k => angle a n k ^ 2) = squareSum a n := by
      unfold squareSum
      apply Finset.sum_congr rfl
      intro k hk
      exact hangleSq k hk
    have hrepr : logTangentSum a n - squareSum a n =
        (Finset.Icc 1 n).sum (fun k =>
          (R (angle a n k) - 1) * angle a n k ^ 2) := by
      rw [logTangentSum, squareSum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← hangleSq k hk]
      dsimp [R]
      have hx := hangleNe k hk
      field_simp [hx]
    rw [hrepr]
    calc
      dist ((Finset.Icc 1 n).sum (fun k =>
          (R (angle a n k) - 1) * angle a n k ^ 2)) 0 =
          |(Finset.Icc 1 n).sum (fun k =>
            (R (angle a n k) - 1) * angle a n k ^ 2)| := by
        simp [Real.dist_eq]
      _ ≤ (Finset.Icc 1 n).sum (fun k =>
          |(R (angle a n k) - 1) * angle a n k ^ 2|) :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ (Finset.Icc 1 n).sum (fun k =>
          η * angle a n k ^ 2) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul, abs_of_nonneg (sq_nonneg (angle a n k))]
        exact mul_le_mul_of_nonneg_right
          (le_of_lt (hratio k hk)) (sq_nonneg _)
      _ = η * squareSum a n := by
        rw [← Finset.mul_sum, hsumSq]
      _ < η * C := mul_lt_mul_of_pos_left hnbound hη
      _ < ε := by
        have hηC : η * C = ε / 2 := by
          dsimp [η]
          field_simp [ne_of_gt hC]
        rw [hηC]
        linarith
  have htan : Filter.Tendsto (logTangentSum a)
      Filter.atTop (nhds (a ^ 2 / 3)) := by
    have h := hdiff.add (gap9 a)
    simpa only [sub_add_cancel, zero_add] using h
  have hlimEq :
      (-(1 / 2 : ℝ)) * (a ^ 2 / 3) = -(a ^ 2 / 6) := by
    ring
  have hscaled : Filter.Tendsto
      (fun n : ℕ => -(1 / 2 : ℝ) * logTangentSum a n)
      Filter.atTop (nhds (-(a ^ 2 / 6))) := by
    rw [← hlimEq]
    exact tendsto_const_nhds.mul htan
  obtain ⟨N, hN⟩ := gap4 a (gap1 a)
  refine hscaled.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  exact (hN n hn).symm

/-- Exercise 636, gap 11. -/
theorem gap11 (a : ℝ) :
    Filter.Tendsto (productSeq a) Filter.atTop
      (nhds (Real.exp (-(a ^ 2 / 6)))) := by
  have hcomp : Filter.Tendsto
      (fun n : ℕ => Real.exp (Real.log (productSeq a n)))
      Filter.atTop (nhds (Real.exp (-(a ^ 2 / 6)))) := by
    simpa [Function.comp_def] using
      Real.continuous_exp.continuousAt.tendsto.comp (gap10 a)
  rcases gap1 a with ⟨N, hN⟩
  apply hcomp.congr'
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  rw [Real.exp_log]
  unfold productSeq
  exact Finset.prod_pos fun k hk => hN n hn k hk

end

end ProofGap.Exercise636
