import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise3095

noncomputable section

open Filter
open scoped Topology

def sign (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n * (n - 1) / 2)

def p (n : ℕ) : ℝ :=
  1 + sign n / (n : ℝ)

def u (n : ℕ) : ℝ :=
  Real.log (p n)

def a (k : ℕ) : ℝ :=
  u (2 * k - 1) + u (2 * k)

def pairedClosedForm (k : ℕ) : ℝ :=
  Real.log
    (1 + (((-1 : ℝ) ^ (k - 1) - 1) /
      ((2 * (k : ℝ)) * (2 * (k : ℝ) - 1))))

def SummableFromOne (f : ℕ → ℝ) : Prop :=
  ∃ L : ℝ,
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, f (k + 1)) atTop (𝓝 L)

def ConditionallySummableFromOne (f : ℕ → ℝ) : Prop :=
  SummableFromOne f ∧ ¬SummableFromOne (fun n => |f n|)

private theorem neg_one_pow_two_mul (j : ℕ) :
    (-1 : ℝ) ^ (2 * j) = 1 := by
  rw [pow_mul]
  norm_num

private theorem neg_one_pow_two_mul_add_one (j : ℕ) :
    (-1 : ℝ) ^ (2 * j + 1) = -1 := by
  rw [pow_add, neg_one_pow_two_mul]
  norm_num

private theorem sign_two_mul (k : ℕ) (hk : 1 ≤ k) :
    sign (2 * k) = (-1 : ℝ) ^ k := by
  unfold sign
  have he :
      (2 * k) * (2 * k - 1) / 2 = k * (2 * k - 1) := by
    rw [show (2 * k) * (2 * k - 1) =
      2 * (k * (2 * k - 1)) by ring]
    simpa [mul_comm] using Nat.mul_div_left (k * (2 * k - 1)) 2
  rw [he]
  have hodd : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
  calc
    (-1 : ℝ) ^ (k * (2 * k - 1)) =
        ((-1 : ℝ) ^ (2 * k - 1)) ^ k := by
      rw [mul_comm, pow_mul]
    _ = (-1 : ℝ) ^ k := by
      rw [hodd, neg_one_pow_two_mul_add_one]

private theorem sign_two_mul_sub_one (k : ℕ) (hk : 1 ≤ k) :
    sign (2 * k - 1) = (-1 : ℝ) ^ (k - 1) := by
  unfold sign
  have hpred : 2 * k - 1 - 1 = 2 * (k - 1) := by omega
  rw [hpred]
  have he :
      (2 * k - 1) * (2 * (k - 1)) / 2 =
        (2 * k - 1) * (k - 1) := by
    rw [show (2 * k - 1) * (2 * (k - 1)) =
      2 * ((2 * k - 1) * (k - 1)) by ring]
    simpa [mul_comm] using
      Nat.mul_div_left ((2 * k - 1) * (k - 1)) 2
  rw [he, pow_mul]
  have hodd : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
  rw [hodd, neg_one_pow_two_mul_add_one]

private theorem abs_sign (n : ℕ) :
    |sign n| = 1 := by
  unfold sign
  rw [abs_pow]
  norm_num

private theorem isEquivalent_abs {ι : Type*} {l : Filter ι}
    {f g : ι → ℝ} (h : Asymptotics.IsEquivalent l f g) :
    Asymptotics.IsEquivalent l (fun x => |f x|) (fun x => |g x|) := by
  rw [Asymptotics.IsEquivalent, Asymptotics.isLittleO_iff]
  intro c hc
  have he := h.isLittleO.def hc
  filter_upwards [he] with x hx
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hx ⊢
  calc
    abs (abs (f x) - abs (g x)) ≤ abs (f x - g x) :=
      abs_abs_sub_abs_le_abs_sub _ _
    _ ≤ c * abs (g x) := hx
    _ = c * abs (abs (g x)) := by rw [abs_of_nonneg (abs_nonneg _)]

private theorem log_one_add_isEquivalent :
    Asymptotics.IsEquivalent (𝓝 0)
      (fun x : ℝ => Real.log (1 + x)) (fun x : ℝ => x) := by
  have hinner :
      HasDerivAt (fun x : ℝ => 1 + x) 1 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) 0).const_add 1
  have houter :
      HasDerivAt Real.log 1 ((fun x : ℝ => 1 + x) 0) := by
    simpa using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
  have hderiv :
      HasDerivAt (fun x : ℝ => Real.log (1 + x)) 1 0 := by
    simpa [Function.comp_def] using houter.comp 0 hinner
  have hlo :
      Asymptotics.IsLittleO (𝓝 0)
        (fun x : ℝ => Real.log (1 + x) - x)
        (fun x : ℝ => x) := by
    simpa using hderiv.isLittleO
  exact hlo.isEquivalent

private theorem one_add_neg_one_pow_div_pos (e : ℕ) {d : ℝ}
    (hd : 1 < d) :
    0 < 1 + (-1 : ℝ) ^ e / d := by
  have hdpos : 0 < d := lt_trans zero_lt_one hd
  have hr : -1 ≤ (-1 : ℝ) ^ e := by
    have habs : |(-1 : ℝ) ^ e| = 1 := by
      rw [abs_pow]
      norm_num
    exact (abs_le.mp (by rw [habs])).1
  have hdiv :
      (-1 : ℝ) / d ≤ (-1 : ℝ) ^ e / d :=
    (div_le_div_iff_of_pos_right hdpos).mpr hr
  have hneg : (-1 : ℝ) < (-1 : ℝ) / d := by
    rw [lt_div_iff₀ hdpos]
    nlinarith
  linarith

private theorem norm_even_paired_log_le (m : ℕ) (hm : 1 ≤ m) :
    ‖Real.log
        (1 - 2 / ((4 * (m : ℝ)) * (4 * (m : ℝ) - 1)))‖
      ≤ 1 / (m : ℝ) ^ 2 := by
  let mr : ℝ := m
  let D : ℝ := (4 * mr) * (4 * mr - 1)
  let x : ℝ := 2 / D
  have hmone : 1 ≤ mr := by
    dsimp [mr]
    exact_mod_cast hm
  have hmpos : 0 < mr := lt_of_lt_of_le zero_lt_one hmone
  have hmquad : 0 ≤ mr * (mr - 1) :=
    mul_nonneg hmpos.le (sub_nonneg.mpr hmone)
  have hDgt : 2 < D := by
    dsimp [D]
    nlinarith
  have hDpos : 0 < D := lt_trans (by norm_num) hDgt
  have hDsub : 0 < D - 2 := sub_pos.mpr hDgt
  have hxpos : 0 < x := by
    dsimp [x]
    positivity
  have hxlt : x < 1 := by
    dsimp [x]
    exact (div_lt_one hDpos).mpr hDgt
  have hxabs : |x| = x := abs_of_pos hxpos
  have hlog :
      |Real.log (1 - x)| ≤ x / (1 - x) := by
    have h := Real.abs_log_sub_add_sum_range_le (x := x)
      (by rw [hxabs]; exact hxlt) 0
    simpa [hxabs] using h
  have hfrac : x / (1 - x) = 2 / (D - 2) := by
    dsimp [x]
    field_simp [ne_of_gt hDpos, ne_of_gt hDsub]
  have hm2pos : 0 < mr ^ 2 := sq_pos_of_pos hmpos
  have hcross : 2 * mr ^ 2 ≤ D - 2 := by
    dsimp [D]
    nlinarith
  have hfinal : x / (1 - x) ≤ 1 / mr ^ 2 := by
    rw [hfrac]
    apply (div_le_div_iff₀ hDsub hm2pos).mpr
    nlinarith
  change ‖Real.log (1 - x)‖ ≤ 1 / mr ^ 2
  rw [Real.norm_eq_abs]
  exact hlog.trans hfinal

/--
Exercise 3095, gap 1; remove the erroneous extra factor
`1/n` and retain the definition of arbitrary `p₀`.
-/
theorem gap1 (p₀ : ℕ → ℝ) (hp : ∀ n, p₀ n = p n) :
    ∀ n : ℕ, 1 ≤ n →
      |Real.log (p₀ n)| = |Real.log (1 + sign n / (n : ℝ))| := by
  intro n hn
  rw [hp n]
  rfl

/-- Exercise 3095, gap 2; state the asymptotic relation functionally. -/
theorem gap2 :
    Asymptotics.IsEquivalent atTop
      (fun n => |u n|) (fun n => 1 / (n : ℝ)) := by
  let x : ℕ → ℝ := fun n => sign n / (n : ℝ)
  have hinv :
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ))
          atTop atTop))
  have hx : Tendsto x atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    convert hinv using 1
    funext n
    simp only [x, Real.norm_eq_abs, abs_div, abs_sign]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  have hcomp := log_one_add_isEquivalent.comp_tendsto hx
  have habs := isEquivalent_abs hcomp
  refine (habs.congr_left ?_).congr_right ?_
  · apply Eventually.of_forall
    intro n
    simp only [Function.comp_apply, x, u, p]
  · apply Eventually.of_forall
    intro n
    simp only [Function.comp_apply, id_eq, x, abs_div, abs_sign]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]

/-- Exercise 3095, gap 3. -/
theorem gap3 :
    ¬SummableFromOne (fun n => |u n|) := by
  intro hsum
  rcases hsum with ⟨L, hL⟩
  have hshift : Summable (fun n : ℕ => |u (n + 1)|) := by
    refine ⟨L, (hasSum_iff_tendsto_nat_of_nonneg
      (fun n => abs_nonneg (u (n + 1))) L).mpr ?_⟩
    simpa using hL
  have habs : Summable (fun n : ℕ => |u n|) :=
    (summable_nat_add_iff 1).mp hshift
  have hinv : Summable (fun n : ℕ => 1 / (n : ℝ)) :=
    summable_of_isBigO_nat habs gap2.isBigO_symm
  have hnot :
      ¬Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 : ℕ)) := by
    rw [Real.summable_one_div_nat_pow]
    norm_num
  apply hnot
  simpa using hinv

/-- Exercise 3095, gap 4; predecessor indices require `k ≥ 1`. -/
theorem gap4 :
    ∀ k : ℕ, 1 ≤ k →
      u (2 * k - 1) =
        Real.log (1 + (-1 : ℝ) ^ (k - 1) / (2 * (k : ℝ) - 1)) := by
  intro k hk
  unfold u p
  rw [sign_two_mul_sub_one k hk]
  have hcast : ((2 * k - 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hcast]

/-- Exercise 3095, gap 5; paired indices start at one. -/
theorem gap5 :
    ∀ k : ℕ, 1 ≤ k →
      u (2 * k) = Real.log (1 + (-1 : ℝ) ^ k / (2 * (k : ℝ))) := by
  intro k hk
  unfold u p
  rw [sign_two_mul k hk]
  congr 2
  push_cast
  ring

/-- Exercise 3095, gap 6; combine the two positive factors. -/
theorem gap6 :
    ∀ k : ℕ, 1 ≤ k → a k = pairedClosedForm k := by
  intro k hk
  rw [a, gap4 k hk, gap5 k hk]
  unfold pairedClosedForm
  have hkone : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden1 : 2 * (k : ℝ) - 1 ≠ 0 := by
    nlinarith
  have hden2 : 2 * (k : ℝ) ≠ 0 := by
    positivity
  have hfac1 :
      1 + (-1 : ℝ) ^ (k - 1) / (2 * (k : ℝ) - 1) ≠ 0 := by
    by_cases hk1 : k = 1
    · subst k
      norm_num
    · apply ne_of_gt
      apply one_add_neg_one_pow_div_pos
      have hk2 : (2 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (show 2 ≤ k by omega)
      linarith
  have hfac2 :
      1 + (-1 : ℝ) ^ k / (2 * (k : ℝ)) ≠ 0 := by
    apply ne_of_gt
    apply one_add_neg_one_pow_div_pos
    linarith
  rw [← Real.log_mul hfac1 hfac2]
  congr 1
  have hpow :
      (-1 : ℝ) ^ k = -((-1 : ℝ) ^ (k - 1)) := by
    rw [show k = (k - 1) + 1 by omega, pow_add]
    norm_num
  have hsquare :
      ((-1 : ℝ) ^ (k - 1)) ^ 2 = 1 := by
    rw [← pow_mul]
    have heven : (k - 1) * 2 = 2 * (k - 1) := by ring
    rw [heven, neg_one_pow_two_mul]
  rw [hpow]
  field_simp [hden1, hden2]
  nlinarith

/-- Exercise 3095, gap 7; predecessor indices require `m ≥ 1`. -/
theorem gap7 :
    ∀ m : ℕ, 1 ≤ m → a (2 * m - 1) = 0 := by
  intro m hm
  rw [gap6 (2 * m - 1) (by omega)]
  unfold pairedClosedForm
  have heven : 2 * m - 1 - 1 = 2 * (m - 1) := by omega
  rw [heven, neg_one_pow_two_mul]
  norm_num

/-- Exercise 3095, gap 8; paired indices start at one. -/
theorem gap8 :
    ∀ m : ℕ, 1 ≤ m →
      a (2 * m) =
        Real.log (1 - 2 / ((4 * (m : ℝ)) * (4 * (m : ℝ) - 1))) := by
  intro m hm
  rw [gap6 (2 * m) (by omega)]
  unfold pairedClosedForm
  have hodd : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
  rw [hodd, neg_one_pow_two_mul_add_one]
  congr 1
  push_cast
  ring

/-- Exercise 3095, gap 9. -/
theorem gap9 : SummableFromOne a := by
  have hp0 :
      Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hp :
      Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) :=
    (summable_nat_add_iff 1).mpr hp0
  have hevenShift :
      Summable (fun n : ℕ => a (2 * (n + 1))) := by
    apply Summable.of_norm_bounded hp
    intro n
    rw [gap8 (n + 1) (by omega)]
    exact norm_even_paired_log_le (n + 1) (by omega)
  have heven : Summable (fun n : ℕ => a (2 * n)) :=
    (summable_nat_add_iff 1).mp hevenShift
  have hodd : Summable (fun n : ℕ => a (2 * n + 1)) := by
    convert (summable_zero : Summable (fun _ : ℕ => (0 : ℝ))) using 1
    funext n
    rw [show 2 * n + 1 = 2 * (n + 1) - 1 by omega,
      gap7 (n + 1) (by omega)]
  have hall : Summable a :=
    Summable.even_add_odd heven hodd
  have hshift : Summable (fun n : ℕ => a (n + 1)) :=
    (summable_nat_add_iff 1).mpr hall
  exact ⟨∑' n : ℕ, a (n + 1), hshift.tendsto_sum_tsum_nat⟩

/-- Exercise 3095, gap 10. -/
theorem gap10 : Tendsto u atTop (𝓝 0) := by
  have hinv :
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ))
          atTop atTop))
  have habs : Tendsto (fun n : ℕ => |u n|) atTop (𝓝 0) :=
    gap2.tendsto_nhds_iff.mpr hinv
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using habs

/-- Exercise 3095, gap 11. -/
theorem gap11 : SummableFromOne u := by
  rcases gap9 with ⟨L, hL⟩
  let S : ℕ → ℝ := fun N => ∑ k ∈ Finset.range N, u (k + 1)
  have heq (N : ℕ) :
      S (2 * N) = ∑ k ∈ Finset.range N, a (k + 1) := by
    induction N with
    | zero => simp [S]
    | succ N ih =>
        calc
          S (2 * (N + 1)) =
              S (2 * N) + u (2 * N + 1) + u (2 * N + 2) := by
            simp only [S]
            rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
              Finset.sum_range_succ, Finset.sum_range_succ]
          _ = (∑ k ∈ Finset.range N, a (k + 1)) + a (N + 1) := by
            rw [ih]
            unfold a
            rw [show 2 * (N + 1) - 1 = 2 * N + 1 by omega,
              show 2 * (N + 1) = 2 * N + 2 by omega]
            ring
          _ = ∑ k ∈ Finset.range (N + 1), a (k + 1) := by
            rw [Finset.sum_range_succ]
  have heven : Tendsto (fun N : ℕ => S (2 * N)) atTop (𝓝 L) := by
    convert hL using 1
    funext N
    exact heq N
  have hindex : Tendsto (fun N : ℕ => 2 * N + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  have hodd : Tendsto (fun N : ℕ => S (2 * N + 1)) atTop (𝓝 L) := by
    have hadd := heven.add (gap10.comp hindex)
    simpa only [S, Finset.sum_range_succ, add_zero] using hadd
  have hfull : Tendsto S atTop (𝓝 L) := by
    rw [tendsto_def]
    intro V hV
    have hVe : ∀ᶠ N in atTop, S (2 * N) ∈ V := heven.eventually hV
    have hVo : ∀ᶠ N in atTop, S (2 * N + 1) ∈ V := hodd.eventually hV
    rcases eventually_atTop.mp hVe with ⟨Ne, hNe⟩
    rcases eventually_atTop.mp hVo with ⟨No, hNo⟩
    refine eventually_atTop.2 ⟨2 * max Ne No + 1, ?_⟩
    intro N hN
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' N
    · exact hNe k (by omega)
    · exact hNo k (by omega)
  exact ⟨L, by simpa only [S] using hfull⟩

/-- Exercise 3095, gap 12. -/
theorem gap12 :
    ConditionallySummableFromOne (fun n => Real.log (p n)) := by
  constructor
  · simpa [u] using gap11
  · simpa [u] using gap3

end

end ProofGap.Exercise3095
