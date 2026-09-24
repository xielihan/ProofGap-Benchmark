import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise3105_2

noncomputable section

open Filter
open scoped BigOperators Topology

def admissible (x : ℝ) : Prop :=
  ∀ m : ℕ, x ≠ -(m : ℝ)

def eulerApproximant (x : ℝ) (n : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) * Real.rpow n x /
    (x * ∏ k ∈ Finset.Icc 1 n, (x + k))

def p (x : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (1 + 1 / (n : ℝ)) x / (1 + x / n)

def alpha (x : ℝ) (n : ℕ) : ℝ :=
  p x n - 1

def SummableFromOne (f : ℕ → ℝ) : Prop :=
  Summable (fun n : ℕ => f (n + 1))

def partialProduct (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∏ n ∈ Finset.Icc 1 N, f n

def HasProductFromOne (f : ℕ → ℝ) (L : ℝ) : Prop :=
  Tendsto (partialProduct f) atTop (𝓝 L)

/-- Source: `proof_gap/exercise_3105_2/1.txt`; formalize nonnegative and positive integers. -/
theorem gap1 :
    ∀ x : ℝ, admissible x →
      ∀ n : ℕ, 1 ≤ n → 1 + x / n ≠ 0 := by
  intro x hx n hn hzero
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hxn : x = -(n : ℝ) := by
    field_simp [hn0] at hzero
    linarith
  exact hx n hxn

/--
Source: `proof_gap/exercise_3105_2/2.txt`; bind `x` in `p` and `alpha`, and
represent the asymptotic remainder at function level.
-/
theorem gap2 :
    ∀ x : ℝ,
      (fun n : ℕ =>
        alpha x (n + 1) -
          x * (x - 1) / (2 * ((n + 1 : ℕ) : ℝ) ^ 2))
        =O[atTop] (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 3)) := by
  intro x
  let δ : ℝ := 1 / (2 * (|x| + 1))
  let N : ℝ → ℝ := fun u => Real.rpow (1 + u) x
  let c : ℝ := x * (x - 1) / 2
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hbase : ∀ u ∈ Set.Icc (0 : ℝ) δ, 1 + u ≠ 0 := by
    intro u hu
    exact ne_of_gt (by linarith [hu.1])
  have hNcont : ContDiffOn ℝ 3 N (Set.Icc (0 : ℝ) δ) := by
    dsimp [N]
    exact (contDiffOn_const.add contDiffOn_id).rpow_const_of_ne hbase
  obtain ⟨C, hC⟩ :=
    exists_taylor_mean_remainder_bound
      (f := N) (n := 2) (a := (0 : ℝ)) (b := δ)
      hδpos.le hNcont
  have hglobal (k : ℕ) :
      iteratedDeriv k N 0 =
        (descPochhammer ℝ k).eval x := by
    have H := congrFun (iteratedDeriv_comp_const_add k
      (fun z : ℝ => Real.rpow z x) 1) 0
    calc
      iteratedDeriv k N 0 =
          iteratedDeriv k (fun z : ℝ => Real.rpow z x) (1 + 0) := by
            simpa [N] using H
      _ = (descPochhammer ℝ k).eval x := by
        simpa [iteratedDeriv_eq_iterate] using
          Real.iter_deriv_rpow_const x 1 k
  have hwithin (k : ℕ) :
      iteratedDerivWithin k N (Set.Icc (0 : ℝ) δ) 0 =
        (descPochhammer ℝ k).eval x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc hδpos)
      (show ContDiffAt ℝ k N 0 by
        dsimp [N]
        exact (contDiffAt_const.add contDiffAt_id).rpow_const_of_ne (by norm_num))
      (Set.left_mem_Icc.mpr hδpos.le)]
    exact hglobal k
  have hTaylor : ∀ u : ℝ,
      taylorWithinEval N 2 (Set.Icc (0 : ℝ) δ) 0 u =
        1 + x * u + c * u ^ 2 := by
    intro u
    rw [show (2 : ℕ) = 1 + 1 by norm_num,
      taylorWithinEval_succ, taylorWithinEval_succ,
      taylor_within_zero_eval, hwithin, hwithin]
    dsimp [N, c]
    norm_num [descPochhammer]
    ring
  have hevent : ∀ᶠ n : ℕ in atTop,
      1 / (((n + 1 : ℕ) : ℝ)) ≤ δ := by
    have ht : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact (ht.eventually_le_const hδpos).mono (fun n hn => by simpa using hn)
  refine Asymptotics.isBigO_iff.2
    ⟨2 * (|C| + |x * c|), ?_⟩
  filter_upwards [hevent] with n hn
  let u : ℝ := 1 / (((n + 1 : ℕ) : ℝ))
  have hunonneg : 0 ≤ u := by dsimp [u]; positivity
  have huIcc : u ∈ Set.Icc (0 : ℝ) δ := ⟨hunonneg, hn⟩
  have hrem0 := hC u huIcc
  rw [hTaylor] at hrem0
  have hrem :
      |N u - (1 + x * u + c * u ^ 2)| ≤
        |C| * u ^ 3 := by
    rw [Real.norm_eq_abs] at hrem0
    have hu3 : 0 ≤ u ^ 3 := by positivity
    calc
      |N u - (1 + x * u + c * u ^ 2)|
          ≤ C * (u - 0) ^ 3 := hrem0
      _ ≤ |C| * u ^ 3 := by
        nlinarith [le_abs_self C]
  have hxu : |x| * u ≤ 1 / 2 := by
    have hδ :
        δ * |x| ≤ 1 / 2 := by
      dsimp [δ]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg x]
    calc
      |x| * u ≤ |x| * δ :=
        mul_le_mul_of_nonneg_left hn (abs_nonneg x)
      _ = δ * |x| := by ring
      _ ≤ 1 / 2 := hδ
  have hdenpos : 1 / 2 ≤ 1 + x * u := by
    have hxlower : -|x| ≤ x := neg_abs_le x
    have hm : -(|x| * u) ≤ x * u :=
      by
        convert mul_le_mul_of_nonneg_right hxlower hunonneg using 1 <;> ring
    nlinarith
  have hden0 : 1 + x * u ≠ 0 := by linarith
  have halgebra :
      N u / (1 + x * u) - 1 - c * u ^ 2 =
        (N u - (1 + x * u + c * u ^ 2) -
          x * c * u ^ 3) / (1 + x * u) := by
    field_simp [hden0]
    ring
  have hnum :
      |N u - (1 + x * u + c * u ^ 2) - x * c * u ^ 3| ≤
        (|C| + |x * c|) * u ^ 3 := by
    calc
      |N u - (1 + x * u + c * u ^ 2) - x * c * u ^ 3|
          ≤ |N u - (1 + x * u + c * u ^ 2)| +
              |x * c * u ^ 3| := abs_sub _ _
      _ ≤ |C| * u ^ 3 + |x * c| * u ^ 3 := by
        gcongr
        rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hunonneg]
      _ = (|C| + |x * c|) * u ^ 3 := by ring
  have hquot :
      |N u / (1 + x * u) - 1 - c * u ^ 2| ≤
        2 * (|C| + |x * c|) * u ^ 3 := by
    rw [halgebra, abs_div]
    apply (div_le_iff₀ (abs_pos.mpr hden0)).2
    rw [abs_of_nonneg (by linarith [hdenpos] : 0 ≤ 1 + x * u)]
    have hK : 0 ≤ |C| + |x * c| := by positivity
    have hu3 : 0 ≤ u ^ 3 := by positivity
    have hscale :
        (|C| + |x * c|) * u ^ 3 ≤
          2 * (|C| + |x * c|) * u ^ 3 * (1 + x * u) := by
      nlinarith [mul_nonneg hK hu3]
    exact hnum.trans hscale
  change ‖alpha x (n + 1) -
      x * (x - 1) / (2 * ((n + 1 : ℕ) : ℝ) ^ 2)‖ ≤
    (2 * (|C| + |x * c|)) *
      ‖1 / (((n + 1 : ℕ) : ℝ) ^ 3)‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hrewrite :
      alpha x (n + 1) -
          x * (x - 1) / (2 * ((n + 1 : ℕ) : ℝ) ^ 2) =
        N u / (1 + x * u) - 1 - c * u ^ 2 := by
    dsimp [alpha, p, N, c, u]
    congr 2 <;> field_simp <;> ring
  rw [hrewrite]
  have hpow :
      1 / (((n + 1 : ℕ) : ℝ) ^ 3) = u ^ 3 := by
    simp [u, one_div, inv_pow]
  rw [hpow, abs_of_nonneg (by positivity : 0 ≤ u ^ 3)]
  exact hquot

/-- Source: `proof_gap/exercise_3105_2/3.txt`; the free parameter `x` is explicit. -/
theorem gap3 :
    ∀ x : ℝ, SummableFromOne (fun n => |alpha x n|) := by
  intro x
  have hcube :
      Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 3)) := by
    simpa [Function.comp_def] using
      ((Real.summable_one_div_nat_pow (p := 3)).mpr (by norm_num)).comp_injective
        Nat.succ_injective
  have hrem :
      Summable (fun n : ℕ =>
        alpha x (n + 1) -
          x * (x - 1) / (2 * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
    summable_of_isBigO_nat hcube (gap2 x)
  have hsquare :
      Summable (fun n : ℕ =>
        x * (x - 1) / (2 * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
    have h :
        Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
      simpa [Function.comp_def] using
        ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)).comp_injective
          Nat.succ_injective
    convert h.mul_left (x * (x - 1) / 2) using 1
    funext n
    ring
  have halpha : Summable (fun n : ℕ => alpha x (n + 1)) := by
    convert hrem.add hsquare using 1
    funext n
    ring
  exact halpha.abs

/-- Source: `proof_gap/exercise_3105_2/4.txt`; the free parameter `x` is explicit. -/
theorem gap4 :
    ∀ x : ℝ, SummableFromOne (fun n => |Real.log (p x n)|) := by
  intro x
  have haabs : Summable (fun n : ℕ => |alpha x (n + 1)|) := gap3 x
  have ha : Summable (fun n : ℕ => alpha x (n + 1)) :=
    haabs.of_norm_bounded (fun n => by
      simpa [Real.norm_eq_abs] using le_rfl)
  have hlog :=
    Real.summable_log_one_add_of_summable ha
  have hlog' : Summable (fun n : ℕ => Real.log (p x (n + 1))) := by
    apply hlog.congr
    intro n
    simp [alpha]
  exact hlog'.abs

private lemma admissible_ne_zero {x : ℝ} (hx : admissible x) : x ≠ 0 := by
  simpa using hx 0

private lemma admissible_add_nat_ne_zero {x : ℝ} (hx : admissible x) (k : ℕ) :
    x + k ≠ 0 := by
  intro h
  apply hx k
  linarith

private lemma factorial_eq_prod_Icc_cast (n : ℕ) :
    (Nat.factorial n : ℝ) = ∏ k ∈ Finset.Icc 1 n, (k : ℝ) := by
  rw [← Finset.prod_natCast]
  rw [← Finset.prod_Ico_id_eq_factorial]
  congr 1

private lemma prod_one_add_div (x : ℝ) (n : ℕ) :
    (∏ k ∈ Finset.Icc 1 n, (1 + x / k)) =
      (∏ k ∈ Finset.Icc 1 n, (x + k)) / (Nat.factorial n : ℝ) := by
  rw [factorial_eq_prod_Icc_cast]
  calc
    (∏ k ∈ Finset.Icc 1 n, (1 + x / k)) =
        ∏ k ∈ Finset.Icc 1 n, ((x + k) / k) := by
      apply Finset.prod_congr rfl
      intro k hk
      have hk0 : (k : ℝ) ≠ 0 := by
        have : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        positivity
      field_simp
      ring
    _ = (∏ k ∈ Finset.Icc 1 n, (x + k)) /
        ∏ k ∈ Finset.Icc 1 n, (k : ℝ) := by
      rw [Finset.prod_div_distrib]

private lemma prod_one_add_inv (n : ℕ) :
    (∏ k ∈ Finset.Icc 1 n, (1 + 1 / (k : ℝ))) = n + 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : n + 1 ∉ Finset.Icc 1 n := by
        intro hmem
        have hle := (Finset.mem_Icc.mp hmem).2
        omega
      rw [hIcc, Finset.prod_insert hnot, ih]
      have hnpos : (0 : ℝ) < n + 1 := by positivity
      field_simp
      norm_num [Nat.cast_add, Nat.cast_one]

private lemma prod_rpow_one_add_inv (x : ℝ) (n : ℕ) :
    (∏ k ∈ Finset.Icc 1 n, Real.rpow (1 + 1 / (k : ℝ)) x) =
      Real.rpow (n + 1 : ℕ) x := by
  have hnonneg : ∀ k ∈ Finset.Icc 1 n, (0 : ℝ) ≤ 1 + 1 / (k : ℝ) := by
    intro k hk
    have hkpos : (0 : ℝ) < k := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1)
    positivity
  have h := Real.finset_prod_rpow (Finset.Icc 1 n)
    (fun k : ℕ => 1 + 1 / (k : ℝ)) hnonneg x
  rw [prod_one_add_inv] at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

private lemma prod_rpow_div_last (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (∏ k ∈ Finset.Icc 1 n, Real.rpow (1 + 1 / (k : ℝ)) x) /
        Real.rpow (1 + 1 / (n : ℝ)) x =
      Real.rpow n x := by
  rw [prod_rpow_one_add_inv]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1pos : (0 : ℝ) < n + 1 := by positivity
  have hbase : 1 + 1 / (n : ℝ) = ((n : ℝ) + 1) / n := by
    field_simp
  rw [hbase]
  norm_num [Nat.cast_add, Nat.cast_one]
  rw [Real.div_rpow hn1pos.le hnpos.le]
  have hnpow : Real.rpow (n : ℝ) x ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos x).ne'
  have hn1pow : Real.rpow ((n : ℝ) + 1) x ≠ 0 :=
    (Real.rpow_pos_of_pos hn1pos x).ne'
  field_simp

private lemma prod_range_add_eq (x : ℝ) (n : ℕ) :
    (∏ j ∈ Finset.range (n + 1), (x + j)) =
      x * ∏ k ∈ Finset.Icc 1 n, (x + k) := by
  have hset : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hzero : 0 ∉ Finset.Icc 1 n := by simp
  rw [hset, Finset.prod_insert hzero]
  norm_num

private lemma eulerApproximant_eq_GammaSeq (x : ℝ) (n : ℕ) :
    eulerApproximant x n = Real.GammaSeq x n := by
  unfold eulerApproximant Real.GammaSeq
  rw [prod_range_add_eq]
  change (Nat.factorial n : ℝ) * Real.rpow (n : ℝ) x /
      (x * ∏ k ∈ Finset.Icc 1 n, (x + k)) =
    Real.rpow (n : ℝ) x * (Nat.factorial n : ℝ) /
      (x * ∏ k ∈ Finset.Icc 1 n, (x + k))
  ring

private lemma partialProduct_eq_prod_div (x : ℝ) (n : ℕ) :
    partialProduct (p x) n =
      (∏ k ∈ Finset.Icc 1 n, Real.rpow (1 + 1 / (k : ℝ)) x) /
        (∏ k ∈ Finset.Icc 1 n, (1 + x / k)) := by
  unfold partialProduct p
  rw [Finset.prod_div_distrib]

private lemma eulerApproximant_product_formula
    (n : ℕ) (x : ℝ) (hn : 1 ≤ n) (hx : admissible x) :
    eulerApproximant x n =
      (1 / x) *
        ((∏ k ∈ Finset.Icc 1 n, Real.rpow (1 + 1 / (k : ℝ)) x) /
          (∏ k ∈ Finset.Icc 1 n, (1 + x / k))) *
        (1 / Real.rpow (1 + 1 / (n : ℝ)) x) := by
  have hx0 := admissible_ne_zero hx
  have hprod0 : (∏ k ∈ Finset.Icc 1 n, (x + k)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact admissible_add_nat_ne_zero hx k
  have hfact0 : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hden0 : (∏ k ∈ Finset.Icc 1 n, (1 + x / k)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    have hk0 : (k : ℝ) ≠ 0 := by
      have : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      positivity
    have hxk0 := admissible_add_nat_ne_zero hx k
    rw [show 1 + x / (k : ℝ) = (x + k) / k by
      field_simp [hk0]
      ring]
    exact div_ne_zero hxk0 hk0
  have hlast0 : Real.rpow (1 + 1 / (n : ℝ)) x ≠ 0 := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hbase : 0 < 1 + 1 / (n : ℝ) := by positivity
    exact (Real.rpow_pos_of_pos hbase x).ne'
  have hfirst :
      eulerApproximant x n =
        Real.rpow n x / x *
          (1 / ∏ k ∈ Finset.Icc 1 n, (1 + x / k)) := by
    unfold eulerApproximant
    rw [prod_one_add_div]
    field_simp [hx0, hprod0, hfact0]
  rw [hfirst]
  have hprod := prod_rpow_div_last x n hn
  field_simp [hx0, hden0, hlast0] at hprod ⊢
  nlinarith

private lemma partialProduct_eq_euler_mul (x : ℝ) (n : ℕ)
    (hn : 1 ≤ n) (hx : admissible x) :
    partialProduct (p x) n =
      x * eulerApproximant x n * Real.rpow (1 + 1 / (n : ℝ)) x := by
  have h := eulerApproximant_product_formula n x hn hx
  rw [← partialProduct_eq_prod_div] at h
  have hx0 := admissible_ne_zero hx
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbase : 0 < 1 + 1 / (n : ℝ) := by positivity
  have hr0 : Real.rpow (1 + 1 / (n : ℝ)) x ≠ 0 :=
    (Real.rpow_pos_of_pos hbase x).ne'
  have hrewrite : 1 + 1 / (n : ℝ) = ((n : ℝ) + 1) / n := by
    field_simp
  rw [hrewrite] at h hr0 ⊢
  field_simp [hx0, hr0] at h
  calc
    partialProduct (p x) n =
        eulerApproximant x n * x * Real.rpow (((n : ℝ) + 1) / n) x := h.symm
    _ = x * eulerApproximant x n * Real.rpow (((n : ℝ) + 1) / n) x := by ring

/--
Source: `proof_gap/exercise_3105_2/5.txt`; retain the pole restriction and use
a witnessed nonzero-domain product limit rather than a totalized product value.
-/
theorem gap5 (Gamma : ℝ → ℝ)
    (hGamma :
      ∀ x : ℝ, admissible x →
        Tendsto (eulerApproximant x) atTop (𝓝 (Gamma x))) :
    ∀ x : ℝ, admissible x →
      ∃ L : ℝ,
        L ≠ 0 ∧
        HasProductFromOne (p x) L ∧
        Gamma x = (1 / x) * L := by
  intro x hx
  have hx0 := admissible_ne_zero hx
  have hEulerReal : Tendsto (eulerApproximant x) atTop (𝓝 (Real.Gamma x)) := by
    apply (Real.GammaSeq_tendsto_Gamma x).congr'
    exact Eventually.of_forall fun n => (eulerApproximant_eq_GammaSeq x n).symm
  have hGammaEq : Gamma x = Real.Gamma x :=
    tendsto_nhds_unique (hGamma x hx) hEulerReal
  have hGamma0 : Gamma x ≠ 0 := by
    rw [hGammaEq]
    exact Real.Gamma_ne_zero hx
  refine ⟨x * Gamma x, mul_ne_zero hx0 hGamma0, ?_, ?_⟩
  · unfold HasProductFromOne
    have hbase :
        Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hrpow :
        Tendsto (fun n : ℕ => Real.rpow (1 + 1 / (n : ℝ)) x)
          atTop (𝓝 1) := by
      have h :=
        hbase.rpow_const (p := x) (Or.inl one_ne_zero)
      simpa [Real.rpow_eq_pow] using h
    have hmodel :
        Tendsto
          (fun n : ℕ =>
            x * eulerApproximant x n *
              Real.rpow (1 + 1 / (n : ℝ)) x)
          atTop (𝓝 (x * Gamma x)) := by
      convert (tendsto_const_nhds.mul (hGamma x hx)).mul hrpow using 1 <;> ring
    apply hmodel.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact (partialProduct_eq_euler_mul x n hn hx).symm
  · field_simp

/--
Source: `proof_gap/exercise_3105_2/6.txt`; this is the explicit-factor form
of the preceding product statement.
-/
theorem gap6 (Gamma : ℝ → ℝ)
    (hGamma :
      ∀ x : ℝ, admissible x →
        Tendsto (eulerApproximant x) atTop (𝓝 (Gamma x))) :
    ∀ x : ℝ, admissible x →
      ∃ L : ℝ,
        L ≠ 0 ∧
        HasProductFromOne
          (fun n =>
            Real.rpow (1 + 1 / (n : ℝ)) x / (1 + x / n)) L ∧
        Gamma x = (1 / x) * L := by
  intro x hx
  obtain ⟨L, hL, hpL, hGL⟩ := gap5 Gamma hGamma x hx
  refine ⟨L, hL, ?_, hGL⟩
  change HasProductFromOne (p x) L
  exact hpL

end

end ProofGap.Exercise3105_2
