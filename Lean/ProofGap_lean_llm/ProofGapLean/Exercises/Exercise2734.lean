import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity
import Mathlib.Order.Filter.Tendsto

namespace ProofGap.Exercise2734

noncomputable section

open Filter

def term (x y : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (|x| ^ (n ^ 2) + |y| ^ (n ^ 2)) (1 / (n : ℝ))

def normalizedFactor (x y : ℝ) (n : ℕ) : ℝ :=
  let m := max |x| |y|
  Real.rpow ((|x| / m) ^ (n ^ 2) + (|y| / m) ^ (n ^ 2)) (1 / (n : ℝ))

def rootMagnitude (x y : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (term x y n) (1 / (n : ℝ))

private theorem private_rpow_pow_div (a : ℝ) (ha : 0 < a) (p q : ℕ)
    (hq : 1 ≤ q) :
    Real.rpow (a ^ p) (1 / (q : ℝ)) =
      Real.rpow a ((p : ℝ) / (q : ℝ)) := by
  have hnat : Real.rpow a (p : ℝ) = a ^ p := Real.rpow_natCast a p
  calc
    Real.rpow (a ^ p) (1 / (q : ℝ)) =
        Real.rpow (Real.rpow a (p : ℝ)) (1 / (q : ℝ)) :=
      congrArg (fun z : ℝ => Real.rpow z (1 / (q : ℝ))) hnat.symm
    _ = Real.rpow a ((p : ℝ) * (1 / (q : ℝ))) := by
      exact (Real.rpow_mul (le_of_lt ha) (p : ℝ) (1 / (q : ℝ))).symm
    _ = Real.rpow a ((p : ℝ) / (q : ℝ)) := by
      congr 1
      ring

private theorem private_normalizedFactor_bounds (x y : ℝ)
    (hm : 0 < max |x| |y|) (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ normalizedFactor x y n ∧
      normalizedFactor x y n ≤ Real.rpow 2 (1 / (n : ℝ)) ∧
      normalizedFactor x y n ≤ 2 := by
  let m : ℝ := max |x| |y|
  have hm0 : 0 ≤ m := le_of_lt hm
  have hmne : m ≠ 0 := ne_of_gt hm
  have hxn : 0 ≤ |x| / m := div_nonneg (abs_nonneg x) hm0
  have hyn : 0 ≤ |y| / m := div_nonneg (abs_nonneg y) hm0
  have hxl : |x| / m ≤ 1 := (div_le_one hm).2 (le_max_left |x| |y|)
  have hyl : |y| / m ≤ 1 := (div_le_one hm).2 (le_max_right |x| |y|)
  have hxpow0 : 0 ≤ (|x| / m) ^ (n ^ 2) := pow_nonneg hxn _
  have hypow0 : 0 ≤ (|y| / m) ^ (n ^ 2) := pow_nonneg hyn _
  have hxpow1 : (|x| / m) ^ (n ^ 2) ≤ 1 := pow_le_one₀ hxn hxl
  have hypow1 : (|y| / m) ^ (n ^ 2) ≤ 1 := pow_le_one₀ hyn hyl
  have hs0 : 0 ≤ (|x| / m) ^ (n ^ 2) + (|y| / m) ^ (n ^ 2) :=
    add_nonneg hxpow0 hypow0
  have hs2 : (|x| / m) ^ (n ^ 2) + (|y| / m) ^ (n ^ 2) ≤ 2 := by
    linarith
  have hs1 : 1 ≤ (|x| / m) ^ (n ^ 2) + (|y| / m) ^ (n ^ 2) := by
    rcases le_total |x| |y| with hxy | hyx
    · have hm_eq : m = |y| := max_eq_right hxy
      have hyne : |y| ≠ 0 := by
        intro hy0
        exact hmne (hm_eq.trans hy0)
      have hydiv : |y| / m = 1 := by
        rw [hm_eq, div_self hyne]
      rw [hydiv, one_pow]
      linarith
    · have hm_eq : m = |x| := max_eq_left hyx
      have hxne : |x| ≠ 0 := by
        intro hx0
        exact hmne (hm_eq.trans hx0)
      have hxdiv : |x| / m = 1 := by
        rw [hm_eq, div_self hxne]
      rw [hxdiv, one_pow]
      linarith
  have hnreal : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have he0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have he1 : 1 / (n : ℝ) ≤ 1 :=
    (div_le_one hnreal).2 (by exact_mod_cast hn)
  have hlo : 1 ≤ Real.rpow
      ((|x| / m) ^ (n ^ 2) + (|y| / m) ^ (n ^ 2))
      (1 / (n : ℝ)) := by
    simpa using Real.one_le_rpow hs1 he0
  have hup : Real.rpow
      ((|x| / m) ^ (n ^ 2) + (|y| / m) ^ (n ^ 2))
      (1 / (n : ℝ)) ≤ Real.rpow 2 (1 / (n : ℝ)) :=
    Real.rpow_le_rpow hs0 hs2 he0
  have htwo : Real.rpow 2 (1 / (n : ℝ)) ≤ 2 := by
    calc
      Real.rpow 2 (1 / (n : ℝ)) ≤ Real.rpow 2 1 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) he1
      _ = 2 := by norm_num
  have hbounds :
      1 ≤ Real.rpow
          ((|x| / m) ^ (n ^ 2) + (|y| / m) ^ (n ^ 2))
          (1 / (n : ℝ)) ∧
        Real.rpow
            ((|x| / m) ^ (n ^ 2) + (|y| / m) ^ (n ^ 2))
            (1 / (n : ℝ)) ≤ Real.rpow 2 (1 / (n : ℝ)) ∧
        Real.rpow
            ((|x| / m) ^ (n ^ 2) + (|y| / m) ^ (n ^ 2))
            (1 / (n : ℝ)) ≤ 2 :=
    ⟨hlo, hup, hup.trans htwo⟩
  simpa [normalizedFactor, m] using hbounds

private theorem private_tendsto_two_rpow_inv_succ :
    Tendsto (fun n : ℕ => Real.rpow 2 (1 / ((n + 1 : ℕ) : ℝ)))
      atTop (nhds 1) := by
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp hcast
  have hinv_succ : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ))
      atTop (nhds 0) := hinv.comp hshift
  have hcont : Tendsto (fun z : ℝ => Real.rpow 2 z) (nhds 0) (nhds 1) := by
    have hmul : Tendsto (fun z : ℝ => Real.log 2 * z)
        (nhds 0) (nhds 0) := by
      simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => Real.log 2)
            (nhds 0) (nhds (Real.log 2))).mul
          (tendsto_id : Tendsto (fun z : ℝ => z) (nhds 0) (nhds 0)))
    have hexp : Tendsto (fun z : ℝ => Real.exp (Real.log 2 * z))
        (nhds 0) (nhds 1) := by
      have hexp_at_zero :
          Tendsto (fun w : ℝ => Real.exp w) (nhds 0)
            (nhds (Real.exp 0)) := by
        exact Real.continuous_exp.continuousAt
      simpa [Function.comp_def] using (hexp_at_zero.comp hmul)
    simpa [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] using hexp
  exact hcont.comp hinv_succ

theorem gap1 (x y : ℝ) (hxy : 0 < max |x| |y|) :
    ∀ n : ℕ, 1 ≤ n →
      term x y n = normalizedFactor x y n * (max |x| |y|) ^ n := by
  intro n hn
  let m : ℝ := max |x| |y|
  have hm : 0 < m := hxy
  have hmne : m ≠ 0 := ne_of_gt hm
  have hx : |x| = (|x| / m) * m := by
    field_simp
  have hy : |y| = (|y| / m) * m := by
    field_simp
  have hs0 :
      0 ≤ (|x| / m) ^ (n ^ 2) + (|y| / m) ^ (n ^ 2) :=
    add_nonneg (pow_nonneg (div_nonneg (abs_nonneg x) (le_of_lt hm)) _)
      (pow_nonneg (div_nonneg (abs_nonneg y) (le_of_lt hm)) _)
  have hbase :
      |x| ^ (n ^ 2) + |y| ^ (n ^ 2) =
        ((|x| / m) ^ (n ^ 2) + (|y| / m) ^ (n ^ 2)) * m ^ (n ^ 2) := by
    calc
      |x| ^ (n ^ 2) + |y| ^ (n ^ 2) =
          ((|x| / m) * m) ^ (n ^ 2) + ((|y| / m) * m) ^ (n ^ 2) := by
            rw [← hx, ← hy]
      _ = ((|x| / m) ^ (n ^ 2) + (|y| / m) ^ (n ^ 2)) * m ^ (n ^ 2) := by
            rw [mul_pow, mul_pow]
            ring
  simp only [term, normalizedFactor]
  change Real.rpow (|x| ^ (n ^ 2) + |y| ^ (n ^ 2)) (1 / (n : ℝ)) =
    Real.rpow ((|x| / m) ^ (n ^ 2) + (|y| / m) ^ (n ^ 2))
      (1 / (n : ℝ)) * m ^ n
  rw [hbase]
  have hmul :
      Real.rpow
          (((|x| / m) ^ (n ^ 2) + (|y| / m) ^ (n ^ 2)) * m ^ (n ^ 2))
          (1 / (n : ℝ)) =
        Real.rpow ((|x| / m) ^ (n ^ 2) + (|y| / m) ^ (n ^ 2))
            (1 / (n : ℝ)) *
          Real.rpow (m ^ (n ^ 2)) (1 / (n : ℝ)) :=
    Real.mul_rpow hs0 (pow_nonneg (le_of_lt hm) _)
  calc
    Real.rpow
        (((|x| / m) ^ (n ^ 2) + (|y| / m) ^ (n ^ 2)) * m ^ (n ^ 2))
        (1 / (n : ℝ)) =
      Real.rpow ((|x| / m) ^ (n ^ 2) + (|y| / m) ^ (n ^ 2))
          (1 / (n : ℝ)) *
        Real.rpow (m ^ (n ^ 2)) (1 / (n : ℝ)) := hmul
    _ = Real.rpow ((|x| / m) ^ (n ^ 2) + (|y| / m) ^ (n ^ 2))
          (1 / (n : ℝ)) *
        Real.rpow m (((n ^ 2 : ℕ) : ℝ) / (n : ℝ)) := by
          rw [private_rpow_pow_div m hm (n ^ 2) n hn]
    _ = Real.rpow ((|x| / m) ^ (n ^ 2) + (|y| / m) ^ (n ^ 2))
          (1 / (n : ℝ)) * m ^ n := by
          have hn0 : (n : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt hn)
          have he : ((n ^ 2 : ℕ) : ℝ) / (n : ℝ) = (n : ℝ) := by
            push_cast
            field_simp
          have hnat : Real.rpow m (n : ℝ) = m ^ n :=
            Real.rpow_natCast m n
          rw [he]
          exact congrArg
            (fun z : ℝ =>
              Real.rpow
                  ((|x| / m) ^ (n ^ 2) + (|y| / m) ^ (n ^ 2))
                  (1 / (n : ℝ)) * z)
            hnat

theorem gap2 (x y : ℝ) :
    Tendsto (fun n : ℕ => rootMagnitude x y (n + 1))
      atTop (nhds (max |x| |y|)) := by
  let m : ℝ := max |x| |y|
  have hm0 : 0 ≤ m := le_trans (abs_nonneg x) (le_max_left |x| |y|)
  by_cases hmz : m = 0
  · have hxabs : |x| = 0 := by
      apply le_antisymm
      · simpa [m, hmz] using (le_max_left |x| |y|)
      · exact abs_nonneg x
    have hyabs : |y| = 0 := by
      apply le_antisymm
      · simpa [m, hmz] using (le_max_right |x| |y|)
      · exact abs_nonneg y
    have hx : x = 0 := abs_eq_zero.mp hxabs
    have hy : y = 0 := abs_eq_zero.mp hyabs
    subst x
    subst y
    have hzero :
        (fun n : ℕ => rootMagnitude 0 0 (n + 1)) =
          (fun _ : ℕ => (0 : ℝ)) := by
      funext n
      have hkNat : n + 1 ≠ 0 := Nat.succ_ne_zero n
      have hkReal : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by
        exact_mod_cast hkNat
      have he : 1 / (((n + 1 : ℕ) : ℝ)) ≠ 0 := one_div_ne_zero hkReal
      have hpow : (n + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hkNat
      have hz :
          Real.rpow (0 : ℝ) (1 / (((n + 1 : ℕ) : ℝ))) = 0 := by
        change (0 : ℝ) ^ (1 / (((n + 1 : ℕ) : ℝ))) = 0
        exact Real.zero_rpow he
      simp only [rootMagnitude, term, abs_zero, zero_pow hpow, zero_add]
      calc
        Real.rpow
            (Real.rpow (0 : ℝ) (1 / (((n + 1 : ℕ) : ℝ))))
            (1 / (((n + 1 : ℕ) : ℝ))) =
          Real.rpow (0 : ℝ) (1 / (((n + 1 : ℕ) : ℝ))) := by
            exact congrArg
              (fun z : ℝ => Real.rpow z (1 / (((n + 1 : ℕ) : ℝ)))) hz
        _ = 0 := hz
    rw [hzero]
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  · have hm : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hmz)
    have hlower : ∀ n : ℕ, m ≤ rootMagnitude x y (n + 1) := by
      intro n
      let k := n + 1
      have hk : 1 ≤ k := by omega
      have hb := private_normalizedFactor_bounds x y hm k hk
      have ht := gap1 x y hm k hk
      have hterm : m ^ k ≤ term x y k := by
        rw [ht]
        change m ^ k ≤ normalizedFactor x y k * m ^ k
        simpa using
          mul_le_mul_of_nonneg_right hb.1 (pow_nonneg hm0 k)
      have hp :
          Real.rpow (m ^ k) (1 / (k : ℝ)) ≤
            Real.rpow (term x y k) (1 / (k : ℝ)) :=
        Real.rpow_le_rpow (pow_nonneg hm0 k) hterm
          (by positivity : 0 ≤ (1 / (k : ℝ)))
      have hmk : Real.rpow (m ^ k) (1 / (k : ℝ)) = m := by
        rw [private_rpow_pow_div m hm k k hk]
        have hk0 : (k : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt hk)
        rw [div_self hk0]
        norm_num
      change m ≤ Real.rpow (term x y k) (1 / (k : ℝ))
      calc
        m = Real.rpow (m ^ k) (1 / (k : ℝ)) := hmk.symm
        _ ≤ Real.rpow (term x y k) (1 / (k : ℝ)) := hp
    have hupper : ∀ n : ℕ,
        rootMagnitude x y (n + 1) ≤
          Real.rpow 2 (1 / ((n + 1 : ℕ) : ℝ)) * m := by
      intro n
      let k := n + 1
      have hk : 1 ≤ k := by omega
      have hb := private_normalizedFactor_bounds x y hm k hk
      have ht := gap1 x y hm k hk
      have hterm : term x y k ≤ 2 * m ^ k := by
        rw [ht]
        change normalizedFactor x y k * m ^ k ≤ 2 * m ^ k
        exact mul_le_mul_of_nonneg_right hb.2.2 (pow_nonneg hm0 k)
      have hterm0 : 0 ≤ term x y k := by
        unfold term
        apply Real.rpow_nonneg
        exact add_nonneg
          (pow_nonneg (abs_nonneg x) (k ^ 2))
          (pow_nonneg (abs_nonneg y) (k ^ 2))
      have hp :
          Real.rpow (term x y k) (1 / (k : ℝ)) ≤
            Real.rpow (2 * m ^ k) (1 / (k : ℝ)) :=
        Real.rpow_le_rpow hterm0 hterm
          (by positivity : 0 ≤ (1 / (k : ℝ)))
      have hmk : Real.rpow (m ^ k) (1 / (k : ℝ)) = m := by
        rw [private_rpow_pow_div m hm k k hk]
        have hk0 : (k : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt hk)
        rw [div_self hk0]
        norm_num
      change Real.rpow (term x y k) (1 / (k : ℝ)) ≤
        Real.rpow 2 (1 / (k : ℝ)) * m
      calc
        Real.rpow (term x y k) (1 / (k : ℝ)) ≤
            Real.rpow (2 * m ^ k) (1 / (k : ℝ)) := hp
        _ = Real.rpow 2 (1 / (k : ℝ)) *
            Real.rpow (m ^ k) (1 / (k : ℝ)) :=
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (pow_nonneg hm0 k)
        _ = Real.rpow 2 (1 / (k : ℝ)) * m := by rw [hmk]
    have hu : Tendsto
        (fun n : ℕ => Real.rpow 2 (1 / ((n + 1 : ℕ) : ℝ)) * m)
        atTop (nhds m) := by
      simpa using private_tendsto_two_rpow_inv_succ.mul_const m
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hu
      (Filter.Eventually.of_forall hlower)
      (Filter.Eventually.of_forall hupper)

theorem gap3 (x y : ℝ) (hxy : max |x| |y| < 1) :
    Summable (fun n : ℕ => |term x y (n + 1)|) := by
  let m : ℝ := max |x| |y|
  have hm0 : 0 ≤ m := le_trans (abs_nonneg x) (le_max_left |x| |y|)
  by_cases hmz : m = 0
  · have hxabs : |x| = 0 := by
      apply le_antisymm
      · simpa [m, hmz] using (le_max_left |x| |y|)
      · exact abs_nonneg x
    have hyabs : |y| = 0 := by
      apply le_antisymm
      · simpa [m, hmz] using (le_max_right |x| |y|)
      · exact abs_nonneg y
    have hx : x = 0 := abs_eq_zero.mp hxabs
    have hy : y = 0 := abs_eq_zero.mp hyabs
    subst x
    subst y
    have hzero :
        (fun n : ℕ => |term 0 0 (n + 1)|) =
          (fun _ : ℕ => (0 : ℝ)) := by
      funext n
      have hkNat : n + 1 ≠ 0 := Nat.succ_ne_zero n
      have hkReal : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by
        exact_mod_cast hkNat
      have he : 1 / (((n + 1 : ℕ) : ℝ)) ≠ 0 := one_div_ne_zero hkReal
      have hpow : (n + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hkNat
      have hz :
          Real.rpow (0 : ℝ) (1 / (((n + 1 : ℕ) : ℝ))) = 0 := by
        change (0 : ℝ) ^ (1 / (((n + 1 : ℕ) : ℝ))) = 0
        exact Real.zero_rpow he
      simp only [term, abs_zero, zero_pow hpow, zero_add]
      calc
        |Real.rpow (0 : ℝ) (1 / (((n + 1 : ℕ) : ℝ)))| = |(0 : ℝ)| :=
          congrArg (fun z : ℝ => |z|) hz
        _ = 0 := abs_zero
    rw [hzero]
    exact summable_zero
  · have hm : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hmz)
    have hmnorm : ‖m‖ < 1 := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hm0, m] using hxy
    have hgeo : Summable (fun n : ℕ => m ^ n) :=
      summable_geometric_of_norm_lt_one hmnorm
    have hmajorant : Summable (fun n : ℕ => 2 * m ^ (n + 1)) := by
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
        hgeo.mul_left (2 * m)
    apply Summable.of_nonneg_of_le (fun n => abs_nonneg (term x y (n + 1)))
      (fun n => ?_) hmajorant
    have hk : 1 ≤ n + 1 := by omega
    have hb := private_normalizedFactor_bounds x y hm (n + 1) hk
    have ht := gap1 x y hm (n + 1) hk
    have hterm0 : 0 ≤ term x y (n + 1) := by
      unfold term
      apply Real.rpow_nonneg
      exact add_nonneg
        (pow_nonneg (abs_nonneg x) ((n + 1) ^ 2))
        (pow_nonneg (abs_nonneg y) ((n + 1) ^ 2))
    rw [abs_of_nonneg hterm0, ht]
    change normalizedFactor x y (n + 1) * m ^ (n + 1) ≤
      2 * m ^ (n + 1)
    exact mul_le_mul_of_nonneg_right hb.2.2 (pow_nonneg hm0 (n + 1))

theorem gap4 (x y : ℝ) (hxy : 1 < max |x| |y|) :
    ¬ Summable (fun n : ℕ => term x y (n + 1)) := by
  intro hs
  let m : ℝ := max |x| |y|
  have hm : 0 < m := lt_trans zero_lt_one hxy
  have hz := hs.tendsto_atTop_zero
  have hev : ∀ᶠ n : ℕ in atTop, term x y (n + 1) < 1 :=
    (tendsto_order.1 hz).2 1 zero_lt_one
  rcases hev.exists with ⟨n, hn⟩
  have hk : 1 ≤ n + 1 := by omega
  have hb := private_normalizedFactor_bounds x y hm (n + 1) hk
  have ht := gap1 x y hm (n + 1) hk
  have hpow : 1 ≤ m ^ (n + 1) := one_le_pow₀ (le_of_lt hxy)
  have hterm : m ^ (n + 1) ≤ term x y (n + 1) := by
    rw [ht]
    change m ^ (n + 1) ≤ normalizedFactor x y (n + 1) * m ^ (n + 1)
    simpa using
      mul_le_mul_of_nonneg_right hb.1 (pow_nonneg (le_of_lt hm) (n + 1))
  linarith

theorem gap5 (x y : ℝ) (hxy : max |x| |y| = 1) :
    Tendsto (fun n : ℕ => term x y (n + 1)) atTop (nhds 1) := by
  have hm : 0 < max |x| |y| := by rw [hxy]; norm_num
  have hlower : ∀ n : ℕ, 1 ≤ term x y (n + 1) := by
    intro n
    have hk : 1 ≤ n + 1 := by omega
    have hb := private_normalizedFactor_bounds x y hm (n + 1) hk
    rw [gap1 x y hm (n + 1) hk, hxy, one_pow, mul_one]
    exact hb.1
  have hupper : ∀ n : ℕ,
      term x y (n + 1) ≤ Real.rpow 2 (1 / ((n + 1 : ℕ) : ℝ)) := by
    intro n
    have hk : 1 ≤ n + 1 := by omega
    have hb := private_normalizedFactor_bounds x y hm (n + 1) hk
    rw [gap1 x y hm (n + 1) hk, hxy, one_pow, mul_one]
    exact hb.2.1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds private_tendsto_two_rpow_inv_succ
    (Filter.Eventually.of_forall hlower)
    (Filter.Eventually.of_forall hupper)

theorem gap6 (x y : ℝ) (hxy : max |x| |y| = 1) :
    ¬ Summable (fun n : ℕ => term x y (n + 1)) := by
  intro hs
  have hz := hs.tendsto_atTop_zero
  have hone := gap5 x y hxy
  have heq : (0 : ℝ) = 1 := tendsto_nhds_unique hz hone
  norm_num at heq

theorem gap7 (x y : ℝ) :
    max |x| |y| < 1 ↔ Summable (fun n : ℕ => term x y (n + 1)) := by
  constructor
  · intro h
    apply Summable.of_norm
    simpa [Real.norm_eq_abs] using gap3 x y h
  · intro hs
    by_contra hnot
    have hmge : 1 ≤ max |x| |y| := le_of_not_gt hnot
    rcases eq_or_lt_of_le hmge with heq | hgt
    · exact gap6 x y heq.symm hs
    · exact gap4 x y hgt hs

end

end ProofGap.Exercise2734
