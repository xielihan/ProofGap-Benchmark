import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.PSeries

open scoped BigOperators

namespace ProofGap.Exercise2598

noncomputable section

def wallisBase (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n,
    (2 * ((j + 1 : ℕ) : ℝ) - 1) / (2 * ((j + 1 : ℕ) : ℝ))

def term (p : ℝ) (n : ℕ) : ℝ := Real.rpow (wallisBase n) p

def raabeRatio (p : ℝ) (n : ℕ) : ℝ :=
  term p n / term p (n + 1)

def explicitRatio (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 1)) p

def raabeQuantity (p : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * (raabeRatio p n - 1)

def normalizedIncrement (p : ℝ) (n : ℕ) : ℝ :=
  (explicitRatio p n - 1) / (1 / (n : ℝ))

private theorem wallisBase_succ (n : ℕ) :
    wallisBase (n + 1) = wallisBase n *
      ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) := by
  rw [wallisBase, Finset.prod_range_succ]
  unfold wallisBase
  congr 1
  push_cast
  ring

private theorem wallisBase_pos (n : ℕ) : 0 < wallisBase n := by
  unfold wallisBase
  apply Finset.prod_pos
  intro j hj
  apply div_pos
  · have hj0 : (0 : ℝ) ≤ j := by positivity
    push_cast
    nlinarith
  · positivity

private theorem wallisBase_le_one (n : ℕ) : wallisBase n ≤ 1 := by
  unfold wallisBase
  apply Finset.prod_le_one
  · intro j hj
    apply (div_pos ?_ ?_).le
    · have hj0 : (0 : ℝ) ≤ j := by positivity
      push_cast
      nlinarith
    · positivity
  · intro j hj
    apply (div_le_one (by positivity)).2
    norm_num

private theorem wallisBase_sq_mul_W (n : ℕ) :
    wallisBase n ^ 2 * (((2 : ℝ) * n + 1) * Real.Wallis.W n) = 1 := by
  induction n with
  | zero => norm_num [wallisBase, Real.Wallis.W]
  | succ n ih =>
      rw [wallisBase_succ, Real.Wallis.W_succ]
      calc
        (wallisBase n * ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2))) ^ 2 *
            ((2 * ((n + 1 : ℕ) : ℝ) + 1) *
              (Real.Wallis.W n *
                ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 1) *
                  ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3))))) =
            wallisBase n ^ 2 * (((2 : ℝ) * n + 1) * Real.Wallis.W n) := by
          push_cast
          field_simp
          ring
        _ = 1 := ih

private theorem wallisBase_sq_eq_inv (n : ℕ) :
    wallisBase n ^ 2 = 1 / (((2 : ℝ) * n + 1) * Real.Wallis.W n) := by
  apply (eq_div_iff ?_).2
  · exact wallisBase_sq_mul_W n
  · exact ne_of_gt (mul_pos (by positivity) (Real.Wallis.W_pos n))

private theorem half_le_W (n : ℕ) : (1 / 2 : ℝ) ≤ Real.Wallis.W n := by
  have hratio : (1 / 2 : ℝ) ≤ ((2 : ℝ) * n + 1) / (2 * n + 2) := by
    apply (le_div_iff₀ (by positivity)).2
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have hpi : (1 : ℝ) ≤ Real.pi / 2 := by
    nlinarith [Real.pi_gt_three]
  calc
    (1 / 2 : ℝ) ≤ (((2 : ℝ) * n + 1) / (2 * n + 2)) * 1 := by
      simpa using hratio
    _ ≤ (((2 : ℝ) * n + 1) / (2 * n + 2)) * (Real.pi / 2) :=
      mul_le_mul_of_nonneg_left hpi (by positivity)
    _ ≤ Real.Wallis.W n := Real.Wallis.le_W n

private theorem W_le_two (n : ℕ) : Real.Wallis.W n ≤ 2 :=
  (Real.Wallis.W_le n).trans (by nlinarith [Real.pi_lt_four])

private theorem wallisBase_sq_le_inv (n : ℕ) (hn : 1 ≤ n) :
    wallisBase n ^ 2 ≤ 1 / (n : ℝ) := by
  have hD : (n : ℝ) ≤ ((2 : ℝ) * n + 1) * Real.Wallis.W n := by
    calc
      (n : ℝ) ≤ ((2 : ℝ) * n + 1) * (1 / 2 : ℝ) := by nlinarith
      _ ≤ ((2 : ℝ) * n + 1) * Real.Wallis.W n :=
        mul_le_mul_of_nonneg_left (half_le_W n) (by positivity)
  rw [wallisBase_sq_eq_inv]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hD

private theorem inv_six_mul_le_wallisBase_sq (n : ℕ) (hn : 1 ≤ n) :
    1 / (6 * (n : ℝ)) ≤ wallisBase n ^ 2 := by
  have hDpos : 0 < ((2 : ℝ) * n + 1) * Real.Wallis.W n :=
    mul_pos (by positivity) (Real.Wallis.W_pos n)
  have hD : ((2 : ℝ) * n + 1) * Real.Wallis.W n ≤ 6 * n := by
    calc
      ((2 : ℝ) * n + 1) * Real.Wallis.W n ≤ ((2 : ℝ) * n + 1) * 2 :=
        mul_le_mul_of_nonneg_left (W_le_two n) (by positivity)
      _ ≤ 6 * n := by
        have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
  rw [wallisBase_sq_eq_inv]
  exact one_div_le_one_div_of_le hDpos hD

private theorem rpow_eq_sq_rpow_half (x p : ℝ) (hx : 0 < x) :
    Real.rpow x p = Real.rpow (x ^ 2) (p / 2) := by
  calc
    Real.rpow x p = Real.rpow x ((2 : ℝ) * (p / 2)) := by
      congr 1
      ring
    _ = Real.rpow (Real.rpow x (2 : ℝ)) (p / 2) :=
      Real.rpow_mul hx.le 2 (p / 2)
    _ = Real.rpow (x ^ 2) (p / 2) := by
      congr 1
      exact Real.rpow_natCast x 2

private theorem inv_rpow_eq_neg_rpow (x e : ℝ) (hx : 0 ≤ x) :
    Real.rpow (1 / x) e = Real.rpow x (-e) := by
  calc
    Real.rpow (1 / x) e = Inv.inv (Real.rpow x e) := by
      simpa [one_div] using Real.inv_rpow hx e
    _ = Real.rpow x (-e) := (Real.rpow_neg hx e).symm

private theorem inv_six_mul_rpow (x e : ℝ) (hx : 0 ≤ x) :
    Real.rpow (1 / (6 * x)) e =
      Real.rpow 6 (-e) * Real.rpow x (-e) := by
  calc
    Real.rpow (1 / (6 * x)) e = Real.rpow (6 * x) (-e) :=
      inv_rpow_eq_neg_rpow (6 * x) e (by positivity)
    _ = Real.rpow 6 (-e) * Real.rpow x (-e) :=
      Real.mul_rpow (by norm_num) hx

private theorem summable_term_of_two_lt (p : ℝ) (hp : 2 < p) :
    Summable (term p) := by
  have hpseries : Summable (fun n : ℕ ↦ Real.rpow (n : ℝ) (-p / 2)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hmajorant : Summable (fun n : ℕ ↦
      Real.rpow ((n + 1 : ℕ) : ℝ) (-p / 2)) := by
    simpa using (summable_nat_add_iff 1).mpr hpseries
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_nonneg_of_le (f := fun n : ℕ ↦
    Real.rpow ((n + 1 : ℕ) : ℝ) (-p / 2))
  · intro n
    exact Real.rpow_nonneg (wallisBase_pos (n + 1)).le p
  · intro n
    let m := n + 1
    have hm : 1 ≤ m := by omega
    have hsq := wallisBase_sq_le_inv m hm
    have hrpow := Real.rpow_le_rpow (sq_nonneg (wallisBase m)) hsq
      (show 0 ≤ p / 2 by linarith)
    calc
      term p (n + 1) = Real.rpow (wallisBase m ^ 2) (p / 2) := by
        unfold term
        exact rpow_eq_sq_rpow_half (wallisBase m) p (wallisBase_pos m)
      _ ≤ Real.rpow (1 / (m : ℝ)) (p / 2) := hrpow
      _ = Real.rpow (m : ℝ) (-p / 2) := by
        convert inv_rpow_eq_neg_rpow (m : ℝ) (p / 2) (by positivity) using 1 <;> ring
      _ = Real.rpow ((n + 1 : ℕ) : ℝ) (-p / 2) := by rfl
  · exact hmajorant

theorem gap1
    (a : ℕ → ℝ) (p : ℝ)
    (ha : ∀ n, a n = term p n) :
    ∀ n, a n / a (n + 1) = explicitRatio p n := by
  intro n
  rw [ha n, ha (n + 1)]
  unfold term explicitRatio
  rw [wallisBase_succ]
  have hw : 0 < wallisBase n := wallisBase_pos n
  have hf : 0 < (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) := by positivity
  have hmul :
      Real.rpow (wallisBase n * ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2))) p =
        Real.rpow (wallisBase n) p *
          Real.rpow ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) p :=
    Real.mul_rpow hw.le hf.le
  have hrecip : (2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 1) =
      1 / ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) := by
    field_simp
  have hdiv := Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) hf.le p
  have hrecipPow :
      Real.rpow (1 / ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2))) p =
        1 / Real.rpow ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) p := by
    calc
      Real.rpow (1 / ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2))) p =
          Real.rpow 1 p /
            Real.rpow ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) p := hdiv
      _ = 1 / Real.rpow ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) p := by
        congr 1
        exact Real.one_rpow p
  calc
    Real.rpow (wallisBase n) p /
        Real.rpow (wallisBase n * ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2))) p =
        Real.rpow (wallisBase n) p /
          (Real.rpow (wallisBase n) p *
            Real.rpow ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) p) :=
      congrArg (fun z : ℝ ↦ Real.rpow (wallisBase n) p / z) hmul
    _ = 1 / Real.rpow ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) p := by
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hw p),
        ne_of_gt (Real.rpow_pos_of_pos hf p)]
    _ = Real.rpow ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 1)) p := by
      rw [hrecip]
      exact hrecipPow.symm

theorem gap2
    (p : ℝ)
    (hratio : ∀ n, raabeRatio p n = explicitRatio p n) :
    ∀ n, raabeQuantity p n =
      (n : ℝ) * (explicitRatio p n - 1) := by
  intro n
  simp [raabeQuantity, hratio n]

theorem gap3
    (p : ℝ) :
    ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) * (explicitRatio p n - 1) =
        normalizedIncrement p n := by
  intro n hn
  unfold normalizedIncrement
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp

theorem gap4
    (p : ℝ) :
    Tendsto (normalizedIncrement p) atTop (nhds (p / 2)) := by
  let F : ℝ → ℝ := fun t ↦ Real.rpow ((2 + 2 * t) / (2 + t)) p
  have hnum : HasDerivAt (fun t : ℝ ↦ 2 + 2 * t) 2 0 := by
    convert ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul 2).const_add 2 using 1 <;> norm_num
  have hden : HasDerivAt (fun t : ℝ ↦ 2 + t) 1 0 := by
    convert (hasDerivAt_id (𝕜 := ℝ) 0).const_add 2 using 1 <;> norm_num
  have hinner : HasDerivAt (fun t : ℝ ↦ (2 + 2 * t) / (2 + t)) (1 / 2) 0 := by
    convert hnum.div hden (by norm_num) using 1 <;> norm_num
  have hF : HasDerivAt F (p / 2) 0 := by
    dsimp [F]
    convert hinner.rpow_const (Or.inl (by norm_num)) using 1 <;> norm_num <;> ring
  have hinv : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop
      (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_one_div_atTop_nhds_zero_nat,
      Filter.eventually_atTop.2 ⟨1, fun n hn ↦ by
        show 0 < 1 / (n : ℝ)
        positivity⟩⟩
  have hslope := hF.tendsto_slope_zero_right.comp hinv
  apply hslope.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hratio : (2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 1) =
      (2 + 2 * (1 / (n : ℝ))) / (2 + 1 / (n : ℝ)) := by
    field_simp
  unfold normalizedIncrement explicitRatio
  dsimp [F]
  rw [hratio]
  norm_num
  ring

theorem gap5
    (p : ℝ)
    (hidentity : ∀ n : ℕ, 1 ≤ n →
      raabeQuantity p n = normalizedIncrement p n)
    (hlimit : Tendsto (normalizedIncrement p) atTop (nhds (p / 2))) :
    Tendsto (raabeQuantity p) atTop (nhds (p / 2)) := by
  apply hlimit.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact (hidentity n hn).symm

theorem gap6
    (p : ℝ)
    (hraabe : Tendsto (raabeQuantity p) atTop (nhds (p / 2))) :
    p / 2 > 1 → Summable (term p) := by
  intro hp
  exact summable_term_of_two_lt p (by linarith)

theorem gap7 (p : ℝ) :
    p / 2 > 1 ↔ p > 2 := by constructor <;> intro h <;> linarith

theorem gap8 (p : ℝ) :
    p > 2 ↔ Summable (term p) := by
  constructor
  · exact summable_term_of_two_lt p
  · intro hsum
    by_contra hp
    have hp_le : p ≤ 2 := le_of_not_gt hp
    by_cases hp_nonpos : p ≤ 0
    · have hevent : ∀ᶠ n in atTop, term p n < (1 / 2 : ℝ) :=
        (tendsto_order.mp hsum.tendsto_atTop_zero).2 (1 / 2 : ℝ) (by norm_num)
      obtain ⟨n, hn⟩ := hevent.exists
      have hge : (1 : ℝ) ≤ term p n := by
        unfold term
        exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
          (wallisBase_pos n) (wallisBase_le_one n) hp_nonpos
      linarith
    · have hp_pos : 0 < p := lt_of_not_ge hp_nonpos
      let e : ℝ := p / 2
      let c : ℝ := Real.rpow 6 (-e)
      have he_pos : 0 < e := by dsimp [e]; linarith
      have hc_pos : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
      have hshift : Summable (fun n : ℕ ↦ term p (n + 1)) :=
        (summable_nat_add_iff 1).mpr hsum
      have hscaled : Summable (fun n : ℕ ↦
          c * Real.rpow ((n + 1 : ℕ) : ℝ) (-e)) := by
        apply Summable.of_nonneg_of_le (f := fun n : ℕ ↦ term p (n + 1))
        · intro n
          exact mul_nonneg hc_pos.le (Real.rpow_nonneg (by positivity) _)
        · intro n
          let m := n + 1
          have hm : 1 ≤ m := by omega
          have hsq := inv_six_mul_le_wallisBase_sq m hm
          have hrpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 1 / (6 * m))
            hsq he_pos.le
          calc
            c * Real.rpow ((n + 1 : ℕ) : ℝ) (-e) =
                Real.rpow (1 / (6 * (m : ℝ))) e := by
              dsimp [c]
              exact (inv_six_mul_rpow (m : ℝ) e (by positivity)).symm
            _ ≤ Real.rpow (wallisBase m ^ 2) e := hrpow
            _ = term p (n + 1) := by
              dsimp [e, m]
              unfold term
              exact (rpow_eq_sq_rpow_half (wallisBase (n + 1)) p
                (wallisBase_pos (n + 1))).symm
        · exact hshift
      have hpowerShift : Summable (fun n : ℕ ↦
          Real.rpow ((n + 1 : ℕ) : ℝ) (-e)) :=
        (summable_mul_left_iff hc_pos.ne').mp hscaled
      have hpower : Summable (fun n : ℕ ↦ Real.rpow (n : ℝ) (-e)) :=
        (summable_nat_add_iff 1).mp hpowerShift
      have hexponent := Real.summable_nat_rpow.mp hpower
      dsimp [e] at hexponent
      linarith

end

end ProofGap.Exercise2598
