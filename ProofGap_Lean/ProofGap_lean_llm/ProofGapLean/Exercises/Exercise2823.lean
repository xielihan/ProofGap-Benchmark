import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2823

noncomputable section

open Filter
open scoped BigOperators Topology

def coefficient (a : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow a (Real.sqrt n)

def powerTerm (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  coefficient a n * x ^ n

def SeriesConvergesAt (a x : ℝ) : Prop :=
  Summable (fun k : ℕ => powerTerm a (k + 1) x)

def HasConvergenceRadiusOne (a : ℝ) : Prop :=
  (∀ x : ℝ, |x| < 1 → SeriesConvergesAt a x) ∧
    (∀ x : ℝ, 1 < |x| → ¬ SeriesConvergesAt a x)

private theorem coefficient_pos {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 < coefficient a n := by
  exact one_div_pos.mpr (Real.rpow_pos_of_pos ha _)

theorem gap1 :
    ∀ a : ℝ, 0 < a →
      Tendsto
        (fun n : ℕ => |coefficient a (n + 1) / coefficient a (n + 2)|)
        atTop (𝓝 1) := by
  intro a ha
  have hshift1 : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hshift2 : Tendsto (fun n : ℕ => n + 2) atTop atTop :=
    tendsto_add_atTop_nat 2
  have hsqrt1 :
      Tendsto (fun n : ℕ => Real.sqrt (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hshift1)
  have hsqrt2 :
      Tendsto (fun n : ℕ => Real.sqrt (((n + 2 : ℕ) : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hshift2)
  have hden :
      Tendsto
        (fun n : ℕ =>
          Real.sqrt (((n + 2 : ℕ) : ℝ)) +
            Real.sqrt (((n + 1 : ℕ) : ℝ)))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [(tendsto_atTop.1 hsqrt1) b] with n hn
    exact hn.trans
      (le_add_of_nonneg_left (Real.sqrt_nonneg (((n + 2 : ℕ) : ℝ))))
  have hinv :
      Tendsto
        (fun n : ℕ =>
          1 /
            (Real.sqrt (((n + 2 : ℕ) : ℝ)) +
              Real.sqrt (((n + 1 : ℕ) : ℝ))))
        atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hden
  have hdiff :
      Tendsto
        (fun n : ℕ =>
          Real.sqrt (((n + 2 : ℕ) : ℝ)) -
            Real.sqrt (((n + 1 : ℕ) : ℝ)))
        atTop (𝓝 0) := by
    refine hinv.congr' (Eventually.of_forall (fun n => ?_))
    symm
    have hden_pos :
        0 <
          Real.sqrt (((n + 2 : ℕ) : ℝ)) +
            Real.sqrt (((n + 1 : ℕ) : ℝ)) := by
      have : 0 < Real.sqrt (((n + 1 : ℕ) : ℝ)) := by
        positivity
      positivity
    apply (eq_div_iff (ne_of_gt hden_pos)).2
    have hsq2 :
        (Real.sqrt (((n + 2 : ℕ) : ℝ))) ^ 2 =
          ((n + 2 : ℕ) : ℝ) :=
      Real.sq_sqrt (by positivity)
    have hsq1 :
        (Real.sqrt (((n + 1 : ℕ) : ℝ))) ^ 2 =
          ((n + 1 : ℕ) : ℝ) :=
      Real.sq_sqrt (by positivity)
    calc
      (Real.sqrt (((n + 2 : ℕ) : ℝ)) -
            Real.sqrt (((n + 1 : ℕ) : ℝ))) *
          (Real.sqrt (((n + 2 : ℕ) : ℝ)) +
            Real.sqrt (((n + 1 : ℕ) : ℝ))) =
          (Real.sqrt (((n + 2 : ℕ) : ℝ))) ^ 2 -
            (Real.sqrt (((n + 1 : ℕ) : ℝ))) ^ 2 := by ring
      _ = 1 := by
        rw [hsq2, hsq1]
        norm_num
  have hrpow :
      Tendsto
        (fun n : ℕ =>
          Real.rpow a
            (Real.sqrt (((n + 2 : ℕ) : ℝ)) -
              Real.sqrt (((n + 1 : ℕ) : ℝ))))
        atTop (𝓝 1) := by
    simpa using
      (tendsto_const_nhds (x := a)).rpow hdiff (Or.inl ha.ne')
  refine hrpow.congr' (Eventually.of_forall (fun n => ?_))
  symm
  change
    |coefficient a (n + 1) / coefficient a (n + 2)| =
      Real.rpow a
        (Real.sqrt (((n + 2 : ℕ) : ℝ)) -
          Real.sqrt (((n + 1 : ℕ) : ℝ)))
  rw [abs_of_pos (div_pos (coefficient_pos ha _) (coefficient_pos ha _))]
  simp only [coefficient, one_div]
  calc
    (Real.rpow a (Real.sqrt (((n + 1 : ℕ) : ℝ))))⁻¹ /
          (Real.rpow a (Real.sqrt (((n + 2 : ℕ) : ℝ))))⁻¹ =
        Real.rpow a (Real.sqrt (((n + 2 : ℕ) : ℝ))) /
          Real.rpow a (Real.sqrt (((n + 1 : ℕ) : ℝ))) := by
      field_simp [ne_of_gt (Real.rpow_pos_of_pos ha _)]
    _ =
        Real.rpow a
          (Real.sqrt (((n + 2 : ℕ) : ℝ)) -
            Real.sqrt (((n + 1 : ℕ) : ℝ))) :=
      (Real.rpow_sub ha _ _).symm

private theorem powerTerm_ratio_tendsto (a x : ℝ) (ha : 0 < a) (hx : x ≠ 0) :
    Tendsto
      (fun n : ℕ =>
        ‖powerTerm a (n + 2) x‖ / ‖powerTerm a (n + 1) x‖)
      atTop (𝓝 |x|) := by
  have hc := gap1 a ha
  have hlim :
      Tendsto
        (fun n : ℕ =>
          |x| / |coefficient a (n + 1) / coefficient a (n + 2)|)
        atTop (𝓝 |x|) := by
    simpa using (tendsto_const_nhds.div hc one_ne_zero)
  refine hlim.congr' (Eventually.of_forall (fun n => ?_))
  change
    |x| / |coefficient a (n + 1) / coefficient a (n + 2)| =
      ‖powerTerm a (n + 2) x‖ / ‖powerTerm a (n + 1) x‖
  simp only [powerTerm, Real.norm_eq_abs, abs_mul, abs_pow]
  rw [abs_of_pos (coefficient_pos ha (n + 1)),
    abs_of_pos (coefficient_pos ha (n + 2)),
    abs_of_pos
      (div_pos (coefficient_pos ha (n + 1))
        (coefficient_pos ha (n + 2)))]
  field_simp [ne_of_gt (coefficient_pos ha (n + 1)),
    ne_of_gt (coefficient_pos ha (n + 2)), abs_ne_zero.mpr hx, pow_succ]
  <;> ring

theorem gap2 :
    ∀ a : ℝ, 0 < a → HasConvergenceRadiusOne a := by
  intro a ha
  constructor
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      simp [SeriesConvergesAt, powerTerm]
    · have hratio :
          Tendsto
            (fun n : ℕ =>
              ‖powerTerm a ((n + 1) + 1) x‖ /
                ‖powerTerm a (n + 1) x‖)
            atTop (𝓝 |x|) := by
        simpa [Nat.add_assoc] using powerTerm_ratio_tendsto a x ha hx0
      have hne :
          ∀ᶠ n : ℕ in atTop, powerTerm a (n + 1) x ≠ 0 :=
        Eventually.of_forall (fun n => by
          exact mul_ne_zero (ne_of_gt (coefficient_pos ha _))
            (pow_ne_zero _ hx0))
      exact summable_of_ratio_test_tendsto_lt_one hx hne hratio
  · intro x hx hs
    have hx0 : x ≠ 0 := by
      exact abs_ne_zero.mp (ne_of_gt (lt_trans zero_lt_one hx))
    have hratio :
        Tendsto
          (fun n : ℕ =>
            ‖powerTerm a ((n + 1) + 1) x‖ /
              ‖powerTerm a (n + 1) x‖)
          atTop (𝓝 |x|) := by
      simpa [Nat.add_assoc] using powerTerm_ratio_tendsto a x ha hx0
    exact (not_summable_of_ratio_test_tendsto_gt_one hx hratio) hs

theorem gap3 :
    ∀ (a x : ℝ), 0 < a → |x| < 1 → SeriesConvergesAt a x := by
  intro a x ha hx
  exact (gap2 a ha).1 x hx

theorem gap4 :
    ∀ a : ℝ, 0 < a →
      (fun k : ℕ => powerTerm a (k + 1) 1) =
        fun k : ℕ => 1 / Real.rpow a (Real.sqrt (k + 1)) := by
  intro a ha
  funext k
  simp [powerTerm, coefficient]

theorem gap5 :
    ∀ a : ℝ, 1 < a →
      Summable
        (fun k : ℕ => 1 / Real.rpow a (Real.sqrt (k + 1))) := by
  intro a ha
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  let q : ℝ := 1 / a
  have hq0 : 0 < q := by
    dsimp [q]
    positivity
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hq0]
    dsimp [q]
    exact (div_lt_one ha0).2 ha
  let u : ℕ → ℕ := fun k => (k + 1) ^ 2
  let f : ℕ → ℝ :=
    fun n => 1 / Real.rpow a (Real.sqrt (n + 1))
  have hnonneg : ∀ n, 0 ≤ f n := by
    intro n
    exact (one_div_pos.mpr (Real.rpow_pos_of_pos ha0 _)).le
  have hmono :
      ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m := by
    intro m n hm hmn
    apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos ha0 _)
    apply Real.rpow_le_rpow_of_exponent_le ha.le
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hupos : ∀ k, 0 < u k := by
    intro k
    dsimp [u]
    positivity
  have hust : StrictMono u := by
    apply strictMono_nat_of_lt_succ
    intro k
    dsimp [u]
    have hstep :
        (k + 2) ^ 2 = (k + 1) ^ 2 + (2 * k + 3) := by
      ring
    rw [show k + 1 + 1 = k + 2 by omega, hstep]
    omega
  have hudiff : SuccDiffBounded 2 u := by
    intro k
    dsimp [u]
    have hstep1 :
        (k + 2) ^ 2 = (k + 1) ^ 2 + (2 * k + 3) := by
      ring
    have hstep2 :
        (k + 3) ^ 2 = (k + 2) ^ 2 + (2 * k + 5) := by
      ring
    rw [show k + 1 + 1 = k + 2 by omega,
      show k + 2 + 1 = k + 3 by omega, hstep2, hstep1]
    omega
  have hnq :
      Summable (fun k : ℕ => (k : ℝ) * q ^ k) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hqnorm)
  have hgeo : Summable (fun k : ℕ => q ^ k) :=
    summable_geometric_of_norm_lt_one hqnorm
  have hmajor :
      Summable (fun k : ℕ => (2 * (k : ℝ) + 3) * q ^ (k + 1)) := by
    have hs :=
      ((hnq.mul_left 2).add (hgeo.mul_left 3)).mul_left q
    refine hs.congr ?_
    intro k
    simp only [pow_succ]
    ring
  have hcondensed :
      Summable
        (fun k : ℕ =>
          (u (k + 1) - (u k : ℝ)) * f (u k)) := by
    refine Summable.of_norm_bounded hmajor ?_
    intro k
    have hdiffNat : u (k + 1) - u k = 2 * k + 3 := by
      dsimp [u]
      have hstep :
          (k + 2) ^ 2 = (k + 1) ^ 2 + (2 * k + 3) := by
        ring
      rw [show k + 1 + 1 = k + 2 by omega, hstep]
      omega
    have hdiff :
        (u (k + 1) : ℝ) - (u k : ℝ) =
          2 * (k : ℝ) + 3 := by
      rw [← Nat.cast_sub (hust.monotone (Nat.le_succ k))]
      exact_mod_cast hdiffNat
    have hsqrt :
        ((k + 1 : ℕ) : ℝ) ≤
          Real.sqrt ((u k : ℝ) + 1) := by
      apply Real.le_sqrt_of_sq_le
      dsimp [u]
      push_cast
      nlinarith
    have hfa : f (u k) ≤ q ^ (k + 1) := by
      dsimp [f]
      calc
        1 / Real.rpow a (Real.sqrt ((u k : ℝ) + 1)) ≤
            1 / Real.rpow a (((k + 1 : ℕ) : ℝ)) := by
          apply one_div_le_one_div_of_le
            (Real.rpow_pos_of_pos ha0 _)
          exact Real.rpow_le_rpow_of_exponent_le ha.le hsqrt
        _ = q ^ (k + 1) := by
          rw [show
            Real.rpow a (((k + 1 : ℕ) : ℝ)) = a ^ (k + 1) from
              Real.rpow_natCast a (k + 1)]
          simp [q, one_div]
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (mul_nonneg
          (sub_nonneg.mpr
            (mod_cast hust.monotone (Nat.le_succ k)))
          (hnonneg (u k))),
      hdiff]
    exact mul_le_mul_of_nonneg_left hfa (by positivity)
  exact
    (summable_schlomilch_iff_of_nonneg hnonneg hmono hupos hust
      (by norm_num : (2 : ℕ) ≠ 0) hudiff).mp hcondensed

theorem gap6 :
    ∀ a : ℝ, 1 < a → SeriesConvergesAt a 1 := by
  intro a ha
  simpa [SeriesConvergesAt, powerTerm, coefficient] using gap5 a ha

theorem gap7 :
    ∀ a : ℝ, 0 < a → a ≤ 1 →
      ¬ Summable
        (fun k : ℕ => 1 / Real.rpow a (Real.sqrt (k + 1))) := by
  intro a ha ha1 hs
  have hlim :
      Tendsto
        (fun k : ℕ => 1 / Real.rpow a (Real.sqrt (k + 1)))
        atTop (𝓝 0) :=
    hs.tendsto_atTop_zero
  have hevent :
      ∀ᶠ k : ℕ in atTop,
        1 / Real.rpow a (Real.sqrt (k + 1)) < (1 / 2 : ℝ) :=
    (tendsto_order.1 hlim).2 (1 / 2 : ℝ) (by norm_num)
  rcases eventually_atTop.1 hevent with ⟨N, hN⟩
  have hpow_pos :
      0 < Real.rpow a (Real.sqrt (N + 1)) :=
    Real.rpow_pos_of_pos ha _
  have hpow_le :
      Real.rpow a (Real.sqrt (N + 1)) ≤ 1 :=
    Real.rpow_le_one (le_of_lt ha) ha1 (Real.sqrt_nonneg _)
  have hterm : (1 : ℝ) ≤ 1 / Real.rpow a (Real.sqrt (N + 1)) :=
    one_le_one_div hpow_pos hpow_le
  linarith [hN N le_rfl]

theorem gap8 :
    ∀ a : ℝ, 0 < a → a ≤ 1 → ¬ SeriesConvergesAt a 1 := by
  intro a ha ha1 hs
  apply gap7 a ha ha1
  simpa [SeriesConvergesAt, powerTerm, coefficient] using hs

theorem gap9 :
    ∀ a : ℝ, 0 < a →
      (fun k : ℕ => powerTerm a (k + 1) (-1)) =
        fun k : ℕ =>
          (-1 : ℝ) ^ (k + 1) /
            Real.rpow a (Real.sqrt (k + 1)) := by
  intro a ha
  funext k
  simp [powerTerm, coefficient, div_eq_mul_inv, mul_comm]

theorem gap10 :
    ∀ a : ℝ, 1 < a →
      Summable (fun k : ℕ => |powerTerm a (k + 1) (-1)|) := by
  intro a ha
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hs := gap5 a ha
  refine hs.congr ?_
  intro k
  rw [congrFun (gap9 a ha0) k, abs_div]
  simp only [abs_pow, abs_neg, abs_one, one_pow]
  congr 1
  exact (abs_of_pos (Real.rpow_pos_of_pos ha0 _)).symm

theorem gap11 :
    ∀ a : ℝ, 0 < a → a ≤ 1 → ¬ SeriesConvergesAt a (-1) := by
  intro a ha ha1 hs
  have hlim :
      Tendsto (fun k : ℕ => powerTerm a (k + 1) (-1)) atTop (𝓝 0) :=
    hs.tendsto_atTop_zero
  have habslim :
      Tendsto (fun k : ℕ => |powerTerm a (k + 1) (-1)|) atTop (𝓝 0) := by
    simpa using hlim.abs
  have hevent :
      ∀ᶠ k : ℕ in atTop,
        |powerTerm a (k + 1) (-1)| < (1 / 2 : ℝ) :=
    (tendsto_order.1 habslim).2 (1 / 2 : ℝ) (by norm_num)
  rcases eventually_atTop.1 hevent with ⟨N, hN⟩
  have habs :
      |powerTerm a (N + 1) (-1)| =
        1 / Real.rpow a (Real.sqrt (N + 1)) := by
    rw [congrFun (gap9 a ha) N, abs_div]
    simp only [abs_pow, abs_neg, abs_one, one_pow]
    congr 1
    exact abs_of_pos (Real.rpow_pos_of_pos ha _)
  have hpow_pos :
      0 < Real.rpow a (Real.sqrt (N + 1)) :=
    Real.rpow_pos_of_pos ha _
  have hpow_le :
      Real.rpow a (Real.sqrt (N + 1)) ≤ 1 :=
    Real.rpow_le_one (le_of_lt ha) ha1 (Real.sqrt_nonneg _)
  have hterm :
      (1 : ℝ) ≤ |powerTerm a (N + 1) (-1)| := by
    rw [habs]
    exact one_le_one_div hpow_pos hpow_le
  linarith [hN N le_rfl]

theorem gap12 :
    ∀ (a x : ℝ), 0 < a →
      (x ∈
          {y : ℝ |
            (1 < a ∧ y ∈ Set.Icc (-1 : ℝ) 1) ∨
            (a ≤ 1 ∧ y ∈ Set.Ioo (-1 : ℝ) 1)} ↔
        SeriesConvergesAt a x) := by
  intro a x ha
  constructor
  · rintro (⟨ha1, hxleft, hxright⟩ | ⟨ha1, hxleft, hxright⟩)
    · by_cases hleft : x = -1
      · subst x
        unfold SeriesConvergesAt
        exact (gap10 a ha1).of_abs
      · by_cases hright : x = 1
        · subst x
          exact gap6 a ha1
        · exact gap3 a x ha (by
            rw [abs_lt]
            exact ⟨lt_of_le_of_ne hxleft (Ne.symm hleft),
              lt_of_le_of_ne hxright hright⟩)
    · exact gap3 a x ha (by
        rw [abs_lt]
        constructor <;> linarith)
  · intro hconv
    by_cases ha1 : 1 < a
    · left
      refine ⟨ha1, ?_⟩
      constructor
      · by_contra hleft
        have hx : x < -1 := lt_of_not_ge hleft
        apply (gap2 a ha).2 x (by
          rw [abs_of_neg (by linarith : x < 0)]
          linarith)
        exact hconv
      · by_contra hright
        have hx : 1 < x := lt_of_not_ge hright
        apply (gap2 a ha).2 x (by
          rw [abs_of_pos (by linarith : 0 < x)]
          exact hx)
        exact hconv
    · right
      have ha1' : a ≤ 1 := le_of_not_gt ha1
      refine ⟨ha1', ?_⟩
      constructor
      · by_contra hleft
        have hx : x ≤ -1 := le_of_not_gt hleft
        rcases hx.eq_or_lt with hEq | hlt
        · subst x
          exact gap11 a ha ha1' hconv
        · apply (gap2 a ha).2 x (by
            rw [abs_of_neg (by linarith : x < 0)]
            linarith)
          exact hconv
      · by_contra hright
        have hx : 1 ≤ x := le_of_not_gt hright
        rcases hx.eq_or_lt with hEq | hlt
        · subst x
          exact gap8 a ha ha1' hconv
        · apply (gap2 a ha).2 x (by
            rw [abs_of_pos (by linarith : 0 < x)]
            exact hlt)
          exact hconv

end

end ProofGap.Exercise2823
