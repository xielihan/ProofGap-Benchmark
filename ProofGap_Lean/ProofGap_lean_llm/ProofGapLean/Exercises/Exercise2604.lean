import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2604

noncomputable section

open Filter
open scoped BigOperators

def oddProduct (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 n, (2 * k - 1 : ℕ)

def evenProduct (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 n, (2 * k : ℕ)

def term (p q : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (oddProduct n / evenProduct n) p / Real.rpow n q

def converges (p q : ℝ) : Prop :=
  Summable (fun n : ℕ => term p q (n + 1))

def ratioRaabe (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  n * (a n / a (n + 1) - 1)

def explicitRaabe (p q : ℝ) (n : ℕ) : ℝ :=
  n *
    (Real.rpow ((2 * n + 2 : ℝ) / (2 * n + 1)) p *
        Real.rpow ((n + 1 : ℝ) / n) q - 1)

def localQuotient (p q x : ℝ) : ℝ :=
  (Real.rpow ((2 + 2 * x) / (2 + x)) p * Real.rpow (1 + x) q - 1) / x

private def wallisBase (n : ℕ) : ℝ :=
  oddProduct n / evenProduct n

private def normalizedSquare (n : ℕ) : ℝ :=
  (n : ℝ) * wallisBase n ^ 2

private def coefficient (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (normalizedSquare n) (p / 2)

private theorem oddProduct_succ (n : ℕ) :
    oddProduct (n + 1) = oddProduct n * (2 * (n : ℝ) + 1) := by
  unfold oddProduct
  rw [Finset.prod_Icc_succ_top (by omega)]
  congr 1
  exact_mod_cast (show 2 * (n + 1) - 1 = 2 * n + 1 by omega)

private theorem evenProduct_succ (n : ℕ) :
    evenProduct (n + 1) = evenProduct n * (2 * (n : ℝ) + 2) := by
  unfold evenProduct
  rw [Finset.prod_Icc_succ_top (by omega)]
  congr 1
  exact_mod_cast (show 2 * (n + 1) = 2 * n + 2 by omega)

private theorem oddProduct_pos (n : ℕ) : 0 < oddProduct n := by
  unfold oddProduct
  apply Finset.prod_pos
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  exact_mod_cast (show 0 < 2 * k - 1 by omega)

private theorem evenProduct_pos (n : ℕ) : 0 < evenProduct n := by
  unfold evenProduct
  apply Finset.prod_pos
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  exact_mod_cast (show 0 < 2 * k by omega)

private theorem wallisBase_pos (n : ℕ) : 0 < wallisBase n := by
  exact div_pos (oddProduct_pos n) (evenProduct_pos n)

private theorem wallisBase_succ (n : ℕ) :
    wallisBase (n + 1) =
      wallisBase n * ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) := by
  unfold wallisBase
  rw [oddProduct_succ, evenProduct_succ]
  field_simp [(evenProduct_pos n).ne']

private theorem wallis_identity (n : ℕ) :
    wallisBase n ^ 2 * (((2 : ℝ) * n + 1) * Real.Wallis.W n) = 1 := by
  induction n with
  | zero =>
      simp [wallisBase, oddProduct, evenProduct, Real.Wallis.W]
  | succ n ih =>
      rw [wallisBase_succ, Real.Wallis.W_succ]
      norm_num [Nat.cast_add, Nat.cast_one]
      have h1 : (2 : ℝ) * n + 1 ≠ 0 := by positivity
      have h2 : (2 : ℝ) * n + 2 ≠ 0 := by positivity
      have h3 : (2 : ℝ) * n + 3 ≠ 0 := by positivity
      field_simp [h1, h2, h3]
      nlinarith

private theorem normalizedSquare_eq (n : ℕ) :
    normalizedSquare n =
      ((n : ℝ) / ((2 : ℝ) * n + 1)) * (1 / Real.Wallis.W n) := by
  have hW : 0 < Real.Wallis.W n := Real.Wallis.W_pos n
  have hlin : 0 < (2 : ℝ) * n + 1 := by positivity
  have hid := wallis_identity n
  unfold normalizedSquare
  field_simp [hW.ne', hlin.ne'] at hid
  field_simp [hW.ne', hlin.ne']
  nlinarith

private theorem normalizedSquare_tendsto :
    Tendsto normalizedSquare atTop (nhds (1 / Real.pi)) := by
  have hinvNat : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hcontinuous : Tendsto (fun x : ℝ => 1 / (2 + x))
      (nhds 0) (nhds (1 / 2)) := by
    have h : ContinuousAt (fun x : ℝ => 1 / (2 + x)) 0 := by
      fun_prop (disch := norm_num)
    convert h.tendsto using 1 <;> norm_num
  have hhalf : Tendsto (fun n : ℕ => (n : ℝ) / ((2 : ℝ) * n + 1))
      atTop (nhds (1 / 2)) := by
    apply (hcontinuous.comp hinvNat).congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    simp only [Function.comp_apply]
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    field_simp [hn0]
  have hInvW : Tendsto (fun n : ℕ => 1 / Real.Wallis.W n) atTop
      (nhds (1 / (Real.pi / 2))) :=
    tendsto_const_nhds.div Real.Wallis.tendsto_W_nhds_pi_div_two
      (div_ne_zero Real.pi_ne_zero (by norm_num))
  have hfactor : Tendsto (fun n : ℕ =>
      ((n : ℝ) / ((2 : ℝ) * n + 1)) * (1 / Real.Wallis.W n))
      atTop (nhds (1 / Real.pi)) := by
    convert hhalf.mul hInvW using 1
    field_simp [Real.pi_ne_zero]
  apply hfactor.congr'
  filter_upwards [] with n
  exact (normalizedSquare_eq n).symm

private theorem coefficient_tendsto (p : ℝ) :
    Tendsto (coefficient p) atTop
      (nhds (Real.rpow (1 / Real.pi) (p / 2))) := by
  unfold coefficient
  exact normalizedSquare_tendsto.rpow_const
    (Or.inl (one_div_pos.mpr Real.pi_pos).ne')

private theorem term_nonneg (p q : ℝ) (n : ℕ) : 0 ≤ term p q n := by
  unfold term
  change 0 ≤ Real.rpow (wallisBase n) p / Real.rpow n q
  exact div_nonneg (Real.rpow_nonneg (wallisBase_pos n).le _)
    (Real.rpow_nonneg (by positivity) _)

private theorem term_eq_coefficient (p q : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    term p q n = coefficient p n * Real.rpow n (-(q + p / 2)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hbpos : 0 < wallisBase n := wallisBase_pos n
  have hbpow2 : Real.rpow (wallisBase n) 2 = wallisBase n ^ 2 :=
    Real.rpow_natCast (wallisBase n) 2
  have hsquare : Real.rpow (wallisBase n ^ 2) (p / 2) =
      Real.rpow (wallisBase n) p := by
    calc
      Real.rpow (wallisBase n ^ 2) (p / 2) =
          Real.rpow (Real.rpow (wallisBase n) 2) (p / 2) := by rw [hbpow2]
      _ = Real.rpow (wallisBase n) (2 * (p / 2)) :=
        (Real.rpow_mul hbpos.le 2 (p / 2)).symm
      _ = Real.rpow (wallisBase n) p := by congr 1; ring
  have hcoeff : coefficient p n =
      Real.rpow n (p / 2) * Real.rpow (wallisBase n) p := by
    unfold coefficient normalizedSquare
    calc
      Real.rpow ((n : ℝ) * wallisBase n ^ 2) (p / 2) =
          Real.rpow n (p / 2) * Real.rpow (wallisBase n ^ 2) (p / 2) := by
        exact Real.mul_rpow hnpos.le (sq_nonneg (wallisBase n))
      _ = _ := by rw [hsquare]
  have hcombine : Real.rpow n (p / 2) * Real.rpow n (-(q + p / 2)) =
      Real.rpow n (-q) := by
    calc
      Real.rpow n (p / 2) * Real.rpow n (-(q + p / 2)) =
          Real.rpow n ((p / 2) + -(q + p / 2)) :=
        (Real.rpow_add hnpos (p / 2) (-(q + p / 2))).symm
      _ = Real.rpow n (-q) := by congr 1; ring
  have hnegQ : Real.rpow n (-q) = 1 / Real.rpow n q := by
    convert Real.rpow_sub hnpos 0 q using 1 <;> simp
  unfold term
  change Real.rpow (wallisBase n) p / Real.rpow n q =
    coefficient p n * Real.rpow n (-(q + p / 2))
  rw [hcoeff]
  calc
    Real.rpow (wallisBase n) p / Real.rpow n q =
        Real.rpow (wallisBase n) p * (1 / Real.rpow n q) := by ring
    _ = Real.rpow (wallisBase n) p * Real.rpow n (-q) := by rw [hnegQ]
    _ = Real.rpow (wallisBase n) p *
        (Real.rpow n (p / 2) * Real.rpow n (-(q + p / 2))) := by rw [hcombine]
    _ = (Real.rpow n (p / 2) * Real.rpow (wallisBase n) p) *
        Real.rpow n (-(q + p / 2)) := by ring

private theorem summable_term_of_threshold (p q : ℝ) (h : 1 < q + p / 2) :
    Summable (term p q) := by
  let e : ℝ := -(q + p / 2)
  let L : ℝ := Real.rpow (1 / Real.pi) (p / 2)
  let C : ℝ := L + 1
  have hLPos : 0 < L := by
    exact Real.rpow_pos_of_pos (one_div_pos.mpr Real.pi_pos) _
  have hCPos : 0 < C := by dsimp [C]; linarith
  have hpseries : Summable (fun n : ℕ => Real.rpow (n : ℝ) e) :=
    Real.summable_nat_rpow.mpr (by dsimp [e]; linarith)
  have hmajorant : Summable (fun n : ℕ => C * Real.rpow (n : ℝ) e) :=
    hpseries.mul_left C
  have hupper : ∀ᶠ n : ℕ in atTop, coefficient p n < C :=
    (tendsto_order.1 (coefficient_tendsto p)).2 C (by dsimp [C, L]; linarith)
  apply Summable.of_norm_bounded_eventually hmajorant
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hupper, Filter.eventually_ge_atTop 1] with n hnCoeff hn
  rw [Real.norm_eq_abs, abs_of_nonneg (term_nonneg p q n),
    term_eq_coefficient p q n hn]
  exact mul_le_mul_of_nonneg_right hnCoeff.le
    (Real.rpow_nonneg (by positivity) _)

private theorem threshold_of_summable_term (p q : ℝ) (hsum : Summable (term p q)) :
    1 < q + p / 2 := by
  let e : ℝ := -(q + p / 2)
  let L : ℝ := Real.rpow (1 / Real.pi) (p / 2)
  let c : ℝ := L / 2
  have hLPos : 0 < L := by
    exact Real.rpow_pos_of_pos (one_div_pos.mpr Real.pi_pos) _
  have hcPos : 0 < c := by dsimp [c]; positivity
  have hlower : ∀ᶠ n : ℕ in atTop, c < coefficient p n := by
    apply (tendsto_order.1 (coefficient_tendsto p)).1 c
    change c < L
    dsimp [c]
    linarith
  have hscaled : Summable (fun n : ℕ => (1 / c) * term p q n) :=
    hsum.mul_left (1 / c)
  have hpseries : Summable (fun n : ℕ => Real.rpow (n : ℝ) e) := by
    apply Summable.of_norm_bounded_eventually hscaled
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hlower, Filter.eventually_ge_atTop 1] with n hnCoeff hn
    have hrpowNonneg : 0 ≤ Real.rpow (n : ℝ) e :=
      Real.rpow_nonneg (by positivity) _
    rw [Real.norm_eq_abs, abs_of_nonneg hrpowNonneg,
      term_eq_coefficient p q n hn]
    calc
      Real.rpow (n : ℝ) e = (1 / c) * (c * Real.rpow (n : ℝ) e) := by
        field_simp [hcPos.ne']
      _ ≤ (1 / c) * (coefficient p n * Real.rpow (n : ℝ) e) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hnCoeff.le hrpowNonneg) (by positivity)
  have hexponent := Real.summable_nat_rpow.mp hpseries
  dsimp [e] at hexponent
  linarith

theorem gap1 (p q : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    term p q n / term p q (n + 1) =
      Real.rpow ((2 * n + 2 : ℝ) / (2 * n + 1)) p *
        Real.rpow ((n + 1 : ℝ) / n) q := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1pos : (0 : ℝ) < n + 1 := by positivity
  have hbpos : 0 < wallisBase n := wallisBase_pos n
  have hbspos : 0 < wallisBase (n + 1) := wallisBase_pos (n + 1)
  have hratio : wallisBase n / wallisBase (n + 1) =
      ((2 * n + 2 : ℝ) / (2 * n + 1)) := by
    rw [wallisBase_succ]
    field_simp [hbpos.ne']
  have hpbase : Real.rpow ((2 * n + 2 : ℝ) / (2 * n + 1)) p =
      Real.rpow (wallisBase n) p / Real.rpow (wallisBase (n + 1)) p := by
    calc
      Real.rpow ((2 * n + 2 : ℝ) / (2 * n + 1)) p =
          Real.rpow (wallisBase n / wallisBase (n + 1)) p := by rw [hratio]
      _ = Real.rpow (wallisBase n) p / Real.rpow (wallisBase (n + 1)) p :=
        Real.div_rpow hbpos.le hbspos.le p
  have hpnat : Real.rpow ((n + 1 : ℝ) / n) q =
      Real.rpow (n + 1 : ℝ) q / Real.rpow n q :=
    Real.div_rpow hn1pos.le hnpos.le q
  have hbn : Real.rpow (wallisBase n) p ≠ 0 :=
    (Real.rpow_pos_of_pos hbpos p).ne'
  have hbs : Real.rpow (wallisBase (n + 1)) p ≠ 0 :=
    (Real.rpow_pos_of_pos hbspos p).ne'
  have hnn : Real.rpow n q ≠ 0 := (Real.rpow_pos_of_pos hnpos q).ne'
  have hns : Real.rpow (n + 1 : ℝ) q ≠ 0 :=
    (Real.rpow_pos_of_pos hn1pos q).ne'
  unfold term
  simp only [Nat.cast_add, Nat.cast_one]
  change (Real.rpow (wallisBase n) p / Real.rpow n q) /
      (Real.rpow (wallisBase (n + 1)) p / Real.rpow ((n : ℝ) + 1) q) = _
  rw [hpbase, hpnat]
  field_simp [hbn, hbs, hnn, hns]

theorem gap2 (p q : ℝ) (a : ℕ → ℝ)
    (ha : ∀ n ≥ 1, a n = term p q n) (n : ℕ) (hn : 1 ≤ n) :
    ratioRaabe a n = explicitRaabe p q n := by
  unfold ratioRaabe explicitRaabe
  rw [ha n hn, ha (n + 1) (by omega), gap1 p q n hn]

theorem gap3 (p q L : ℝ)
    (hlocal :
      Tendsto (localQuotient p q) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    Tendsto (fun n : ℕ => explicitRaabe p q (n + 1)) atTop (nhds L) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hinvZero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      atTop (nhds 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp hcast
  have hinvWithin : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact hinvZero
    · exact Filter.Eventually.of_forall (fun n => by
        simp only [Set.mem_Ioi]
        positivity)
  apply (hlocal.comp hinvWithin).congr'
  filter_upwards [] with n
  unfold localQuotient explicitRaabe
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have hmpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hfirst :
      (2 + 2 * (1 / ((n : ℝ) + 1))) / (2 + 1 / ((n : ℝ) + 1)) =
        (2 * ((n : ℝ) + 1) + 2) / (2 * ((n : ℝ) + 1) + 1) := by
    field_simp [hmpos.ne']
  have hsecond : 1 + 1 / ((n : ℝ) + 1) =
      (((n : ℝ) + 1) + 1) / ((n : ℝ) + 1) := by
    field_simp [hmpos.ne']
  rw [hfirst, hsecond]
  field_simp [hmpos.ne']

theorem gap4 (p q : ℝ) :
    Tendsto (localQuotient p q) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (q + p / 2)) := by
  have hbaseDeriv : HasDerivAt (fun x : ℝ => (2 + 2 * x) / (2 + x)) (1 / 2) 0 := by
    convert ((hasDerivAt_const (x := (0 : ℝ)) 2).add
      ((hasDerivAt_const (x := (0 : ℝ)) 2).mul (hasDerivAt_id 0))).div
        ((hasDerivAt_const (x := (0 : ℝ)) 2).add (hasDerivAt_id 0))
          (by norm_num) using 1 <;> norm_num
  have hfirstDeriv : HasDerivAt (fun x : ℝ =>
      Real.rpow ((2 + 2 * x) / (2 + x)) p) (p / 2) 0 := by
    convert hbaseDeriv.rpow_const (Or.inl (by norm_num)) using 1 <;> norm_num
    ring
  have hfirstQuot : Tendsto (fun x : ℝ =>
      (Real.rpow ((2 + 2 * x) / (2 + x)) p - 1) / x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (p / 2)) := by
    convert hfirstDeriv.tendsto_slope_zero_right using 1
    funext x
    simp [div_eq_mul_inv, mul_comm]
  have hsecondDeriv : HasDerivAt (fun x : ℝ => Real.rpow (1 + x) q) q 0 := by
    have hbase : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := by
      convert (hasDerivAt_const (x := (0 : ℝ)) 1).add (hasDerivAt_id 0) using 1 <;>
        norm_num
    convert hbase.rpow_const (Or.inl (by norm_num)) using 1 <;> norm_num
  have hsecondQuot : Tendsto (fun x : ℝ => (Real.rpow (1 + x) q - 1) / x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds q) := by
    convert hsecondDeriv.tendsto_slope_zero_right using 1
    funext x
    simp [div_eq_mul_inv, mul_comm]
  have hsecond : Tendsto (fun x : ℝ => Real.rpow (1 + x) q)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    convert hsecondDeriv.continuousAt.tendsto.mono_left inf_le_left using 1 <;>
      norm_num
  have hsum : Tendsto (fun x : ℝ =>
      ((Real.rpow ((2 + 2 * x) / (2 + x)) p - 1) / x) * Real.rpow (1 + x) q +
        (Real.rpow (1 + x) q - 1) / x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (q + p / 2)) := by
    convert hfirstQuot.mul hsecond |>.add hsecondQuot using 1 <;> ring
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxpos : 0 < x := by simpa only [Set.mem_Ioi] using hx
  unfold localQuotient
  let A : ℝ := Real.rpow ((2 + 2 * x) / (2 + x)) p
  let B : ℝ := Real.rpow (1 + x) q
  change ((A - 1) / x) * B + (B - 1) / x = (A * B - 1) / x
  field_simp [hxpos.ne']
  ring

theorem gap5 (p q : ℝ) (a : ℕ → ℝ)
    (ha : ∀ n ≥ 1, a n = term p q n) :
    Tendsto (fun n : ℕ => ratioRaabe a (n + 1)) atTop
      (nhds (q + p / 2)) := by
  apply (gap3 p q (q + p / 2) (gap4 p q)).congr'
  filter_upwards [] with n
  exact (gap2 p q a ha (n + 1) (by omega)).symm

theorem gap6 (p q : ℝ) (h : 1 < q + p / 2) :
    converges p q := by
  unfold converges
  exact (summable_nat_add_iff 1).mpr (summable_term_of_threshold p q h)

theorem gap7 (p q : ℝ) :
    converges p q ↔ 1 < q + p / 2 := by
  constructor
  · intro hconv
    unfold converges at hconv
    exact threshold_of_summable_term p q ((summable_nat_add_iff 1).mp hconv)
  · exact gap6 p q

end

end ProofGap.Exercise2604
