import ProofGapLean.Prelude.Analysis
import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2898

noncomputable section

open Filter
open scoped BigOperators ENNReal Topology

def ratioSeq (a : ℕ → ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal |a n / a (n + 1)|

def rootSeq (a : ℕ → ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.rpow |a n| (1 / (n : ℝ)))

def ratioProduct (a : ℕ → ℝ) (m n : ℕ) : ℝ≥0∞ :=
  ∏ j ∈ Finset.Icc (m + 1) n,
    ENNReal.ofReal (|a j| / |a (j - 1)|)

def SeriesConvergesAt (a : ℕ → ℝ) (x : ℝ) : Prop :=
  Summable (fun n : ℕ => a n * x ^ n)

def IsConvergenceRadius (a : ℕ → ℝ) (R : ℝ≥0∞) : Prop :=
  (∀ x : ℝ, ENNReal.ofReal |x| < R → SeriesConvergesAt a x) ∧
    (∀ x : ℝ, R < ENNReal.ofReal |x| → ¬ SeriesConvergesAt a x)

def RatioData (a : ℕ → ℝ) (l L R : ℝ≥0∞) : Prop :=
  (∀ n, a n ≠ 0) ∧
    l = liminf (ratioSeq a) atTop ∧
    L = limsup (ratioSeq a) atTop ∧
    IsConvergenceRadius a R

private theorem nextRatio_eq_inv_ratioSeq
    (a : ℕ → ℝ) (ha : ∀ n, a n ≠ 0) (n : ℕ) :
    ENNReal.ofReal (|a (n + 1)| / |a n|) = (ratioSeq a n)⁻¹ := by
  rw [ratioSeq, abs_div]
  rw [ENNReal.ofReal_div_of_pos (abs_pos.2 (ha n))]
  rw [ENNReal.ofReal_div_of_pos (abs_pos.2 (ha (n + 1)))]
  exact (ENNReal.inv_div
    (Or.inl ENNReal.ofReal_ne_top)
    (Or.inl ((ENNReal.ofReal_ne_zero_iff).2 (abs_pos.2 (ha (n + 1)))))).symm

private theorem ennreal_prod_lt_pow {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ≥0∞) (B : ℝ≥0∞)
    (hs : s.Nonempty) (h : ∀ i ∈ s, f i < B) :
    (∏ i ∈ s, f i) < B ^ s.card := by
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert i s hi ih =>
      by_cases hs0 : s = ∅
      · subst s
        simpa using h i (by simp)
      · rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
        have his : f i < B := h i (by simp)
        have hrs : (∏ j ∈ s, f j) < B ^ s.card :=
          ih (Finset.nonempty_iff_ne_empty.2 hs0) (fun j hj => h j (by simp [hj]))
        simpa [pow_succ, mul_comm] using ENNReal.mul_lt_mul his hrs

private theorem ennreal_pow_lt_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ≥0∞) (C : ℝ≥0∞)
    (hs : s.Nonempty) (h : ∀ i ∈ s, C < f i) :
    C ^ s.card < ∏ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert i s hi ih =>
      by_cases hs0 : s = ∅
      · subst s
        simpa using h i (by simp)
      · rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
        have his : C < f i := h i (by simp)
        have hrs : C ^ s.card < ∏ j ∈ s, f j :=
          ih (Finset.nonempty_iff_ne_empty.2 hs0) (fun j hj => h j (by simp [hj]))
        simpa [pow_succ, mul_comm] using ENNReal.mul_lt_mul his hrs

private theorem eventually_root_lt_of_geometric
    (u : ℕ → ℝ≥0∞) (C B : ℝ≥0∞)
    (hufin : ∀ n, u n ≠ ⊤) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hCB : C < B) (m : ℕ)
    (hgeom : ∀ n, m < n → u n < u m * C ^ (n - m)) :
    ∀ᶠ n in atTop, u n ^ (1 / (n : ℝ)) < B := by
  let D : ℝ≥0∞ := u m / C ^ m
  let y : ℝ≥0∞ := B / C
  have hCp0 : C ^ m ≠ 0 := pow_ne_zero _ hC0
  have hCptop : C ^ m ≠ ⊤ := by simp [hCtop]
  have hDtop : D ≠ ⊤ := by
    exact ENNReal.div_ne_top (hufin m) hCp0
  have hy : 1 < y := by
    apply (ENNReal.lt_div_iff_mul_lt
      (Or.inl hC0) (Or.inl hCtop)).2
    simpa [y]
  have hDroot : ∀ᶠ n : ℕ in atTop, D ^ (1 / (n : ℝ)) ≤ y :=
    ENNReal.eventually_pow_one_div_le hDtop hy
  filter_upwards [hDroot, eventually_gt_atTop m] with n hDn hmn
  have hn0 : n ≠ 0 := by omega
  have hrewrite : u m * C ^ (n - m) = D * C ^ n := by
    symm
    calc
      D * C ^ n = (u m / C ^ m) * (C ^ m * C ^ (n - m)) := by
        dsimp [D]
        rw [← pow_add, Nat.add_sub_of_le hmn.le]
      _ = u m * C ^ (n - m) := by
        rw [← mul_assoc, ENNReal.div_mul_cancel hCp0 hCptop]
  have hbase : u n < D * C ^ n := (hgeom n hmn).trans_eq hrewrite
  have hroot := ENNReal.rpow_lt_rpow hbase
    (one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)))
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr (Nat.cast_nonneg n))] at hroot
  have hCr : (C ^ n) ^ (1 / (n : ℝ)) = C := by
    simpa [one_div] using ENNReal.pow_rpow_inv_natCast hn0 C
  rw [hCr] at hroot
  have hmul : D ^ (1 / (n : ℝ)) * C ≤ y * C :=
    mul_le_mul_right' hDn C
  have hyC : y * C = B := by
    dsimp [y]
    exact ENNReal.div_mul_cancel hC0 hCtop
  exact hroot.trans_le (hmul.trans_eq hyC)

private theorem eventually_lt_root_of_geometric
    (u : ℕ → ℝ≥0∞) (A C : ℝ≥0∞)
    (hupos : ∀ n, u n ≠ 0) (hufin : ∀ n, u n ≠ ⊤)
    (hA0 : A ≠ 0) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hAC : A < C) (m : ℕ)
    (hgeom : ∀ n, m < n → u m * C ^ (n - m) < u n) :
    ∀ᶠ n in atTop, A < u n ^ (1 / (n : ℝ)) := by
  let D : ℝ≥0∞ := u m / C ^ m
  let y : ℝ≥0∞ := A / C
  have hCp0 : C ^ m ≠ 0 := pow_ne_zero _ hC0
  have hCptop : C ^ m ≠ ⊤ := by simp [hCtop]
  have hD0 : D ≠ 0 := by
    exact ENNReal.div_ne_zero.2 ⟨hupos m, hCptop⟩
  have hDtop : D ≠ ⊤ := ENNReal.div_ne_top (hufin m) hCp0
  have hy0 : y ≠ 0 := by
    exact ENNReal.div_ne_zero.2 ⟨hA0, hCtop⟩
  have hylt : y < 1 := by
    apply (ENNReal.div_lt_iff
      (Or.inl hC0) (Or.inl hCtop)).2
    simpa [y] using hAC
  have hyinv : 1 < y⁻¹ := ENNReal.one_lt_inv.2 hylt
  have hDroot : ∀ᶠ n : ℕ in atTop, D⁻¹ ^ (1 / (n : ℝ)) ≤ y⁻¹ :=
    ENNReal.eventually_pow_one_div_le (ENNReal.inv_ne_top.2 hD0) hyinv
  filter_upwards [hDroot, eventually_gt_atTop m] with n hDn hmn
  have hn0 : n ≠ 0 := by omega
  have hrewrite : u m * C ^ (n - m) = D * C ^ n := by
    symm
    calc
      D * C ^ n = (u m / C ^ m) * (C ^ m * C ^ (n - m)) := by
        dsimp [D]
        rw [← pow_add, Nat.add_sub_of_le hmn.le]
      _ = u m * C ^ (n - m) := by
        rw [← mul_assoc, ENNReal.div_mul_cancel hCp0 hCptop]
  have hbase : D * C ^ n < u n := hrewrite ▸ hgeom n hmn
  have hroot := ENNReal.rpow_lt_rpow hbase
    (one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)))
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr (Nat.cast_nonneg n))] at hroot
  have hCr : (C ^ n) ^ (1 / (n : ℝ)) = C := by
    simpa [one_div] using ENNReal.pow_rpow_inv_natCast hn0 C
  rw [hCr] at hroot
  rw [ENNReal.inv_rpow] at hDn
  have hyD : y ≤ D ^ (1 / (n : ℝ)) := ENNReal.inv_le_inv.mp hDn
  have hmul : y * C ≤ D ^ (1 / (n : ℝ)) * C :=
    mul_le_mul_right' hyD C
  have hyC : y * C = A := by
    dsimp [y]
    exact ENNReal.div_mul_cancel hC0 hCtop
  exact (hyC ▸ hmul).trans_lt hroot

private theorem ofReal_ratio_eq_ratioProduct
    (a : ℕ → ℝ) (ha : ∀ n, a n ≠ 0) :
    ∀ m n : ℕ, m ≤ n →
      ENNReal.ofReal (|a n| / |a m|) = ratioProduct a m n := by
  intro m n hmn
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      simp [ratioProduct, ha]
  | succ n ih =>
      by_cases hm : m = n + 1
      · subst m
        simp [ratioProduct, ha]
      · have hmn' : m ≤ n := by omega
        rw [ratioProduct, Finset.prod_Icc_succ_top (by omega)]
        change ENNReal.ofReal (|a (n + 1)| / |a m|) =
          ratioProduct a m n * ENNReal.ofReal (|a (n + 1)| / |a n|)
        rw [← ih m hmn']
        rw [← ENNReal.ofReal_mul (div_nonneg (abs_nonneg _) (abs_nonneg _))]
        congr 1
        field_simp [abs_ne_zero.mpr (ha m), abs_ne_zero.mpr (ha n)]

private theorem eventually_lt_root_of_limsup_zero
    (a : ℕ → ℝ) (ha : ∀ n, a n ≠ 0)
    (hlim : limsup (ratioSeq a) atTop = 0)
    (A : ℝ≥0∞) (hAtop : A ≠ ⊤) (hA0 : A ≠ 0) :
    ∀ᶠ n in atTop, A < rootSeq a n := by
  let C : ℝ≥0∞ := A + 1
  have hAC : A < C := ENNReal.lt_add_right hAtop one_ne_zero
  have hC0 : C ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hAC)
  have hCtop : C ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hAtop, ENNReal.one_ne_top⟩
  have hcut : limsup (ratioSeq a) atTop < C⁻¹ := by
    rw [hlim]
    exact ENNReal.inv_pos.2 hCtop
  have hq : ∀ᶠ n in atTop, ratioSeq a n < C⁻¹ :=
    eventually_lt_of_limsup_lt hcut (hu := isBounded_le_of_top)
  have hp : ∀ᶠ n in atTop,
      C < ENNReal.ofReal (|a (n + 1)| / |a n|) := by
    filter_upwards [hq] with n hn
    rw [nextRatio_eq_inv_ratioSeq a ha n]
    exact ENNReal.lt_inv_iff_lt_inv.2 hn
  rw [eventually_atTop] at hp
  obtain ⟨m, hm⟩ := hp
  have hgeom : ∀ n, m < n →
      ENNReal.ofReal |a m| * C ^ (n - m) < ENNReal.ofReal |a n| := by
    intro n hmn
    have hs : (Finset.Icc (m + 1) n).Nonempty :=
      ⟨m + 1, by simp [Nat.succ_le_iff.2 hmn]⟩
    have hprod := ennreal_pow_lt_prod
      (Finset.Icc (m + 1) n)
      (fun j => ENNReal.ofReal (|a j| / |a (j - 1)|)) C hs
      (fun j hj => by
        rcases Finset.mem_Icc.1 hj with ⟨hmj, hjn⟩
        have hjm : m ≤ j - 1 := by omega
        have hjone : 1 ≤ j := by omega
        simpa [Nat.sub_add_cancel hjone] using hm (j - 1) hjm)
    have hratio : C ^ (n - m) < ENNReal.ofReal (|a n| / |a m|) := by
      rw [ofReal_ratio_eq_ratioProduct a ha m n hmn.le]
      simpa [Nat.card_Icc] using hprod
    rw [ENNReal.ofReal_div_of_pos (abs_pos.2 (ha m))] at hratio
    have hmul := (ENNReal.lt_div_iff_mul_lt
      (Or.inl ((ENNReal.ofReal_ne_zero_iff).2 (abs_pos.2 (ha m))))
      (Or.inl ENNReal.ofReal_ne_top)).1 hratio
    simpa [mul_comm] using hmul
  have hroot := eventually_lt_root_of_geometric
    (fun n => ENNReal.ofReal |a n|) A C
    (fun n => (ENNReal.ofReal_ne_zero_iff).2 (abs_pos.2 (ha n)))
    (fun n => ENNReal.ofReal_ne_top) hA0 hC0 hCtop hAC m hgeom
  filter_upwards [hroot] with n hn
  unfold rootSeq
  calc
    A < ENNReal.ofReal |a n| ^ (1 / (n : ℝ)) := hn
    _ = ENNReal.ofReal (Real.rpow |a n| (1 / (n : ℝ))) :=
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (a n))
        (one_div_nonneg.mpr (Nat.cast_nonneg n))

private theorem eventually_root_lt_of_liminf_top
    (a : ℕ → ℝ) (ha : ∀ n, a n ≠ 0)
    (hlim : liminf (ratioSeq a) atTop = ⊤)
    (B : ℝ≥0∞) (hB0 : B ≠ 0) (hBtop : B ≠ ⊤) :
    ∀ᶠ n in atTop, rootSeq a n < B := by
  obtain ⟨C, hC0pos, hCB⟩ := exists_between (pos_iff_ne_zero.2 hB0)
  have hC0 : C ≠ 0 := ne_of_gt hC0pos
  have hCtop : C ≠ ⊤ := ne_of_lt (hCB.trans (lt_top_iff_ne_top.2 hBtop))
  have hcut : C⁻¹ < liminf (ratioSeq a) atTop := by
    rw [hlim]
    exact lt_top_iff_ne_top.2 (ENNReal.inv_ne_top.2 hC0)
  have hq : ∀ᶠ n in atTop, C⁻¹ < ratioSeq a n :=
    eventually_lt_of_lt_liminf hcut (hu := isBounded_ge_of_bot)
  have hp : ∀ᶠ n in atTop,
      ENNReal.ofReal (|a (n + 1)| / |a n|) < C := by
    filter_upwards [hq] with n hn
    rw [nextRatio_eq_inv_ratioSeq a ha n]
    exact ENNReal.inv_lt_iff_inv_lt.2 hn
  rw [eventually_atTop] at hp
  obtain ⟨m, hm⟩ := hp
  have hgeom : ∀ n, m < n →
      ENNReal.ofReal |a n| < ENNReal.ofReal |a m| * C ^ (n - m) := by
    intro n hmn
    have hs : (Finset.Icc (m + 1) n).Nonempty :=
      ⟨m + 1, by simp [Nat.succ_le_iff.2 hmn]⟩
    have hprod := ennreal_prod_lt_pow
      (Finset.Icc (m + 1) n)
      (fun j => ENNReal.ofReal (|a j| / |a (j - 1)|)) C hs
      (fun j hj => by
        rcases Finset.mem_Icc.1 hj with ⟨hmj, hjn⟩
        have hjm : m ≤ j - 1 := by omega
        have hjone : 1 ≤ j := by omega
        simpa [Nat.sub_add_cancel hjone] using hm (j - 1) hjm)
    have hratio : ENNReal.ofReal (|a n| / |a m|) < C ^ (n - m) := by
      rw [ofReal_ratio_eq_ratioProduct a ha m n hmn.le]
      simpa [Nat.card_Icc] using hprod
    rw [ENNReal.ofReal_div_of_pos (abs_pos.2 (ha m))] at hratio
    have hmul := (ENNReal.div_lt_iff
      (Or.inl ((ENNReal.ofReal_ne_zero_iff).2 (abs_pos.2 (ha m))))
      (Or.inl ENNReal.ofReal_ne_top)).1 hratio
    simpa [mul_comm] using hmul
  have hroot := eventually_root_lt_of_geometric
    (fun n => ENNReal.ofReal |a n|) C B
    (fun n => ENNReal.ofReal_ne_top) hC0 hCtop hCB m hgeom
  filter_upwards [hroot] with n hn
  unfold rootSeq
  calc
    ENNReal.ofReal (Real.rpow |a n| (1 / (n : ℝ))) =
        ENNReal.ofReal |a n| ^ (1 / (n : ℝ)) :=
      (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (a n))
        (one_div_nonneg.mpr (Nat.cast_nonneg n))).symm
    _ < B := hn

private theorem series_summable_of_eventually_ratio_lt
    (a : ℕ → ℝ) (ha : ∀ n, a n ≠ 0)
    (B : ℝ≥0∞) (hBtop : B ≠ ⊤) (x : ℝ)
    (hBx : B * ENNReal.ofReal |x| < 1)
    (hp : ∀ᶠ n in atTop,
      ENNReal.ofReal (|a (n + 1)| / |a n|) < B) :
    SeriesConvergesAt a x := by
  let r : ℝ := B.toReal * |x|
  have hprodtop : B * ENNReal.ofReal |x| ≠ ⊤ :=
    ENNReal.mul_ne_top hBtop ENNReal.ofReal_ne_top
  have hr : r < 1 := by
    have ht := (ENNReal.toReal_lt_toReal hprodtop ENNReal.one_ne_top).2 hBx
    simpa [r, ENNReal.toReal_mul, hBtop] using ht
  apply summable_of_ratio_norm_eventually_le hr
  filter_upwards [hp] with n hn
  have hratio : |a (n + 1)| / |a n| < B.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal
      (div_nonneg (abs_nonneg _) (abs_nonneg _)) hBtop).1 hn
  have han : 0 < |a n| := abs_pos.2 (ha n)
  have hcoef : |a (n + 1)| ≤ B.toReal * |a n| :=
    ((div_le_iff₀ han).1 hratio.le)
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, pow_succ]
  calc
    |a (n + 1)| * (|x| ^ n * |x|) =
        (|a (n + 1)| * |x|) * |x| ^ n := by ring
    _ ≤ ((B.toReal * |a n|) * |x|) * |x| ^ n := by
      gcongr
    _ = r * (|a n| * |x| ^ n) := by
      dsimp [r]
      ring

private theorem series_not_summable_of_eventually_ratio_gt
    (a : ℕ → ℝ) (ha : ∀ n, a n ≠ 0)
    (A : ℝ≥0∞) (hAtop : A ≠ ⊤) (x : ℝ) (hx0 : x ≠ 0)
    (hAx : 1 < A * ENNReal.ofReal |x|)
    (hp : ∀ᶠ n in atTop,
      A < ENNReal.ofReal (|a (n + 1)| / |a n|)) :
    ¬ SeriesConvergesAt a x := by
  let r : ℝ := A.toReal * |x|
  have hprodtop : A * ENNReal.ofReal |x| ≠ ⊤ :=
    ENNReal.mul_ne_top hAtop ENNReal.ofReal_ne_top
  have hr : 1 < r := by
    have ht := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hprodtop).2 hAx
    simpa [r, ENNReal.toReal_mul, hAtop] using ht
  apply not_summable_of_ratio_norm_eventually_ge hr
  · exact (Frequently.of_forall fun n => by
      simp [ha n, hx0])
  · filter_upwards [hp] with n hn
    have hratio : A.toReal < |a (n + 1)| / |a n| :=
      (ENNReal.lt_ofReal_iff_toReal_lt hAtop).1 hn
    have han : 0 < |a n| := abs_pos.2 (ha n)
    have hcoef : A.toReal * |a n| ≤ |a (n + 1)| :=
      ((le_div_iff₀ han).1 hratio.le)
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, pow_succ]
    calc
      r * (|a n| * |x| ^ n) =
          ((A.toReal * |a n|) * |x|) * |x| ^ n := by
        dsimp [r]
        ring
      _ ≤ (|a (n + 1)| * |x|) * |x| ^ n := by
        gcongr
      _ = |a (n + 1)| * (|x| ^ n * |x|) := by ring

private theorem series_summable_of_ratio_liminf_top
    (a : ℕ → ℝ) (ha : ∀ n, a n ≠ 0)
    (hlim : liminf (ratioSeq a) atTop = ⊤) (x : ℝ) :
    SeriesConvergesAt a x := by
  let t : ℝ≥0∞ := ENNReal.ofReal |x|
  let D : ℝ≥0∞ := t + 1
  let B : ℝ≥0∞ := D⁻¹
  have httop : t ≠ ⊤ := ENNReal.ofReal_ne_top
  have hD0 : D ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le
    (ENNReal.lt_add_right httop one_ne_zero))
  have hDtop : D ≠ ⊤ := ENNReal.add_ne_top.2 ⟨httop, ENNReal.one_ne_top⟩
  have hB0 : B ≠ 0 := ENNReal.inv_ne_zero.2 hDtop
  have hBtop : B ≠ ⊤ := ENNReal.inv_ne_top.2 hD0
  have htD : t < D := ENNReal.lt_add_right httop one_ne_zero
  have hBt : B * t < 1 := by
    calc
      B * t < B * D := ENNReal.mul_lt_mul_right hB0 hBtop htD
      _ = 1 := by
        dsimp [B]
        exact ENNReal.inv_mul_cancel hD0 hDtop
  have hcut : B⁻¹ < liminf (ratioSeq a) atTop := by
    rw [hlim]
    exact lt_top_iff_ne_top.2 (ENNReal.inv_ne_top.2 hB0)
  have hq : ∀ᶠ n in atTop, B⁻¹ < ratioSeq a n :=
    eventually_lt_of_lt_liminf hcut (hu := isBounded_ge_of_bot)
  have hp : ∀ᶠ n in atTop,
      ENNReal.ofReal (|a (n + 1)| / |a n|) < B := by
    filter_upwards [hq] with n hn
    rw [nextRatio_eq_inv_ratioSeq a ha n]
    exact ENNReal.inv_lt_iff_inv_lt.2 hn
  exact series_summable_of_eventually_ratio_lt a ha B hBtop x
    (by simpa [t] using hBt) hp

private theorem series_not_summable_of_ratio_limsup_zero
    (a : ℕ → ℝ) (ha : ∀ n, a n ≠ 0)
    (hlim : limsup (ratioSeq a) atTop = 0) (x : ℝ) (hx0 : x ≠ 0) :
    ¬ SeriesConvergesAt a x := by
  let t : ℝ≥0∞ := ENNReal.ofReal |x|
  let A : ℝ≥0∞ := t⁻¹ + 1
  have ht0 : t ≠ 0 :=
    (ENNReal.ofReal_ne_zero_iff).2 (abs_pos.2 hx0)
  have httop : t ≠ ⊤ := ENNReal.ofReal_ne_top
  have hAtop : A ≠ ⊤ := ENNReal.add_ne_top.2
    ⟨ENNReal.inv_ne_top.2 ht0, ENNReal.one_ne_top⟩
  have hAt : 1 < A * t := by
    dsimp [A]
    rw [add_mul]
    simpa [ENNReal.inv_mul_cancel ht0 httop] using
      ENNReal.lt_add_right ENNReal.one_ne_top ht0
  have hcut : limsup (ratioSeq a) atTop < A⁻¹ := by
    rw [hlim]
    exact ENNReal.inv_pos.2 hAtop
  have hq : ∀ᶠ n in atTop, ratioSeq a n < A⁻¹ :=
    eventually_lt_of_limsup_lt hcut (hu := isBounded_le_of_top)
  have hp : ∀ᶠ n in atTop,
      A < ENNReal.ofReal (|a (n + 1)| / |a n|) := by
    filter_upwards [hq] with n hn
    rw [nextRatio_eq_inv_ratioSeq a ha n]
    exact ENNReal.lt_inv_iff_lt_inv.2 hn
  exact series_not_summable_of_eventually_ratio_gt a ha A hAtop x hx0
    (by simpa [t] using hAt) hp

theorem gap1
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R) :
    0 ≤ l := by
  exact bot_le

theorem gap2
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R) :
    0 ≤ L := by
  exact bot_le

theorem gap3 (l : ℝ≥0∞) :
    l = 0 → 1 / l = ⊤ := by
  rintro rfl
  simp

theorem gap4 (l : ℝ≥0∞) :
    l = ⊤ → 1 / l = 0 := by
  rintro rfl
  simp

theorem gap5
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R) :
    1 / L ≤ 1 / l := by
  rw [h.2.1, h.2.2.1]
  simpa [one_div] using ENNReal.inv_le_inv.mpr
    (liminf_le_limsup (u := ratioSeq a) (f := atTop))

theorem gap6 :
    ∀ ε : ℝ, 0 < ε → ε < 2 →
      ∃ δ₁ δ₂ : ℝ, 0 < δ₁ ∧ 0 < δ₂ ∧
        1 / (1 + δ₁) = 1 - ε / 2 ∧
        1 / (1 - δ₂) = 1 + ε / 2 := by
  intro ε hε hε2
  refine ⟨ε / (2 - ε), ε / (2 + ε), ?_, ?_, ?_, ?_⟩
  · exact div_pos hε (by linarith)
  · exact div_pos hε (by linarith)
  · have hd : 2 - ε ≠ 0 := by linarith
    field_simp [hd]
    <;> ring
  · have hd : 2 + ε ≠ 0 := by linarith
    field_simp [hd]
    <;> ring

theorem gap7
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R)
    (hL0 : L ≠ 0) (hlTop : l ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε → ε < 2 →
      ∃ N : ℕ, ∀ n ≥ N,
        l * ENNReal.ofReal (1 - ε / 2) < ratioSeq a n ∧
          ratioSeq a n < L * ENNReal.ofReal (1 + ε / 2) := by
  intro ε hε hε2
  have hsmall : ENNReal.ofReal (1 - ε / 2) < (1 : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by linarith)
  have hlarge : (1 : ℝ≥0∞) < ENNReal.ofReal (1 + ε / 2) := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have hl_event :
      ∀ᶠ n in atTop, l * ENNReal.ofReal (1 - ε / 2) < ratioSeq a n := by
    by_cases hl0 : l = 0
    · filter_upwards [] with n
      rw [hl0, zero_mul]
      exact ENNReal.ofReal_pos.2 (abs_pos.2 (div_ne_zero (h.1 n) (h.1 (n + 1))))
    · apply eventually_lt_of_lt_liminf (hu := isBounded_ge_of_bot)
      rw [← h.2.1]
      simpa using ENNReal.mul_lt_mul_right hl0 hlTop hsmall
  have hL_event :
      ∀ᶠ n in atTop, ratioSeq a n < L * ENNReal.ofReal (1 + ε / 2) := by
    by_cases hLTop : L = ⊤
    · filter_upwards [] with n
      have hf0 : ENNReal.ofReal (1 + ε / 2) ≠ 0 :=
        ne_of_gt (lt_trans (by simp) hlarge)
      simpa [hLTop, hf0, ratioSeq] using
        (ENNReal.ofReal_lt_top (r := |a n / a (n + 1)|))
    · apply eventually_lt_of_limsup_lt (hu := isBounded_le_of_top)
      rw [← h.2.2.1]
      simpa using ENNReal.mul_lt_mul_right hL0 hLTop hlarge
  exact (eventually_atTop.1 (hl_event.and hL_event))

theorem gap8
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R)
    (hl0 : l ≠ 0) (hL0 : L ≠ 0)
    (hlTop : l ≠ ⊤) (hLTop : L ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε → ε < 2 →
      ∃ N : ℕ, ∀ n ≥ N,
        (1 / L) * ENNReal.ofReal (1 - ε / 2) <
            ENNReal.ofReal (|a (n + 1)| / |a n|) ∧
          ENNReal.ofReal (|a (n + 1)| / |a n|) <
            (1 / l) * ENNReal.ofReal (1 + ε / 2) := by
  intro ε hε hε2
  let c : ℝ≥0∞ := ENNReal.ofReal (1 - ε / 2)
  let d : ℝ≥0∞ := ENNReal.ofReal (1 + ε / 2)
  have hc : c < 1 := by
    dsimp [c]
    exact ENNReal.ofReal_lt_one.2 (by linarith)
  have hd : 1 < d := by
    dsimp [d]
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have hupperCut : L < ((1 / L) * c)⁻¹ := by
    apply ENNReal.lt_inv_iff_lt_inv.2
    simpa [one_div] using ENNReal.mul_lt_mul_right
      (ENNReal.inv_ne_zero.2 hLTop) (ENNReal.inv_ne_top.2 hL0) hc
  have hlowerCut : ((1 / l) * d)⁻¹ < l := by
    apply ENNReal.inv_lt_iff_inv_lt.2
    simpa [one_div] using ENNReal.mul_lt_mul_right
      (ENNReal.inv_ne_zero.2 hlTop) (ENNReal.inv_ne_top.2 hl0) hd
  have hu : ∀ᶠ n in atTop, ratioSeq a n < ((1 / L) * c)⁻¹ := by
    apply eventually_lt_of_limsup_lt (hu := isBounded_le_of_top)
    simpa only [h.2.2.1] using hupperCut
  have hl : ∀ᶠ n in atTop, ((1 / l) * d)⁻¹ < ratioSeq a n := by
    apply eventually_lt_of_lt_liminf (hu := isBounded_ge_of_bot)
    simpa only [h.2.1] using hlowerCut
  rw [eventually_atTop] at hu hl
  obtain ⟨Nu, hNu⟩ := hu
  obtain ⟨Nl, hNl⟩ := hl
  refine ⟨max Nu Nl, fun n hn => ?_⟩
  have hnu := hNu n (le_trans (le_max_left _ _) hn)
  have hnl := hNl n (le_trans (le_max_right _ _) hn)
  rw [nextRatio_eq_inv_ratioSeq a h.1 n]
  exact ⟨ENNReal.lt_inv_iff_lt_inv.2 hnu,
    ENNReal.inv_lt_iff_inv_lt.2 hnl⟩

theorem gap9
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R) :
    ∀ m n : ℕ, m ≤ n →
      ENNReal.ofReal (|a n| / |a m|) = ratioProduct a m n := by
  exact ofReal_ratio_eq_ratioProduct a h.1

theorem gap10
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R)
    (hl0 : l ≠ 0) (hlTop : l ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → m < n →
        ratioProduct a m n <
          ((1 / l) * ENNReal.ofReal (1 + ε / 2)) ^ (n - m) := by
  intro ε hε
  let B : ℝ≥0∞ := (1 / l) * ENNReal.ofReal (1 + ε / 2)
  have hd : (1 : ℝ≥0∞) < ENNReal.ofReal (1 + ε / 2) := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have hcut : B⁻¹ < l := by
    apply ENNReal.inv_lt_iff_inv_lt.2
    simpa [B, one_div] using ENNReal.mul_lt_mul_right
      (ENNReal.inv_ne_zero.2 hlTop) (ENNReal.inv_ne_top.2 hl0) hd
  have hq : ∀ᶠ n in atTop, B⁻¹ < ratioSeq a n := by
    apply eventually_lt_of_lt_liminf (hu := isBounded_ge_of_bot)
    simpa only [h.2.1] using hcut
  have hp : ∀ᶠ n in atTop,
      ENNReal.ofReal (|a (n + 1)| / |a n|) < B := by
    filter_upwards [hq] with n hn
    rw [nextRatio_eq_inv_ratioSeq a h.1 n]
    exact ENNReal.inv_lt_iff_inv_lt.2 hn
  rw [eventually_atTop] at hp
  obtain ⟨N, hN⟩ := hp
  refine ⟨N, fun m n hNm hmn => ?_⟩
  have hs : (Finset.Icc (m + 1) n).Nonempty :=
    ⟨m + 1, by simp [Nat.succ_le_iff.2 hmn]⟩
  have hprod := ennreal_prod_lt_pow
    (Finset.Icc (m + 1) n)
    (fun j => ENNReal.ofReal (|a j| / |a (j - 1)|)) B hs
    (fun j hj => by
      rcases Finset.mem_Icc.1 hj with ⟨hmj, hjn⟩
      have hjN : N ≤ j - 1 := by omega
      have hjone : 1 ≤ j := by omega
      simpa [Nat.sub_add_cancel hjone] using hN (j - 1) hjN)
  simpa [ratioProduct, B, Nat.card_Icc] using hprod

theorem gap11
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R)
    (hl0 : l ≠ 0) (hlTop : l ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → m < n →
        ENNReal.ofReal (|a n| / |a m|) <
          ((1 / l) * ENNReal.ofReal (1 + ε / 2)) ^ (n - m) := by
  intro ε hε
  obtain ⟨N, hN⟩ := gap10 a l L R h hl0 hlTop ε hε
  refine ⟨N, fun m n hNm hmn => ?_⟩
  rw [gap9 a l L R h m n hmn.le]
  exact hN m n hNm hmn

theorem gap12
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R)
    (hl0 : l ≠ 0) (hlTop : l ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        rootSeq a n < (1 / l) * ENNReal.ofReal (1 + ε / 2) := by
  intro ε hε
  let C : ℝ≥0∞ := (1 / l) * ENNReal.ofReal (1 + (ε / 2) / 2)
  let B : ℝ≥0∞ := (1 / l) * ENNReal.ofReal (1 + ε / 2)
  have hi0 : (1 / l : ℝ≥0∞) ≠ 0 := by
    simpa [one_div] using ENNReal.inv_ne_zero.2 hlTop
  have hitop : (1 / l : ℝ≥0∞) ≠ ⊤ := by
    simpa [one_div] using ENNReal.inv_ne_top.2 hl0
  have hc0 : ENNReal.ofReal (1 + (ε / 2) / 2) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.2 (by linarith))
  have hC0 : C ≠ 0 := by
    exact mul_ne_zero hi0 hc0
  have hCtop : C ≠ ⊤ := by
    exact ENNReal.mul_ne_top hitop ENNReal.ofReal_ne_top
  have hfac : ENNReal.ofReal (1 + (ε / 2) / 2) <
      ENNReal.ofReal (1 + ε / 2) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have hCB : C < B := by
    exact ENNReal.mul_lt_mul_right hi0 hitop hfac
  obtain ⟨m, hm⟩ := gap11 a l L R h hl0 hlTop (ε / 2) (by linarith)
  have hgeom : ∀ n, m < n →
      ENNReal.ofReal |a n| < ENNReal.ofReal |a m| * C ^ (n - m) := by
    intro n hmn
    have hq := hm m n le_rfl hmn
    rw [ENNReal.ofReal_div_of_pos (abs_pos.2 (h.1 m))] at hq
    have hmul := (ENNReal.div_lt_iff
      (Or.inl ((ENNReal.ofReal_ne_zero_iff).2 (abs_pos.2 (h.1 m))))
      (Or.inl ENNReal.ofReal_ne_top)).1 hq
    simpa [C, mul_comm] using hmul
  have hroot := eventually_root_lt_of_geometric
    (fun n => ENNReal.ofReal |a n|) C B
    (fun n => ENNReal.ofReal_ne_top) hC0 hCtop hCB m hgeom
  filter_upwards [hroot] with n hn
  unfold rootSeq
  calc
    ENNReal.ofReal (Real.rpow |a n| (1 / (n : ℝ))) =
        ENNReal.ofReal |a n| ^ (1 / (n : ℝ)) :=
      (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (a n))
        (one_div_nonneg.mpr (Nat.cast_nonneg n))).symm
    _ < (1 / l) * ENNReal.ofReal (1 + ε / 2) := by
      simpa [B] using hn

theorem gap13
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R)
    (hL0 : L ≠ 0) (hLTop : L ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε → ε < 2 →
      ∀ᶠ n in atTop,
        (1 / L) * ENNReal.ofReal (1 - ε / 2) < rootSeq a n := by
  intro ε hε hε2
  let A : ℝ≥0∞ := (1 / L) * ENNReal.ofReal (1 - ε / 2)
  let C : ℝ≥0∞ := (1 / L) * ENNReal.ofReal (1 - (ε / 2) / 2)
  have hi0 : (1 / L : ℝ≥0∞) ≠ 0 := by
    simpa [one_div] using ENNReal.inv_ne_zero.2 hLTop
  have hitop : (1 / L : ℝ≥0∞) ≠ ⊤ := by
    simpa [one_div] using ENNReal.inv_ne_top.2 hL0
  have haf0 : ENNReal.ofReal (1 - ε / 2) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.2 (by linarith))
  have hcf0 : ENNReal.ofReal (1 - (ε / 2) / 2) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.2 (by linarith))
  have hA0 : A ≠ 0 := mul_ne_zero hi0 haf0
  have hC0 : C ≠ 0 := mul_ne_zero hi0 hcf0
  have hCtop : C ≠ ⊤ := ENNReal.mul_ne_top hitop ENNReal.ofReal_ne_top
  have hfac : ENNReal.ofReal (1 - ε / 2) <
      ENNReal.ofReal (1 - (ε / 2) / 2) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have hAC : A < C := ENNReal.mul_lt_mul_right hi0 hitop hfac
  have hclt : ENNReal.ofReal (1 - (ε / 2) / 2) < (1 : ℝ≥0∞) :=
    ENNReal.ofReal_lt_one.2 (by linarith)
  have hcut : L < C⁻¹ := by
    apply ENNReal.lt_inv_iff_lt_inv.2
    simpa [C, one_div] using ENNReal.mul_lt_mul_right
      (ENNReal.inv_ne_zero.2 hLTop) (ENNReal.inv_ne_top.2 hL0) hclt
  have hq : ∀ᶠ n in atTop, ratioSeq a n < C⁻¹ := by
    apply eventually_lt_of_limsup_lt (hu := isBounded_le_of_top)
    simpa only [h.2.2.1] using hcut
  have hp : ∀ᶠ n in atTop,
      C < ENNReal.ofReal (|a (n + 1)| / |a n|) := by
    filter_upwards [hq] with n hn
    rw [nextRatio_eq_inv_ratioSeq a h.1 n]
    exact ENNReal.lt_inv_iff_lt_inv.2 hn
  rw [eventually_atTop] at hp
  obtain ⟨m, hm⟩ := hp
  have hgeom : ∀ n, m < n →
      ENNReal.ofReal |a m| * C ^ (n - m) < ENNReal.ofReal |a n| := by
    intro n hmn
    have hs : (Finset.Icc (m + 1) n).Nonempty :=
      ⟨m + 1, by simp [Nat.succ_le_iff.2 hmn]⟩
    have hprod := ennreal_pow_lt_prod
      (Finset.Icc (m + 1) n)
      (fun j => ENNReal.ofReal (|a j| / |a (j - 1)|)) C hs
      (fun j hj => by
        rcases Finset.mem_Icc.1 hj with ⟨hmj, hjn⟩
        have hjm : m ≤ j - 1 := by omega
        have hjone : 1 ≤ j := by omega
        have hj := hm (j - 1) hjm
        simpa [C, Nat.sub_add_cancel hjone] using hj)
    have hratio : C ^ (n - m) < ENNReal.ofReal (|a n| / |a m|) := by
      rw [gap9 a l L R h m n hmn.le]
      simpa [Nat.card_Icc] using hprod
    rw [ENNReal.ofReal_div_of_pos (abs_pos.2 (h.1 m))] at hratio
    have hmul := (ENNReal.lt_div_iff_mul_lt
      (Or.inl ((ENNReal.ofReal_ne_zero_iff).2 (abs_pos.2 (h.1 m))))
      (Or.inl ENNReal.ofReal_ne_top)).1 hratio
    simpa [mul_comm] using hmul
  have hroot := eventually_lt_root_of_geometric
    (fun n => ENNReal.ofReal |a n|) A C
    (fun n => (ENNReal.ofReal_ne_zero_iff).2 (abs_pos.2 (h.1 n)))
    (fun n => ENNReal.ofReal_ne_top) hA0 hC0 hCtop hAC m hgeom
  filter_upwards [hroot] with n hn
  unfold rootSeq
  calc
    (1 / L) * ENNReal.ofReal (1 - ε / 2) <
        ENNReal.ofReal |a n| ^ (1 / (n : ℝ)) := by simpa [A] using hn
    _ = ENNReal.ofReal (Real.rpow |a n| (1 / (n : ℝ))) :=
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (a n))
        (one_div_nonneg.mpr (Nat.cast_nonneg n))

theorem gap14
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R)
    (hl0 : l ≠ 0) (hL0 : L ≠ 0)
    (hlTop : l ≠ ⊤) (hLTop : L ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε → ε < 2 →
      ∃ N : ℕ, ∀ n ≥ N,
        (1 / L) * ENNReal.ofReal (1 - ε) < rootSeq a n ∧
          rootSeq a n < (1 / l) * ENNReal.ofReal (1 + ε) := by
  intro ε hε hε2
  have hl := gap13 a l L R h hL0 hLTop ε hε hε2
  have hu := gap12 a l L R h hl0 hlTop (2 * ε) (by linarith)
  have hi0 : (1 / L : ℝ≥0∞) ≠ 0 := by
    simpa [one_div] using ENNReal.inv_ne_zero.2 hLTop
  have hitop : (1 / L : ℝ≥0∞) ≠ ⊤ := by
    simpa [one_div] using ENNReal.inv_ne_top.2 hL0
  have hfac : ENNReal.ofReal (1 - ε) < ENNReal.ofReal (1 - ε / 2) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have hlower : (1 / L) * ENNReal.ofReal (1 - ε) <
      (1 / L) * ENNReal.ofReal (1 - ε / 2) :=
    ENNReal.mul_lt_mul_right hi0 hitop hfac
  rw [eventually_atTop] at hl hu
  obtain ⟨Nl, hNl⟩ := hl
  obtain ⟨Nu, hNu⟩ := hu
  refine ⟨max Nl Nu, fun n hn => ?_⟩
  have hln := hNl n (le_trans (le_max_left _ _) hn)
  have hun := hNu n (le_trans (le_max_right _ _) hn)
  constructor
  · exact hlower.trans hln
  · simpa only [show 1 + 2 * ε / 2 = 1 + ε by ring] using hun

theorem gap15
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R)
    (hl0 : l ≠ 0) (hlTop : l ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        rootSeq a n / (1 / l) < ENNReal.ofReal (1 + ε) := by
  intro ε hε
  have hr := gap12 a l L R h hl0 hlTop (2 * ε) (by linarith)
  have hi0 : (1 / l : ℝ≥0∞) ≠ 0 := by
    simpa [one_div] using ENNReal.inv_ne_zero.2 hlTop
  have hitop : (1 / l : ℝ≥0∞) ≠ ⊤ := by
    simpa [one_div] using ENNReal.inv_ne_top.2 hl0
  filter_upwards [hr] with n hn
  apply (ENNReal.div_lt_iff (Or.inl hi0) (Or.inl hitop)).2
  have hn' : rootSeq a n < (1 / l) * ENNReal.ofReal (1 + ε) := by
    convert hn using 1 <;> ring
  simpa only [mul_comm] using hn'

theorem gap16
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R)
    (hL0 : L ≠ 0) (hLTop : L ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ᶠ n in atTop,
        ENNReal.ofReal (1 - ε) < rootSeq a n / (1 / L) := by
  intro ε hε hε1
  have hr := gap13 a l L R h hL0 hLTop (2 * ε) (by linarith) (by linarith)
  have hi0 : (1 / L : ℝ≥0∞) ≠ 0 := by
    simpa [one_div] using ENNReal.inv_ne_zero.2 hLTop
  have hitop : (1 / L : ℝ≥0∞) ≠ ⊤ := by
    simpa [one_div] using ENNReal.inv_ne_top.2 hL0
  filter_upwards [hr] with n hn
  apply (ENNReal.lt_div_iff_mul_lt (Or.inl hi0) (Or.inl hitop)).2
  have hn' : (1 / L) * ENNReal.ofReal (1 - ε) < rootSeq a n := by
    convert hn using 1 <;> ring
  simpa only [mul_comm] using hn'

theorem gap17
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      (1 / L) * ENNReal.ofReal (1 - ε) ≤
        liminf (rootSeq a) atTop := by
  intro ε hε hε1
  by_cases hL0 : L = 0
  · have hlim : limsup (ratioSeq a) atTop = 0 := h.2.2.1.symm.trans hL0
    have hrootTop : liminf (rootSeq a) atTop = ⊤ := by
      apply top_unique
      apply (le_liminf_iff
        (f := atTop) (u := rootSeq a)
        isCobounded_ge_of_top isBounded_ge_of_bot).2
      intro A hAtop
      by_cases hA0 : A = 0
      · subst A
        filter_upwards [] with n
        unfold rootSeq
        exact ENNReal.ofReal_pos.2
          (Real.rpow_pos_of_pos (abs_pos.2 (h.1 n)) _)
      · exact eventually_lt_root_of_limsup_zero a h.1 hlim A
          (ne_of_lt hAtop) hA0
    rw [hrootTop]
    exact le_top
  · by_cases hLTop : L = ⊤
    · simp [hLTop]
    · have hr := gap13 a l L R h hL0 hLTop (2 * ε) (by linarith) (by linarith)
      apply le_liminf_of_le (hf := isCobounded_ge_of_top)
      filter_upwards [hr] with n hn
      have hn' : (1 / L) * ENNReal.ofReal (1 - ε) < rootSeq a n := by
        convert hn using 1 <;> ring
      exact hn'.le

theorem gap18
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R) :
    ∀ ε : ℝ, 0 < ε →
      limsup (rootSeq a) atTop ≤
        (1 / l) * ENNReal.ofReal (1 + ε) := by
  intro ε hε
  by_cases hl0 : l = 0
  · have hf0 : ENNReal.ofReal (1 + ε) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.2 (by linarith))
    simpa [hl0, hf0] using (show limsup (rootSeq a) atTop ≤ (⊤ : ℝ≥0∞) from le_top)
  · by_cases hlTop : l = ⊤
    · have hlim : liminf (ratioSeq a) atTop = ⊤ := h.2.1.symm.trans hlTop
      have hroot0 : limsup (rootSeq a) atTop = 0 := by
        apply bot_unique
        apply (limsup_le_iff
          (f := atTop) (u := rootSeq a)
          isCobounded_le_of_bot isBounded_le_of_top).2
        intro B hB0
        by_cases hBTop : B = ⊤
        · subst B
          filter_upwards [] with n
          unfold rootSeq
          exact ENNReal.ofReal_lt_top
        · exact eventually_root_lt_of_liminf_top a h.1 hlim B
            (ne_of_gt hB0) hBTop
      rw [hroot0]
      exact bot_le
    · have hr := gap12 a l L R h hl0 hlTop (2 * ε) (by linarith)
      apply limsup_le_of_le (hf := isCobounded_le_of_bot)
      filter_upwards [hr] with n hn
      have hn' : rootSeq a n < (1 / l) * ENNReal.ofReal (1 + ε) := by
        convert hn using 1 <;> ring
      exact hn'.le

theorem gap19
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R) :
    ∀ ε : ℝ, 0 < ε →
      1 / ((1 / l) * ENNReal.ofReal (1 + ε)) ≤ R := by
  intro ε hε
  have hd0 : ENNReal.ofReal (1 + ε) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.2 (by linarith))
  by_cases hl0 : l = 0
  · simp [hl0, hd0]
  · by_cases hlTop : l = ⊤
    · have hlim : liminf (ratioSeq a) atTop = ⊤ := h.2.1.symm.trans hlTop
      have hRtop : R = ⊤ := by
        by_contra hR
        have hRlt : R < ⊤ := lt_top_iff_ne_top.2 hR
        let T : ℝ≥0∞ := R + 1
        have hTtop : T ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hR, ENNReal.one_ne_top⟩
        have hRT : R < T := ENNReal.lt_add_right hR one_ne_zero
        have hT0 : T ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hRT)
        let x : ℝ := T.toReal
        have hxpos : 0 < x := ENNReal.toReal_pos hT0 hTtop
        have hxeq : ENNReal.ofReal |x| = T := by
          simp [x, abs_of_pos hxpos, ENNReal.ofReal_toReal hTtop]
        have hs := series_summable_of_ratio_liminf_top a h.1 hlim x
        exact (h.2.2.2.2 x (by simpa [hxeq] using hRT)) hs
      simp [hlTop, hd0, hRtop]
    · let B : ℝ≥0∞ := (1 / l) * ENNReal.ofReal (1 + ε)
      let S : ℝ≥0∞ := B⁻¹
      have hi0 : (1 / l : ℝ≥0∞) ≠ 0 := by
        simpa [one_div] using ENNReal.inv_ne_zero.2 hlTop
      have hitop : (1 / l : ℝ≥0∞) ≠ ⊤ := by
        simpa [one_div] using ENNReal.inv_ne_top.2 hl0
      have hB0 : B ≠ 0 := mul_ne_zero hi0 hd0
      have hBtop : B ≠ ⊤ := ENNReal.mul_ne_top hitop ENNReal.ofReal_ne_top
      have hd : (1 : ℝ≥0∞) < ENNReal.ofReal (1 + ε) := by
        rw [← ENNReal.ofReal_one]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
      have hcut : B⁻¹ < l := by
        apply ENNReal.inv_lt_iff_inv_lt.2
        simpa [B, one_div] using ENNReal.mul_lt_mul_right
          (ENNReal.inv_ne_zero.2 hlTop) (ENNReal.inv_ne_top.2 hl0) hd
      have hq : ∀ᶠ n in atTop, B⁻¹ < ratioSeq a n := by
        apply eventually_lt_of_lt_liminf (hu := isBounded_ge_of_bot)
        simpa only [h.2.1] using hcut
      have hp : ∀ᶠ n in atTop,
          ENNReal.ofReal (|a (n + 1)| / |a n|) < B := by
        filter_upwards [hq] with n hn
        rw [nextRatio_eq_inv_ratioSeq a h.1 n]
        exact ENNReal.inv_lt_iff_inv_lt.2 hn
      by_contra hSR
      have hSR' : ¬ S ≤ R := by
        simpa [S, B, one_div] using hSR
      have hRS : R < S := lt_of_not_ge hSR'
      obtain ⟨t, hRt, htS⟩ := exists_between hRS
      have htTop : t ≠ ⊤ := ne_of_lt (htS.trans_le le_top)
      have ht0 : t ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hRt)
      let x : ℝ := t.toReal
      have hxpos : 0 < x := ENNReal.toReal_pos ht0 htTop
      have hxeq : ENNReal.ofReal |x| = t := by
        simp [x, abs_of_pos hxpos, ENNReal.ofReal_toReal htTop]
      have hBt : B * t < 1 := by
        apply ENNReal.mul_lt_of_lt_div'
        simpa [S, one_div] using htS
      have hs := series_summable_of_eventually_ratio_lt a h.1 B hBtop x
        (by simpa [hxeq] using hBt) hp
      exact (h.2.2.2.2 x (by simpa [hxeq] using hRt)) hs

theorem gap20
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      R ≤ 1 / ((1 / L) * ENNReal.ofReal (1 - ε)) := by
  intro ε hε hε1
  have hc0 : ENNReal.ofReal (1 - ε) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.2 (by linarith))
  by_cases hL0 : L = 0
  · have hlim : limsup (ratioSeq a) atTop = 0 := h.2.2.1.symm.trans hL0
    have hR0 : R = 0 := by
      apply bot_unique
      by_contra hR
      have hRpos : 0 < R := lt_of_not_ge hR
      obtain ⟨t, ht0, htR⟩ := exists_between hRpos
      have htTop : t ≠ ⊤ := ne_of_lt (htR.trans_le le_top)
      have ht0' : t ≠ 0 := ne_of_gt ht0
      let x : ℝ := t.toReal
      have hxpos : 0 < x := ENNReal.toReal_pos ht0' htTop
      have hx0 : x ≠ 0 := ne_of_gt hxpos
      have hxeq : ENNReal.ofReal |x| = t := by
        simp [x, abs_of_pos hxpos, ENNReal.ofReal_toReal htTop]
      have hs := h.2.2.2.1 x (by simpa [hxeq] using htR)
      exact (series_not_summable_of_ratio_limsup_zero a h.1 hlim x hx0) hs
    simp [hL0, hc0, hR0]
  · by_cases hLTop : L = ⊤
    · simpa [hLTop] using (show R ≤ (⊤ : ℝ≥0∞) from le_top)
    · let A : ℝ≥0∞ := (1 / L) * ENNReal.ofReal (1 - ε)
      let S : ℝ≥0∞ := A⁻¹
      have hi0 : (1 / L : ℝ≥0∞) ≠ 0 := by
        simpa [one_div] using ENNReal.inv_ne_zero.2 hLTop
      have hitop : (1 / L : ℝ≥0∞) ≠ ⊤ := by
        simpa [one_div] using ENNReal.inv_ne_top.2 hL0
      have hA0 : A ≠ 0 := mul_ne_zero hi0 hc0
      have hAtop : A ≠ ⊤ := ENNReal.mul_ne_top hitop ENNReal.ofReal_ne_top
      have hc : ENNReal.ofReal (1 - ε) < (1 : ℝ≥0∞) :=
        ENNReal.ofReal_lt_one.2 (by linarith)
      have hcut : L < A⁻¹ := by
        apply ENNReal.lt_inv_iff_lt_inv.2
        simpa [A, one_div] using ENNReal.mul_lt_mul_right
          (ENNReal.inv_ne_zero.2 hLTop) (ENNReal.inv_ne_top.2 hL0) hc
      have hq : ∀ᶠ n in atTop, ratioSeq a n < A⁻¹ := by
        apply eventually_lt_of_limsup_lt (hu := isBounded_le_of_top)
        simpa only [h.2.2.1] using hcut
      have hp : ∀ᶠ n in atTop,
          A < ENNReal.ofReal (|a (n + 1)| / |a n|) := by
        filter_upwards [hq] with n hn
        rw [nextRatio_eq_inv_ratioSeq a h.1 n]
        exact ENNReal.lt_inv_iff_lt_inv.2 hn
      by_contra hRS
      have hRS' : ¬ R ≤ S := by
        simpa [S, A, one_div] using hRS
      have hSR : S < R := lt_of_not_ge hRS'
      obtain ⟨t, hSt, htR⟩ := exists_between hSR
      have htTop : t ≠ ⊤ := ne_of_lt (htR.trans_le le_top)
      have ht0 : t ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hSt)
      let x : ℝ := t.toReal
      have hxpos : 0 < x := ENNReal.toReal_pos ht0 htTop
      have hx0 : x ≠ 0 := ne_of_gt hxpos
      have hxeq : ENNReal.ofReal |x| = t := by
        simp [x, abs_of_pos hxpos, ENNReal.ofReal_toReal htTop]
      have hAt : 1 < A * t := by
        calc
          1 = A * S := by
            dsimp [S]
            exact (ENNReal.mul_inv_cancel hA0 hAtop).symm
          _ < A * t := ENNReal.mul_lt_mul_right hA0 hAtop hSt
      have hns := series_not_summable_of_eventually_ratio_gt
        a h.1 A hAtop x hx0 (by simpa [hxeq] using hAt) hp
      exact hns (h.2.2.2.1 x (by simpa [hxeq] using htR))

theorem gap21
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R) :
    ∀ ε : ℝ, 0 < ε →
      l / ENNReal.ofReal (1 + ε) ≤ R := by
  intro ε hε
  let d : ℝ≥0∞ := ENNReal.ofReal (1 + ε)
  have hd0 : d ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.2 (by linarith))
  have hdtop : d ≠ ⊤ := ENNReal.ofReal_ne_top
  have heq : 1 / ((1 / l) * d) = l / d := by
    rw [one_div, one_div]
    rw [ENNReal.mul_inv (Or.inr hdtop) (Or.inr hd0), inv_inv, div_eq_mul_inv]
  rw [← heq]
  exact gap19 a l L R h ε hε

theorem gap22
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      R ≤ L / ENNReal.ofReal (1 - ε) := by
  intro ε hε hε1
  let c : ℝ≥0∞ := ENNReal.ofReal (1 - ε)
  have hc0 : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.2 (by linarith))
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have heq : 1 / ((1 / L) * c) = L / c := by
    rw [one_div, one_div]
    rw [ENNReal.mul_inv (Or.inr hctop) (Or.inr hc0), inv_inv, div_eq_mul_inv]
  rw [← heq]
  exact gap20 a l L R h ε hε hε1

theorem gap23
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R) :
    l ≤ R := by
  by_contra hlR
  have hRl : R < l := lt_of_not_ge hlR
  by_cases hlTop : l = ⊤
  · have hb := gap21 a l L R h 1 (by norm_num)
    have hReq : R = ⊤ := by
      simpa [hlTop, ENNReal.top_div, ENNReal.ofReal_ne_top] using hb
    exact (ne_of_lt hRl) (hReq.trans hlTop.symm)
  · have hRtop : R ≠ ⊤ := ne_of_lt (hRl.trans (lt_top_iff_ne_top.2 hlTop))
    have hl0 : l ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hRl)
    by_cases hR0 : R = 0
    · have hb := gap21 a l L R h 1 (by norm_num)
      have hpos : 0 < l / ENNReal.ofReal (1 + (1 : ℝ)) :=
        ENNReal.div_pos hl0 ENNReal.ofReal_ne_top
      rw [hR0] at hb
      exact (not_lt_of_ge hb) hpos
    · let lr : ℝ := l.toReal
      let rr : ℝ := R.toReal
      have hlrpos : 0 < lr := ENNReal.toReal_pos hl0 hlTop
      have hrrpos : 0 < rr := ENNReal.toReal_pos hR0 hRtop
      have hrrlt : rr < lr := (ENNReal.toReal_lt_toReal hRtop hlTop).2 hRl
      let ε : ℝ := (lr - rr) / (2 * rr)
      have hε : 0 < ε := by
        dsimp [ε]
        exact div_pos (sub_pos.2 hrrlt) (mul_pos (by norm_num) hrrpos)
      have hden : 0 < 1 + ε := by linarith
      have hstrict : rr < lr / (1 + ε) := by
        rw [lt_div_iff₀ hden]
        dsimp [ε]
        field_simp [ne_of_gt hrrpos]
        nlinarith
      have hb := gap21 a l L R h ε hε
      have hd0 : ENNReal.ofReal (1 + ε) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.2 hden)
      have hlefttop : l / ENNReal.ofReal (1 + ε) ≠ ⊤ :=
        ENNReal.div_ne_top hlTop hd0
      have hreal := (ENNReal.toReal_le_toReal hlefttop hRtop).2 hb
      have hreal' : lr / (1 + ε) ≤ rr := by
        simpa [lr, rr, ENNReal.toReal_div,
          ENNReal.toReal_ofReal hden.le] using hreal
      exact (not_lt_of_ge hreal') hstrict

theorem gap24
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R) :
    R ≤ L := by
  by_contra hRL
  have hLR : L < R := lt_of_not_ge hRL
  by_cases hL0 : L = 0
  · have hb := gap22 a l L R h (1 / 2 : ℝ) (by norm_num) (by norm_num)
    have hb0 : R ≤ 0 := by
      simpa [hL0] using hb
    have hRpos : 0 < R := by simpa [hL0] using hLR
    exact (not_lt_of_ge hb0) hRpos
  · by_cases hLTop : L = ⊤
    · have hbad : (⊤ : ℝ≥0∞) < R := by simpa [hLTop] using hLR
      exact (not_lt_of_ge le_top) hbad
    · have hbfin := gap22 a l L R h (1 / 2 : ℝ) (by norm_num) (by norm_num)
      have hcfin0 : ENNReal.ofReal (1 - (1 / 2 : ℝ)) ≠ 0 := by norm_num
      have hrighttop : L / ENNReal.ofReal (1 - (1 / 2 : ℝ)) ≠ ⊤ :=
        ENNReal.div_ne_top hLTop hcfin0
      have hRtop : R ≠ ⊤ := ne_top_of_le_ne_top hrighttop hbfin
      let ll : ℝ := L.toReal
      let rr : ℝ := R.toReal
      have hllpos : 0 < ll := ENNReal.toReal_pos hL0 hLTop
      have hrrpos : 0 < rr := ENNReal.toReal_pos
        (ne_of_gt (lt_of_le_of_lt bot_le hLR)) hRtop
      have hlllt : ll < rr := (ENNReal.toReal_lt_toReal hLTop hRtop).2 hLR
      let ε : ℝ := (rr - ll) / (2 * rr)
      have hdenom : 0 < 2 * rr := mul_pos (by norm_num) hrrpos
      have hε : 0 < ε := by
        dsimp [ε]
        exact div_pos (sub_pos.2 hlllt) hdenom
      have hε1 : ε < 1 := by
        dsimp [ε]
        rw [div_lt_one hdenom]
        nlinarith
      have hone : 0 < 1 - ε := by linarith
      have hstrict : ll / (1 - ε) < rr := by
        rw [div_lt_iff₀ hone]
        dsimp [ε]
        field_simp [ne_of_gt hrrpos]
        nlinarith
      have hb := gap22 a l L R h ε hε hε1
      have hc0 : ENNReal.ofReal (1 - ε) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.2 hone)
      have hrighttop' : L / ENNReal.ofReal (1 - ε) ≠ ⊤ :=
        ENNReal.div_ne_top hLTop hc0
      have hreal := (ENNReal.toReal_le_toReal hRtop hrighttop').2 hb
      have hreal' : rr ≤ ll / (1 - ε) := by
        simpa [ll, rr, ENNReal.toReal_div,
          ENNReal.toReal_ofReal hone.le] using hreal
      exact (not_lt_of_ge hreal') hstrict

theorem gap25
    (a : ℕ → ℝ) (l L R : ℝ≥0∞) (h : RatioData a l L R) :
    l ≤ R ∧ R ≤ L := by
  exact ⟨gap23 a l L R h, gap24 a l L R h⟩

end

end ProofGap.Exercise2898
