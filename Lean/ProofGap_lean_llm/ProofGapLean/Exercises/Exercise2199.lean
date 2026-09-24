import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise2199
noncomputable section

open Filter MeasureTheory
open scoped BigOperators Interval

def grid (a b : ℝ) (n i : ℕ) : ℝ :=
  a + ((i : ℝ) / n) * (b - a)

def cell (a b : ℝ) (n i : ℕ) : Set ℝ :=
  Set.Icc (grid a b n i) (grid a b n (i + 1))

def lowerValue (f : ℝ → ℝ) (a b : ℝ) (n i : ℕ) : ℝ :=
  sInf (f '' cell a b n i)

def upperValue (f : ℝ → ℝ) (a b : ℝ) (n i : ℕ) : ℝ :=
  sSup (f '' cell a b n i)

def osc (f : ℝ → ℝ) (a b : ℝ) (n i : ℕ) : ℝ :=
  upperValue f a b n i - lowerValue f a b n i

def Approximant (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) (φ : ℝ → ℝ) : Prop :=
  ContinuousOn φ (Set.Icc a b) ∧
    ∀ i < n, ∀ x ∈ cell a b n i,
      lowerValue f a b n i ≤ φ x ∧ φ x ≤ upperValue f a b n i

def mesh (a b : ℝ) (n : ℕ) : ℝ :=
  |b - a| / (n : ℝ)

def oscSum (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    osc f a b n i * (grid a b n (i + 1) - grid a b n i)

def RiemannIntegrableOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  IntervalIntegrable f volume a b ∧
    Bornology.IsBounded (f '' Set.Icc a b) ∧
    Tendsto (oscSum f a b) atTop (nhds (0 : ℝ))

private theorem grid_step (a b : ℝ) (n i : ℕ) (hn : 0 < n) :
    grid a b n (i + 1) - grid a b n i = (b - a) / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hicast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by
    norm_num
  unfold grid
  rw [hicast]
  field_simp [hn0]
  ring

private theorem grid_mono (a b : ℝ) (n i j : ℕ)
    (hab : a ≤ b) (hn : 0 < n) (hij : i ≤ j) :
    grid a b n i ≤ grid a b n j := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hdiv : (i : ℝ) / n ≤ (j : ℝ) / n :=
    (div_le_div_iff_of_pos_right hnR).2 hijR
  have hmul := mul_le_mul_of_nonneg_right hdiv (sub_nonneg.mpr hab)
  simpa [grid] using add_le_add_left hmul a

private theorem grid_point_mem (a b : ℝ) (n j : ℕ)
    (hab : a ≤ b) (hn : 0 < n) (hj : j ≤ n) :
    grid a b n j ∈ Set.Icc a b := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj
  have hq0 : (0 : ℝ) ≤ (j : ℝ) / n := div_nonneg hj0 (le_of_lt hnR)
  have hq1 : (j : ℝ) / n ≤ 1 := (div_le_one hnR).2 hjn
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  constructor
  · dsimp [grid]
    exact le_add_of_nonneg_right (mul_nonneg hq0 hba)
  · dsimp [grid]
    have hm := mul_le_mul_of_nonneg_right hq1 hba
    nlinarith

private theorem cell_subset_global (a b : ℝ) (n i : ℕ)
    (hab : a ≤ b) (hn : 0 < n) (hi : i < n) :
    cell a b n i ⊆ Set.Icc a b := by
  intro x hx
  have hleft := grid_point_mem a b n i hab hn (Nat.le_of_lt hi)
  have hright := grid_point_mem a b n (i + 1) hab hn
    (Nat.succ_le_iff.mpr hi)
  exact ⟨le_trans hleft.1 hx.1, le_trans hx.2 hright.2⟩

private theorem cell_mem_forces_order (a b : ℝ) (n i : ℕ) (x : ℝ)
    (hn : 0 < n) (hx : x ∈ cell a b n i) : a ≤ b := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have horder : grid a b n i ≤ grid a b n (i + 1) := le_trans hx.1 hx.2
  have hq : 0 ≤ (b - a) / (n : ℝ) := by
    rw [← grid_step a b n i hn]
    linarith
  have hba : 0 ≤ b - a := by
    rcases div_nonneg_iff.mp hq with h | h
    · exact h.1
    · exact False.elim ((not_le_of_gt hnR) h.2)
  exact sub_nonneg.mp hba

private theorem intervalIntegrable_subinterval
    (g : ℝ → ℝ) (a b c d : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c) (hdb : d ≤ b)
    (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable g volume c d := by
  apply hg.mono_set
  simpa [Set.uIcc_of_le hab, Set.uIcc_of_le hcd] using
    (Set.Icc_subset_Icc hac hdb)

private def splineAux (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℕ → ℝ → ℝ
  | 0 => fun _ => f (grid a b n 0)
  | k + 1 => fun x =>
      splineAux f a b n k (min x (grid a b n k)) +
        ((f (grid a b n (k + 1)) - f (grid a b n k)) /
          (grid a b n (k + 1) - grid a b n k)) *
        max (x - grid a b n k) 0

private theorem continuous_splineAux (f : ℝ → ℝ) (a b : ℝ) (n k : ℕ) :
    Continuous (splineAux f a b n k) := by
  induction k with
  | zero =>
      exact continuous_const
  | succ k ih =>
      simpa only [splineAux] using
        (ih.comp (continuous_id.min continuous_const)).add
          (continuous_const.mul
            ((continuous_id.sub continuous_const).max continuous_const))

private theorem splineAux_node (f : ℝ → ℝ) (a b : ℝ) (n k : ℕ)
    (hlt : a < b) (hn : 0 < n) :
    splineAux f a b n k (grid a b n k) = f (grid a b n k) := by
  induction k with
  | zero =>
      simp [splineAux]
  | succ k ih =>
      have hstep : 0 < grid a b n (k + 1) - grid a b n k := by
        rw [grid_step a b n k hn]
        exact div_pos (sub_pos.mpr hlt) (by exact_mod_cast hn)
      have hgrid : grid a b n k ≤ grid a b n (k + 1) := by
        linarith
      have hmin :
          min (grid a b n (k + 1)) (grid a b n k) = grid a b n k :=
        min_eq_right hgrid
      have hmax :
          max (grid a b n (k + 1) - grid a b n k) 0 =
            grid a b n (k + 1) - grid a b n k :=
        max_eq_left (sub_nonneg.mpr hgrid)
      simp only [splineAux]
      rw [hmin, hmax, ih]
      field_simp [ne_of_gt hstep] <;> ring

private theorem splineAux_stable (f : ℝ → ℝ) (a b : ℝ) (n : ℕ)
    (hab : a ≤ b) (hn : 0 < n) (x : ℝ) {k m : ℕ}
    (hkm : k ≤ m) (hx : x ≤ grid a b n k) :
    splineAux f a b n m x = splineAux f a b n k x := by
  rcases Nat.exists_eq_add_of_le hkm with ⟨r, rfl⟩
  induction r with
  | zero =>
      simp
  | succ r ih =>
      have hxr : x ≤ grid a b n (k + r) :=
        le_trans hx (grid_mono a b n k (k + r) hab hn (Nat.le_add_right k r))
      have hmin : min x (grid a b n (k + r)) = x :=
        min_eq_left hxr
      have hmax : max (x - grid a b n (k + r)) 0 = 0 :=
        max_eq_right (sub_nonpos.mpr hxr)
      change splineAux f a b n (Nat.succ (k + r)) x = splineAux f a b n k x
      simp only [splineAux]
      rw [hmin, hmax, ih (Nat.le_add_right k r)]
      simp

private theorem splineAux_on_cell (f : ℝ → ℝ) (a b : ℝ) (n i : ℕ) (x : ℝ)
    (hlt : a < b) (hn : 0 < n) (hi : i < n)
    (hx : x ∈ cell a b n i) :
    splineAux f a b n n x =
      f (grid a b n i) +
        ((f (grid a b n (i + 1)) - f (grid a b n i)) /
          (grid a b n (i + 1) - grid a b n i)) *
        (x - grid a b n i) := by
  have hab : a ≤ b := le_of_lt hlt
  have hbase : splineAux f a b n (i + 1) x =
      f (grid a b n i) +
        ((f (grid a b n (i + 1)) - f (grid a b n i)) /
          (grid a b n (i + 1) - grid a b n i)) *
        (x - grid a b n i) := by
    simp only [splineAux]
    rw [min_eq_right hx.1]
    rw [max_eq_left (sub_nonneg.mpr hx.1)]
    rw [splineAux_node f a b n i hlt hn]
  calc
    splineAux f a b n n x = splineAux f a b n (i + 1) x :=
      splineAux_stable f a b n hab hn x (Nat.succ_le_iff.mpr hi) hx.2
    _ = _ := hbase

theorem gap1 (a b : ℝ) (n i : ℕ) (hn : 0 < n) (hi : i ≤ n) :
    grid a b n i = a + ((i : ℝ) / n) * (b - a) := by
  rfl

theorem gap2 (f φ : ℝ → ℝ) (a b : ℝ) (n : ℕ)
    (hφ : Approximant f a b n φ) :
    ContinuousOn φ (Set.Icc a b) := by
  exact hφ.1

theorem gap3 (f φ : ℝ → ℝ) (a b : ℝ) (n : ℕ)
    (hab : a ≤ b) (hφ : Approximant f a b n φ) :
    IntervalIntegrable φ volume a b := by
  apply ContinuousOn.intervalIntegrable
  simpa [Set.uIcc_of_le hab] using hφ.1

theorem gap4 (f φ : ℝ → ℝ) (a b : ℝ) (n i : ℕ) (x : ℝ)
    (hi : i < n) (hx : x ∈ cell a b n i)
    (hφ : Approximant f a b n φ) :
    lowerValue f a b n i ≤ φ x := by
  exact (hφ.2 i hi x hx).1

theorem gap5 (f φ : ℝ → ℝ) (a b : ℝ) (n i : ℕ) (x : ℝ)
    (hi : i < n) (hx : x ∈ cell a b n i)
    (hφ : Approximant f a b n φ) :
    φ x ≤ upperValue f a b n i := by
  exact (hφ.2 i hi x hx).2

theorem gap6 (f : ℝ → ℝ) (a b : ℝ) (n i : ℕ) (x : ℝ)
    (hf : RiemannIntegrableOn f a b)
    (hi : i < n) (hx : x ∈ cell a b n i) :
    lowerValue f a b n i ≤ f x := by
  have hn : 0 < n := Nat.zero_lt_of_lt hi
  have hab : a ≤ b := cell_mem_forces_order a b n i x hn hx
  have hcell := cell_subset_global a b n i hab hn hi
  apply csInf_le
  · exact hf.2.1.bddBelow.mono (Set.image_mono hcell)
  · exact ⟨x, hx, rfl⟩

theorem gap7 (f : ℝ → ℝ) (a b : ℝ) (n i : ℕ) (x : ℝ)
    (hf : RiemannIntegrableOn f a b)
    (hi : i < n) (hx : x ∈ cell a b n i) :
    f x ≤ upperValue f a b n i := by
  have hn : 0 < n := Nat.zero_lt_of_lt hi
  have hab : a ≤ b := cell_mem_forces_order a b n i x hn hx
  have hcell := cell_subset_global a b n i hab hn hi
  apply le_csSup
  · exact hf.2.1.bddAbove.mono (Set.image_mono hcell)
  · exact ⟨x, hx, rfl⟩

theorem gap8 (f φ : ℝ → ℝ) (a b : ℝ) (n i : ℕ) (x : ℝ)
    (hf : RiemannIntegrableOn f a b)
    (hφ : Approximant f a b n φ)
    (hi : i < n) (hx : x ∈ cell a b n i) :
    |φ x - f x| ≤ osc f a b n i := by
  have hφb := hφ.2 i hi x hx
  have hfb₁ := gap6 f a b n i x hf hi hx
  have hfb₂ := gap7 f a b n i x hf hi hx
  rw [abs_le]
  dsimp [osc]
  constructor <;> linarith

theorem gap9 (f φ : ℝ → ℝ) (a b c : ℝ)
    (hab : a ≤ b) (hc : c ∈ Set.Icc a b)
    (hf : IntervalIntegrable f volume a b)
    (hφ : IntervalIntegrable φ volume a b) :
    |(∫ x in a..c, f x) - ∫ x in a..c, φ x| ≤
      ∫ x in a..c, |f x - φ x| := by
  have hf_ac : IntervalIntegrable f volume a c :=
    intervalIntegrable_subinterval f a b a c hab hc.1 le_rfl hc.2 hf
  have hφ_ac : IntervalIntegrable φ volume a c :=
    intervalIntegrable_subinterval φ a b a c hab hc.1 le_rfl hc.2 hφ
  calc
    |(∫ x in a..c, f x) - ∫ x in a..c, φ x| =
        |∫ x in a..c, (f x - φ x)| := by
          rw [intervalIntegral.integral_sub hf_ac hφ_ac]
    _ ≤ ∫ x in a..c, |f x - φ x| := by
      simpa [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm (μ := volume)
          (f := fun x : ℝ => f x - φ x) hc.1)

theorem gap10 (f φ : ℝ → ℝ) (a b c : ℝ)
    (hab : a ≤ b) (hc : c ∈ Set.Icc a b)
    (hf : IntervalIntegrable (fun x => |f x - φ x|) volume a b) :
    (∫ x in a..c, |f x - φ x|) ≤
      ∫ x in a..b, |f x - φ x| := by
  let g : ℝ → ℝ := fun x => |f x - φ x|
  have hg_ac : IntervalIntegrable g volume a c :=
    intervalIntegrable_subinterval g a b a c hab hc.1 le_rfl hc.2 hf
  have hg_cb : IntervalIntegrable g volume c b :=
    intervalIntegrable_subinterval g a b c b hab hc.2 hc.1 le_rfl hf
  have hnonneg : 0 ≤ ∫ x in c..b, g x :=
    intervalIntegral.integral_nonneg hc.2 (fun x hx => abs_nonneg _)
  calc
    (∫ x in a..c, |f x - φ x|) = ∫ x in a..c, g x := rfl
    _ ≤ (∫ x in a..c, g x) + ∫ x in c..b, g x :=
      le_add_of_nonneg_right hnonneg
    _ = ∫ x in a..b, g x :=
      intervalIntegral.integral_add_adjacent_intervals hg_ac hg_cb
    _ = ∫ x in a..b, |f x - φ x| := rfl

theorem gap11 (f φ : ℝ → ℝ) (a b c : ℝ)
    (hab : a ≤ b) (hc : c ∈ Set.Icc a b)
    (hf : IntervalIntegrable f volume a b)
    (hφ : IntervalIntegrable φ volume a b) :
    |(∫ x in a..c, f x) - ∫ x in a..c, φ x| ≤
      ∫ x in a..b, |f x - φ x| := by
  have hd : IntervalIntegrable (fun x => |f x - φ x|) volume a b := by
    simpa [Real.norm_eq_abs] using (hf.sub hφ).norm
  exact le_trans (gap9 f φ a b c hab hc hf hφ)
    (gap10 f φ a b c hab hc hd)

theorem gap12 (f φ : ℝ → ℝ) (a b : ℝ) (n : ℕ)
    (hab : a ≤ b) (hn : 0 < n)
    (hf : IntervalIntegrable (fun x => |f x - φ x|) volume a b) :
    (∫ x in a..b, |f x - φ x|) =
      ∑ i ∈ Finset.range n,
        ∫ x in (grid a b n i)..(grid a b n (i + 1)), |f x - φ x| := by
  let g : ℝ → ℝ := fun x => |f x - φ x|
  have hsum : ∀ k : ℕ, k ≤ n →
      (∑ i ∈ Finset.range k,
        ∫ x in (grid a b n i)..(grid a b n (i + 1)), g x) =
      ∫ x in (grid a b n 0)..(grid a b n k), g x := by
    intro k
    induction k with
    | zero =>
        intro hk
        simp
    | succ k ih =>
        intro hk
        have hk' : k ≤ n := le_trans (Nat.le_succ k) hk
        rw [Finset.sum_range_succ, ih hk']
        have h0 := grid_point_mem a b n 0 hab hn (Nat.zero_le n)
        have hpk := grid_point_mem a b n k hab hn hk'
        have hps := grid_point_mem a b n (k + 1) hab hn hk
        have h0k : grid a b n 0 ≤ grid a b n k :=
          grid_mono a b n 0 k hab hn (Nat.zero_le k)
        have hks : grid a b n k ≤ grid a b n (k + 1) :=
          grid_mono a b n k (k + 1) hab hn (Nat.le_succ k)
        have hleft : IntervalIntegrable g volume
            (grid a b n 0) (grid a b n k) :=
          intervalIntegrable_subinterval g a b (grid a b n 0) (grid a b n k)
            hab h0k h0.1 hpk.2 hf
        have hright : IntervalIntegrable g volume
            (grid a b n k) (grid a b n (k + 1)) :=
          intervalIntegrable_subinterval g a b (grid a b n k) (grid a b n (k + 1))
            hab hks hpk.1 hps.2 hf
        exact intervalIntegral.integral_add_adjacent_intervals hleft hright
  symm
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simpa [g, grid, hn0] using hsum n le_rfl

theorem gap13 (f φ : ℝ → ℝ) (a b : ℝ) (n : ℕ)
    (hab : a ≤ b) (hn : 0 < n)
    (hf : RiemannIntegrableOn f a b)
    (hφ : Approximant f a b n φ) :
    (∑ i ∈ Finset.range n,
        ∫ x in (grid a b n i)..(grid a b n (i + 1)), |f x - φ x|) ≤
      oscSum f a b n := by
  have hφi : IntervalIntegrable φ volume a b := gap3 f φ a b n hab hφ
  have hd : IntervalIntegrable (fun x => |f x - φ x|) volume a b := by
    simpa [Real.norm_eq_abs] using (hf.1.sub hφi).norm
  unfold oscSum
  apply Finset.sum_le_sum
  intro i hiFin
  simp only [Finset.mem_range] at hiFin
  have hli := grid_point_mem a b n i hab hn (Nat.le_of_lt hiFin)
  have hri := grid_point_mem a b n (i + 1) hab hn
    (Nat.succ_le_iff.mpr hiFin)
  have hgrid : grid a b n i ≤ grid a b n (i + 1) :=
    grid_mono a b n i (i + 1) hab hn (Nat.le_succ i)
  have hdi : IntervalIntegrable (fun x => |f x - φ x|) volume
      (grid a b n i) (grid a b n (i + 1)) :=
    intervalIntegrable_subinterval (fun x => |f x - φ x|) a b
      (grid a b n i) (grid a b n (i + 1)) hab hgrid hli.1 hri.2 hd
  have hconst : IntervalIntegrable (fun _ : ℝ => osc f a b n i) volume
      (grid a b n i) (grid a b n (i + 1)) := intervalIntegrable_const
  calc
    (∫ x in (grid a b n i)..(grid a b n (i + 1)), |f x - φ x|) ≤
        ∫ _ in (grid a b n i)..(grid a b n (i + 1)), osc f a b n i := by
      apply intervalIntegral.integral_mono_on hgrid hdi hconst
      intro x hx
      simpa [abs_sub_comm] using gap8 f φ a b n i x hf hφ hiFin hx
    _ = osc f a b n i *
        (grid a b n (i + 1) - grid a b n i) := by
      simp [intervalIntegral.integral_const]
      ring

theorem gap14 (f φ : ℝ → ℝ) (a b : ℝ) (n : ℕ)
    (hab : a ≤ b) (hn : 0 < n)
    (hf : RiemannIntegrableOn f a b)
    (hφ : Approximant f a b n φ) :
    (∫ x in a..b, |f x - φ x|) ≤ oscSum f a b n := by
  have hφi : IntervalIntegrable φ volume a b := gap3 f φ a b n hab hφ
  have hd : IntervalIntegrable (fun x => |f x - φ x|) volume a b := by
    simpa [Real.norm_eq_abs] using (hf.1.sub hφi).norm
  rw [gap12 f φ a b n hab hn hd]
  exact gap13 f φ a b n hab hn hf hφ

theorem gap15 (a b : ℝ) (n i : ℕ)
    (hab : a ≤ b) (hn : 0 < n) (hi : i < n) :
    |grid a b n (i + 1) - grid a b n i| = (b - a) / (n : ℝ) := by
  rw [grid_step a b n i hn]
  rw [abs_of_nonneg]
  exact div_nonneg (sub_nonneg.mpr hab) (by positivity)

theorem gap16 (a b : ℝ) :
    Tendsto (mesh a b) atTop (nhds (0 : ℝ)) := by
  have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  simpa [mesh, div_eq_mul_inv] using
    (tendsto_const_nhds.mul hzero :
      Tendsto (fun n : ℕ => |b - a| * ((1 : ℝ) / n)) atTop
        (nhds (|b - a| * 0)))

theorem gap17 (a b : ℝ) :
    Tendsto (mesh a b) atTop (nhds (0 : ℝ)) := by
  exact gap16 a b

theorem gap18 (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf : RiemannIntegrableOn f a b) :
    Tendsto (oscSum f a b) atTop (nhds (0 : ℝ)) := by
  exact hf.2.2

theorem gap19 (f : ℝ → ℝ) (a b c : ℝ)
    (hab : a ≤ b) (hc : c ∈ Set.Icc a b)
    (hf : RiemannIntegrableOn f a b)
    (φ : ℕ → ℝ → ℝ)
    (hφ : ∀ n, 0 < n → Approximant f a b n (φ n)) :
    Tendsto (fun n => ∫ x in a..c, φ n x) atTop
      (nhds (∫ x in a..c, f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hf.2.2) ε hε
  refine ⟨max N 1, ?_⟩
  intro n hnmax
  have hNn : N ≤ n := le_trans (Nat.le_max_left N 1) hnmax
  have hn1 : 1 ≤ n := le_trans (Nat.le_max_right N 1) hnmax
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hosc_n := hN n hNn
  have hφn := hφ n hn
  have hφint : IntervalIntegrable (φ n) volume a b :=
    gap3 f (φ n) a b n hab hφn
  have hmain :
      |(∫ x in a..c, f x) - ∫ x in a..c, φ n x| ≤ oscSum f a b n :=
    le_trans
      (gap11 f (φ n) a b c hab hc hf.1 hφint)
      (gap14 f (φ n) a b n hab hn hf hφn)
  rw [Real.dist_eq]
  rw [Real.dist_eq, sub_zero] at hosc_n
  calc
    |(∫ x in a..c, φ n x) - ∫ x in a..c, f x| =
        |(∫ x in a..c, f x) - ∫ x in a..c, φ n x| := abs_sub_comm _ _
    _ ≤ oscSum f a b n := hmain
    _ ≤ |oscSum f a b n| := le_abs_self _
    _ < ε := hosc_n

theorem gap20 (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf : RiemannIntegrableOn f a b) :
    ∃ φ : ℕ → ℝ → ℝ,
      (∀ n, 0 < n → ContinuousOn (φ n) (Set.Icc a b)) ∧
      ∀ c ∈ Set.Icc a b,
        Tendsto (fun n => ∫ x in a..c, φ n x) atTop
          (nhds (∫ x in a..c, f x)) := by
  by_cases heq : a = b
  · subst b
    refine ⟨fun _ _ => f a, ?_, ?_⟩
    · intro n hn
      exact continuousOn_const
    · intro c hc
      have hca : c = a := le_antisymm hc.2 hc.1
      subst c
      simp
  · have hlt : a < b := lt_of_le_of_ne hab heq
    let φ : ℕ → ℝ → ℝ := fun n => splineAux f a b n n
    have hφ : ∀ n, 0 < n → Approximant f a b n (φ n) := by
      intro n hn
      constructor
      · change ContinuousOn (splineAux f a b n n) (Set.Icc a b)
        exact (continuous_splineAux f a b n n).continuousOn
      · intro i hi x hx
        have hgrid : grid a b n i ≤ grid a b n (i + 1) :=
          grid_mono a b n i (i + 1) hab hn (Nat.le_succ i)
        have hxL : grid a b n i ∈ cell a b n i := ⟨le_rfl, hgrid⟩
        have hxR : grid a b n (i + 1) ∈ cell a b n i := ⟨hgrid, le_rfl⟩
        have hL0 := gap6 f a b n i (grid a b n i) hf hi hxL
        have hL1 := gap6 f a b n i (grid a b n (i + 1)) hf hi hxR
        have hU0 := gap7 f a b n i (grid a b n i) hf hi hxL
        have hU1 := gap7 f a b n i (grid a b n (i + 1)) hf hi hxR
        have hstep : 0 < grid a b n (i + 1) - grid a b n i := by
          rw [grid_step a b n i hn]
          exact div_pos (sub_pos.mpr hlt) (by exact_mod_cast hn)
        let t : ℝ := (x - grid a b n i) /
          (grid a b n (i + 1) - grid a b n i)
        have ht0 : 0 ≤ t := by
          dsimp [t]
          exact div_nonneg (sub_nonneg.mpr hx.1) (le_of_lt hstep)
        have ht1 : t ≤ 1 := by
          dsimp [t]
          apply (div_le_one hstep).2
          linarith [hx.2]
        have hformula : φ n x = f (grid a b n i) +
            t * (f (grid a b n (i + 1)) - f (grid a b n i)) := by
          change splineAux f a b n n x = _
          rw [splineAux_on_cell f a b n i x hlt hn hi hx]
          dsimp [t]
          ring
        have hpL0 : 0 ≤ (1 - t) *
            (f (grid a b n i) - lowerValue f a b n i) :=
          mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hL0)
        have hpL1 : 0 ≤ t *
            (f (grid a b n (i + 1)) - lowerValue f a b n i) :=
          mul_nonneg ht0 (sub_nonneg.mpr hL1)
        have hpU0 : 0 ≤ (1 - t) *
            (upperValue f a b n i - f (grid a b n i)) :=
          mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hU0)
        have hpU1 : 0 ≤ t *
            (upperValue f a b n i - f (grid a b n (i + 1))) :=
          mul_nonneg ht0 (sub_nonneg.mpr hU1)
        rw [hformula]
        constructor <;> nlinarith
    refine ⟨φ, ?_, ?_⟩
    · intro n hn
      exact (hφ n hn).1
    · intro c hc
      exact gap19 f a b c hab hc hf φ hφ

end
end ProofGap.Exercise2199
