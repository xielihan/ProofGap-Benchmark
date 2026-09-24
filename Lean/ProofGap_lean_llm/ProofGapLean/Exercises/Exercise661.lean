import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite

namespace ProofGap.Exercise661

noncomputable section

def envelope (F : ℕ → ℝ → ℝ) (q : ℝ → ℕ) (x : ℝ) : ℝ :=
  (q x : ℝ) * ((Finset.Icc 1 (q x)).sum (fun k => |F k x|) + 1)

/-- Exercise 661, gap 1; replace the overloaded `f(n,x),f(x)` by a family `F` and its envelope. -/
theorem gap1 (F : ℕ → ℝ → ℝ) (q : ℝ → ℕ) (x : ℝ) (n : ℕ)
    (hn : 1 ≤ n) (hnq : n ≤ q x) (hq : 1 ≤ q x) :
    |F n x / envelope F q x| =
      |F n x| / ((q x : ℝ) *
        ((Finset.Icc 1 (q x)).sum (fun k => |F k x|) + 1)) := by
  unfold envelope
  rw [abs_div]
  have hqpos : 0 < q x := lt_of_lt_of_le Nat.zero_lt_one hq
  have hqpos' : (0 : ℝ) < (q x : ℝ) := (Nat.cast_pos).2 hqpos
  have hsum :
      0 ≤ (Finset.Icc 1 (q x)).sum (fun k => |F k x|) :=
    Finset.sum_nonneg (fun k hk => abs_nonneg (F k x))
  have hfactor :
      0 < (Finset.Icc 1 (q x)).sum (fun k => |F k x|) + 1 :=
    add_pos_of_nonneg_of_pos hsum zero_lt_one
  have hden :
      0 < (q x : ℝ) *
        ((Finset.Icc 1 (q x)).sum (fun k => |F k x|) + 1) :=
    mul_pos hqpos' hfactor
  rw [abs_of_pos hden]

/-- Exercise 661, gap 2; make the finite sum and positive index explicit. -/
theorem gap2 (F : ℕ → ℝ → ℝ) (q : ℝ → ℕ) (x : ℝ) (n : ℕ)
    (hn : 1 ≤ n) (hnq : n ≤ q x) (hq : 1 ≤ q x) :
    |F n x| / ((q x : ℝ) *
        ((Finset.Icc 1 (q x)).sum (fun k => |F k x|) + 1)) <
      1 / (q x : ℝ) := by
  have hqpos : 0 < q x := lt_of_lt_of_le Nat.zero_lt_one hq
  have hqpos' : (0 : ℝ) < (q x : ℝ) := (Nat.cast_pos).2 hqpos
  have hqne : (q x : ℝ) ≠ 0 := ne_of_gt hqpos'
  have hsum :
      0 ≤ (Finset.Icc 1 (q x)).sum (fun k => |F k x|) :=
    Finset.sum_nonneg (fun k hk => abs_nonneg (F k x))
  have hfactor :
      0 < (Finset.Icc 1 (q x)).sum (fun k => |F k x|) + 1 :=
    add_pos_of_nonneg_of_pos hsum zero_lt_one
  have hden :
      0 < (q x : ℝ) *
        ((Finset.Icc 1 (q x)).sum (fun k => |F k x|) + 1) :=
    mul_pos hqpos' hfactor
  have hnmem : n ∈ Finset.Icc 1 (q x) :=
    Finset.mem_Icc.mpr ⟨hn, hnq⟩
  have hterm :
      |F n x| ≤ (Finset.Icc 1 (q x)).sum (fun k => |F k x|) :=
    Finset.single_le_sum (fun k hk => abs_nonneg (F k x)) hnmem
  have hlt :
      |F n x| < (Finset.Icc 1 (q x)).sum (fun k => |F k x|) + 1 :=
    lt_of_le_of_lt hterm (lt_add_of_pos_right _ zero_lt_one)
  apply (div_lt_iff₀ hden).2
  calc
    |F n x| <
        (Finset.Icc 1 (q x)).sum (fun k => |F k x|) + 1 := hlt
    _ = (1 / (q x : ℝ)) *
        ((q x : ℝ) *
          ((Finset.Icc 1 (q x)).sum (fun k => |F k x|) + 1)) := by
      symm
      calc
        (1 / (q x : ℝ)) *
            ((q x : ℝ) *
              ((Finset.Icc 1 (q x)).sum (fun k => |F k x|) + 1)) =
            ((1 / (q x : ℝ)) * (q x : ℝ)) *
              ((Finset.Icc 1 (q x)).sum (fun k => |F k x|) + 1) := by
          rw [← mul_assoc]
        _ = (Finset.Icc 1 (q x)).sum (fun k => |F k x|) + 1 := by
          simp [hqne]

/-- Exercise 661, gap 3. -/
theorem gap3 (F : ℕ → ℝ → ℝ) (q : ℝ → ℕ) (x : ℝ) (n : ℕ)
    (hn : 1 ≤ n) (hnq : n ≤ q x) (hq : 1 ≤ q x) :
    |F n x / envelope F q x| < 1 / (q x : ℝ) := by
  calc
    |F n x / envelope F q x| =
        |F n x| / ((q x : ℝ) *
          ((Finset.Icc 1 (q x)).sum (fun k => |F k x|) + 1)) :=
      gap1 F q x n hn hnq hq
    _ < 1 / (q x : ℝ) := gap2 F q x n hn hnq hq

/-- Exercise 661, gap 4; bind the integer selector tending to infinity. -/
theorem gap4 (F : ℕ → ℝ → ℝ) (q : ℝ → ℕ) (n : ℕ) (hn : 1 ≤ n)
    (hq : Filter.Tendsto q Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun x => F n x / envelope F q x)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hev : ∀ᶠ y in Filter.atTop, max n N ≤ q y :=
    (Filter.tendsto_atTop.1 hq) (max n N)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 hev
  refine ⟨X, ?_⟩
  intro y hy
  have hmax : max n N ≤ q y := hX y hy
  have hnq : n ≤ q y :=
    le_trans (Nat.le_max_left n N) hmax
  have hNq : N ≤ q y :=
    le_trans (Nat.le_max_right n N) hmax
  have hq1 : 1 ≤ q y := le_trans hn hnq
  have hbound :
      |F n y / envelope F q y| < 1 / (q y : ℝ) :=
    gap3 F q y n hn hnq hq1
  have hNq' : (N : ℝ) ≤ (q y : ℝ) := (Nat.cast_le).2 hNq
  have honeN : 1 < (N : ℝ) * ε :=
    (div_lt_iff₀ hε).1 hN
  have hmul : (N : ℝ) * ε ≤ (q y : ℝ) * ε :=
    mul_le_mul_of_nonneg_right hNq' (le_of_lt hε)
  have honeq : 1 < ε * (q y : ℝ) := by
    calc
      1 < (N : ℝ) * ε := honeN
      _ ≤ (q y : ℝ) * ε := hmul
      _ = ε * (q y : ℝ) := mul_comm _ _
  have hqposNat : 0 < q y :=
    lt_of_lt_of_le Nat.zero_lt_one hq1
  have hqpos : (0 : ℝ) < (q y : ℝ) :=
    (Nat.cast_pos).2 hqposNat
  have hrecip : 1 / (q y : ℝ) < ε :=
    (div_lt_iff₀ hqpos).2 honeq
  simpa only [Real.dist_eq, sub_zero] using
    (lt_trans hbound hrecip)

/-- Exercise 661, gap 5. -/
theorem gap5 (F : ℕ → ℝ → ℝ) (q : ℝ → ℕ)
    (hq : Filter.Tendsto q Filter.atTop Filter.atTop) :
    ∀ n ≥ 1, Filter.Tendsto (fun x => F n x / envelope F q x)
      Filter.atTop (nhds 0) := by
  intro n hn
  exact gap4 F q n hn hq

/-- Exercise 661, gap 6; correct the overloaded self-reference by constructing a separate dominating function. -/
theorem gap6 (x₀ : ℝ) (F : ℕ → ℝ → ℝ) :
    ∃ g : ℝ → ℝ, ∀ n ≥ 1,
      Filter.Tendsto (fun x => F n x / g x) Filter.atTop (nhds 0) := by
  refine ⟨fun _ => 0, ?_⟩
  intro n hn
  simpa using
    (Filter.tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) Filter.atTop (nhds 0))

end

end ProofGap.Exercise661
