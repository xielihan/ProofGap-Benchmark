import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2732

noncomputable section

def term (x y : ℝ) (n : ℕ) : ℝ :=
  x ^ n * y ^ n / (x ^ n + y ^ n)

def rewrittenTerm (x y : ℝ) (n : ℕ) : ℝ :=
  x ^ n / (1 + (x / y) ^ n)

theorem gap1 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    ∀ n : ℕ, 1 ≤ n → term x y n = rewrittenTerm x y n := by
  intro n hn
  have hxn : 0 < x ^ n := pow_pos hx n
  have hyn : 0 < y ^ n := pow_pos hy n
  have hyn0 : y ^ n ≠ 0 := ne_of_gt hyn
  have hsum : x ^ n + y ^ n ≠ 0 := ne_of_gt (add_pos hxn hyn)
  unfold term rewrittenTerm
  rw [div_pow]
  field_simp [hyn0, hsum]
  <;> ring

theorem gap2 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    ∀ n : ℕ, 1 ≤ n → 0 < rewrittenTerm x y n := by
  intro n hn
  unfold rewrittenTerm
  exact div_pos (pow_pos hx n)
    (add_pos zero_lt_one (pow_pos (div_pos hx hy) n))

theorem gap3 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    ∀ n : ℕ, 1 ≤ n → rewrittenTerm x y n ≤ x ^ n := by
  intro n hn
  have ha : 0 ≤ x ^ n := le_of_lt (pow_pos hx n)
  have hr : 0 ≤ (x / y) ^ n := pow_nonneg (le_of_lt (div_pos hx hy)) n
  have hden : 0 < 1 + (x / y) ^ n :=
    add_pos_of_pos_of_nonneg zero_lt_one hr
  unfold rewrittenTerm
  apply (div_le_iff₀ hden).2
  nlinarith [mul_nonneg ha hr]

theorem gap4 (x : ℝ) (hx0 : 0 < x) :
    ∀ n : ℕ, 1 ≤ n → 0 < x ^ n := by
  intro n hn
  exact pow_pos hx0 n

theorem gap5 (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Summable (fun n : ℕ => x ^ (n + 1)) := by
  have hnorm : ‖x‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_pos hx0] using hx1
  have hgeo : Summable (fun n : ℕ => x ^ n) :=
    summable_geometric_of_norm_lt_one hnorm
  simpa [pow_succ, mul_comm] using hgeo.mul_left x

theorem gap6 (x y : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hy : 0 < y) :
    Summable (fun n : ℕ => |term x y (n + 1)|) := by
  apply (gap5 x hx0 hx1).of_norm_bounded
  intro n
  have hn : 1 ≤ n + 1 := Nat.le_add_left 1 n
  have ht : 0 < term x y (n + 1) := by
    rw [gap1 x y hx0 hy (n + 1) hn]
    exact gap2 x y hx0 hy (n + 1) hn
  have hle : term x y (n + 1) ≤ x ^ (n + 1) := by
    rw [gap1 x y hx0 hy (n + 1) hn]
    exact gap3 x y hx0 hy (n + 1) hn
  simpa [Real.norm_eq_abs, abs_of_pos ht] using hle

theorem gap7 (x y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) (hx : 0 < x) :
    Summable (fun n : ℕ => |term x y (n + 1)|) := by
  simpa only [term, mul_comm, add_comm] using gap6 y x hy0 hy1 hx

theorem gap8 :
    {q : ℝ × ℝ |
        0 < q.1 ∧ 0 < q.2 ∧
          Summable (fun n : ℕ => |term q.1 q.2 (n + 1)|)} =
      {q : ℝ × ℝ | 0 < min q.1 q.2 ∧ min q.1 q.2 < 1} := by
  ext q
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hy, hs⟩
    refine ⟨(lt_min_iff).2 ⟨hx, hy⟩, ?_⟩
    by_contra hlt
    have hm : 1 ≤ min q.1 q.2 := le_of_not_gt hlt
    have hx1 : 1 ≤ q.1 := le_trans hm (min_le_left q.1 q.2)
    have hy1 : 1 ≤ q.2 := le_trans hm (min_le_right q.1 q.2)
    have hpow : ∀ (z : ℝ), 1 ≤ z → ∀ k : ℕ, 1 ≤ z ^ k := by
      intro z hz k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ]
          nlinarith [mul_nonneg (sub_nonneg.mpr ih) (sub_nonneg.mpr hz)]
    have hlower : ∀ n : ℕ, (1 / 2 : ℝ) ≤ |term q.1 q.2 (n + 1)| := by
      intro n
      have hxp : 1 ≤ q.1 ^ (n + 1) := hpow q.1 hx1 (n + 1)
      have hyp : 1 ≤ q.2 ^ (n + 1) := hpow q.2 hy1 (n + 1)
      have hden : 0 < q.1 ^ (n + 1) + q.2 ^ (n + 1) :=
        add_pos (lt_of_lt_of_le zero_lt_one hxp)
          (lt_of_lt_of_le zero_lt_one hyp)
      have hraw : (1 / 2 : ℝ) ≤ term q.1 q.2 (n + 1) := by
        unfold term
        apply (le_div_iff₀ hden).2
        nlinarith [mul_nonneg (sub_nonneg.mpr hxp) (sub_nonneg.mpr hyp)]
      have ht0 : 0 ≤ term q.1 q.2 (n + 1) :=
        le_trans (by norm_num) hraw
      simpa [abs_of_nonneg ht0] using hraw
    have htend :
        Tendsto (fun n : ℕ => |term q.1 q.2 (n + 1)|) atTop (nhds 0) :=
      hs.tendsto_atTop_zero
    have hevent :
        ∀ᶠ n : ℕ in atTop, |term q.1 q.2 (n + 1)| < (1 / 2 : ℝ) :=
      (tendsto_order.1 htend).2 (1 / 2) (by norm_num)
    rcases hevent.exists with ⟨n, hn⟩
    exact (not_lt_of_ge (hlower n)) hn
  · rintro ⟨hmin0, hmin1⟩
    have hx : 0 < q.1 := lt_of_lt_of_le hmin0 (min_le_left q.1 q.2)
    have hy : 0 < q.2 := lt_of_lt_of_le hmin0 (min_le_right q.1 q.2)
    refine ⟨hx, hy, ?_⟩
    by_cases hxy : q.1 ≤ q.2
    · have hx1 : q.1 < 1 := by
        simpa [min_eq_left hxy] using hmin1
      exact gap6 q.1 q.2 hx hx1 hy
    · have hyx : q.2 ≤ q.1 := le_of_lt (lt_of_not_ge hxy)
      have hy1 : q.2 < 1 := by
        simpa [min_eq_right hyx] using hmin1
      exact gap7 q.1 q.2 hy hy1 hx

theorem gap9 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (0 < min x y ∧ min x y < 1) ↔
      Summable (fun n : ℕ => term x y (n + 1)) := by
  have hterm_pos : ∀ n : ℕ, 0 < term x y (n + 1) := by
    intro n
    have hn : 1 ≤ n + 1 := Nat.le_add_left 1 n
    rw [gap1 x y hx hy (n + 1) hn]
    exact gap2 x y hx hy (n + 1) hn
  have habseq :
      (fun n : ℕ => |term x y (n + 1)|) =
        (fun n : ℕ => term x y (n + 1)) := by
    funext n
    exact abs_of_pos (hterm_pos n)
  constructor
  · rintro ⟨hmin0, hmin1⟩
    have hx0 : 0 < x := lt_of_lt_of_le hmin0 (min_le_left x y)
    have hy0 : 0 < y := lt_of_lt_of_le hmin0 (min_le_right x y)
    have habs : Summable (fun n : ℕ => |term x y (n + 1)|) := by
      by_cases hxy : x ≤ y
      · have hx1 : x < 1 := by
          simpa [min_eq_left hxy] using hmin1
        exact gap6 x y hx0 hx1 hy0
      · have hyx : y ≤ x := le_of_lt (lt_of_not_ge hxy)
        have hy1 : y < 1 := by
          simpa [min_eq_right hyx] using hmin1
        exact gap7 x y hy0 hy1 hx0
    rw [← habseq]
    exact habs
  · intro hs
    have habs : Summable (fun n : ℕ => |term x y (n + 1)|) := by
      rw [habseq]
      exact hs
    have hmem :
        (x, y) ∈ {q : ℝ × ℝ |
          0 < q.1 ∧ 0 < q.2 ∧
            Summable (fun n : ℕ => |term q.1 q.2 (n + 1)|)} :=
      ⟨hx, hy, habs⟩
    rw [gap8] at hmem
    simpa using hmem

end

end ProofGap.Exercise2732
