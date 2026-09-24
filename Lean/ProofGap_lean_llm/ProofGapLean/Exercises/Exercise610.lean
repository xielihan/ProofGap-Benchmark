import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Tactic
import Mathlib.Order.Filter.AtTopBot.Ring

namespace ProofGap.Exercise610

noncomputable section

def unitRatio (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  (f (x + 1) - f x) / (g (x + 1) - g x)
def quotient (f g : ℝ → ℝ) (x : ℝ) : ℝ := f x / g x
def HasFiniteLimit (h : ℝ → ℝ) (l : ℝ) : Prop :=
  Filter.Tendsto h Filter.atTop (nhds l)
def HasPosInfiniteLimit (h : ℝ → ℝ) : Prop :=
  Filter.Tendsto h Filter.atTop Filter.atTop
def HasNegInfiniteLimit (h : ℝ → ℝ) : Prop :=
  Filter.Tendsto h Filter.atTop Filter.atBot
def UnitIncreasing (g : ℝ → ℝ) : Prop := ∀ x, g x < g (x + 1)
def τ (x X₀ : ℝ) (n : ℕ) : ℝ := x - X₀ - n
def weight (g : ℝ → ℝ) (X₀ t x : ℝ) (k : ℕ) : ℝ :=
  (g (X₀ + t + k) - g (X₀ + t + k - 1)) / (g x - g (X₀ + t))
def polyG (n : ℕ) (x : ℝ) : ℝ := x ^ (n + 1)
def polyNorm (n : ℕ) (x : ℝ) : ℝ :=
  ((x + 1) ^ (n + 1) - x ^ (n + 1)) / x ^ n
def appNormalized (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((f (x + 1) - f x) / x ^ n) * (1 / polyNorm n x)

private theorem sum_Icc_one_shift_sub (u : ℝ → ℝ) (a : ℝ) :
    ∀ n : ℕ,
      (Finset.Icc 1 n).sum (fun k => u (a + k) - u (a + k - 1)) =
        u (a + n) - u a := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [← Finset.insert_Icc_right_eq_Icc_add_one (a := 1) (b := n) (by omega)]
      rw [Finset.sum_insert (by simp), ih]
      norm_num [Nat.cast_succ]
      ring_nf

/-- Exercise 610, gap 1; bind one tail threshold instead of shadowing it. -/
private theorem polyNorm_hasFiniteLimit (n : ℕ) :
    HasFiniteLimit (polyNorm n) (((n + 1 : ℕ) : ℝ)) := by
  induction n with
  | zero =>
      have hfun : polyNorm 0 = fun _ : ℝ => 1 := by
        funext x
        simp [polyNorm]
      rw [hfun]
      unfold HasFiniteLimit
      simpa only [Nat.zero_add, Nat.cast_one] using
        (tendsto_const_nhds : Filter.Tendsto
          (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1))
  | succ n ih =>
      change Filter.Tendsto (polyNorm n) Filter.atTop
        (nhds (((n + 1 : ℕ) : ℝ))) at ih
      change Filter.Tendsto (polyNorm (Nat.succ n)) Filter.atTop
        (nhds (((Nat.succ n + 1 : ℕ) : ℝ)))
      have hinv : Filter.Tendsto (fun x : ℝ => x⁻¹)
          Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
      have hratio0 : Filter.Tendsto (fun x : ℝ => 1 + x⁻¹)
          Filter.atTop (nhds 1) := by
        convert
          ((tendsto_const_nhds : Filter.Tendsto
            (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1)).add hinv) using 1 <;>
          norm_num
      have hratio : Filter.Tendsto (fun x : ℝ => (x + 1) / x)
          Filter.atTop (nhds 1) := by
        refine hratio0.congr' ?_
        filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
        field_simp [ne_of_gt hx]
      have hrec :
          (fun x : ℝ => (x + 1) / x * polyNorm n x + 1) =ᶠ[Filter.atTop]
            polyNorm (Nat.succ n) := by
        filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
        have hx0 : x ≠ 0 := ne_of_gt hx
        unfold polyNorm
        field_simp [hx0, pow_succ]
        ring_nf
        simp only [pow_succ]
        rw [show n * 2 = n + n by omega, pow_add]
        ring
      have hone : Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
          Filter.atTop (nhds 1) := tendsto_const_nhds
      have hlim := (hratio.mul ih).add hone
      have hlim' := hlim.congr' hrec
      convert hlim' using 1 <;>
        norm_num [Nat.cast_succ, Nat.cast_add] <;> ring

theorem gap1 (f g : ℝ → ℝ) (l : ℝ)
    (h : HasFiniteLimit (unitRatio f g) l) :
    ∀ ε > 0, ∃ X₀ : ℝ, ∀ x ≥ X₀,
      |unitRatio f g x - l| < ε / 2 := by
  change Filter.Tendsto (unitRatio f g) Filter.atTop (nhds l) at h
  rw [Metric.tendsto_atTop] at h
  intro ε hε
  rcases h (ε / 2) (by linarith) with ⟨X₀, hX₀⟩
  refine ⟨X₀, fun x hx => ?_⟩
  simpa [Real.dist_eq] using hX₀ x hx

/-- Exercise 610, gap 2; make the Archimedean integer witness explicit. -/
theorem gap2 (x X₀ : ℝ) (hx : X₀ + 1 < x) :
    ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) ≤ x - X₀ ∧ x - X₀ < n + 1 := by
  have hr : 1 < x - X₀ := by linarith
  have hr0 : 0 ≤ x - X₀ := by linarith
  have hlt := Nat.lt_floor_add_one (x - X₀)
  refine ⟨⌊x - X₀⌋₊, ?_, Nat.floor_le hr0, hlt⟩
  by_contra h
  have hz : ⌊x - X₀⌋₊ = 0 := by omega
  rw [hz] at hlt
  norm_num at hlt
  linarith

/-- Exercise 610, gap 3; define `τ=x-X₀-n`. -/
theorem gap3 (x X₀ : ℝ) (n : ℕ)
    (hn0 : (n : ℝ) ≤ x - X₀) : 0 ≤ τ x X₀ n := by
  unfold τ
  exact sub_nonneg.mpr (by linarith)

/-- Exercise 610, gap 4. -/
theorem gap4 (x X₀ : ℝ) (n : ℕ)
    (hn1 : x - X₀ < n + 1) : τ x X₀ n < 1 := by
  unfold τ
  norm_num at hn1 ⊢
  linarith

/-- Exercise 610, gap 5; bind the previously free `n`. -/
theorem gap5 (x X₀ : ℝ) (n : ℕ) :
    x = X₀ + τ x X₀ n + n := by
  unfold τ
  push_cast
  ring

/-- Exercise 610, gap 6; replace the ellipsis by a finite telescoping sum. -/
theorem gap6 (f g : ℝ → ℝ) (l x X₀ t : ℝ) (n : ℕ)
    (hx : x = X₀ + t + n) (hden : g x ≠ g (X₀ + t))
    (hstepPos : ∀ k ∈ Finset.Icc 1 n,
      g (X₀ + t + k - 1) < g (X₀ + t + k)) :
    (f x - f (X₀ + t)) / (g x - g (X₀ + t)) - l =
      (Finset.Icc 1 n).sum (fun k =>
        weight g X₀ t x k * (unitRatio f g (X₀ + t + k - 1) - l)) := by
  have hstep : ∀ k ∈ Finset.Icc 1 n,
      g (X₀ + t + k) - g (X₀ + t + k - 1) ≠ 0 := by
    intro k hk
    exact sub_ne_zero.mpr (hstepPos k hk).ne'
  have hf := sum_Icc_one_shift_sub f (X₀ + t) n
  have hg := sum_Icc_one_shift_sub g (X₀ + t) n
  have hterm : ∀ k ∈ Finset.Icc 1 n,
      weight g X₀ t x k * (unitRatio f g (X₀ + t + k - 1) - l) =
        (f (X₀ + t + k) - f (X₀ + t + k - 1)) /
            (g x - g (X₀ + t)) -
          l * (g (X₀ + t + k) - g (X₀ + t + k - 1)) /
            (g x - g (X₀ + t)) := by
    intro k hk
    have hk0 := hstep k hk
    have harg : X₀ + t + (k : ℝ) - 1 + 1 = X₀ + t + k := by ring
    rw [show unitRatio f g (X₀ + t + k - 1) =
        (f (X₀ + t + k) - f (X₀ + t + k - 1)) /
          (g (X₀ + t + k) - g (X₀ + t + k - 1)) by
      unfold unitRatio
      rw [harg]]
    unfold weight
    field_simp [hk0, hden]
  rw [hx] at hden
  have hd : g (X₀ + t + n) - g (X₀ + t) ≠ 0 := sub_ne_zero.mpr hden
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
    ← Finset.mul_sum, hf, hg, hx]
  field_simp [hd]

/-- Exercise 610, gap 7; bind the integer range and tail assumption. -/
theorem gap7 (f g : ℝ → ℝ) (l ε X₀ t : ℝ) (n k : ℕ)
    (hk : k ∈ Finset.Icc 1 n)
    (htail : ∀ y ≥ X₀, |unitRatio f g y - l| < ε / 2)
    (ht : 0 ≤ t) :
    |unitRatio f g (X₀ + t + k - 1) - l| < ε / 2 := by
  apply htail
  have hk1nat : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1nat
  linarith

/-- Exercise 610, gap 8. -/
theorem gap8 (g : ℝ → ℝ) (x X₀ t : ℝ) (n : ℕ)
    (hx : x = X₀ + t + n) : g x = g (X₀ + t + n) := by
  simpa [hx]

/-- Exercise 610, gap 9. -/
theorem gap9 (g : ℝ → ℝ) (X₀ t : ℝ) (n : ℕ) (hn : 0 < n)
    (hinc : UnitIncreasing g) :
    g (X₀ + t + n - 1) < g (X₀ + t + n) := by
  have h := hinc (X₀ + t + (n : ℝ) - 1)
  convert h using 1 <;> ring

/-- Exercise 610, gap 10; replace the omitted chain by its indexed form. -/
theorem gap10 (g : ℝ → ℝ) (X₀ t : ℝ) (n : ℕ)
    (hinc : UnitIncreasing g) :
    ∀ k ∈ Finset.Icc 1 n,
      g (X₀ + t + k - 1) < g (X₀ + t + k) := by
  intro k hk
  have h := hinc (X₀ + t + (k : ℝ) - 1)
  convert h using 1 <;> ring

/-- Exercise 610, gap 11; state the endpoint consequence of the chain. -/
theorem gap11 (g : ℝ → ℝ) (X₀ t : ℝ) (n : ℕ) (hn : 0 < n)
    (hinc : UnitIncreasing g) :
    g (X₀ + t) < g (X₀ + t + n) := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        convert hinc (X₀ + t) using 1 <;> norm_num
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hprev := ih hnpos
        have hstep :
            g (X₀ + t + (n : ℝ)) < g (X₀ + t + (Nat.succ n : ℕ)) := by
          convert hinc (X₀ + t + (n : ℝ)) using 1 <;>
            norm_num [Nat.cast_succ] <;> ring
        exact lt_trans hprev hstep

private theorem endpoint_lt_of_steps (g : ℝ → ℝ) (a : ℝ) (n : ℕ)
    (hn : 0 < n)
    (hstep : ∀ k ∈ Finset.Icc 1 n,
      g (a + k - 1) < g (a + k)) :
    g a < g (a + n) := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        simpa using hstep 1 (by simp)
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hprev := ih hnpos (fun k hk => hstep k (by
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,
            le_trans (Finset.mem_Icc.mp hk).2 (Nat.le_succ n)⟩))
        have hlast := hstep (Nat.succ n) (by simp)
        have hlast' : g (a + (n : ℝ)) < g (a + (Nat.succ n : ℕ)) := by
          convert hlast using 1 <;> norm_num [Nat.cast_succ] <;> ring
        exact hprev.trans hlast'

/-- Exercise 610, gap 12. -/
theorem gap12 (g : ℝ → ℝ) (x X₀ t : ℝ) (n : ℕ) (hn : 0 < n)
    (hx : x = X₀ + t + n) (hinc : UnitIncreasing g) :
    g (X₀ + t) < g x := by
  rw [hx]
  exact gap11 g X₀ t n hn hinc

/-- Exercise 610, gap 13; bind `k` to the telescoping range. -/
theorem gap13 (g : ℝ → ℝ) (x X₀ t : ℝ) (n k : ℕ)
    (hk : k ∈ Finset.Icc 1 n) (hx : x = X₀ + t + n)
    (hinc : UnitIncreasing g) :
    0 < weight g X₀ t x k := by
  have hki := Finset.mem_Icc.mp hk
  have hn : 0 < n :=
    lt_of_lt_of_le Nat.zero_lt_one (le_trans hki.1 hki.2)
  unfold weight
  apply div_pos
  · have hstep := gap10 g X₀ t n hinc k hk
    linarith
  · have hend := gap12 g x X₀ t n hn hx hinc
    linarith

/-- Exercise 610, gap 14; use positivity and unit total weight. -/
theorem gap14 (f g : ℝ → ℝ) (l ε x X₀ t : ℝ) (n : ℕ)
    (hterms : ∀ k ∈ Finset.Icc 1 n,
      0 ≤ weight g X₀ t x k ∧
      |unitRatio f g (X₀ + t + k - 1) - l| < ε / 2)
    (hsum : (Finset.Icc 1 n).sum (weight g X₀ t x) = 1) :
    |(Finset.Icc 1 n).sum (fun k =>
      weight g X₀ t x k * (unitRatio f g (X₀ + t + k - 1) - l))| < ε / 2 := by
  let s := Finset.Icc 1 n
  have hpos : ∃ k ∈ s, 0 < weight g X₀ t x k := by
    by_contra h
    push_neg at h
    have hz : ∀ k ∈ s, weight g X₀ t x k = 0 := by
      intro k hk
      exact le_antisymm (h k hk) (hterms k hk).1
    have hzsum : s.sum (weight g X₀ t x) = 0 := Finset.sum_eq_zero hz
    change s.sum (weight g X₀ t x) = 1 at hsum
    linarith
  calc
    |s.sum (fun k => weight g X₀ t x k *
        (unitRatio f g (X₀ + t + k - 1) - l))| ≤
        s.sum (fun k => |weight g X₀ t x k *
          (unitRatio f g (X₀ + t + k - 1) - l)|) :=
      Finset.abs_sum_le_sum_abs _ _
    _ = s.sum (fun k => weight g X₀ t x k *
          |unitRatio f g (X₀ + t + k - 1) - l|) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [abs_mul, abs_of_nonneg (hterms k hk).1]
    _ < s.sum (fun k => weight g X₀ t x k * (ε / 2)) := by
      apply Finset.sum_lt_sum
      · intro k hk
        exact mul_le_mul_of_nonneg_left
          (le_of_lt (hterms k hk).2) (hterms k hk).1
      · rcases hpos with ⟨k, hk, hw⟩
        refine ⟨k, hk, ?_⟩
        exact mul_lt_mul_of_pos_left (hterms k hk).2 hw
    _ = ε / 2 := by
      rw [← Finset.sum_mul, hsum]
      ring

/-- Exercise 610, gap 15; state the quotient decomposition with nonzero denominators. -/
theorem gap15 (f g : ℝ → ℝ) (l x y : ℝ)
    (hg : g x ≠ 0) (hxy : g x ≠ g y) :
    quotient f g x - l =
      (1 - g y / g x) * ((f x - f y) / (g x - g y) - l) +
        (f y - l * g y) / g x := by
  unfold quotient
  have hd : g x - g y ≠ 0 := sub_ne_zero.mpr hxy
  field_simp [hg, hd]
  ring

/-- Exercise 610, gap 16; derive the two small fixed-numerator ratios from `g→+∞`. -/
theorem gap16 (f g : ℝ → ℝ) (l y ε : ℝ) (hε : 0 < ε)
    (hg : HasPosInfiniteLimit g) :
    ∃ X₁ : ℝ, ∀ x > X₁,
      |g y / g x| < 1 / 2 ∧ |(f y - l * g y) / g x| < ε / 4 := by
  change Filter.Tendsto g Filter.atTop Filter.atTop at hg
  let B := f y - l * g y
  let M := max (2 * |g y| + 1) (4 * |B| / ε + 1)
  have hev : ∀ᶠ x in Filter.atTop, M ≤ g x :=
    (Filter.tendsto_atTop.1 hg) M
  rcases Filter.eventually_atTop.1 hev with ⟨X₁, hX₁⟩
  refine ⟨X₁, fun x hx => ?_⟩
  have hM : M ≤ g x := hX₁ x (le_of_lt hx)
  have hga : 2 * |g y| < g x := by
    have hm : 2 * |g y| + 1 ≤ M := le_max_left _ _
    linarith
  have hgx : 0 < g x := by
    have ha := abs_nonneg (g y)
    linarith
  have hgbound : 4 * |B| / ε < g x := by
    have hm : 4 * |B| / ε + 1 ≤ M := le_max_right _ _
    linarith
  have hgbound' : 4 * |B| < g x * ε :=
    (div_lt_iff₀ hε).mp hgbound
  constructor
  · rw [abs_div, abs_of_pos hgx]
    apply (div_lt_iff₀ hgx).2
    linarith
  · change |B / g x| < ε / 4
    rw [abs_div, abs_of_pos hgx]
    apply (div_lt_iff₀ hgx).2
    nlinarith

/-- Exercise 610, gap 17. -/
theorem gap17 (z ε : ℝ) (hε : 0 < ε)
    (hz : |z| < (3 / 2 : ℝ) * (ε / 2) + ε / 4) :
    |z| < (3 / 2 : ℝ) * (ε / 2) + ε / 4 := by
  exact hz

/-- Exercise 610, gap 18. -/
theorem gap18 (ε : ℝ) :
    (3 / 2 : ℝ) * (ε / 2) + ε / 4 = ε := by
  ring

/-- Exercise 610, gap 19. -/
theorem gap19 (z ε : ℝ) (hε : 0 < ε)
    (hz : |z| < (3 / 2 : ℝ) * (ε / 2) + ε / 4) :
    |z| < ε := by
  rw [gap18 ε] at hz
  exact hz

private theorem secant_close_of_tail (f g : ℝ → ℝ) (l η X₀ x : ℝ)
    (hη : 0 < η)
    (hinc : ∀ y ≥ X₀, g y < g (y + 1))
    (htail : ∀ y ≥ X₀, |unitRatio f g y - l| < η)
    (hx : X₀ + 1 < x) :
    ∃ y : ℝ, X₀ ≤ y ∧ y < X₀ + 1 ∧ g y < g x ∧
      |(f x - f y) / (g x - g y) - l| < η := by
  rcases gap2 x X₀ hx with ⟨n, hnpos, hnle, hnlt⟩
  let t := τ x X₀ n
  have ht0 : 0 ≤ t := by
    simpa [t] using gap3 x X₀ n hnle
  have ht1 : t < 1 := by
    simpa [t] using gap4 x X₀ n hnlt
  have hxrep : x = X₀ + t + n := by
    simpa [t] using gap5 x X₀ n
  have hsteps : ∀ k ∈ Finset.Icc 1 n,
      g (X₀ + t + k - 1) < g (X₀ + t + k) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hy : X₀ ≤ X₀ + t + (k : ℝ) - 1 := by linarith
    convert hinc _ hy using 1 <;> ring
  have hend0 : g (X₀ + t) < g (X₀ + t + n) :=
    endpoint_lt_of_steps g (X₀ + t) n (by omega) (by
      intro k hk
      simpa only [add_assoc] using hsteps k hk)
  have hend : g (X₀ + t) < g x := by simpa [hxrep] using hend0
  have hden : g x ≠ g (X₀ + t) := hend.ne'
  have hweights : ∀ k ∈ Finset.Icc 1 n, 0 < weight g X₀ t x k := by
    intro k hk
    unfold weight
    exact div_pos (sub_pos.mpr (hsteps k hk)) (sub_pos.mpr hend)
  have hsum : (Finset.Icc 1 n).sum (weight g X₀ t x) = 1 := by
    unfold weight
    rw [← Finset.sum_div, sum_Icc_one_shift_sub g (X₀ + t) n]
    rw [← hxrep]
    exact div_self (sub_ne_zero.mpr hden)
  have hterms : ∀ k ∈ Finset.Icc 1 n,
      0 ≤ weight g X₀ t x k ∧
      |unitRatio f g (X₀ + t + k - 1) - l| < η := by
    intro k hk
    refine ⟨le_of_lt (hweights k hk), ?_⟩
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hk).1
    apply htail
    linarith
  have hsumClose := gap14 f g l (2 * η) x X₀ t n (by
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hterms) hsum
  have htel := gap6 f g l x X₀ t n hxrep hden hsteps
  refine ⟨X₀ + t, by linarith, by linarith, hend, ?_⟩
  rw [htel]
  simpa using hsumClose

private theorem secant_gt_of_tail (f g : ℝ → ℝ) (R X₀ x : ℝ)
    (hinc : ∀ y ≥ X₀, g y < g (y + 1))
    (htail : ∀ y ≥ X₀, R < unitRatio f g y)
    (hx : X₀ + 1 < x) :
    ∃ y : ℝ, X₀ ≤ y ∧ y < X₀ + 1 ∧ g y < g x ∧
      R < (f x - f y) / (g x - g y) := by
  rcases gap2 x X₀ hx with ⟨n, hnpos, hnle, hnlt⟩
  let t := τ x X₀ n
  have ht0 : 0 ≤ t := by
    simpa [t] using gap3 x X₀ n hnle
  have ht1 : t < 1 := by
    simpa [t] using gap4 x X₀ n hnlt
  have hxrep : x = X₀ + t + n := by
    simpa [t] using gap5 x X₀ n
  have hsteps : ∀ k ∈ Finset.Icc 1 n,
      g (X₀ + t + k - 1) < g (X₀ + t + k) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hy : X₀ ≤ X₀ + t + (k : ℝ) - 1 := by linarith
    convert hinc _ hy using 1 <;> ring
  have hend0 : g (X₀ + t) < g (X₀ + t + n) :=
    endpoint_lt_of_steps g (X₀ + t) n (by omega) (by
      intro k hk
      simpa only [add_assoc] using hsteps k hk)
  have hend : g (X₀ + t) < g x := by simpa [hxrep] using hend0
  have hden : g x ≠ g (X₀ + t) := hend.ne'
  have hweights : ∀ k ∈ Finset.Icc 1 n, 0 < weight g X₀ t x k := by
    intro k hk
    unfold weight
    exact div_pos (sub_pos.mpr (hsteps k hk)) (sub_pos.mpr hend)
  have hsum : (Finset.Icc 1 n).sum (weight g X₀ t x) = 1 := by
    unfold weight
    rw [← Finset.sum_div, sum_Icc_one_shift_sub g (X₀ + t) n]
    rw [← hxrep]
    exact div_self (sub_ne_zero.mpr hden)
  have hsumgt : R < (Finset.Icc 1 n).sum (fun k =>
      weight g X₀ t x k * unitRatio f g (X₀ + t + k - 1)) := by
    calc
      R = (Finset.Icc 1 n).sum (fun k => weight g X₀ t x k * R) := by
        rw [← Finset.sum_mul, hsum]
        ring
      _ < (Finset.Icc 1 n).sum (fun k =>
          weight g X₀ t x k * unitRatio f g (X₀ + t + k - 1)) := by
        apply Finset.sum_lt_sum
        · intro k hk
          exact le_of_lt (mul_lt_mul_of_pos_left (htail _ (by
            have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
              exact_mod_cast (Finset.mem_Icc.mp hk).1
            linarith)) (hweights k hk))
        · refine ⟨1, Finset.mem_Icc.mpr ⟨by simp, hnpos⟩, ?_⟩
          exact mul_lt_mul_of_pos_left (htail _ (by norm_num; linarith))
            (hweights 1 (Finset.mem_Icc.mpr ⟨by simp, hnpos⟩))
  have htel := gap6 f g 0 x X₀ t n hxrep hden hsteps
  refine ⟨X₀ + t, by linarith, by linarith, hend, ?_⟩
  rw [show (f x - f (X₀ + t)) / (g x - g (X₀ + t)) =
      (f x - f (X₀ + t)) / (g x - g (X₀ + t)) - 0 by ring,
    htel]
  simpa using hsumgt

private theorem finite_stolz_eventually (f g : ℝ → ℝ) (l : ℝ)
    (hf : ∀ a b : ℝ, a < b → ∃ M, ∀ x, a < x → x < b → |f x| ≤ M)
    (hgloc : ∀ a b : ℝ, a < b → ∃ M, ∀ x, a < x → x < b → |g x| ≤ M)
    (hincEv : ∃ A : ℝ, ∀ y ≥ A, g y < g (y + 1))
    (hg : HasPosInfiniteLimit g)
    (hdiff : HasFiniteLimit (unitRatio f g) l) :
    HasFiniteLimit (quotient f g) l := by
  rcases hincEv with ⟨A, hinc⟩
  change Filter.Tendsto (quotient f g) Filter.atTop (nhds l)
  rw [Metric.tendsto_atTop]
  intro ε hε
  rcases gap1 f g l hdiff ε hε with ⟨Xd, htail0⟩
  let X₀ := max Xd A
  have htail : ∀ x ≥ X₀, |unitRatio f g x - l| < ε / 2 := by
    intro x hx
    exact htail0 x (le_trans (le_max_left Xd A) hx)
  have hincTail : ∀ y ≥ X₀, g y < g (y + 1) := by
    intro y hy
    exact hinc y (le_trans (le_max_right Xd A) hy)
  rcases hf (X₀ - 1) (X₀ + 2) (by linarith) with ⟨Mf, hMf⟩
  rcases hgloc (X₀ - 1) (X₀ + 2) (by linarith) with ⟨Mg, hMg⟩
  have hMf0 : |f X₀| ≤ Mf := hMf X₀ (by linarith) (by linarith)
  have hMg0 : |g X₀| ≤ Mg := hMg X₀ (by linarith) (by linarith)
  have hMf_nonneg : 0 ≤ Mf := le_trans (abs_nonneg _) hMf0
  have hMg_nonneg : 0 ≤ Mg := le_trans (abs_nonneg _) hMg0
  let B := Mf + |l| * Mg
  let C := max (2 * Mg + 1) (4 * B / ε + 1)
  have hg' : Filter.Tendsto g Filter.atTop Filter.atTop := hg
  have hev : ∀ᶠ x in Filter.atTop, C ≤ g x :=
    (Filter.tendsto_atTop.1 hg') C
  rcases Filter.eventually_atTop.1 hev with ⟨X₁, hX₁⟩
  refine ⟨max (X₀ + 2) X₁, ?_⟩
  intro x hx
  have hx0 : X₀ + 1 < x := by
    have := le_trans (le_max_left (X₀ + 2) X₁) hx
    linarith
  have hx1 : X₁ ≤ x := le_trans (le_max_right (X₀ + 2) X₁) hx
  have hC : C ≤ g x := hX₁ x hx1
  rcases secant_close_of_tail f g l (ε / 2) X₀ x (by linarith)
      hincTail htail hx0 with
    ⟨y, hy0, hy1, hgyx, hsec⟩
  have hfy : |f y| ≤ Mf := hMf y (by linarith) (by linarith)
  have hgy : |g y| ≤ Mg := hMg y (by linarith) (by linarith)
  have hga : 2 * |g y| < g x := by
    have hleft : 2 * Mg + 1 ≤ C := le_max_left _ _
    nlinarith
  have hgx : 0 < g x := by nlinarith [abs_nonneg (g y)]
  have hratio : |g y / g x| < 1 / 2 := by
    rw [abs_div, abs_of_pos hgx]
    apply (div_lt_iff₀ hgx).2
    nlinarith
  have hnum : |f y - l * g y| ≤ B := by
    calc
      |f y - l * g y| ≤ |f y| + |l * g y| := abs_sub _ _
      _ = |f y| + |l| * |g y| := by rw [abs_mul]
      _ ≤ Mf + |l| * Mg := by
        exact add_le_add hfy (mul_le_mul_of_nonneg_left hgy (abs_nonneg l))
      _ = B := rfl
  have hgbound : 4 * B / ε < g x := by
    have hright : 4 * B / ε + 1 ≤ C := le_max_right _ _
    linarith
  have hgbound' : 4 * B < g x * ε := (div_lt_iff₀ hε).mp hgbound
  have hres : |(f y - l * g y) / g x| < ε / 4 := by
    rw [abs_div, abs_of_pos hgx]
    apply (div_lt_iff₀ hgx).2
    nlinarith
  have hfactor : |1 - g y / g x| < (3 / 2 : ℝ) := by
    have htri : |1 - g y / g x| ≤ |(1 : ℝ)| + |g y / g x| := abs_sub _ _
    norm_num at htri ⊢
    linarith
  have hmul :
      |(1 - g y / g x) * ((f x - f y) / (g x - g y) - l)| <
        (3 / 2 : ℝ) * (ε / 2) := by
    rw [abs_mul]
    nlinarith [abs_nonneg (1 - g y / g x),
      abs_nonneg ((f x - f y) / (g x - g y) - l)]
  have hdecomp := gap15 f g l x y (ne_of_gt hgx) hgyx.ne'
  rw [Real.dist_eq, hdecomp]
  have htri := abs_add_le
    ((1 - g y / g x) * ((f x - f y) / (g x - g y) - l))
    ((f y - l * g y) / g x)
  calc
    |(1 - g y / g x) * ((f x - f y) / (g x - g y) - l) +
        (f y - l * g y) / g x| ≤
        |(1 - g y / g x) * ((f x - f y) / (g x - g y) - l)| +
          |(f y - l * g y) / g x| := htri
    _ < (3 / 2 : ℝ) * (ε / 2) + ε / 4 := add_lt_add hmul hres
    _ = ε := by ring

/-- Exercise 610, gap 20; finite-valued Stolz-type conclusion with all functions fixed. -/
theorem gap20 (f g : ℝ → ℝ) (l : ℝ)
    (hf : ∀ a b : ℝ, a < b → ∃ M, ∀ x, a < x → x < b → |f x| ≤ M)
    (hgloc : ∀ a b : ℝ, a < b → ∃ M, ∀ x, a < x → x < b → |g x| ≤ M)
    (hinc : UnitIncreasing g) (hg : HasPosInfiniteLimit g)
    (hdiff : HasFiniteLimit (unitRatio f g) l) :
    HasFiniteLimit (quotient f g) l := by
  exact finite_stolz_eventually f g l hf hgloc ⟨0, fun y _ => hinc y⟩ hg hdiff

/-- Exercise 610, gap 21; bind the positive-infinite difference-ratio hypothesis. -/
theorem gap21 (f g : ℝ → ℝ)
    (hdiff : HasPosInfiniteLimit (unitRatio f g)) :
    ∀ G > 0, ∃ X₀ : ℝ, ∀ x ≥ X₀, 4 * G < unitRatio f g x := by
  change Filter.Tendsto (unitRatio f g) Filter.atTop Filter.atTop at hdiff
  intro G hG
  have hev : ∀ᶠ x in Filter.atTop, 4 * G + 1 ≤ unitRatio f g x :=
    (Filter.tendsto_atTop.1 hdiff) (4 * G + 1)
  rcases Filter.eventually_atTop.1 hev with ⟨X₀, hX₀⟩
  refine ⟨X₀, fun x hx => ?_⟩
  have := hX₀ x hx
  linarith

/-- Exercise 610, gap 22; formulate the telescoped lower bound. -/
theorem gap22 (f g : ℝ → ℝ) (G x y : ℝ)
    (h : 4 * G < (f x - f y) / (g x - g y)) :
    4 * G < (f x - f y) / (g x - g y) := by
  exact h

/-- Exercise 610, gap 23; infinite-case quotient decomposition. -/
theorem gap23 (f g : ℝ → ℝ) (x y : ℝ)
    (hg : g x ≠ 0) (hxy : g x ≠ g y) :
    quotient f g x =
      (1 - g y / g x) * ((f x - f y) / (g x - g y)) + f y / g x := by
  unfold quotient
  have hd : g x - g y ≠ 0 := sub_ne_zero.mpr hxy
  field_simp [hg, hd]
  ring

/-- Exercise 610, gap 24. -/
theorem gap24 (f g : ℝ → ℝ) (y G : ℝ) (hG : 0 < G)
    (hg : HasPosInfiniteLimit g) :
    ∃ X₁ : ℝ, ∀ x > X₁, |g y / g x| < 1 / 2 ∧ |f y / g x| < G := by
  rcases gap16 f g 0 y (4 * G) (by linarith) hg with ⟨X₁, hX₁⟩
  refine ⟨X₁, fun x hx => ?_⟩
  have h := hX₁ x hx
  constructor
  · exact h.1
  · convert h.2 using 1 <;> ring

/-- Exercise 610, gap 25. -/
theorem gap25 (z G : ℝ) (hG : 0 < G)
    (hz : (1 / 2 : ℝ) * (4 * G) - G < z) :
    (1 / 2 : ℝ) * (4 * G) - G < z := by
  exact hz

/-- Exercise 610, gap 26. -/
theorem gap26 (G : ℝ) : (1 / 2 : ℝ) * (4 * G) - G = G := by
  ring

/-- Exercise 610, gap 27. -/
theorem gap27 (z G : ℝ) (hG : 0 < G)
    (hz : (1 / 2 : ℝ) * (4 * G) - G < z) : G < z := by
  rw [gap26 G] at hz
  exact hz

/-- Exercise 610, gap 28. -/
theorem gap28 (f g : ℝ → ℝ)
    (hf : ∀ a b : ℝ, a < b → ∃ M, ∀ x, a < x → x < b → |f x| ≤ M)
    (hgloc : ∀ a b : ℝ, a < b → ∃ M, ∀ x, a < x → x < b → |g x| ≤ M)
    (hinc : UnitIncreasing g) (hg : HasPosInfiniteLimit g)
    (hdiff : HasPosInfiniteLimit (unitRatio f g)) :
    HasPosInfiniteLimit (quotient f g) := by
  change Filter.Tendsto (quotient f g) Filter.atTop Filter.atTop
  rw [Filter.tendsto_atTop]
  intro A
  let G := max A 1
  have hG : 0 < G := lt_of_lt_of_le zero_lt_one (le_max_right A 1)
  have hAG : A ≤ G := le_max_left A 1
  rcases gap21 f g hdiff G hG with ⟨X₀, htail⟩
  rcases hf (X₀ - 1) (X₀ + 2) (by linarith) with ⟨Mf, hMf⟩
  rcases hgloc (X₀ - 1) (X₀ + 2) (by linarith) with ⟨Mg, hMg⟩
  have hMf0 : |f X₀| ≤ Mf := hMf X₀ (by linarith) (by linarith)
  have hMg0 : |g X₀| ≤ Mg := hMg X₀ (by linarith) (by linarith)
  have hMf_nonneg : 0 ≤ Mf := le_trans (abs_nonneg _) hMf0
  have hMg_nonneg : 0 ≤ Mg := le_trans (abs_nonneg _) hMg0
  let C := max (2 * Mg + 1) (Mf / G + 1)
  have hg' : Filter.Tendsto g Filter.atTop Filter.atTop := hg
  have hev : ∀ᶠ x in Filter.atTop, C ≤ g x :=
    (Filter.tendsto_atTop.1 hg') C
  rcases Filter.eventually_atTop.1 hev with ⟨X₁, hX₁⟩
  filter_upwards [Filter.eventually_ge_atTop (max (X₀ + 2) X₁)] with x hx
  have hx0 : X₀ + 1 < x := by
    have := le_trans (le_max_left (X₀ + 2) X₁) hx
    linarith
  have hx1 : X₁ ≤ x := le_trans (le_max_right (X₀ + 2) X₁) hx
  have hC : C ≤ g x := hX₁ x hx1
  rcases secant_gt_of_tail f g (4 * G) X₀ x
      (fun y _ => hinc y) htail hx0 with
    ⟨y, hy0, hy1, hgyx, hsec⟩
  have hfy : |f y| ≤ Mf := hMf y (by linarith) (by linarith)
  have hgy : |g y| ≤ Mg := hMg y (by linarith) (by linarith)
  have hga : 2 * |g y| < g x := by
    have hleft : 2 * Mg + 1 ≤ C := le_max_left _ _
    nlinarith
  have hgx : 0 < g x := by nlinarith [abs_nonneg (g y)]
  have hratio : |g y / g x| < 1 / 2 := by
    rw [abs_div, abs_of_pos hgx]
    apply (div_lt_iff₀ hgx).2
    nlinarith
  have hfbound : Mf / G < g x := by
    have hright : Mf / G + 1 ≤ C := le_max_right _ _
    linarith
  have hfbound' : Mf < g x * G := (div_lt_iff₀ hG).mp hfbound
  have hres : |f y / g x| < G := by
    rw [abs_div, abs_of_pos hgx]
    apply (div_lt_iff₀ hgx).2
    nlinarith
  have hfactor : (1 / 2 : ℝ) < 1 - g y / g x := by
    have := (abs_lt.mp hratio).2
    linarith
  have hprod : 2 * G <
      (1 - g y / g x) * ((f x - f y) / (g x - g y)) := by
    have hsecpos : 0 < (f x - f y) / (g x - g y) := by linarith
    have := mul_lt_mul hfactor (le_of_lt hsec) (by positivity : (0 : ℝ) < 4 * G)
      (le_of_lt (by linarith : 0 < 1 - g y / g x))
    nlinarith
  have hdecomp := gap23 f g x y (ne_of_gt hgx) hgyx.ne'
  rw [hdecomp]
  have hresLower := (abs_lt.mp hres).1
  linarith

/-- Exercise 610, gap 29; include the negative-infinite analogue explicitly. -/
theorem gap29 (f g : ℝ → ℝ)
    (hf : ∀ a b : ℝ, a < b → ∃ M, ∀ x, a < x → x < b → |f x| ≤ M)
    (hgloc : ∀ a b : ℝ, a < b → ∃ M, ∀ x, a < x → x < b → |g x| ≤ M)
    (hinc : UnitIncreasing g) (hg : HasPosInfiniteLimit g)
    (hdiff : HasNegInfiniteLimit (unitRatio f g)) :
    HasNegInfiniteLimit (quotient f g) := by
  have hfneg : ∀ a b : ℝ, a < b → ∃ M, ∀ x,
      a < x → x < b → |(fun z => -f z) x| ≤ M := by
    intro a b hab
    rcases hf a b hab with ⟨M, hM⟩
    refine ⟨M, fun x hax hxb => ?_⟩
    simpa using hM x hax hxb
  have hdiffneg : HasPosInfiniteLimit (unitRatio (fun x => -f x) g) := by
    change Filter.Tendsto (unitRatio (fun x => -f x) g)
      Filter.atTop Filter.atTop
    rw [Filter.tendsto_atTop]
    intro A
    have hev : ∀ᶠ x in Filter.atTop, unitRatio f g x ≤ -A :=
      (Filter.tendsto_atBot.1 hdiff) (-A)
    filter_upwards [hev] with x hx
    have heq : unitRatio (fun z => -f z) g x = -unitRatio f g x := by
      unfold unitRatio
      ring
    rw [heq]
    linarith
  have hqneg := gap28 (fun x => -f x) g hfneg hgloc hinc hg hdiffneg
  change Filter.Tendsto (quotient f g) Filter.atTop Filter.atBot
  rw [Filter.tendsto_atBot]
  intro A
  have hev : ∀ᶠ x in Filter.atTop, -A ≤ quotient (fun x => -f x) g x :=
    (Filter.tendsto_atTop.1 hqneg) (-A)
  filter_upwards [hev] with x hx
  have heq : quotient (fun z => -f z) g x = -quotient f g x := by
    unfold quotient
    ring
  rw [heq] at hx
  linarith

/-- Exercise 610, gap 30; package the corrected finite and infinite conclusions. -/
theorem gap30 (f g : ℝ → ℝ) (hinc : UnitIncreasing g)
    (hf : ∀ a b : ℝ, a < b → ∃ M, ∀ x, a < x → x < b → |f x| ≤ M)
    (hgloc : ∀ a b : ℝ, a < b → ∃ M, ∀ x, a < x → x < b → |g x| ≤ M)
    (hg : HasPosInfiniteLimit g) :
    (∀ l, HasFiniteLimit (unitRatio f g) l → HasFiniteLimit (quotient f g) l) ∧
    (HasPosInfiniteLimit (unitRatio f g) → HasPosInfiniteLimit (quotient f g)) ∧
    (HasNegInfiniteLimit (unitRatio f g) → HasNegInfiniteLimit (quotient f g)) := by
  refine ⟨fun l h => gap20 f g l hf hgloc hinc hg h, ?_, ?_⟩
  · exact fun h => gap28 f g hf hgloc hinc hg h
  · exact fun h => gap29 f g hf hgloc hinc hg h

/-- Exercise 610, gap 31; choose `g(x)=x^(n+1)`. -/
theorem gap31 (f : ℝ → ℝ) (n : ℕ) (L : ℝ) :
    HasFiniteLimit (unitRatio f (polyG n)) L ↔
      HasFiniteLimit
        (fun x => (f (x + 1) - f x) / ((x + 1) ^ (n + 1) - x ^ (n + 1))) L := by
  rfl

/-- Exercise 610, gap 32; replace the binomial ellipsis by `polyNorm`. -/
theorem gap32 (f : ℝ → ℝ) (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    (f (x + 1) - f x) / ((x + 1) ^ (n + 1) - x ^ (n + 1)) =
      appNormalized f n x := by
  let D := (x + 1) ^ (n + 1) - x ^ (n + 1)
  by_cases hD : D = 0
  · simp [appNormalized, polyNorm, D, hD]
  · have hxn : x ^ n ≠ 0 := pow_ne_zero n hx
    unfold appNormalized polyNorm
    change (f (x + 1) - f x) / D =
      ((f (x + 1) - f x) / x ^ n) * (1 / (D / x ^ n))
    field_simp [hD, hxn]

/-- Exercise 610, gap 33; retain the missing premise naming `l`. -/
theorem gap33 (f : ℝ → ℝ) (n : ℕ) (l : ℝ)
    (hdiff : HasFiniteLimit (fun x => (f (x + 1) - f x) / x ^ n) l) :
    HasFiniteLimit (appNormalized f n) (l / (n + 1)) := by
  change Filter.Tendsto
    (fun x => (f (x + 1) - f x) / x ^ n)
    Filter.atTop (nhds l) at hdiff
  change Filter.Tendsto
    (fun x => ((f (x + 1) - f x) / x ^ n) * (1 / polyNorm n x))
    Filter.atTop (nhds (l / (n + 1)))
  have hnorm := polyNorm_hasFiniteLimit n
  change Filter.Tendsto (polyNorm n) Filter.atTop
    (nhds (((n + 1 : ℕ) : ℝ))) at hnorm
  have hnonzero : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hinv := hnorm.inv₀ hnonzero
  have hprod := hdiff.mul hinv
  simpa only [div_eq_mul_inv, one_mul, Nat.cast_add, Nat.cast_one] using hprod

/-- Exercise 610, gap 34. -/
theorem gap34 (f : ℝ → ℝ) (n : ℕ) (l : ℝ)
    (hdiff : HasFiniteLimit (fun x => (f (x + 1) - f x) / x ^ n) l) :
    HasFiniteLimit (unitRatio f (polyG n)) (l / (n + 1)) := by
  apply (gap31 f n (l / (n + 1))).2
  have happ := gap33 f n l hdiff
  refine happ.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  exact (gap32 f n x (ne_of_gt hx)).symm

/-- Exercise 610, gap 35. -/
theorem gap35 (f : ℝ → ℝ) (n : ℕ) :
    quotient f (polyG n) = fun x => f x / x ^ (n + 1) := by
  rfl

private theorem polyG_locallyBounded (n : ℕ) :
    ∀ a b : ℝ, a < b → ∃ M, ∀ x, a < x → x < b → |polyG n x| ≤ M := by
  intro a b hab
  refine ⟨(max |a| |b|) ^ (n + 1), ?_⟩
  intro x hax hxb
  have hxabs : |x| ≤ max |a| |b| := by
    apply abs_le.2
    constructor
    · have ha : |a| ≤ max |a| |b| := le_max_left _ _
      have hnega : -|a| ≤ a := neg_abs_le a
      linarith
    · have hb : |b| ≤ max |a| |b| := le_max_right _ _
      have hble : b ≤ |b| := le_abs_self b
      linarith
  simpa [polyG, abs_pow] using
    (pow_le_pow_left₀ (abs_nonneg x) hxabs (n + 1))

private theorem polyG_eventuallyUnitIncreasing (n : ℕ) :
    ∃ A : ℝ, ∀ x ≥ A, polyG n x < polyG n (x + 1) := by
  refine ⟨0, ?_⟩
  intro x hx
  unfold polyG
  exact pow_lt_pow_left₀ (by linarith) hx (by omega)

private theorem polyG_posInfinite (n : ℕ) : HasPosInfiniteLimit (polyG n) := by
  unfold HasPosInfiniteLimit polyG
  exact Filter.tendsto_pow_atTop (by omega)

/-- Exercise 610, gap 36; apply the finite Stolz conclusion. -/
theorem gap36 (f : ℝ → ℝ) (n : ℕ) (l : ℝ)
    (hlocal : ∀ a b : ℝ, a < b → ∃ M, ∀ x,
      a < x → x < b → |f x| ≤ M)
    (hdiff : HasFiniteLimit (unitRatio f (polyG n)) (l / (n + 1))) :
    HasFiniteLimit (quotient f (polyG n)) (l / (n + 1)) := by
  exact finite_stolz_eventually f (polyG n) (l / (n + 1))
    hlocal (polyG_locallyBounded n) (polyG_eventuallyUnitIncreasing n)
    (polyG_posInfinite n) hdiff

/-- Exercise 610, gap 37. -/
theorem gap37 (f : ℝ → ℝ) (n : ℕ) (l : ℝ)
    (hlocal : ∀ a b : ℝ, a < b → ∃ M, ∀ x,
      a < x → x < b → |f x| ≤ M)
    (hdiff : HasFiniteLimit (fun x => (f (x + 1) - f x) / x ^ n) l) :
    HasFiniteLimit (fun x => f x / x ^ (n + 1)) (l / (n + 1)) := by
  have hunit := gap34 f n l hdiff
  have hquot := gap36 f n l hlocal hunit
  simpa only [gap35 f n] using hquot

/-- Exercise 610, gap 38. -/
theorem gap38 (f : ℝ → ℝ) (n : ℕ) (l : ℝ)
    (hlocal : ∀ a b : ℝ, a < b → ∃ M, ∀ x,
      a < x → x < b → |f x| ≤ M)
    (hdiff : HasFiniteLimit (fun x => (f (x + 1) - f x) / x ^ n) l) :
    HasFiniteLimit (fun x => f x / x ^ (n + 1)) (l / (n + 1)) := by
  exact gap37 f n l hlocal hdiff

end

end ProofGap.Exercise610
