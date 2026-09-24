import ProofGapLean.Prelude.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise409

open scoped BigOperators

noncomputable section

def poly (n : ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  (Finset.range (n + 1)).sum (fun i => a i * x ^ (n - i))

def R (n m : ℕ) (a b : ℕ → ℝ) (x : ℝ) : ℝ :=
  poly n a x / poly m b x

def normalizedNumerator (n m : ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  poly n a x / x ^ m

def normalizedDenominator (m : ℕ) (b : ℕ → ℝ) (x : ℝ) : ℝ :=
  poly m b x / x ^ m

def HasLimitAtInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x, N < |x| → |f x - L| < ε

def AbsTendsToInfinity (f : ℝ → ℝ) : Prop :=
  ∀ E > 0, ∃ N > 0, ∀ x, N < |x| → E < |f x|

/-- Source: `proof_gap/exercise_409/1.txt`; express division by the common power without ellipses. -/
private theorem aux_hasLimit_congr {f g : ℝ → ℝ} {L : ℝ}
    (hg : HasLimitAtInfinity g L) (hfg : ∀ x, f x = g x) :
    HasLimitAtInfinity f L := by
  intro ε hε
  obtain ⟨N, hN, hbound⟩ := hg ε hε
  refine ⟨N, hN, ?_⟩
  intro x hx
  rw [hfg x]
  exact hbound x hx

private theorem aux_hasLimit_congr_nonzero {f g : ℝ → ℝ} {L : ℝ}
    (hg : HasLimitAtInfinity g L) (hfg : ∀ x, x ≠ 0 → f x = g x) :
    HasLimitAtInfinity f L := by
  intro ε hε
  obtain ⟨N, hN, hbound⟩ := hg ε hε
  refine ⟨N, hN, ?_⟩
  intro x hx
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    have : N < 0 := by simpa using hx
    linarith
  rw [hfg x hx0]
  exact hbound x hx

private theorem aux_absTends_congr_nonzero {f g : ℝ → ℝ}
    (hg : AbsTendsToInfinity g) (hfg : ∀ x, x ≠ 0 → f x = g x) :
    AbsTendsToInfinity f := by
  intro E hE
  obtain ⟨N, hN, hbound⟩ := hg E hE
  refine ⟨N, hN, ?_⟩
  intro x hx
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    have : N < 0 := by simpa using hx
    linarith
  rw [hfg x hx0]
  exact hbound x hx

private theorem aux_hasLimit_const (c : ℝ) :
    HasLimitAtInfinity (fun _ : ℝ => c) c := by
  intro ε hε
  refine ⟨1, zero_lt_one, ?_⟩
  intro x hx
  simpa using hε

private theorem aux_hasLimit_add {f g : ℝ → ℝ} {A B : ℝ}
    (hf : HasLimitAtInfinity f A) (hg : HasLimitAtInfinity g B) :
    HasLimitAtInfinity (fun x => f x + g x) (A + B) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨Nf, hNf, hfN⟩ := hf (ε / 2) hhalf
  obtain ⟨Ng, hNg, hgN⟩ := hg (ε / 2) hhalf
  refine ⟨max Nf Ng, lt_of_lt_of_le hNf (le_max_left _ _), ?_⟩
  intro x hx
  have hfx := hfN x (lt_of_le_of_lt (le_max_left _ _) hx)
  have hgx := hgN x (lt_of_le_of_lt (le_max_right _ _) hx)
  calc
    |f x + g x - (A + B)| = |(f x - A) + (g x - B)| := by congr 1 <;> ring
    _ ≤ |f x - A| + |g x - B| := abs_add_le _ _
    _ < ε := by linarith

private theorem aux_hasLimit_const_mul (c : ℝ) {f : ℝ → ℝ} {A : ℝ}
    (hf : HasLimitAtInfinity f A) :
    HasLimitAtInfinity (fun x => c * f x) (c * A) := by
  by_cases hc : c = 0
  · subst c
    simpa using aux_hasLimit_const 0
  have hcabs : 0 < |c| := abs_pos.mpr hc
  intro ε hε
  have hq : 0 < ε / |c| := div_pos hε hcabs
  obtain ⟨N, hN, hbound⟩ := hf (ε / |c|) hq
  refine ⟨N, hN, ?_⟩
  intro x hx
  have hh := hbound x hx
  change |c * f x - c * A| < ε
  calc
    |c * f x - c * A| = |c| * |f x - A| := by
      rw [← abs_mul]
      congr 1
      ring
    _ < |c| * (ε / |c|) := mul_lt_mul_of_pos_left hh hcabs
    _ = ε := by field_simp [ne_of_gt hcabs]

private theorem aux_hasLimit_shift {f : ℝ → ℝ} {A : ℝ}
    (hf : HasLimitAtInfinity f A) :
    HasLimitAtInfinity (fun x => f x - A) 0 := by
  intro ε hε
  obtain ⟨N, hN, hbound⟩ := hf ε hε
  refine ⟨N, hN, ?_⟩
  intro x hx
  simpa only [sub_zero] using hbound x hx

private theorem aux_hasLimit_mul_zero {f g : ℝ → ℝ}
    (hf : HasLimitAtInfinity f 0) (hg : HasLimitAtInfinity g 0) :
    HasLimitAtInfinity (fun x => f x * g x) 0 := by
  intro ε hε
  obtain ⟨Nf, hNf, hfN⟩ := hf ε hε
  obtain ⟨Ng, hNg, hgN⟩ := hg 1 zero_lt_one
  refine ⟨max Nf Ng, lt_of_lt_of_le hNf (le_max_left _ _), ?_⟩
  intro x hx
  have hfx := hfN x (lt_of_le_of_lt (le_max_left _ _) hx)
  have hgx := hgN x (lt_of_le_of_lt (le_max_right _ _) hx)
  have hfx' : |f x| < ε := by
    simpa only [sub_zero] using hfx
  have hgx' : |g x| < 1 := by
    simpa only [sub_zero] using hgx
  have hmul : |f x| * |g x| < ε * 1 :=
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (le_of_lt hgx') (abs_nonneg (f x)))
      (mul_lt_mul_of_pos_right hfx' zero_lt_one)
  simpa only [sub_zero, abs_mul, mul_one] using hmul

private theorem aux_hasLimit_mul {f g : ℝ → ℝ} {A B : ℝ}
    (hf : HasLimitAtInfinity f A) (hg : HasLimitAtInfinity g B) :
    HasLimitAtInfinity (fun x => f x * g x) (A * B) := by
  have hf0 := aux_hasLimit_shift hf
  have hg0 := aux_hasLimit_shift hg
  have hp :
      HasLimitAtInfinity (fun x => (f x - A) * (g x - B)) 0 :=
    aux_hasLimit_mul_zero hf0 hg0
  have hA : HasLimitAtInfinity (fun x => A * (g x - B)) 0 := by
    simpa using aux_hasLimit_const_mul A hg0
  have hB : HasLimitAtInfinity (fun x => B * (f x - A)) 0 := by
    simpa using aux_hasLimit_const_mul B hf0
  have hs1 :
      HasLimitAtInfinity
        (fun x => (f x - A) * (g x - B) + A * (g x - B)) 0 := by
    simpa using aux_hasLimit_add hp hA
  have hs2 :
      HasLimitAtInfinity
        (fun x => (f x - A) * (g x - B) + A * (g x - B) +
          B * (f x - A)) 0 := by
    simpa using aux_hasLimit_add hs1 hB
  have hc := aux_hasLimit_const (A * B)
  have hs3 := aux_hasLimit_add hs2 hc
  have hresult :
      HasLimitAtInfinity (fun x => f x * g x) (0 + A * B) := by
    apply aux_hasLimit_congr hs3
    intro x
    ring
  simpa only [zero_add] using hresult

private theorem aux_hasLimit_inv :
    HasLimitAtInfinity (fun x : ℝ => x⁻¹) 0 := by
  intro ε hε
  refine ⟨ε⁻¹, inv_pos.mpr hε, ?_⟩
  intro x hx
  have hxabs : 0 < |x| := lt_trans (inv_pos.mpr hε) hx
  have heq : ε⁻¹ * ε = 1 := inv_mul_cancel₀ (ne_of_gt hε)
  have hxeq : |x|⁻¹ * |x| = 1 := inv_mul_cancel₀ (ne_of_gt hxabs)
  have hp : 0 < (|x| - ε⁻¹) * (|x|⁻¹ * ε) :=
    mul_pos (sub_pos.mpr hx) (mul_pos (inv_pos.mpr hxabs) hε)
  rw [sub_zero, abs_inv]
  nlinarith

private theorem aux_hasLimit_inv_pow (i : ℕ) (hi : 0 < i) :
    HasLimitAtInfinity (fun x : ℝ => (x⁻¹) ^ i) 0 := by
  induction i with
  | zero => simp at hi
  | succ i ih =>
      cases i with
      | zero => simpa using aux_hasLimit_inv
      | succ j =>
          have hprev := ih (Nat.succ_pos j)
          have hmul := aux_hasLimit_mul_zero hprev aux_hasLimit_inv
          simpa [pow_succ] using hmul

private theorem aux_hasLimit_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℝ) (L : ι → ℝ)
    (h : ∀ i ∈ s, HasLimitAtInfinity (f i) (L i)) :
    HasLimitAtInfinity (fun x => ∑ i ∈ s, f i x) (∑ i ∈ s, L i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using aux_hasLimit_const 0
  | @insert i s hi ih =>
      have hiLim := h i (Finset.mem_insert_self i s)
      have hsLim := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      simpa [Finset.sum_insert hi] using aux_hasLimit_add hiLim hsLim

private theorem aux_finset_sum_mul {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) (r : ℝ) :
    (∑ i ∈ s, f i) * r = ∑ i ∈ s, f i * r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, add_mul, ih]

private theorem aux_pow_div_pow_eq_inv_pow (x : ℝ) (hx : x ≠ 0)
    {p q : ℕ} (hpq : p ≤ q) :
    x ^ p / x ^ q = (x⁻¹) ^ (q - p) := by
  apply (div_eq_iff (pow_ne_zero q hx)).2
  rw [inv_pow]
  field_simp [pow_ne_zero (q - p) hx]
  rw [← pow_add]
  congr 1
  omega

private theorem aux_poly_normalized_limit (d : ℕ) (c : ℕ → ℝ) :
    HasLimitAtInfinity (fun x => poly d c x / x ^ d) (c 0) := by
  have hsum :
      (∑ i ∈ Finset.range (d + 1), if i = 0 then c 0 else 0) = c 0 := by
    induction d with
    | zero => simp
    | succ d ih =>
        rw [Finset.sum_range_succ]
        simp [ih]
  have hseries :
      HasLimitAtInfinity
        (fun x => ∑ i ∈ Finset.range (d + 1), c i * (x⁻¹) ^ i) (c 0) := by
    have hs := aux_hasLimit_sum (Finset.range (d + 1))
      (fun i x => c i * (x⁻¹) ^ i)
      (fun i => if i = 0 then c 0 else 0) (by
        intro i hi
        by_cases hi0 : i = 0
        · subst i
          simpa using aux_hasLimit_const (c 0)
        · have hp := aux_hasLimit_inv_pow i (Nat.pos_of_ne_zero hi0)
          have hmul :
              HasLimitAtInfinity (fun x => c i * (x⁻¹) ^ i) (c i * 0) :=
            aux_hasLimit_const_mul (c i) hp
          simpa [hi0] using hmul)
    simpa only [hsum] using hs
  apply aux_hasLimit_congr_nonzero hseries
  intro x hx
  unfold poly
  rw [div_eq_mul_inv, aux_finset_sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hid : i ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hpd : d - i ≤ d := Nat.sub_le d i
  have he : d - (d - i) = i := by omega
  calc
    (c i * x ^ (d - i)) * (x ^ d)⁻¹ =
        c i * (x ^ (d - i) / x ^ d) := by
          rw [div_eq_mul_inv]
          ring
    _ = c i * (x⁻¹) ^ (d - (d - i)) := by
          rw [aux_pow_div_pow_eq_inv_pow x hx hpd]
    _ = c i * (x⁻¹) ^ i := by rw [he]

private theorem aux_poly_over_higher_limit_zero
    (n m : ℕ) (c : ℕ → ℝ) (hnm : n < m) :
    HasLimitAtInfinity (fun x => poly n c x / x ^ m) 0 := by
  have hseries :
      HasLimitAtInfinity
        (fun x => ∑ i ∈ Finset.range (n + 1),
          c i * (x⁻¹) ^ (m - (n - i))) 0 := by
    have hs := aux_hasLimit_sum (Finset.range (n + 1))
      (fun i x => c i * (x⁻¹) ^ (m - (n - i)))
      (fun _ => 0) (by
        intro i hi
        have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have hk : 0 < m - (n - i) := by omega
        have hp := aux_hasLimit_inv_pow (m - (n - i)) hk
        simpa using aux_hasLimit_const_mul (c i) hp)
    simpa using hs
  apply aux_hasLimit_congr_nonzero hseries
  intro x hx
  unfold poly
  rw [div_eq_mul_inv, aux_finset_sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hp : n - i ≤ m := by omega
  calc
    (c i * x ^ (n - i)) * (x ^ m)⁻¹ =
        c i * (x ^ (n - i) / x ^ m) := by
          rw [div_eq_mul_inv]
          ring
    _ = c i * (x⁻¹) ^ (m - (n - i)) := by
          rw [aux_pow_div_pow_eq_inv_pow x hx hp]

private theorem aux_hasLimit_inv_of_ne {g : ℝ → ℝ} {A : ℝ}
    (hg : HasLimitAtInfinity g A) (hA0 : A ≠ 0) :
    HasLimitAtInfinity (fun x => (g x)⁻¹) A⁻¹ := by
  intro ε hε
  have hA : 0 < |A| := abs_pos.mpr hA0
  have hsq : 0 < |A| ^ 2 := by nlinarith [mul_pos hA hA]
  have hsecond : 0 < ε * |A| ^ 2 / 2 := by
    nlinarith [mul_pos hε hsq]
  have hdelta : 0 < min (|A| / 2) (ε * |A| ^ 2 / 2) :=
    lt_min (by linarith) hsecond
  obtain ⟨N, hN, hbound⟩ := hg _ hdelta
  refine ⟨N, hN, ?_⟩
  intro x hx
  have hclose := hbound x hx
  have htri : |A| ≤ |g x| + |g x - A| := by
    calc
      |A| = |g x + (A - g x)| := by congr 1 <;> ring
      _ ≤ |g x| + |A - g x| := abs_add_le _ _
      _ = |g x| + |g x - A| := by rw [abs_sub_comm]
  have hglower : |A| / 2 < |g x| := by
    have hc : |g x - A| < |A| / 2 :=
      lt_of_lt_of_le hclose (min_le_left _ _)
    linarith
  have hgpos : 0 < |g x| := lt_trans (by linarith) hglower
  have hg0 : g x ≠ 0 := abs_pos.mp hgpos
  have hnum : |A - g x| < ε * |A| ^ 2 / 2 := by
    rw [abs_sub_comm]
    exact lt_of_lt_of_le hclose (min_le_right _ _)
  have hden0 : (|A| / 2) * |A| < |g x| * |A| :=
    mul_lt_mul_of_pos_right hglower hA
  have hden : |A| ^ 2 / 2 < |g x| * |A| := by
    nlinarith
  have hscaled := mul_lt_mul_of_pos_left hden hε
  have hnum' : |A - g x| < ε * (|g x| * |A|) := by
    nlinarith [hnum, hscaled]
  have hinv : (g x)⁻¹ - A⁻¹ = (A - g x) / (g x * A) := by
    field_simp [hg0, hA0] <;> ring
  change |(g x)⁻¹ - A⁻¹| < ε
  rw [hinv, abs_div, abs_mul]
  exact (div_lt_iff₀ (mul_pos hgpos hA)).2 hnum'

private theorem aux_hasLimit_div {f g : ℝ → ℝ} {A B : ℝ}
    (hf : HasLimitAtInfinity f A) (hg : HasLimitAtInfinity g B)
    (hB : B ≠ 0) :
    HasLimitAtInfinity (fun x => f x / g x) (A / B) := by
  have hi := aux_hasLimit_inv_of_ne hg hB
  have hm := aux_hasLimit_mul hf hi
  simpa [div_eq_mul_inv] using hm

private theorem aux_power_times_nonzero_tends_abs
    (k : ℕ) (hk : 0 < k) {f : ℝ → ℝ} {A : ℝ}
    (hf : HasLimitAtInfinity f A) (hA0 : A ≠ 0) :
    AbsTendsToInfinity (fun x => x ^ k * f x) := by
  intro E hE
  have hA : 0 < |A| := abs_pos.mpr hA0
  have hhalf : 0 < |A| / 2 := by linarith
  obtain ⟨Nf, hNf, hfN⟩ := hf (|A| / 2) hhalf
  let N := max Nf (max 1 (2 * E / |A|))
  have hN : 0 < N := lt_of_lt_of_le hNf (by simp [N])
  refine ⟨N, hN, ?_⟩
  intro x hx
  have hxNf : Nf < |x| :=
    lt_of_le_of_lt (by simp [N]) hx
  have hxone : 1 < |x| :=
    lt_of_le_of_lt (by simp [N]) hx
  have hxE : 2 * E / |A| < |x| :=
    lt_of_le_of_lt (by simp [N]) hx
  have hclose := hfN x hxNf
  have htri : |A| ≤ |f x| + |f x - A| := by
    calc
      |A| = |f x + (A - f x)| := by congr 1 <;> ring
      _ ≤ |f x| + |A - f x| := abs_add_le _ _
      _ = |f x| + |f x - A| := by rw [abs_sub_comm]
  have hflower : |A| / 2 < |f x| := by linarith
  have hxe : 2 * E < |x| * |A| := (div_lt_iff₀ hA).1 hxE
  have hbase : E < |x| * (|A| / 2) := by nlinarith
  cases k with
  | zero => simp at hk
  | succ j =>
      clear hk
      have hj : 1 ≤ |x| ^ j := by
        induction j with
        | zero => simp
        | succ j ih =>
            rw [pow_succ]
            calc
              1 = 1 * 1 := by ring
              _ ≤ |x| ^ j * |x| :=
                mul_le_mul ih (le_of_lt hxone) zero_le_one
                  (pow_nonneg (abs_nonneg x) j)
      have hpow : |x| ≤ |x| ^ (Nat.succ j) := by
        rw [pow_succ]
        calc
          |x| = 1 * |x| := by ring
          _ ≤ |x| ^ j * |x| :=
            mul_le_mul_of_nonneg_right hj (abs_nonneg x)
      have hstep1 : |x| * (|A| / 2) < |x| * |f x| :=
        mul_lt_mul_of_pos_left hflower (lt_trans zero_lt_one hxone)
      have hstep2 : |x| * |f x| ≤ |x| ^ (Nat.succ j) * |f x| :=
        mul_le_mul_of_nonneg_right hpow (abs_nonneg (f x))
      calc
        E < |x| * (|A| / 2) := hbase
        _ < |x| * |f x| := hstep1
        _ ≤ |x| ^ (Nat.succ j) * |f x| := hstep2
        _ = |x ^ (Nat.succ j) * f x| := by rw [abs_mul, abs_pow]

private theorem aux_normalized_factor
    (n m : ℕ) (a : ℕ → ℝ) (x : ℝ) (hx : x ≠ 0) (hnm : m < n) :
    normalizedNumerator n m a x =
      x ^ (n - m) * normalizedNumerator n n a x := by
  unfold normalizedNumerator
  have hpow : x ^ n = x ^ (n - m) * x ^ m := by
    rw [← pow_add]
    congr 1
    omega
  field_simp [pow_ne_zero m hx, pow_ne_zero n hx]
  rw [hpow]
  ring

private theorem aux_absTends_div {f g : ℝ → ℝ} {B : ℝ}
    (hf : AbsTendsToInfinity f) (hg : HasLimitAtInfinity g B)
    (hB0 : B ≠ 0) :
    AbsTendsToInfinity (fun x => f x / g x) := by
  intro E hE
  have hB : 0 < |B| := abs_pos.mpr hB0
  have hhalf : 0 < |B| / 2 := by linarith
  obtain ⟨Ng, hNg, hgN⟩ := hg (|B| / 2) hhalf
  have hrequest : 0 < E * (2 * |B|) := by positivity
  obtain ⟨Nf, hNf, hfN⟩ := hf (E * (2 * |B|)) hrequest
  refine ⟨max Nf Ng, lt_of_lt_of_le hNf (le_max_left _ _), ?_⟩
  intro x hx
  have hfx := hfN x (lt_of_le_of_lt (le_max_left _ _) hx)
  have hgx := hgN x (lt_of_le_of_lt (le_max_right _ _) hx)
  have hlowerTri : |B| ≤ |g x| + |g x - B| := by
    calc
      |B| = |g x + (B - g x)| := by congr 1 <;> ring
      _ ≤ |g x| + |B - g x| := abs_add_le _ _
      _ = |g x| + |g x - B| := by rw [abs_sub_comm]
  have hglower : |B| / 2 < |g x| := by linarith
  have hgpos : 0 < |g x| := lt_trans (by linarith) hglower
  have hupperTri : |g x| ≤ |B| + |g x - B| := by
    calc
      |g x| = |B + (g x - B)| := by congr 1 <;> ring
      _ ≤ |B| + |g x - B| := abs_add_le _ _
  have hgupper : |g x| < 2 * |B| := by linarith
  change E < |f x / g x|
  rw [abs_div]
  apply (lt_div_iff₀ hgpos).2
  have hscaled := mul_lt_mul_of_pos_left hgupper hE
  exact lt_trans hscaled hfx

theorem gap1 (n m : ℕ) (a b : ℕ → ℝ) : ∀ x, x ≠ 0 →
    R n m a b x =
      normalizedNumerator n m a x / normalizedDenominator m b x := by
  intro x hx
  unfold R normalizedNumerator normalizedDenominator
  by_cases hq : poly m b x = 0
  · simp [hq]
  · field_simp [hq, pow_ne_zero m hx] <;> ring

/-- Source: `proof_gap/exercise_409/2.txt`; unsigned infinity is expressed using absolute values. -/
theorem gap2 (n m : ℕ) (a : ℕ → ℝ) (ha : a 0 ≠ 0) (hnm : m < n) :
    AbsTendsToInfinity (normalizedNumerator n m a) := by
  have hlead :
      HasLimitAtInfinity (normalizedNumerator n n a) (a 0) := by
    simpa [normalizedNumerator] using aux_poly_normalized_limit n a
  have hdiv :=
    aux_power_times_nonzero_tends_abs (n - m) (by omega) hlead ha
  apply aux_absTends_congr_nonzero hdiv
  intro x hx
  exact aux_normalized_factor n m a x hx hnm

/-- Source: `proof_gap/exercise_409/3.txt`. -/
theorem gap3 (n m : ℕ) (b : ℕ → ℝ) (hnm : m < n) :
    HasLimitAtInfinity (normalizedDenominator m b) (b 0) := by
  simpa [normalizedDenominator] using aux_poly_normalized_limit m b

/-- Source: `proof_gap/exercise_409/4.txt`; use magnitude because the sign at the two ends need not agree. -/
theorem gap4 (n m : ℕ) (a b : ℕ → ℝ)
    (ha : a 0 ≠ 0) (hb : b 0 ≠ 0) (hnm : m < n) :
    AbsTendsToInfinity (R n m a b) := by
  have hnum := gap2 n m a ha hnm
  have hden :
      HasLimitAtInfinity (normalizedDenominator m b) (b 0) := by
    simpa [normalizedDenominator] using aux_poly_normalized_limit m b
  have hquot := aux_absTends_div hnum hden hb
  apply aux_absTends_congr_nonzero hquot
  intro x hx
  exact gap1 n m a b x hx

/-- Source: `proof_gap/exercise_409/5.txt`. -/
theorem gap5 (n m : ℕ) (a : ℕ → ℝ) (hnm : n = m) :
    HasLimitAtInfinity (normalizedNumerator n m a) (a 0) := by
  subst m
  simpa [normalizedNumerator] using aux_poly_normalized_limit n a

/-- Source: `proof_gap/exercise_409/6.txt`. -/
theorem gap6 (n m : ℕ) (b : ℕ → ℝ) (hnm : n = m) :
    HasLimitAtInfinity (normalizedDenominator m b) (b 0) := by
  simpa [normalizedDenominator] using aux_poly_normalized_limit m b

/-- Source: `proof_gap/exercise_409/7.txt`. -/
theorem gap7 (n m : ℕ) (a b : ℕ → ℝ)
    (hb : b 0 ≠ 0) (hnm : n = m) :
    HasLimitAtInfinity (R n m a b) (a 0 / b 0) := by
  subst m
  have hnum :
      HasLimitAtInfinity (normalizedNumerator n n a) (a 0) := by
    simpa [normalizedNumerator] using aux_poly_normalized_limit n a
  have hden :
      HasLimitAtInfinity (normalizedDenominator n b) (b 0) := by
    simpa [normalizedDenominator] using aux_poly_normalized_limit n b
  have hquot := aux_hasLimit_div hnum hden hb
  apply aux_hasLimit_congr_nonzero hquot
  intro x hx
  exact gap1 n n a b x hx

/-- Source: `proof_gap/exercise_409/8.txt`. -/
theorem gap8 (n m : ℕ) (a : ℕ → ℝ) (hnm : n < m) :
    HasLimitAtInfinity (normalizedNumerator n m a) 0 := by
  simpa [normalizedNumerator] using aux_poly_over_higher_limit_zero n m a hnm

/-- Source: `proof_gap/exercise_409/9.txt`. -/
theorem gap9 (n m : ℕ) (b : ℕ → ℝ) (hnm : n < m) :
    HasLimitAtInfinity (normalizedDenominator m b) (b 0) := by
  simpa [normalizedDenominator] using aux_poly_normalized_limit m b

/-- Source: `proof_gap/exercise_409/10.txt`. -/
theorem gap10 (n m : ℕ) (a b : ℕ → ℝ)
    (hb : b 0 ≠ 0) (hnm : n < m) :
    HasLimitAtInfinity (R n m a b) 0 := by
  have hnum :
      HasLimitAtInfinity (normalizedNumerator n m a) 0 := by
    simpa [normalizedNumerator] using aux_poly_over_higher_limit_zero n m a hnm
  have hden :
      HasLimitAtInfinity (normalizedDenominator m b) (b 0) := by
    simpa [normalizedDenominator] using aux_poly_normalized_limit m b
  have hquot := aux_hasLimit_div hnum hden hb
  have hresult : HasLimitAtInfinity (R n m a b) (0 / b 0) := by
    apply aux_hasLimit_congr_nonzero hquot
    intro x hx
    exact gap1 n m a b x hx
  simpa using hresult

/-- Source: `proof_gap/exercise_409/11.txt`; replace the mixed real/∞ piecewise value by three typed cases. -/
theorem gap11 (n m : ℕ) (a b : ℕ → ℝ)
    (ha : a 0 ≠ 0) (hb : b 0 ≠ 0) :
    (m < n → AbsTendsToInfinity (R n m a b)) ∧
      (n = m → HasLimitAtInfinity (R n m a b) (a 0 / b 0)) ∧
        (n < m → HasLimitAtInfinity (R n m a b) 0) := by
  constructor
  · intro hmn
    exact gap4 n m a b ha hb hmn
  constructor
  · intro hnm
    exact gap7 n m a b hb hnm
  · intro hnm
    exact gap10 n m a b hb hnm

end

end ProofGap.Exercise409
