import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1215

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def t (x : ℝ) : ℂ := (Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)
def f (p : ℕ) (x : ℝ) : ℝ := Real.sin x ^ (2 * p)

def complexBinomial (p : ℕ) (x : ℝ) : ℂ :=
  1 / (2 * Complex.I) ^ (2 * p) *
    ∑ k ∈ Finset.range (2 * p + 1),
      (Nat.choose (2 * p) k : ℂ) * t x ^ (2 * p - k) *
        (-1 : ℂ) ^ k * star (t x) ^ k

def cosineExpansion (p : ℕ) (x : ℝ) : ℝ :=
  (Nat.choose (2 * p) p : ℝ) / 2 ^ (2 * p) +
    ∑ k ∈ Finset.range p,
      ((-1 : ℝ) ^ (p + k) * 2 * (Nat.choose (2 * p) k : ℝ) /
          2 ^ (2 * p)) * Real.cos ((2 * p - 2 * k : ℕ) * x)

def derivativeExpansion (p n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range p,
    ((-1 : ℝ) ^ (p + k) * 2 * (Nat.choose (2 * p) k : ℝ) /
        2 ^ (2 * p)) *
      (2 * p - 2 * k : ℝ) ^ n *
      Real.cos ((2 * p - 2 * k : ℕ) * x + (n : ℝ) / 2 * Real.pi)

private theorem t_mul (x y : ℝ) : t x * t y = t (x + y) := by
  apply Complex.ext <;>
    simp [t, Real.cos_add, Real.sin_add] <;>
    ring

private theorem star_t (x : ℝ) : star (t x) = t (-x) := by
  apply Complex.ext <;>
    simp [t, Real.cos_neg, Real.sin_neg]

private theorem t_pow (n : ℕ) (x : ℝ) : t x ^ n = t ((n : ℝ) * x) := by
  induction n with
  | zero => simp [t]
  | succ n ih =>
      rw [pow_succ, ih, t_mul]
      congr 1
      push_cast
      ring

private theorem two_mul_I_sq : (2 * Complex.I : ℂ) ^ 2 = -4 := by
  calc
    (2 * Complex.I : ℂ) ^ 2 = 4 * (Complex.I * Complex.I) := by ring
    _ = -4 := by rw [Complex.I_mul_I]; norm_num

private theorem two_mul_I_pow_even (p : ℕ) :
    (2 * Complex.I : ℂ) ^ (2 * p) =
      (-1 : ℂ) ^ p * (2 : ℂ) ^ (2 * p) := by
  calc
    (2 * Complex.I : ℂ) ^ (2 * p) = ((2 * Complex.I : ℂ) ^ 2) ^ p := by
      rw [pow_mul]
    _ = (-4 : ℂ) ^ p := by rw [two_mul_I_sq]
    _ = ((-1 : ℂ) * 4) ^ p := by norm_num
    _ = (-1 : ℂ) ^ p * (4 : ℂ) ^ p := by rw [mul_pow]
    _ = (-1 : ℂ) ^ p * (2 : ℂ) ^ (2 * p) := by
      congr 1
      rw [show (4 : ℂ) = 2 ^ 2 by norm_num, ← pow_mul]

private theorem neg_one_pow_mod_two (n : ℕ) :
    (-1 : ℝ) ^ n = (-1 : ℝ) ^ (n % 2) := by
  conv_lhs => rw [show n = n % 2 + 2 * (n / 2) by omega]
  rw [pow_add, pow_mul]
  norm_num

private def fourierSummand (p : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ (p + k) * (Nat.choose (2 * p) k : ℝ) /
      2 ^ (2 * p) *
    Real.cos (((2 * p : ℕ) : ℝ) * x - 2 * (k : ℝ) * x)

private theorem complex_summand_re (p k : ℕ) (x : ℝ)
    (hk : k ≤ 2 * p) :
    (1 / (2 * Complex.I) ^ (2 * p) *
        (Nat.choose (2 * p) k : ℂ) * t x ^ (2 * p - k) *
        (-1 : ℂ) ^ k * star (t x) ^ k).re =
      fourierSummand p x k := by
  have hcast : (((2 * p - k : ℕ) : ℝ)) = (2 * p : ℝ) - k := by
    rw [Nat.cast_sub hk]
    norm_num
  have harg :
      ((2 * p : ℝ) - k) * x + (k : ℝ) * (-x) =
        ((2 * p : ℕ) : ℝ) * x - 2 * (k : ℝ) * x := by
    push_cast
    ring
  have hcoeff :
      1 / ((-1 : ℂ) ^ p * (2 : ℂ) ^ (2 * p)) *
          (Nat.choose (2 * p) k : ℂ) * (-1 : ℂ) ^ k =
        (((-1 : ℝ) ^ (p + k) * (Nat.choose (2 * p) k : ℝ) /
          2 ^ (2 * p) : ℝ) : ℂ) := by
    have hs : ((-1 : ℂ) ^ p)⁻¹ = (-1 : ℂ) ^ p := by
      rw [← inv_pow]
      norm_num
    push_cast
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev, hs, pow_add]
    ring
  have hrearrange :
      1 / (2 * Complex.I) ^ (2 * p) *
          (Nat.choose (2 * p) k : ℂ) * t x ^ (2 * p - k) *
          (-1 : ℂ) ^ k * star (t x) ^ k =
        (((-1 : ℝ) ^ (p + k) * (Nat.choose (2 * p) k : ℝ) /
          2 ^ (2 * p) : ℝ) : ℂ) *
          t (((2 * p : ℕ) : ℝ) * x - 2 * (k : ℝ) * x) := by
    rw [two_mul_I_pow_even, t_pow, star_t, t_pow, hcast]
    calc
      1 / ((-1 : ℂ) ^ p * (2 : ℂ) ^ (2 * p)) *
          (Nat.choose (2 * p) k : ℂ) * t (((2 * p : ℝ) - k) * x) *
          (-1 : ℂ) ^ k * t ((k : ℝ) * -x) =
        (1 / ((-1 : ℂ) ^ p * (2 : ℂ) ^ (2 * p)) *
          (Nat.choose (2 * p) k : ℂ) * (-1 : ℂ) ^ k) *
          (t (((2 * p : ℝ) - k) * x) * t ((k : ℝ) * -x)) := by ring
      _ = (((-1 : ℝ) ^ (p + k) * (Nat.choose (2 * p) k : ℝ) /
          2 ^ (2 * p) : ℝ) : ℂ) *
          (t (((2 * p : ℝ) - k) * x) * t ((k : ℝ) * -x)) := by
        rw [hcoeff]
      _ = (((-1 : ℝ) ^ (p + k) * (Nat.choose (2 * p) k : ℝ) /
          2 ^ (2 * p) : ℝ) : ℂ) *
          t ((((2 * p : ℝ) - k) * x) + (k : ℝ) * -x) := by
        rw [t_mul]
      _ = (((-1 : ℝ) ^ (p + k) * (Nat.choose (2 * p) k : ℝ) /
          2 ^ (2 * p) : ℝ) : ℂ) *
          t (((2 * p : ℕ) : ℝ) * x - 2 * (k : ℝ) * x) := by
        rw [harg]
  have ht_re (y : ℝ) : (t y).re = Real.cos y := by
    change Real.cos y + (0 * Real.sin y - 1 * 0) = Real.cos y
    ring
  rw [hrearrange]
  change
    ((-1 : ℝ) ^ (p + k) * (Nat.choose (2 * p) k : ℝ) /
        2 ^ (2 * p)) *
          (t (((2 * p : ℕ) : ℝ) * x - 2 * (k : ℝ) * x)).re -
      0 * (t (((2 * p : ℕ) : ℝ) * x - 2 * (k : ℝ) * x)).im =
        fourierSummand p x k
  simp [ht_re, fourierSummand]

private theorem complexBinomial_re (p : ℕ) (x : ℝ) :
    (complexBinomial p x).re =
      ∑ k ∈ Finset.range (2 * p + 1), fourierSummand p x k := by
  unfold complexBinomial
  rw [Finset.mul_sum]
  change Complex.reCLM
      (∑ k ∈ Finset.range (2 * p + 1),
        1 / (2 * Complex.I) ^ (2 * p) *
          ((Nat.choose (2 * p) k : ℂ) * t x ^ (2 * p - k) *
            (-1 : ℂ) ^ k * star (t x) ^ k)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  simpa only [mul_assoc] using complex_summand_re p k x (by omega)

private theorem fourierSummand_reflect (p : ℕ) (x : ℝ) (k : ℕ)
    (hk : k ≤ 2 * p) :
    fourierSummand p x (2 * p - k) = fourierSummand p x k := by
  have hpar :
      (p + (2 * p - k)) % 2 = (p + k) % 2 := by omega
  have hsign :
      (-1 : ℝ) ^ (p + (2 * p - k)) = (-1 : ℝ) ^ (p + k) := by
    calc
      (-1 : ℝ) ^ (p + (2 * p - k)) =
          (-1 : ℝ) ^ ((p + (2 * p - k)) % 2) :=
        neg_one_pow_mod_two (p + (2 * p - k))
      _ = (-1 : ℝ) ^ ((p + k) % 2) := by rw [hpar]
      _ = (-1 : ℝ) ^ (p + k) := (neg_one_pow_mod_two (p + k)).symm
  have hchoose :
      Nat.choose (2 * p) (2 * p - k) = Nat.choose (2 * p) k := by
    simpa using (Nat.choose_symm hk)
  have hcast : (((2 * p - k : ℕ) : ℝ)) = (2 * p : ℝ) - k := by
    rw [Nat.cast_sub hk]
    norm_num
  have hangle :
      (((2 * p : ℕ) : ℝ) * x - 2 * ((2 * p - k : ℕ) : ℝ) * x) =
        -(((2 * p : ℕ) : ℝ) * x - 2 * (k : ℝ) * x) := by
    rw [hcast]
    push_cast
    ring
  simp only [fourierSummand]
  rw [hsign, hchoose, hangle, Real.cos_neg]

private theorem sum_fourier_reflect (p : ℕ) (x : ℝ)
    (hreflect : ∀ k, k ≤ 2 * p →
      fourierSummand p x (2 * p - k) = fourierSummand p x k) :
    (∑ k ∈ Finset.range (2 * p + 1), fourierSummand p x k) =
      fourierSummand p x p +
        2 * ∑ k ∈ Finset.range p, fourierSummand p x k := by
  classical
  have hsplit :
      Finset.range (2 * p + 1) =
        Finset.range p ∪ Finset.Icc p (2 * p) := by
    ext k
    simp
    omega
  have hd : Disjoint (Finset.range p) (Finset.Icc p (2 * p)) := by
    rw [Finset.disjoint_left]
    intro k hk hki
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Icc] at hki
    omega
  have himage :
      Finset.Icc p (2 * p) =
        (Finset.range (p + 1)).image (fun k => 2 * p - k) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hk
      refine ⟨2 * p - k, ?_, ?_⟩
      · omega
      · omega
    · rintro ⟨a, ha, rfl⟩
      omega
  rw [hsplit, Finset.sum_union hd, himage]
  rw [Finset.sum_image]
  · rw [Finset.sum_range_succ]
    have hlow :
        (∑ k ∈ Finset.range p, fourierSummand p x (2 * p - k)) =
          ∑ k ∈ Finset.range p, fourierSummand p x k := by
      apply Finset.sum_congr rfl
      intro k hk
      apply hreflect
      simp only [Finset.mem_range] at hk
      omega
    rw [hlow, hreflect p (by omega)]
    ring
  · intro a ha b hb hab
    have ha_lt : a < p + 1 := Finset.mem_range.mp ha
    have hb_lt : b < p + 1 := Finset.mem_range.mp hb
    change 2 * p - a = 2 * p - b at hab
    have ha_le : a ≤ 2 * p := by omega
    have hb_le : b ≤ 2 * p := by omega
    have ha_cancel : 2 * p - a + a = 2 * p := Nat.sub_add_cancel ha_le
    have hb_cancel : 2 * p - b + b = 2 * p := Nat.sub_add_cancel hb_le
    have hsum_eq : 2 * p - a + a = 2 * p - b + b := by
      calc
        2 * p - a + a = 2 * p := ha_cancel
        _ = 2 * p - b + b := hb_cancel.symm
    rw [hab] at hsum_eq
    exact Nat.add_left_cancel hsum_eq

private theorem fourierSummand_recombine (p : ℕ) (x : ℝ) :
    fourierSummand p x p +
        2 * ∑ k ∈ Finset.range p, fourierSummand p x k =
      cosineExpansion p x := by
  have hmiddle :
      fourierSummand p x p =
        (Nat.choose (2 * p) p : ℝ) / 2 ^ (2 * p) := by
    have heven : (-1 : ℝ) ^ (p + p) = 1 := by
      rw [show p + p = 2 * p by omega, pow_mul]
      norm_num
    simp [fourierSummand, heven]
  rw [hmiddle]
  unfold cosineExpansion
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  have hle : 2 * k ≤ 2 * p := by omega
  have hcast : (((2 * p - 2 * k : ℕ) : ℝ)) = (2 * p : ℝ) - 2 * k := by
    rw [Nat.cast_sub hle]
    norm_num
  rw [hcast]
  simp [fourierSummand]
  push_cast
  ring

private theorem hasDerivAt_cos_phase (a c : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y => c * a ^ n *
        Real.cos (a * y + (n : ℝ) / 2 * Real.pi))
      (c * a ^ (n + 1) *
        Real.cos (a * x + ((n + 1 : ℕ) : ℝ) / 2 * Real.pi)) x := by
  have h :=
    ((((hasDerivAt_id x).const_mul a).add_const
      ((n : ℝ) / 2 * Real.pi)).cos.const_mul (c * a ^ n))
  have h' :
      HasDerivAt
        (fun y => c * a ^ n *
          Real.cos (a * y + (n : ℝ) / 2 * Real.pi))
        (c * a ^ n *
          (-Real.sin (a * x + (n : ℝ) / 2 * Real.pi) * a)) x := by
    simpa only [id_eq, mul_one] using h
  have hphase :
      a * x + ((n + 1 : ℕ) : ℝ) / 2 * Real.pi =
        (a * x + (n : ℝ) / 2 * Real.pi) + Real.pi / 2 := by
    push_cast
    ring
  convert h' using 1
  rw [hphase, Real.cos_add_pi_div_two]
  ring

private theorem hasDerivAt_derivativeExpansion (p n : ℕ) (x : ℝ) :
    HasDerivAt (derivativeExpansion p n)
      (derivativeExpansion p (n + 1) x) x := by
  have hsum :
      HasDerivAt
        (∑ k ∈ Finset.range p, fun y =>
          ((-1 : ℝ) ^ (p + k) * 2 *
              (Nat.choose (2 * p) k : ℝ) / 2 ^ (2 * p)) *
            (2 * p - 2 * k : ℝ) ^ n *
            Real.cos (((2 * p - 2 * k : ℕ) : ℝ) * y +
              (n : ℝ) / 2 * Real.pi))
        (∑ k ∈ Finset.range p,
          ((-1 : ℝ) ^ (p + k) * 2 *
              (Nat.choose (2 * p) k : ℝ) / 2 ^ (2 * p)) *
            (2 * p - 2 * k : ℝ) ^ (n + 1) *
            Real.cos (((2 * p - 2 * k : ℕ) : ℝ) * x +
              ((n + 1 : ℕ) : ℝ) / 2 * Real.pi)) x := by
    exact
      HasDerivAt.sum (u := Finset.range p) (x := x)
        (fun k hk => by
          have hklt : k < p := Finset.mem_range.mp hk
          have hle : 2 * k ≤ 2 * p := by omega
          have hcast :
              (((2 * p - 2 * k : ℕ) : ℝ)) = (2 * p : ℝ) - 2 * k := by
            rw [Nat.cast_sub hle]
            norm_num
          have hterm :
              HasDerivAt
                (fun y =>
                  ((-1 : ℝ) ^ (p + k) * 2 *
                      (Nat.choose (2 * p) k : ℝ) / 2 ^ (2 * p)) *
                    (2 * p - 2 * k : ℝ) ^ n *
                    Real.cos (((2 * p - 2 * k : ℕ) : ℝ) * y +
                      (n : ℝ) / 2 * Real.pi))
                (((-1 : ℝ) ^ (p + k) * 2 *
                      (Nat.choose (2 * p) k : ℝ) / 2 ^ (2 * p)) *
                    (2 * p - 2 * k : ℝ) ^ (n + 1) *
                    Real.cos (((2 * p - 2 * k : ℕ) : ℝ) * x +
                      ((n + 1 : ℕ) : ℝ) / 2 * Real.pi)) x := by
            convert hasDerivAt_cos_phase
                (2 * p - 2 * k : ℝ)
                ((-1 : ℝ) ^ (p + k) * 2 *
                  (Nat.choose (2 * p) k : ℝ) / 2 ^ (2 * p)) n x using 1 <;>
              simp only [hcast]
          exact hterm)
  have hfun :
      (∑ k ∈ Finset.range p, fun y =>
        ((-1 : ℝ) ^ (p + k) * 2 *
            (Nat.choose (2 * p) k : ℝ) / 2 ^ (2 * p)) *
          (2 * p - 2 * k : ℝ) ^ n *
          Real.cos (((2 * p - 2 * k : ℕ) : ℝ) * y +
            (n : ℝ) / 2 * Real.pi)) = derivativeExpansion p n := by
    funext y
    simp only [Finset.sum_apply, derivativeExpansion]
  have hder :
      (∑ k ∈ Finset.range p,
        ((-1 : ℝ) ^ (p + k) * 2 *
            (Nat.choose (2 * p) k : ℝ) / 2 ^ (2 * p)) *
          (2 * p - 2 * k : ℝ) ^ (n + 1) *
          Real.cos (((2 * p - 2 * k : ℕ) : ℝ) * x +
            ((n + 1 : ℕ) : ℝ) / 2 * Real.pi)) =
        derivativeExpansion p (n + 1) x := by
    rfl
  rw [← hfun, ← hder]
  exact hsum

private theorem hasDerivAt_cosineExpansion (p : ℕ) (x : ℝ) :
    HasDerivAt (cosineExpansion p)
      (derivativeExpansion p 1 x) x := by
  have h :=
    (hasDerivAt_const x
      ((Nat.choose (2 * p) p : ℝ) / 2 ^ (2 * p))).add
      (hasDerivAt_derivativeExpansion p 0 x)
  have hfun :
      (fun _ : ℝ => (Nat.choose (2 * p) p : ℝ) / 2 ^ (2 * p)) +
          derivativeExpansion p 0 = cosineExpansion p := by
    funext y
    simp [cosineExpansion, derivativeExpansion]
  rw [hfun] at h
  simpa only [zero_add] using h

private theorem deriv_cosineExpansion (p : ℕ) :
    deriv (cosineExpansion p) = derivativeExpansion p 1 := by
  funext x
  exact (hasDerivAt_cosineExpansion p x).deriv

private theorem deriv_derivativeExpansion (p n : ℕ) :
    deriv (derivativeExpansion p n) = derivativeExpansion p (n + 1) := by
  funext x
  exact (hasDerivAt_derivativeExpansion p n x).deriv

private theorem iterDeriv_add_one (n : ℕ) (g : ℝ → ℝ) :
    iterDeriv (n + 1) g = deriv (iterDeriv n g) := by
  simp [iterDeriv, Function.iterate_succ_apply']

private theorem iterDeriv_cosineExpansion_succ (p m : ℕ) :
    iterDeriv (m + 1) (cosineExpansion p) =
      derivativeExpansion p (m + 1) := by
  induction m with
  | zero =>
      simpa [iterDeriv_add_one] using deriv_cosineExpansion p
  | succ m ih =>
      calc
        iterDeriv (m.succ + 1) (cosineExpansion p) =
            deriv (iterDeriv m.succ (cosineExpansion p)) :=
          iterDeriv_add_one m.succ (cosineExpansion p)
        _ = deriv (derivativeExpansion p m.succ) := by rw [ih]
        _ = derivativeExpansion p (m.succ + 1) := by
          rw [deriv_derivativeExpansion]

theorem gap1 (p : ℕ) (x : ℝ) (hp : 1 ≤ p) :
    (Real.sin x : ℂ) = 1 / (2 * Complex.I) * (t x - star (t x)) := by
  have hI : (2 * Complex.I : ℂ) ≠ 0 := by norm_num
  have hdiff :
      t x - star (t x) = 2 * Complex.I * (Real.sin x : ℂ) := by
    rw [star_t]
    apply Complex.ext <;>
      simp [t, Real.cos_neg, Real.sin_neg] <;>
      ring
  rw [hdiff]
  field_simp [hI]

theorem gap2 (p : ℕ) (x : ℝ) (hp : 1 ≤ p) :
    (Real.sin x : ℂ) ^ (2 * p) =
      1 / (2 * Complex.I) ^ (2 * p) * (t x - star (t x)) ^ (2 * p) := by
  calc
    (Real.sin x : ℂ) ^ (2 * p) =
        (1 / (2 * Complex.I) * (t x - star (t x))) ^ (2 * p) := by
      rw [gap1 p x hp]
    _ = (1 / (2 * Complex.I)) ^ (2 * p) *
        (t x - star (t x)) ^ (2 * p) := by
      rw [mul_pow]
    _ = 1 / (2 * Complex.I) ^ (2 * p) *
        (t x - star (t x)) ^ (2 * p) := by
      rw [one_div_pow]

theorem gap3 (p : ℕ) (x : ℝ) (hp : 1 ≤ p) :
    1 / (2 * Complex.I) ^ (2 * p) * (t x - star (t x)) ^ (2 * p) =
      complexBinomial p x := by
  unfold complexBinomial
  congr 1
  rw [sub_eq_add_neg, add_comm, add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [neg_pow]
  ring

theorem gap4 (p : ℕ) (x : ℝ) (hp : 1 ≤ p) :
    (f p x : ℂ) = complexBinomial p x := by
  simpa [f] using (gap2 p x hp).trans (gap3 p x hp)

theorem gap5 (p : ℕ) (x : ℝ) (hp : 1 ≤ p) :
    f p x = cosineExpansion p x := by
  have hc := congrArg Complex.re (gap4 p x hp)
  have hreflect : ∀ k, k ≤ 2 * p →
      fourierSummand p x (2 * p - k) = fourierSummand p x k := by
    intro k hk
    exact fourierSummand_reflect p x k hk
  have hsum := sum_fourier_reflect p x hreflect
  calc
    f p x = (complexBinomial p x).re := by simpa using hc
    _ = ∑ k ∈ Finset.range (2 * p + 1), fourierSummand p x k :=
      complexBinomial_re p x
    _ = fourierSummand p x p +
        2 * ∑ k ∈ Finset.range p, fourierSummand p x k := hsum
    _ = cosineExpansion p x := fourierSummand_recombine p x

theorem gap6 (p n : ℕ) (x : ℝ) (hp : 1 ≤ p) :
    iterDeriv n (f p) x = iterDeriv n (cosineExpansion p) x := by
  have hfun : f p = cosineExpansion p := by
    funext y
    exact gap5 p y hp
  rw [hfun]

theorem gap7 (p n : ℕ) (x : ℝ) (hp : 1 ≤ p) (hn : 1 ≤ n) :
    iterDeriv n (f p) x = derivativeExpansion p n x := by
  rw [gap6 p n x hp]
  cases n with
  | zero => omega
  | succ m =>
      simpa [Nat.succ_eq_add_one] using
        congrFun (iterDeriv_cosineExpansion_succ p m) x

end

end ProofGap.Exercise1215
