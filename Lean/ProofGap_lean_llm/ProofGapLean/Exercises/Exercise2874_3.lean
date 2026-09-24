import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2874_3

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def auxiliary (x h : ℝ) : ℝ :=
  (h / (1 + x ^ 2)) / (1 + x / (1 + x ^ 2) * h)

def AlgebraicConditions (x h : ℝ) : Prop :=
  1 + x / (1 + x ^ 2) * h ≠ 0 ∧ 1 - x * auxiliary x h ≠ 0

def SmallEnough (x h : ℝ) : Prop :=
  |x / (1 + x ^ 2) * h| < 1 ∧
    |auxiliary x h| < 1 ∧
    0 < 1 - x * auxiliary x h

def arctangentTerm (y : ℝ) (m : ℕ) : ℝ :=
  (-1 : ℝ) ^ m * y ^ (2 * m + 1) / (2 * m + 1)

def auxiliaryGeometricTerm (x h : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * (x / (1 + x ^ 2) * h) ^ k

def expandedOuterTerm (x h : ℝ) (m : ℕ) : ℝ :=
  (-1 : ℝ) ^ m / (2 * m + 1) *
    (h / (1 + x ^ 2)) ^ (2 * m + 1) *
      (∑' s : ℕ,
        (Nat.choose (2 * m + s) s : ℝ) * (-1 : ℝ) ^ s *
          (x * h / (1 + x ^ 2)) ^ s)

def derivativeSum (x : ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range ((n + 1) / 2),
    (-1 : ℝ) ^ m * (Nat.choose (n - 1) (2 * m) : ℝ) *
      x ^ (n - 2 * m - 1) / (2 * m + 1)

def coefficientTerm (x h : ℝ) (n : ℕ) : ℝ :=
  let q := n + 1
  (-1 : ℝ) ^ (q - 1) / (1 + x ^ 2) ^ q *
    derivativeSum x q * h ^ q

def A (x : ℝ) (n : ℕ) : ℝ :=
  derivativeSum x n

private lemma sum_range_odd
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ)
    (heven : ∀ k : ℕ, Even k → f k = 0) :
    ∑ k ∈ Finset.range (n + 1), f k =
      ∑ m ∈ Finset.range ((n + 1) / 2), f (2 * m + 1) := by
  calc
    _ = ∑ k ∈ (Finset.range (n + 1)).filter Odd, f k := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro k hk hknot
      apply heven k
      rw [← Nat.not_odd_iff_even]
      intro hkodd
      apply hknot
      simp [hk, hkodd]
    _ = _ := by
      apply Finset.sum_bij (fun k _ => k / 2)
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_range] at hk
        rw [Nat.odd_iff] at hk
        simp only [Finset.mem_range]
        rw [Nat.lt_div_iff_mul_lt (by norm_num : 0 < 2)]
        omega
      · intro k₁ hk₁ k₂ hk₂ heq
        simp only [Finset.mem_filter, Finset.mem_range] at hk₁ hk₂
        rw [Nat.odd_iff] at hk₁ hk₂
        omega
      · intro m hm
        simp only [Finset.mem_range] at hm
        refine ⟨2 * m + 1, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_range]
          constructor
          · omega
          · exact ⟨m, by omega⟩
        · omega
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_range] at hk
        rw [Nat.odd_iff] at hk
        apply congrArg f
        omega

private lemma I_pow_even_im (m : ℕ) :
    (Complex.I ^ (2 * m)).im = 0 := by
  rw [pow_mul, Complex.I_sq]
  have hreal :
      (-1 : ℂ) ^ m = (↑((-1 : ℝ) ^ m) : ℂ) := by
    rw [Complex.ofReal_pow]
    norm_num
  simp only [hreal, Complex.ofReal_im]

private lemma I_pow_odd_im (m : ℕ) :
    (Complex.I ^ (2 * m + 1)).im = (-1 : ℝ) ^ m := by
  rw [pow_add, pow_mul, Complex.I_sq]
  simp only [pow_one]
  have hreal :
      (-1 : ℂ) ^ m = (↑((-1 : ℝ) ^ m) : ℂ) := by
    rw [Complex.ofReal_pow]
    norm_num
  rw [Complex.mul_im]
  rw [hreal]
  rw [Complex.ofReal_re, Complex.ofReal_im]
  norm_num

private lemma complex_term_im (x : ℝ) (n k : ℕ) :
    (Complex.I ^ k * (x : ℂ) ^ (n - k) *
      (Nat.choose n k : ℂ)).im =
      (Complex.I ^ k).im * x ^ (n - k) * (Nat.choose n k : ℝ) := by
  have hxpow :
      (x : ℂ) ^ (n - k) = (↑(x ^ (n - k)) : ℂ) := by
    exact (Complex.ofReal_pow x (n - k)).symm
  rw [hxpow]
  rw [Complex.mul_im, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im]
  ring

private lemma complex_term_im_even (x : ℝ) (n k : ℕ) (hk : Even k) :
    (Complex.I ^ k * (x : ℂ) ^ (n - k) *
      (Nat.choose n k : ℂ)).im = 0 := by
  rw [complex_term_im]
  rcases hk with ⟨m, rfl⟩
  rw [show m + m = 2 * m by omega, I_pow_even_im]
  ring

private lemma derivativeSum_mul_eq_im (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * derivativeSum x n =
      (((x : ℂ) + Complex.I) ^ n).im := by
  rw [show (x : ℂ) + Complex.I = Complex.I + (x : ℂ) by ring]
  rw [add_pow, Complex.im_sum]
  rw [sum_range_odd
    (fun k : ℕ =>
      (Complex.I ^ k * (x : ℂ) ^ (n - k) *
        (Nat.choose n k : ℂ)).im)
    n (complex_term_im_even x n)]
  unfold derivativeSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_range] at hm
  rw [complex_term_im, I_pow_odd_im]
  have hlt : 2 * m < n := by
    rw [Nat.lt_div_iff_mul_lt (by norm_num : 0 < 2)] at hm
    omega
  have hsubadd : n - 1 + 1 = n := by omega
  have hchooseNat := Nat.add_one_mul_choose_eq (n - 1) (2 * m)
  rw [hsubadd] at hchooseNat
  have hchoose :
      (n : ℝ) * (Nat.choose (n - 1) (2 * m) : ℝ) =
        (Nat.choose n (2 * m + 1) : ℝ) * (2 * m + 1 : ℝ) := by
    exact_mod_cast hchooseNat
  have hden : (2 * m + 1 : ℝ) ≠ 0 := by positivity
  rw [show n - (2 * m + 1) = n - 2 * m - 1 by omega]
  calc
    (n : ℝ) *
          ((-1 : ℝ) ^ m * (Nat.choose (n - 1) (2 * m) : ℝ) *
            x ^ (n - 2 * m - 1) / (2 * m + 1 : ℝ)) =
        (-1 : ℝ) ^ m * x ^ (n - 2 * m - 1) *
          ((n : ℝ) * (Nat.choose (n - 1) (2 * m) : ℝ)) /
            (2 * m + 1 : ℝ) := by ring
    _ = (-1 : ℝ) ^ m * x ^ (n - 2 * m - 1) *
          ((Nat.choose n (2 * m + 1) : ℝ) * (2 * m + 1 : ℝ)) /
            (2 * m + 1 : ℝ) := by rw [hchoose]
    _ = (-1 : ℝ) ^ m * x ^ (n - 2 * m - 1) *
          (Nat.choose n (2 * m + 1) : ℝ) := by
      field_simp

private lemma im_pow_recurrence (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (1 + x ^ 2) * (((x : ℂ) + Complex.I) ^ (n - 1)).im -
        2 * x * (((x : ℂ) + Complex.I) ^ n).im =
      -(((x : ℂ) + Complex.I) ^ (n + 1)).im := by
  let z : ℂ := (x : ℂ) + Complex.I
  have hquad : z ^ 2 = (2 * x : ℂ) * z - (1 + x ^ 2 : ℝ) := by
    apply Complex.ext
    · simp [z, pow_two, Complex.mul_re]
      ring
    · simp [z, pow_two, Complex.mul_im]
      ring
  have hpow : z ^ (n + 1) =
      (2 * x : ℂ) * z ^ n - (1 + x ^ 2 : ℝ) * z ^ (n - 1) := by
    calc
      z ^ (n + 1) = z ^ (n - 1) * z ^ 2 := by
        rw [← pow_add]
        congr 1
        omega
      _ = z ^ (n - 1) *
          ((2 * x : ℂ) * z - (1 + x ^ 2 : ℝ)) := by rw [hquad]
      _ = (2 * x : ℂ) * z ^ n -
          (1 + x ^ 2 : ℝ) * z ^ (n - 1) := by
        rw [show z ^ n = z ^ (n - 1) * z by
          rw [← pow_succ]
          congr 1
          omega]
        ring
  have him := congrArg Complex.im hpow
  have htwo : (2 : ℂ) * (x : ℂ) = (↑(2 * x) : ℂ) := by norm_num
  rw [htwo] at him
  simp only [Complex.sub_im, Complex.im_ofReal_mul] at him
  change (1 + x ^ 2) * (z ^ (n - 1)).im -
      2 * x * (z ^ n).im = -(z ^ (n + 1)).im
  linarith

private lemma hasDerivAt_im_pow (x : ℝ) (n : ℕ) :
    HasDerivAt
      (fun y : ℝ => (((y : ℂ) + Complex.I) ^ n).im)
      ((n : ℝ) * (((x : ℂ) + Complex.I) ^ (n - 1)).im) x := by
  have hcast :
      HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using
      Complex.ofRealCLM.hasDerivAt
  have hpow :=
    (hcast.add_const Complex.I).pow n
  have him :=
    (hasDerivAt_const x Complex.imCLM).clm_apply hpow
  convert him using 1 <;>
    simp [Complex.imCLM_apply, mul_comm]

private noncomputable def higherForm (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ (n - 1) * (Nat.factorial (n - 1) : ℝ) *
    (((x : ℂ) + Complex.I) ^ n).im / (1 + x ^ 2) ^ n

private lemma hasDerivAt_higherForm (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    HasDerivAt (higherForm n) (higherForm (n + 1) x) x := by
  let c : ℝ :=
    (-1 : ℝ) ^ (n - 1) * (Nat.factorial (n - 1) : ℝ)
  have hp := (hasDerivAt_im_pow x n).const_mul c
  have hd0 :
      HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2) using 1 <;>
      simp [id]
  have hd := hd0.pow n
  have hne : (1 + x ^ 2) ^ n ≠ 0 := by positivity
  have hquot := hp.div hd hne
  have hrec := im_pow_recurrence x n hn
  have hsucc : (n - 1).succ = n := by omega
  have hfactNat : n.factorial = n * (n - 1).factorial := by
    have hsubadd : n - 1 + 1 = n := by omega
    simpa only [hsubadd] using Nat.factorial_succ (n - 1)
  have hfact :
      (Nat.factorial n : ℝ) =
        (n : ℝ) * (Nat.factorial (n - 1) : ℝ) := by
    exact_mod_cast hfactNat
  have hsign : -(-1 : ℝ) ^ (n - 1) = (-1 : ℝ) ^ n := by
    cases n with
    | zero => omega
    | succ k => simp [pow_succ]
  have hpowexp :
      (1 + x ^ 2) ^ (n - 1) * (1 + x ^ 2) ^ n * (1 + x ^ 2) =
        (1 + x ^ 2) ^ (n * 2) := by
    calc
      _ = (1 + x ^ 2) ^ ((n - 1) + n) * (1 + x ^ 2) := by
        rw [pow_add]
      _ = (1 + x ^ 2) ^ ((n - 1) + n + 1) := by
        exact (pow_succ _ _).symm
      _ = _ := by
        congr 1
        omega
  convert hquot using 1
  · simp only [higherForm, c, Pi.pow_apply, Nat.add_sub_cancel]
    field_simp [hne]
    rw [hfact, ← hsign]
    ring_nf at hrec ⊢
    linear_combination
      -(-1 : ℝ) ^ (n - 1) * (Nat.factorial (n - 1) : ℝ) *
        (n : ℝ) * (1 + x ^ 2) ^ (n * 2) * hrec -
      -2 * (-1 : ℝ) ^ (n - 1) * (Nat.factorial (n - 1) : ℝ) *
        (n : ℝ) * x * (((x : ℂ) + Complex.I) ^ n).im * hpowexp

private lemma iterDeriv_arctan_eq_higherForm
    (n : ℕ) (hn : 1 ≤ n) :
    iterDeriv n Real.arctan = higherForm n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        funext x
        simp [iterDeriv, higherForm, Real.deriv_arctan]
      · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have hiter := ih hnpos
        funext x
        calc
          iterDeriv (Nat.succ n) Real.arctan x =
              deriv (iterDeriv n Real.arctan) x := by
                simp only [iterDeriv, Function.iterate_succ_apply']
          _ = deriv (higherForm n) x := by rw [hiter]
          _ = higherForm (n + 1) x :=
            (hasDerivAt_higherForm x n hnpos).deriv
          _ = higherForm (Nat.succ n) x := by rfl

theorem gap1
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.arctan x) :
    ∀ x h : ℝ, AlgebraicConditions x h →
      (x + auxiliary x h) / (1 - x * auxiliary x h) = x + h := by
  intro x h halg
  rcases halg with ⟨hinner, houter⟩
  have hxden : 1 + x ^ 2 ≠ 0 := by positivity
  let d : ℝ := 1 + x ^ 2
  let e : ℝ := 1 + x / d * h
  let y : ℝ := (h / d) / e
  have hd : d ≠ 0 := by simpa [d] using hxden
  have he : e ≠ 0 := by simpa [e, d] using hinner
  have heq : e = (d + x * h) / d := by
    dsimp [e]
    field_simp [hd]
  have hde : d + x * h ≠ 0 := by
    intro hzero
    apply he
    rw [heq, hzero]
    simp
  have hyform : y = h / (d + x * h) := by
    dsimp [y]
    rw [heq]
    field_simp [hd, hde]
  have hy : y * (d + x * h) = h := by
    rw [hyform]
    exact div_mul_cancel₀ h hde
  have hout : 1 - x * y ≠ 0 := by
    simpa [y, e, d] using houter
  change (x + y) / (1 - x * y) = x + h
  apply (div_eq_iff hout).2
  dsimp [d] at hy
  ring_nf at hy ⊢
  linear_combination hy

theorem gap2
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.arctan x)
    (hauxiliary :
      ∀ x h : ℝ, AlgebraicConditions x h →
        (x + auxiliary x h) / (1 - x * auxiliary x h) = x + h) :
    ∀ x h : ℝ,
      f (x + h) - f x = Real.arctan (x + h) - Real.arctan x := by
  intro x h
  rw [hf (x + h), hf x]

theorem gap3
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.arctan x)
    (hauxiliary :
      ∀ x h : ℝ, AlgebraicConditions x h →
        (x + auxiliary x h) / (1 - x * auxiliary x h) = x + h)
    (hincrement :
      ∀ x h : ℝ,
        f (x + h) - f x = Real.arctan (x + h) - Real.arctan x) :
    ∀ x h : ℝ, AlgebraicConditions x h →
      Real.arctan (x + h) - Real.arctan x =
        Real.arctan ((x + auxiliary x h) / (1 - x * auxiliary x h)) -
          Real.arctan x := by
  intro x h halg
  rw [hauxiliary x h halg]

theorem gap4
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.arctan x) :
    ∀ x h : ℝ, SmallEnough x h →
      Real.arctan ((x + auxiliary x h) / (1 - x * auxiliary x h)) -
          Real.arctan x =
        Real.arctan (auxiliary x h) := by
  intro x h hsmall
  have hmul : x * auxiliary x h < 1 := by
    linarith [hsmall.2.2]
  have hadd :=
    Real.arctan_add (x := x) (y := auxiliary x h) hmul
  linarith

theorem gap5
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.arctan x)
    (hincrement :
      ∀ x h : ℝ,
        f (x + h) - f x = Real.arctan (x + h) - Real.arctan x)
    (hsubstitute :
      ∀ x h : ℝ, AlgebraicConditions x h →
        Real.arctan (x + h) - Real.arctan x =
          Real.arctan ((x + auxiliary x h) / (1 - x * auxiliary x h)) -
            Real.arctan x)
    (haddition :
      ∀ x h : ℝ, SmallEnough x h →
        Real.arctan ((x + auxiliary x h) / (1 - x * auxiliary x h)) -
            Real.arctan x =
          Real.arctan (auxiliary x h)) :
    ∀ x h : ℝ, SmallEnough x h → AlgebraicConditions x h →
      f (x + h) - f x = Real.arctan (auxiliary x h) := by
  intro x h hsmall halg
  rw [hincrement x h, hsubstitute x h halg, haddition x h hsmall]

theorem gap6
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.arctan x)
    (haux :
      ∀ x h : ℝ, SmallEnough x h → AlgebraicConditions x h →
        f (x + h) - f x = Real.arctan (auxiliary x h)) :
    ∀ x h : ℝ, SmallEnough x h → AlgebraicConditions x h →
      f (x + h) - f x =
        Real.arctan
          ((h / (1 + x ^ 2)) * (1 / (1 + x / (1 + x ^ 2) * h))) := by
  intro x h hsmall halg
  rw [haux x h hsmall halg]
  simp [auxiliary, div_eq_mul_inv]

theorem gap7
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.arctan x) :
    ∀ x h : ℝ, SmallEnough x h →
      Real.arctan (auxiliary x h) =
        ∑' m, arctangentTerm (auxiliary x h) m := by
  intro x h hsmall
  have hnorm : ‖auxiliary x h‖ < 1 := by
    simpa [Real.norm_eq_abs] using hsmall.2.1
  simpa [arctangentTerm] using
    (Real.hasSum_arctan hnorm).tsum_eq.symm

theorem gap8
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.arctan x) :
    ∀ x h : ℝ, SmallEnough x h →
      auxiliary x h =
        (h / (1 + x ^ 2)) * (1 / (1 + x / (1 + x ^ 2) * h)) := by
  intro x h hsmall
  simp [auxiliary, div_eq_mul_inv]

theorem gap9
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.arctan x) :
    ∀ x h : ℝ, SmallEnough x h →
      (h / (1 + x ^ 2)) * (1 / (1 + x / (1 + x ^ 2) * h)) =
        h / (1 + x ^ 2) * (∑' k, auxiliaryGeometricTerm x h k) := by
  intro x h hsmall
  let q : ℝ := x / (1 + x ^ 2) * h
  have hq : ‖-q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_neg]
    exact hsmall.1
  have hs :
      HasSum (fun k : ℕ => auxiliaryGeometricTerm x h k)
        (1 + q)⁻¹ := by
    have hfun :
        (fun k : ℕ => auxiliaryGeometricTerm x h k) =
          (fun k : ℕ => (-q) ^ k) := by
      funext k
      change (-1 : ℝ) ^ k * q ^ k = (-q) ^ k
      rw [neg_pow q k]
    rw [hfun]
    convert hasSum_geometric_of_norm_lt_one hq using 1
    ring
  change
    h / (1 + x ^ 2) * (1 / (1 + q)) =
      h / (1 + x ^ 2) *
        (∑' k, auxiliaryGeometricTerm x h k)
  rw [hs.tsum_eq]
  simp only [one_div]

theorem gap10
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.arctan x)
    (hauxiliary :
      ∀ x h : ℝ, SmallEnough x h →
        auxiliary x h =
          (h / (1 + x ^ 2)) * (1 / (1 + x / (1 + x ^ 2) * h)))
    (hgeometric :
      ∀ x h : ℝ, SmallEnough x h →
        (h / (1 + x ^ 2)) * (1 / (1 + x / (1 + x ^ 2) * h)) =
          h / (1 + x ^ 2) * (∑' k, auxiliaryGeometricTerm x h k)) :
    ∀ x h : ℝ, SmallEnough x h →
      auxiliary x h =
        h / (1 + x ^ 2) * (∑' k, auxiliaryGeometricTerm x h k) := by
  intro x h hsmall
  exact (hauxiliary x h hsmall).trans (hgeometric x h hsmall)

theorem gap11
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.arctan x)
    (hincrement :
      ∀ x h : ℝ, SmallEnough x h → AlgebraicConditions x h →
        f (x + h) - f x = Real.arctan (auxiliary x h))
    (harctanSeries :
      ∀ x h : ℝ, SmallEnough x h →
        Real.arctan (auxiliary x h) =
          ∑' m, arctangentTerm (auxiliary x h) m)
    (hauxSeries :
      ∀ x h : ℝ, SmallEnough x h →
        auxiliary x h =
          h / (1 + x ^ 2) * (∑' k, auxiliaryGeometricTerm x h k)) :
    ∀ x h : ℝ, SmallEnough x h → AlgebraicConditions x h →
      f (x + h) - f x =
        ∑' m : ℕ,
          (-1 : ℝ) ^ m / (2 * m + 1) *
            (h / (1 + x ^ 2) *
              (∑' k, auxiliaryGeometricTerm x h k)) ^ (2 * m + 1) := by
  intro x h hsmall halg
  rw [hincrement x h hsmall halg, harctanSeries x h hsmall,
    hauxSeries x h hsmall]
  apply tsum_congr
  intro m
  simp only [arctangentTerm]
  ring

theorem gap12
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.arctan x)
    (hsubstituted :
      ∀ x h : ℝ, SmallEnough x h → AlgebraicConditions x h →
        f (x + h) - f x =
          ∑' m : ℕ,
            (-1 : ℝ) ^ m / (2 * m + 1) *
              (h / (1 + x ^ 2) *
                (∑' k, auxiliaryGeometricTerm x h k)) ^ (2 * m + 1)) :
    ∀ x h : ℝ, SmallEnough x h → AlgebraicConditions x h →
      f (x + h) - f x = ∑' m, expandedOuterTerm x h m := by
  intro x h hsmall halg
  rw [hsubstituted x h hsmall halg]
  let q : ℝ := x / (1 + x ^ 2) * h
  have hq : ‖-q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_neg]
    exact hsmall.1
  have hgeom :
      (∑' k : ℕ, auxiliaryGeometricTerm x h k) = (1 + q)⁻¹ := by
    have hfun :
        (fun k : ℕ => auxiliaryGeometricTerm x h k) =
          (fun k : ℕ => (-q) ^ k) := by
      funext k
      change (-1 : ℝ) ^ k * q ^ k = (-q) ^ k
      rw [neg_pow q k]
    rw [hfun, (hasSum_geometric_of_norm_lt_one hq).tsum_eq]
    ring
  apply tsum_congr
  intro m
  have hbinom :
      (∑' s : ℕ,
        (Nat.choose (2 * m + s) s : ℝ) * (-1 : ℝ) ^ s * q ^ s) =
          1 / (1 + q) ^ (2 * m + 1) := by
    calc
      _ = ∑' s : ℕ,
          (Nat.choose (s + 2 * m) (2 * m) : ℝ) * (-q) ^ s := by
        apply tsum_congr
        intro s
        have hc :
            (Nat.choose (2 * m + s) s : ℝ) =
              (Nat.choose (s + 2 * m) (2 * m) : ℝ) := by
          exact_mod_cast (by
            simpa [Nat.add_comm] using
              (Nat.choose_symm_add (a := s) (b := 2 * m)))
        rw [hc]
        calc
          _ = (Nat.choose (s + 2 * m) (2 * m) : ℝ) *
                ((-1 : ℝ) ^ s * q ^ s) := by ring
          _ = _ := congrArg
            (fun z : ℝ => (Nat.choose (s + 2 * m) (2 * m) : ℝ) * z)
            (neg_pow q s).symm
      _ = 1 / (1 - (-q)) ^ (2 * m + 1) :=
        tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (2 * m) hq
      _ = _ := by ring
  have hqform : x * h / (1 + x ^ 2) = q := by
    dsimp [q]
    ring
  have hinv :
      ((1 + q)⁻¹) ^ (2 * m + 1) =
        1 / (1 + q) ^ (2 * m + 1) := by
    rw [one_div, inv_pow]
  simp only [expandedOuterTerm]
  rw [hgeom, hqform, hbinom]
  calc
    _ = (-1 : ℝ) ^ m / (2 * m + 1) *
          (h / (1 + x ^ 2)) ^ (2 * m + 1) *
            ((1 + q)⁻¹) ^ (2 * m + 1) := by
      rw [mul_pow]
      ring
    _ = _ := by rw [hinv]

theorem gap13
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.arctan x)
    (hexpanded :
      ∀ x h : ℝ, SmallEnough x h → AlgebraicConditions x h →
        f (x + h) - f x = ∑' m, expandedOuterTerm x h m) :
    ∀ x h : ℝ, SmallEnough x h → h ^ 2 < 1 + x ^ 2 →
      AlgebraicConditions x h →
      f (x + h) - f x = ∑' n, coefficientTerm x h n := by
  intro x h hsmall hconv halg
  let d : ℝ := 1 + x ^ 2
  let w : ℂ := ((h / d : ℝ) : ℂ) * ((x : ℂ) + Complex.I)
  have hdpos : 0 < d := by
    dsimp [d]
    positivity
  have hwsq : ‖w‖ ^ 2 = h ^ 2 / d := by
    rw [Complex.sq_norm]
    simp only [w, Complex.normSq_mul, Complex.normSq_ofReal]
    rw [show (x : ℂ) + Complex.I =
        (x : ℂ) + (1 : ℝ) * Complex.I by norm_num,
      Complex.normSq_add_mul_I]
    field_simp [hdpos.ne']
    ring
  have hw : ‖w‖ < 1 := by
    have hsquare : ‖w‖ ^ 2 < 1 := by
      rw [hwsq]
      apply (div_lt_one hdpos).2
      simpa [d] using hconv
    nlinarith [norm_nonneg w]
  have hlog0 := Complex.hasSum_taylorSeries_log hw
  have hlog :
      HasSum
        (fun n : ℕ =>
          (-1 : ℂ) ^ n * w ^ (n + 1) / (n + 1 : ℂ))
        (Complex.log (1 + w)) := by
    have hshift := (hasSum_nat_add_iff' 1).2 hlog0
    convert hshift using 1 with n
    · simp [pow_succ]
    · simp
  have him := hlog.map Complex.imCLM Complex.imCLM.continuous
  have him' :
      HasSum
        (fun n : ℕ =>
          ((-1 : ℂ) ^ n * w ^ (n + 1) / (n + 1 : ℂ)).im)
        (Complex.log (1 + w)).im := by
    simpa [Function.comp_def, Complex.imCLM_apply] using him
  have hterm : ∀ n : ℕ,
      coefficientTerm x h n =
        ((-1 : ℂ) ^ n * w ^ (n + 1) / (n + 1 : ℂ)).im := by
    intro n
    have hn : 1 ≤ n + 1 := by omega
    have hn0 : (n + 1 : ℝ) ≠ 0 := by positivity
    have hderiv := derivativeSum_mul_eq_im x (n + 1) hn
    have hz :
        (-1 : ℂ) ^ n * w ^ (n + 1) / (n + 1 : ℂ) =
          ((((-1 : ℝ) ^ n * (h / d) ^ (n + 1) /
              (n + 1 : ℝ) : ℝ) : ℂ) *
            (((x : ℂ) + Complex.I) ^ (n + 1))) := by
      dsimp [w]
      rw [mul_pow]
      push_cast
      ring
    rw [hz, Complex.im_ofReal_mul, ← hderiv]
    simp only [coefficientTerm, Nat.add_sub_cancel]
    rw [div_pow]
    dsimp [d]
    field_simp [hn0]
    push_cast
    ring
  let q : ℝ := x / (1 + x ^ 2) * h
  have hqsmall : |q| < 1 := by
    simpa [q] using hsmall.1
  have hqpos : 0 < 1 + q := by
    linarith [(abs_lt.mp hqsmall).1]
  have hwre : w.re = h / d * x := by
    dsimp [w]
    simp [Complex.mul_re]
  have hwim : w.im = h / d := by
    dsimp [w]
    simp [Complex.mul_im]
  have hdenpos : 0 < 1 + x ^ 2 + x * h := by
    calc
      1 + x ^ 2 + x * h = d * (1 + q) := by
        dsimp [d, q]
        field_simp [hdpos.ne']
      _ > 0 := mul_pos hdpos hqpos
  have hdenpos' : 0 < 1 + h * x + x ^ 2 := by
    nlinarith [hdenpos]
  have hfactor :
      1 + w = ((1 + q : ℝ) : ℂ) *
        (1 + (auxiliary x h : ℂ) * Complex.I) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.one_re, hwre, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, add_zero, zero_mul]
      dsimp [d, q]
      ring
    · simp only [Complex.add_im, Complex.one_im, hwim, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, add_zero, zero_mul, mul_one, zero_add]
      change h / d = (1 + q) * ((h / d) / (1 + q))
      field_simp [hqpos.ne']
  have harg :
      (1 + (auxiliary x h : ℂ) * Complex.I).arg =
        Real.arctan (auxiliary x h) := by
    let r : ℝ := Real.sqrt (1 + (auxiliary x h) ^ 2)
    have hr : 0 < r := by
      dsimp [r]
      positivity
    have hpolar :
        1 + (auxiliary x h : ℂ) * Complex.I =
          (r : ℂ) *
            ((Real.cos (Real.arctan (auxiliary x h)) : ℂ) +
              (Real.sin (Real.arctan (auxiliary x h)) : ℂ) * Complex.I) := by
      rw [Real.cos_arctan, Real.sin_arctan]
      apply Complex.ext
      · simp [r, hr.ne']
      · simp [r, hr.ne']
        field_simp [hr.ne']
    rw [hpolar]
    rw [Complex.ofReal_cos, Complex.ofReal_sin]
    apply Complex.arg_mul_cos_add_sin_mul_I hr
    have ha := Real.arctan_mem_Ioo (auxiliary x h)
    have hpihalf : Real.pi / 2 < Real.pi :=
      div_lt_self Real.pi_pos one_lt_two
    exact ⟨(neg_lt_neg hpihalf).trans ha.1, (ha.2.trans hpihalf).le⟩
  have hlogim :
      (Complex.log (1 + w)).im = Real.arctan (auxiliary x h) := by
    rw [Complex.log_im, hfactor, Complex.arg_real_mul _ hqpos, harg]
  have hcoeff :
      HasSum (coefficientTerm x h) (Real.arctan (auxiliary x h)) := by
    rw [← hlogim]
    rw [funext hterm]
    exact him'
  have harct := gap4 f hf x h hsmall
  rw [gap1 f hf x h halg] at harct
  rw [hf (x + h), hf x, harct]
  exact hcoeff.tsum_eq.symm

theorem gap14
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.arctan x)
    (hcoefficientSeries :
      ∀ x h : ℝ, SmallEnough x h → h ^ 2 < 1 + x ^ 2 →
        AlgebraicConditions x h →
        f (x + h) - f x = ∑' n, coefficientTerm x h n) :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      iterDeriv n f x =
        (-1 : ℝ) ^ (n - 1) * (Nat.factorial n : ℝ) /
          (1 + x ^ 2) ^ n * A x n := by
  intro n hn x
  have hfun : f = Real.arctan := funext hf
  rw [hfun, iterDeriv_arctan_eq_higherForm n hn]
  have hfactNat : n.factorial = n * (n - 1).factorial := by
    have hsubadd : n - 1 + 1 = n := by omega
    simpa only [hsubadd] using Nat.factorial_succ (n - 1)
  have hfact :
      (Nat.factorial n : ℝ) =
        (n : ℝ) * (Nat.factorial (n - 1) : ℝ) := by
    exact_mod_cast hfactNat
  simp only [higherForm, A]
  rw [← derivativeSum_mul_eq_im x n hn, hfact]
  ring

theorem gap15
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.arctan x) :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      (-1 : ℝ) ^ (n - 1) * (Nat.factorial n : ℝ) /
          (1 + x ^ 2) ^ n * A x n =
        (-1 : ℝ) ^ (n - 1) * (Nat.factorial n : ℝ) /
          (1 + x ^ 2) ^ n * derivativeSum x n := by
  intro n hn x
  rfl

theorem gap16
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.arctan x)
    (hwithA :
      ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
        iterDeriv n f x =
          (-1 : ℝ) ^ (n - 1) * (Nat.factorial n : ℝ) /
            (1 + x ^ 2) ^ n * A x n)
    (hsubstitute :
      ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
        (-1 : ℝ) ^ (n - 1) * (Nat.factorial n : ℝ) /
            (1 + x ^ 2) ^ n * A x n =
          (-1 : ℝ) ^ (n - 1) * (Nat.factorial n : ℝ) /
            (1 + x ^ 2) ^ n * derivativeSum x n) :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      iterDeriv n f x =
        (-1 : ℝ) ^ (n - 1) * (Nat.factorial n : ℝ) /
          (1 + x ^ 2) ^ n * derivativeSum x n := by
  intro n hn x
  exact (hwithA n hn x).trans (hsubstitute n hn x)

theorem gap17
    (f : ℝ → ℝ) (hf : ∀ x, f x = Real.arctan x)
    (hderivative :
      ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
        iterDeriv n f x =
          (-1 : ℝ) ^ (n - 1) * (Nat.factorial n : ℝ) /
            (1 + x ^ 2) ^ n * derivativeSum x n) :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      iterDeriv n f x =
        (-1 : ℝ) ^ (n - 1) * (Nat.factorial n : ℝ) /
          (1 + x ^ 2) ^ n *
            (∑ m ∈ Finset.range ((n + 1) / 2),
              (-1 : ℝ) ^ m * (Nat.choose (n - 1) (2 * m) : ℝ) *
                x ^ (n - 2 * m - 1) / (2 * m + 1)) := by
  intro n hn x
  simpa [derivativeSum] using hderivative n hn x

end

end ProofGap.Exercise2874_3
