import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise1224

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f

def f (n : ℕ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else x ^ (2 * n) * Real.sin (1 / x)

def reciprocalSine (x : ℝ) : ℝ := Real.sin (1 / x)

def IsBigOAtZero (g h : ℝ → ℝ) : Prop :=
  ∃ C > 0, ∃ ε > 0, ∀ x, 0 < |x| → |x| < ε → |g x| ≤ C * |h x|

def HasPuncturedLimit (g : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto g (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

def leadingTerm (n m : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ m * x ^ (2 * (n - m)) *
    Real.sin (1 / x + (m : ℝ) * Real.pi / 2)

def leibnizSum (n m : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1),
    (Nat.choose m i : ℝ) *
      iterDeriv (m - i) (fun t : ℝ => t ^ (2 * n)) x *
      iterDeriv i reciprocalSine x

theorem gap1 (n m : ℕ) (x : ℝ) (hm : 1 ≤ m) (hx : x ≠ 0) :
    iterDeriv m (f n) x =
      iterDeriv m (fun t : ℝ => t ^ (2 * n) * Real.sin (1 / t)) x := by
  congr 2
  funext t
  by_cases ht : t = 0
  · subst t
    simp [f]
  · simp [f, ht]

theorem gap2 (n m : ℕ) (x : ℝ) (hm : 1 ≤ m) (hx : x ≠ 0) :
    iterDeriv m (fun t : ℝ => t ^ (2 * n) * Real.sin (1 / t)) x =
      leibnizSum n m x := by
  have hp : ContDiffAt ℝ m (fun t : ℝ => t ^ (2 * n)) x := by fun_prop
  have hs : ContDiffAt ℝ m reciprocalSine x := by
    unfold reciprocalSine
    exact Real.contDiff_sin.contDiffAt.comp x
      (contDiffAt_const.div contDiffAt_id hx)
  rw [show (fun t : ℝ => t ^ (2 * n) * Real.sin (1 / t)) =
      (fun t : ℝ => reciprocalSine t * t ^ (2 * n)) by
        funext t
        simp [reciprocalSine, mul_comm]]
  rw [iterDeriv, ← iteratedDeriv_eq_iterate,
    iteratedDeriv_fun_mul hs hp]
  simp only [leibnizSum, iterDeriv, ← iteratedDeriv_eq_iterate]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem gap3 (n m : ℕ) (x : ℝ) (hm : 1 ≤ m) (hx : x ≠ 0) :
    iterDeriv m (f n) x = leibnizSum n m x := by
  rw [gap1 n m x hm hx, gap2 n m x hm hx]

private def oscTerm (i k : ℕ) (x : ℝ) : ℝ :=
  x ^ (-(i + k : ℤ)) *
    Real.sin (1 / x + (k : ℝ) * Real.pi / 2)

private theorem hasDerivAt_oscTerm (i k : ℕ) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (oscTerm i k)
      (-(i + k : ℝ) * oscTerm (i + 1) k x -
        oscTerm (i + 1) (k + 1) x) x := by
  have hp := hasDerivAt_zpow (-(i + k : ℤ)) x (Or.inl hx)
  have hi : HasDerivAt (fun t : ℝ => 1 / t) (-1 / x ^ 2) x := by
    convert (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx using 1 <;>
      simp [id] <;> ring
  have hu := hi.add_const ((k : ℝ) * Real.pi / 2)
  have hs := (Real.hasDerivAt_sin
    (1 / x + (k : ℝ) * Real.pi / 2)).comp x hu
  unfold oscTerm
  convert hp.mul hs using 1
  simp only [Function.comp_apply]
  have hphase : 1 / x + (k + 1 : ℕ) * Real.pi / 2 =
      (1 / x + (k : ℝ) * Real.pi / 2) + Real.pi / 2 := by
    push_cast
    ring
  rw [hphase, Real.sin_add_pi_div_two]
  have he₁ : -(i + k : ℤ) - 1 = -((i + 1) + k : ℕ) := by omega
  have he₂ : -(i + k : ℤ) - 2 = -((i + 1) + (k + 1) : ℕ) := by omega
  rw [he₁]
  have hz : x ^ (-(i + k : ℤ)) / x ^ 2 =
      x ^ (-(i + k : ℤ) - 2) := by
    rw [div_eq_mul_inv, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hx]
    congr 1
  push_cast
  rw [show x ^ (-(i + k : ℤ)) *
      (Real.cos (1 / x + (k : ℝ) * Real.pi / 2) * (-1 / x ^ 2)) =
      -Real.cos (1 / x + (k : ℝ) * Real.pi / 2) *
        (x ^ (-(i + k : ℤ)) / x ^ 2) by ring]
  rw [hz, he₂]
  ring_nf
  rw [show -2 + (-(i : ℤ) - (k : ℤ)) =
    -((2 + i + k : ℕ) : ℤ) by omega]
  ring

private theorem reciprocal_expansion (i : ℕ) (hi : 1 ≤ i) :
    ∃ b : ℕ → ℝ, b i = (-1 : ℝ) ^ i ∧
      ∀ x : ℝ, x ≠ 0 →
        iterDeriv i reciprocalSine x =
          ∑ k ∈ Finset.Ico 1 (i + 1), b k * oscTerm i k x := by
  induction i, hi using Nat.le_induction with
  | base =>
      let b : ℕ → ℝ := fun _ => -1
      refine ⟨b, by simp [b], ?_⟩
      intro x hx
      have hi' : HasDerivAt (fun t : ℝ => 1 / t) (-1 / x ^ 2) x := by
        convert (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx using 1 <;>
          simp [id] <;> ring
      have hs : HasDerivAt reciprocalSine
          (Real.cos (1 / x) * (-1 / x ^ 2)) x := by
        unfold reciprocalSine
        simpa only [Function.comp_apply] using
          (Real.hasDerivAt_sin (1 / x)).comp x hi'
      simp only [iterDeriv, Function.iterate_one, hs.deriv]
      simp [b, oscTerm, Real.sin_add_pi_div_two]
      field_simp [hx]
  | succ i hi ih =>
      rcases ih with ⟨b, hbi, hb⟩
      let b' : ℕ → ℝ := fun k =>
        (if k ≤ i then b k * (-(i + k : ℝ)) else 0) -
          (if 2 ≤ k then b (k - 1) else 0)
      refine ⟨b', ?_, ?_⟩
      · simp [b', show ¬i + 1 ≤ i by omega, show 2 ≤ i + 1 by omega, hbi,
          pow_succ]
      · intro x hx
        have hev : (iterDeriv i reciprocalSine) =ᶠ[nhds x]
            (fun y => ∑ k ∈ Finset.Ico 1 (i + 1), b k * oscTerm i k y) := by
          filter_upwards [eventually_ne_nhds hx] with y hy
          exact hb y hy
        have hd : HasDerivAt
            (fun y => ∑ k ∈ Finset.Ico 1 (i + 1),
              b k * oscTerm i k y)
            (∑ k ∈ Finset.Ico 1 (i + 1),
              b k * (-(i + k : ℝ) * oscTerm (i + 1) k x -
                oscTerm (i + 1) (k + 1) x)) x := by
          have hsum :=
            HasDerivAt.sum (u := Finset.Ico 1 (i + 1)) fun k hk =>
              (hasDerivAt_oscTerm i k x hx).const_mul (b k)
          convert hsum using 1
          funext y
          simp only [Finset.sum_apply]
        rw [show iterDeriv (i + 1) reciprocalSine =
            deriv (iterDeriv i reciprocalSine) by
          funext y
          simp [iterDeriv, Function.iterate_succ_apply']]
        change deriv (iterDeriv i reciprocalSine) x = _
        rw [Filter.EventuallyEq.deriv_eq hev, hd.deriv]
        have hfirst :
            (∑ k ∈ Finset.Ico 1 (i + 1),
              b k * (-(i + k : ℝ)) * oscTerm (i + 1) k x) =
            ∑ k ∈ Finset.Ico 1 (i + 2),
              (if k ≤ i then b k * (-(i + k : ℝ)) else 0) *
                oscTerm (i + 1) k x := by
          rw [Finset.sum_Ico_succ_top (a := 1) (b := i + 1) (by omega)]
          rw [if_neg (show ¬i + 1 ≤ i by omega)]
          simp only [zero_mul, add_zero]
          apply Finset.sum_congr rfl
          intro k hk
          rw [if_pos]
          exact (by
            have hki := (Finset.mem_Ico.mp hk).2
            omega)
        have hshift :
            (∑ k ∈ Finset.Ico 1 (i + 1),
              b k * oscTerm (i + 1) (k + 1) x) =
            ∑ k ∈ Finset.Ico 1 (i + 2),
              (if 2 ≤ k then b (k - 1) else 0) *
                oscTerm (i + 1) k x := by
          have hmove :
              (∑ k ∈ Finset.Ico 1 (i + 1),
                b k * oscTerm (i + 1) (k + 1) x) =
              ∑ k ∈ Finset.Ico 2 (i + 2),
                b (k - 1) * oscTerm (i + 1) k x := by
            simpa [add_comm, add_left_comm, add_assoc] using
              (Finset.sum_Ico_add
                (fun k => b (k - 1) * oscTerm (i + 1) k x)
                1 (i + 1) 1)
          rw [hmove]
          symm
          rw [← Finset.sum_Ico_consecutive
            (fun k => (if 2 ≤ k then b (k - 1) else 0) *
              oscTerm (i + 1) k x) (by omega : 1 ≤ 2) (by omega : 2 ≤ i + 2)]
          have hone : (∑ k ∈ Finset.Ico 1 2,
              (if 2 ≤ k then b (k - 1) else 0) *
                oscTerm (i + 1) k x) = 0 := by
            norm_num
          rw [hone, zero_add]
          apply Finset.sum_congr rfl
          intro k hk
          rw [if_pos (Finset.mem_Ico.mp hk).1]
        calc
          (∑ k ∈ Finset.Ico 1 (i + 1),
              b k * (-(i + k : ℝ) * oscTerm (i + 1) k x -
                oscTerm (i + 1) (k + 1) x)) =
              (∑ k ∈ Finset.Ico 1 (i + 1),
                b k * (-(i + k : ℝ)) * oscTerm (i + 1) k x) -
              ∑ k ∈ Finset.Ico 1 (i + 1),
                b k * oscTerm (i + 1) (k + 1) x := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ = (∑ k ∈ Finset.Ico 1 (i + 2),
                (if k ≤ i then b k * (-(i + k : ℝ)) else 0) *
                  oscTerm (i + 1) k x) -
              ∑ k ∈ Finset.Ico 1 (i + 2),
                (if 2 ≤ k then b (k - 1) else 0) *
                  oscTerm (i + 1) k x := by rw [hfirst, hshift]
          _ = ∑ k ∈ Finset.Ico 1 (i + 1 + 1),
                b' k * oscTerm (i + 1) k x := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr
            · congr
            · intro k hk
              dsimp [b']
              ring

theorem gap4 (i : ℕ) (hi : 1 ≤ i) :
    ∃ a : ℕ → ℝ, ∀ x : ℝ, x ≠ 0 →
      iterDeriv i reciprocalSine x =
        (∑ k ∈ Finset.Ico 1 i,
          a k * x ^ (-(i + k : ℤ)) *
            Real.sin (1 / x + (k : ℝ) * Real.pi / 2)) +
        (-x ^ (-2 : ℤ)) ^ i *
          Real.sin (1 / x + (i : ℝ) * Real.pi / 2) := by
  rcases reciprocal_expansion i hi with ⟨b, hbi, hb⟩
  refine ⟨b, ?_⟩
  intro x hx
  rw [hb x hx, Finset.sum_Ico_succ_top hi]
  simp only [oscTerm]
  rw [hbi]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    ring
  · have hz :
        (x ^ (-2 : ℤ)) ^ i = x ^ (-(i + i : ℤ)) := by
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [show -x ^ (-2 : ℤ) = (-1 : ℝ) * x ^ (-2 : ℤ) by ring,
      mul_pow, hz]
    ring

private theorem pow_mul_zpow_neg (x : ℝ) (hx : x ≠ 0) (a b : ℕ) (hba : b ≤ a) :
    x ^ a * x ^ (-(b : ℤ)) = x ^ (a - b) := by
  rw [← zpow_natCast, ← zpow_add₀ hx]
  have he : (a : ℤ) + -(b : ℤ) = ((a - b : ℕ) : ℤ) := by omega
  rw [he, zpow_natCast]

private theorem neg_zpow_pow (x : ℝ) (i : ℕ) :
    (-x ^ (-2 : ℤ)) ^ i = (-1 : ℝ) ^ i * x ^ (-(2 * i : ℕ) : ℤ) := by
  rw [show -x ^ (-2 : ℤ) = (-1 : ℝ) * x ^ (-2 : ℤ) by ring, mul_pow]
  congr 1
  rw [← zpow_natCast, ← zpow_mul]
  congr 1

private theorem bigO_add {g h q : ℝ → ℝ}
    (hg : IsBigOAtZero g q) (hh : IsBigOAtZero h q) :
    IsBigOAtZero (fun x => g x + h x) q := by
  rcases hg with ⟨Cg, hCg, εg, hεg, hg⟩
  rcases hh with ⟨Ch, hCh, εh, hεh, hh⟩
  exact ⟨Cg + Ch, add_pos hCg hCh, min εg εh, lt_min hεg hεh,
    fun x hx hxε => (abs_add_le (g x) (h x)).trans
      ((add_le_add
        (hg x hx (lt_of_lt_of_le hxε (min_le_left _ _)))
        (hh x hx (lt_of_lt_of_le hxε (min_le_right _ _)))).trans_eq
          (add_mul Cg Ch |q x|).symm)⟩

private theorem bigO_sum {ι : Type} [DecidableEq ι] (s : Finset ι)
    (g : ι → ℝ → ℝ) (q : ℝ → ℝ)
    (hg : ∀ i ∈ s, IsBigOAtZero (g i) q) :
    IsBigOAtZero (fun x => ∑ i ∈ s, g i x) q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, zero_lt_one, 1, zero_lt_one, ?_⟩
      intro x hx hx1
      simpa only [Finset.sum_empty, abs_zero] using
        mul_nonneg zero_le_one (abs_nonneg (q x))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact bigO_add (hg a (by simp)) (ih (fun i hi => hg i (by simp [hi])))

private theorem bigO_monomial_sin (c phase : ℝ) (e p : ℕ) (hpe : p ≤ e) :
    IsBigOAtZero
      (fun x => c * x ^ e * Real.sin (1 / x + phase))
      (fun x => |x| ^ p) := by
  refine ⟨|c| + 1, by positivity, 1, by norm_num, ?_⟩
  intro x hx hx1
  have hpow : |x| ^ e ≤ |x| ^ p :=
    pow_le_pow_of_le_one (abs_nonneg x) (le_of_lt hx1) hpe
  have hsin := Real.abs_sin_le_one (1 / x + phase)
  have hc : |c| ≤ |c| + 1 := by linarith
  calc
    |(fun x => c * x ^ e * Real.sin (1 / x + phase)) x| =
        |c| * |x| ^ e * |Real.sin (1 / x + phase)| := by
          rw [abs_mul, abs_mul, abs_pow]
    _ ≤ |c| * |x| ^ e := by
      simpa using mul_le_mul_of_nonneg_left hsin
        (mul_nonneg (abs_nonneg c) (pow_nonneg (abs_nonneg x) e))
    _ ≤ |c| * |x| ^ p :=
      mul_le_mul_of_nonneg_left hpow (abs_nonneg c)
    _ ≤ (|c| + 1) * |x| ^ p :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg (abs_nonneg x) p)
    _ = (|c| + 1) * |(fun x => |x| ^ p) x| := by
      rw [abs_of_nonneg (pow_nonneg (abs_nonneg x) p)]

private theorem bigO_congr_punctured {g h q : ℝ → ℝ}
    (hgh : ∀ x, x ≠ 0 → g x = h x)
    (hh : IsBigOAtZero h q) : IsBigOAtZero g q := by
  rcases hh with ⟨C, hC, ε, hε, hh⟩
  refine ⟨C, hC, ε, hε, ?_⟩
  intro x hx hxε
  have hb := hh x hx hxε
  simpa only [hgh x (abs_pos.mp hx)] using hb

private theorem iterDeriv_pow_formula (d e : ℕ) (x : ℝ) :
    iterDeriv d (fun t : ℝ => t ^ e) x =
      (e.descFactorial d : ℝ) * x ^ (e - d) := by
  simp [iterDeriv, ← iteratedDeriv_eq_iterate, iteratedDeriv_pow]

private theorem pow_mul_zpow_sin (x c u : ℝ) (hx : x ≠ 0)
    (a b : ℕ) (hba : b ≤ a) :
    x ^ a * (c * x ^ (-(b : ℕ) : ℤ) * Real.sin u) =
      c * x ^ (a - b) * Real.sin u := by
  rw [show x ^ a * (c * x ^ (-(b : ℕ) : ℤ) * Real.sin u) =
      c * (x ^ a * x ^ (-(b : ℕ) : ℤ)) * Real.sin u by ring,
    pow_mul_zpow_neg x hx a b hba]

theorem gap5 (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    IsBigOAtZero
      (fun x => iterDeriv m (f n) x - leadingTerm n m x)
      (fun x => |x| ^ (2 * (n - m) + 1)) := by
  classical
  let term : ℕ → ℝ → ℝ := fun i x =>
    (Nat.choose m i : ℝ) *
      iterDeriv (m - i) (fun t : ℝ => t ^ (2 * n)) x *
      iterDeriv i reciprocalSine x
  have hlower : ∀ i ∈ Finset.range m,
      IsBigOAtZero (term i) (fun x => |x| ^ (2 * (n - m) + 1)) := by
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    by_cases hi0 : i = 0
    · subst i
      refine bigO_congr_punctured ?_
        (bigO_monomial_sin
          ((2 * n).descFactorial m : ℝ) 0 (2 * n - m)
          (2 * (n - m) + 1) (by omega))
      intro x hx
      dsimp [term]
      rw [iterDeriv_pow_formula]
      simp [iterDeriv, reciprocalSine]
    · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      rcases gap4 i hi1 with ⟨a, ha⟩
      let P : ℝ :=
        (Nat.choose m i : ℝ) * ((2 * n).descFactorial (m - i) : ℝ)
      have hsum :
          IsBigOAtZero
            (fun x => ∑ k ∈ Finset.Ico 1 i,
              (P * a k) * x ^ (2 * n - m - k) *
                Real.sin (1 / x + (k : ℝ) * Real.pi / 2))
            (fun x => |x| ^ (2 * (n - m) + 1)) := by
        apply bigO_sum (Finset.Ico 1 i)
        intro k hk
        exact bigO_monomial_sin (P * a k)
          ((k : ℝ) * Real.pi / 2) (2 * n - m - k)
          (2 * (n - m) + 1) (by
            have hki := (Finset.mem_Ico.mp hk).2
            omega)
      have hlead :
          IsBigOAtZero
            (fun x => (P * (-1 : ℝ) ^ i) *
              x ^ (2 * n - m - i) *
                Real.sin (1 / x + (i : ℝ) * Real.pi / 2))
            (fun x => |x| ^ (2 * (n - m) + 1)) := by
        exact bigO_monomial_sin (P * (-1 : ℝ) ^ i)
          ((i : ℝ) * Real.pi / 2) (2 * n - m - i)
          (2 * (n - m) + 1) (by omega)
      refine bigO_congr_punctured ?_ (bigO_add hsum hlead)
      intro x hx
      dsimp [term]
      rw [iterDeriv_pow_formula, ha x hx]
      rw [show
        (Nat.choose m i : ℝ) *
              (((2 * n).descFactorial (m - i) : ℝ) *
                x ^ (2 * n - (m - i))) =
            P * x ^ (2 * n - (m - i)) by
          dsimp [P]
          ring]
      rw [mul_add, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        have hki := (Finset.mem_Ico.mp hk).2
        rw [show -((i : ℤ) + (k : ℤ)) =
            -((i + k : ℕ) : ℤ) by omega]
        rw [show
          P * x ^ (2 * n - (m - i)) *
                (a k * x ^ (-((i + k : ℕ) : ℤ)) *
                  Real.sin (1 / x + (k : ℝ) * Real.pi / 2)) =
            P * (x ^ (2 * n - (m - i)) *
              (a k * x ^ (-(i + k : ℕ) : ℤ) *
                Real.sin (1 / x + (k : ℝ) * Real.pi / 2))) by ring,
          pow_mul_zpow_sin x (a k)
            (1 / x + (k : ℝ) * Real.pi / 2) hx
            (2 * n - (m - i)) (i + k) (by omega)]
        have he :
            (2 * n - (m - i)) - (i + k) = 2 * n - m - k := by omega
        rw [he]
        ring
      · rw [neg_zpow_pow]
        rw [show
          P * x ^ (2 * n - (m - i)) *
                ((-1 : ℝ) ^ i * x ^ (-(2 * i : ℕ) : ℤ) *
                  Real.sin (1 / x + (i : ℝ) * Real.pi / 2)) =
            P * (-1 : ℝ) ^ i *
              (x ^ (2 * n - (m - i)) *
                (1 * x ^ (-(2 * i : ℕ) : ℤ) *
                  Real.sin (1 / x + (i : ℝ) * Real.pi / 2))) by ring,
          pow_mul_zpow_sin x 1
            (1 / x + (i : ℝ) * Real.pi / 2) hx
            (2 * n - (m - i)) (2 * i) (by omega)]
        simp only [one_mul]
        have he :
            (2 * n - (m - i)) - 2 * i = 2 * n - m - i := by omega
        rw [he]
        ring
  have htop :
      IsBigOAtZero (fun x => term m x - leadingTerm n m x)
        (fun x => |x| ^ (2 * (n - m) + 1)) := by
    rcases gap4 m hm with ⟨a, ha⟩
    have hsum :
        IsBigOAtZero
          (fun x => ∑ k ∈ Finset.Ico 1 m,
            a k * x ^ (2 * n - m - k) *
              Real.sin (1 / x + (k : ℝ) * Real.pi / 2))
          (fun x => |x| ^ (2 * (n - m) + 1)) := by
      apply bigO_sum (Finset.Ico 1 m)
      intro k hk
      exact bigO_monomial_sin (a k)
        ((k : ℝ) * Real.pi / 2) (2 * n - m - k)
        (2 * (n - m) + 1) (by
          have hkm := (Finset.mem_Ico.mp hk).2
          omega)
    refine bigO_congr_punctured ?_ hsum
    intro x hx
    dsimp [term]
    rw [iterDeriv_pow_formula, ha x hx]
    simp only [Nat.choose_self,
      Nat.cast_one, one_mul, Nat.sub_self, Nat.descFactorial_zero,
      Nat.cast_one]
    change
      x ^ (2 * n) *
          ((∑ k ∈ Finset.Ico 1 m,
              a k * x ^ (-(m + k : ℤ)) *
                Real.sin (1 / x + (k : ℝ) * Real.pi / 2)) +
            (-x ^ (-2 : ℤ)) ^ m *
              Real.sin (1 / x + (m : ℝ) * Real.pi / 2)) -
        leadingTerm n m x = _
    rw [mul_add, Finset.mul_sum]
    have hlead :
        x ^ (2 * n) *
            ((-x ^ (-2 : ℤ)) ^ m *
              Real.sin (1 / x + (m : ℝ) * Real.pi / 2)) =
          leadingTerm n m x := by
      rw [neg_zpow_pow]
      rw [show
        x ^ (2 * n) *
              ((-1 : ℝ) ^ m * x ^ (-(2 * m : ℕ) : ℤ) *
                Real.sin (1 / x + (m : ℝ) * Real.pi / 2)) =
          (-1 : ℝ) ^ m *
            (x ^ (2 * n) *
              (1 * x ^ (-(2 * m : ℕ) : ℤ) *
                Real.sin (1 / x + (m : ℝ) * Real.pi / 2))) by ring,
        pow_mul_zpow_sin x 1
          (1 / x + (m : ℝ) * Real.pi / 2) hx
          (2 * n) (2 * m) (by omega)]
      simp only [one_mul, leadingTerm]
      have he : 2 * n - 2 * m = 2 * (n - m) := by omega
      rw [he]
      ring
    rw [hlead, add_sub_cancel_right]
    apply Finset.sum_congr rfl
    intro k hk
    have hkm := (Finset.mem_Ico.mp hk).2
    have hez : -((m : ℤ) + (k : ℤ)) = -((m + k : ℕ) : ℤ) := by omega
    rw [hez, pow_mul_zpow_sin x (a k)
      (1 / x + (k : ℝ) * Real.pi / 2) hx
      (2 * n) (m + k) (by omega)]
    have he : 2 * n - (m + k) = 2 * n - m - k := by omega
    rw [he]
  refine bigO_congr_punctured ?_
    (bigO_add (bigO_sum (Finset.range m) term
      (fun x => |x| ^ (2 * (n - m) + 1))
      (fun i hi => hlower i hi)) htop)
  intro x hx
  rw [gap3 n m x hm hx]
  simp only [leibnizSum, term, Finset.sum_range_succ]
  ring

private theorem tendsto_pow_mul_sin_shift_zero (k : ℕ) (hk : 1 ≤ k) (c : ℝ) :
    Filter.Tendsto (fun x : ℝ => x ^ k * Real.sin (1 / x + c))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun x : ℝ => |x| ^ k)
    (Filter.Eventually.of_forall fun x => norm_nonneg _) ?_ ?_
  · exact Filter.Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
      exact mul_le_of_le_one_right (pow_nonneg (abs_nonneg x) k)
        (Real.abs_sin_le_one (1 / x + c))
  · have h :=
      (continuous_abs.continuousAt.tendsto.pow k).mono_left
        (show nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left)
    simpa [Nat.ne_of_gt hk] using h

private theorem tendsto_pow_mul_sin_inv_zero (k : ℕ) (hk : 1 ≤ k) :
    Filter.Tendsto (fun x : ℝ => x ^ k * Real.sin (1 / x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
  simpa using tendsto_pow_mul_sin_shift_zero k hk 0

private theorem hasDerivAt_f_zero (n : ℕ) (hn : 1 ≤ n) :
    HasDerivAt (f n) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hk : 1 ≤ 2 * n - 1 := by omega
  apply (tendsto_pow_mul_sin_inv_zero (2 * n - 1) hk).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  have he : 2 * n = (2 * n - 1) + 1 := by omega
  have hp : x ^ (2 * n) = x * x ^ (2 * n - 1) := by
    conv_lhs => rw [he]
    rw [pow_succ']
  simp [f, hx0, smul_eq_mul]
  rw [hp]
  field_simp [hx0]

theorem gap6 (n : ℕ) (hn : 1 ≤ n) :
    HasPuncturedLimit (fun x => (f n x - f n 0) / x) (deriv (f n) 0) := by
  have hd := hasDerivAt_f_zero n hn
  have hlim := hd.tendsto_slope
  rw [hd.deriv]
  change Filter.Tendsto _ _ _
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp [slope, f, hx0, smul_eq_mul]
  rw [div_eq_inv_mul]

theorem gap7 (n : ℕ) (hn : 1 ≤ n) :
    ∀ x : ℝ, x ≠ 0 →
      (f n x - f n 0) / x = x ^ (2 * n - 1) * Real.sin (1 / x) := by
  intro x hx
  simp [f, hx]
  have he : 2 * n = (2 * n - 1) + 1 := by omega
  have hp : x ^ (2 * n) = x * x ^ (2 * n - 1) := by
    conv_lhs => rw [he]
    rw [pow_succ']
  rw [hp]
  field_simp [hx]

theorem gap8 (n : ℕ) (hn : 1 ≤ n) :
    HasPuncturedLimit (fun x => x ^ (2 * n - 1) * Real.sin (1 / x)) 0 := by
  exact tendsto_pow_mul_sin_inv_zero (2 * n - 1) (by omega)

theorem gap9 (n : ℕ) (hn : 1 ≤ n) :
    deriv (f n) 0 = 0 := by
  exact (hasDerivAt_f_zero n hn).deriv

private theorem deriv_f_ne_zero (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : x ≠ 0) :
    deriv (f n) x =
      (2 * n : ℕ) * x ^ (2 * n - 1) * Real.sin (1 / x) -
        x ^ (2 * n - 2) * Real.sin (1 / x + Real.pi / 2) := by
  have hp : HasDerivAt (fun t : ℝ => t ^ (2 * n))
      ((2 * n : ℝ) * x ^ (2 * n - 1)) x := by
    simpa using (hasDerivAt_id x).pow (2 * n)
  have hi : HasDerivAt (fun t : ℝ => 1 / t) (-1 / x ^ 2) x := by
    convert (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx using 1 <;>
      simp [id] <;> ring
  have hs : HasDerivAt (fun t : ℝ => Real.sin (1 / t))
      (Real.cos (1 / x) * (-1 / x ^ 2)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sin (1 / x)).comp x hi
  have hprod := hp.mul hs
  rw [show f n = fun t : ℝ => t ^ (2 * n) * Real.sin (1 / t) by
    funext t
    by_cases ht : t = 0
    · subst t
      simp [f]
    · simp [f, ht]]
  change deriv ((fun t : ℝ => t ^ (2 * n)) *
    (fun t : ℝ => Real.sin (1 / t))) x = _
  rw [hprod.deriv, Real.sin_add_pi_div_two]
  push_cast
  have he : 2 * n = (2 * n - 2) + 2 := by omega
  have hpow : x ^ (2 * n) = x ^ 2 * x ^ (2 * n - 2) := by
    conv_lhs => rw [he, pow_add]
    ring
  rw [hpow]
  field_simp [hx]
  ring

private theorem hasDerivAt_deriv_f_zero (n : ℕ) (hn : 2 ≤ n) :
    HasDerivAt (deriv (f n)) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have h₁ := (tendsto_pow_mul_sin_inv_zero (2 * n - 2) (by omega)).const_mul
    (2 * n : ℝ)
  have h₂ := tendsto_pow_mul_sin_shift_zero (2 * n - 3) (by omega)
    (Real.pi / 2)
  have hlim : Filter.Tendsto
      (fun x => (2 * n : ℝ) * (x ^ (2 * n - 2) * Real.sin (1 / x)) -
        x ^ (2 * n - 3) * Real.sin (1 / x + Real.pi / 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using h₁.sub h₂
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp only [zero_add]
  rw [deriv_f_ne_zero n (by omega) x hx0, gap9 n (by omega)]
  simp [smul_eq_mul]
  have he₁ : 2 * n - 1 = (2 * n - 2) + 1 := by omega
  have he₂ : 2 * n - 2 = (2 * n - 3) + 1 := by omega
  have hp₁ : x ^ (2 * n - 1) = x * x ^ (2 * n - 2) := by
    conv_lhs => rw [he₁]
    rw [pow_succ']
  have hp₂ : x ^ (2 * n - 2) = x * x ^ (2 * n - 3) := by
    conv_lhs => rw [he₂]
    rw [pow_succ']
  rw [hp₁, hp₂]
  field_simp [hx0]

theorem gap10 (n : ℕ) (hn : 2 ≤ n) :
    HasPuncturedLimit (fun x => deriv (f n) x / x) (iterDeriv 2 (f n) 0) := by
  have hd := hasDerivAt_deriv_f_zero n hn
  rw [show iterDeriv 2 (f n) 0 = deriv (deriv (f n)) 0 by
    simp [iterDeriv, Function.iterate_succ_apply']]
  rw [hd.deriv]
  change Filter.Tendsto _ _ _
  apply hd.tendsto_slope.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp [slope, gap9 n (by omega), smul_eq_mul, div_eq_inv_mul]

theorem gap11 (n : ℕ) (hn : 2 ≤ n) :
    ∃ r : ℝ → ℝ,
      IsBigOAtZero r (fun x => |x| ^ (2 * n - 2)) ∧
      ∀ x : ℝ, x ≠ 0 →
        deriv (f n) x / x =
          -x ^ (2 * n - 3) * Real.sin (1 / x + Real.pi / 2) + r x := by
  let r : ℝ → ℝ :=
    fun x => (2 * n : ℕ) * x ^ (2 * n - 2) * Real.sin (1 / x)
  refine ⟨r, ?_, ?_⟩
  · refine ⟨(2 * n : ℝ), by positivity, 1, by norm_num, ?_⟩
    intro x hx0 hx1
    dsimp [r]
    have hc : (0 : ℝ) ≤ (2 * n : ℕ) := by positivity
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hc]
    have hs := Real.abs_sin_le_one (1 / x)
    have hp : 0 ≤ |x| ^ (2 * n - 2) := pow_nonneg (abs_nonneg x) _
    simpa [abs_abs, mul_assoc] using
      (mul_le_mul_of_nonneg_left hs ((mul_nonneg (by positivity) hp)))
  · intro x hx
    rw [deriv_f_ne_zero n (by omega) x hx]
    dsimp [r]
    have he₁ : 2 * n - 1 = (2 * n - 2) + 1 := by omega
    have he₂ : 2 * n - 2 = (2 * n - 3) + 1 := by omega
    have hp₁ : x ^ (2 * n - 1) = x * x ^ (2 * n - 2) := by
      conv_lhs => rw [he₁]
      rw [pow_succ']
    have hp₂ : x ^ (2 * n - 2) = x * x ^ (2 * n - 3) := by
      conv_lhs => rw [he₂]
      rw [pow_succ']
    rw [hp₁, hp₂]
    field_simp [hx]
    ring

private theorem tendsto_of_bigO_pow {r : ℝ → ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hr : IsBigOAtZero r (fun x => |x| ^ k)) :
    Filter.Tendsto r (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
  rcases hr with ⟨C, hC, ε, hε, hr⟩
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun x : ℝ => C * |x| ^ k)
    (Filter.Eventually.of_forall fun x => norm_nonneg _) ?_ ?_
  · have he : ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, |x| < ε := by
      have ht := (continuous_abs.continuousAt.tendsto.eventually
        (Iio_mem_nhds (show |(0 : ℝ)| < ε by simpa using hε)))
      exact ht.filter_mono inf_le_left
    filter_upwards [self_mem_nhdsWithin, he] with x hx hxε
    have hx0 : 0 < |x| := abs_pos.mpr (by simpa using hx)
    simpa [Real.norm_eq_abs] using hr x hx0 hxε
  · have hp :=
      (continuous_abs.continuousAt.tendsto.pow k).mono_left
        (show nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left)
    have hc : Filter.Tendsto (fun _ : ℝ => C)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds C) := tendsto_const_nhds
    have hmul := hc.mul hp
    simpa [Nat.ne_of_gt hk] using hmul

theorem gap12 (n : ℕ) (hn : 2 ≤ n) (r : ℝ → ℝ)
    (hr : IsBigOAtZero r (fun x => |x| ^ (2 * n - 2))) :
    HasPuncturedLimit
      (fun x => -x ^ (2 * n - 3) * Real.sin (1 / x + Real.pi / 2) + r x) 0 := by
  change Filter.Tendsto _ _ _
  simpa using (tendsto_pow_mul_sin_shift_zero (2 * n - 3) (by omega)
    (Real.pi / 2)).neg.add (tendsto_of_bigO_pow (by omega) hr)

theorem gap13 (n : ℕ) (hn : 2 ≤ n) :
    iterDeriv 2 (f n) 0 = 0 := by
  simpa [iterDeriv, Function.iterate_succ_apply'] using
    (hasDerivAt_deriv_f_zero n hn).deriv

private theorem bigO_div_x {g : ℝ → ℝ} {k : ℕ}
    (hg : IsBigOAtZero g (fun x => |x| ^ (k + 1))) :
    IsBigOAtZero (fun x => g x / x) (fun x => |x| ^ k) := by
  rcases hg with ⟨C, hC, ε, hε, hg⟩
  refine ⟨C, hC, ε, hε, ?_⟩
  intro x hx hxε
  have hx0 : x ≠ 0 := abs_pos.mp hx
  have hbound := hg x hx hxε
  have hbound' : |g x| ≤ C * |x| ^ (k + 1) := by
    simpa [abs_of_nonneg (pow_nonneg (abs_nonneg x) (k + 1))] using hbound
  change |g x / x| ≤ C * |(|x| ^ k)|
  rw [abs_div, abs_of_nonneg (pow_nonneg (abs_nonneg x) k)]
  have hp : |x| ^ (k + 1) = |x| ^ k * |x| := by rw [pow_succ]
  rw [hp] at hbound'
  calc
    |g x| / |x| ≤ (C * (|x| ^ k * |x|)) / |x| :=
      (div_le_div_iff_of_pos_right hx).2 hbound'
    _ = C * |x| ^ k := by field_simp

private theorem leading_div_tendsto_zero (n m : ℕ) (hm : m < n) :
    Filter.Tendsto (fun x => leadingTerm n m x / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
  have hk : 1 ≤ 2 * (n - m) - 1 := by omega
  have hlim := (tendsto_pow_mul_sin_shift_zero
    (2 * (n - m) - 1) hk ((m : ℝ) * Real.pi / 2)).const_mul
      ((-1 : ℝ) ^ m)
  have hlim' : Filter.Tendsto
      (fun x => (-1 : ℝ) ^ m *
        (x ^ (2 * (n - m) - 1) *
          Real.sin (1 / x + (m : ℝ) * Real.pi / 2)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using hlim
  apply hlim'.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp only [leadingTerm]
  have he : 2 * (n - m) = (2 * (n - m) - 1) + 1 := by omega
  have hp : x ^ (2 * (n - m)) = x * x ^ (2 * (n - m) - 1) := by
    conv_lhs => rw [he]
    rw [pow_succ']
  rw [hp]
  field_simp [hx0]

private theorem iterDeriv_f_zero_le (n m : ℕ) (hn : 1 ≤ n) (hm : m ≤ n) :
    iterDeriv m (f n) 0 = 0 := by
  induction m with
  | zero => simp [iterDeriv, f]
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        simpa [iterDeriv, Function.iterate_succ_apply'] using gap9 n hn
      · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
        have hmn : m < n := by omega
        let e : ℝ → ℝ :=
          fun x => iterDeriv m (f n) x - leadingTerm n m x
        have heO : IsBigOAtZero e
            (fun x => |x| ^ (2 * (n - m) + 1)) := gap5 n m hm1 (by omega)
        have hrO : IsBigOAtZero (fun x => e x / x)
            (fun x => |x| ^ (2 * (n - m))) := by
          exact bigO_div_x heO
        have hr0 := tendsto_of_bigO_pow (show 1 ≤ 2 * (n - m) by omega) hrO
        have hlead := leading_div_tendsto_zero n m hmn
        have hsum : Filter.Tendsto
            (fun x => leadingTerm n m x / x + e x / x)
            (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
          simpa using hlead.add hr0
        have hslope : Filter.Tendsto
            (fun x => x⁻¹ • (iterDeriv m (f n) (0 + x) -
              iterDeriv m (f n) 0))
            (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
          apply hsum.congr'
          filter_upwards [self_mem_nhdsWithin] with x hx
          have hx0 : x ≠ 0 := by simpa using hx
          rw [ih (by omega)]
          simp only [zero_add, sub_zero, smul_eq_mul]
          dsimp [e]
          rw [div_eq_inv_mul]
          ring
        have hd : HasDerivAt (iterDeriv m (f n)) 0 0 :=
          hasDerivAt_iff_tendsto_slope_zero.mpr hslope
        simpa [iterDeriv, Function.iterate_succ_apply'] using hd.deriv

theorem gap14 (n : ℕ) (hn : 1 ≤ n) :
    HasPuncturedLimit
      (fun x => iterDeriv (n - 1) (f n) x / x)
      (iterDeriv n (f n) 0) := by
  have hz := iterDeriv_f_zero_le n (n - 1) hn (by omega)
  have htarget := iterDeriv_f_zero_le n n hn le_rfl
  rw [htarget]
  have hm : n - 1 < n := by omega
  have hm1 : n = 1 ∨ 1 ≤ n - 1 := by omega
  rcases hm1 with rfl | hm1
  · change Filter.Tendsto _ _ _
    apply (tendsto_pow_mul_sin_inv_zero 1 (by omega)).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    simp [iterDeriv, f, hx0]
    field_simp [hx0]
  · let e : ℝ → ℝ :=
      fun x => iterDeriv (n - 1) (f n) x - leadingTerm n (n - 1) x
    have hsub : n - (n - 1) = 1 := by omega
    have heO : IsBigOAtZero e (fun x => |x| ^ 3) := by
      simpa [hsub] using gap5 n (n - 1) hm1 (by omega)
    have hrO : IsBigOAtZero (fun x => e x / x) (fun x => |x| ^ 2) :=
      bigO_div_x heO
    have hlim := (leading_div_tendsto_zero n (n - 1) hm).add
      (tendsto_of_bigO_pow (by omega) hrO)
    change Filter.Tendsto _ _ _
    have hlim' : Filter.Tendsto
        (fun x => leadingTerm n (n - 1) x / x + e x / x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
      simpa using hlim
    apply hlim'.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    dsimp [e]
    ring

theorem gap15 (n : ℕ) (hn : 1 ≤ n) :
    ∃ r : ℝ → ℝ,
      IsBigOAtZero r (fun x => |x| ^ 2) ∧
      ∀ x : ℝ, x ≠ 0 →
        iterDeriv (n - 1) (f n) x / x =
          (-1 : ℝ) ^ (n - 1) * x *
            Real.sin (1 / x + (n - 1 : ℕ) * Real.pi / 2) + r x := by
  let e : ℝ → ℝ :=
    fun x => iterDeriv (n - 1) (f n) x - leadingTerm n (n - 1) x
  let r : ℝ → ℝ := fun x => e x / x
  have hsub : n - (n - 1) = 1 := by omega
  have hm1 : n = 1 ∨ 1 ≤ n - 1 := by omega
  have heO : IsBigOAtZero e (fun x => |x| ^ 3) := by
    rcases hm1 with rfl | hm1
    · dsimp [e]
      simp [iterDeriv, f, leadingTerm, IsBigOAtZero]
      exact ⟨1, by norm_num, 1, by norm_num, by
        intro x hx hx1
        simp [hx]⟩
    · simpa [hsub] using gap5 n (n - 1) hm1 (by omega)
  refine ⟨r, ?_, ?_⟩
  · exact bigO_div_x heO
  · intro x hx
    dsimp [r, e, leadingTerm]
    simp only [hsub, Nat.mul_one, pow_two]
    field_simp [hx]
    ring

theorem gap16 (n : ℕ) (hn : 1 ≤ n) (r : ℝ → ℝ)
    (hr : IsBigOAtZero r (fun x => |x| ^ 2)) :
    HasPuncturedLimit
      (fun x => (-1 : ℝ) ^ (n - 1) * x *
        Real.sin (1 / x + (n - 1 : ℕ) * Real.pi / 2) + r x) 0 := by
  have hlead := (tendsto_pow_mul_sin_shift_zero 1 (by omega)
    ((n - 1 : ℕ) * Real.pi / 2)).const_mul ((-1 : ℝ) ^ (n - 1))
  have hr0 := tendsto_of_bigO_pow (by omega) hr
  change Filter.Tendsto _ _ _
  simpa [mul_assoc] using hlead.add hr0

theorem gap17 (n : ℕ) (hn : 1 ≤ n) :
    iterDeriv n (f n) 0 = 0 := by
  exact iterDeriv_f_zero_le n n hn le_rfl

theorem gap18 (n : ℕ) (hn : 1 ≤ n) :
    DifferentiableAt ℝ (iterDeriv n (f n)) 0 →
      HasPuncturedLimit
        (fun x => iterDeriv n (f n) x / x)
        (iterDeriv (n + 1) (f n) 0) := by
  intro hd
  have hder := hd.hasDerivAt
  rw [show iterDeriv (n + 1) (f n) 0 =
      deriv (iterDeriv n (f n)) 0 by
    simp [iterDeriv, Function.iterate_succ_apply']]
  apply hder.tendsto_slope.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp [slope, gap17 n hn, smul_eq_mul, div_eq_inv_mul]

theorem gap19 (n : ℕ) (hn : 1 ≤ n) :
    ∃ r : ℝ → ℝ,
      IsBigOAtZero r (fun _ => 1) ∧
      ∀ x : ℝ, x ≠ 0 →
        iterDeriv n (f n) x / x =
          (-1 : ℝ) ^ n / x *
            Real.sin (1 / x + (n : ℝ) * Real.pi / 2) + r x := by
  let e : ℝ → ℝ := fun x => iterDeriv n (f n) x - leadingTerm n n x
  let r : ℝ → ℝ := fun x => e x / x
  have heO : IsBigOAtZero e (fun x => |x| ^ 1) := by
    simpa using gap5 n n hn le_rfl
  refine ⟨r, ?_, ?_⟩
  · simpa using (bigO_div_x (k := 0) heO)
  · intro x hx
    dsimp [r, e, leadingTerm]
    simp only [Nat.sub_self, Nat.mul_zero, pow_zero]
    field_simp [hx]
    ring

theorem gap20 (n : ℕ) (hn : 1 ≤ n) :
    DifferentiableAt ℝ (iterDeriv n (f n)) 0 →
      ∃ L : ℝ, HasPuncturedLimit (fun x => iterDeriv n (f n) x / x) L := by
  intro hd
  exact ⟨iterDeriv (n + 1) (f n) 0, gap18 n hn hd⟩

theorem gap21 (n : ℕ) (hn : 1 ≤ n) (r : ℝ → ℝ)
    (hr : IsBigOAtZero r (fun _ => 1)) :
    ¬ ∃ L : ℝ, HasPuncturedLimit
      (fun x => (-1 : ℝ) ^ n / x *
        Real.sin (1 / x + (n : ℝ) * Real.pi / 2) + r x) L := by
  rintro ⟨L, hL⟩
  rcases hr with ⟨C, hC, ε, hε, hr⟩
  let s : ℝ := (-1 : ℝ) ^ n
  let phase : ℝ := (n : ℝ) * Real.pi / 2
  let d : ℕ → ℝ :=
    fun k => Real.pi / 2 + (k : ℝ) * (2 * Real.pi) - phase
  let x : ℕ → ℝ := fun k => 1 / d k
  let g : ℝ → ℝ := fun y =>
    s / y * Real.sin (1 / y + phase) + r y
  have hnat : Filter.Tendsto (fun k : ℕ => (k : ℝ))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hmul : Filter.Tendsto (fun k : ℕ => (2 * Real.pi) * (k : ℝ))
      Filter.atTop Filter.atTop :=
    hnat.const_mul_atTop (by positivity)
  have hd : Filter.Tendsto d Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro B
    have he := hmul.eventually
      (Filter.eventually_ge_atTop (B - (Real.pi / 2 - phase)))
    filter_upwards [he] with k hk
    dsimp [d]
    linarith
  have hx0 : Filter.Tendsto x Filter.atTop (nhds 0) := by
    simpa [x, Function.comp_def] using tendsto_inv_atTop_zero.comp hd
  have hdpos : ∀ᶠ k : ℕ in Filter.atTop, 0 < d k :=
    hd.eventually (Filter.eventually_gt_atTop 0)
  have hxwithin : Filter.Tendsto x Filter.atTop
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hx0, ?_⟩
    filter_upwards [hdpos] with k hk
    have hdk : d k ≠ 0 := ne_of_gt hk
    simp [x, hdk]
  have hgL : Filter.Tendsto (fun k => s * g (x k))
      Filter.atTop (nhds (s * L)) := by
    have hg := hL.comp hxwithin
    simpa [g, s, phase] using hg.const_mul s
  have hupper : ∀ᶠ k : ℕ in Filter.atTop,
      s * g (x k) < s * L + 1 :=
    hgL.eventually (Iio_mem_nhds (by linarith))
  have hxε : ∀ᶠ k : ℕ in Filter.atTop, |x k| < ε := by
    exact hx0.abs.eventually (Iio_mem_nhds (by simpa using hε))
  have hrbound : ∀ᶠ k : ℕ in Filter.atTop, |r (x k)| ≤ C := by
    filter_upwards [hdpos, hxε] with k hdk hxk
    have hxk0 : x k ≠ 0 := by
      simp [x, ne_of_gt hdk]
    have hxkpos : 0 < |x k| := abs_pos.mpr hxk0
    simpa using hr (x k) hxkpos hxk
  have hdlarge : ∀ᶠ k : ℕ in Filter.atTop,
      s * L + 1 + C < d k :=
    hd.eventually (Filter.eventually_gt_atTop (s * L + 1 + C))
  have hall : ∀ᶠ k : ℕ in Filter.atTop,
      0 < d k ∧ s * g (x k) < s * L + 1 ∧
        |r (x k)| ≤ C ∧ s * L + 1 + C < d k := by
    filter_upwards [hdpos, hupper, hrbound, hdlarge] with k hdk huk hrk hlarge
    exact ⟨hdk, huk, hrk, hlarge⟩
  rcases hall.exists with ⟨k, hdk, huk, hrk, hlarge⟩
  have hdk0 : d k ≠ 0 := ne_of_gt hdk
  have hinv : 1 / x k = d k := by
    simp [x, hdk0]
  have hang : d k + phase =
      Real.pi / 2 + (k : ℝ) * (2 * Real.pi) := by
    dsimp [d]
    ring
  have hsin : Real.sin (1 / x k + phase) = 1 := by
    rw [hinv, hang, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
  have hsabs : |s| = 1 := by simp [s]
  have hss : s * s = 1 := by
    nlinarith [sq_abs s]
  have hformula : s * g (x k) = d k + s * r (x k) := by
    dsimp [g]
    rw [hsin]
    have hinv' : (x k)⁻¹ = d k := by simpa [one_div] using hinv
    rw [div_eq_mul_inv, hinv']
    nlinarith
  have habsmul : |s * r (x k)| = |r (x k)| := by
    rw [abs_mul, hsabs, one_mul]
  have hrlower : -C ≤ s * r (x k) := by
    have hneg := neg_abs_le (s * r (x k))
    rw [habsmul] at hneg
    linarith
  rw [hformula] at huk
  linarith

theorem gap22 (n : ℕ) (hn : 1 ≤ n) :
    ¬ DifferentiableAt ℝ (iterDeriv n (f n)) 0 := by
  intro hd
  rcases gap19 n hn with ⟨r, hr, heq⟩
  rcases gap20 n hn hd with ⟨L, hL⟩
  apply gap21 n hn r hr
  refine ⟨L, ?_⟩
  apply hL.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  exact heq x hx0

private theorem differentiable_iterDeriv_lt (n q : ℕ) (hn : 1 ≤ n) (hq : q < n) :
    DifferentiableAt ℝ (iterDeriv q (f n)) 0 := by
  by_cases hq0 : q = 0
  · subst q
    simpa [iterDeriv] using (hasDerivAt_f_zero n hn).differentiableAt
  · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
    let e : ℝ → ℝ :=
      fun x => iterDeriv q (f n) x - leadingTerm n q x
    have heO : IsBigOAtZero e
        (fun x => |x| ^ (2 * (n - q) + 1)) := gap5 n q hq1 (by omega)
    have hrO : IsBigOAtZero (fun x => e x / x)
        (fun x => |x| ^ (2 * (n - q))) := bigO_div_x heO
    have hr0 := tendsto_of_bigO_pow (show 1 ≤ 2 * (n - q) by omega) hrO
    have hlead := leading_div_tendsto_zero n q hq
    have hsum : Filter.Tendsto
        (fun x => leadingTerm n q x / x + e x / x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
      simpa using hlead.add hr0
    have hslope : Filter.Tendsto
        (fun x => x⁻¹ •
          (iterDeriv q (f n) (0 + x) - iterDeriv q (f n) 0))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
      apply hsum.congr'
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := by simpa using hx
      rw [iterDeriv_f_zero_le n q hn (by omega)]
      simp only [zero_add, sub_zero, smul_eq_mul]
      dsimp [e]
      rw [div_eq_inv_mul]
      ring
    exact (hasDerivAt_iff_tendsto_slope_zero.mpr hslope).differentiableAt

theorem gap23 (n : ℕ) (hn : 1 ≤ n) :
    (∀ m : ℕ, 1 ≤ m → m ≤ n →
      DifferentiableAt ℝ (iterDeriv (m - 1) (f n)) 0) ∧
      ¬ DifferentiableAt ℝ (iterDeriv n (f n)) 0 := by
  refine ⟨?_, gap22 n hn⟩
  intro m hm hmn
  exact differentiable_iterDeriv_lt n (m - 1) hn (by omega)

end

end ProofGap.Exercise1224
