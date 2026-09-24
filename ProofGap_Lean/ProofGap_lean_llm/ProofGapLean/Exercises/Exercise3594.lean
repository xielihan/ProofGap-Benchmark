import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Choose.Sum

namespace ProofGap.Exercise3594

noncomputable section

abbrev Point2 := ℝ × ℝ

def logFunction (q : Point2) : ℝ :=
  Real.log (1 + q.1 + q.2)

def logSeriesTerm (k : ℕ) (t : ℝ) : ℝ :=
  if k = 0 then 0 else
    ((-1 : ℝ) ^ (k - 1) / (k : ℝ)) * t ^ k

def logSeries (t : ℝ) : ℝ :=
  ∑' k : ℕ, logSeriesTerm k t

def homogeneousTerm (k : ℕ) (q : Point2) : ℝ :=
  if k = 0 then 0 else
    ∑ m ∈ Finset.range (k + 1),
      ((-1 : ℝ) ^ (k - 1) / (k : ℝ)) *
        (Nat.choose k m : ℝ) * q.1 ^ m * q.2 ^ (k - m)

def homogeneousSeries (q : Point2) : ℝ :=
  ∑' k : ℕ, homogeneousTerm k q

def factorialHomogeneousTerm (k : ℕ) (q : Point2) : ℝ :=
  if k = 0 then 0 else
    ∑ m ∈ Finset.range (k + 1),
      ((-1 : ℝ) ^ (k - 1) * (Nat.factorial (k - 1) : ℝ) /
        ((Nat.factorial m : ℝ) * (Nat.factorial (k - m) : ℝ))) *
        q.1 ^ m * q.2 ^ (k - m)

def factorialHomogeneousSeries (q : Point2) : ℝ :=
  ∑' k : ℕ, factorialHomogeneousTerm k q

def doubleCoefficient (m n : ℕ) : ℝ :=
  if m + n = 0 then 0 else
    (-1 : ℝ) ^ (m + n - 1) * (Nat.factorial (m + n - 1) : ℝ) /
      ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))

def doubleSeriesTerm (q : Point2) (m n : ℕ) : ℝ :=
  doubleCoefficient m n * q.1 ^ m * q.2 ^ n

def doubleSeries (q : Point2) : ℝ :=
  ∑' m : ℕ, ∑' n : ℕ, doubleSeriesTerm q m n

private theorem logCoefficient_eq_factorial
    (k m : ℕ) (hk : k ≠ 0) (hm : m ≤ k) :
    ((-1 : ℝ) ^ (k - 1) / (k : ℝ)) * (Nat.choose k m : ℝ) =
      (-1 : ℝ) ^ (k - 1) * (Nat.factorial (k - 1) : ℝ) /
        ((Nat.factorial m : ℝ) * (Nat.factorial (k - m) : ℝ)) := by
  have hfacNat := Nat.choose_mul_factorial_mul_factorial hm
  have hfac :
      (Nat.choose k m : ℝ) * (Nat.factorial m : ℝ) *
          (Nat.factorial (k - m) : ℝ) = (Nat.factorial k : ℝ) := by
    simpa only [Nat.cast_mul] using
      congrArg (fun z : ℕ => (z : ℝ)) hfacNat
  have hkstep : k = (k - 1) + 1 := by omega
  have hkfacNat : Nat.factorial k = k * Nat.factorial (k - 1) := by
    calc
      Nat.factorial k = Nat.factorial ((k - 1) + 1) := by rw [← hkstep]
      _ = ((k - 1) + 1) * Nat.factorial (k - 1) :=
        Nat.factorial_succ (k - 1)
      _ = k * Nat.factorial (k - 1) := by rw [← hkstep]
  have hkfac :
      (Nat.factorial k : ℝ) =
        (k : ℝ) * (Nat.factorial (k - 1) : ℝ) := by
    simpa only [Nat.cast_mul] using
      congrArg (fun z : ℕ => (z : ℝ)) hkfacNat
  have hkR : (k : ℝ) ≠ 0 := by simp [hk]
  have hmR : (Nat.factorial m : ℝ) ≠ 0 := by positivity
  have hkmR : (Nat.factorial (k - m) : ℝ) ≠ 0 := by positivity
  have hchoose :
      (Nat.choose k m : ℝ) =
        (Nat.factorial k : ℝ) /
          ((Nat.factorial m : ℝ) * (Nat.factorial (k - m) : ℝ)) := by
    apply (eq_div_iff (mul_ne_zero hmR hkmR)).2
    simpa [mul_assoc] using hfac
  rw [hchoose, hkfac]
  field_simp [hkR, hmR, hkmR]

private def antidiagonalEquiv :
    (Sigma fun k : ℕ => Fin (k + 1)) ≃ ℕ × ℕ :=
  Equiv.ofBijective
    (fun z => (z.2.1, z.1 - z.2.1))
    (by
      constructor
      · rintro ⟨k, m⟩ ⟨l, n⟩ h
        have hfst : m.1 = n.1 := congrArg Prod.fst h
        have hsnd : k - m.1 = l - n.1 := congrArg Prod.snd h
        have hm : m.1 ≤ k := by omega
        have hn : n.1 ≤ l := by omega
        have hkl : k = l := by omega
        subst l
        have hmn : m = n := Fin.ext hfst
        subst n
        rfl
      · rintro ⟨m, n⟩
        refine ⟨⟨m + n, ⟨m, by omega⟩⟩, ?_⟩
        simp)

private def sigmaProdEquiv :
    (Sigma fun _ : ℕ => ℕ) ≃ ℕ × ℕ where
  toFun z := (z.1, z.2)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by
    rintro ⟨m, n⟩
    rfl
  right_inv := by
    rintro ⟨m, n⟩
    rfl

private theorem doubleSeriesFacts (x y : ℝ) (hxy : |x| + |y| < 1) :
    Summable (Function.uncurry (doubleSeriesTerm (x, y))) ∧
      doubleSeries (x, y) = factorialHomogeneousSeries (x, y) := by
  let r : ℝ := |x| + |y|
  let d : (Sigma fun k : ℕ => Fin (k + 1)) → ℝ := fun z =>
    doubleSeriesTerm (x, y) z.2.1 (z.1 - z.2.1)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hxy
  have hdegree :
      ∀ k : ℕ, (∑' i : Fin (k + 1), ‖d ⟨k, i⟩‖) ≤ r ^ k := by
    intro k
    rw [tsum_fintype]
    by_cases hk : k = 0
    · subst k
      simp [d, doubleSeriesTerm, doubleCoefficient, r]
    · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hkRpos : 0 < (k : ℝ) := by exact_mod_cast hkpos
      have heq :
          (∑ i : Fin (k + 1), ‖d ⟨k, i⟩‖) = r ^ k / (k : ℝ) := by
        rw [show (∑ i : Fin (k + 1), ‖d ⟨k, i⟩‖) =
            ∑ m ∈ Finset.range (k + 1),
              ((Nat.choose k m : ℝ) / (k : ℝ)) *
                |x| ^ m * |y| ^ (k - m) by
          rw [← Fin.sum_univ_eq_sum_range]
          apply Finset.sum_congr rfl
          intro i hi
          have hik : i.1 ≤ k := by omega
          have hsum : i.1 + (k - i.1) = k := Nat.add_sub_of_le hik
          have hc := logCoefficient_eq_factorial k i.1 hk hik
          have hcoeff :
              doubleCoefficient i.1 (k - i.1) =
                ((-1 : ℝ) ^ (k - 1) / (k : ℝ)) *
                  (Nat.choose k i.1 : ℝ) := by
            rw [doubleCoefficient, hsum, if_neg hk]
            exact hc.symm
          have hchoose0 : 0 ≤ (Nat.choose k i.1 : ℝ) := Nat.cast_nonneg _
          simp only [d, doubleSeriesTerm]
          rw [hcoeff]
          simp only [norm_mul, norm_div, norm_pow, Real.norm_eq_abs,
            abs_neg, abs_one, abs_of_pos hkRpos,
            abs_of_nonneg hchoose0]
          ring]
        have hbin :
            (∑ m ∈ Finset.range (k + 1),
                (Nat.choose k m : ℝ) * |x| ^ m * |y| ^ (k - m)) =
              r ^ k := by
          dsimp [r]
          rw [add_pow]
          apply Finset.sum_congr rfl
          intro m hm
          ring
        calc
          (∑ m ∈ Finset.range (k + 1),
              (Nat.choose k m : ℝ) / (k : ℝ) *
                |x| ^ m * |y| ^ (k - m)) =
              (1 / (k : ℝ)) *
                ∑ m ∈ Finset.range (k + 1),
                  (Nat.choose k m : ℝ) * |x| ^ m * |y| ^ (k - m) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m hm
            ring
          _ = r ^ k / (k : ℝ) := by
            rw [hbin]
            ring
      rw [heq]
      have hkcast : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
      exact div_le_self (pow_nonneg hr0 k) hkcast
  have hout :
      Summable (fun k : ℕ => ∑' i : Fin (k + 1), ‖d ⟨k, i⟩‖) := by
    have hgeom : Summable (fun k : ℕ => r ^ k) :=
      summable_geometric_of_norm_lt_one hr
    refine hgeom.of_norm_bounded ?_
    intro k
    calc
      ‖∑' i : Fin (k + 1), ‖d ⟨k, i⟩‖‖ =
          ∑' i : Fin (k + 1), ‖d ⟨k, i⟩‖ := by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
      _ ≤ r ^ k := hdegree k
  have hdnorm : Summable (fun z => ‖d z‖) := by
    refine (summable_sigma_of_nonneg
      (f := fun z => ‖d z‖) (fun z => norm_nonneg (d z))).2 ?_
    constructor
    · intro k
      exact (hasSum_fintype
        (fun i : Fin (k + 1) => ‖d ⟨k, i⟩‖)).summable
    · exact hout
  have hd : Summable d := hdnorm.of_norm
  have hdcomp :
      d = Function.uncurry (doubleSeriesTerm (x, y)) ∘
        antidiagonalEquiv := by
    funext z
    rfl
  have hnormcomp :
      (fun z => ‖d z‖) =
        (fun p => ‖Function.uncurry (doubleSeriesTerm (x, y)) p‖) ∘
          antidiagonalEquiv := by
    funext z
    rfl
  have hpnorm :
      Summable (fun p => ‖Function.uncurry (doubleSeriesTerm (x, y)) p‖) := by
    apply antidiagonalEquiv.summable_iff.mp
    rw [← hnormcomp]
    exact hdnorm
  have hp : Summable (Function.uncurry (doubleSeriesTerm (x, y))) :=
    hpnorm.of_norm
  refine ⟨hp, ?_⟩
  have hdiag : ∀ k : ℕ,
      (∑' i : Fin (k + 1), d ⟨k, i⟩) =
        factorialHomogeneousTerm k (x, y) := by
    intro k
    rw [tsum_fintype]
    by_cases hk : k = 0
    · subst k
      simp [d, doubleSeriesTerm, doubleCoefficient,
        factorialHomogeneousTerm]
    · rw [show (∑ i : Fin (k + 1), d ⟨k, i⟩) =
          ∑ m ∈ Finset.range (k + 1),
            ((-1 : ℝ) ^ (k - 1) * (Nat.factorial (k - 1) : ℝ) /
                ((Nat.factorial m : ℝ) *
                  (Nat.factorial (k - m) : ℝ))) *
              x ^ m * y ^ (k - m) by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i hi
        have hik : i.1 ≤ k := by omega
        have hsum : i.1 + (k - i.1) = k := Nat.add_sub_of_le hik
        simp only [d, doubleSeriesTerm]
        rw [doubleCoefficient, hsum, if_neg hk]]
      simp [factorialHomogeneousTerm, hk]
  calc
    doubleSeries (x, y) =
        ∑' p : ℕ × ℕ, Function.uncurry (doubleSeriesTerm (x, y)) p := by
      unfold doubleSeries
      exact hp.tsum_prod.symm
    _ = ∑' z : Sigma fun k : ℕ => Fin (k + 1), d z := by
      rw [hdcomp]
      exact (antidiagonalEquiv.tsum_eq
        (Function.uncurry (doubleSeriesTerm (x, y)))).symm
    _ = ∑' k : ℕ, ∑' i : Fin (k + 1), d ⟨k, i⟩ := hd.tsum_sigma
    _ = factorialHomogeneousSeries (x, y) := by
      unfold factorialHomogeneousSeries
      apply tsum_congr
      exact hdiag

theorem gap1 :
    ∀ x y : ℝ, logFunction (x, y) = Real.log (1 + x + y) := by
  intro x y
  rfl

theorem gap2 :
    ∀ x y : ℝ, |x + y| < 1 →
      Real.log (1 + x + y) = logSeries (x + y) := by
  intro x y hxy
  have hneg : |-(x + y)| < 1 := by
    simpa only [abs_neg] using hxy
  have hs0 :
      HasSum (fun b : ℕ =>
        -((-(x + y)) ^ (b + 1) / ((b : ℝ) + 1)))
        (Real.log (1 + x + y)) := by
    simpa only [neg_neg, sub_neg_eq_add, add_assoc] using
      (Real.hasSum_pow_div_log_of_abs_lt_one
        (x := -(x + y)) hneg).neg
  have hfull :
      HasSum (fun k : ℕ => -((-(x + y)) ^ k / (k : ℝ)))
        (Real.log (1 + x + y)) := by
    have htail :
        HasSum
          (fun b : ℕ =>
            (fun k : ℕ => -((-(x + y)) ^ k / (k : ℝ))) (b + 1))
          (Real.log (1 + x + y)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hs0
    simpa using
      (hasSum_nat_add_iff
        (f := fun k : ℕ => -((-(x + y)) ^ k / (k : ℝ))) 1).mp htail
  have hterm :
      (fun k : ℕ => logSeriesTerm k (x + y)) =
        (fun k : ℕ => -((-(x + y)) ^ k / (k : ℝ))) := by
    funext k
    cases k with
    | zero =>
        simp [logSeriesTerm]
    | succ j =>
        simp only [logSeriesTerm, Nat.succ_ne_zero, if_false,
          Nat.succ_sub_one]
        have hnegmul : -(x + y) = (-1 : ℝ) * (x + y) := by
          ring
        have hpow :
            (-1 : ℝ) ^ (j + 1) = -((-1 : ℝ) ^ j) := by
          rw [pow_succ]
          ring
        rw [hnegmul, mul_pow, hpow]
        ring
  have hs :
      HasSum (fun k : ℕ => logSeriesTerm k (x + y))
        (Real.log (1 + x + y)) := by
    rw [hterm]
    exact hfull
  unfold logSeries
  exact hs.tsum_eq.symm

theorem gap3 :
    ∀ x y : ℝ,
      logSeries (x + y) = homogeneousSeries (x, y) := by
  intro x y
  unfold logSeries homogeneousSeries
  apply tsum_congr
  intro k
  by_cases hk : k = 0
  · simp [logSeriesTerm, homogeneousTerm, hk]
  · simp only [logSeriesTerm, homogeneousTerm, hk, if_false]
    rw [add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    ring

theorem gap4 :
    ∀ x y : ℝ, |x + y| < 1 →
      logFunction (x, y) = homogeneousSeries (x, y) := by
  intro x y hxy
  calc
    logFunction (x, y) = Real.log (1 + x + y) := gap1 x y
    _ = logSeries (x + y) := gap2 x y hxy
    _ = homogeneousSeries (x, y) := gap3 x y

theorem gap5 :
    ∀ x y : ℝ, |x + y| < 1 →
      logFunction (x, y) = factorialHomogeneousSeries (x, y) := by
  intro x y hxy
  calc
    logFunction (x, y) = homogeneousSeries (x, y) := gap4 x y hxy
    _ = factorialHomogeneousSeries (x, y) := by
      unfold homogeneousSeries factorialHomogeneousSeries
      apply tsum_congr
      intro k
      by_cases hk : k = 0
      · simp [homogeneousTerm, factorialHomogeneousTerm, hk]
      · simp only [homogeneousTerm, factorialHomogeneousTerm, hk, if_false]
        apply Finset.sum_congr rfl
        intro m hm
        have hmk : m ≤ k := by
          have := Finset.mem_range.mp hm
          omega
        rw [logCoefficient_eq_factorial k m hk hmk]

theorem gap6 :
    ∀ x y : ℝ, |x| + |y| < 1 →
      logFunction (x, y) = doubleSeries (x, y) := by
  intro x y hxy
  have hf := doubleSeriesFacts x y hxy
  have hsum : |x + y| < 1 := by
    calc
      |x + y| ≤ |x| + |y| := abs_add_le x y
      _ < 1 := hxy
  calc
    logFunction (x, y) = factorialHomogeneousSeries (x, y) :=
      gap5 x y hsum
    _ = doubleSeries (x, y) := hf.2.symm

theorem gap7 :
    doubleCoefficient 0 0 = 0 := by
  simp [doubleCoefficient]

theorem gap8 :
    ∀ x y : ℝ, |x| + |y| < 1 → |x + y| < 1 := by
  intro x y hxy
  calc
    |x + y| ≤ |x| + |y| := abs_add_le x y
    _ < 1 := hxy

theorem gap9 :
    ∀ x y : ℝ, |x| + |y| < 1 →
      (∀ m : ℕ, Summable (fun n : ℕ => doubleSeriesTerm (x, y) m n)) ∧
        Summable (fun m : ℕ => ∑' n : ℕ, doubleSeriesTerm (x, y) m n) := by
  set_option maxHeartbeats 2000000 in
    intro x y hxy
    have hp := (doubleSeriesFacts x y hxy).1
    have hrows :
        ∀ m : ℕ, Summable (fun n : ℕ => doubleSeriesTerm (x, y) m n) := by
      intro m
      have hinj : Function.Injective (fun n : ℕ => (m, n)) := by
        intro a b hab
        exact Prod.mk.inj hab |>.2
      have hc := hp.comp_injective hinj
      simpa [Function.comp_def] using hc
    have hsigma :
        Summable (fun z : Sigma fun _ : ℕ => ℕ =>
          doubleSeriesTerm (x, y) z.1 z.2) := by
      have hc :
          Summable
            (Function.uncurry (doubleSeriesTerm (x, y)) ∘ sigmaProdEquiv) :=
        sigmaProdEquiv.summable_iff.mpr hp
      simpa [Function.comp_def] using hc
    refine ⟨hrows, ?_⟩
    simpa using hsigma.sigma

end

end ProofGap.Exercise3594
