import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fin.Rev
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2874_2

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def reciprocalExponential (a x : ℝ) : ℝ :=
  Real.exp (a / x)

def ValidIncrement (x h : ℝ) : Prop :=
  x ≠ 0 ∧ x + h ≠ 0

def SmallIncrement (x h : ℝ) : Prop :=
  x ≠ 0 ∧ |h| < |x|

def incrementExponent (a x h : ℝ) : ℝ :=
  -(a * h) / (x * (x + h))

def reciprocalExponentTerm (a x h : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * a * h ^ (n + 1) / x ^ (n + 2)

def outerExponentialTerm (a x h : ℝ) (m : ℕ) : ℝ :=
  let q := m + 1
  (∑' n, reciprocalExponentTerm a x h n) ^ q / (Nat.factorial q : ℝ)

def doubleSeriesTerm (a x h : ℝ) (m s : ℕ) : ℝ :=
  let q := m + 1
  (-1 : ℝ) ^ (q + s) * a ^ q /
      ((Nat.factorial q : ℝ) * x ^ q) *
    (h / x) ^ (q + s) * (Nat.choose (s + q - 1) s : ℝ)

def normalizedCoefficient (a x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / x ^ (2 * n) *
    ∑ s ∈ Finset.range n,
      (Nat.choose (n - 1) s : ℝ) *
        (x ^ s * a ^ (n - s) / (Nat.factorial (n - s) : ℝ))

def derivativeCoefficient (a x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / x ^ (2 * n) *
    ∑ s ∈ Finset.range n,
      (Nat.factorial s : ℝ) * (Nat.choose n s : ℝ) *
        (Nat.choose (n - 1) s : ℝ) * a ^ (n - s) * x ^ s

def regroupedIncrementTerm (a x h : ℝ) (n : ℕ) : ℝ :=
  let q := n + 1
  normalizedCoefficient a x q * h ^ q

def derivativeIncrementTerm (a x h : ℝ) (n : ℕ) : ℝ :=
  let q := n + 1
  derivativeCoefficient a x q / (Nat.factorial q : ℝ) * h ^ q

private theorem smallIncrement_valid {x h : ℝ} (hsmall : SmallIncrement x h) :
    ValidIncrement x h := by
  refine ⟨hsmall.1, ?_⟩
  intro hzero
  have : |h| = |x| := by
    rw [show h = -x by linarith, abs_neg]
  linarith [hsmall.2]

private theorem reciprocalExponent_hasSum (a x h : ℝ)
    (hsmall : SmallIncrement x h) :
    HasSum (reciprocalExponentTerm a x h) (incrementExponent a x h) := by
  have hx : x ≠ 0 := hsmall.1
  have hxh : x + h ≠ 0 := (smallIncrement_valid hsmall).2
  let r : ℝ := -h / x
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_div, abs_neg]
    exact (div_lt_one (abs_pos.mpr hx)).2 hsmall.2
  have hgeom := hasSum_geometric_of_norm_lt_one hr
  have hs := hgeom.mul_left (-a * h / x ^ 2)
  convert hs using 1
  · funext n
    unfold reciprocalExponentTerm
    dsimp [r]
    rw [div_pow, neg_pow, pow_succ]
    field_simp [hx]
    ring
  · unfold incrementExponent
    dsimp [r]
    field_simp [hx, hxh]
    ring

private theorem tsum_reciprocalExponentTerm (a x h : ℝ)
    (hsmall : SmallIncrement x h) :
    (∑' n, reciprocalExponentTerm a x h n) = incrementExponent a x h :=
  (reciprocalExponent_hasSum a x h hsmall).tsum_eq

private theorem outerExponentialTerm_eq_tsum_doubleSeriesTerm
    (a x h : ℝ) (m : ℕ) (hsmall : SmallIncrement x h) :
    outerExponentialTerm a x h m =
      ∑' s, doubleSeriesTerm a x h m s := by
  have hx : x ≠ 0 := hsmall.1
  let q : ℕ := m + 1
  let r : ℝ := -h / x
  let C : ℝ := (-a * h / x ^ 2) ^ q / (Nat.factorial q : ℝ)
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_div, abs_neg]
    exact (div_lt_one (abs_pos.mpr hx)).2 hsmall.2
  have hnegative := hasSum_choose_mul_geometric_of_norm_lt_one m hr
  have hs := hnegative.mul_left C
  have hterm :
      (fun s : ℕ => C * (((s + m).choose m : ℝ) * r ^ s)) =
        doubleSeriesTerm a x h m := by
    funext s
    have htop : s + q - 1 = s + m := by simp [q]
    have hchoose : (s + m).choose s = (s + m).choose m :=
      Nat.choose_symm_add
    unfold doubleSeriesTerm
    dsimp only
    rw [show m + 1 = q by rfl, htop, hchoose]
    dsimp [C, r]
    rw [div_pow, div_pow, mul_pow, neg_pow, neg_pow]
    simp only [pow_add, one_pow, mul_one]
    rw [div_pow, div_pow, neg_pow]
    have hxpow : (x ^ 2) ^ q = x ^ q * x ^ q := by
      rw [pow_two, mul_pow]
    rw [hxpow]
    field_simp [hx]
    rw [neg_pow]
    ring
  have hsum :
      C * (1 / (1 - r) ^ (m + 1)) = outerExponentialTerm a x h m := by
    have hu :
        incrementExponent a x h =
          (-a * h / x ^ 2) / (1 + h / x) := by
      unfold incrementExponent
      have hxh := (smallIncrement_valid hsmall).2
      field_simp [hx, hxh]
    unfold outerExponentialTerm
    rw [tsum_reciprocalExponentTerm a x h hsmall, hu]
    change C * (1 / (1 - r) ^ q) =
      ((-a * h / x ^ 2) / (1 + h / x)) ^ q /
        (Nat.factorial q : ℝ)
    dsimp [C, r]
    simp only [div_eq_mul_inv, one_div, mul_pow, inv_pow]
    ring
  rw [← hterm]
  exact (hs.tsum_eq.trans hsum).symm

private theorem normalizedCoefficient_eq_derivativeCoefficient_div_factorial
    (a x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    normalizedCoefficient a x n =
      derivativeCoefficient a x n / (Nat.factorial n : ℝ) := by
  have hterm (s : ℕ) (hs : s ∈ Finset.range n) :
      (Nat.choose (n - 1) s : ℝ) *
          (x ^ s * a ^ (n - s) / (Nat.factorial (n - s) : ℝ)) =
        ((Nat.factorial s : ℝ) * (Nat.choose n s : ℝ) *
            (Nat.choose (n - 1) s : ℝ) * a ^ (n - s) * x ^ s) /
          (Nat.factorial n : ℝ) := by
    have hsn : s ≤ n := (Finset.mem_range.mp hs).le.trans (Nat.le_refl n)
    have hfacNat := Nat.choose_mul_factorial_mul_factorial hsn
    have hfacReal :
        (Nat.choose n s : ℝ) * (Nat.factorial s : ℝ) *
            (Nat.factorial (n - s) : ℝ) =
          (Nat.factorial n : ℝ) := by
      exact_mod_cast hfacNat
    field_simp
    rw [← hfacReal]
    ring
  have hsum :
      (∑ s ∈ Finset.range n,
        (Nat.choose (n - 1) s : ℝ) *
          (x ^ s * a ^ (n - s) / (Nat.factorial (n - s) : ℝ))) =
        (∑ s ∈ Finset.range n,
          (Nat.factorial s : ℝ) * (Nat.choose n s : ℝ) *
            (Nat.choose (n - 1) s : ℝ) * a ^ (n - s) * x ^ s) /
          (Nat.factorial n : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s hs
    exact hterm s hs
  unfold normalizedCoefficient derivativeCoefficient
  rw [hsum]
  ring

private theorem norm_doubleSeriesTerm_eq
    (a x h : ℝ) (m s : ℕ) (hx : x ≠ 0) :
    let q := m + 1
    let r := |h / x|
    let K := |a| ^ q / ((Nat.factorial q : ℝ) * |x| ^ q) * r ^ q
    ‖doubleSeriesTerm a x h m s‖ =
      K * ((s + m).choose m : ℝ) * r ^ s := by
  dsimp only
  unfold doubleSeriesTerm
  dsimp only
  have htop : s + (m + 1) - 1 = s + m := by omega
  rw [htop, Nat.choose_symm_add]
  have hfacpos : 0 < (Nat.factorial (m + 1) : ℝ) := by positivity
  have hchoose : 0 ≤ (Nat.choose (s + m) m : ℝ) := by positivity
  simp only [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_neg,
    abs_one, one_pow, abs_of_pos hfacpos, abs_of_nonneg hchoose]
  rw [pow_add]
  ring

private theorem summable_norm_doubleSeriesTerm_prod
    (a x h : ℝ) (hsmall : SmallIncrement x h) :
    Summable (fun p : ℕ × ℕ => ‖doubleSeriesTerm a x h p.1 p.2‖) := by
  have hx : x ≠ 0 := hsmall.1
  let r : ℝ := |h / x|
  let B : ℝ := |a| * r / |x| / (1 - r)
  have hxabs : 0 < |x| := abs_pos.mpr hx
  have hr0 : 0 ≤ r := by simp [r]
  have hr1 : r < 1 := by
    dsimp [r]
    rw [abs_div]
    exact (div_lt_one hxabs).2 hsmall.2
  have hrnorm : ‖r‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hinner (m : ℕ) :
      Summable (fun s : ℕ => ‖doubleSeriesTerm a x h m s‖) := by
    let q : ℕ := m + 1
    let K : ℝ := |a| ^ q / ((Nat.factorial q : ℝ) * |x| ^ q) * r ^ q
    have hbase := (summable_choose_mul_geometric_of_norm_lt_one m hrnorm).mul_left K
    apply hbase.congr
    intro s
    simpa [K, q, r, mul_assoc] using
      (norm_doubleSeriesTerm_eq a x h m s hx).symm
  have hinnerSum (m : ℕ) :
      (∑' s : ℕ, ‖doubleSeriesTerm a x h m s‖) =
        B ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) := by
    let q : ℕ := m + 1
    let K : ℝ := |a| ^ q / ((Nat.factorial q : ℝ) * |x| ^ q) * r ^ q
    have hbase := (hasSum_choose_mul_geometric_of_norm_lt_one m hrnorm).mul_left K
    calc
      (∑' s : ℕ, ‖doubleSeriesTerm a x h m s‖) =
          ∑' s : ℕ, K * (((s + m).choose m : ℝ) * r ^ s) := by
        apply tsum_congr
        intro s
        simpa [K, q, r, mul_assoc] using
          norm_doubleSeriesTerm_eq a x h m s hx
      _ = K * (1 / (1 - r) ^ (m + 1)) := hbase.tsum_eq
      _ = B ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) := by
        change
          (|a| ^ q / ((Nat.factorial q : ℝ) * |x| ^ q) * r ^ q) *
              (1 / (1 - r) ^ q) =
            (|a| * r / |x| / (1 - r)) ^ q /
              (Nat.factorial q : ℝ)
        rw [div_pow, div_pow, mul_pow]
        ring
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
  refine ⟨hinner, ?_⟩
  have htail :
      Summable (fun m : ℕ =>
        B ^ (m + 1) / (Nat.factorial (m + 1) : ℝ)) := by
    exact (summable_nat_add_iff 1).2 (Real.summable_pow_div_factorial B)
  exact htail.congr (fun m => by simpa using (hinnerSum m).symm)

private def antidiagonalEquiv :
    (Sigma fun n : ℕ => Fin (n + 1)) ≃ ℕ × ℕ :=
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

private theorem sum_double_antidiagonal_eq_regrouped
    (a x h : ℝ) (n : ℕ) (hx : x ≠ 0) :
    (∑ i : Fin (n + 1), doubleSeriesTerm a x h i (n - i)) =
      regroupedIncrementTerm a x h n := by
  rw [← Equiv.sum_comp Fin.revPerm]
  unfold regroupedIncrementTerm normalizedCoefficient
  dsimp only
  rw [Finset.mul_sum, Finset.sum_mul, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hiv : (i : ℕ) ≤ n := by omega
  have hrev : ((Fin.rev i : Fin (n + 1)) : ℕ) = n - i := by
    simpa using congrArg Fin.val (Fin.last_sub i).symm
  rw [show Fin.revPerm i = Fin.rev i by rfl, hrev]
  unfold doubleSeriesTerm
  dsimp only
  have hs : n - (n - (i : ℕ)) = (i : ℕ) := by omega
  have hq : n - (i : ℕ) + 1 = n + 1 - (i : ℕ) := by omega
  have htotal : n + 1 - (i : ℕ) + (i : ℕ) = n + 1 := by omega
  have htop : (i : ℕ) + (n + 1 - (i : ℕ)) - 1 = n := by omega
  rw [hs, hq, htotal, htop, show n + 1 - 1 = n by omega]
  rw [div_pow]
  field_simp [hx]
  rw [pow_add]
  have hxp :
      x ^ (n + 1 - (i : ℕ)) * x ^ (n + 1) * x ^ (i : ℕ) =
        x ^ (2 * (n + 1)) := by
    calc
      x ^ (n + 1 - (i : ℕ)) * x ^ (n + 1) * x ^ (i : ℕ) =
          x ^ ((n + 1 - (i : ℕ)) + (n + 1)) * x ^ (i : ℕ) := by
        exact congrArg (fun z : ℝ => z * x ^ (i : ℕ))
          (pow_add x (n + 1 - (i : ℕ)) (n + 1)).symm
      _ = x ^ ((n + 1 - (i : ℕ)) + (n + 1) + (i : ℕ)) := by
        exact (pow_add x ((n + 1 - (i : ℕ)) + (n + 1)) (i : ℕ)).symm
      _ = x ^ (2 * (n + 1)) := by congr 1 <;> omega
  rw [← hxp]
  ring

private theorem regroupedIncrementTerm_eq_derivativeIncrementTerm
    (a x h : ℝ) (n : ℕ) :
    regroupedIncrementTerm a x h n = derivativeIncrementTerm a x h n := by
  unfold regroupedIncrementTerm derivativeIncrementTerm
  dsimp only
  rw [normalizedCoefficient_eq_derivativeCoefficient_div_factorial
    a x (n + 1) (by omega)]

private theorem summable_derivativeIncrementTerm
    (a x h : ℝ) (hsmall : SmallIncrement x h) :
    Summable (derivativeIncrementTerm a x h) := by
  have hx : x ≠ 0 := hsmall.1
  have hnorm := summable_norm_doubleSeriesTerm_prod a x h hsmall
  let d : (Sigma fun n : ℕ => Fin (n + 1)) → ℝ := fun z =>
    doubleSeriesTerm a x h z.2 (z.1 - z.2)
  have hnormcomp :
      (fun z => ‖d z‖) =
        (fun p => ‖Function.uncurry (doubleSeriesTerm a x h) p‖) ∘
          antidiagonalEquiv := by
    funext z
    rfl
  have hdnorm : Summable (fun z => ‖d z‖) := by
    rw [hnormcomp]
    exact antidiagonalEquiv.summable_iff.mpr hnorm
  have hd : Summable d := hdnorm.of_norm
  have hregroup : Summable (regroupedIncrementTerm a x h) := by
    have hsigma := hd.sigma
    apply hsigma.congr
    intro n
    rw [tsum_fintype]
    change (∑ i : Fin (n + 1),
      doubleSeriesTerm a x h i (n - i)) = _
    exact sum_double_antidiagonal_eq_regrouped a x h n hx
  exact hregroup.congr (regroupedIncrementTerm_eq_derivativeIncrementTerm a x h)

theorem gap1
    (f : ℝ → ℝ) (a : ℝ) (hf : ∀ x, x ≠ 0 → f x = reciprocalExponential a x) :
    ∃ c : ℝ, c = a ∧ ∀ x h : ℝ, ValidIncrement x h →
      f (x + h) - f x =
        Real.exp (a / (x + h)) - Real.exp (c / x) := by
  refine ⟨a, rfl, ?_⟩
  intro x h hvalid
  rw [hf (x + h) hvalid.2, hf x hvalid.1]
  rfl

theorem gap2
    (f : ℝ → ℝ) (a : ℝ) (hf : ∀ x, x ≠ 0 → f x = reciprocalExponential a x)
    (hincrement :
      ∃ c : ℝ, c = a ∧ ∀ x h : ℝ, ValidIncrement x h →
        f (x + h) - f x =
          Real.exp (a / (x + h)) - Real.exp (c / x)) :
    ∃ c : ℝ, c = a ∧ ∀ x h : ℝ, ValidIncrement x h →
      Real.exp (a / (x + h)) - Real.exp (c / x) =
        Real.exp (a / x) * (Real.exp (incrementExponent a x h) - 1) := by
  refine ⟨a, rfl, ?_⟩
  intro x h hvalid
  have hexponent :
      a / (x + h) = a / x + incrementExponent a x h := by
    unfold incrementExponent
    field_simp [hvalid.1, hvalid.2]
    ring
  rw [hexponent, Real.exp_add]
  ring

theorem gap3
    (f : ℝ → ℝ) (a : ℝ) (hf : ∀ x, x ≠ 0 → f x = reciprocalExponential a x)
    (hfactor :
      ∃ c : ℝ, c = a ∧ ∀ x h : ℝ, ValidIncrement x h →
        Real.exp (a / (x + h)) - Real.exp (c / x) =
          Real.exp (a / x) * (Real.exp (incrementExponent a x h) - 1)) :
    ∀ x h : ℝ, ValidIncrement x h →
      Real.exp (a / x) * (Real.exp (incrementExponent a x h) - 1) =
        Real.exp (a / x) *
          (Real.exp ((-(a * h) / x ^ 2) / (1 + h / x)) - 1) := by
  intro x h hvalid
  congr 3
  unfold incrementExponent
  field_simp [hvalid.1, hvalid.2]

theorem gap4
    (f : ℝ → ℝ) (a : ℝ) (hf : ∀ x, x ≠ 0 → f x = reciprocalExponential a x)
    (hincrement :
      ∃ c : ℝ, c = a ∧ ∀ x h : ℝ, ValidIncrement x h →
        f (x + h) - f x =
          Real.exp (a / (x + h)) - Real.exp (c / x))
    (hfactor :
      ∃ c : ℝ, c = a ∧ ∀ x h : ℝ, ValidIncrement x h →
        Real.exp (a / (x + h)) - Real.exp (c / x) =
          Real.exp (a / x) * (Real.exp (incrementExponent a x h) - 1))
    (hrewrite :
      ∀ x h : ℝ, ValidIncrement x h →
        Real.exp (a / x) * (Real.exp (incrementExponent a x h) - 1) =
          Real.exp (a / x) *
            (Real.exp ((-(a * h) / x ^ 2) / (1 + h / x)) - 1)) :
    ∀ x h : ℝ, ValidIncrement x h →
      f (x + h) - f x =
        Real.exp (a / x) * (Real.exp (incrementExponent a x h) - 1) := by
  rcases hincrement with ⟨c, hc, hincrement⟩
  subst c
  rcases hfactor with ⟨c, hc, hfactor⟩
  subst c
  intro x h hvalid
  rw [hincrement x h hvalid, hfactor x h hvalid]

theorem gap5
    (f : ℝ → ℝ) (a : ℝ) (hf : ∀ x, x ≠ 0 → f x = reciprocalExponential a x)
    (hfactor :
      ∀ x h : ℝ, ValidIncrement x h →
        f (x + h) - f x =
          Real.exp (a / x) * (Real.exp (incrementExponent a x h) - 1)) :
    ∀ x h : ℝ, SmallIncrement x h →
      f (x + h) - f x =
        Real.exp (a / x) *
          (Real.exp (∑' n, reciprocalExponentTerm a x h n) - 1) := by
  intro x h hsmall
  rw [hfactor x h (smallIncrement_valid hsmall),
    tsum_reciprocalExponentTerm a x h hsmall]

theorem gap6
    (f : ℝ → ℝ) (a : ℝ) (hf : ∀ x, x ≠ 0 → f x = reciprocalExponential a x)
    (hinner :
      ∀ x h : ℝ, SmallIncrement x h →
        f (x + h) - f x =
          Real.exp (a / x) *
            (Real.exp (∑' n, reciprocalExponentTerm a x h n) - 1)) :
    ∀ x h : ℝ, SmallIncrement x h →
      f (x + h) - f x =
        Real.exp (a / x) * (∑' m, outerExponentialTerm a x h m) := by
  intro x h hsmall
  rw [hinner x h hsmall]
  congr 1
  let u : ℝ := ∑' n, reciprocalExponentTerm a x h n
  have hexp : HasSum (fun n : ℕ => u ^ n / (Nat.factorial n : ℝ))
      (Real.exp u) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp u
  have htail := (hasSum_nat_add_iff' 1).2 hexp
  exact (by
    simpa [u, outerExponentialTerm] using htail.tsum_eq.symm)

theorem gap7
    (f : ℝ → ℝ) (a : ℝ) (hf : ∀ x, x ≠ 0 → f x = reciprocalExponential a x)
    (houter :
      ∀ x h : ℝ, SmallIncrement x h →
        f (x + h) - f x =
          Real.exp (a / x) * (∑' m, outerExponentialTerm a x h m)) :
    ∀ x h : ℝ, SmallIncrement x h →
      f (x + h) - f x =
        Real.exp (a / x) * (∑' m, ∑' s, doubleSeriesTerm a x h m s) := by
  intro x h hsmall
  rw [houter x h hsmall]
  congr 1
  apply tsum_congr
  intro m
  exact outerExponentialTerm_eq_tsum_doubleSeriesTerm a x h m hsmall

theorem gap8
    (f : ℝ → ℝ) (a : ℝ) (hf : ∀ x, x ≠ 0 → f x = reciprocalExponential a x)
    (hdouble :
      ∀ x h : ℝ, SmallIncrement x h →
        f (x + h) - f x =
          Real.exp (a / x) * (∑' m, ∑' s, doubleSeriesTerm a x h m s)) :
    ∀ x h : ℝ, SmallIncrement x h →
      f (x + h) - f x =
        Real.exp (a / x) * (∑' n, regroupedIncrementTerm a x h n) := by
  intro x h hsmall
  rw [hdouble x h hsmall]
  congr 1
  have hx : x ≠ 0 := hsmall.1
  have hnorm := summable_norm_doubleSeriesTerm_prod a x h hsmall
  have hp : Summable (Function.uncurry (doubleSeriesTerm a x h)) :=
    hnorm.of_norm
  let d : (Sigma fun n : ℕ => Fin (n + 1)) → ℝ := fun z =>
    doubleSeriesTerm a x h z.2 (z.1 - z.2)
  have hdcomp :
      d = Function.uncurry (doubleSeriesTerm a x h) ∘ antidiagonalEquiv := by
    funext z
    rfl
  have hnormcomp :
      (fun z => ‖d z‖) =
        (fun p => ‖Function.uncurry (doubleSeriesTerm a x h) p‖) ∘
          antidiagonalEquiv := by
    funext z
    rfl
  have hdnorm : Summable (fun z => ‖d z‖) := by
    rw [hnormcomp]
    exact antidiagonalEquiv.summable_iff.mpr hnorm
  have hd : Summable d := hdnorm.of_norm
  have hdiag (n : ℕ) :
      (∑' i : Fin (n + 1), d ⟨n, i⟩) =
        regroupedIncrementTerm a x h n := by
    rw [tsum_fintype]
    change (∑ i : Fin (n + 1),
      doubleSeriesTerm a x h i (n - i)) = _
    exact sum_double_antidiagonal_eq_regrouped a x h n hx
  calc
    (∑' m, ∑' s, doubleSeriesTerm a x h m s) =
        ∑' p : ℕ × ℕ, Function.uncurry (doubleSeriesTerm a x h) p :=
      hp.tsum_prod.symm
    _ = ∑' z : Sigma fun n : ℕ => Fin (n + 1), d z := by
      rw [hdcomp]
      exact (antidiagonalEquiv.tsum_eq
        (Function.uncurry (doubleSeriesTerm a x h))).symm
    _ = ∑' n : ℕ, ∑' i : Fin (n + 1), d ⟨n, i⟩ := hd.tsum_sigma
    _ = ∑' n, regroupedIncrementTerm a x h n := by
      apply tsum_congr
      exact hdiag

theorem gap9
    (f : ℝ → ℝ) (a : ℝ) (hf : ∀ x, x ≠ 0 → f x = reciprocalExponential a x)
    (hregroup :
      ∀ x h : ℝ, SmallIncrement x h →
        f (x + h) - f x =
          Real.exp (a / x) * (∑' n, regroupedIncrementTerm a x h n)) :
    ∀ x h : ℝ, SmallIncrement x h →
      f (x + h) - f x =
        Real.exp (a / x) * (∑' n, derivativeIncrementTerm a x h n) := by
  intro x h hsmall
  rw [hregroup x h hsmall]
  congr 1
  apply tsum_congr
  intro n
  exact regroupedIncrementTerm_eq_derivativeIncrementTerm a x h n

theorem gap10
    (f : ℝ → ℝ) (a : ℝ) (hf : ∀ x, x ≠ 0 → f x = reciprocalExponential a x)
    (htaylor :
      ∀ x h : ℝ, SmallIncrement x h →
        f (x + h) - f x =
          Real.exp (a / x) * (∑' n, derivativeIncrementTerm a x h n)) :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, x ≠ 0 →
      iterDeriv n f x = Real.exp (a / x) * derivativeCoefficient a x n := by
  intro n hn x hx
  let c : ℕ → ℝ
    | 0 => Real.exp (a / x)
    | m + 1 => Real.exp (a / x) * derivativeCoefficient a x (m + 1) /
        (Nat.factorial (m + 1) : ℝ)
  let p : FormalMultilinearSeries ℝ ℝ ℝ :=
    FormalMultilinearSeries.ofScalars ℝ c
  let R : NNReal := ⟨|x| / 2, by positivity⟩
  have hRpos : 0 < R := by
    exact_mod_cast div_pos (abs_pos.mpr hx) (by norm_num : (0 : ℝ) < 2)
  have hRlt : (R : ℝ) < |x| := by
    dsimp [R]
    linarith [abs_pos.mpr hx]
  have hsmallR : SmallIncrement x (R : ℝ) := by
    refine ⟨hx, ?_⟩
    rw [abs_of_nonneg R.coe_nonneg]
    exact hRlt
  have htailNorm :
      Summable (fun m : ℕ => |c (m + 1)| * (R : ℝ) ^ (m + 1)) := by
    have hs := (summable_derivativeIncrementTerm a x (R : ℝ) hsmallR).abs
      |>.mul_left |Real.exp (a / x)|
    apply hs.congr
    intro m
    simp only [c, derivativeIncrementTerm, abs_mul, abs_div, abs_pow,
      abs_of_nonneg R.coe_nonneg]
    have hfac : 0 < (Nat.factorial (m + 1) : ℝ) := by positivity
    rw [abs_of_pos hfac]
    ring
  have hcNorm : Summable (fun m : ℕ => |c m| * (R : ℝ) ^ m) :=
    (summable_nat_add_iff 1).1 htailNorm
  have hrle : (R : ENNReal) ≤ p.radius := by
    apply p.le_radius_of_summable_norm
    simpa [p, FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs] using hcNorm
  have hpSeries : HasFPowerSeriesOnBall f p x (R : ENNReal) := by
    refine ⟨hrle, ?_, ?_⟩
    · exact_mod_cast hRpos
    · intro y hy
      rw [Metric.eball_coe] at hy
      have hyR : |y| < (R : ℝ) := by
        simpa [Real.norm_eq_abs] using hy
      have hsmallY : SmallIncrement x y :=
        ⟨hx, lt_trans hyR hRlt⟩
      have htail :=
        (summable_derivativeIncrementTerm a x y hsmallY).hasSum.mul_left
          (Real.exp (a / x))
      apply (hasSum_nat_add_iff' 1).1
      convert htail using 1
      · funext m
        simp [p, c, FormalMultilinearSeries.ofScalars_apply_eq,
          derivativeIncrementTerm, smul_eq_mul]
        ring
      · rw [Finset.sum_range_one]
        simp only [p, FormalMultilinearSeries.ofScalars_apply_eq, c,
          smul_eq_mul, pow_zero, mul_one]
        have hfx : f x = Real.exp (a / x) := by
          simpa [reciprocalExponential] using hf x hx
        calc
          f (x + y) - Real.exp (a / x) = f (x + y) - f x := by rw [hfx]
          _ = Real.exp (a / x) *
              (∑' b, derivativeIncrementTerm a x y b) :=
            htaylor x y hsmallY
  cases n with
  | zero => omega
  | succ m =>
      have hfact := hpSeries.factorial_smul (1 : ℝ) (m + 1)
      have hiter :
          (Nat.factorial (m + 1) : ℝ) *
              (Real.exp (a / x) * derivativeCoefficient a x (m + 1) /
                (Nat.factorial (m + 1) : ℝ)) =
            iterDeriv (m + 1) f x := by
        simpa [p, c, FormalMultilinearSeries.ofScalars_apply_eq,
          smul_eq_mul, ← iteratedDeriv_eq_iteratedFDeriv, iterDeriv,
          iteratedDeriv_eq_iterate] using hfact
      rw [← hiter]
      have hfac : (Nat.factorial (m + 1) : ℝ) ≠ 0 := by positivity
      field_simp

theorem gap11
    (f : ℝ → ℝ) (a : ℝ) (hf : ∀ x, x ≠ 0 → f x = reciprocalExponential a x)
    (hderivative :
      ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, x ≠ 0 →
        iterDeriv n f x = Real.exp (a / x) * derivativeCoefficient a x n) :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, x ≠ 0 →
      iterDeriv n f x =
        (-1 : ℝ) ^ n / x ^ (2 * n) * Real.exp (a / x) *
          (∑ s ∈ Finset.range n,
            (Nat.factorial s : ℝ) * (Nat.choose n s : ℝ) *
              (Nat.choose (n - 1) s : ℝ) * a ^ (n - s) * x ^ s) := by
  intro n hn x hx
  rw [hderivative n hn x hx]
  unfold derivativeCoefficient
  ring

end

end ProofGap.Exercise2874_2
