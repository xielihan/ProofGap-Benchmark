import ProofGapLean.Prelude.Analysis
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise2196
noncomputable section

open scoped BigOperators

def f (x : ℝ) : ℝ :=
  if x = 0 then 0 else x * (Int.floor (1 / x) : ℝ)

def discontinuities : Set ℝ :=
  {x ∈ Set.Icc (0 : ℝ) 1 |
    ¬ ContinuousWithinAt f (Set.Icc (0 : ℝ) 1) x}

def oscillationOn (g : ℝ → ℝ) (I : Set ℝ) : ℝ :=
  sSup {r : ℝ | ∃ u ∈ I, ∃ v ∈ I, r = |g u - g v|}

def IsPartitionOn (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) : Prop :=
  x 0 = a ∧ x n = b ∧ ∀ i < n, x i < x (i + 1)

def width (x : ℕ → ℝ) (i : ℕ) : ℝ := x (i + 1) - x i

def Fine (n : ℕ) (x : ℕ → ℝ) (δ : ℝ) : Prop :=
  ∀ i < n, |width x i| < δ

def omega (g : ℝ → ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  oscillationOn g (Set.Icc (x i) (x (i + 1)))

def oscillationSum (g : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, omega g x i * width x i

def initialSum (g : ℝ → ℝ) (x : ℕ → ℝ) (i₀ : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (i₀ + 1), omega g x i * width x i

def tailSum (g : ℝ → ℝ) (x : ℕ → ℝ) (i₀ n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico (i₀ + 1) n, omega g x i * width x i

def DarbouxIntegrableOn (g : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε > 0, ∃ n : ℕ, ∃ x : ℕ → ℝ,
    0 < n ∧ IsPartitionOn a b n x ∧ oscillationSum g n x < ε

def TailControlled (ε δ : ℝ) : Prop :=
  ∀ n : ℕ, ∀ x : ℕ → ℝ, ∀ i₀ < n,
    IsPartitionOn 0 1 n x →
    x i₀ ≤ ε / 3 → ε / 3 < x (i₀ + 1) →
    Fine n x δ → tailSum f x i₀ n < ε / 3

private theorem f_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    f x ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hx0 : x = 0
  · subst x
    simp [f]
  · have hq : 0 ≤ 1 / x := one_div_nonneg.mpr hx.1
    have hfloorInt : (0 : ℤ) ≤ Int.floor (1 / x) := Int.floor_nonneg.mpr hq
    have hfloor : (0 : ℝ) ≤ (Int.floor (1 / x) : ℝ) := by
      exact_mod_cast hfloorInt
    have hfloorLe : (Int.floor (1 / x) : ℝ) ≤ 1 / x := Int.floor_le _
    rw [f, if_neg hx0]
    constructor
    · exact mul_nonneg hx.1 hfloor
    · calc
        x * (Int.floor (1 / x) : ℝ) ≤ x * (1 / x) :=
          mul_le_mul_of_nonneg_left hfloorLe hx.1
        _ = 1 := by field_simp

private theorem partition_le_on {a b : ℝ} {n : ℕ} {x : ℕ → ℝ}
    (hp : IsPartitionOn a b n x) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ n) : x i ≤ x j := by
  induction j generalizing i with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      exact le_rfl
  | succ j ih =>
      by_cases h : i = j + 1
      · subst i
        exact le_rfl
      · have hij' : i ≤ j := by omega
        have hjn : j < n := by omega
        exact (ih hij' (by omega)).trans (hp.2.2 j hjn).le

private theorem sum_width (x : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m, width x i) = x m - x 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [width]
      ring

private theorem fine_mono {n : ℕ} {x : ℕ → ℝ} {δ d : ℝ}
    (hf : Fine n x δ) (hδd : δ ≤ d) : Fine n x d := by
  intro i hi
  exact lt_of_lt_of_le (hf i hi) hδd

private def stepCount (x : ℝ) : ℝ := (Int.floor (1 / x) : ℝ)

private theorem stepCount_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ stepCount x := by
  unfold stepCount
  exact_mod_cast (Int.floor_nonneg.mpr (one_div_nonneg.mpr hx))

private theorem stepCount_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    stepCount y ≤ stepCount x := by
  unfold stepCount
  have hdiv : 1 / y ≤ 1 / x := one_div_le_one_div_of_le hx hxy
  exact_mod_cast Int.floor_mono hdiv

private theorem point_oscillation_ordered {a p q u v : ℝ}
    (ha : 0 < a) (hap : a ≤ p) (hpu : p ≤ u) (huv : u ≤ v)
    (hvq : v ≤ q) (hq1 : q ≤ 1) :
    |f u - f v| ≤ (1 / a) * (q - p) +
      (stepCount p - stepCount q) := by
  have hp : 0 < p := lt_of_lt_of_le ha hap
  have hu : 0 < u := lt_of_lt_of_le hp hpu
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hqu : stepCount u ≤ stepCount p := stepCount_antitone hp hpu
  have huvq : stepCount v ≤ stepCount u := stepCount_antitone hu huv
  have hqv : stepCount q ≤ stepCount v := stepCount_antitone hv hvq
  have hqu0 : 0 ≤ stepCount u := stepCount_nonneg hu.le
  have hv0 : 0 ≤ v := hv.le
  have hdiff0 : 0 ≤ stepCount u - stepCount v := sub_nonneg.mpr huvq
  have hquBound : stepCount u ≤ 1 / a := by
    calc
      stepCount u ≤ stepCount p := hqu
      _ ≤ 1 / p := Int.floor_le _
      _ ≤ 1 / a := one_div_le_one_div_of_le ha hap
  have huvWidth : v - u ≤ q - p := by linarith
  have hv1 : v ≤ 1 := hvq.trans hq1
  have hdiffBound : stepCount u - stepCount v ≤
      stepCount p - stepCount q := by
    linarith
  have hfirst : stepCount u * (v - u) ≤ (1 / a) * (q - p) := by
    calc
      stepCount u * (v - u) ≤ (1 / a) * (v - u) :=
        mul_le_mul_of_nonneg_right hquBound (sub_nonneg.mpr huv)
      _ ≤ (1 / a) * (q - p) :=
        mul_le_mul_of_nonneg_left huvWidth (one_div_nonneg.mpr ha.le)
  have hsecond : v * (stepCount u - stepCount v) ≤
      stepCount p - stepCount q := by
    have hmul := mul_nonneg (sub_nonneg.mpr hv1) hdiff0
    nlinarith
  have hrewrite : f u - f v =
      stepCount u * (u - v) + v * (stepCount u - stepCount v) := by
    simp only [f, if_neg (ne_of_gt hu), if_neg (ne_of_gt hv), stepCount]
    ring
  rw [hrewrite]
  calc
    |stepCount u * (u - v) + v * (stepCount u - stepCount v)|
        ≤ |stepCount u * (u - v)| +
          |v * (stepCount u - stepCount v)| := abs_add_le _ _
    _ = stepCount u * (v - u) + v * (stepCount u - stepCount v) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hqu0, abs_of_nonneg hv0,
        abs_of_nonneg hdiff0, abs_of_nonpos (sub_nonpos.mpr huv)]
      ring
    _ ≤ (1 / a) * (q - p) + (stepCount p - stepCount q) :=
      add_le_add hfirst hsecond

private theorem point_oscillation_bound {a p q u v : ℝ}
    (ha : 0 < a) (hap : a ≤ p)
    (hu : u ∈ Set.Icc p q) (hv : v ∈ Set.Icc p q) (hq1 : q ≤ 1) :
    |f u - f v| ≤ (1 / a) * (q - p) +
      (stepCount p - stepCount q) := by
  rcases le_total u v with huv | hvu
  · exact point_oscillation_ordered ha hap hu.1 huv hv.2 hq1
  · simpa [abs_sub_comm] using
      (point_oscillation_ordered ha hap hv.1 hvu hu.2 hq1)

private theorem oscillation_cell_bound {a p q : ℝ}
    (ha : 0 < a) (hap : a ≤ p) (hpq : p < q) (hq1 : q ≤ 1) :
    oscillationOn f (Set.Icc p q) ≤
      (1 / a) * (q - p) + (stepCount p - stepCount q) := by
  unfold oscillationOn
  apply csSup_le
  · exact ⟨0, p, ⟨le_rfl, hpq.le⟩, p, ⟨le_rfl, hpq.le⟩, by simp⟩
  · rintro r ⟨u, hu, v, hv, rfl⟩
    exact point_oscillation_bound ha hap hu hv hq1

private theorem sum_width_Ico (x : ℕ → ℝ) {l n : ℕ} (hln : l ≤ n) :
    (∑ i ∈ Finset.Ico l n, width x i) = x n - x l := by
  rw [Finset.sum_Ico_eq_sub _ hln, sum_width x n, sum_width x l]
  ring

private theorem sum_step_range (x : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m,
      (stepCount (x (i + 1)) - stepCount (x i))) =
        stepCount (x m) - stepCount (x 0) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring

private theorem sum_step_Ico (x : ℕ → ℝ) {l n : ℕ} (hln : l ≤ n) :
    (∑ i ∈ Finset.Ico l n,
      (stepCount (x i) - stepCount (x (i + 1)))) =
        stepCount (x l) - stepCount (x n) := by
  have htel :
      (∑ i ∈ Finset.Ico l n,
        (stepCount (x (i + 1)) - stepCount (x i))) =
          stepCount (x n) - stepCount (x l) := by
    rw [Finset.sum_Ico_eq_sub _ hln, sum_step_range x n,
      sum_step_range x l]
    ring
  calc
    (∑ i ∈ Finset.Ico l n,
      (stepCount (x i) - stepCount (x (i + 1)))) =
        -(∑ i ∈ Finset.Ico l n,
          (stepCount (x (i + 1)) - stepCount (x i))) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = stepCount (x l) - stepCount (x n) := by
      rw [htel]
      ring

private theorem controlled_sum_Ico (a : ℝ) (n : ℕ) (x : ℕ → ℝ)
    (l : ℕ) (δ : ℝ)
    (ha : 0 < a) (hδ : 0 ≤ δ) (hp : IsPartitionOn (x 0) 1 n x)
    (hal : a ≤ x l) (hln : l ≤ n) (hfine : Fine n x δ) :
    (∑ i ∈ Finset.Ico l n, omega f x i * width x i) ≤
      δ * (2 / a) := by
  have hterm : ∀ i ∈ Finset.Ico l n,
      omega f x i * width x i ≤
        δ * ((1 / a) * width x i +
          (stepCount (x i) - stepCount (x (i + 1)))) := by
    intro i hi
    have hil := (Finset.mem_Ico.mp hi).1
    have hin := (Finset.mem_Ico.mp hi).2
    have hxi : a ≤ x i := hal.trans
      (partition_le_on hp hil (le_of_lt hin))
    have hinc : x i < x (i + 1) := hp.2.2 i hin
    have hq1 : x (i + 1) ≤ 1 := by
      calc
        x (i + 1) ≤ x n := partition_le_on hp (by omega) le_rfl
        _ = 1 := hp.2.1
    have homega : omega f x i ≤
        (1 / a) * width x i +
          (stepCount (x i) - stepCount (x (i + 1))) := by
      simpa [omega, width] using
        oscillation_cell_bound ha hxi hinc hq1
    have hw0 : 0 ≤ width x i := sub_nonneg.mpr hinc.le
    have hwδ : width x i ≤ δ := by
      have hfinei := hfine i hin
      rw [abs_of_nonneg hw0] at hfinei
      exact hfinei.le
    have hstep0 : 0 ≤ stepCount (x i) - stepCount (x (i + 1)) := by
      apply sub_nonneg.mpr
      exact stepCount_antitone (lt_of_lt_of_le ha hxi) hinc.le
    have hbound0 : 0 ≤ (1 / a) * width x i +
        (stepCount (x i) - stepCount (x (i + 1))) := by
      positivity
    calc
      omega f x i * width x i ≤
          ((1 / a) * width x i +
            (stepCount (x i) - stepCount (x (i + 1)))) * width x i :=
        mul_le_mul_of_nonneg_right homega hw0
      _ ≤ ((1 / a) * width x i +
            (stepCount (x i) - stepCount (x (i + 1)))) * δ :=
        mul_le_mul_of_nonneg_left hwδ hbound0
      _ = δ * ((1 / a) * width x i +
            (stepCount (x i) - stepCount (x (i + 1)))) := by ring
  have hsum := Finset.sum_le_sum hterm
  have hrewrite :
      (∑ i ∈ Finset.Ico l n,
        δ * ((1 / a) * width x i +
          (stepCount (x i) - stepCount (x (i + 1))))) =
      δ * ((1 / a) * (x n - x l) +
        (stepCount (x l) - stepCount (x n))) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_width_Ico x hln, sum_step_Ico x hln]
  rw [hrewrite] at hsum
  have hstepL : stepCount (x l) ≤ 1 / a := by
    calc
      stepCount (x l) ≤ 1 / x l := Int.floor_le _
      _ ≤ 1 / a := one_div_le_one_div_of_le ha hal
  have hstepN : 0 ≤ stepCount (x n) := by
    rw [hp.2.1]
    exact stepCount_nonneg zero_le_one
  have hnonneg : 0 ≤ 1 / a := one_div_nonneg.mpr ha.le
  have hfirst : (1 / a) * (x n - x l) ≤ 1 / a := by
    rw [hp.2.1]
    have hxl0 : 0 ≤ x l := le_trans ha.le hal
    have hsub : 1 - x l ≤ 1 := by linarith
    simpa using mul_le_mul_of_nonneg_left hsub hnonneg
  have hinside : (1 / a) * (x n - x l) +
      (stepCount (x l) - stepCount (x n)) ≤ 2 / a := by
    have htwo : 2 / a = 1 / a + 1 / a := by ring
    rw [htwo]
    linarith
  exact hsum.trans (mul_le_mul_of_nonneg_left hinside hδ)

private theorem isBounded_Icc :
    Bornology.IsBounded (Set.Icc (0 : ℝ) 1) := by
  exact Metric.isBounded_Icc (0 : ℝ) 1

theorem gap1 :
    Bornology.IsBounded (f '' Set.Icc (0 : ℝ) 1) := by
  refine (isBounded_Icc : Bornology.IsBounded (Set.Icc (0 : ℝ) 1)).subset ?_
  rintro y ⟨x, hx, rfl⟩
  exact f_mem_Icc hx

theorem gap2 :
    discontinuities =
      ({0} : Set ℝ) ∪
        {x : ℝ | ∃ n : ℕ, 2 ≤ n ∧ x = 1 / (n : ℝ)} := by
  classical
  ext x
  constructor
  · rintro ⟨hxI, hxdisc⟩
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      have hxpos : 0 < x := lt_of_le_of_ne hxI.1 (Ne.symm hx0)
      let k : ℤ := Int.floor (1 / x)
      have hklo : (k : ℝ) ≤ 1 / x := by
        dsimp [k]
        exact Int.floor_le _
      have hkhi : 1 / x < (k : ℝ) + 1 := by
        dsimp [k]
        exact Int.lt_floor_add_one _
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast Int.floor_nonneg.mpr (one_div_nonneg.mpr hxpos.le)
      have hkeq : (k : ℝ) = 1 / x := by
        by_contra hne
        have hklt : (k : ℝ) < 1 / x := lt_of_le_of_ne hklo hne
        apply hxdisc
        rw [Metric.continuousWithinAt_iff]
        intro η hη
        let A : ℝ := 1 - (k : ℝ) * x
        let B : ℝ := ((k : ℝ) + 1) * x - 1
        have hA : 0 < A := by
          dsimp [A]
          have := (lt_div_iff₀ hxpos).1 hklt
          linarith
        have hB : 0 < B := by
          dsimp [B]
          have := (div_lt_iff₀ hxpos).1 hkhi
          linarith
        let d₁ := A / (2 * (|(k : ℝ)| + 1))
        let d₂ := B / (2 * (|(k : ℝ) + 1| + 1))
        let d₃ := x / 2
        let d₄ := η / (|(k : ℝ)| + 1)
        have hkden : 0 < |(k : ℝ)| + 1 := by linarith [abs_nonneg (k : ℝ)]
        have hk1den : 0 < |(k : ℝ) + 1| + 1 := by
          linarith [abs_nonneg ((k : ℝ) + 1)]
        refine ⟨min (min d₁ d₂) (min d₃ d₄), ?_, ?_⟩
        · apply lt_min
          · apply lt_min
            · dsimp [d₁]
              positivity
            · dsimp [d₂]
              positivity
          · apply lt_min
            · dsimp [d₃]
              positivity
            · dsimp [d₄]
              positivity
        · intro y hyI hy
          have hδ₁ : dist y x < d₁ :=
            lt_of_lt_of_le hy (min_le_of_left_le (min_le_left _ _))
          have hδ₂ : dist y x < d₂ :=
            lt_of_lt_of_le hy (min_le_of_left_le (min_le_right _ _))
          have hδ₃ : dist y x < d₃ :=
            lt_of_lt_of_le hy (min_le_of_right_le (min_le_left _ _))
          have hδ₄ : dist y x < d₄ :=
            lt_of_lt_of_le hy (min_le_of_right_le (min_le_right _ _))
          rw [Real.dist_eq] at hδ₁ hδ₂ hδ₃ hδ₄
          have hypos : 0 < y := by
            dsimp [d₃] at hδ₃
            have habs := abs_lt.mp hδ₃
            linarith
          have hfloor : Int.floor (1 / y) = k := by
            rw [Int.floor_eq_iff]
            constructor
            · apply (le_div_iff₀ hypos).2
              have hmul : |y - x| * (2 * (|(k : ℝ)| + 1)) < A := by
                apply (lt_div_iff₀ (mul_pos (by norm_num) hkden)).1
                simpa [d₁] using hδ₁
              have habsBound : |(k : ℝ)| * |y - x| < A := by
                nlinarith [abs_nonneg (k : ℝ), abs_nonneg (y - x)]
              have hpert : (k : ℝ) * (y - x) ≤ |(k : ℝ)| * |y - x| := by
                calc
                  (k : ℝ) * (y - x) ≤ |(k : ℝ) * (y - x)| := le_abs_self _
                  _ = |(k : ℝ)| * |y - x| := abs_mul _ _
              dsimp [A] at hA habsBound
              nlinarith
            · apply (div_lt_iff₀ hypos).2
              have hmul : |y - x| * (2 * (|(k : ℝ) + 1| + 1)) < B := by
                apply (lt_div_iff₀ (mul_pos (by norm_num) hk1den)).1
                simpa [d₂] using hδ₂
              have habsBound : |(k : ℝ) + 1| * |y - x| < B := by
                nlinarith [abs_nonneg ((k : ℝ) + 1), abs_nonneg (y - x)]
              have hpert : -(|(k : ℝ) + 1| * |y - x|) ≤
                  ((k : ℝ) + 1) * (y - x) := by
                calc
                  -(|(k : ℝ) + 1| * |y - x|) =
                      -|((k : ℝ) + 1) * (y - x)| := by rw [abs_mul]
                  _ ≤ ((k : ℝ) + 1) * (y - x) := neg_abs_le _
              dsimp [B] at hB habsBound
              nlinarith
          have hkdef : Int.floor (1 / x) = k := rfl
          simp only [f, if_neg hx0, if_neg (ne_of_gt hypos), hfloor, hkdef]
          rw [Real.dist_eq,
            show y * (k : ℝ) - x * (k : ℝ) = (k : ℝ) * (y - x) by ring,
            abs_mul]
          calc
            |(k : ℝ)| * |y - x| ≤ (|(k : ℝ)| + 1) * |y - x| :=
              mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
            _ < (|(k : ℝ)| + 1) * d₄ :=
              mul_lt_mul_of_pos_left hδ₄ hkden
            _ = η := by
              dsimp [d₄]
              field_simp [ne_of_gt hkden]
      have hkpos : 0 < k := by
        have hone : (1 : ℝ) ≤ 1 / x :=
          (le_div_iff₀ hxpos).2 (by simpa using hxI.2)
        have hkone : (1 : ℝ) ≤ (k : ℝ) := by linarith
        exact_mod_cast hkone
      obtain ⟨n, hkn⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hkpos)
      have hnposZ : (0 : ℤ) < (n : ℤ) := by
        rw [← hkn]
        exact hkpos
      have hnpos : 0 < n := by exact_mod_cast hnposZ
      have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
      have hknR : (k : ℝ) = (n : ℝ) := by exact_mod_cast hkn
      have hxrecip : x = 1 / (n : ℝ) := by
        apply (eq_div_iff (ne_of_gt hnR)).2
        calc
          x * (n : ℝ) = x * (k : ℝ) := by rw [hknR]
          _ = x * (1 / x) := by rw [hkeq]
          _ = 1 := by field_simp [hx0]
      have hn2 : 2 ≤ n := by
        by_contra hn2
        have hn1 : n = 1 := by omega
        have hx1 : x = 1 := by simpa [hn1] using hxrecip
        apply hxdisc
        rw [hx1]
        rw [Metric.continuousWithinAt_iff]
        intro η hη
        refine ⟨min (1 / 2 : ℝ) η, lt_min (by norm_num) hη, ?_⟩
        intro y hyI hy
        have hyhalf : 1 / 2 < y := by
          have hy' : |y - 1| < 1 / 2 := by
            rw [← Real.dist_eq]
            exact lt_of_lt_of_le hy (min_le_left _ _)
          linarith [abs_lt.mp hy']
        have hypos : 0 < y := by linarith
        have hfloor : Int.floor (1 / y) = 1 := by
          rw [Int.floor_eq_iff]
          constructor
          · apply (le_div_iff₀ hypos).2
            simpa using hyI.2
          · apply (div_lt_iff₀ hypos).2
            norm_num at ⊢
            linarith
        have hyη : dist y 1 < η := lt_of_lt_of_le hy (min_le_right _ _)
        have hfloorR : (Int.floor (1 / y) : ℝ) = 1 := by
          exact_mod_cast hfloor
        have hfy : f y = y := by
          rw [f, if_neg (ne_of_gt hypos), hfloorR]
          ring
        have hf1 : f 1 = 1 := by norm_num [f]
        rw [hfy, hf1]
        exact hyη
      exact ⟨n, hn2, hxrecip⟩
  · rintro (hx0 | hrecip)
    · subst x
      constructor
      · constructor <;> norm_num
      · rw [Metric.continuousWithinAt_iff]
        push_neg
        refine ⟨1 / 2, by norm_num, ?_⟩
        intro δ hδ
        obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (max (1 / δ) 1)
        have hnpos : (0 : ℝ) < n := by
          linarith [le_max_right (1 / δ) 1]
        let y : ℝ := 1 / (n : ℝ)
        have hypos : 0 < y := by dsimp [y]; positivity
        have hyone : y ≤ 1 := by
          dsimp [y]
          exact (div_le_one hnpos).2 (by linarith [le_max_right (1 / δ) 1])
        have hydelta : dist y 0 < δ := by
          rw [Real.dist_eq]
          dsimp [y]
          rw [sub_zero, abs_of_pos (by positivity)]
          apply (div_lt_iff₀ hnpos).2
          have hnd : 1 / δ < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
          have hmul := (div_lt_iff₀ hδ).1 hnd
          simpa [mul_comm] using hmul
        have hinv : 1 / y = (n : ℝ) := by
          dsimp [y]
          field_simp [ne_of_gt hnpos]
        have hfloor : Int.floor (1 / y) = (n : ℤ) := by
          rw [hinv]
          exact Int.floor_natCast n
        have hfy : f y = 1 := by
          rw [f, if_neg (ne_of_gt hypos), hfloor]
          dsimp [y]
          norm_num <;> field_simp [ne_of_gt hnpos]
        refine ⟨y, ⟨hypos.le, hyone⟩, hydelta, ?_⟩
        rw [hfy]
        norm_num [f]
    · obtain ⟨n, hn, rfl⟩ := hrecip
      have hnR : (0 : ℝ) < n := by positivity
      have hnRone : (1 : ℝ) < n := by
        exact_mod_cast (show 1 < n by omega)
      have hm : 0 < (n : ℝ) - 1 := sub_pos.mpr hnRone
      have hcast : (((n : ℤ) - 1 : ℤ) : ℝ) = (n : ℝ) - 1 := by
        norm_num
      constructor
      · constructor
        · positivity
        · exact (div_le_one hnR).2
            (by exact_mod_cast (show 1 ≤ n by omega))
      · rw [Metric.continuousWithinAt_iff]
        push_neg
        refine ⟨1 / (2 * (n : ℝ)), one_div_pos.mpr (mul_pos (by norm_num) hnR), ?_⟩
        intro δ hδ
        let d : ℝ := min (δ / 2)
          ((1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) / 2)
        let y : ℝ := 1 / (n : ℝ) + d
        have hgap : 0 < 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) := by
          apply sub_pos.mpr
          exact one_div_lt_one_div_of_lt hm (by linarith)
        have hd : 0 < d := by
          dsimp [d]
          apply lt_min <;> linarith
        have hdleft : d ≤ δ / 2 := by
          dsimp [d]
          exact min_le_left _ _
        have hdle : d ≤
            (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) / 2 := by
          dsimp [d]
          exact min_le_right _ _
        have hypos : 0 < y := by
          dsimp [y]
          linarith [one_div_pos.mpr hnR]
        have hygt : 1 / (n : ℝ) < y := by
          dsimp [y]
          linarith
        have hylt : y < 1 / ((n : ℝ) - 1) := by
          dsimp [y]
          linarith
        have hlower : (n : ℝ) - 1 ≤ 1 / y := by
          apply (le_div_iff₀ hypos).2
          have hmul : y * ((n : ℝ) - 1) < 1 :=
            (lt_div_iff₀ hm).1 hylt
          simpa [mul_comm] using hmul.le
        have hupper : 1 / y < (n : ℝ) := by
          apply (div_lt_iff₀ hypos).2
          have hmul : 1 < y * (n : ℝ) :=
            (div_lt_iff₀ hnR).1 hygt
          simpa [mul_comm] using hmul
        have hfloor : Int.floor (1 / y) = (n : ℤ) - 1 := by
          rw [Int.floor_eq_iff]
          constructor
          · rw [hcast]
            exact hlower
          · rw [hcast]
            simpa using hupper
        have hnRtwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
        have hmone : (1 : ℝ) ≤ (n : ℝ) - 1 := by linarith
        have hyone : y ≤ 1 := by
          exact hylt.le.trans ((div_le_one hm).2 hmone)
        have hydelta : dist y (1 / (n : ℝ)) < δ := by
          rw [Real.dist_eq]
          dsimp [y]
          rw [add_sub_cancel_left, abs_of_pos hd]
          linarith
        have hinv : 1 / (1 / (n : ℝ)) = (n : ℝ) := by
          field_simp [ne_of_gt hnR]
        have hfloorBase : Int.floor (1 / (1 / (n : ℝ))) = (n : ℤ) := by
          rw [hinv]
          exact Int.floor_natCast n
        have hbase : f (1 / (n : ℝ)) = 1 := by
          rw [f, if_neg (by positivity), hfloorBase]
          norm_num <;> field_simp [ne_of_gt hnR]
        have hfy : f y = y * ((n : ℝ) - 1) := by
          rw [f, if_neg (ne_of_gt hypos), hfloor, hcast]
        have hdm : d * ((n : ℝ) - 1) ≤ 1 / (2 * (n : ℝ)) := by
          calc
            d * ((n : ℝ) - 1) ≤
                ((1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) / 2) *
                  ((n : ℝ) - 1) :=
              mul_le_mul_of_nonneg_right hdle hm.le
            _ = 1 / (2 * (n : ℝ)) := by
              field_simp [ne_of_gt hnR, ne_of_gt hm] <;> ring
        have hhalf : 1 / (n : ℝ) = 2 * (1 / (2 * (n : ℝ))) := by
          field_simp [ne_of_gt hnR] <;> ring
        have hbaseMul :
            (1 / (n : ℝ)) * ((n : ℝ) - 1) = 1 - 1 / (n : ℝ) := by
          field_simp [ne_of_gt hnR] <;> ring
        have hym : y * ((n : ℝ) - 1) ≤ 1 - 1 / (2 * (n : ℝ)) := by
          calc
            y * ((n : ℝ) - 1) =
                (1 / (n : ℝ)) * ((n : ℝ) - 1) +
                  d * ((n : ℝ) - 1) := by
              dsimp [y]
              ring
            _ = (1 - 1 / (n : ℝ)) + d * ((n : ℝ) - 1) := by
              rw [hbaseMul]
            _ ≤ 1 - 1 / (2 * (n : ℝ)) := by
              linarith
        have hym1 : y * ((n : ℝ) - 1) < 1 := by
          have hsmall : 1 - 1 / (2 * (n : ℝ)) < 1 := by
            have hpos : 0 < 1 / (2 * (n : ℝ)) :=
              one_div_pos.mpr (mul_pos (by norm_num) hnR)
            linarith
          exact lt_of_le_of_lt hym hsmall
        refine ⟨y, ⟨hypos.le, hyone⟩, hydelta, ?_⟩
        rw [hfy, hbase, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hym1.le)]
        linarith

theorem gap3 (I : Set ℝ) (hI : I ⊆ Set.Icc (0 : ℝ) 1) :
    oscillationOn f I ≤ 1 := by
  classical
  by_cases hne : I.Nonempty
  · unfold oscillationOn
    apply csSup_le
    · obtain ⟨u, hu⟩ := hne
      exact ⟨0, u, hu, u, hu, by simp⟩
    · rintro r ⟨u, hu, v, hv, rfl⟩
      rcases f_mem_Icc (hI hu) with ⟨hu0, hu1⟩
      rcases f_mem_Icc (hI hv) with ⟨hv0, hv1⟩
      rw [abs_le]
      constructor <;> linarith
  · have hIempty : I = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [oscillationOn, hIempty]

theorem gap4 (ε : ℝ) (hε : 0 < ε) (hε3 : ε < 3) :
    DarbouxIntegrableOn f (ε / 3) 1 := by
  classical
  unfold DarbouxIntegrableOn
  intro η hη
  let a := ε / 3
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos hε (by norm_num)
  have ha1 : a < 1 := by
    dsimp [a]
    linarith
  let d := η * a / 4
  have hd : 0 < d := by
    dsimp [d]
    exact div_pos (mul_pos hη ha) (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_gt ((1 - a) / d)
  have hquot : 0 < (1 - a) / d :=
    div_pos (sub_pos.mpr ha1) hd
  have hnR : (0 : ℝ) < n := lt_trans hquot hn
  have hnN : 0 < n := by exact_mod_cast hnR
  let x : ℕ → ℝ := fun i => a + (i : ℝ) * (1 - a) / (n : ℝ)
  have hp : IsPartitionOn a 1 n x := by
    constructor
    · simp [x]
    constructor
    · simp [x, ne_of_gt hnR]
    · intro i hi
      dsimp [x]
      rw [add_lt_add_iff_left]
      apply (div_lt_div_iff_of_pos_right hnR).2
      apply mul_lt_mul_of_pos_right _ (sub_pos.mpr ha1)
      exact_mod_cast Nat.lt_succ_self i
  have hfine : Fine n x d := by
    intro i hi
    have hw : width x i = (1 - a) / (n : ℝ) := by
      dsimp [width, x]
      rw [Nat.cast_add, Nat.cast_one]
      field_simp [ne_of_gt hnR] <;> ring
    have hwpos : 0 < (1 - a) / (n : ℝ) :=
      div_pos (sub_pos.mpr ha1) hnR
    rw [hw, abs_of_pos hwpos]
    apply (div_lt_iff₀ hnR).2
    have hprod := (div_lt_iff₀ hd).1 hn
    simpa [mul_comm] using hprod
  have hx0 : x 0 = a := by simp [x]
  have hp' : IsPartitionOn (x 0) 1 n x := by
    rw [hx0]
    exact hp
  have hbound := controlled_sum_Ico a n x 0 d ha hd.le hp'
    (by linarith [hx0]) (Nat.zero_le n) hfine
  refine ⟨n, x, hnN, hp, ?_⟩
  have hcalc : d * (2 / a) = η / 2 := by
    dsimp [d]
    field_simp [ne_of_gt ha] <;> ring
  rw [hcalc] at hbound
  simpa [oscillationSum] using lt_of_le_of_lt hbound (by linarith)

theorem gap5 (ε : ℝ) (hε : 0 < ε) (hε3 : ε < 3) :
    ∃ δ > 0, TailControlled ε δ := by
  classical
  let a := ε / 3
  let δ := ε * a / 12
  have ha : 0 < a := by dsimp [a]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro n x i₀ hi hp hleft hright hfine
  unfold tailSum
  have hl : i₀ + 1 ≤ n := by omega
  have hp' : IsPartitionOn (x 0) 1 n x := by simpa [hp.1] using hp
  have hbound := controlled_sum_Ico a n x (i₀ + 1) δ ha hδ.le hp'
    hright.le hl hfine
  have hcalc : δ * (2 / a) = ε / 6 := by
    dsimp [δ]
    field_simp [ne_of_gt ha]
    ring
  rw [hcalc] at hbound
  exact lt_of_le_of_lt hbound (by linarith)

theorem gap6 (n : ℕ) (x : ℕ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hε3 : ε < 3)
    (hp : IsPartitionOn 0 1 n x) :
    ∃ i₀ < n, x i₀ ≤ ε / 3 := by
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    linarith [hp.1, hp.2.1]
  refine ⟨0, hn, ?_⟩
  rw [hp.1]
  linarith

theorem gap7 (n : ℕ) (x : ℕ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hε3 : ε < 3)
    (hp : IsPartitionOn 0 1 n x) :
    ∃ i₀ < n, x i₀ ≤ ε / 3 ∧ ε / 3 < x (i₀ + 1) := by
  classical
  have hex : ∃ k : ℕ, ε / 3 < x k := by
    refine ⟨n, ?_⟩
    rw [hp.2.1]
    linarith
  let k := Nat.find hex
  have hk : ε / 3 < x k := by
    simpa [k] using Nat.find_spec hex
  have hkn : k ≤ n := by
    simpa [k] using Nat.find_min' hex
      (show ε / 3 < x n by rw [hp.2.1]; linarith)
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos h
    rw [hk0, hp.1] at hk
    linarith
  have hleft : x (k - 1) ≤ ε / 3 := by
    by_contra h
    have hgt : ε / 3 < x (k - 1) := lt_of_not_ge h
    have hpred : k - 1 < Nat.find hex := by
      simpa [k] using Nat.pred_lt (Nat.ne_of_gt hkpos)
    exact (Nat.find_min hex hpred) hgt
  refine ⟨k - 1, by omega, hleft, ?_⟩
  simpa [Nat.sub_add_cancel hkpos] using hk

theorem gap8 (n i₀ : ℕ) (x : ℕ → ℝ)
    (hp : IsPartitionOn 0 1 n x) (hi : i₀ < n) :
    x i₀ < x (i₀ + 1) := by
  exact hp.2.2 i₀ hi

theorem gap9 (n i₀ : ℕ) (x : ℕ → ℝ) (ε δ : ℝ)
    (hi : i₀ < n) (hp : IsPartitionOn 0 1 n x)
    (hleft : x i₀ ≤ ε / 3) (hright : ε / 3 < x (i₀ + 1))
    (hfine : Fine n x δ) (hcontrol : TailControlled ε δ) :
    tailSum f x i₀ n < ε / 3 := by
  exact hcontrol n x i₀ hi hp hleft hright hfine

theorem gap10 (n i₀ : ℕ) (x : ℕ → ℝ)
    (hp : IsPartitionOn 0 1 n x) (hi : i₀ < n) :
    initialSum f x i₀ ≤
      ∑ i ∈ Finset.range (i₀ + 1), width x i := by
  unfold initialSum
  apply Finset.sum_le_sum
  intro i hiRange
  have hii₀ : i < i₀ + 1 := Finset.mem_range.mp hiRange
  have hin : i < n := by omega
  have hwidth : 0 ≤ width x i := sub_nonneg.mpr (hp.2.2 i hin).le
  have hsubset : Set.Icc (x i) (x (i + 1)) ⊆ Set.Icc (0 : ℝ) 1 := by
    rintro y ⟨hiy, hyi⟩
    constructor
    · calc
        0 = x 0 := hp.1.symm
        _ ≤ x i := partition_le_on hp (Nat.zero_le i) (by omega)
        _ ≤ y := hiy
    · calc
        y ≤ x (i + 1) := hyi
        _ ≤ x n := partition_le_on hp (by omega) le_rfl
        _ = 1 := hp.2.1
  have homega : omega f x i ≤ 1 := by
    simpa [omega] using gap3 (Set.Icc (x i) (x (i + 1))) hsubset
  simpa using mul_le_mul_of_nonneg_right homega hwidth

theorem gap11 (n i₀ : ℕ) (x : ℕ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hp : IsPartitionOn 0 1 n x) (hi : i₀ < n)
    (hleft : x i₀ ≤ ε / 3) (hright : ε / 3 < x (i₀ + 1))
    (hfine : Fine n x (ε / 3)) :
    (∑ i ∈ Finset.range (i₀ + 1), width x i) < 2 * ε / 3 := by
  rw [sum_width, hp.1]
  have hw := hfine i₀ hi
  rw [abs_lt] at hw
  dsimp [width] at hw
  linarith

theorem gap12 (n i₀ : ℕ) (x : ℕ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hp : IsPartitionOn 0 1 n x) (hi : i₀ < n)
    (hleft : x i₀ ≤ ε / 3) (hright : ε / 3 < x (i₀ + 1))
    (hfine : Fine n x (ε / 3)) :
    initialSum f x i₀ < 2 * ε / 3 := by
  exact lt_of_le_of_lt (gap10 n i₀ x hp hi)
    (gap11 n i₀ x ε hε hp hi hleft hright hfine)

theorem gap13 (n i₀ : ℕ) (x : ℕ → ℝ) (hi : i₀ < n) :
    oscillationSum f n x = initialSum f x i₀ + tailSum f x i₀ n := by
  unfold oscillationSum initialSum tailSum
  have hunion : Finset.range n =
      Finset.range (i₀ + 1) ∪ Finset.Ico (i₀ + 1) n := by
    ext j
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdis : Disjoint (Finset.range (i₀ + 1))
      (Finset.Ico (i₀ + 1) n) := by
    refine Finset.disjoint_left.mpr ?_
    intro j hj₁ hj₂
    simp only [Finset.mem_range] at hj₁
    simp only [Finset.mem_Ico] at hj₂
    omega
  rw [hunion, Finset.sum_union hdis]

theorem gap14 (n i₀ : ℕ) (x : ℕ → ℝ) (ε : ℝ)
    (hinit : initialSum f x i₀ < 2 * ε / 3)
    (htail : tailSum f x i₀ n < ε / 3) :
    initialSum f x i₀ + tailSum f x i₀ n < ε := by
  linarith

theorem gap15 (n i₀ : ℕ) (x : ℕ → ℝ) (ε : ℝ)
    (hi : i₀ < n)
    (hinit : initialSum f x i₀ < 2 * ε / 3)
    (htail : tailSum f x i₀ n < ε / 3) :
    oscillationSum f n x < ε := by
  rw [gap13 n i₀ x hi]
  exact gap14 n i₀ x ε hinit htail

theorem gap16 :
    ∀ ε > 0, ∃ δ > 0, ∀ n : ℕ, ∀ x : ℕ → ℝ,
      IsPartitionOn 0 1 n x → Fine n x δ →
        oscillationSum f n x < ε := by
  intro ε hε
  let e : ℝ := min ε 1
  have he : 0 < e := by
    dsimp [e]
    exact lt_min hε zero_lt_one
  have he3 : e < 3 := by
    calc
      e ≤ 1 := min_le_right _ _
      _ < 3 := by norm_num
  obtain ⟨d, hd, hcontrol⟩ := gap5 e he he3
  refine ⟨min d (e / 3), lt_min hd (by positivity), ?_⟩
  intro n x hp hfine
  have hfineD : Fine n x d := fine_mono hfine (min_le_left _ _)
  have hfineE : Fine n x (e / 3) := fine_mono hfine (min_le_right _ _)
  obtain ⟨i₀, hi, hleft, hright⟩ := gap7 n x e he he3 hp
  have htail : tailSum f x i₀ n < e / 3 :=
    gap9 n i₀ x e d hi hp hleft hright hfineD hcontrol
  have hinit : initialSum f x i₀ < 2 * e / 3 :=
    gap12 n i₀ x e he hp hi hleft hright hfineE
  have hsum : oscillationSum f n x < e :=
    gap15 n i₀ x e hi hinit htail
  exact lt_of_lt_of_le hsum (min_le_left _ _)

theorem gap17 :
    DarbouxIntegrableOn f 0 1 := by
  unfold DarbouxIntegrableOn
  intro ε hε
  obtain ⟨δ, hδ, hall⟩ := gap16 ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have hrecip : 0 < 1 / δ := by positivity
    linarith
  have hnN : 0 < n := by exact_mod_cast hnR
  have hmesh : 1 / (n : ℝ) < δ := by
    have hmul : 1 < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
    exact (div_lt_iff₀ hnR).2 (by simpa [mul_comm] using hmul)
  let x : ℕ → ℝ := fun i => (i : ℝ) / (n : ℝ)
  have hp : IsPartitionOn 0 1 n x := by
    constructor
    · simp [x]
    constructor
    · simp [x, ne_of_gt hnR]
    · intro i hi
      dsimp [x]
      apply (div_lt_div_iff_of_pos_right hnR).2
      exact_mod_cast Nat.lt_succ_self i
  refine ⟨n, x, hnN, hp, hall n x hp ?_⟩
  intro i hi
  have hw : width x i = 1 / (n : ℝ) := by
    dsimp [width, x]
    rw [Nat.cast_add, Nat.cast_one]
    field_simp [ne_of_gt hnR]
    ring
  rw [hw, abs_of_pos (by positivity)]
  exact hmesh

theorem gap18 :
    DarbouxIntegrableOn f 0 1 := by
  exact gap17

end
end ProofGap.Exercise2196
