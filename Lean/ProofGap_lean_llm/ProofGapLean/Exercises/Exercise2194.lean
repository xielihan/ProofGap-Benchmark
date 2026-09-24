import ProofGapLean.Prelude.Analysis
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Sign
import Mathlib.Topology.Instances.Sign
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2194
noncomputable section

open Filter
open scoped BigOperators

def f (x : ℝ) : ℝ :=
  SignType.sign (Real.sin (Real.pi / x))

def discontinuities : Set ℝ :=
  {x ∈ Set.Icc (0 : ℝ) 1 | ¬ ContinuousAt f x}

def oscillationOn (g : ℝ → ℝ) (I : Set ℝ) : ℝ :=
  sSup {r : ℝ | ∃ u ∈ I, ∃ v ∈ I, r = |g u - g v|}

def IsPartitionOn (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) : Prop :=
  x 0 = a ∧ x n = b ∧ ∀ i < n, x i < x (i + 1)

def width (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  x (i + 1) - x i

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
    x i₀ ≤ ε / 5 → ε / 5 < x (i₀ + 1) →
    Fine n x δ → tailSum f x i₀ n < ε / 5

private theorem f_mem_Icc (x : ℝ) : f x ∈ Set.Icc (-1 : ℝ) 1 := by
  unfold f
  rcases lt_trichotomy (Real.sin (Real.pi / x)) 0 with hneg | hzero | hpos
  · simp [sign_neg hneg]
  · simp [hzero]
  · simp [sign_pos hpos]

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

private theorem sin_recip_perturb_ne_zero (n : ℕ) (d : ℝ)
    (hd0 : 0 < d) (hd1 : d < 1) :
    Real.sin (Real.pi / (1 / ((n : ℝ) + d))) ≠ 0 := by
  have hden : 0 < (n : ℝ) + d := add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) hd0
  have hphase : Real.pi / (1 / ((n : ℝ) + d)) =
      ((n : ℝ) + d) * Real.pi := by
    field_simp [ne_of_gt hden]
  rw [hphase, Real.sin_ne_zero_iff]
  intro z hz
  have heq : (z : ℝ) = (n : ℝ) + d := by
    nlinarith [Real.pi_pos]
  have hlowR : (n : ℝ) < (z : ℝ) := by linarith
  have hhighR : (z : ℝ) < (n + 1 : ℕ) := by
    push_cast
    linarith
  have hlowZ : (n : ℤ) < z := by exact_mod_cast hlowR
  have hhighZ : z < (n : ℤ) + 1 := by exact_mod_cast hhighR
  omega

private def phaseJump (p q : ℝ) : ℝ :=
  ((Int.floor (1 / p) - Int.floor (1 / q) : ℤ) : ℝ) +
    ((Int.ceil (1 / p) - Int.ceil (1 / q) : ℤ) : ℝ)

private theorem reciprocal_index_between_of_f_ne {p q u v : ℝ}
    (hp : 0 < p) (hpq : p < q)
    (hu : u ∈ Set.Icc p q) (hv : v ∈ Set.Icc p q)
    (hneq : f u ≠ f v) :
    ∃ k : ℤ, 1 / q ≤ (k : ℝ) ∧ (k : ℝ) ≤ 1 / p := by
  let su := Real.sin (Real.pi / u)
  let sv := Real.sin (Real.pi / v)
  have hsign : SignType.sign su ≠ SignType.sign sv := by
    intro h
    apply hneq
    unfold f
    change (SignType.sign su : ℝ) = (SignType.sign sv : ℝ)
    rw [h]
  have hzero : (0 : ℝ) ∈ Set.uIcc su sv := by
    by_cases hu0 : su = 0
    · rw [hu0]
      exact Set.left_mem_uIcc
    by_cases hv0 : sv = 0
    · rw [hv0]
      exact Set.right_mem_uIcc
    rcases lt_or_gt_of_ne hu0 with huNeg | huPos
    · rcases lt_or_gt_of_ne hv0 with hvNeg | hvPos
      · exact (hsign (by rw [sign_neg huNeg, sign_neg hvNeg])).elim
      · exact Set.mem_uIcc_of_le huNeg.le hvPos.le
    · rcases lt_or_gt_of_ne hv0 with hvNeg | hvPos
      · exact Set.mem_uIcc_of_ge hvNeg.le huPos.le
      · exact (hsign (by rw [sign_pos huPos, sign_pos hvPos])).elim
  obtain ⟨z, hzmem, hzsin⟩ :=
    (intermediate_value_uIcc Real.continuous_sin.continuousOn) hzero
  obtain ⟨k, hkz⟩ := Real.sin_eq_zero_iff.mp hzsin
  have huPos : 0 < u := lt_of_lt_of_le hp hu.1
  have hvPos : 0 < v := lt_of_lt_of_le hp hv.1
  have hqPos : 0 < q := hp.trans hpq
  have hphaseU : Real.pi / u ∈ Set.Icc (Real.pi / q) (Real.pi / p) := by
    constructor
    · exact div_le_div_of_nonneg_left Real.pi_pos.le huPos (hu.2)
    · exact div_le_div_of_nonneg_left Real.pi_pos.le hp hu.1
  have hphaseV : Real.pi / v ∈ Set.Icc (Real.pi / q) (Real.pi / p) := by
    constructor
    · exact div_le_div_of_nonneg_left Real.pi_pos.le hvPos hv.2
    · exact div_le_div_of_nonneg_left Real.pi_pos.le hp hv.1
  have hzI : z ∈ Set.Icc (Real.pi / q) (Real.pi / p) :=
    Set.uIcc_subset_Icc hphaseU hphaseV hzmem
  refine ⟨k, ?_, ?_⟩
  · rw [← mul_le_mul_iff_right₀ Real.pi_pos]
    calc
      Real.pi * (1 / q) = Real.pi / q := by ring
      _ ≤ z := hzI.1
      _ = Real.pi * (k : ℝ) := by rw [← hkz]; ring
  · rw [← mul_le_mul_iff_right₀ Real.pi_pos]
    calc
      Real.pi * (k : ℝ) = z := by rw [← hkz]; ring
      _ ≤ Real.pi / p := hzI.2
      _ = Real.pi * (1 / p) := by ring

private theorem one_le_phaseJump {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    {k : ℤ} (hklo : 1 / q ≤ (k : ℝ)) (hkhi : (k : ℝ) ≤ 1 / p) :
    1 ≤ phaseJump p q := by
  have hdiv : 1 / q < 1 / p := one_div_lt_one_div_of_lt hp hpq
  have hfloorMono : Int.floor (1 / q) ≤ Int.floor (1 / p) :=
    Int.floor_mono hdiv.le
  have hceilMono : Int.ceil (1 / q) ≤ Int.ceil (1 / p) :=
    Int.ceil_mono hdiv.le
  by_cases heq : (k : ℝ) = 1 / q
  · have hklt : (k : ℝ) < 1 / p := by linarith
    have hkceil : k < Int.ceil (1 / p) := (Int.lt_ceil).2 hklt
    have hqceil : Int.ceil (1 / q) = k := by
      rw [← heq]
      simp
    unfold phaseJump
    push_cast
    exact_mod_cast (show (1 : ℤ) ≤
      (Int.floor (1 / p) - Int.floor (1 / q)) +
        (Int.ceil (1 / p) - Int.ceil (1 / q)) by omega)
  · have hklostrict : 1 / q < (k : ℝ) := lt_of_le_of_ne hklo (Ne.symm heq)
    have hqfloor : Int.floor (1 / q) < k := (Int.floor_lt).2 hklostrict
    have hkfloor : k ≤ Int.floor (1 / p) := (Int.le_floor).2 hkhi
    unfold phaseJump
    push_cast
    exact_mod_cast (show (1 : ℤ) ≤
      (Int.floor (1 / p) - Int.floor (1 / q)) +
        (Int.ceil (1 / p) - Int.ceil (1 / q)) by omega)

private theorem phaseJump_nonneg {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    0 ≤ phaseJump p q := by
  have hdiv : 1 / q ≤ 1 / p := one_div_le_one_div_of_le hp hpq
  have hf := Int.floor_mono hdiv
  have hc := Int.ceil_mono hdiv
  unfold phaseJump
  push_cast
  exact_mod_cast (show (0 : ℤ) ≤
    (Int.floor (1 / p) - Int.floor (1 / q)) +
      (Int.ceil (1 / p) - Int.ceil (1 / q)) by omega)

private theorem point_oscillation_phase_bound {p q u v : ℝ}
    (hp : 0 < p) (hpq : p < q)
    (hu : u ∈ Set.Icc p q) (hv : v ∈ Set.Icc p q) :
    |f u - f v| ≤ 2 * phaseJump p q := by
  by_cases hEq : f u = f v
  · rw [hEq, sub_self, abs_zero]
    have hjump : 0 ≤ phaseJump p q := phaseJump_nonneg hp hpq.le
    linarith
  · obtain ⟨k, hklo, hkhi⟩ :=
      reciprocal_index_between_of_f_ne hp hpq hu hv hEq
    have hjump := one_le_phaseJump hp hpq hklo hkhi
    rcases f_mem_Icc u with ⟨hu0, hu1⟩
    rcases f_mem_Icc v with ⟨hv0, hv1⟩
    have habs : |f u - f v| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith
    linarith

private theorem oscillation_cell_phase_bound {p q : ℝ}
    (hp : 0 < p) (hpq : p < q) :
    oscillationOn f (Set.Icc p q) ≤ 2 * phaseJump p q := by
  unfold oscillationOn
  apply csSup_le
  · exact ⟨0, p, ⟨le_rfl, hpq.le⟩, p, ⟨le_rfl, hpq.le⟩, by simp⟩
  · rintro r ⟨u, hu, v, hv, rfl⟩
    exact point_oscillation_phase_bound hp hpq hu hv

private theorem sum_diff_range (g : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m, (g i - g (i + 1))) = g 0 - g m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring

private theorem sum_diff_Ico (g : ℕ → ℝ) {l n : ℕ} (hln : l ≤ n) :
    (∑ i ∈ Finset.Ico l n, (g i - g (i + 1))) = g l - g n := by
  rw [Finset.sum_Ico_eq_sub _ hln, sum_diff_range, sum_diff_range]
  ring

private theorem sum_phaseJump_Ico (x : ℕ → ℝ) {l n : ℕ} (hln : l ≤ n) :
    (∑ i ∈ Finset.Ico l n, phaseJump (x i) (x (i + 1))) =
      ((Int.floor (1 / x l) - Int.floor (1 / x n) : ℤ) : ℝ) +
        ((Int.ceil (1 / x l) - Int.ceil (1 / x n) : ℤ) : ℝ) := by
  simp only [phaseJump, Int.cast_sub]
  rw [Finset.sum_add_distrib,
    sum_diff_Ico (fun i => (Int.floor (1 / x i) : ℝ)) hln,
    sum_diff_Ico (fun i => (Int.ceil (1 / x i) : ℝ)) hln]

private theorem controlled_sum_Ico (a : ℝ) (n : ℕ) (x : ℕ → ℝ)
    (l : ℕ) (δ : ℝ)
    (ha : 0 < a) (hδ : 0 ≤ δ) (hp : IsPartitionOn (x 0) 1 n x)
    (hal : a ≤ x l) (hln : l ≤ n) (hfine : Fine n x δ) :
    (∑ i ∈ Finset.Ico l n, omega f x i * width x i) ≤ δ * (4 / a) := by
  have hterm : ∀ i ∈ Finset.Ico l n,
      omega f x i * width x i ≤ 2 * δ * phaseJump (x i) (x (i + 1)) := by
    intro i hi
    have hil : l ≤ i := (Finset.mem_Ico.mp hi).1
    have hin : i < n := (Finset.mem_Ico.mp hi).2
    have hxi : a ≤ x i := hal.trans
      (partition_le_on hp hil (le_of_lt hin))
    have hinc : x i < x (i + 1) := hp.2.2 i hin
    have homega : omega f x i ≤ 2 * phaseJump (x i) (x (i + 1)) := by
      simpa [omega] using oscillation_cell_phase_bound (lt_of_lt_of_le ha hxi) hinc
    have hw0 : 0 ≤ width x i := sub_nonneg.mpr hinc.le
    have hwδ : width x i ≤ δ := by
      have hiFine := hfine i hin
      rw [abs_of_nonneg hw0] at hiFine
      exact hiFine.le
    have hjump0 : 0 ≤ phaseJump (x i) (x (i + 1)) :=
      phaseJump_nonneg (lt_of_lt_of_le ha hxi) hinc.le
    calc
      omega f x i * width x i ≤
          (2 * phaseJump (x i) (x (i + 1))) * width x i :=
        mul_le_mul_of_nonneg_right homega hw0
      _ ≤ (2 * phaseJump (x i) (x (i + 1))) * δ :=
        mul_le_mul_of_nonneg_left hwδ (mul_nonneg (by norm_num) hjump0)
      _ = 2 * δ * phaseJump (x i) (x (i + 1)) := by ring
  have hsum := Finset.sum_le_sum hterm
  have hrewrite :
      (∑ i ∈ Finset.Ico l n, 2 * δ * phaseJump (x i) (x (i + 1))) =
        2 * δ *
          (((Int.floor (1 / x l) - Int.floor (1 / x n) : ℤ) : ℝ) +
            ((Int.ceil (1 / x l) - Int.ceil (1 / x n) : ℤ) : ℝ)) := by
    rw [← Finset.mul_sum, sum_phaseJump_Ico x hln]
  rw [hrewrite] at hsum
  have hxlpos : 0 < x l := lt_of_lt_of_le ha hal
  have hdiv : 1 / x l ≤ 1 / a := one_div_le_one_div_of_le ha hal
  have hfloor : ((Int.floor (1 / x l) : ℤ) : ℝ) ≤ 1 / x l := Int.floor_le _
  have hceilFloor : Int.ceil (1 / x l) ≤ Int.floor (1 / x l) + 1 :=
    Int.ceil_le_floor_add_one _
  have hceilFloorR : ((Int.ceil (1 / x l) : ℤ) : ℝ) ≤
      (Int.floor (1 / x l) : ℝ) + 1 := by exact_mod_cast hceilFloor
  have hcastBound :
      (Int.floor (1 / x l) : ℝ) - 1 +
        ((Int.ceil (1 / x l) : ℤ) : ℝ) - 1 ≤ 2 / a := by
    rw [show 2 / a = 2 * (1 / a) by ring]
    linarith
  have hinside :
      ((Int.floor (1 / x l) - Int.floor (1 / x n) : ℤ) : ℝ) +
        ((Int.ceil (1 / x l) - Int.ceil (1 / x n) : ℤ) : ℝ) ≤ 2 / a := by
    rw [hp.2.1]
    norm_num
    push_cast
    convert hcastBound using 1 <;> ring
  calc
    (∑ i ∈ Finset.Ico l n, omega f x i * width x i) ≤
        2 * δ *
          (((Int.floor (1 / x l) - Int.floor (1 / x n) : ℤ) : ℝ) +
            ((Int.ceil (1 / x l) - Int.ceil (1 / x n) : ℤ) : ℝ)) := hsum
    _ ≤ 2 * δ * (2 / a) :=
      mul_le_mul_of_nonneg_left hinside (mul_nonneg (by norm_num) hδ)
    _ = δ * (4 / a) := by ring

theorem gap1 :
    Bornology.IsBounded (f '' Set.Icc (0 : ℝ) 1) := by
  refine (Metric.isBounded_Icc (-1 : ℝ) 1).subset ?_
  rintro y ⟨x, hx, rfl⟩
  exact f_mem_Icc x

theorem gap2 :
    discontinuities =
      ({0} : Set ℝ) ∪
        {x : ℝ | ∃ n : ℕ, 0 < n ∧ x = 1 / (n : ℝ)} := by
  classical
  ext x
  constructor
  · rintro ⟨hxI, hxdisc⟩
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      have hxpos : 0 < x := lt_of_le_of_ne hxI.1 (Ne.symm hx0)
      have hsin : Real.sin (Real.pi / x) = 0 := by
        by_contra hs
        apply hxdisc
        have hdiv : ContinuousAt (fun y : ℝ => Real.pi / y) x :=
          continuousAt_const.div continuousAt_id hx0
        have hinner : ContinuousAt (fun y : ℝ => Real.sin (Real.pi / y)) x :=
          Real.continuous_sin.continuousAt.comp hdiv
        have hsign : ContinuousAt
            (fun y : ℝ => SignType.sign (Real.sin (Real.pi / y))) x :=
          ContinuousAt.comp' (f := fun y : ℝ => Real.sin (Real.pi / y))
            (continuousAt_sign_of_ne_zero hs) hinner
        have hcoe : Continuous (fun s : SignType => (s : ℝ)) :=
          continuous_of_discreteTopology
        simpa [f, Function.comp_def] using hcoe.continuousAt.comp' hsign
      obtain ⟨z, hz⟩ := Real.sin_eq_zero_iff.mp hsin
      have hzval : (z : ℝ) = 1 / x := by
        apply mul_right_cancel₀ (ne_of_gt Real.pi_pos)
        calc
          (z : ℝ) * Real.pi = Real.pi / x := hz
          _ = (1 / x) * Real.pi := by ring
      have hzpos : 0 < z := by
        exact_mod_cast (show (0 : ℝ) < (z : ℝ) by rw [hzval]; positivity)
      obtain ⟨n, hzn⟩ := Int.eq_ofNat_of_zero_le hzpos.le
      have hn : 0 < n := by
        exact_mod_cast (show (0 : ℤ) < (n : ℤ) by rw [← hzn]; exact hzpos)
      have hznR : (z : ℝ) = (n : ℝ) := by exact_mod_cast hzn
      refine ⟨n, hn, ?_⟩
      apply (eq_div_iff (by positivity : (n : ℝ) ≠ 0)).2
      rw [← hznR, hzval]
      field_simp [hx0]
  · rintro (hx0 | hrecip)
    · subst x
      constructor
      · constructor <;> norm_num
      · rw [Metric.continuousAt_iff]
        push_neg
        refine ⟨1 / 2, by norm_num, ?_⟩
        intro δ hδ
        obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / δ) 1)
        have hnR : (1 : ℝ) < n := lt_of_le_of_lt (le_max_right _ _) hn
        let d : ℝ := 1 / 2
        let y : ℝ := 1 / ((n : ℝ) + d)
        have hd0 : 0 < d := by norm_num [d]
        have hd1 : d < 1 := by norm_num [d]
        have hden : 0 < (n : ℝ) + d := by positivity
        have hypos : 0 < y := by dsimp [y]; positivity
        have hny : y < 1 / (n : ℝ) := by
          dsimp [y]
          exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
        have hnδ : 1 / (n : ℝ) < δ := by
          apply (div_lt_iff₀ (by linarith : (0 : ℝ) < n)).2
          have hnd : 1 / δ < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
          have hmul := (div_lt_iff₀ hδ).1 hnd
          simpa [mul_comm] using hmul
        have hydist : dist y 0 < δ := by
          rw [Real.dist_eq, sub_zero, abs_of_pos hypos]
          exact hny.trans hnδ
        have hsin := sin_recip_perturb_ne_zero n d hd0 hd1
        refine ⟨y, hydist, ?_⟩
        have hf0 : f 0 = 0 := by norm_num [f]
        rcases hsin.lt_or_gt with hneg | hpos
        · rw [hf0, f, sign_neg hneg, Real.dist_eq]
          norm_num
        · rw [hf0, f, sign_pos hpos, Real.dist_eq]
          norm_num
    · obtain ⟨n, hn, rfl⟩ := hrecip
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hbasePhase : Real.pi / (1 / (n : ℝ)) = (n : ℝ) * Real.pi := by
        field_simp [ne_of_gt hnR]
      have hfbase : f (1 / (n : ℝ)) = 0 := by
        unfold f
        rw [hbasePhase, Real.sin_nat_mul_pi, sign_zero]
        rfl
      constructor
      · constructor
        · positivity
        · exact (div_le_one hnR).2 (by exact_mod_cast hn)
      · rw [Metric.continuousAt_iff]
        push_neg
        refine ⟨1 / 2, by norm_num, ?_⟩
        intro δ hδ
        have hg : ContinuousAt
            (fun d : ℝ => 1 / ((n : ℝ) + d)) 0 := by
          exact continuousAt_const.div (continuousAt_const.add continuousAt_id)
            (by simpa using ne_of_gt hnR)
        obtain ⟨η, hη, hclose⟩ := (Metric.continuousAt_iff.mp hg) δ hδ
        let d : ℝ := min (η / 2) (1 / 2)
        have hd0 : 0 < d := by
          dsimp [d]
          exact lt_min (by positivity) (by norm_num)
        have hd1 : d < 1 := by
          calc
            d ≤ 1 / 2 := min_le_right _ _
            _ < 1 := by norm_num
        have hddist : dist d 0 < η := by
          rw [Real.dist_eq, sub_zero, abs_of_pos hd0]
          exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
        let y : ℝ := 1 / ((n : ℝ) + d)
        have hydist : dist y (1 / (n : ℝ)) < δ := by
          simpa [y] using hclose hddist
        have hsin := sin_recip_perturb_ne_zero n d hd0 hd1
        refine ⟨y, hydist, ?_⟩
        rcases hsin.lt_or_gt with hneg | hpos
        · rw [hfbase, f, sign_neg hneg, Real.dist_eq]
          norm_num
        · rw [hfbase, f, sign_pos hpos, Real.dist_eq]
          norm_num

theorem gap3 (I : Set ℝ) (hI : I ⊆ Set.Icc (0 : ℝ) 1) :
    oscillationOn f I ≤ 2 := by
  classical
  by_cases hne : I.Nonempty
  · unfold oscillationOn
    apply csSup_le
    · obtain ⟨u, hu⟩ := hne
      exact ⟨0, u, hu, u, hu, by simp⟩
    · rintro r ⟨u, hu, v, hv, rfl⟩
      rcases f_mem_Icc u with ⟨hu0, hu1⟩
      rcases f_mem_Icc v with ⟨hv0, hv1⟩
      rw [abs_le]
      constructor <;> linarith
  · have hIempty : I = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [oscillationOn, hIempty]

theorem gap4 (ε : ℝ) (hε : 0 < ε) (hε5 : ε < 5) :
    DarbouxIntegrableOn f (ε / 5) 1 := by
  classical
  unfold DarbouxIntegrableOn
  intro η hη
  let a := ε / 5
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos hε (by norm_num)
  have ha1 : a < 1 := by
    dsimp [a]
    linarith
  let d := η * a / 8
  have hd : 0 < d := by
    dsimp [d]
    exact div_pos (mul_pos hη ha) (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_gt ((1 - a) / d)
  have hquot : 0 < (1 - a) / d := div_pos (sub_pos.mpr ha1) hd
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
    have hwpos : 0 < (1 - a) / (n : ℝ) := div_pos (sub_pos.mpr ha1) hnR
    rw [hw, abs_of_pos hwpos]
    apply (div_lt_iff₀ hnR).2
    have hprod := (div_lt_iff₀ hd).1 hn
    simpa [mul_comm] using hprod
  have hx0 : x 0 = a := by simp [x]
  have hp' : IsPartitionOn (x 0) 1 n x := by
    rw [hx0]
    exact hp
  have hbound := controlled_sum_Ico a n x 0 d ha hd.le hp'
    (by rw [hx0]) (Nat.zero_le n) hfine
  refine ⟨n, x, hnN, hp, ?_⟩
  have hcalc : d * (4 / a) = η / 2 := by
    dsimp [d]
    field_simp [ne_of_gt ha] <;> ring
  rw [hcalc] at hbound
  simpa [oscillationSum] using lt_of_le_of_lt hbound (by linarith)

theorem gap5 (ε : ℝ) (hε : 0 < ε) (hε5 : ε < 5) :
    ∃ δ > 0, TailControlled ε δ := by
  classical
  let a := ε / 5
  let δ := ε * a / 40
  have ha : 0 < a := by dsimp [a]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro n x i₀ hi hp hleft hright hfine
  unfold tailSum
  have hl : i₀ + 1 ≤ n := by omega
  have hp' : IsPartitionOn (x 0) 1 n x := by simpa [hp.1] using hp
  have hbound := controlled_sum_Ico a n x (i₀ + 1) δ ha hδ.le hp'
    hright.le hl hfine
  have hcalc : δ * (4 / a) = ε / 10 := by
    dsimp [δ]
    field_simp [ne_of_gt ha] <;> ring
  rw [hcalc] at hbound
  exact lt_of_le_of_lt hbound (by linarith)

theorem gap6 (n : ℕ) (x : ℕ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hε5 : ε < 5)
    (hp : IsPartitionOn 0 1 n x) :
    ∃ i₀ < n, x i₀ ≤ ε / 5 := by
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    linarith [hp.1, hp.2.1]
  refine ⟨0, hn, ?_⟩
  rw [hp.1]
  linarith

theorem gap7 (n : ℕ) (x : ℕ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hε5 : ε < 5)
    (hp : IsPartitionOn 0 1 n x) :
    ∃ i₀ < n, x i₀ ≤ ε / 5 ∧ ε / 5 < x (i₀ + 1) := by
  classical
  have hex : ∃ k : ℕ, ε / 5 < x k := by
    refine ⟨n, ?_⟩
    rw [hp.2.1]
    linarith
  let k := Nat.find hex
  have hk : ε / 5 < x k := by
    simpa [k] using Nat.find_spec hex
  have hkn : k ≤ n := by
    simpa [k] using Nat.find_min' hex
      (show ε / 5 < x n by rw [hp.2.1]; linarith)
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos h
    rw [hk0, hp.1] at hk
    linarith
  have hleft : x (k - 1) ≤ ε / 5 := by
    by_contra h
    have hgt : ε / 5 < x (k - 1) := lt_of_not_ge h
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
    (hleft : x i₀ ≤ ε / 5) (hright : ε / 5 < x (i₀ + 1))
    (hfine : Fine n x δ) (hcontrol : TailControlled ε δ) :
    tailSum f x i₀ n < ε / 5 := by
  exact hcontrol n x i₀ hi hp hleft hright hfine

theorem gap10 (n i₀ : ℕ) (x : ℕ → ℝ)
    (hp : IsPartitionOn 0 1 n x) (hi : i₀ < n) :
    initialSum f x i₀ ≤
      2 * ∑ i ∈ Finset.range (i₀ + 1), width x i := by
  unfold initialSum
  rw [Finset.mul_sum]
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
  have homega : omega f x i ≤ 2 := by
    simpa [omega] using gap3 (Set.Icc (x i) (x (i + 1))) hsubset
  simpa [mul_assoc] using mul_le_mul_of_nonneg_right homega hwidth

theorem gap11 (n i₀ : ℕ) (x : ℕ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hp : IsPartitionOn 0 1 n x) (hi : i₀ < n)
    (hleft : x i₀ ≤ ε / 5) (hright : ε / 5 < x (i₀ + 1))
    (hfine : Fine n x (ε / 5)) :
    2 * (∑ i ∈ Finset.range (i₀ + 1), width x i) <
      2 * (2 * ε / 5) := by
  rw [sum_width, hp.1]
  have hw := hfine i₀ hi
  rw [abs_lt] at hw
  dsimp [width] at hw
  linarith

theorem gap12 (ε : ℝ) :
    2 * (2 * ε / 5) = 4 * ε / 5 := by
  ring

theorem gap13 (n i₀ : ℕ) (x : ℕ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hp : IsPartitionOn 0 1 n x) (hi : i₀ < n)
    (hleft : x i₀ ≤ ε / 5) (hright : ε / 5 < x (i₀ + 1))
    (hfine : Fine n x (ε / 5)) :
    initialSum f x i₀ < 4 * ε / 5 := by
  have hbound := lt_of_le_of_lt (gap10 n i₀ x hp hi)
    (gap11 n i₀ x ε hε hp hi hleft hright hfine)
  rw [gap12 ε] at hbound
  exact hbound

theorem gap14 (n i₀ : ℕ) (x : ℕ → ℝ) (hi : i₀ < n) :
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

theorem gap15 (n i₀ : ℕ) (x : ℕ → ℝ) (ε : ℝ)
    (hε : 0 < ε)
    (hinit : initialSum f x i₀ < 4 * ε / 5)
    (htail : tailSum f x i₀ n < ε / 5) :
    initialSum f x i₀ + tailSum f x i₀ n < ε := by
  linarith

theorem gap16 (n i₀ : ℕ) (x : ℕ → ℝ) (ε : ℝ)
    (hi : i₀ < n)
    (hinit : initialSum f x i₀ < 4 * ε / 5)
    (htail : tailSum f x i₀ n < ε / 5) :
    oscillationSum f n x < ε := by
  rw [gap14 n i₀ x hi]
  linarith

theorem gap17 :
    ∀ ε > 0, ∃ δ > 0, ∀ n : ℕ, ∀ x : ℕ → ℝ,
      IsPartitionOn 0 1 n x → Fine n x δ →
        oscillationSum f n x < ε := by
  intro ε hε
  let e : ℝ := min ε 1
  have he : 0 < e := by
    dsimp [e]
    exact lt_min hε zero_lt_one
  have he5 : e < 5 := by
    calc
      e ≤ 1 := min_le_right _ _
      _ < 5 := by norm_num
  obtain ⟨d, hd, hcontrol⟩ := gap5 e he he5
  refine ⟨min d (e / 5), lt_min hd (by positivity), ?_⟩
  intro n x hp hfine
  have hfineD : Fine n x d := fine_mono hfine (min_le_left _ _)
  have hfineE : Fine n x (e / 5) := fine_mono hfine (min_le_right _ _)
  obtain ⟨i₀, hi, hleft, hright⟩ := gap7 n x e he he5 hp
  have htail : tailSum f x i₀ n < e / 5 :=
    gap9 n i₀ x e d hi hp hleft hright hfineD hcontrol
  have hinit : initialSum f x i₀ < 4 * e / 5 :=
    gap13 n i₀ x e he hp hi hleft hright hfineE
  have hsum : oscillationSum f n x < e :=
    gap16 n i₀ x e hi hinit htail
  exact lt_of_lt_of_le hsum (min_le_left _ _)

theorem gap18 :
    DarbouxIntegrableOn f 0 1 := by
  unfold DarbouxIntegrableOn
  intro ε hε
  obtain ⟨δ, hδ, hall⟩ := gap17 ε hε
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

theorem gap19 :
    DarbouxIntegrableOn f 0 1 := by
  exact gap18

end
end ProofGap.Exercise2194
