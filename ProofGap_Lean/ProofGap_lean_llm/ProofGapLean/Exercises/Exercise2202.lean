import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2202
noncomputable section

open scoped BigOperators

def oscillationOn (g : ℝ → ℝ) (I : Set ℝ) : ℝ :=
  sSup {r : ℝ | ∃ u ∈ I, ∃ v ∈ I, r = |g u - g v|}

def IsPartitionOn (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) : Prop :=
  x 0 = a ∧ x n = b ∧ ∀ i < n, x i < x (i + 1)

def width (x : ℕ → ℝ) (i : ℕ) : ℝ := x (i + 1) - x i

def Fine (n : ℕ) (x : ℕ → ℝ) (δ : ℝ) : Prop :=
  ∀ i < n, width x i < δ

def omega (g : ℝ → ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  oscillationOn g (Set.Icc (x i) (x (i + 1)))

def oscillationSum (g : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, omega g x i * width x i

def RiemannIntegrableOn (g : ℝ → ℝ) (a b : ℝ) : Prop :=
  Bornology.IsBounded (g '' Set.Icc a b) ∧
    ∀ ε > 0, ∃ δ > 0, ∀ n : ℕ, ∀ x : ℕ → ℝ,
      IsPartitionOn a b n x → Fine n x δ →
        oscillationSum g n x < ε

def goodIndices (f : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (η : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun i => omega f x i < η)

def badIndices (f : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (η : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun i => η ≤ omega f x i)

def goodCompSum (φ f : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (η : ℝ) : ℝ :=
  ∑ i ∈ goodIndices f n x η, omega (φ ∘ f) x i * width x i

def badCompSum (φ f : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (η : ℝ) : ℝ :=
  ∑ i ∈ badIndices f n x η, omega (φ ∘ f) x i * width x i

def badLength (f : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (η : ℝ) : ℝ :=
  ∑ i ∈ badIndices f n x η, width x i

theorem gap1 (φ : ℝ → ℝ) (A B ε : ℝ)
    (hφ : ContinuousOn φ (Set.Icc A B)) (hε : 0 < ε) :
    UniformContinuousOn φ (Set.Icc A B) := by
  exact isCompact_Icc.uniformContinuousOn_of_continuous hφ

theorem gap2 (φ : ℝ → ℝ) (A B a b ε : ℝ)
    (hAB : A ≤ B) (hab : a < b)
    (hφ : ContinuousOn φ (Set.Icc A B)) (hε : 0 < ε) :
    ∃ η > 0, ∀ u ∈ Set.Icc A B, ∀ v ∈ Set.Icc A B,
      |u - v| < η → |φ u - φ v| < ε / (2 * (b - a)) := by
  have htarget : 0 < ε / (2 * (b - a)) := by
    exact div_pos hε (mul_pos (by norm_num) (sub_pos.mpr hab))
  rcases Metric.uniformContinuousOn_iff.mp (gap1 φ A B ε hφ hε)
      (ε / (2 * (b - a))) htarget with ⟨η, hη, hmod⟩
  refine ⟨η, hη, ?_⟩
  intro u hu v hv huv
  have hout := hmod u hu v hv
  simpa [Real.dist_eq] using hout (by simpa [Real.dist_eq] using huv)

theorem gap3 (f : ℝ → ℝ) (a b η Ω ε : ℝ)
    (hab : a < b) (hη : 0 < η) (hΩ : 0 < Ω) (hε : 0 < ε)
    (hf : RiemannIntegrableOn f a b) :
    ∃ δ > 0, ∀ n : ℕ, ∀ x : ℕ → ℝ,
      IsPartitionOn a b n x → Fine n x δ →
        oscillationSum f n x < η * ε / (2 * Ω) := by
  exact hf.2 (η * ε / (2 * Ω)) (by positivity)

theorem gap4 (φ f : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (η : ℝ) :
    oscillationSum (φ ∘ f) n x =
      goodCompSum φ f n x η + badCompSum φ f n x η := by
  classical
  unfold oscillationSum goodCompSum badCompSum goodIndices badIndices
  symm
  simpa only [not_lt] using
    (Finset.sum_filter_add_sum_filter_not (Finset.range n)
      (fun i => omega f x i < η)
      (fun i => omega (φ ∘ f) x i * width x i))

theorem gap6 (f : ℝ → ℝ) (a b η Ω ε δ : ℝ)
    (n : ℕ) (x : ℕ → ℝ)
    (hη : 0 < η) (hΩ : 0 < Ω)
    (hcontrol : ∀ n : ℕ, ∀ x : ℕ → ℝ,
      IsPartitionOn a b n x → Fine n x δ →
        oscillationSum f n x < η * ε / (2 * Ω))
    (hp : IsPartitionOn a b n x) (hfine : Fine n x δ) :
    oscillationSum f n x < η * ε / (2 * Ω) := by
  exact hcontrol n x hp hfine

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

private theorem cell_subset_partition_interval {a b : ℝ} {n i : ℕ}
    {x : ℕ → ℝ} (hp : IsPartitionOn a b n x) (hi : i < n) :
    Set.Icc (x i) (x (i + 1)) ⊆ Set.Icc a b := by
  rintro y ⟨hiy, hyi⟩
  constructor
  · calc
      a = x 0 := hp.1.symm
      _ ≤ x i := partition_le_on hp (Nat.zero_le i) (by omega)
      _ ≤ y := hiy
  · calc
      y ≤ x (i + 1) := hyi
      _ ≤ x n := partition_le_on hp (by omega) le_rfl
      _ = b := hp.2.1

private theorem sum_width (x : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m, width x i) = x m - x 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [width]
      ring

private theorem oscillationOn_nonneg (g : ℝ → ℝ) (I : Set ℝ) :
    0 ≤ oscillationOn g I := by
  unfold oscillationOn
  apply Real.sSup_nonneg
  rintro r ⟨u, hu, v, hv, rfl⟩
  exact abs_nonneg _

private theorem oscillationOn_le_of_pair_bound
    (g : ℝ → ℝ) (I : Set ℝ) (M : ℝ) (hI : I.Nonempty)
    (hbound : ∀ u ∈ I, ∀ v ∈ I, |g u - g v| ≤ M) :
    oscillationOn g I ≤ M := by
  unfold oscillationOn
  apply csSup_le
  · obtain ⟨u, hu⟩ := hI
    exact ⟨0, u, hu, u, hu, by simp⟩
  · rintro r ⟨u, hu, v, hv, rfl⟩
    exact hbound u hu v hv

private theorem pair_le_oscillationOn
    (g : ℝ → ℝ) (I : Set ℝ) (M : ℝ)
    (hbound : ∀ u ∈ I, ∀ v ∈ I, |g u - g v| ≤ M)
    {u v : ℝ} (hu : u ∈ I) (hv : v ∈ I) :
    |g u - g v| ≤ oscillationOn g I := by
  unfold oscillationOn
  apply le_csSup
  · exact ⟨M, by
      rintro r ⟨y, hy, z, hz, rfl⟩
      exact hbound y hy z hz⟩
  · exact ⟨u, hu, v, hv, rfl⟩

theorem gap7 (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) (η : ℝ)
    (hη : 0 ≤ η) (hp : IsPartitionOn a b n x) :
    η * badLength f n x η ≤ oscillationSum f n x := by
  classical
  unfold badLength badIndices oscillationSum
  rw [Finset.mul_sum]
  calc
    (∑ i ∈ (Finset.range n).filter (fun i => η ≤ omega f x i),
        η * width x i) ≤
        ∑ i ∈ (Finset.range n).filter (fun i => η ≤ omega f x i),
          omega f x i * width x i := by
      apply Finset.sum_le_sum
      intro i hi
      have hip := Finset.mem_filter.mp hi
      have hw : 0 ≤ width x i :=
        sub_nonneg.mpr (hp.2.2 i (Finset.mem_range.mp hip.1)).le
      exact mul_le_mul_of_nonneg_right hip.2 hw
    _ ≤ ∑ i ∈ Finset.range n, omega f x i * width x i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro i hi hiBad
      have hin : i < n := Finset.mem_range.mp hi
      exact mul_nonneg
        (by simpa [omega] using
          oscillationOn_nonneg f (Set.Icc (x i) (x (i + 1))))
        (sub_nonneg.mpr (hp.2.2 i hin).le)

theorem gap8 (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) (x : ℕ → ℝ)
    (η Ω ε : ℝ) (hη : 0 < η) (hΩ : 0 < Ω)
    (hp : IsPartitionOn a b n x)
    (hsmall : oscillationSum f n x < η * ε / (2 * Ω)) :
    badLength f n x η < ε / (2 * Ω) := by
  have hlt : η * badLength f n x η < η * (ε / (2 * Ω)) := by
    calc
      η * badLength f n x η ≤ oscillationSum f n x :=
        gap7 f a b n x η hη.le hp
      _ < η * ε / (2 * Ω) := hsmall
      _ = η * (ε / (2 * Ω)) := by ring
  nlinarith

theorem gap10 (a b Ω ε : ℝ)
    (hab : a < b) (hΩ : 0 < Ω) :
    ε / (2 * (b - a)) * (b - a) + Ω * (ε / (2 * Ω)) = ε := by
  field_simp [ne_of_gt (sub_pos.mpr hab), ne_of_gt hΩ]
  ring

theorem gap11 (φ f : ℝ → ℝ) (a b ε : ℝ)
    (hab : a < b) (hε : 0 < ε)
    (hsmall : ∃ δ > 0, ∀ n : ℕ, ∀ x : ℕ → ℝ,
      IsPartitionOn a b n x → Fine n x δ →
        oscillationSum (φ ∘ f) n x < ε) :
    ∃ δ > 0, ∀ n : ℕ, ∀ x : ℕ → ℝ,
      IsPartitionOn a b n x → Fine n x δ →
        oscillationSum (φ ∘ f) n x < ε := by
  exact hsmall

private theorem exists_positive_pair_bound
    (φ : ℝ → ℝ) (A B : ℝ) (hφ : ContinuousOn φ (Set.Icc A B)) :
    ∃ Ω > 0, ∀ u ∈ Set.Icc A B, ∀ v ∈ Set.Icc A B,
      |φ u - φ v| ≤ Ω := by
  have hb : Bornology.IsBounded (φ '' Set.Icc A B) :=
    (isCompact_Icc.image_of_continuousOn hφ).isBounded
  rcases (Metric.isBounded_iff_subset_ball (0 : ℝ)).mp hb with ⟨r, hr⟩
  let M : ℝ := max 1 r
  have hM : 0 < M := lt_max_of_lt_left zero_lt_one
  refine ⟨2 * M, mul_pos (by norm_num) hM, ?_⟩
  intro u hu v hv
  have huBall : φ u ∈ Metric.ball (0 : ℝ) r := hr ⟨u, hu, rfl⟩
  have hvBall : φ v ∈ Metric.ball (0 : ℝ) r := hr ⟨v, hv, rfl⟩
  have huM : |φ u| ≤ M := by
    have hur : |φ u| < r := by simpa [Real.dist_eq] using huBall
    exact (le_of_lt hur).trans (le_max_right 1 r)
  have hvM : |φ v| ≤ M := by
    have hvr : |φ v| < r := by simpa [Real.dist_eq] using hvBall
    exact (le_of_lt hvr).trans (le_max_right 1 r)
  calc
    |φ u - φ v| ≤ |φ u| + |φ v| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (φ u) (-φ v)
    _ ≤ M + M := add_le_add huM hvM
    _ = 2 * M := by ring

private theorem composition_oscillationSum_le
    (φ f : ℝ → ℝ) (A B a b η Ω ε : ℝ)
    (n : ℕ) (x : ℕ → ℝ)
    (hAB : A ≤ B) (hab : a < b) (hε : 0 < ε)
    (hp : IsPartitionOn a b n x)
    (hrange : ∀ t ∈ Set.Icc a b, f t ∈ Set.Icc A B)
    (hmod : ∀ u ∈ Set.Icc A B, ∀ v ∈ Set.Icc A B,
      |u - v| < η → |φ u - φ v| < ε / (2 * (b - a)))
    (hΩ : ∀ u ∈ Set.Icc A B, ∀ v ∈ Set.Icc A B,
      |φ u - φ v| ≤ Ω) :
    oscillationSum (φ ∘ f) n x ≤
      ε / (2 * (b - a)) * (b - a) + Ω * badLength f n x η := by
  classical
  let q : ℝ := ε / (2 * (b - a))
  have hq : 0 ≤ q := (div_pos hε (mul_pos (by norm_num) (sub_pos.mpr hab))).le
  have hcell (i : ℕ) (hi : i < n) :
      (Set.Icc (x i) (x (i + 1))).Nonempty :=
    ⟨x i, le_rfl, (hp.2.2 i hi).le⟩
  have hfPair (i : ℕ) (hi : i < n) :
      ∀ u ∈ Set.Icc (x i) (x (i + 1)),
        ∀ v ∈ Set.Icc (x i) (x (i + 1)), |f u - f v| ≤ B - A := by
    intro u hu v hv
    have hsub := cell_subset_partition_interval hp hi
    have hfu := hrange u (hsub hu)
    have hfv := hrange v (hsub hv)
    rw [abs_le]
    constructor <;> linarith [hfu.1, hfu.2, hfv.1, hfv.2]
  have hgoodOmega (i : ℕ) (hi : i < n) (hgood : omega f x i < η) :
      omega (φ ∘ f) x i ≤ q := by
    unfold omega
    apply oscillationOn_le_of_pair_bound _ _ q (hcell i hi)
    intro u hu v hv
    have hsub := cell_subset_partition_interval hp hi
    have hfu := hrange u (hsub hu)
    have hfv := hrange v (hsub hv)
    have huv : |f u - f v| ≤
        oscillationOn f (Set.Icc (x i) (x (i + 1))) :=
      pair_le_oscillationOn f _ (B - A) (hfPair i hi) hu hv
    have hout := hmod (f u) hfu (f v) hfv (huv.trans_lt hgood)
    simpa only [Function.comp_apply, q] using hout.le
  have hglobalOmega (i : ℕ) (hi : i < n) :
      omega (φ ∘ f) x i ≤ Ω := by
    unfold omega
    apply oscillationOn_le_of_pair_bound _ _ Ω (hcell i hi)
    intro u hu v hv
    have hsub := cell_subset_partition_interval hp hi
    simpa only [Function.comp_apply] using
      hΩ (f u) (hrange u (hsub hu)) (f v) (hrange v (hsub hv))
  have hgoodSum : goodCompSum φ f n x η ≤ q * (b - a) := by
    calc
      goodCompSum φ f n x η ≤
          ∑ i ∈ goodIndices f n x η, q * width x i := by
        apply Finset.sum_le_sum
        intro i hi
        have hip : i ∈ (Finset.range n).filter (fun j => omega f x j < η) := by
          simpa [goodIndices] using hi
        have hin : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hip).1
        have hw : 0 ≤ width x i := sub_nonneg.mpr (hp.2.2 i hin).le
        exact mul_le_mul_of_nonneg_right
          (hgoodOmega i hin (Finset.mem_filter.mp hip).2) hw
      _ ≤ ∑ i ∈ Finset.range n, q * width x i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · change (Finset.range n).filter (fun j => omega f x j < η) ⊆
            Finset.range n
          exact Finset.filter_subset _ _
        · intro i hi hiGood
          exact mul_nonneg hq
            (sub_nonneg.mpr (hp.2.2 i (Finset.mem_range.mp hi)).le)
      _ = q * (b - a) := by
        rw [← Finset.mul_sum, sum_width, hp.2.1, hp.1]
  have hbadSum : badCompSum φ f n x η ≤ Ω * badLength f n x η := by
    calc
      badCompSum φ f n x η ≤
          ∑ i ∈ badIndices f n x η, Ω * width x i := by
        apply Finset.sum_le_sum
        intro i hi
        have hip : i ∈ (Finset.range n).filter (fun j => η ≤ omega f x j) := by
          simpa [badIndices] using hi
        have hin : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hip).1
        have hw : 0 ≤ width x i := sub_nonneg.mpr (hp.2.2 i hin).le
        exact mul_le_mul_of_nonneg_right (hglobalOmega i hin) hw
      _ = Ω * badLength f n x η := by
        unfold badLength
        rw [Finset.mul_sum]
  calc
    oscillationSum (φ ∘ f) n x =
        goodCompSum φ f n x η + badCompSum φ f n x η := gap4 φ f n x η
    _ ≤ q * (b - a) + Ω * badLength f n x η :=
      add_le_add hgoodSum hbadSum
    _ = ε / (2 * (b - a)) * (b - a) +
        Ω * badLength f n x η := by rfl

theorem gap5 (φ f : ℝ → ℝ) (A B a b η Ω ε : ℝ)
    (n : ℕ) (x : ℕ → ℝ)
    (hab : a < b) (hε : 0 < ε)
    (hp : IsPartitionOn a b n x)
    (hrange : ∀ t ∈ Set.Icc a b, f t ∈ Set.Icc A B)
    (hmod : ∀ u ∈ Set.Icc A B, ∀ v ∈ Set.Icc A B,
      |u - v| < η → |φ u - φ v| < ε / (2 * (b - a)))
    (hΩ : ∀ u ∈ Set.Icc A B, ∀ v ∈ Set.Icc A B, |φ u - φ v| ≤ Ω) :
    oscillationSum (φ ∘ f) n x ≤
      ε / (2 * (b - a)) * (b - a) + Ω * badLength f n x η := by
  have hfa := hrange a ⟨le_rfl, hab.le⟩
  have hAB : A ≤ B := hfa.1.trans hfa.2
  exact composition_oscillationSum_le
    φ f A B a b η Ω ε n x hAB hab hε hp hrange hmod hΩ

theorem gap9 (φ f : ℝ → ℝ) (A B a b η Ω ε : ℝ)
    (n : ℕ) (x : ℕ → ℝ)
    (hab : a < b) (hε : 0 < ε) (hΩ : 0 < Ω)
    (hp : IsPartitionOn a b n x)
    (hrange : ∀ t ∈ Set.Icc a b, f t ∈ Set.Icc A B)
    (hmod : ∀ u ∈ Set.Icc A B, ∀ v ∈ Set.Icc A B,
      |u - v| < η → |φ u - φ v| < ε / (2 * (b - a)))
    (hbound : ∀ u ∈ Set.Icc A B, ∀ v ∈ Set.Icc A B, |φ u - φ v| ≤ Ω)
    (hbad : badLength f n x η < ε / (2 * Ω)) :
    oscillationSum (φ ∘ f) n x <
      ε / (2 * (b - a)) * (b - a) + Ω * (ε / (2 * Ω)) := by
  have hestimate :=
    gap5 φ f A B a b η Ω ε n x hab hε hp hrange hmod hbound
  have hbad' : Ω * badLength f n x η < Ω * (ε / (2 * Ω)) :=
    mul_lt_mul_of_pos_left hbad hΩ
  linarith

theorem gap12 (φ f : ℝ → ℝ) (A B a b : ℝ)
    (hAB : A ≤ B) (hab : a < b)
    (hφ : ContinuousOn φ (Set.Icc A B))
    (hf : RiemannIntegrableOn f a b)
    (hrange : ∀ x ∈ Set.Icc a b, f x ∈ Set.Icc A B) :
    RiemannIntegrableOn (φ ∘ f) a b := by
  have hφBound : Bornology.IsBounded (φ '' Set.Icc A B) :=
    (isCompact_Icc.image_of_continuousOn hφ).isBounded
  have hcompBound : Bornology.IsBounded ((φ ∘ f) '' Set.Icc a b) := by
    apply hφBound.subset
    rintro y ⟨t, ht, rfl⟩
    exact ⟨f t, hrange t ht, rfl⟩
  refine ⟨hcompBound, ?_⟩
  intro ε hε
  obtain ⟨Ω, hΩ, hΩbound⟩ := exists_positive_pair_bound φ A B hφ
  obtain ⟨η, hη, hmod⟩ := gap2 φ A B a b ε hAB hab hφ hε
  obtain ⟨δ, hδ, hcontrol⟩ := gap3 f a b η Ω ε hab hη hΩ hε hf
  refine ⟨δ, hδ, ?_⟩
  intro n x hp hfine
  have hsmall := hcontrol n x hp hfine
  have hbad := gap8 f a b n x η Ω ε hη hΩ hp hsmall
  have hestimate := composition_oscillationSum_le
    φ f A B a b η Ω ε n x hAB hab hε hp hrange hmod hΩbound
  have hbad' : Ω * badLength f n x η < Ω * (ε / (2 * Ω)) :=
    mul_lt_mul_of_pos_left hbad hΩ
  calc
    oscillationSum (φ ∘ f) n x ≤
        ε / (2 * (b - a)) * (b - a) +
          Ω * badLength f n x η := hestimate
    _ < ε / (2 * (b - a)) * (b - a) +
          Ω * (ε / (2 * Ω)) := by linarith
    _ = ε := gap10 a b Ω ε hab hΩ

theorem gap13 (φ f : ℝ → ℝ) (A B a b : ℝ)
    (hAB : A ≤ B) (hab : a < b)
    (hφ : ContinuousOn φ (Set.Icc A B))
    (hf : RiemannIntegrableOn f a b)
    (hrange : ∀ x ∈ Set.Icc a b, f x ∈ Set.Icc A B) :
    RiemannIntegrableOn (φ ∘ f) a b := by
  exact gap12 φ f A B a b hAB hab hφ hf hrange

end
end ProofGap.Exercise2202
