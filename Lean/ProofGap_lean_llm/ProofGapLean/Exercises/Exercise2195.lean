import ProofGapLean.Prelude.Analysis
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2195
noncomputable section

open scoped BigOperators

def IsRational (x : ℝ) : Prop :=
  ∃ q : ℚ, (q : ℝ) = x

def rationalRepresentative (x : ℝ) (h : IsRational x) : ℚ :=
  Classical.choose h

def φ (x : ℝ) : ℝ := by
  classical
  exact if h : IsRational x
    then 1 / ((rationalRepresentative x h).den : ℝ)
    else 0

def IsPartitionOn (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) : Prop :=
  x 0 = a ∧ x n = b ∧ ∀ i < n, x i < x (i + 1)

def width (x : ℕ → ℝ) (i : ℕ) : ℝ := x (i + 1) - x i

def Fine (n : ℕ) (x : ℕ → ℝ) (meshBound : ℝ) : Prop :=
  ∀ i < n, width x i < meshBound

def oscillationOn (g : ℝ → ℝ) (I : Set ℝ) : ℝ :=
  sSup {r : ℝ | ∃ u ∈ I, ∃ v ∈ I, r = |g u - g v|}

def omega (g : ℝ → ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  oscillationOn g (Set.Icc (x i) (x (i + 1)))

def oscillationSum (g : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, omega g x i * width x i

def smallDenominatorSet (N : ℕ) : Set ℝ :=
  {y : ℝ | y ∈ Set.Icc 0 1 ∧
    ∃ q : ℚ, (q : ℝ) = y ∧ q.den ≤ N}

def FirstClass (N : ℕ) (x : ℕ → ℝ) (i : ℕ) : Prop :=
  Set.Nonempty (Set.Icc (x i) (x (i + 1)) ∩ smallDenominatorSet N)

def firstClassCount (N n : ℕ) (x : ℕ → ℝ) : ℕ := by
  classical
  exact ((Finset.range n).filter (FirstClass N x)).card

def firstClassLength (N n : ℕ) (x : ℕ → ℝ) : ℝ := by
  classical
  exact ∑ i ∈ (Finset.range n).filter (FirstClass N x), width x i

def DarbouxIntegrableOn (g : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε > 0, ∃ n : ℕ, ∃ x : ℕ → ℝ,
    0 < n ∧ IsPartitionOn a b n x ∧ oscillationSum g n x < ε

private def smallDenominatorSetOn (a b : ℝ) (N : ℕ) : Set ℝ :=
  {y : ℝ | y ∈ Set.Icc a b ∧
    ∃ q : ℚ, (q : ℝ) = y ∧ q.den ≤ N}

private theorem smallDenominatorSetOn_finite (a b : ℝ) (N : ℕ) :
    (smallDenominatorSetOn a b N).Finite := by
  let C : ℝ := |a| + |b| + 1
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  obtain ⟨K : ℕ, hK⟩ := exists_nat_gt (C * (N : ℝ))
  have hrect :
      (Set.Icc (-(K : ℤ)) (K : ℤ) ×ˢ Set.Icc (1 : ℕ) N).Finite :=
    (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  have hQ : Set.Finite {q : ℚ |
      (q : ℝ) ∈ Set.Icc a b ∧ q.den ≤ N} := by
    refine (hrect.image (fun p : ℤ × ℕ => (p.1 : ℚ) / (p.2 : ℚ))).subset ?_
    intro q hq
    have hd : (0 : ℝ) < (q.den : ℝ) := by
      exact_mod_cast q.den_pos
    have hqlower : -C < (q : ℝ) := by
      dsimp [C]
      nlinarith [neg_abs_le a, abs_nonneg b, hq.1.1]
    have hqupper : (q : ℝ) < C := by
      dsimp [C]
      nlinarith [le_abs_self b, abs_nonneg a, hq.1.2]
    have hCd : C * (q.den : ℝ) ≤ C * (N : ℝ) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hq.2) hC
    have hCdK : C * (q.den : ℝ) < (K : ℝ) := lt_of_le_of_lt hCd hK
    have hnumlowerC : -C * (q.den : ℝ) < (q.num : ℝ) := by
      apply (lt_div_iff₀ hd).mp
      simpa only [Rat.cast_def] using hqlower
    have hnumupperC : (q.num : ℝ) < C * (q.den : ℝ) := by
      apply (div_lt_iff₀ hd).mp
      simpa only [Rat.cast_def] using hqupper
    have hnumlower : (-(K : ℤ) : ℝ) < (q.num : ℝ) := by
      norm_num
      nlinarith
    have hnumupper : (q.num : ℝ) < (K : ℝ) := lt_trans hnumupperC hCdK
    have hnumlowerZ : -(K : ℤ) ≤ q.num := by
      exact_mod_cast le_of_lt hnumlower
    have hnumupperZ : q.num ≤ (K : ℤ) := by
      exact_mod_cast le_of_lt hnumupper
    refine ⟨(q.num, q.den),
      ⟨⟨hnumlowerZ, hnumupperZ⟩, q.den_pos, hq.2⟩, ?_⟩
    simpa using Rat.num_div_den q
  refine (hQ.image fun q : ℚ => (q : ℝ)).subset ?_
  rintro y ⟨hy, q, hqy, hqN⟩
  exact ⟨q, ⟨by simpa [hqy] using hy, hqN⟩, hqy⟩

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

private theorem partition_lt_on {a b : ℝ} {n : ℕ} {x : ℕ → ℝ}
    (hp : IsPartitionOn a b n x) {i j : ℕ}
    (hij : i < j) (hj : j ≤ n) : x i < x j := by
  have hjpos : 0 < j := by omega
  calc
    x i ≤ x (j - 1) := partition_le_on hp (by omega) (by omega)
    _ < x ((j - 1) + 1) := hp.2.2 (j - 1) (by omega)
    _ = x j := by rw [Nat.sub_add_cancel hjpos]

private theorem sum_width (x : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m, width x i) = x m - x 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [width]
      ring

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

private theorem φ_nonneg (y : ℝ) : 0 ≤ φ y := by
  unfold φ
  split
  · positivity
  · exact le_rfl

private theorem φ_le_one (y : ℝ) : φ y ≤ 1 := by
  unfold φ
  split
  · rename_i h
    have hd : (1 : ℝ) ≤ (rationalRepresentative y h).den := by
      exact_mod_cast (rationalRepresentative y h).den_pos
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd
  · norm_num

private theorem φ_le_inv_of_not_mem (a b : ℝ) (N : ℕ) (hN : 0 < N)
    {y : ℝ} (hyI : y ∈ Set.Icc a b) (hy : y ∉ smallDenominatorSetOn a b N) :
    φ y ≤ 1 / (N : ℝ) := by
  classical
  by_cases hrat : IsRational y
  · let q : ℚ := rationalRepresentative y hrat
    have hqy : (q : ℝ) = y := Classical.choose_spec hrat
    have hden : N ≤ q.den := by
      by_contra h
      have hden' : q.den ≤ N := by omega
      exact hy ⟨hyI, q, hqy, hden'⟩
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hdenR : (N : ℝ) ≤ q.den := by exact_mod_cast hden
    change (if h : IsRational y then
      1 / ((rationalRepresentative y h).den : ℝ) else 0) ≤ _
    rw [dif_pos hrat]
    change 1 / (q.den : ℝ) ≤ 1 / (N : ℝ)
    exact one_div_le_one_div_of_le hNR hdenR
  · simp [φ, hrat]

private theorem oscillationOn_le_of_bounds (g : ℝ → ℝ) (I : Set ℝ) (M : ℝ)
    (hI : I.Nonempty) (hlo : ∀ y ∈ I, 0 ≤ g y)
    (hhi : ∀ y ∈ I, g y ≤ M) : oscillationOn g I ≤ M := by
  unfold oscillationOn
  apply csSup_le
  · obtain ⟨y, hy⟩ := hI
    exact ⟨0, y, hy, y, hy, by simp⟩
  · rintro r ⟨u, hu, v, hv, rfl⟩
    rw [abs_le]
    constructor <;> linarith [hlo u hu, hlo v hv, hhi u hu, hhi v hv]

private theorem omega_le_one {a b : ℝ} {n i : ℕ} {x : ℕ → ℝ}
    (hp : IsPartitionOn a b n x) (hi : i < n) : omega φ x i ≤ 1 := by
  have hcell : Set.Nonempty (Set.Icc (x i) (x (i + 1))) :=
    ⟨x i, le_rfl, (hp.2.2 i hi).le⟩
  unfold omega
  exact oscillationOn_le_of_bounds φ _ 1 hcell
    (fun y hy => φ_nonneg y) (fun y hy => φ_le_one y)

private theorem omega_le_inv_of_no_hit {a b : ℝ} {N n i : ℕ} {x : ℕ → ℝ}
    (hN : 0 < N) (hp : IsPartitionOn a b n x) (hi : i < n)
    (hsecond : ¬ Set.Nonempty
      (Set.Icc (x i) (x (i + 1)) ∩ smallDenominatorSetOn a b N)) :
    omega φ x i ≤ 1 / (N : ℝ) := by
  have hcell : Set.Nonempty (Set.Icc (x i) (x (i + 1))) :=
    ⟨x i, le_rfl, (hp.2.2 i hi).le⟩
  have hsub := cell_subset_partition_interval hp hi
  unfold omega
  apply oscillationOn_le_of_bounds φ _ (1 / (N : ℝ)) hcell
  · intro y hy
    exact φ_nonneg y
  · intro y hy
    apply φ_le_inv_of_not_mem a b N hN (hsub hy)
    intro hyS
    exact hsecond ⟨y, hy, hyS⟩

private def Hit (S : Set ℝ) (x : ℕ → ℝ) (i : ℕ) : Prop :=
  Set.Nonempty (Set.Icc (x i) (x (i + 1)) ∩ S)

private def hitFinset (S : Set ℝ) (n : ℕ) (x : ℕ → ℝ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (Hit S x)

private def cellIndices (n : ℕ) (x : ℕ → ℝ) (y : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun i => y ∈ Set.Icc (x i) (x (i + 1)))

private theorem cell_indices_adjacent {a b y : ℝ} {n i j : ℕ} {x : ℕ → ℝ}
    (hp : IsPartitionOn a b n x) (hi : i < n) (hj : j < n)
    (hyi : y ∈ Set.Icc (x i) (x (i + 1)))
    (hyj : y ∈ Set.Icc (x j) (x (j + 1))) :
    i ≤ j + 1 ∧ j ≤ i + 1 := by
  constructor
  · by_contra h
    have hlt : j + 1 < i := by omega
    have hxlt : x (j + 1) < x i := partition_lt_on hp hlt (by omega)
    linarith [hyi.1, hyj.2]
  · by_contra h
    have hlt : i + 1 < j := by omega
    have hxlt : x (i + 1) < x j := partition_lt_on hp hlt (by omega)
    linarith [hyj.1, hyi.2]

private theorem cellIndices_card_le_two {a b y : ℝ} {n : ℕ} {x : ℕ → ℝ}
    (hp : IsPartitionOn a b n x) : (cellIndices n x y).card ≤ 2 := by
  classical
  by_contra hcard
  have htwo : 2 < (cellIndices n x y).card := by omega
  obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ :=
    Finset.two_lt_card_iff.mp htwo
  simp only [cellIndices, Finset.mem_filter, Finset.mem_range] at hi hj hk
  have ha := cell_indices_adjacent hp hi.1 hj.1 hi.2 hj.2
  have hb := cell_indices_adjacent hp hi.1 hk.1 hi.2 hk.2
  have hc := cell_indices_adjacent hp hj.1 hk.1 hj.2 hk.2
  omega

private theorem hitFinset_card_le_two_ncard {a b : ℝ} {S : Set ℝ} {n : ℕ}
    {x : ℕ → ℝ} (hS : S.Finite) (hp : IsPartitionOn a b n x) :
    (hitFinset S n x).card ≤ 2 * S.ncard := by
  classical
  let T : Finset ℝ := hS.toFinset
  have hsub : hitFinset S n x ⊆ T.biUnion (cellIndices n x) := by
    intro i hi
    simp only [hitFinset, Finset.mem_filter, Finset.mem_range] at hi
    rcases hi.2 with ⟨y, hycell, hyS⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨y, ?_, ?_⟩
    · exact hS.mem_toFinset.mpr hyS
    · simp only [cellIndices, Finset.mem_filter, Finset.mem_range]
      exact ⟨hi.1, hycell⟩
  calc
    (hitFinset S n x).card ≤ (T.biUnion (cellIndices n x)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ y ∈ T, (cellIndices n x y).card := Finset.card_biUnion_le
    _ ≤ ∑ y ∈ T, 2 := by
      apply Finset.sum_le_sum
      intro y hy
      exact cellIndices_card_le_two hp
    _ = 2 * S.ncard := by
      rw [Set.ncard_eq_toFinset_card S hS]
      simp [T, Nat.mul_comm]

private theorem hitLength_le {S : Set ℝ} {n : ℕ} {x : ℕ → ℝ} {meshBound : ℝ}
    (hfine : Fine n x meshBound) :
    (∑ i ∈ hitFinset S n x, width x i) ≤
      ((hitFinset S n x).card : ℝ) * meshBound := by
  classical
  calc
    (∑ i ∈ hitFinset S n x, width x i) ≤
        ∑ i ∈ hitFinset S n x, meshBound := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hfine i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)).le
    _ = ((hitFinset S n x).card : ℝ) * meshBound := by simp

private theorem oscillationSum_le_hitLength_add (a b : ℝ) (N n : ℕ)
    (x : ℕ → ℝ) (hN : 0 < N) (hp : IsPartitionOn a b n x) :
    oscillationSum φ n x ≤
      (∑ i ∈ hitFinset (smallDenominatorSetOn a b N) n x, width x i) +
        (b - a) / (N : ℝ) := by
  classical
  let S := smallDenominatorSetOn a b N
  let F := hitFinset S n x
  let G := (Finset.range n).filter (fun i => ¬ Hit S x i)
  have hfirst : (∑ i ∈ F, omega φ x i * width x i) ≤
      ∑ i ∈ F, width x i := by
    apply Finset.sum_le_sum
    intro i hiF
    have hi : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hiF).1
    have hw : 0 ≤ width x i := sub_nonneg.mpr (hp.2.2 i hi).le
    simpa using mul_le_mul_of_nonneg_right (omega_le_one hp hi) hw
  have hsecondPoint : (∑ i ∈ G, omega φ x i * width x i) ≤
      ∑ i ∈ G, (1 / (N : ℝ)) * width x i := by
    apply Finset.sum_le_sum
    intro i hiG
    have hiParts := Finset.mem_filter.mp hiG
    have hi : i < n := Finset.mem_range.mp hiParts.1
    have hw : 0 ≤ width x i := sub_nonneg.mpr (hp.2.2 i hi).le
    have hω := omega_le_inv_of_no_hit hN hp hi hiParts.2
    exact mul_le_mul_of_nonneg_right hω hw
  have hsecondAll : (∑ i ∈ G, (1 / (N : ℝ)) * width x i) ≤
      ∑ i ∈ Finset.range n, (1 / (N : ℝ)) * width x i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i hi hiG
    have hi' : i < n := Finset.mem_range.mp hi
    exact mul_nonneg (one_div_nonneg.mpr (by positivity))
      (sub_nonneg.mpr (hp.2.2 i hi').le)
  have hsecond : (∑ i ∈ G, omega φ x i * width x i) ≤
      (b - a) / (N : ℝ) := by
    calc
      (∑ i ∈ G, omega φ x i * width x i) ≤
          ∑ i ∈ G, (1 / (N : ℝ)) * width x i := hsecondPoint
      _ ≤ ∑ i ∈ Finset.range n, (1 / (N : ℝ)) * width x i := hsecondAll
      _ = (b - a) / (N : ℝ) := by
        rw [← Finset.mul_sum, sum_width, hp.1, hp.2.1]
        ring
  have hdecomp : oscillationSum φ n x =
      (∑ i ∈ F, omega φ x i * width x i) +
        ∑ i ∈ G, omega φ x i * width x i := by
    unfold oscillationSum
    rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.range n) (Hit S x)]
    rfl
  rw [hdecomp]
  exact add_le_add hfirst hsecond

private theorem oscillationSum_le_bound (a b : ℝ) (N n : ℕ)
    (x : ℕ → ℝ) (meshBound : ℝ) (hab : a < b) (hN : 0 < N)
    (hp : IsPartitionOn a b n x) (hfine : Fine n x meshBound) :
    oscillationSum φ n x ≤
      2 * ((smallDenominatorSetOn a b N).ncard : ℝ) * meshBound +
        (b - a) / (N : ℝ) := by
  let S := smallDenominatorSetOn a b N
  have hS : S.Finite := smallDenominatorSetOn_finite a b N
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    linarith [hp.1, hp.2.1, hab]
  have hmesh : 0 < meshBound := by
    have hwpos : 0 < width x 0 := by
      unfold width
      exact sub_pos.mpr (hp.2.2 0 hn)
    exact lt_trans hwpos (hfine 0 hn)
  have hcount : (hitFinset S n x).card ≤ 2 * S.ncard :=
    hitFinset_card_le_two_ncard hS hp
  have hcountR : ((hitFinset S n x).card : ℝ) ≤ 2 * (S.ncard : ℝ) := by
    exact_mod_cast hcount
  have hlength : (∑ i ∈ hitFinset S n x, width x i) ≤
      2 * (S.ncard : ℝ) * meshBound := by
    calc
      (∑ i ∈ hitFinset S n x, width x i) ≤
          ((hitFinset S n x).card : ℝ) * meshBound := hitLength_le hfine
      _ ≤ (2 * (S.ncard : ℝ)) * meshBound :=
        mul_le_mul_of_nonneg_right hcountR hmesh.le
  calc
    oscillationSum φ n x ≤
        (∑ i ∈ hitFinset S n x, width x i) + (b - a) / (N : ℝ) :=
      oscillationSum_le_hitLength_add a b N n x hN hp
    _ ≤ 2 * (S.ncard : ℝ) * meshBound + (b - a) / (N : ℝ) :=
      add_le_add hlength le_rfl

private theorem uniform_oscillation_bound (a b : ℝ) (hab : a < b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ n : ℕ, ∀ x : ℕ → ℝ,
      IsPartitionOn a b n x → Fine n x δ → oscillationSum φ n x < ε := by
  let L := b - a
  have hL : 0 < L := sub_pos.mpr hab
  obtain ⟨N : ℕ, hNlarge⟩ := exists_nat_gt (2 * L / ε)
  have hNposR : (0 : ℝ) < N := lt_trans (by positivity) hNlarge
  have hN : 0 < N := by exact_mod_cast hNposR
  let S := smallDenominatorSetOn a b N
  let c : ℝ := S.ncard
  let δ := ε / (8 * (c + 1))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : 0 < c + 1 := by linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hfirst : 2 * c * δ ≤ ε / 4 := by
    have hcle : c ≤ c + 1 := by linarith
    calc
      2 * c * δ ≤ 2 * (c + 1) * δ := by
        gcongr
      _ = ε / 4 := by
        dsimp [δ]
        field_simp [ne_of_gt hc1]
        ring
  have hsecond : L / (N : ℝ) < ε / 2 := by
    have hmul : 2 * L < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hNlarge
    apply (div_lt_iff₀ hNposR).2
    nlinarith
  refine ⟨δ, hδ, ?_⟩
  intro n x hp hfine
  have hbound := oscillationSum_le_bound a b N n x δ hab hN hp hfine
  change oscillationSum φ n x ≤ 2 * c * δ + L / (N : ℝ) at hbound
  linarith

private theorem darboux_of_uniform (a b : ℝ) (hab : a < b)
    (huniform : ∀ ε > 0, ∃ δ > 0, ∀ n : ℕ, ∀ x : ℕ → ℝ,
      IsPartitionOn a b n x → Fine n x δ → oscillationSum φ n x < ε) :
    DarbouxIntegrableOn φ a b := by
  unfold DarbouxIntegrableOn
  intro ε hε
  obtain ⟨δ, hδ, hall⟩ := huniform ε hε
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt ((b - a) / δ)
  have hquot : 0 < (b - a) / δ := div_pos (sub_pos.mpr hab) hδ
  have hnR : (0 : ℝ) < n := lt_trans hquot hn
  have hnN : 0 < n := by exact_mod_cast hnR
  let x : ℕ → ℝ := fun i => a + (i : ℝ) * (b - a) / (n : ℝ)
  have hp : IsPartitionOn a b n x := by
    constructor
    · simp [x]
    constructor
    · simp [x, ne_of_gt hnR]
    · intro i hi
      dsimp [x]
      rw [add_lt_add_iff_left]
      apply (div_lt_div_iff_of_pos_right hnR).2
      apply mul_lt_mul_of_pos_right _ (sub_pos.mpr hab)
      exact_mod_cast Nat.lt_succ_self i
  have hfine : Fine n x δ := by
    intro i hi
    have hw : width x i = (b - a) / (n : ℝ) := by
      dsimp [width, x]
      rw [Nat.cast_add, Nat.cast_one]
      field_simp [ne_of_gt hnR]
      ring
    rw [hw]
    have hprod : b - a < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
    exact (div_lt_iff₀ hnR).2 (by simpa [mul_comm] using hprod)
  exact ⟨n, x, hnN, hp, hall n x hp hfine⟩

theorem gap1 (n : ℕ) (x : ℕ → ℝ) (meshBound : ℝ)
    (hfine : Fine n x meshBound) :
    ∀ i < n, width x i < meshBound := by
  exact hfine

theorem gap2 (N : ℕ) (hN : 0 < N) :
    (smallDenominatorSet N).Finite := by
  simpa [smallDenominatorSet, smallDenominatorSetOn] using
    smallDenominatorSetOn_finite 0 1 N

theorem gap3 (N n : ℕ) (x : ℕ → ℝ)
    (hN : 0 < N) (hp : IsPartitionOn 0 1 n x) :
    firstClassCount N n x ≤ 2 * (smallDenominatorSet N).ncard := by
  classical
  simpa [firstClassCount, FirstClass, hitFinset, Hit] using
    hitFinset_card_le_two_ncard (gap2 N hN) hp

theorem gap4 (N n : ℕ) (x : ℕ → ℝ) (meshBound : ℝ)
    (hN : 0 < N) (hp : IsPartitionOn 0 1 n x)
    (hfine : Fine n x meshBound) :
    firstClassLength N n x <
      (firstClassCount N n x : ℝ) * meshBound := by
  classical
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    linarith [hp.1, hp.2.1]
  have hfirst : FirstClass N x 0 := by
    refine ⟨0, ?_, ?_⟩
    · exact ⟨by linarith [hp.1], by linarith [hp.1, hp.2.2 0 hn]⟩
    · refine ⟨by norm_num, 0, by norm_num, ?_⟩
      simpa using hN
  have hnon : ((Finset.range n).filter (FirstClass N x)).Nonempty := by
    exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, hfirst⟩⟩
  unfold firstClassLength firstClassCount
  simpa using Finset.sum_lt_sum_of_nonempty hnon (fun i hi =>
    hfine i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1))

theorem gap5 (N n i : ℕ) (x : ℕ → ℝ)
    (hN : 0 < N) (hp : IsPartitionOn 0 1 n x)
    (hi : i < n) (hsecond : ¬ FirstClass N x i) :
    omega φ x i ≤ 1 / (N : ℝ) := by
  exact omega_le_inv_of_no_hit hN hp hi (by
    simpa [FirstClass, smallDenominatorSet, smallDenominatorSetOn] using hsecond)

theorem gap6 (N n : ℕ) (x : ℕ → ℝ) (meshBound : ℝ)
    (hN : 0 < N) (hp : IsPartitionOn 0 1 n x)
    (hfine : Fine n x meshBound) :
    oscillationSum φ n x <
      2 * ((smallDenominatorSet N).ncard : ℝ) * meshBound + 1 / (N : ℝ) := by
  classical
  have hbase := oscillationSum_le_hitLength_add 0 1 N n x hN hp
  have hbase' : oscillationSum φ n x ≤
      firstClassLength N n x + 1 / (N : ℝ) := by
    simpa [firstClassLength, FirstClass, hitFinset, Hit,
      smallDenominatorSet, smallDenominatorSetOn] using hbase
  have hlen := gap4 N n x meshBound hN hp hfine
  have hcount := gap3 N n x hN hp
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    linarith [hp.1, hp.2.1]
  have hmesh : 0 < meshBound := lt_trans
    (sub_pos.mpr (hp.2.2 0 hn)) (hfine 0 hn)
  have hcountR : (firstClassCount N n x : ℝ) ≤
      2 * ((smallDenominatorSet N).ncard : ℝ) := by
    exact_mod_cast hcount
  calc
    oscillationSum φ n x ≤ firstClassLength N n x + 1 / (N : ℝ) := hbase'
    _ < (firstClassCount N n x : ℝ) * meshBound + 1 / (N : ℝ) :=
      by linarith
    _ ≤ 2 * ((smallDenominatorSet N).ncard : ℝ) * meshBound + 1 / (N : ℝ) := by
      gcongr

theorem gap7 (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ 2 / ε < N := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  have hNR : (0 : ℝ) < N := lt_trans (by positivity) hN
  exact ⟨N, by exact_mod_cast hNR, hN⟩

theorem gap8 (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ n : ℕ, ∀ x : ℕ → ℝ,
      IsPartitionOn 0 1 n x → Fine n x δ →
        oscillationSum φ n x < ε := by
  exact uniform_oscillation_bound 0 1 (by norm_num) ε hε

theorem gap9 :
    ∀ ε > 0, ∃ δ > 0, ∀ n : ℕ, ∀ x : ℕ → ℝ,
      IsPartitionOn 0 1 n x → Fine n x δ →
        oscillationSum φ n x < ε := by
  exact gap8

theorem gap10 :
    DarbouxIntegrableOn φ 0 1 := by
  exact darboux_of_uniform 0 1 (by norm_num) gap9

theorem gap11 :
    DarbouxIntegrableOn φ 0 1 := by
  exact gap10

theorem gap12 (a b : ℝ) (hab : a < b) :
    DarbouxIntegrableOn φ a b := by
  exact darboux_of_uniform a b hab (fun ε hε =>
    uniform_oscillation_bound a b hab ε hε)

theorem gap13 (a b : ℝ) (hab : a < b) :
    DarbouxIntegrableOn φ a b := by
  exact gap12 a b hab

end
end ProofGap.Exercise2195
