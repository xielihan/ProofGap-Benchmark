import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2554

noncomputable section

def block (a : ℕ → ℝ) (p : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico (p n) (p (n + 1)), a i
def blockPartial (a : ℕ → ℝ) (p : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, block a p k
def originalPartial (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, a k

def alternating (n : ℕ) : ℝ := (-1 : ℝ) ^ (n - 1)
def pairedBlock (n : ℕ) : ℝ :=
  alternating (2 * n - 1) + alternating (2 * n)

theorem gap1 (a : ℕ → ℝ) (p : ℕ → ℕ) (n : ℕ) :
    blockPartial a p n = ∑ k ∈ Finset.Icc 1 n, block a p k := by
  rfl
theorem gap2 (a : ℕ → ℝ) (p : ℕ → ℕ) (n : ℕ)
    (hp1 : p 1 = 1) (hmono : StrictMono p) :
    (∑ k ∈ Finset.Icc 1 n, block a p k) =
      originalPartial a (p (n + 1) - 1) := by
  unfold block originalPartial
  rw [← Finset.sum_biUnion]
  · congr 1
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_Ico]
    constructor
    · rintro ⟨k, ⟨hk1, hkn⟩, hpki, hipk1⟩
      have hpone : 1 ≤ p k := by
        rw [← hp1]
        exact hmono.monotone hk1
      constructor
      · omega
      · have hle : p (k + 1) ≤ p (n + 1) :=
          hmono.monotone (Nat.add_le_add_right hkn 1)
        omega
    · intro hi
      have hip : i < p (n + 1) := by omega
      let hex : ∃ k, i < p (k + 1) := ⟨n, hip⟩
      let k := Nat.find hex
      have hkprop : i < p (k + 1) := by
        dsimp [k]
        exact Nat.find_spec hex
      have hkn : k ≤ n := by
        dsimp [k]
        exact Nat.find_min' hex hip
      have hkpos : 1 ≤ k := by
        by_contra h
        have hkzero : k = 0 := by omega
        have ht : i < p 1 := by
          simpa [hkzero] using hkprop
        rw [hp1] at ht
        omega
      have hpki : p k ≤ i := by
        by_contra h
        have hiPk : i < p k := by omega
        have hkm1 : k - 1 < k := by omega
        have hkeq : (k - 1) + 1 = k := by omega
        exact (Nat.find_min hex hkm1) (by simpa only [hkeq] using hiPk)
      exact ⟨k, ⟨hkpos, hkn⟩, hpki, hkprop⟩
  · intro i hi j hj hij
    simp only [Finset.disjoint_left, Finset.mem_Ico]
    intro x hxi hxj
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have hpij : p (i + 1) ≤ p j := hmono.monotone (by omega)
      omega
    · exact hij heq
    · have hpji : p (j + 1) ≤ p i := hmono.monotone (by omega)
      omega
theorem gap3 (a : ℕ → ℝ) (p : ℕ → ℕ) (n : ℕ)
    (hp1 : p 1 = 1) (hmono : StrictMono p) :
    blockPartial a p n = originalPartial a (p (n + 1) - 1) := by
  rw [gap1, gap2 a p n hp1 hmono]
theorem gap4 (a : ℕ → ℝ) (S : ℝ)
    (hS : Filter.Tendsto (originalPartial a) Filter.atTop (nhds S)) :
    Filter.Tendsto (originalPartial a) Filter.atTop (nhds S) := by
  exact hS
theorem gap5 (a : ℕ → ℝ) (p : ℕ → ℕ) (S : ℝ)
    (hp1 : p 1 = 1) (hmono : StrictMono p)
    (hS : Filter.Tendsto (originalPartial a) Filter.atTop (nhds S)) :
    Filter.Tendsto (blockPartial a p) Filter.atTop (nhds S) := by
  have hq : Filter.Tendsto (fun n => p (n + 1) - 1)
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with n hn
    have hpge : n + 1 ≤ p (n + 1) := hmono.id_le (n + 1)
    omega
  have hc := hS.comp hq
  have heq : blockPartial a p =
      fun n => originalPartial a (p (n + 1) - 1) := by
    funext n
    exact gap3 a p n hp1 hmono
  rw [heq]
  exact hc
theorem gap6 (a : ℕ → ℝ) (p : ℕ → ℕ) (S : ℝ)
    (hp : Filter.Tendsto p Filter.atTop Filter.atTop)
    (hS : Filter.Tendsto (originalPartial a) Filter.atTop (nhds S)) :
    Filter.Tendsto (fun n => originalPartial a (p (n + 1) - 1))
      Filter.atTop (nhds S) := by
  apply hS.comp
  apply Filter.tendsto_atTop.2
  intro b
  have he : ∀ᶠ n in Filter.atTop, b + 1 ≤ p n :=
    hp.eventually (Filter.eventually_ge_atTop (b + 1))
  rcases (Filter.eventually_atTop.1 he) with ⟨N, hN⟩
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hpnext : b + 1 ≤ p (n + 1) := hN (n + 1) (by omega)
  omega
theorem gap7 (a : ℕ → ℝ) (p : ℕ → ℕ) (S : ℝ)
    (hp1 : p 1 = 1) (hmono : StrictMono p)
    (hS : Filter.Tendsto (originalPartial a) Filter.atTop (nhds S)) :
    Filter.Tendsto (blockPartial a p) Filter.atTop (nhds S) := by
  exact gap5 a p S hp1 hmono hS
theorem gap8 (a : ℕ → ℝ) (p : ℕ → ℕ) (S : ℝ)
    (hp1 : p 1 = 1) (hmono : StrictMono p)
    (ha : HasSum (fun n : ℕ => a (n + 1)) S) :
    HasSum (fun n : ℕ => block a p (n + 1)) S := by
  have hshift (n : ℕ) :
      block a p (n + 1) =
        ∑ j ∈ Finset.Ico (p (n + 1) - 1) (p (n + 2) - 1), a (j + 1) := by
    unfold block
    have hA : 1 ≤ p (n + 1) := by
      rw [← hp1]
      exact hmono.monotone (by omega)
    have hAB : p (n + 1) ≤ p (n + 2) :=
      hmono.monotone (by omega)
    have hn : n + 1 + 1 = n + 2 := by omega
    have hpred : p (n + 1) - 1 + 1 = p (n + 1) :=
      Nat.sub_add_cancel hA
    have hlen :
        p (n + 2) - p (n + 1) =
          (p (n + 2) - 1) - (p (n + 1) - 1) := by
      rw [Nat.sub_sub]
      rw [Nat.add_comm 1 (p (n + 1) - 1), hpred]
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr
    · congr 1
    · intro k hk
      congr 1
      omega
  have hcover (j : ℕ) :
      ∃ n, j ∈ Finset.Ico (p (n + 1) - 1) (p (n + 2) - 1) := by
    let i := j + 1
    have hex : ∃ k, i < p (k + 1) := by
      refine ⟨i, ?_⟩
      exact lt_of_lt_of_le (Nat.lt_succ_self i) (hmono.id_le (i + 1))
    let k := Nat.find hex
    have hkprop : i < p (k + 1) := by
      dsimp [k]
      exact Nat.find_spec hex
    have hkpos : 1 ≤ k := by
      by_contra h
      have hkzero : k = 0 := by omega
      have ht : i < p 1 := by
        simpa [hkzero] using hkprop
      rw [hp1] at ht
      dsimp [i] at ht
      omega
    have hpki : p k ≤ i := by
      by_contra h
      have hiPk : i < p k := by omega
      have hkm1 : k - 1 < k := by omega
      have hkeq : (k - 1) + 1 = k := by omega
      exact (Nat.find_min hex hkm1) (by simpa only [hkeq] using hiPk)
    have hpkone : 1 ≤ p k := by
      rw [← hp1]
      exact hmono.monotone hkpos
    refine ⟨k - 1, ?_⟩
    simp only [Finset.mem_Ico]
    have hk1 : k - 1 + 1 = k := by omega
    have hk2 : k - 1 + 2 = k + 1 := by omega
    rw [hk1, hk2]
    dsimp [i] at hpki hkprop
    omega
  let r : ℕ → ℕ := fun j => Classical.choose (hcover j)
  have hr (j : ℕ) :
      j ∈ Finset.Ico (p (r j + 1) - 1) (p (r j + 2) - 1) :=
    Classical.choose_spec (hcover j)
  let q : Finset ℕ → Finset ℕ := fun s =>
    s.biUnion (fun n => Finset.Ico (p (n + 1) - 1) (p (n + 2) - 1))
  have hq : Filter.Tendsto q Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro t
    filter_upwards [Filter.eventually_ge_atTop (t.image r)] with s hs
    intro j hj
    simp only [q, Finset.mem_biUnion]
    exact ⟨r j, hs (Finset.mem_image.2 ⟨j, hj, rfl⟩), hr j⟩
  have hsum (s : Finset ℕ) :
      (∑ n ∈ s, block a p (n + 1)) =
        ∑ j ∈ q s, a (j + 1) := by
    calc
      (∑ n ∈ s, block a p (n + 1)) =
          ∑ n ∈ s, ∑ j ∈ Finset.Ico (p (n + 1) - 1) (p (n + 2) - 1),
            a (j + 1) := by
              apply Finset.sum_congr rfl
              intro n hn
              exact hshift n
      _ = ∑ j ∈ q s, a (j + 1) := by
        dsimp [q]
        rw [← Finset.sum_biUnion]
        intro i hi j hj hij
        simp only [Finset.disjoint_left, Finset.mem_Ico]
        intro x hxi hxj
        rcases lt_trichotomy i j with hlt | heq | hgt
        · have hpij : p (i + 2) ≤ p (j + 1) :=
            hmono.monotone (by omega)
          omega
        · exact hij heq
        · have hpji : p (j + 2) ≤ p (i + 1) :=
            hmono.monotone (by omega)
          omega
  unfold HasSum at ha ⊢
  have heq :
      (fun s : Finset ℕ => ∑ n ∈ s, block a p (n + 1)) =
        fun s => ∑ j ∈ q s, a (j + 1) := by
    funext s
    exact hsum s
  rw [heq]
  exact ha.comp hq
theorem gap9 (a : ℕ → ℝ) (p : ℕ → ℕ) (S : ℝ)
    (hp1 : p 1 = 1) (hmono : StrictMono p)
    (ha : HasSum (fun n : ℕ => a (n + 1)) S) :
    tsum (fun n : ℕ => block a p (n + 1)) =
      tsum (fun n : ℕ => a (n + 1)) := by
  have hb := gap8 a p S hp1 hmono ha
  exact hb.tsum_eq.trans ha.tsum_eq.symm
theorem gap10 : ¬ Summable (fun n : ℕ => alternating (n + 1)) := by
  intro h
  have hz := h.tendsto_atTop_zero
  have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
      Filter.atTop (nhds 0) := by
    simpa [alternating] using hz.norm
  have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
      Filter.atTop (nhds (1 : ℝ)) := tendsto_const_nhds
  have hEq : (1 : ℝ) = 0 := tendsto_nhds_unique hconst hone
  norm_num at hEq
theorem gap11 : Summable (fun n : ℕ => pairedBlock (n + 1)) := by
  have hzero : (fun n : ℕ => pairedBlock (n + 1)) =
      fun _ => (0 : ℝ) := by
    funext n
    unfold pairedBlock alternating
    have h1 : 2 * (n + 1) - 1 - 1 = 2 * n := by omega
    have h2 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    rw [h1, h2, pow_succ, pow_mul]
    norm_num
  rw [hzero]
  exact summable_zero
theorem gap12 :
    ¬ (Summable (fun n : ℕ => pairedBlock (n + 1)) →
      Summable (fun n : ℕ => alternating (n + 1))) := by
  intro h
  exact gap10 (h gap11)
theorem gap13 :
    Summable (fun n : ℕ => pairedBlock (n + 1)) ∧
      ¬ Summable (fun n : ℕ => alternating (n + 1)) := by
  exact ⟨gap11, gap10⟩

end

end ProofGap.Exercise2554
