import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Subadditive

open Filter Topology

namespace ProofGap.Exercise137

noncomputable section

def Subadditive (x : ℕ → ℝ) : Prop :=
  ∀ m n : ℕ, x (m + n) ≤ x m + x n

def Nonnegative (x : ℕ → ℝ) : Prop := ∀ n : ℕ, 0 ≤ x n

def normalized (x : ℕ → ℝ) (n : ℕ) : ℝ := x n / (n : ℝ)

def normalizedValues (x : ℕ → ℝ) : Set ℝ :=
  {v | ∃ n : ℕ, 0 < n ∧ v = normalized x n}

/-- Exercise 137, gap 1; n>1 avoids underflow. -/
theorem gap1 (x : ℕ → ℝ) (hsub : Subadditive x) :
    ∀ n : ℕ, 1 < n → x n ≤ x (n - 1) + x 1 := by
  intro n hn
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hsub (n - 1) 1

/-- Exercise 137, gap 2; n>2 avoids underflow. -/
theorem gap2 (x : ℕ → ℝ) (hsub : Subadditive x) :
    ∀ n : ℕ, 2 < n →
      x (n - 1) + x 1 ≤ x (n - 2) + x 1 + x 1 := by
  intro n hn
  have h : x (n - 1) ≤ x (n - 2) + x 1 := by
    simpa [Nat.sub_sub] using gap1 x hsub (n - 1) (by omega)
  linarith

/-- Exercise 137, gap 3; positive indices are restored. -/
theorem gap3 (x : ℕ → ℝ) (hsub : Subadditive x) :
    ∀ n : ℕ, 0 < n → x n ≤ (n : ℝ) * x 1 := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  induction k with
  | zero => simp
  | succ k ih =>
      have hs := hsub (k + 1) 1
      calc
        x (k + 1 + 1) ≤ x (k + 1) + x 1 := hs
        _ ≤ ((k + 1 : ℕ) : ℝ) * x 1 + x 1 := by
          gcongr
          exact ih (by omega)
        _ = ((k + 1 + 1 : ℕ) : ℝ) * x 1 := by push_cast; ring

/-- Exercise 137, gap 4. -/
theorem gap4 (x : ℕ → ℝ) (hsub : Subadditive x) :
    ∀ n : ℕ, 0 < n → x n ≤ (n : ℝ) * x 1 := by
  exact gap3 x hsub

/-- Exercise 137, gap 5; division uses n>0. -/
theorem gap5 (x : ℕ → ℝ) (hx0 : Nonnegative x) :
    ∀ n : ℕ, 0 < n → 0 ≤ normalized x n := by
  intro n hn
  exact div_nonneg (hx0 n) (Nat.cast_nonneg n)

/-- Exercise 137, gap 6; division uses n>0. -/
theorem gap6 (x : ℕ → ℝ) (hsub : Subadditive x) :
    ∀ n : ℕ, 0 < n → normalized x n ≤ x 1 := by
  intro n hn
  rw [normalized, div_le_iff₀ (by positivity)]
  simpa [mul_comm] using gap3 x hsub n hn

/-- Exercise 137, gap 7. -/
theorem gap7 (x : ℕ → ℝ) (hx0 : Nonnegative x) : 0 ≤ x 1 := by
  exact hx0 1

/-- Exercise 137, gap 8. -/
theorem gap8 (x : ℕ → ℝ) (hx0 : Nonnegative x) (hsub : Subadditive x) :
    Bornology.IsBounded (normalizedValues x) := by
  apply (Metric.isBounded_Icc (0 : ℝ) (x 1)).subset
  rintro v ⟨n, hn, rfl⟩
  exact ⟨gap5 x hx0 n hn, gap6 x hsub n hn⟩

/-- Exercise 137, gap 9. -/
theorem gap9 (x : ℕ → ℝ) (hx0 : Nonnegative x) :
    0 ≤ sInf (normalizedValues x) := by
  apply le_csInf
  · exact ⟨normalized x 1, 1, by omega, rfl⟩
  · rintro v ⟨n, hn, rfl⟩
    exact gap5 x hx0 n hn

/-- Exercise 137, gap 10. -/
theorem gap10 (x : ℕ → ℝ) :
    Nonnegative x →
    sInf (normalizedValues x) ≤ x 1 := by
  intro hx0
  have hbelow : BddBelow (normalizedValues x) := by
    refine ⟨0, ?_⟩
    rintro v ⟨n, hn, rfl⟩
    exact gap5 x hx0 n hn
  calc
    sInf (normalizedValues x) ≤ normalized x 1 :=
      csInf_le hbelow ⟨1, by omega, rfl⟩
    _ = x 1 := by simp [normalized]

/-- Exercise 137, gap 11. -/
theorem gap11 (x : ℕ → ℝ) (hx0 : Nonnegative x) : 0 ≤ x 1 := by
  exact gap7 x hx0

/-- Exercise 137, gap 12. -/
theorem gap12 (x : ℕ → ℝ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 0 < N ∧
        normalized x N < sInf (normalizedValues x) + ε := by
  intro ε hε
  have hvals : (normalizedValues x).Nonempty :=
    ⟨normalized x 1, 1, by omega, rfl⟩
  by_cases hb : BddBelow (normalizedValues x)
  · have hinf_lt :
        sInf (normalizedValues x) <
          sInf (normalizedValues x) + ε := by linarith
    rcases exists_lt_of_csInf_lt hvals hinf_lt with
      ⟨v, ⟨N, hN, rfl⟩, hclose⟩
    exact ⟨N, hN, hclose⟩
  · have hinf0 : sInf (normalizedValues x) = 0 :=
      Real.sInf_of_not_bddBelow hb
    have hex : ∃ v ∈ normalizedValues x, v < ε := by
      by_contra hnot
      push_neg at hnot
      exact hb ⟨ε, fun v hv => hnot v hv⟩
    rcases hex with ⟨v, ⟨N, hN, rfl⟩, hv⟩
    rw [hinf0]
    simpa using ⟨N, hN, hv⟩

/-- Exercise 137, gap 13; q and r depend on n. -/
theorem gap13 :
    ∀ N n : ℕ, 0 < N → N < n →
      ∃ q r : ℕ, n = q * N + r := by
  intro N n hN hNn
  refine ⟨n / N, n % N, ?_⟩
  rw [Nat.mul_comm]
  exact (Nat.div_add_mod n N).symm

/-- Exercise 137, gap 14. -/
theorem gap14 :
    ∀ N n : ℕ, 0 < N → N < n →
      0 < n / N := by
  intro N n hN hNn
  exact Nat.div_pos hNn.le hN

/-- Exercise 137, gap 15. -/
theorem gap15 :
    ∀ N n : ℕ, 0 < N → N < n → 0 ≤ n % N := by
  omega

/-- Exercise 137, gap 16. -/
theorem gap16 :
    ∀ N n : ℕ, 0 < N → n % N < N := by
  intro N n hN
  exact Nat.mod_lt n hN

/-- Exercise 137, gap 17. -/
theorem gap17 (x : ℕ → ℝ) :
    ∀ N n : ℕ, 0 < N →
      x n = x ((n / N) * N + n % N) := by
  intro N n hN
  congr 1
  rw [Nat.mul_comm]
  exact (Nat.div_add_mod n N).symm

/-- Exercise 137, gap 18; q,r are the Euclidean quotient/remainder. -/
theorem gap18 (x : ℕ → ℝ) (hsub : Subadditive x) :
    Nonnegative x →
    ∀ N n : ℕ, 0 < N →
      x ((n / N) * N + n % N) ≤
        (n / N : ℝ) * x N + x (n % N) := by
  intro hx0 N n hN
  have hs : _root_.Subadditive x := by
    intro m k
    exact hsub m k
  have hfloor := hs.apply_mul_add_le (n / N) N (n % N)
  have hqle : ((n / N : ℕ) : ℝ) ≤ (n : ℝ) / (N : ℝ) := by
    rw [le_div_iff₀ (by positivity)]
    exact_mod_cast Nat.div_mul_le_self n N
  exact hfloor.trans
    (add_le_add (mul_le_mul_of_nonneg_right hqle (hx0 N)) le_rfl)

/-- Exercise 137, gap 19. -/
theorem gap19 (x : ℕ → ℝ) (hsub : Subadditive x) :
    x 0 ≤ 0 →
    ∀ N n : ℕ, 0 < N →
      (n / N : ℝ) * x N + x (n % N) ≤
        (n / N : ℝ) * x N + (n % N : ℝ) * x 1 := by
  intro hx00 N n hN
  by_cases hr0 : n % N = 0
  · simpa [hr0] using
      (add_le_add_left hx00 ((n / N : ℝ) * x N))
  · exact add_le_add le_rfl
      (gap3 x hsub (n % N) (Nat.pos_of_ne_zero hr0))

/-- Exercise 137, gap 20. -/
theorem gap20 (x : ℕ → ℝ) (hx1 : 0 ≤ x 1) :
    ∀ N n : ℕ, 0 < N →
      (n / N : ℝ) * x N + (n % N : ℝ) * x 1 ≤
        (n / N : ℝ) * x N + (N : ℝ) * x 1 := by
  intro N n hN
  have hr : (n % N : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.mod_lt n hN).le
  have hmul := mul_le_mul_of_nonneg_right hr hx1
  linarith

private theorem block_bound
    (x : ℕ → ℝ) (hsub : Subadditive x) (hx0 : Nonnegative x) :
    ∀ N n : ℕ, 0 < N → 0 < n →
      x n ≤ (n / N : ℝ) * x N + (N : ℝ) * x 1 := by
  intro N n hN hn
  let q := n / N
  let r := n % N
  have hdecomp : n = q * N + r := by
    dsimp [q, r]
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod n N).symm
  have hqle : (q : ℝ) ≤ (n : ℝ) / (N : ℝ) := by
    rw [le_div_iff₀ (by positivity)]
    exact_mod_cast Nat.div_mul_le_self n N
  have hrle : (r : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.mod_lt n hN).le
  have hmul : ∀ q : ℕ, 0 < q → x (q * N) ≤ (q : ℝ) * x N := by
    intro q hq
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    induction k with
    | zero => simp
    | succ k ih =>
        have hs := hsub ((k + 1) * N) N
        have hindex : (k + 2) * N = (k + 1) * N + N := by ring
        rw [hindex]
        calc
          x ((k + 1) * N + N) ≤ x ((k + 1) * N) + x N := hs
          _ ≤ ((k + 1 : ℕ) : ℝ) * x N + x N := by
            gcongr
            exact ih (by omega)
          _ = ((k + 2 : ℕ) : ℝ) * x N := by push_cast; ring
  by_cases hq0 : q = 0
  · have hnlt : n < N := by
      have hz : n / N = 0 := by simpa [q] using hq0
      exact ((Nat.div_eq_zero_iff).1 hz).resolve_left (by omega)
    have hx_le : x n ≤ (N : ℝ) * x 1 := by
      calc
        x n ≤ (n : ℝ) * x 1 := gap3 x hsub n hn
        _ ≤ (N : ℝ) * x 1 := by
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast hnlt.le) (hx0 1)
    have hfirst0 : 0 ≤ (n / N : ℝ) * x N :=
      mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hx0 N)
    exact hx_le.trans (le_add_of_nonneg_left hfirst0)
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    have hx_floor : x n ≤ (q : ℝ) * x N + (r : ℝ) * x 1 := by
      rw [hdecomp]
      by_cases hr0 : r = 0
      · simpa [hr0] using hmul q hqpos
      · calc
          x (q * N + r) ≤ x (q * N) + x r := hsub _ _
          _ ≤ (q : ℝ) * x N + x r := by
            linarith [hmul q hqpos]
          _ ≤ (q : ℝ) * x N + (r : ℝ) * x 1 := by
            gcongr
            exact gap3 x hsub r (Nat.pos_of_ne_zero hr0)
    calc
      x n ≤ (q : ℝ) * x N + (r : ℝ) * x 1 := hx_floor
      _ ≤ (n / N : ℝ) * x N + (N : ℝ) * x 1 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hqle (hx0 N))
          (mul_le_mul_of_nonneg_right hrle (hx0 1))

/-- Exercise 137, gap 21. -/
theorem gap21 (x : ℕ → ℝ) (hsub : Subadditive x) (hx1 : 0 ≤ x 1) :
    Nonnegative x →
    ∀ N n : ℕ, 0 < N → 0 < n →
      x n ≤ (n / N : ℝ) * x N + (N : ℝ) * x 1 := by
  intro hx0 N n hN hn
  exact block_bound x hsub hx0 N n hN hn

/-- Exercise 137, gap 22; n>0 is explicit. -/
theorem gap22 (x : ℕ → ℝ) (hsub : Subadditive x) (hx1 : 0 ≤ x 1) :
    Nonnegative x →
    ∀ N n : ℕ, 0 < N → 0 < n →
      normalized x n ≤
        (n / N : ℝ) * x N / n + (N : ℝ) * x 1 / n := by
  intro hx0 N n hN hn
  have hb := block_bound x hsub hx0 N n hN hn
  calc
    normalized x n ≤
        ((n / N : ℝ) * x N + (N : ℝ) * x 1) / (n : ℝ) := by
      exact (div_le_div_iff_of_pos_right (by positivity)).2 hb
    _ = (n / N : ℝ) * x N / n + (N : ℝ) * x 1 / n := by ring

/-- Exercise 137, gap 23. -/
theorem gap23 (x : ℕ → ℝ) :
    ∀ N n : ℕ, 0 < N → 0 < n →
      (n / N : ℝ) * x N / n + (N : ℝ) * x 1 / n ≤
        normalized x N + (N : ℝ) * x 1 / n := by
  intro N n hN hn
  rw [normalized]
  field_simp
  exact le_rfl

/-- Exercise 137, gap 24; N is chosen after ε. -/
theorem gap24 (x : ℕ → ℝ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N < n →
        normalized x N + (N : ℝ) * x 1 / n <
          sInf (normalizedValues x) + ε + (N : ℝ) * x 1 / n := by
  intro ε hε
  rcases gap12 x ε hε with ⟨N, hN, hclose⟩
  refine ⟨N, hN, ?_⟩
  intro n hn
  linarith

/-- Exercise 137, gap 25. -/
theorem gap25 (x : ℕ → ℝ) (hsub : Subadditive x) (hx0 : Nonnegative x) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n →
        normalized x n <
          sInf (normalizedValues x) + ε + (N : ℝ) * x 1 / n := by
  intro ε hε
  have hvals : (normalizedValues x).Nonempty :=
    ⟨normalized x 1, 1, by omega, rfl⟩
  have hinf_lt :
      sInf (normalizedValues x) <
        sInf (normalizedValues x) + ε := by linarith
  rcases exists_lt_of_csInf_lt hvals hinf_lt with
    ⟨v, ⟨N, hN, rfl⟩, hclose⟩
  refine ⟨N, fun n hn => ?_⟩
  have hn0 : 0 < n := by omega
  have hb := block_bound x hsub hx0 N n hN hn0
  calc
    normalized x n ≤
        ((n / N : ℝ) * x N + (N : ℝ) * x 1) / (n : ℝ) := by
      exact (div_le_div_iff_of_pos_right (by positivity)).2 hb
    _ = normalized x N + (N : ℝ) * x 1 / n := by
      rw [normalized]
      field_simp
    _ < sInf (normalizedValues x) + ε + (N : ℝ) * x 1 / n := by
      linarith

private theorem normalized_tendsto_inf
    (x : ℕ → ℝ) (hsub : Subadditive x) (hx0 : Nonnegative x) :
    Tendsto (normalized x) atTop (𝓝 (sInf (normalizedValues x))) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  rcases gap25 x hsub hx0 (ε / 2) hhalf with ⟨N, hN⟩
  have htail :
      Tendsto (fun n : ℕ => (N : ℝ) * x 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat ((N : ℝ) * x 1)
  have htail_ev :
      ∀ᶠ n : ℕ in atTop, (N : ℝ) * x 1 / (n : ℝ) < ε / 2 :=
    (tendsto_order.1 htail).2 (ε / 2) hhalf
  rw [eventually_atTop] at htail_ev
  rcases htail_ev with ⟨K, hK⟩
  refine ⟨max (N + 1) K, fun n hn => ?_⟩
  have hnN : N < n := by omega
  have hnK : K ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hlower :
      sInf (normalizedValues x) ≤ normalized x n := by
    apply csInf_le
    · exact ⟨0, by
        rintro v ⟨m, hm, rfl⟩
        exact gap5 x hx0 m hm⟩
    · exact ⟨n, hn0, rfl⟩
  have hupper := hN n hnN
  have htail_small := hK n hnK
  rw [Real.dist_eq]
  apply abs_lt.2
  constructor <;> linarith

private theorem clusterSet_eq_singleton_of_tendsto
    (z : ℕ → ℝ) (a : ℝ) (hlim : Tendsto z atTop (𝓝 a)) :
    ProofGap.ClusterSet z = {a} := by
  ext v
  constructor
  · rintro ⟨p, hp, hv⟩
    have ha := hlim.comp hp.tendsto_atTop
    simpa using tendsto_nhds_unique hv ha
  · intro hv
    have : v = a := by simpa using hv
    subst v
    exact ⟨id, strictMono_id, by simpa using hlim⟩

private theorem normalized_seqLimsup_eq_inf
    (x : ℕ → ℝ) (hsub : Subadditive x) (hx0 : Nonnegative x) :
    ProofGap.seqLimsup (normalized x) = sInf (normalizedValues x) := by
  rw [ProofGap.seqLimsup,
    clusterSet_eq_singleton_of_tendsto (normalized x)
      (sInf (normalizedValues x)) (normalized_tendsto_inf x hsub hx0)]
  simp

private theorem normalized_seqLiminf_eq_inf
    (x : ℕ → ℝ) (hsub : Subadditive x) (hx0 : Nonnegative x) :
    ProofGap.seqLiminf (normalized x) = sInf (normalizedValues x) := by
  rw [ProofGap.seqLiminf,
    clusterSet_eq_singleton_of_tendsto (normalized x)
      (sInf (normalizedValues x)) (normalized_tendsto_inf x hsub hx0)]
  simp

/-- Exercise 137, gap 26. -/
theorem gap26 (x : ℕ → ℝ) (hsub : Subadditive x) (hx0 : Nonnegative x) :
    ∀ ε : ℝ, 0 < ε →
      ProofGap.seqLimsup (normalized x) ≤
        sInf (normalizedValues x) + ε := by
  intro ε hε
  rw [normalized_seqLimsup_eq_inf x hsub hx0]
  linarith

/-- Exercise 137, gap 27. -/
theorem gap27 (x : ℕ → ℝ) (hsub : Subadditive x) (hx0 : Nonnegative x) :
    ProofGap.seqLimsup (normalized x) ≤ sInf (normalizedValues x) := by
  rw [normalized_seqLimsup_eq_inf x hsub hx0]

/-- Exercise 137, gap 28. -/
theorem gap28 (x : ℕ → ℝ) (hsub : Subadditive x) (hx0 : Nonnegative x) :
    ProofGap.seqLimsup (normalized x) = ProofGap.seqLiminf (normalized x) := by
  rw [normalized_seqLimsup_eq_inf x hsub hx0,
    normalized_seqLiminf_eq_inf x hsub hx0]

/-- Exercise 137, gap 29. -/
theorem gap29 (x : ℕ → ℝ) (hsub : Subadditive x) (hx0 : Nonnegative x) :
    ∃ a : ℝ, Tendsto (normalized x) atTop (𝓝 a) := by
  exact ⟨sInf (normalizedValues x), normalized_tendsto_inf x hsub hx0⟩

/-- Exercise 137, gap 30. -/
theorem gap30 (x : ℕ → ℝ) (hsub : Subadditive x) (hx0 : Nonnegative x) :
    ∃ a : ℝ, Tendsto (normalized x) atTop (𝓝 a) := by
  exact gap29 x hsub hx0

end

end ProofGap.Exercise137
