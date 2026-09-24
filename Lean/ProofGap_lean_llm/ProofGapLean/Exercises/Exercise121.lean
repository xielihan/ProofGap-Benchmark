import ProofGapLean.Prelude.Sequences

open Filter Topology

namespace ProofGap.Exercise121

def targets (a : ℕ → ℝ) (p : ℕ) : Set ℝ :=
  {v | ∃ i : ℕ, 1 ≤ i ∧ i ≤ p ∧ v = a i}

def Construction (x a : ℕ → ℝ) (p : ℕ) : Prop :=
  ∀ n i : ℕ, 2 ≤ n → 1 ≤ i → i ≤ p →
    x ((n - 2) * p + i) = a i - 1 / (n : ℝ)

private def rowNumber (p n : ℕ) : ℕ :=
  (n - 1) / p + 2

private def indexNumber (p n : ℕ) : ℕ :=
  (n - 1) % p + 1

private theorem index_data (p n : ℕ) (hp : 0 < p) (hn : 0 < n) :
    2 ≤ rowNumber p n ∧
      1 ≤ indexNumber p n ∧
      indexNumber p n ≤ p ∧
      (rowNumber p n - 2) * p + indexNumber p n = n := by
  have hrow : 2 ≤ (n - 1) / p + 2 :=
    Nat.le_add_left 2 ((n - 1) / p)
  have hmod := Nat.mod_lt (n - 1) hp
  have hdecomp := Nat.div_add_mod (n - 1) p
  dsimp [rowNumber, indexNumber]
  constructor
  · exact hrow
  constructor
  · omega
  constructor
  · omega
  · rw [Nat.add_sub_cancel]
    rw [Nat.mul_comm ((n - 1) / p) p]
    omega

private theorem rowNumber_tendsto (p : ℕ) (hp : 0 < p) :
    Tendsto (rowNumber p) atTop atTop := by
  apply tendsto_atTop.2
  intro Q
  filter_upwards [eventually_ge_atTop (p * Q + 1)] with n hn
  have hdiv : Q ≤ (n - 1) / p := by
    apply (Nat.le_div_iff_mul_le hp).2
    rw [Nat.mul_comm]
    omega
  dsimp [rowNumber]
  omega

private theorem reciprocal_rowNumber_tendsto (p : ℕ) (hp : 0 < p) :
    Tendsto (fun n : ℕ => 1 / (rowNumber p n : ℝ)) atTop (𝓝 0) := by
  have hcast :
      Tendsto (fun n : ℕ => (rowNumber p n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop).comp
        (rowNumber_tendsto p hp)
  simpa [one_div] using
    ((tendsto_inv_atTop_zero :
      Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).comp hcast)

private theorem target_isClosed (a : ℕ → ℝ) (p : ℕ) :
    IsClosed (targets a p) := by
  have heq : targets a p = a '' Set.Icc 1 p := by
    ext v
    constructor
    · rintro ⟨i, hi1, hip, rfl⟩
      exact ⟨i, ⟨hi1, hip⟩, rfl⟩
    · rintro ⟨i, ⟨hi1, hip⟩, rfl⟩
      exact ⟨i, hi1, hip, rfl⟩
  rw [heq]
  exact (Set.finite_Icc 1 p).image a |>.isClosed

/-- Exercise 121, gap 1. -/
theorem gap1
    (x a : ℕ → ℝ) (p : ℕ)
    (h : ProofGap.ClusterSet x = targets a p) :
    ProofGap.ClusterSet x = targets a p := by
  exact h

/-- Exercise 121, gap 2; all construction binders are explicit. -/
theorem gap2
    (x a : ℕ → ℝ) (p : ℕ)
    (hp : 0 < p)
    (hconstruct : Construction x a p) :
    ProofGap.ClusterSet x = targets a p := by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨s, hs, hlim⟩
    have herr :
        Tendsto
          (fun k : ℕ => 1 / (rowNumber p (s k) : ℝ))
          atTop (𝓝 0) :=
      (reciprocal_rowNumber_tendsto p hp).comp hs.tendsto_atTop
    have hevent : ∀ᶠ k : ℕ in atTop, 0 < s k :=
      hs.tendsto_atTop (eventually_ge_atTop 1)
    have happ :
        Tendsto (fun k : ℕ => a (indexNumber p (s k)))
          atTop (𝓝 v) := by
      have hadd := hlim.add herr
      norm_num at hadd
      apply hadd.congr'
      filter_upwards [hevent] with k hsk
      have hd := index_data p (s k) hp hsk
      rw [show x (s k) =
          a (indexNumber p (s k)) -
            1 / (rowNumber p (s k) : ℝ) by
        calc
          x (s k) =
              x ((rowNumber p (s k) - 2) * p +
                indexNumber p (s k)) :=
            (congrArg x hd.2.2.2).symm
          _ = a (indexNumber p (s k)) -
                1 / (rowNumber p (s k) : ℝ) :=
            hconstruct (rowNumber p (s k)) (indexNumber p (s k))
              hd.1 hd.2.1 hd.2.2.1]
      ring
    apply (target_isClosed a p).mem_of_tendsto happ
    filter_upwards [hevent] with k hsk
    have hd := index_data p (s k) hp hsk
    exact ⟨indexNumber p (s k), hd.2.1, hd.2.2.1, rfl⟩
  · intro hv
    rcases hv with ⟨i, hi1, hip, rfl⟩
    let s : ℕ → ℕ := fun k => k * p + i
    have hs : StrictMono s := strictMono_nat_of_lt_succ fun k => by
      dsimp [s]
      rw [Nat.add_mul]
      omega
    refine ⟨s, hs, ?_⟩
    have hindex :
        Tendsto (fun k : ℕ => k + 2) atTop atTop := by
      apply tendsto_atTop.2
      intro Q
      filter_upwards [eventually_ge_atTop Q] with k hk
      omega
    have hinv :
        Tendsto (fun k : ℕ => 1 / ((k + 2 : ℕ) : ℝ))
          atTop (𝓝 0) := by
      have hcast :
          Tendsto (fun k : ℕ => ((k + 2 : ℕ) : ℝ)) atTop atTop :=
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp hindex
      simpa [one_div] using
        ((tendsto_inv_atTop_zero :
          Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).comp hcast)
    have h :
        Tendsto
          (fun k : ℕ => a i - 1 / ((k + 2 : ℕ) : ℝ))
          atTop (𝓝 (a i - 0)) :=
      tendsto_const_nhds.sub hinv
    norm_num at h
    apply h.congr'
    filter_upwards with k
    have hx := hconstruct (k + 2) i (by omega) hi1 hip
    simpa [s, Function.comp_apply] using hx.symm

end ProofGap.Exercise121
