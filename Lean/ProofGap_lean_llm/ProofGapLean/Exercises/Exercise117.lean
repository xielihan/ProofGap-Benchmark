import ProofGapLean.Prelude.Sequences

open Filter Topology

namespace ProofGap.Exercise117

def blockStart (q : ℕ) : ℕ :=
  q * (q - 1) / 2

def GridEnumeration (x : ℕ → ℝ) : Prop :=
  (∀ q : ℕ, 0 < q →
    x (blockStart q) = 1 / (q : ℝ)) ∧
  (∀ q j : ℕ, 0 < j → j < q →
    x (blockStart q + j) = 1 / (j : ℝ) + 1 / (q : ℝ))

def target : Set ℝ :=
  {0} ∪ {v | ∃ n : ℕ, 0 < n ∧ v = 1 / (n : ℝ)}

private theorem blockStart_succ (q : ℕ) :
    blockStart (q + 1) = blockStart q + q := by
  simpa [blockStart] using Nat.triangle_succ q

private theorem exists_block_data (n : ℕ) :
    ∃ q : ℕ, ∃ j : ℕ,
      0 < q ∧ j < q ∧ n = blockStart q + j := by
  induction n with
  | zero =>
      exact ⟨1, 0, by omega, by omega, by norm_num [blockStart]⟩
  | succ n ih =>
      rcases ih with ⟨q, j, hq, hj, hn⟩
      by_cases hnext : j + 1 < q
      · exact ⟨q, j + 1, hq, hnext, by omega⟩
      · have hjq : j + 1 = q := by omega
        refine ⟨q + 1, 0, by omega, by omega, ?_⟩
        rw [blockStart_succ]
        omega

private noncomputable def row (n : ℕ) : ℕ :=
  Classical.choose (exists_block_data n)

private noncomputable def col (n : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (exists_block_data n))

private theorem block_data_spec (n : ℕ) :
    0 < row n ∧ col n < row n ∧ n = blockStart (row n) + col n :=
  Classical.choose_spec (Classical.choose_spec (exists_block_data n))

private theorem row_tendsto : Tendsto row atTop atTop := by
  apply tendsto_atTop.2
  intro Q
  filter_upwards [eventually_ge_atTop (Q * Q + Q)] with n hn
  by_contra hrow
  have hrlt : row n < Q := by omega
  have hspec := block_data_spec n
  have hbs : blockStart (row n) ≤ row n * row n := by
    unfold blockStart
    exact (Nat.div_le_self _ _).trans
      (Nat.mul_le_mul_left (row n) (Nat.sub_le _ _))
  have hnlt : n < row n * row n + row n := by omega
  have hbound : row n * row n + row n < Q * Q + Q := by
    nlinarith
  omega

private theorem reciprocal_row_tendsto :
    Tendsto (fun n : ℕ => 1 / (row n : ℝ)) atTop (𝓝 0) := by
  have hcast :
      Tendsto (fun n : ℕ => (row n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop).comp row_tendsto
  simpa [one_div] using
    ((tendsto_inv_atTop_zero :
      Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).comp hcast)

private noncomputable def approx (n : ℕ) : ℝ :=
  if col n = 0 then 0 else 1 / (col n : ℝ)

private theorem approx_mem_target (n : ℕ) : approx n ∈ target := by
  by_cases hcol : col n = 0
  · simp [approx, target, hcol]
  · right
    exact ⟨col n, Nat.pos_of_ne_zero hcol, by simp [approx, hcol]⟩

private theorem enumeration_error
    (x : ℕ → ℝ) (henum : GridEnumeration x) (n : ℕ) :
    x n = approx n + 1 / (row n : ℝ) := by
  have hs := block_data_spec n
  rcases henum with ⟨hzero, hpos⟩
  by_cases hcol : col n = 0
  · calc
      x n = x (blockStart (row n) + col n) := by rw [← hs.2.2]
      _ = x (blockStart (row n)) := by rw [hcol, add_zero]
      _ = 1 / (row n : ℝ) := hzero (row n) hs.1
      _ = approx n + 1 / (row n : ℝ) := by simp [approx, hcol]
  · calc
      x n = x (blockStart (row n) + col n) := by rw [← hs.2.2]
      _ = 1 / (col n : ℝ) + 1 / (row n : ℝ) :=
        hpos (row n) (col n) (Nat.pos_of_ne_zero hcol) hs.2.1
      _ = approx n + 1 / (row n : ℝ) := by simp [approx, hcol]

private theorem reciprocal_succ_tendsto :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have hcast :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hden :
      Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun n => by linarith) hcast
  simpa [one_div] using
    ((tendsto_inv_atTop_zero :
      Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).comp hden)

private theorem target_isClosed : IsClosed target := by
  have hcompact :
      IsCompact (Set.insert 0
        (Set.range fun n : ℕ => 1 / ((n : ℝ) + 1))) :=
    reciprocal_succ_tendsto.isCompact_insert_range
  have heq :
      target =
        Set.insert 0 (Set.range fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    ext v
    constructor
    · intro hv
      rcases hv with hv | ⟨n, hn, rfl⟩
      · exact Set.mem_insert_iff.2 (Or.inl (by simpa using hv))
      · right
        refine ⟨n - 1, ?_⟩
        change 1 / (((n - 1 : ℕ) : ℝ) + 1) = 1 / (n : ℝ)
        congr 1
        exact_mod_cast (show n - 1 + 1 = n by omega)
    · intro hv
      rcases Set.mem_insert_iff.1 hv with rfl | ⟨n, rfl⟩
      · exact Or.inl rfl
      · right
        refine ⟨n + 1, by omega, ?_⟩
        norm_num
  rw [heq]
  exact hcompact.isClosed

private theorem blockStart_succ_strict (q : ℕ) (hq : 0 < q) :
    blockStart q < blockStart (q + 1) := by
  rw [blockStart_succ]
  omega

/-- Exercise 117, gap 1; replace both ellipses by sets/index data. -/
theorem gap1
    (x : ℕ → ℝ)
    (henum : GridEnumeration x) :
    ProofGap.ClusterSet x = target := by
  ext a
  constructor
  · intro ha
    rcases ha with ⟨p, hp, hlim⟩
    have herr :
        Tendsto (fun k : ℕ => 1 / (row (p k) : ℝ)) atTop (𝓝 0) :=
      reciprocal_row_tendsto.comp hp.tendsto_atTop
    have happ :
        Tendsto (approx ∘ p) atTop (𝓝 a) := by
      have hsub := hlim.sub herr
      have heq :
          (fun k : ℕ => (x ∘ p) k - 1 / (row (p k) : ℝ)) =ᶠ[atTop]
            (approx ∘ p) := by
        filter_upwards with k
        change x (p k) - 1 / (row (p k) : ℝ) = approx (p k)
        rw [enumeration_error x henum (p k)]
        ring
      simpa using hsub.congr' heq
    exact target_isClosed.mem_of_tendsto happ
      (Filter.Eventually.of_forall fun k => approx_mem_target (p k))
  · intro ha
    rcases ha with ha0 | ⟨m, hm, rfl⟩
    · have ha0 : a = 0 := by simpa using ha0
      subst a
      let p : ℕ → ℕ := fun k => blockStart (k + 1)
      have hp : StrictMono p := strictMono_nat_of_lt_succ fun k => by
        dsimp [p]
        exact blockStart_succ_strict (k + 1) (by omega)
      refine ⟨p, hp, ?_⟩
      apply reciprocal_succ_tendsto.congr'
      filter_upwards with k
      have hx := henum.1 (k + 1) (by omega)
      simpa [p, Function.comp_apply] using hx.symm
    · let p : ℕ → ℕ := fun k =>
        blockStart (m + k + 1) + m
      have hp : StrictMono p := strictMono_nat_of_lt_succ fun k => by
        dsimp [p]
        have hs := blockStart_succ_strict (m + k + 1) (by omega)
        rw [show m + (k + 1) + 1 = (m + k + 1) + 1 by omega]
        exact Nat.add_lt_add_right hs m
      refine ⟨p, hp, ?_⟩
      have hlim :
          Tendsto
            (fun k : ℕ => 1 / (m : ℝ) +
              1 / (((m + k : ℕ) : ℝ) + 1))
            atTop (𝓝 (1 / (m : ℝ))) := by
        have h :
            Tendsto
              (fun k : ℕ => (1 / (m : ℝ)) +
                1 / (((m + k : ℕ) : ℝ) + 1))
              atTop (𝓝 ((1 / (m : ℝ)) + 0)) := by
          apply tendsto_const_nhds.add
          have hshift :
              Tendsto (fun k : ℕ => m + k) atTop atTop := by
            apply tendsto_atTop.2
            intro b
            filter_upwards [eventually_ge_atTop b] with k hk
            omega
          exact reciprocal_succ_tendsto.comp hshift
        simpa using h
      apply hlim.congr'
      filter_upwards with k
      have hx := henum.2 (m + k + 1) m hm (by omega)
      simpa [p, Function.comp_apply, add_assoc, add_comm, add_left_comm]
        using hx.symm

/-- Exercise 117, gap 2. -/
theorem gap2 :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  exact reciprocal_succ_tendsto

/-- Exercise 117, gap 3. -/
theorem gap3 :
    Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
  have h :
      Tendsto (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 1))
        atTop (𝓝 ((1 : ℝ) + 0)) :=
    tendsto_const_nhds.add reciprocal_succ_tendsto
  simpa using h

/-- Exercise 117, gap 4. -/
theorem gap4 :
    Tendsto (fun n : ℕ => 1 / 2 + 1 / ((n : ℝ) + 1))
      atTop (𝓝 (1 / 2)) := by
  have h :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) + 1 / ((n : ℝ) + 1))
        atTop (𝓝 ((1 / 2 : ℝ) + 0)) :=
    tendsto_const_nhds.add reciprocal_succ_tendsto
  simpa using h

/-- Exercise 117, gap 5. -/
theorem gap5 :
    Tendsto (fun n : ℕ => 1 / 3 + 1 / ((n : ℝ) + 1))
      atTop (𝓝 (1 / 3)) := by
  have h :
      Tendsto (fun n : ℕ => (1 / 3 : ℝ) + 1 / ((n : ℝ) + 1))
        atTop (𝓝 ((1 / 3 : ℝ) + 0)) :=
    tendsto_const_nhds.add reciprocal_succ_tendsto
  simpa using h

end ProofGap.Exercise117
