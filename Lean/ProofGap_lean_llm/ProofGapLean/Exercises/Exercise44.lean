import ProofGapLean.Prelude.Sequences

open scoped Topology

/-!
# Exercise 44

Semantic formalization of Exercise 44, gaps 1,...,6.
The sequence is written explicitly by parity.
-/

namespace ProofGap.Exercise44

noncomputable section

def x (n : ℕ) : ℝ :=
  if Even n then (n : ℝ) else 1 / (n : ℝ)

def ParityFormula : Prop :=
  ∀ k : ℕ, 0 < k →
    x (2 * k) = (2 * k : ℕ) ∧
      x (2 * k - 1) = 1 / ((2 * k - 1 : ℕ) : ℝ)

def EvenSubsequenceDiverges : Prop :=
  Tendsto (fun k : ℕ => x (2 * k)) atTop atTop

def OddSubsequenceConverges : Prop :=
  Tendsto (fun k : ℕ => x (2 * k - 1)) atTop (𝓝 0)

def BoundedSequence (u : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, |u n| ≤ C

def DoesNotTendToInfinity : Prop :=
  ¬ Tendsto x atTop atTop

/-- Exercise 44, gap 1; repaired to quantified parity cases. -/
theorem gap1 :
    ParityFormula := by
  intro k hk
  have heven : Even (2 * k) := ⟨k, by omega⟩
  have hodd : ¬ Even (2 * k - 1) := by
    rintro ⟨m, hm⟩
    omega
  constructor
  · simp [x, heven]
  · simp [x, hodd]

/-- Exercise 44, gap 2. -/
theorem gap2
    (h1 : ParityFormula) :
    EvenSubsequenceDiverges := by
  unfold EvenSubsequenceDiverges
  rw [Filter.tendsto_atTop]
  intro B
  filter_upwards [Filter.eventually_gt_atTop (Nat.floor B)] with k hk
  have hkpos : 0 < k := by
    have : 0 ≤ Nat.floor B := Nat.zero_le _
    omega
  rw [(h1 k hkpos).1]
  have hfloor : B < ((Nat.floor B : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one B
  have hsuc : Nat.floor B + 1 ≤ k := Nat.succ_le_iff.mpr hk
  have hcast : ((Nat.floor B : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by
    exact_mod_cast hsuc
  norm_num at *
  linarith

/-- Exercise 44, gap 3. -/
theorem gap3
    (h1 : ParityFormula)
    (h2 : EvenSubsequenceDiverges) :
    OddSubsequenceConverges := by
  unfold OddSubsequenceConverges
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨Nat.floor (1 / ε) + 1, ?_⟩
  intro k hk
  have hkpos : 0 < k := by omega
  rw [(h1 k hkpos).2]
  have hfloor : 1 / ε < ((Nat.floor (1 / ε) : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hcast : ((Nat.floor (1 / ε) : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by
    exact_mod_cast hk
  have hkden : k ≤ 2 * k - 1 := by omega
  have hdenpos : 0 < ((2 * k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 2 * k - 1 by omega)
  have hrecip : 1 / ε < ((2 * k - 1 : ℕ) : ℝ) := by
    exact hfloor.trans_le (hcast.trans (by exact_mod_cast hkden))
  have hprod : 1 < ((2 * k - 1 : ℕ) : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hrecip
  simp only [Real.dist_eq, sub_zero, abs_of_pos (one_div_pos.mpr hdenpos)]
  apply (div_lt_iff₀ hdenpos).2
  simpa [mul_comm] using hprod

/-- Exercise 44, gap 4. -/
theorem gap4
    (h2 : EvenSubsequenceDiverges) :
    ¬ BoundedSequence x := by
  rintro ⟨C, hC⟩
  have hev : ∀ᶠ k in atTop, C + 1 ≤ x (2 * k) :=
    (Filter.tendsto_atTop.1 h2) (C + 1)
  obtain ⟨k, hk⟩ := hev.exists
  have hbound := hC (2 * k)
  have hxnonneg : 0 ≤ x (2 * k) := by
    unfold x
    split <;> positivity
  rw [abs_of_nonneg hxnonneg] at hbound
  linarith

/-- Exercise 44, gap 5. -/
theorem gap5
    (h3 : OddSubsequenceConverges)
    (h4 : ¬ BoundedSequence x) :
    DoesNotTendToInfinity := by
  intro hx
  have hp : Tendsto (fun k : ℕ => 2 * k - 1) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.eventually_ge_atTop (N + 1)] with k hk
    omega
  have hxodd :
      Tendsto (fun k : ℕ => x (2 * k - 1)) atTop atTop :=
    hx.comp hp
  have hhigh : ∀ᶠ k in atTop, (1 : ℝ) ≤ x (2 * k - 1) :=
    (Filter.tendsto_atTop.1 hxodd) 1
  have hlow : ∀ᶠ k in atTop, x (2 * k - 1) < (1 : ℝ) :=
    h3.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨k, hkhigh, hklow⟩ := (hhigh.and hlow).exists
  linarith

/-- Exercise 44, gap 6. -/
theorem gap6
    (h4 : ¬ BoundedSequence x)
    (h5 : DoesNotTendToInfinity) :
    ¬ BoundedSequence x ∧ DoesNotTendToInfinity := by
  exact ⟨h4, h5⟩

end

end ProofGap.Exercise44
