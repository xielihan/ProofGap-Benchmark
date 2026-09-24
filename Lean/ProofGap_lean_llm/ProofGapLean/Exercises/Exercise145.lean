import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import ProofGapLean.Exercises.Exercise143
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LHopital

open Filter Topology

namespace ProofGap.Exercise145

noncomputable section

def powSum (p n : ℕ) : ℝ := ∑ i ∈ Finset.Icc 1 n, (i : ℝ) ^ p
def oddPowSum (p n : ℕ) : ℝ := ∑ i ∈ Finset.Icc 1 n, ((2 * i - 1 : ℕ) : ℝ) ^ p
def y (p n : ℕ) : ℝ := (n : ℝ) ^ (p + 1)
def v (p n : ℕ) : ℝ := (n : ℝ) ^ p
def u (p n : ℕ) : ℝ := powSum p n - (n : ℝ) ^ (p + 1) / (p + 1 : ℝ)
def firstRatio (p n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ p / ((((n + 1 : ℕ) : ℝ) ^ (p + 1)) - (n : ℝ) ^ (p + 1))
def secondRatio (p n : ℕ) : ℝ :=
  (u p (n + 1) - u p n) / (v p (n + 1) - v p n)
def oddRatio (p n : ℕ) : ℝ :=
  (((2 * n + 1 : ℕ) : ℝ) ^ p) /
    ((((n + 1 : ℕ) : ℝ) ^ (p + 1)) - (n : ℝ) ^ (p + 1))

/-- Exercise 145, gap 1. -/
theorem gap1 (p : ℕ) : StrictMono (y p) := by
  intro m n hmn
  unfold y
  exact pow_lt_pow_left₀ (by exact_mod_cast hmn) (Nat.cast_nonneg m) (by omega)

/-- Exercise 145, gap 2. -/
theorem gap2 (p : ℕ) : Tendsto (y p) atTop atTop := by
  have hcast :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  apply Filter.tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ)) (g := y p)
  · intro n
    cases n with
    | zero => simp [y]
    | succ n =>
        exact le_self_pow₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
          (by omega)
  · exact hcast

private theorem invNatPos :
    Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_one_div_atTop_nhds_zero_nat, ?_⟩
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  simp only [Set.mem_Ioi]
  positivity

private theorem denomLimit (p : ℕ) :
    Tendsto (fun n : ℕ =>
      ((((n + 1 : ℕ) : ℝ) ^ (p + 1) - (n : ℝ) ^ (p + 1)) /
        (n : ℝ) ^ p))
      atTop (𝓝 (p + 1 : ℝ)) := by
  have hd : HasDerivAt (fun t : ℝ => (1 + t) ^ (p + 1))
      (p + 1 : ℝ) 0 := by
    convert ((hasDerivAt_id (𝕜 := ℝ) (x := 0)).const_add 1).pow (p + 1) using 1 <;>
      norm_num
  have hslope :
      Tendsto (fun t : ℝ => (1 / t) * ((1 + t) ^ (p + 1) - 1))
        (𝓝[>] (0 : ℝ)) (𝓝 (p + 1 : ℝ)) := by
    simpa [smul_eq_mul, mul_comm] using hd.tendsto_slope_zero_right
  apply (hslope.comp invNatPos).congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  change 1 / (1 / (n : ℝ)) * ((1 + 1 / (n : ℝ)) ^ (p + 1) - 1) =
    ((((n + 1 : ℕ) : ℝ) ^ (p + 1) - (n : ℝ) ^ (p + 1)) / (n : ℝ) ^ p)
  norm_num [Nat.cast_add, Nat.cast_one]
  have hbase : 1 + (n : ℝ)⁻¹ = ((n : ℝ) + 1) / (n : ℝ) := by
    field_simp [hn0]
  rw [hbase, div_pow]
  field_simp [hn0]
  ring

private theorem normalizedFirstLimit (p : ℕ) :
    Tendsto (fun n : ℕ =>
      ((1 + 1 / (n : ℝ)) ^ p) /
        (((((n + 1 : ℕ) : ℝ) ^ (p + 1) - (n : ℝ) ^ (p + 1)) /
          (n : ℝ) ^ p)))
      atTop (𝓝 (1 / (p + 1 : ℝ))) := by
  have hnum : Tendsto (fun n : ℕ => (1 + 1 / (n : ℝ)) ^ p)
      atTop (𝓝 (1 : ℝ)) := by
    convert (tendsto_const_nhds.add
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).pow p using 1 <;> norm_num
  convert hnum.div (denomLimit p) (by positivity) using 1 <;> norm_num

/-- Exercise 145, gap 3; the increment quotient is named explicitly. -/
theorem gap3 (p : ℕ) :
    Tendsto (firstRatio p) atTop (𝓝 (1 / (p + 1 : ℝ))) := by
  apply (normalizedFirstLimit p).congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  unfold firstRatio
  have hbase : 1 + (n : ℝ)⁻¹ = ((n : ℝ) + 1) / (n : ℝ) := by
    field_simp [hn0]
  norm_num [Nat.cast_add, Nat.cast_one]
  rw [hbase, div_pow]
  field_simp [hn0]

/-- Exercise 145, gap 4; replace the informal little-o expression by its normalized quotient. -/
theorem gap4 (p : ℕ) :
    Tendsto (fun n : ℕ =>
      ((1 + 1 / (n : ℝ)) ^ p) /
        (((((n + 1 : ℕ) : ℝ) ^ (p + 1) - (n : ℝ) ^ (p + 1)) /
          (n : ℝ) ^ p)))
      atTop (𝓝 (1 / (p + 1 : ℝ))) := by
  exact normalizedFirstLimit p

/-- Exercise 145, gap 5. -/
theorem gap5 (p : ℕ) :
    Tendsto (firstRatio p) atTop (𝓝 (1 / (p + 1 : ℝ))) := by
  exact gap3 p

/-- Exercise 145, gap 6. -/
theorem gap6 (p : ℕ) :
    Tendsto (fun n => (powSum p (n + 1) - powSum p n) /
      (y p (n + 1) - y p n)) atTop (𝓝 (1 / (p + 1 : ℝ))) := by
  apply (gap3 p).congr'
  filter_upwards with n
  have hsum :
      powSum p (n + 1) = powSum p n + ((n + 1 : ℕ) : ℝ) ^ p := by
    unfold powSum
    rw [show Finset.Icc 1 (n + 1) =
      insert (n + 1) (Finset.Icc 1 n) by
        ext i
        simp
        omega]
    simp [add_comm]
  simp [firstRatio, y, hsum]

/-- Exercise 145, gap 7. -/
theorem gap7 (p : ℕ) :
    (fun n => powSum p n / y p n) =
      (fun n => powSum p n / (n : ℝ) ^ (p + 1)) := by
  rfl

/-- Exercise 145, gap 8. -/
theorem gap8 (p : ℕ) :
    Tendsto (fun n => powSum p n / (n : ℝ) ^ (p + 1))
      atTop (𝓝 (1 / (p + 1 : ℝ))) := by
  exact ProofGap.Exercise143.gap22
    (powSum p) (y p) (1 / (p + 1 : ℝ))
    (gap1 p) (gap2 p) (gap6 p)

/-- Exercise 145, gap 9. -/
theorem gap9 (p : ℕ) :
    Tendsto (fun n => powSum p n / y p n)
      atTop (𝓝 (1 / (p + 1 : ℝ))) := by
  simpa [y] using gap8 p

/-- Exercise 145, gap 10; p>0 is required for strict increase. -/
theorem gap10 (p : ℕ) (hp : 0 < p) : StrictMono (v p) := by
  intro m n hmn
  unfold v
  exact pow_lt_pow_left₀ (by exact_mod_cast hmn) (Nat.cast_nonneg m) hp.ne'

/-- Exercise 145, gap 11; p>0 is required for divergence. -/
theorem gap11 (p : ℕ) (hp : 0 < p) : Tendsto (v p) atTop atTop := by
  have hcast :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  apply Filter.tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ)) (g := v p)
  · intro n
    cases n with
    | zero => simp [v]
    | succ n =>
        exact le_self_pow₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
          hp.ne'
  · exact hcast

/-- Exercise 145, gap 12; the exact increment quotient. -/
theorem gap12 (p n : ℕ) :
    secondRatio p n =
      (((p + 1 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ p +
        (n : ℝ) ^ (p + 1) - ((n + 1 : ℕ) : ℝ) ^ (p + 1)) /
        ((p + 1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ p - (n : ℝ) ^ p))) := by
  have hsum :
      powSum p (n + 1) = powSum p n + ((n + 1 : ℕ) : ℝ) ^ p := by
    unfold powSum
    rw [show Finset.Icc 1 (n + 1) =
      insert (n + 1) (Finset.Icc 1 n) by
        ext i
        simp
        omega]
    simp [add_comm]
  unfold secondRatio u v
  rw [hsum]
  by_cases hp0 : p = 0
  · simp [hp0]
  have hpow :
      (n : ℝ) ^ p < ((n + 1 : ℕ) : ℝ) ^ p := by
    exact pow_lt_pow_left₀ (by norm_num) (Nat.cast_nonneg n) hp0
  have hdiff :
      ((n + 1 : ℕ) : ℝ) ^ p - (n : ℝ) ^ p ≠ 0 :=
    ne_of_gt (sub_pos.mpr hpow)
  field_simp [hdiff]
  ring

private theorem quadraticLimit (p : ℕ) :
    Tendsto (fun t : ℝ =>
      (((p + 1 : ℝ) * t * (1 + t) ^ p + 1 - (1 + t) ^ (p + 1)) / t ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 ((p + 1 : ℝ) * p / 2)) := by
  let f : ℝ → ℝ := fun t =>
    (p + 1 : ℝ) * t * (1 + t) ^ p + 1 - (1 + t) ^ (p + 1)
  let fp : ℝ → ℝ := fun t =>
    (p + 1 : ℝ) * p * t * (1 + t) ^ (p - 1)
  let g : ℝ → ℝ := fun t => t ^ 2
  let gp : ℝ → ℝ := fun t => 2 * t
  have hff : ∀ᶠ t in 𝓝[>] (0 : ℝ), HasDerivAt f (fp t) t := by
    filter_upwards with t
    have hb : HasDerivAt (fun x : ℝ => 1 + x) 1 t := by
      convert (hasDerivAt_id t).const_add 1 using 1 <;> simp
    dsimp [f, fp]
    convert (((((hasDerivAt_id t).const_mul (p + 1 : ℝ)).mul
      (hb.pow p)).add_const 1).sub (hb.pow (p + 1))) using 1 <;> simp <;> ring
  have hgg : ∀ᶠ t in 𝓝[>] (0 : ℝ), HasDerivAt g (gp t) t := by
    filter_upwards with t
    dsimp [g, gp]
    convert (hasDerivAt_id t).pow 2 using 1 <;> norm_num
  have hgp : ∀ᶠ t in 𝓝[>] (0 : ℝ), gp t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    dsimp [gp]
    exact mul_ne_zero (by norm_num) (ne_of_gt ht')
  have hf0 : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hb : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := by
      simpa only [id_eq] using (hasDerivAt_id (0 : ℝ)).const_add 1
    have hd : HasDerivAt f 0 0 := by
      dsimp [f]
      convert (((((hasDerivAt_id 0).const_mul (p + 1 : ℝ)).mul
        (hb.pow p)).add_const 1).sub (hb.pow (p + 1))) using 1 <;> simp
    simpa [f] using hd.continuousAt.tendsto.mono_left inf_le_left
  have hg0 : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hd : HasDerivAt g 0 0 := by
      dsimp [g]
      convert (hasDerivAt_id (0 : ℝ)).pow 2 using 1 <;> norm_num
    simpa [g] using hd.continuousAt.tendsto.mono_left inf_le_left
  have hdiv : Tendsto (fun t => fp t / gp t) (𝓝[>] (0 : ℝ))
      (𝓝 ((p + 1 : ℝ) * p / 2)) := by
    have hcont : Tendsto
        (fun t : ℝ => (p + 1 : ℝ) * p / 2 * (1 + t) ^ (p - 1))
        (𝓝[>] (0 : ℝ)) (𝓝 ((p + 1 : ℝ) * p / 2)) := by
      have ht : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_left inf_le_left
      have hc : Tendsto (fun _ : ℝ => (p + 1 : ℝ) * p / 2)
          (𝓝[>] (0 : ℝ)) (𝓝 ((p + 1 : ℝ) * p / 2)) :=
        tendsto_const_nhds
      convert hc.mul ((tendsto_const_nhds.add ht).pow (p - 1)) using 1 <;> norm_num
    apply hcont.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    dsimp [fp, gp]
    field_simp [ne_of_gt ht']
  exact HasDerivAt.lhopital_zero_nhdsGT hff hgg hgp hf0 hg0 hdiv

private theorem numeratorNormalizedLimit (q : ℕ) :
    Tendsto (fun n : ℕ =>
      (((q + 2 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ (q + 1) +
        (n : ℝ) ^ (q + 2) - ((n + 1 : ℕ) : ℝ) ^ (q + 2)) /
        (n : ℝ) ^ q))
      atTop (𝓝 ((q + 2 : ℝ) * (q + 1 : ℝ) / 2)) := by
  have h := (quadraticLimit (q + 1)).comp invNatPos
  norm_num [Nat.cast_add, Nat.cast_one, Nat.add_assoc] at h
  have hconst :
      ((q : ℝ) + 1 + 1) * ((q : ℝ) + 1) / 2 =
        (q + 2 : ℝ) * (q + 1 : ℝ) / 2 := by
    ring
  rw [hconst] at h
  apply h.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  change
    ((((q : ℝ) + 1 + 1) * (n : ℝ)⁻¹ *
        (1 + (n : ℝ)⁻¹) ^ (q + 1) + 1 -
        (1 + (n : ℝ)⁻¹) ^ (q + 2)) /
      ((n : ℝ)⁻¹) ^ 2) =
    (((q + 2 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ (q + 1) +
        (n : ℝ) ^ (q + 2) - ((n + 1 : ℕ) : ℝ) ^ (q + 2)) /
      (n : ℝ) ^ q)
  norm_num [Nat.cast_add, Nat.cast_one]
  have hbase : 1 + (n : ℝ)⁻¹ = ((n : ℝ) + 1) / (n : ℝ) := by
    field_simp [hn0]
  rw [hbase, div_pow, div_pow]
  field_simp [hn0]
  ring

private theorem secondRawLimit (q : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((q + 2 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ (q + 1) +
            (n : ℝ) ^ (q + 2) - ((n + 1 : ℕ) : ℝ) ^ (q + 2)) /
          ((q + 2 : ℝ) *
            (((n + 1 : ℕ) : ℝ) ^ (q + 1) - (n : ℝ) ^ (q + 1)))
      )
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hden : Tendsto (fun n : ℕ =>
      (q + 2 : ℝ) *
        (((((n + 1 : ℕ) : ℝ) ^ (q + 1) - (n : ℝ) ^ (q + 1)) /
          (n : ℝ) ^ q)))
      atTop (𝓝 ((q + 2 : ℝ) * (q + 1 : ℝ))) := by
    have hc : Tendsto (fun _ : ℕ => (q + 2 : ℝ)) atTop
        (𝓝 (q + 2 : ℝ)) := tendsto_const_nhds
    exact hc.mul (denomLimit q)
  have hquot := (numeratorNormalizedLimit q).div hden (by positivity)
  have hlim :
      ((q + 2 : ℝ) * (q + 1 : ℝ) / 2) /
        ((q + 2 : ℝ) * (q + 1 : ℝ)) = (1 / 2 : ℝ) := by
    field_simp
  rw [hlim] at hquot
  apply hquot.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  change
    ((((q + 2 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ (q + 1) +
        (n : ℝ) ^ (q + 2) - ((n + 1 : ℕ) : ℝ) ^ (q + 2)) /
      (n : ℝ) ^ q) /
      ((q + 2 : ℝ) *
        ((((n + 1 : ℕ) : ℝ) ^ (q + 1) - (n : ℝ) ^ (q + 1)) /
          (n : ℝ) ^ q))) =
    (((q + 2 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ (q + 1) +
        (n : ℝ) ^ (q + 2) - ((n + 1 : ℕ) : ℝ) ^ (q + 2)) /
      ((q + 2 : ℝ) *
        (((n + 1 : ℕ) : ℝ) ^ (q + 1) - (n : ℝ) ^ (q + 1))))
  have hpow :
      (n : ℝ) ^ (q + 1) < ((n + 1 : ℕ) : ℝ) ^ (q + 1) :=
    pow_lt_pow_left₀
      (by exact_mod_cast Nat.lt_succ_self n) (Nat.cast_nonneg n) (by omega)
  have hdiff :
      ((n + 1 : ℕ) : ℝ) ^ (q + 1) - (n : ℝ) ^ (q + 1) ≠ 0 :=
    ne_of_gt (sub_pos.mpr hpow)
  field_simp [hn0, hdiff]

/-- Exercise 145, gap 13; the ellipses are replaced by the asymptotic limit they denote. -/
theorem gap13 (p : ℕ) (hp : 0 < p) :
    Tendsto (secondRatio p) atTop (𝓝 (1 / 2 : ℝ)) := by
  cases p with
  | zero => omega
  | succ q =>
      apply (secondRawLimit q).congr'
      filter_upwards with n
      rw [gap12]
      norm_num [Nat.cast_add, Nat.cast_one, Nat.add_assoc]
      rw [show (q : ℝ) + 1 + 1 = (q : ℝ) + 2 by ring]

/-- Exercise 145, gap 14. -/
theorem gap14 (p : ℕ) (hp : 0 < p) :
    Tendsto (secondRatio p) atTop (𝓝 (1 / 2 : ℝ)) := by
  exact gap13 p hp

/-- Exercise 145, gap 15. -/
theorem gap15 (p : ℕ) (hp : 0 < p) :
    Tendsto (secondRatio p) atTop (𝓝 (1 / 2 : ℝ)) := by
  exact gap13 p hp

/-- Exercise 145, gap 16. -/
theorem gap16 (p : ℕ) :
    (fun n => u p n / v p n) =
      (fun n => powSum p n / (n : ℝ) ^ p - (n : ℝ) / (p + 1 : ℝ)) := by
  funext n
  by_cases hn : n = 0
  · subst n
    simp [u, v, powSum]
  · unfold u v
    have hnpow : (n : ℝ) ^ p ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn)
    field_simp [hnpow]
    ring

/-- Exercise 145, gap 17. -/
theorem gap17 (p : ℕ) (hp : 0 < p) :
    Tendsto (fun n => powSum p n / (n : ℝ) ^ p -
      (n : ℝ) / (p + 1 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := by
  have h := ProofGap.Exercise143.gap22
    (u p) (v p) (1 / 2 : ℝ)
    (gap10 p hp) (gap11 p hp) (gap13 p hp)
  change Tendsto (fun n => u p n / v p n) atTop (𝓝 (1 / 2 : ℝ)) at h
  rw [gap16 p] at h
  exact h

/-- Exercise 145, gap 18. -/
theorem gap18 (p : ℕ) (hp : 0 < p) :
    Tendsto (fun n => u p n / v p n) atTop (𝓝 (1 / 2 : ℝ)) := by
  exact ProofGap.Exercise143.gap22
    (u p) (v p) (1 / 2 : ℝ)
    (gap10 p hp) (gap11 p hp) (gap13 p hp)

/-- Exercise 145, gap 19. -/
theorem gap19 (p : ℕ) : StrictMono (y p) := by
  exact gap1 p

/-- Exercise 145, gap 20. -/
theorem gap20 (p : ℕ) : Tendsto (y p) atTop atTop := by
  exact gap2 p

private theorem normalizedOddLimit (p : ℕ) :
    Tendsto (fun n : ℕ =>
      ((2 : ℝ) + 1 / n) ^ p /
        (((((n + 1 : ℕ) : ℝ) ^ (p + 1) - (n : ℝ) ^ (p + 1)) /
          (n : ℝ) ^ p)))
      atTop (𝓝 ((2 : ℝ) ^ p / (p + 1 : ℝ))) := by
  have hnum : Tendsto (fun n : ℕ => ((2 : ℝ) + 1 / (n : ℝ)) ^ p)
      atTop (𝓝 ((2 : ℝ) ^ p)) := by
    convert ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).add
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).pow p using 1 <;> norm_num
  exact hnum.div (denomLimit p) (by positivity)

/-- Exercise 145, gap 21. -/
theorem gap21 (p : ℕ) :
    Tendsto (oddRatio p) atTop (𝓝 ((2 : ℝ) ^ p / (p + 1 : ℝ))) := by
  apply (normalizedOddLimit p).congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  unfold oddRatio
  norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  have hbase : (2 : ℝ) + (n : ℝ)⁻¹ =
      (2 * (n : ℝ) + 1) / (n : ℝ) := by
    field_simp [hn0]
  rw [hbase, div_pow]
  field_simp [hn0]

/-- Exercise 145, gap 22; replace little-o by the normalized quotient. -/
theorem gap22 (p : ℕ) :
    Tendsto (fun n : ℕ =>
      ((2 : ℝ) + 1 / n) ^ p /
        (((((n + 1 : ℕ) : ℝ) ^ (p + 1) - (n : ℝ) ^ (p + 1)) /
          (n : ℝ) ^ p)))
      atTop (𝓝 ((2 : ℝ) ^ p / (p + 1 : ℝ))) := by
  exact normalizedOddLimit p

/-- Exercise 145, gap 23. -/
theorem gap23 (p : ℕ) :
    Tendsto (oddRatio p) atTop (𝓝 ((2 : ℝ) ^ p / (p + 1 : ℝ))) := by
  exact gap21 p

/-- Exercise 145, gap 24. -/
theorem gap24 (p : ℕ) :
    Tendsto (fun n => (oddPowSum p (n + 1) - oddPowSum p n) /
      (y p (n + 1) - y p n))
      atTop (𝓝 ((2 : ℝ) ^ p / (p + 1 : ℝ))) := by
  apply (gap21 p).congr'
  filter_upwards with n
  have hsum :
      oddPowSum p (n + 1) =
        oddPowSum p n + ((2 * n + 1 : ℕ) : ℝ) ^ p := by
    unfold oddPowSum
    rw [show Finset.Icc 1 (n + 1) =
      insert (n + 1) (Finset.Icc 1 n) by
        ext i
        simp
        omega]
    simp [add_comm]
    congr 1
    push_cast
    ring
  simp [oddRatio, y, hsum]

/-- Exercise 145, gap 25. -/
theorem gap25 (p : ℕ) :
    (fun n => oddPowSum p n / y p n) =
      (fun n => oddPowSum p n / (n : ℝ) ^ (p + 1)) := by
  rfl

/-- Exercise 145, gap 26. -/
theorem gap26 (p : ℕ) :
    Tendsto (fun n => oddPowSum p n / (n : ℝ) ^ (p + 1))
      atTop (𝓝 ((2 : ℝ) ^ p / (p + 1 : ℝ))) := by
  exact ProofGap.Exercise143.gap22
    (oddPowSum p) (y p) ((2 : ℝ) ^ p / (p + 1 : ℝ))
    (gap19 p) (gap20 p) (gap24 p)

/-- Exercise 145, gap 27. -/
theorem gap27 (p : ℕ) :
    Tendsto (fun n => oddPowSum p n / y p n)
      atTop (𝓝 ((2 : ℝ) ^ p / (p + 1 : ℝ))) := by
  simpa [y] using gap26 p

/-- Exercise 145, gap 28; the three asymptotic formulas. -/
theorem gap28 (p : ℕ) (hp : 0 < p) :
    Tendsto (fun n => powSum p n / (n : ℝ) ^ (p + 1))
        atTop (𝓝 (1 / (p + 1 : ℝ))) ∧
    Tendsto (fun n => powSum p n / (n : ℝ) ^ p -
        (n : ℝ) / (p + 1 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) ∧
    Tendsto (fun n => oddPowSum p n / (n : ℝ) ^ (p + 1))
        atTop (𝓝 ((2 : ℝ) ^ p / (p + 1 : ℝ))) := by
  exact ⟨gap8 p, gap17 p hp, gap26 p⟩

end

end ProofGap.Exercise145
