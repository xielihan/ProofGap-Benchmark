import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise465

noncomputable section

def indices (n : ℕ) : Finset ℕ := Finset.Icc 1 n
def product (n : ℕ) (α : ℕ → ℝ) (x : ℝ) : ℝ :=
  (indices n).prod (fun i => x + α i)
def nthRoot (n : ℕ) (x : ℝ) : ℝ := Real.rpow x (1 / (n : ℝ))
def original (n : ℕ) (α : ℕ → ℝ) (x : ℝ) : ℝ :=
  nthRoot n (product n α x) - x
def rootDenominator (n : ℕ) (α : ℕ → ℝ) (x : ℝ) : ℝ :=
  (indices n).sum (fun j =>
    Real.rpow (product n α x) ((n - j : ℕ) / (n : ℝ)) * x ^ (j - 1))
def rationalized (n : ℕ) (α : ℕ → ℝ) (x : ℝ) : ℝ :=
  (product n α x - x ^ n) / rootDenominator n α x
def normalized (n : ℕ) (α : ℕ → ℝ) (x : ℝ) : ℝ :=
  ((indices n).sum α + 1 / x) /
    ((indices n).sum (fun j =>
      (indices n).prod (fun i =>
        Real.rpow (1 + α i / x) ((n - j : ℕ) / (n : ℝ)))))
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Source: `proof_gap/exercise_465/1`; rationalize the `n`th-root difference. -/
private theorem geom_sum_Icc (n : ℕ) (a b : ℝ) :
    (a - b) * (Finset.Icc 1 n).sum (fun j => a ^ (n - j) * b ^ (j - 1)) =
      a ^ n - b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hset : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hset, Finset.sum_insert]
      · have hshift :
            (Finset.Icc 1 n).sum (fun j => a ^ (n + 1 - j) * b ^ (j - 1)) =
              a * (Finset.Icc 1 n).sum (fun j => a ^ (n - j) * b ^ (j - 1)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
          have he : n + 1 - j = (n - j) + 1 := by omega
          rw [he, pow_succ]
          ring
        rw [hshift]
        simp only [Nat.sub_self, Nat.add_sub_cancel, pow_zero, one_mul]
        calc
          (a - b) * (b ^ n + a *
              (Finset.Icc 1 n).sum (fun j => a ^ (n - j) * b ^ (j - 1))) =
              (a - b) * b ^ n +
                a * ((a - b) *
                  (Finset.Icc 1 n).sum (fun j => a ^ (n - j) * b ^ (j - 1))) := by
                    ring
          _ = (a - b) * b ^ n + a * (a ^ n - b ^ n) := by rw [ih]
          _ = a ^ (n + 1) - b ^ (n + 1) := by
            rw [pow_succ, pow_succ]
            ring
      · simp [Finset.mem_Icc]

private theorem eventually_positive_data (n : ℕ) (α : ℕ → ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      0 < x ∧ ∀ i ∈ indices n, 0 < x + α i := by
  have hx : ∀ᶠ x : ℝ in Filter.atTop, 0 < x :=
    Filter.eventually_atTop.2 ⟨1, by intro x hx; linarith⟩
  have hs : ∀ᶠ x : ℝ in Filter.atTop, ∀ i ∈ indices n, 0 < x + α i := by
    induction indices n using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        have hii : ∀ᶠ x : ℝ in Filter.atTop, 0 < x + α i :=
          Filter.eventually_atTop.2 ⟨-α i + 1, by intro x hx; linarith⟩
        filter_upwards [hii, ih] with x hxi hxs
        intro k hk
        simp only [Finset.mem_insert] at hk
        rcases hk with rfl | hk
        · exact hxi
        · exact hxs k hk
  filter_upwards [hx, hs] with x hx hs
  exact ⟨hx, hs⟩

private theorem tendsto_rpow_const_one (f : ℝ → ℝ) (c : ℝ)
    (hf : Filter.Tendsto f Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun x => Real.rpow (f x) c) Filter.atTop (nhds 1) := by
  have hlog :
      Filter.Tendsto (fun x => Real.log (f x)) Filter.atTop (nhds 0) := by
    simpa using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hf
  have hc :
      Filter.Tendsto (fun _ : ℝ => c) Filter.atTop (nhds c) :=
    tendsto_const_nhds
  have hmul :
      Filter.Tendsto (fun x => Real.log (f x) * c)
        Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using hlog.mul hc
  have hexp :
      Filter.Tendsto (fun x => Real.exp (Real.log (f x) * c))
        Filter.atTop (nhds 1) := by
    simpa using (Real.continuous_exp.tendsto 0).comp hmul
  have hfpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < f x :=
    hf (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  exact Filter.Tendsto.congr'
    (by
      filter_upwards [hfpos] with x hx
      exact (Real.rpow_def_of_pos hx c).symm)
    hexp

private theorem normalized_denominator_limit (n : ℕ) (hn : 0 < n) (α : ℕ → ℝ) :
    Filter.Tendsto
      (fun x : ℝ =>
        (indices n).sum (fun j =>
          (indices n).prod (fun i =>
            Real.rpow (1 + α i / x) ((n - j : ℕ) / (n : ℝ)))))
      Filter.atTop (nhds (n : ℝ)) := by
  classical
  have hinv : Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hbase (i : ℕ) :
      Filter.Tendsto (fun x : ℝ => 1 + α i / x) Filter.atTop (nhds 1) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv) :
        Filter.Tendsto (fun x : ℝ => 1 + α i * x⁻¹)
          Filter.atTop (nhds (1 + α i * 0)))
  have hterm (j : ℕ) (s : Finset ℕ) :
      Filter.Tendsto
        (fun x : ℝ => s.prod (fun i =>
          Real.rpow (1 + α i / x) ((n - j : ℕ) / (n : ℝ))))
        Filter.atTop (nhds 1) := by
    induction s using Finset.induction_on with
    | empty => simpa using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1))
    | @insert i s hi ih =>
        have hp := tendsto_rpow_const_one
          (fun x : ℝ => 1 + α i / x) ((n - j : ℕ) / (n : ℝ)) (hbase i)
        simpa [Finset.prod_insert hi] using hp.mul ih
  have hsum (s : Finset ℕ) :
      Filter.Tendsto
        (fun x : ℝ => s.sum (fun j =>
          (indices n).prod (fun i =>
            Real.rpow (1 + α i / x) ((n - j : ℕ) / (n : ℝ)))))
        Filter.atTop (nhds (s.card : ℝ)) := by
    induction s using Finset.induction_on with
    | empty => simpa using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) Filter.atTop (nhds 0))
    | @insert j s hj ih =>
        simpa [Finset.sum_insert hj, hj, Nat.cast_add,
          add_comm, add_left_comm, add_assoc] using
          (hterm j (indices n)).add ih
  convert hsum (indices n) using 1 <;> simp [indices]

private theorem normalized_limit (n : ℕ) (hn : 0 < n) (α : ℕ → ℝ) :
    HasLimitAtPosInfinity (normalized n α) ((indices n).sum α / n) := by
  classical
  unfold HasLimitAtPosInfinity normalized
  have hinv : Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hnum :
      Filter.Tendsto
        (fun x : ℝ => (indices n).sum α + 1 / x)
        Filter.atTop (nhds ((indices n).sum α)) := by
    simpa [one_div] using
      (tendsto_const_nhds.add hinv :
        Filter.Tendsto (fun x : ℝ => (indices n).sum α + x⁻¹)
          Filter.atTop (nhds ((indices n).sum α + 0)))
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  exact hnum.div (normalized_denominator_limit n hn α) hn0

private theorem rationalized_limit (n : ℕ) (hn : 0 < n) (α : ℕ → ℝ) :
    HasLimitAtPosInfinity (rationalized n α) ((indices n).sum α / n) := by
  classical
  unfold HasLimitAtPosInfinity
  have hinv : Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hbase (i : ℕ) :
      Filter.Tendsto (fun x : ℝ => 1 + α i / x) Filter.atTop (nhds 1) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv) :
        Filter.Tendsto (fun x : ℝ => 1 + α i * x⁻¹)
          Filter.atTop (nhds (1 + α i * 0)))
  have hprod (s : Finset ℕ) :
      Filter.Tendsto
        (fun x : ℝ => s.prod (fun i => 1 + α i / x))
        Filter.atTop (nhds 1) := by
    induction s using Finset.induction_on with
    | empty => simpa using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1))
    | @insert i s hi ih =>
        simpa [Finset.prod_insert hi] using (hbase i).mul ih
  have hscaled (s : Finset ℕ) :
      Filter.Tendsto
        (fun x : ℝ => x * (s.prod (fun i => 1 + α i / x) - 1))
        Filter.atTop (nhds (s.sum α)) := by
    induction s using Finset.induction_on with
    | empty => simpa using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) Filter.atTop (nhds 0))
    | @insert i s hi ih =>
        have hxne : ∀ᶠ x : ℝ in Filter.atTop, x ≠ 0 :=
          Filter.eventually_atTop.2
            ⟨(1 : ℝ), by
              intro x hx
              exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx)⟩
        have heq :
            (fun x : ℝ => x * ((insert i s).prod (fun k => 1 + α k / x) - 1)) =ᶠ[Filter.atTop]
              (fun x : ℝ =>
                x * (s.prod (fun k => 1 + α k / x) - 1) +
                  α i * s.prod (fun k => 1 + α k / x)) := by
          filter_upwards [hxne] with x hx
          rw [Finset.prod_insert hi]
          field_simp [hx]
          <;> ring
        have hconst :
            Filter.Tendsto (fun _ : ℝ => α i) Filter.atTop (nhds (α i)) :=
          tendsto_const_nhds
        have ht := ih.add (hconst.mul (hprod s))
        apply Filter.Tendsto.congr' heq.symm
        simpa [Finset.sum_insert hi, add_comm, add_left_comm, add_assoc] using ht
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have heq :
      rationalized n α =ᶠ[Filter.atTop]
        (fun x : ℝ =>
          (x * ((indices n).prod (fun i => 1 + α i / x) - 1)) /
            ((indices n).sum (fun j =>
              (indices n).prod (fun i =>
                Real.rpow (1 + α i / x) ((n - j : ℕ) / (n : ℝ)))))) := by
    filter_upwards [eventually_positive_data n α] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    let Q : ℝ := (indices n).prod (fun i => 1 + α i / x)
    let D : ℝ := (indices n).sum (fun j =>
      (indices n).prod (fun i =>
        Real.rpow (1 + α i / x) ((n - j : ℕ) / (n : ℝ))))
    have hfac (i : ℕ) (hi : i ∈ indices n) : 0 < 1 + α i / x := by
      rw [show 1 + α i / x = (x + α i) / x by field_simp [hx0]]
      exact div_pos (hx.2 i hi) hx.1
    have hQpos : 0 < Q := by
      dsimp [Q]
      exact Finset.prod_pos fun i hi => hfac i hi
    have hQ : product n α x = x ^ n * Q := by
      calc
        product n α x =
            (indices n).prod (fun i => x * (1 + α i / x)) := by
              unfold product
              apply Finset.prod_congr rfl
              intro i hi
              field_simp [hx0]
        _ = (indices n).prod (fun _ => x) * Q := by
              rw [Finset.prod_mul_distrib]
        _ = x ^ n * Q := by simp [indices, Q]
    have hxnat (k : ℕ) : Real.rpow x (k : ℝ) = x ^ k := by
      exact Real.rpow_natCast _ _
    have hxpow (k : ℕ) :
        Real.rpow (x ^ n) ((k : ℝ) / (n : ℝ)) = x ^ k := by
      calc
        Real.rpow (x ^ n) ((k : ℝ) / (n : ℝ)) =
            Real.rpow (Real.rpow x (n : ℝ)) ((k : ℝ) / (n : ℝ)) := by
              exact congrArg
                (fun z : ℝ => Real.rpow z ((k : ℝ) / (n : ℝ)))
                (hxnat n).symm
        _ = Real.rpow x ((n : ℝ) * ((k : ℝ) / (n : ℝ))) :=
              (Real.rpow_mul hx.1.le (n : ℝ) ((k : ℝ) / (n : ℝ))).symm
        _ = Real.rpow x (k : ℝ) := by
              congr 1
              field_simp [hn0]
        _ = x ^ k := hxnat k
    have hrpow (j : ℕ) :
        Real.rpow (product n α x) ((n - j : ℕ) / (n : ℝ)) =
          x ^ (n - j) * Real.rpow Q ((n - j : ℕ) / (n : ℝ)) := by
      calc
        Real.rpow (product n α x) ((n - j : ℕ) / (n : ℝ)) =
            Real.rpow (x ^ n * Q) ((n - j : ℕ) / (n : ℝ)) := by
              exact congrArg
                (fun z : ℝ => Real.rpow z ((n - j : ℕ) / (n : ℝ))) hQ
        _ = Real.rpow (x ^ n) ((n - j : ℕ) / (n : ℝ)) *
              Real.rpow Q ((n - j : ℕ) / (n : ℝ)) :=
              Real.mul_rpow (pow_nonneg hx.1.le n) hQpos.le
        _ = x ^ (n - j) * Real.rpow Q ((n - j : ℕ) / (n : ℝ)) := by
              rw [hxpow]
    have hprod_rpow (j : ℕ) : ∀ s : Finset ℕ, s ⊆ indices n →
        Real.rpow (s.prod (fun i => 1 + α i / x))
            ((n - j : ℕ) / (n : ℝ)) =
          s.prod (fun i => Real.rpow (1 + α i / x)
            ((n - j : ℕ) / (n : ℝ))) := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro hs; simp
      | @insert i s hi ih =>
          intro hs
          have hii : i ∈ indices n := hs (Finset.mem_insert_self i s)
          have hss : s ⊆ indices n :=
            fun k hk => hs (Finset.mem_insert_of_mem hk)
          rw [Finset.prod_insert hi, Finset.prod_insert hi]
          calc
            Real.rpow ((1 + α i / x) * s.prod (fun k => 1 + α k / x))
                ((n - j : ℕ) / (n : ℝ)) =
                Real.rpow (1 + α i / x) ((n - j : ℕ) / (n : ℝ)) *
                  Real.rpow (s.prod (fun k => 1 + α k / x))
                    ((n - j : ℕ) / (n : ℝ)) :=
              Real.mul_rpow (hfac i hii).le
                (Finset.prod_nonneg fun k hk => (hfac k (hss hk)).le)
            _ = Real.rpow (1 + α i / x) ((n - j : ℕ) / (n : ℝ)) *
                  s.prod (fun k => Real.rpow (1 + α k / x)
                    ((n - j : ℕ) / (n : ℝ))) := by rw [ih hss]
    have hden : rootDenominator n α x = x ^ (n - 1) * D := by
      unfold rootDenominator
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
      rw [hrpow j, hprod_rpow j (indices n) (fun _ h => h)]
      have hpows : x ^ (n - j) * x ^ (j - 1) = x ^ (n - 1) := by
        rw [← pow_add]
        congr 1
        omega
      calc
        x ^ (n - j) *
              (indices n).prod (fun i =>
                Real.rpow (1 + α i / x) ((n - j : ℕ) / (n : ℝ))) *
              x ^ (j - 1) =
            (x ^ (n - j) * x ^ (j - 1)) *
              (indices n).prod (fun i =>
                Real.rpow (1 + α i / x) ((n - j : ℕ) / (n : ℝ))) := by ring
        _ = x ^ (n - 1) *
              (indices n).prod (fun i =>
                Real.rpow (1 + α i / x) ((n - j : ℕ) / (n : ℝ))) := by
              rw [hpows]
    have hone : 1 ∈ indices n := by
      simp only [indices, Finset.mem_Icc]
      constructor
      · exact le_rfl
      · omega
    have hDpos : 0 < D := by
      dsimp [D]
      apply Finset.sum_pos'
      · intro j hj
        exact (Finset.prod_pos fun i hi => Real.rpow_pos_of_pos (hfac i hi) _).le
      · refine ⟨1, hone, ?_⟩
        exact Finset.prod_pos fun i hi => Real.rpow_pos_of_pos (hfac i hi) _
    have hxsplit : x ^ n = x ^ (n - 1) * x := by
      calc
        x ^ n = x ^ ((n - 1) + 1) := by
          congr 1
          omega
        _ = x ^ (n - 1) * x := by rw [pow_succ]
    change (product n α x - x ^ n) / rootDenominator n α x =
      (x * (Q - 1)) / D
    rw [hQ, hden, hxsplit]
    field_simp [hx0, hDpos.ne']
    <;> ring
  apply Filter.Tendsto.congr' heq.symm
  have hden := normalized_denominator_limit n hn α
  exact (hscaled (indices n)).div hden hn0

theorem gap1 (n : ℕ) (hn : 0 < n) (α : ℕ → ℝ) (L : ℝ) :
    HasLimitAtPosInfinity (original n α) L ↔
      HasLimitAtPosInfinity (rationalized n α) L := by
  classical
  unfold HasLimitAtPosInfinity
  have heq : original n α =ᶠ[Filter.atTop] rationalized n α := by
    filter_upwards [eventually_positive_data n α] with x hx
    simp only [original, rationalized, nthRoot]
    let P : ℝ := product n α x
    let q : ℝ := Real.rpow P (1 / (n : ℝ))
    have hp : 0 < P := by
      dsimp [P]
      unfold product
      exact Finset.prod_pos fun i hi => hx.2 i hi
    have hq : 0 < q := Real.rpow_pos_of_pos hp _
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    have hpow (k : ℕ) :
        Real.rpow P ((k : ℝ) / (n : ℝ)) = q ^ k := by
      calc
        Real.rpow P ((k : ℝ) / (n : ℝ)) =
            Real.rpow P ((1 / (n : ℝ)) * (k : ℝ)) := by
              congr 1
              field_simp [hn0]
        _ = Real.rpow (Real.rpow P (1 / (n : ℝ))) (k : ℝ) :=
              Real.rpow_mul hp.le (1 / (n : ℝ)) (k : ℝ)
        _ = q ^ k := by
              dsimp [q]
              exact Real.rpow_natCast _ _
    have hqpow : q ^ n = P := by
      calc
        q ^ n = Real.rpow P ((n : ℝ) / (n : ℝ)) := (hpow n).symm
        _ = Real.rpow P 1 := by rw [div_self hn0]
        _ = P := by simp
    have hden : rootDenominator n α x =
        (indices n).sum (fun j => q ^ (n - j) * x ^ (j - 1)) := by
      unfold rootDenominator
      apply Finset.sum_congr rfl
      intro j hj
      rw [hpow]
    have hone : 1 ∈ indices n := by
      simp only [indices, Finset.mem_Icc]
      constructor
      · exact le_rfl
      · omega
    have hdenpos : 0 < rootDenominator n α x := by
      rw [hden]
      apply Finset.sum_pos'
      · intro j hj
        exact mul_nonneg (pow_nonneg hq.le _) (pow_nonneg hx.1.le _)
      · refine ⟨1, hone, ?_⟩
        exact mul_pos (pow_pos hq _) (pow_pos hx.1 _)
    change q - x = (P - x ^ n) / rootDenominator n α x
    apply (eq_div_iff hdenpos.ne').2
    rw [hden, ← hqpow]
    exact geom_sum_Icc n q x
  constructor
  · intro h
    exact Filter.Tendsto.congr' heq h
  · intro h
    exact Filter.Tendsto.congr' heq.symm h

/-- Source: `proof_gap/exercise_465/2`; expand the product numerator. -/
theorem gap2 (n : ℕ) (hn : 0 < n) (α : ℕ → ℝ) (L : ℝ) :
    HasLimitAtPosInfinity (rationalized n α) L ↔
      HasLimitAtPosInfinity (normalized n α) L := by
  classical
  have hrat := rationalized_limit n hn α
  have hnorm := normalized_limit n hn α
  constructor
  · intro h
    have hL : L = (indices n).sum α / n :=
      tendsto_nhds_unique h hrat
    simpa [hL] using hnorm
  · intro h
    have hL : L = (indices n).sum α / n :=
      tendsto_nhds_unique h hnorm
    simpa [hL] using hrat

/-- Source: `proof_gap/exercise_465/3`; replace the little-o term by an explicit vanishing term. -/
theorem gap3 (n : ℕ) (hn : 0 < n) (α : ℕ → ℝ) :
    HasLimitAtPosInfinity (normalized n α)
      ((indices n).sum α / n) := by
  exact normalized_limit n hn α

end

end ProofGap.Exercise465
