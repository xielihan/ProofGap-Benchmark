import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3660

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

def objective (m n p : ℝ) (q : Point3) : ℝ :=
  Real.rpow q.x m * Real.rpow q.y n * Real.rpow q.z p

def constraint (a : ℝ) : Set Point3 :=
  {q | q.x + q.y + q.z = a ∧ 0 < q.x ∧ 0 < q.y ∧ 0 < q.z}

def logObjective (m n p : ℝ) (q : Point3) : ℝ :=
  Real.log (objective m n p q)

def critical (a m n p : ℝ) (q : Point3) (lambda : ℝ) : Prop :=
  m / q.x - 1 / lambda = 0 ∧
    n / q.y - 1 / lambda = 0 ∧
    p / q.z - 1 / lambda = 0 ∧
    q.x + q.y + q.z = a

def candidate (a m n p : ℝ) : Point3 :=
  ⟨a * m / (m + n + p),
    a * n / (m + n + p),
    a * p / (m + n + p)⟩

def maximizers (a m n p : ℝ) : Set Point3 :=
  {q | q ∈ constraint a ∧
    ∀ r ∈ constraint a, objective m n p r ≤ objective m n p q}

def ApproachesBoundary (q : ℕ → Point3) (a : ℝ) : Prop :=
  (∀ k, q k ∈ constraint a) ∧
    Filter.Tendsto
      (fun k => min (q k).x (min (q k).y (q k).z))
      Filter.atTop (nhds 0)

private theorem logObjective_eq_sum {m n p : ℝ} {q : Point3}
    (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (hx : 0 < q.x) (hy : 0 < q.y) (hz : 0 < q.z) :
    logObjective m n p q =
      m * Real.log q.x + n * Real.log q.y + p * Real.log q.z := by
  have hxm : 0 < Real.rpow q.x m := Real.rpow_pos_of_pos hx m
  have hyn : 0 < Real.rpow q.y n := Real.rpow_pos_of_pos hy n
  have hzp : 0 < Real.rpow q.z p := Real.rpow_pos_of_pos hz p
  simp only [logObjective, objective]
  rw [Real.log_mul (mul_ne_zero hxm.ne' hyn.ne') hzp.ne',
      Real.log_mul hxm.ne' hyn.ne']
  change
    Real.log (q.x ^ m) + Real.log (q.y ^ n) + Real.log (q.z ^ p) =
      m * Real.log q.x + n * Real.log q.y + p * Real.log q.z
  rw [Real.log_rpow hx, Real.log_rpow hy, Real.log_rpow hz] <;> ring

private theorem candidate_mem_constraint {a m n p : ℝ}
    (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) (ha : 0 < a) :
    candidate a m n p ∈ constraint a := by
  have hs : 0 < m + n + p := by linarith
  change
    a * m / (m + n + p) + a * n / (m + n + p) +
          a * p / (m + n + p) = a ∧
      0 < a * m / (m + n + p) ∧
      0 < a * n / (m + n + p) ∧
      0 < a * p / (m + n + p)
  refine ⟨?_, div_pos (mul_pos ha hm) hs,
    div_pos (mul_pos ha hn) hs, div_pos (mul_pos ha hp) hs⟩
  field_simp [hs.ne'] <;> ring

private theorem critical_eq_candidate {a m n p : ℝ} {q : Point3} {lambda : ℝ}
    (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) (ha : 0 < a)
    (h : critical a m n p q lambda) : q = candidate a m n p := by
  rcases h with ⟨hx, hy, hz, hsum⟩
  have hl : lambda ≠ 0 := by
    intro hl
    subst lambda
    have hqx : q.x = 0 := by
      apply (div_eq_zero_iff.mp (by simpa using hx)).resolve_left hm.ne'
    have hqy : q.y = 0 := by
      apply (div_eq_zero_iff.mp (by simpa using hy)).resolve_left hn.ne'
    have hqz : q.z = 0 := by
      apply (div_eq_zero_iff.mp (by simpa using hz)).resolve_left hp.ne'
    rw [hqx, hqy, hqz] at hsum
    linarith
  have hqx : q.x ≠ 0 := by
    intro hqx
    rw [hqx] at hx
    have hone : 1 / lambda = 0 := by
      simpa using hx
    exact hl ((div_eq_zero_iff.mp hone).resolve_left one_ne_zero)
  have hqy : q.y ≠ 0 := by
    intro hqy
    rw [hqy] at hy
    have hone : 1 / lambda = 0 := by
      simpa using hy
    exact hl ((div_eq_zero_iff.mp hone).resolve_left one_ne_zero)
  have hqz : q.z ≠ 0 := by
    intro hqz
    rw [hqz] at hz
    have hone : 1 / lambda = 0 := by
      simpa using hz
    exact hl ((div_eq_zero_iff.mp hone).resolve_left one_ne_zero)
  have ex : q.x = m * lambda := by
    field_simp [hqx, hl] at hx
    nlinarith
  have ey : q.y = n * lambda := by
    field_simp [hqy, hl] at hy
    nlinarith
  have ez : q.z = p * lambda := by
    field_simp [hqz, hl] at hz
    nlinarith
  have hs : m + n + p ≠ 0 := by linarith
  have hel : lambda * (m + n + p) = a := by
    rw [← hsum, ex, ey, ez]
    ring
  have hlam : lambda = a / (m + n + p) := (eq_div_iff hs).2 hel
  rw [hlam] at ex ey ez
  rcases q with ⟨qx, qy, qz⟩
  simp only at ex ey ez
  simp only [candidate]
  rw [ex, ey, ez]
  all_goals ring

private theorem candidate_critical {a m n p : ℝ}
    (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) (ha : 0 < a) :
    critical a m n p (candidate a m n p) (a / (m + n + p)) := by
  have hs : 0 < m + n + p := by linarith
  have hxm : a * m / (m + n + p) ≠ 0 :=
    (div_pos (mul_pos ha hm) hs).ne'
  have hyn : a * n / (m + n + p) ≠ 0 :=
    (div_pos (mul_pos ha hn) hs).ne'
  have hzp : a * p / (m + n + p) ≠ 0 :=
    (div_pos (mul_pos ha hp) hs).ne'
  change
    m / (a * m / (m + n + p)) - 1 / (a / (m + n + p)) = 0 ∧
    n / (a * n / (m + n + p)) - 1 / (a / (m + n + p)) = 0 ∧
    p / (a * p / (m + n + p)) - 1 / (a / (m + n + p)) = 0 ∧
    a * m / (m + n + p) + a * n / (m + n + p) +
      a * p / (m + n + p) = a
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp [hxm, hs.ne', ha.ne', hm.ne'] <;> ring
  · field_simp [hyn, hs.ne', ha.ne', hn.ne'] <;> ring
  · field_simp [hzp, hs.ne', ha.ne', hp.ne'] <;> ring
  · field_simp [hs.ne'] <;> ring

private theorem objective_lt_candidate_of_mem_ne {a m n p : ℝ} {q : Point3}
    (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) (ha : 0 < a)
    (hq : q ∈ constraint a) (hne : q ≠ candidate a m n p) :
    objective m n p q < objective m n p (candidate a m n p) := by
  let c := candidate a m n p
  have hs : 0 < m + n + p := by linarith
  have hc := candidate_mem_constraint hm hn hp ha
  have hqx : 0 < q.x := hq.2.1
  have hqy : 0 < q.y := hq.2.2.1
  have hqz : 0 < q.z := hq.2.2.2
  have hcx : 0 < c.x := hc.2.1
  have hcy : 0 < c.y := hc.2.2.1
  have hcz : 0 < c.z := hc.2.2.2
  have hxlog : Real.log q.x - Real.log c.x ≤ q.x / c.x - 1 := by
    rw [← Real.log_div hqx.ne' hcx.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hqx hcx)
  have hylog : Real.log q.y - Real.log c.y ≤ q.y / c.y - 1 := by
    rw [← Real.log_div hqy.ne' hcy.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hqy hcy)
  have hzlog : Real.log q.z - Real.log c.z ≤ q.z / c.z - 1 := by
    rw [← Real.log_div hqz.ne' hcz.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hqz hcz)
  have hzero :
      m * (q.x / c.x - 1) + n * (q.y / c.y - 1) +
        p * (q.z / c.z - 1) = 0 := by
    have ex : m * (q.x / c.x - 1) = (m + n + p) * q.x / a - m := by
      dsimp [c, candidate]
      field_simp [hs.ne', ha.ne', hm.ne'] <;> ring
    have ey : n * (q.y / c.y - 1) = (m + n + p) * q.y / a - n := by
      dsimp [c, candidate]
      field_simp [hs.ne', ha.ne', hn.ne'] <;> ring
    have ez : p * (q.z / c.z - 1) = (m + n + p) * q.z / a - p := by
      dsimp [c, candidate]
      field_simp [hs.ne', ha.ne', hp.ne'] <;> ring
    rw [ex, ey, ez, ← hq.1]
    field_simp [ha.ne'] <;> ring
  have hcoords : q.x ≠ c.x ∨ q.y ≠ c.y ∨ q.z ≠ c.z := by
    by_cases hx : q.x = c.x
    · by_cases hy : q.y = c.y
      · right
        right
        intro hz
        apply hne
        cases q with
        | mk qx qy qz =>
          cases c with
          | mk cx cy cz =>
            simp only at hx hy hz ⊢
            rw [hx, hy, hz]
      · exact Or.inr (Or.inl hy)
    · exact Or.inl hx
  have hloglt : logObjective m n p q < logObjective m n p c := by
    rw [logObjective_eq_sum hm hn hp hqx hqy hqz,
      logObjective_eq_sum hm hn hp hcx hcy hcz]
    rcases hcoords with hxne | hyne | hzne
    · have hratio : q.x / c.x ≠ 1 := by
        intro h
        apply hxne
        exact (div_eq_one_iff_eq hcx.ne').mp h
      have hxstrict := Real.log_lt_sub_one_of_pos (div_pos hqx hcx) hratio
      rw [Real.log_div hqx.ne' hcx.ne'] at hxstrict
      have hmx := mul_lt_mul_of_pos_left hxstrict hm
      have hny := mul_le_mul_of_nonneg_left hylog hn.le
      have hpz := mul_le_mul_of_nonneg_left hzlog hp.le
      nlinarith
    · have hratio : q.y / c.y ≠ 1 := by
        intro h
        apply hyne
        exact (div_eq_one_iff_eq hcy.ne').mp h
      have hystrict := Real.log_lt_sub_one_of_pos (div_pos hqy hcy) hratio
      rw [Real.log_div hqy.ne' hcy.ne'] at hystrict
      have hmx := mul_le_mul_of_nonneg_left hxlog hm.le
      have hny := mul_lt_mul_of_pos_left hystrict hn
      have hpz := mul_le_mul_of_nonneg_left hzlog hp.le
      nlinarith
    · have hratio : q.z / c.z ≠ 1 := by
        intro h
        apply hzne
        exact (div_eq_one_iff_eq hcz.ne').mp h
      have hzstrict := Real.log_lt_sub_one_of_pos (div_pos hqz hcz) hratio
      rw [Real.log_div hqz.ne' hcz.ne'] at hzstrict
      have hmx := mul_le_mul_of_nonneg_left hxlog hm.le
      have hny := mul_le_mul_of_nonneg_left hylog hn.le
      have hpz := mul_lt_mul_of_pos_left hzstrict hp
      nlinarith
  have hobjq : 0 < objective m n p q := by
    exact mul_pos (mul_pos (Real.rpow_pos_of_pos hqx m)
      (Real.rpow_pos_of_pos hqy n)) (Real.rpow_pos_of_pos hqz p)
  have hobjc : 0 < objective m n p c := by
    exact mul_pos (mul_pos (Real.rpow_pos_of_pos hcx m)
      (Real.rpow_pos_of_pos hcy n)) (Real.rpow_pos_of_pos hcz p)
  by_contra hnot
  have hle : objective m n p c ≤ objective m n p q := le_of_not_gt hnot
  have hlogle : logObjective m n p c ≤ logObjective m n p q := by
    unfold logObjective
    exact Real.strictMonoOn_log.monotoneOn hobjc hobjq hle
  linarith

private theorem logObjective_le_min_bound {a m n p : ℝ} {q : Point3}
    (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) (ha : 0 < a)
    (hq : q ∈ constraint a)
    (hd : Real.log (min q.x (min q.y q.z)) ≤ 0) :
    logObjective m n p q ≤
      min m (min n p) * Real.log (min q.x (min q.y q.z)) +
        (m + n + p) * max (Real.log a) 0 := by
  have hx : 0 < q.x := hq.2.1
  have hy : 0 < q.y := hq.2.2.1
  have hz : 0 < q.z := hq.2.2.2
  have hxa : q.x ≤ a := by nlinarith [hq.1]
  have hya : q.y ≤ a := by nlinarith [hq.1]
  have hza : q.z ≤ a := by nlinarith [hq.1]
  have hlx : Real.log q.x ≤ max (Real.log a) 0 :=
    le_trans (Real.strictMonoOn_log.monotoneOn hx ha hxa)
      (le_max_left _ _)
  have hly : Real.log q.y ≤ max (Real.log a) 0 :=
    le_trans (Real.strictMonoOn_log.monotoneOn hy ha hya)
      (le_max_left _ _)
  have hlz : Real.log q.z ≤ max (Real.log a) 0 :=
    le_trans (Real.strictMonoOn_log.monotoneOn hz ha hza)
      (le_max_left _ _)
  have hmx := mul_le_mul_of_nonneg_left hlx hm.le
  have hny := mul_le_mul_of_nonneg_left hly hn.le
  have hpz := mul_le_mul_of_nonneg_left hlz hp.le
  rw [logObjective_eq_sum hm hn hp hx hy hz]
  by_cases hxmin : q.x ≤ min q.y q.z
  · rw [min_eq_left hxmin] at hd ⊢
    have hw : min m (min n p) ≤ m := min_le_left _ _
    have hcoeff : m * Real.log q.x ≤ min m (min n p) * Real.log q.x := by
      nlinarith
    nlinarith [le_max_right (Real.log a) 0]
  · have hrest : min q.y q.z ≤ q.x := le_of_not_ge hxmin
    rw [min_eq_right hrest] at hd ⊢
    by_cases hyz : q.y ≤ q.z
    · rw [min_eq_left hyz] at hd ⊢
      have hw : min m (min n p) ≤ n :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      have hcoeff : n * Real.log q.y ≤ min m (min n p) * Real.log q.y := by
        nlinarith
      nlinarith [le_max_right (Real.log a) 0]
    · have hzy : q.z ≤ q.y := le_of_not_ge hyz
      rw [min_eq_right hzy] at hd ⊢
      have hw : min m (min n p) ≤ p :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      have hcoeff : p * Real.log q.z ≤ min m (min n p) * Real.log q.z := by
        nlinarith
      nlinarith [le_max_right (Real.log a) 0]

theorem gap1 (a m n p : ℝ) (hm : 0 < m) (hn : 0 < n)
    (hp : 0 < p) (ha : 0 < a) :
    ∀ q ∈ constraint a,
      logObjective m n p q =
        m * Real.log q.x + n * Real.log q.y + p * Real.log q.z := by
  intro q hq
  exact logObjective_eq_sum hm hn hp hq.2.1 hq.2.2.1 hq.2.2.2

theorem gap2 (a m n p : ℝ) (hm : 0 < m) (hn : 0 < n)
    (hp : 0 < p) (ha : 0 < a) :
    ∀ q lambda, critical a m n p q lambda →
      q.x = (candidate a m n p).x := by
  intro q lambda h
  exact congrArg Point3.x (critical_eq_candidate hm hn hp ha h)

theorem gap3 (a m n p : ℝ) (hm : 0 < m) (hn : 0 < n)
    (hp : 0 < p) (ha : 0 < a) :
    ∀ q lambda, critical a m n p q lambda →
      q.y = (candidate a m n p).y := by
  intro q lambda h
  exact congrArg Point3.y (critical_eq_candidate hm hn hp ha h)

theorem gap4 (a m n p : ℝ) (hm : 0 < m) (hn : 0 < n)
    (hp : 0 < p) (ha : 0 < a) :
    ∀ q lambda, critical a m n p q lambda →
      q.z = (candidate a m n p).z := by
  intro q lambda h
  exact congrArg Point3.z (critical_eq_candidate hm hn hp ha h)

theorem gap5 (a m n p : ℝ) (hm : 0 < m) (hn : 0 < n)
    (hp : 0 < p) (ha : 0 < a) :
    {q | ∃ lambda, critical a m n p q lambda} =
      ({candidate a m n p} : Set Point3) := by
  ext q
  change (∃ lambda, critical a m n p q lambda) ↔ q = candidate a m n p
  constructor
  · rintro ⟨lambda, h⟩
    exact critical_eq_candidate hm hn hp ha h
  · intro h
    subst q
    exact ⟨a / (m + n + p), candidate_critical hm hn hp ha⟩

theorem gap6 (a m n p : ℝ) (hm : 0 < m) (hn : 0 < n)
    (hp : 0 < p) (ha : 0 < a) :
    ∀ q : ℕ → Point3, ApproachesBoundary q a →
      Filter.Tendsto (fun k => logObjective m n p (q k))
        Filter.atTop Filter.atBot := by
  intro q hq
  let d : ℕ → ℝ := fun k => min (q k).x (min (q k).y (q k).z)
  have hdpos : ∀ k, 0 < d k := by
    intro k
    have hk := (hq.1 k).2
    exact lt_min hk.1 (lt_min hk.2.1 hk.2.2)
  have hdlim : Filter.Tendsto d Filter.atTop (nhds 0) := hq.2
  have hdwithin :
      Filter.Tendsto d Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.2
      ⟨hdlim, Filter.Eventually.of_forall (fun k => hdpos k)⟩
  have hlog :
      Filter.Tendsto (fun k => Real.log (d k)) Filter.atTop Filter.atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hdwithin
  let w := min m (min n p)
  let L := max (Real.log a) 0
  have hw : 0 < w := by
    dsimp [w]
    exact lt_min hm (lt_min hn hp)
  refine Filter.tendsto_atBot.2 ?_
  intro b
  have hevent := Filter.tendsto_atBot.1 hlog ((b - (m + n + p) * L) / w)
  have hzero := Filter.tendsto_atBot.1 hlog 0
  filter_upwards [hevent, hzero] with k hk hk0
  have hbound := logObjective_le_min_bound hm hn hp ha (hq.1 k) hk0
  have hbound' :
      logObjective m n p (q k) ≤
        w * Real.log (d k) + (m + n + p) * L := by
    simpa [w, L, d] using hbound
  have hscaled :
      w * Real.log (d k) ≤ b - (m + n + p) * L := by
    have hk' := (le_div_iff₀ hw).1 hk
    simpa [mul_comm] using hk'
  linarith

theorem gap7 (a m n p : ℝ) (hm : 0 < m) (hn : 0 < n)
    (hp : 0 < p) (ha : 0 < a) :
    maximizers a m n p =
      ({candidate a m n p} : Set Point3) := by
  ext q
  change
    (q ∈ constraint a ∧
      ∀ r ∈ constraint a, objective m n p r ≤ objective m n p q) ↔
      q = candidate a m n p
  constructor
  · rintro ⟨hq, hmax⟩
    by_contra hne
    have hlt := objective_lt_candidate_of_mem_ne hm hn hp ha hq hne
    have hge := hmax (candidate a m n p) (candidate_mem_constraint hm hn hp ha)
    linarith
  · intro hq
    subst q
    refine ⟨candidate_mem_constraint hm hn hp ha, ?_⟩
    intro r hr
    by_cases hre : r = candidate a m n p
    · simpa [hre]
    · exact le_of_lt (objective_lt_candidate_of_mem_ne hm hn hp ha hr hre)

theorem gap8 (a m n p : ℝ) (hm : 0 < m) (hn : 0 < n)
    (hp : 0 < p) (ha : 0 < a) :
    objective m n p (candidate a m n p) =
      (Real.rpow a (m + n + p) *
          Real.rpow m m * Real.rpow n n * Real.rpow p p) /
        Real.rpow (m + n + p) (m + n + p) := by
  have hs : 0 < m + n + p := by linarith
  have ha_mn : a ^ (m + n) = a ^ m * a ^ n := by
    exact Real.rpow_add ha m n
  have ha_mnp : a ^ ((m + n) + p) = a ^ (m + n) * a ^ p := by
    exact Real.rpow_add ha (m + n) p
  have haPow :
      a ^ m * a ^ n * a ^ p = a ^ (m + n + p) := by
    calc
      a ^ m * a ^ n * a ^ p = a ^ (m + n) * a ^ p :=
        congrArg (fun t : ℝ => t * a ^ p) ha_mn.symm
      _ = a ^ ((m + n) + p) := ha_mnp.symm
  have hs_mn :
      (m + n + p) ^ (m + n) =
        (m + n + p) ^ m * (m + n + p) ^ n := by
    exact Real.rpow_add hs m n
  have hs_mnp :
      (m + n + p) ^ ((m + n) + p) =
        (m + n + p) ^ (m + n) * (m + n + p) ^ p := by
    exact Real.rpow_add hs (m + n) p
  have hsPow :
      (m + n + p) ^ m * (m + n + p) ^ n * (m + n + p) ^ p =
        (m + n + p) ^ (m + n + p) := by
    calc
      (m + n + p) ^ m * (m + n + p) ^ n * (m + n + p) ^ p =
          (m + n + p) ^ (m + n) * (m + n + p) ^ p :=
        congrArg (fun t : ℝ => t * (m + n + p) ^ p) hs_mn.symm
      _ = (m + n + p) ^ ((m + n) + p) := hs_mnp.symm
  have hsm : 0 < (m + n + p) ^ m := Real.rpow_pos_of_pos hs m
  have hsn : 0 < (m + n + p) ^ n := Real.rpow_pos_of_pos hs n
  have hsp : 0 < (m + n + p) ^ p := Real.rpow_pos_of_pos hs p
  dsimp [objective, candidate]
  change
    ((a * m / (m + n + p)) ^ m *
        (a * n / (m + n + p)) ^ n) *
        (a * p / (m + n + p)) ^ p =
      (a ^ (m + n + p) * m ^ m * n ^ n * p ^ p) /
        (m + n + p) ^ (m + n + p)
  rw [Real.div_rpow (mul_nonneg ha.le hm.le) hs.le,
      Real.div_rpow (mul_nonneg ha.le hn.le) hs.le,
      Real.div_rpow (mul_nonneg ha.le hp.le) hs.le,
      Real.mul_rpow ha.le hm.le,
      Real.mul_rpow ha.le hn.le,
      Real.mul_rpow ha.le hp.le,
      ← haPow, ← hsPow]
  field_simp [hsm.ne', hsn.ne', hsp.ne'] <;> ring

end

end ProofGap.Exercise3660
