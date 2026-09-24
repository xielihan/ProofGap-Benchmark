import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4344

noncomputable section

open scoped Interval Topology

abbrev Point3 := ℝ × (ℝ × ℝ)

def coneSolid : Set Point3 :=
  {p |
    Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2) ≤ p.2.2 ∧
      p.2.2 ≤ 1}

def coneSide : Set Point3 :=
  {p |
    p.2.2 = Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2) ∧
      p.1 ^ 2 + p.2.1 ^ 2 ≤ 1}

def topDisk : Set Point3 :=
  {p | p.2.2 = 1 ∧ p.1 ^ 2 + p.2.1 ^ 2 ≤ 1}

def coneHeight (x y : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + y ^ 2)

def coneAreaFactor (x y : ℝ) : ℝ :=
  Real.sqrt
    (1 + (deriv (fun s => coneHeight s y) x) ^ 2 +
      (deriv (fun s => coneHeight x s) y) ^ 2)

def topAreaFactor (_x _y : ℝ) : ℝ := 1

def polarRadialMoment : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ∫ r in (0 : ℝ)..1, r ^ 3

def coneMoment : ℝ := Real.sqrt 2 * polarRadialMoment

def topMoment : ℝ := polarRadialMoment

def boundaryMoment : ℝ := coneMoment + topMoment

private theorem interior_coneSolid :
    interior coneSolid =
      {p : Point3 |
        Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2) < p.2.2 ∧ p.2.2 < 1} := by
  have hx : Continuous (fun p : Point3 => p.1) := continuous_fst
  have hy : Continuous (fun p : Point3 => p.2.1) :=
    continuous_fst.comp continuous_snd
  have hz : Continuous (fun p : Point3 => p.2.2) :=
    continuous_snd.comp continuous_snd
  have hrad :
      Continuous (fun p : Point3 =>
        Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2)) :=
    Real.continuous_sqrt.comp ((hx.pow 2).add (hy.pow 2))
  ext p
  constructor
  · intro hp
    have hps : p ∈ coneSolid := interior_subset hp
    change
      Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2) ≤ p.2.2 ∧ p.2.2 ≤ 1 at hps
    let g : ℝ → Point3 := fun t => (p.1, (p.2.1, t))
    have hg : Continuous g :=
      continuous_const.prodMk (continuous_const.prodMk continuous_id)
    have hopen : IsOpen (g ⁻¹' interior coneSolid) :=
      isOpen_interior.preimage hg
    have hzmem : p.2.2 ∈ g ⁻¹' interior coneSolid := by
      change g p.2.2 ∈ interior coneSolid
      simpa [g] using hp
    rcases Metric.isOpen_iff.1 hopen p.2.2 hzmem with
      ⟨ε, hε, hball⟩
    have hdownball : p.2.2 - ε / 2 ∈ Metric.ball p.2.2 ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have he : 0 < ε / 2 := by linarith
      rw [show p.2.2 - ε / 2 - p.2.2 = -(ε / 2) by ring,
        abs_neg, abs_of_pos he]
      linarith
    have hupball : p.2.2 + ε / 2 ∈ Metric.ball p.2.2 ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have he : 0 < ε / 2 := by linarith
      rw [show p.2.2 + ε / 2 - p.2.2 = ε / 2 by ring,
        abs_of_pos he]
      linarith
    have hdown : g (p.2.2 - ε / 2) ∈ coneSolid :=
      interior_subset (hball hdownball)
    have hup : g (p.2.2 + ε / 2) ∈ coneSolid :=
      interior_subset (hball hupball)
    change
      Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2) ≤ p.2.2 - ε / 2 ∧
        p.2.2 - ε / 2 ≤ 1 at hdown
    change
      Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2) ≤ p.2.2 + ε / 2 ∧
        p.2.2 + ε / 2 ≤ 1 at hup
    have hfirst_ne :
        Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2) ≠ p.2.2 := by
      intro heq
      nlinarith [hdown.1]
    have hsecond_ne : p.2.2 ≠ 1 := by
      intro heq
      nlinarith [hup.2]
    exact
      ⟨lt_of_le_of_ne hps.1 hfirst_ne,
        lt_of_le_of_ne hps.2 hsecond_ne⟩
  · intro hp
    have hopen : IsOpen
        {p : Point3 |
          Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2) < p.2.2 ∧ p.2.2 < 1} :=
      (isOpen_lt hrad hz).inter (isOpen_lt hz continuous_const)
    apply (interior_maximal _ hopen) hp
    intro q hq
    change
      Real.sqrt (q.1 ^ 2 + q.2.1 ^ 2) < q.2.2 ∧ q.2.2 < 1 at hq
    change
      Real.sqrt (q.1 ^ 2 + q.2.1 ^ 2) ≤ q.2.2 ∧ q.2.2 ≤ 1
    exact ⟨le_of_lt hq.1, le_of_lt hq.2⟩

theorem gap1 :
    frontier coneSolid = coneSide ∪ topDisk := by
  have hx : Continuous (fun p : Point3 => p.1) := continuous_fst
  have hy : Continuous (fun p : Point3 => p.2.1) :=
    continuous_fst.comp continuous_snd
  have hz : Continuous (fun p : Point3 => p.2.2) :=
    continuous_snd.comp continuous_snd
  have hrad :
      Continuous (fun p : Point3 =>
        Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2)) :=
    Real.continuous_sqrt.comp ((hx.pow 2).add (hy.pow 2))
  have hclosed : IsClosed coneSolid := by
    have hcone : IsClosed {p : Point3 |
        Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2) ≤ p.2.2} :=
      isClosed_le hrad hz
    have htop : IsClosed {p : Point3 | p.2.2 ≤ (1 : ℝ)} :=
      isClosed_le hz continuous_const
    change IsClosed
      ({p : Point3 | Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2) ≤ p.2.2} ∩
        {p : Point3 | p.2.2 ≤ (1 : ℝ)})
    exact hcone.inter htop
  change closure coneSolid \ interior coneSolid = coneSide ∪ topDisk
  rw [hclosed.closure_eq, interior_coneSolid]
  ext p
  change
    ((Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2) ≤ p.2.2 ∧ p.2.2 ≤ 1) ∧
        ¬(Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2) < p.2.2 ∧ p.2.2 < 1)) ↔
      ((p.2.2 = Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2) ∧
          p.1 ^ 2 + p.2.1 ^ 2 ≤ 1) ∨
        (p.2.2 = 1 ∧ p.1 ^ 2 + p.2.1 ^ 2 ≤ 1))
  let q : ℝ := p.1 ^ 2 + p.2.1 ^ 2
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hs0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hsq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq0
  constructor
  · rintro ⟨hsolid, hnot⟩
    change Real.sqrt q ≤ p.2.2 ∧ p.2.2 ≤ 1 at hsolid
    change ¬(Real.sqrt q < p.2.2 ∧ p.2.2 < 1) at hnot
    have hqle : q ≤ 1 := by nlinarith
    by_cases heq : Real.sqrt q = p.2.2
    · left
      exact ⟨heq.symm, hqle⟩
    · right
      have hlt : Real.sqrt q < p.2.2 := lt_of_le_of_ne hsolid.1 heq
      have hz1 : p.2.2 = 1 := by
        by_contra hne
        exact hnot ⟨hlt, lt_of_le_of_ne hsolid.2 hne⟩
      exact ⟨hz1, hqle⟩
  · intro h
    rcases h with hside | htop
    · change p.2.2 = Real.sqrt q ∧ q ≤ 1 at hside
      have hsle : Real.sqrt q ≤ 1 := by
        nlinarith [hsq, hs0, hside.2]
      rcases hside with ⟨hz, hqle⟩
      constructor
      · constructor
        · rw [hz]
        · rw [hz]
          exact hsle
      · rintro ⟨hstrict, _⟩
        rw [hz] at hstrict
        exact lt_irrefl _ hstrict
    · change p.2.2 = 1 ∧ q ≤ 1 at htop
      have hsle : Real.sqrt q ≤ 1 := by
        nlinarith [hsq, hs0, htop.2]
      rcases htop with ⟨hz, hqle⟩
      constructor
      · constructor
        · rw [hz]
          exact hsle
        · rw [hz]
      · rintro ⟨_, hstrict⟩
        rw [hz] at hstrict
        exact lt_irrefl _ hstrict

theorem gap2
    (x y : ℝ) (hne : (x, y) ≠ (0, 0)) :
    coneAreaFactor x y = Real.sqrt 2 := by
  let q : ℝ := x ^ 2 + y ^ 2
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqne : q ≠ 0 := by
    intro hq
    have hx0 : x = 0 := by
      dsimp [q] at hq
      nlinarith [sq_nonneg x, sq_nonneg y]
    have hy0 : y = 0 := by
      dsimp [q] at hq
      nlinarith [sq_nonneg x, sq_nonneg y]
    apply hne
    simp [hx0, hy0]
  have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqne)
  have hspos : 0 < Real.sqrt q := Real.sqrt_pos.2 hqpos
  have hsne : Real.sqrt q ≠ 0 := ne_of_gt hspos
  have hxinner :
      HasDerivAt (fun s : ℝ => s ^ 2 + y ^ 2) (2 * x) x := by
    simpa [mul_comm] using
      (((hasDerivAt_id x).pow 2).add_const (y ^ 2))
  have hyinner :
      HasDerivAt (fun s : ℝ => x ^ 2 + s ^ 2) (2 * y) y := by
    simpa [mul_comm] using
      (((hasDerivAt_id y).pow 2).const_add (x ^ 2))
  have hxcomp := (Real.hasDerivAt_sqrt hqne).comp x hxinner
  have hycomp := (Real.hasDerivAt_sqrt hqne).comp y hyinner
  have hxcomp' :
      HasDerivAt (fun s : ℝ => Real.sqrt (s ^ 2 + y ^ 2))
        (1 / (2 * Real.sqrt q) * (2 * x)) x := by
    simpa only [Function.comp_apply] using hxcomp
  have hycomp' :
      HasDerivAt (fun s : ℝ => Real.sqrt (x ^ 2 + s ^ 2))
        (1 / (2 * Real.sqrt q) * (2 * y)) y := by
    simpa only [Function.comp_apply] using hycomp
  have hxder :
      deriv (fun s : ℝ => Real.sqrt (s ^ 2 + y ^ 2)) x =
        x / Real.sqrt q := by
    calc
      deriv (fun s : ℝ => Real.sqrt (s ^ 2 + y ^ 2)) x =
          1 / (2 * Real.sqrt q) * (2 * x) := hxcomp'.deriv
      _ = x / Real.sqrt q := by
        field_simp [hsne]
  have hyder :
      deriv (fun s : ℝ => Real.sqrt (x ^ 2 + s ^ 2)) y =
        y / Real.sqrt q := by
    calc
      deriv (fun s : ℝ => Real.sqrt (x ^ 2 + s ^ 2)) y =
          1 / (2 * Real.sqrt q) * (2 * y) := hycomp'.deriv
      _ = y / Real.sqrt q := by
        field_simp [hsne]
  have hsq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq0
  have hinside :
      1 + (x / Real.sqrt q) ^ 2 + (y / Real.sqrt q) ^ 2 = 2 := by
    rw [div_pow, div_pow, hsq]
    change 1 + x ^ 2 / q + y ^ 2 / q = 2
    field_simp [hqne] <;> dsimp [q] <;> ring
  unfold coneAreaFactor coneHeight
  rw [hxder, hyder, hinside]

theorem gap3 (x y : ℝ) :
    topAreaFactor x y = 1 := by
  rfl

theorem gap4 :
    boundaryMoment = coneMoment + topMoment := by
  rfl

theorem gap5 :
    boundaryMoment =
      Real.sqrt 2 *
          (∫ φ in (0 : ℝ)..2 * Real.pi,
            ∫ r in (0 : ℝ)..1, r ^ 3) +
        (∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..1, r ^ 3) := by
  rfl

theorem gap6 :
    Real.sqrt 2 *
          (∫ φ in (0 : ℝ)..2 * Real.pi,
            ∫ r in (0 : ℝ)..1, r ^ 3) +
        (∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..1, r ^ 3) =
      Real.pi / 2 * (1 + Real.sqrt 2) := by
  have hr : (∫ r in (0 : ℝ)..1, r ^ 3) = (1 / 4 : ℝ) := by
    have hfour :
        (∫ r in (0 : ℝ)..1, (4 : ℝ) * r ^ 3) = 1 := by
      let f : ℝ → ℝ := fun r => r ^ 4
      have hfund :
          (∫ r in (0 : ℝ)..1, (4 : ℝ) * r ^ 3) = f 1 - f 0 := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro r _
          simpa [f] using ((hasDerivAt_id r).pow 4)
        · exact
            (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable 0 1
      simpa [f] using hfund
    rw [intervalIntegral.integral_const_mul] at hfour
    norm_num at hfour ⊢
    linarith
  have hp :
      (∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1, r ^ 3) = Real.pi / 2 := by
    rw [hr]
    rw [intervalIntegral.integral_const]
    simp
    ring
  rw [hp]
  ring

theorem gap7 :
    boundaryMoment = Real.pi / 2 * (1 + Real.sqrt 2) := by
  exact gap5.trans gap6

end

end ProofGap.Exercise4344
