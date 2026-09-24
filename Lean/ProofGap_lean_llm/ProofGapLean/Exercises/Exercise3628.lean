import Mathlib.Analysis.Calculus.Deriv.Basic
import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3628

noncomputable section

def z (p : ℝ × ℝ) : ℝ :=
  p.1 * p.2 + 50 / p.1 + 20 / p.2

def partialX (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => g (x, p.2)) p.1

def partialY (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => g (p.1, y)) p.2

def partialXX (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => partialX g (x, p.2)) p.1

def partialXY (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => partialX g (p.1, y)) p.2

def partialYY (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => partialY g (p.1, y)) p.2

def positiveQuadrant : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2}

def basePoint : ℝ × ℝ :=
  (5, 2)

def hessianA : ℝ :=
  partialXX z basePoint

def hessianB : ℝ :=
  partialXY z basePoint

def hessianC : ℝ :=
  partialYY z basePoint

def hessianDiscriminant : ℝ :=
  hessianA * hessianC - hessianB ^ 2

def IsUniqueGlobalMinimizerOn
    (g : ℝ × ℝ → ℝ) (s : Set (ℝ × ℝ)) (p : ℝ × ℝ) : Prop :=
  p ∈ s ∧ (∀ q ∈ s, g p ≤ g q) ∧
    (∀ q ∈ s, g q = g p → q = p)

private theorem hasDerivAt_const_div_id (c x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => c / t) (-c / x ^ 2) x := by
  convert (hasDerivAt_const x c).div (hasDerivAt_id x) hx using 1 <;>
    simp [id] <;> ring

private theorem partialX_z_of_ne (p : ℝ × ℝ) (hp : p.1 ≠ 0) :
    partialX z p = p.2 - 50 / p.1 ^ 2 := by
  change deriv (fun x : ℝ => x * p.2 + 50 / x + 20 / p.2) p.1 =
    p.2 - 50 / p.1 ^ 2
  have hlin : HasDerivAt (fun x : ℝ => x * p.2) p.2 p.1 := by
    convert (hasDerivAt_id p.1).mul (hasDerivAt_const p.1 p.2) using 1 <;> ring
  have hquot := hasDerivAt_const_div_id (50 : ℝ) p.1 hp
  have hconst : HasDerivAt (fun _ : ℝ => 20 / p.2) 0 p.1 :=
    hasDerivAt_const p.1 (20 / p.2)
  have h :
      HasDerivAt (fun x : ℝ => x * p.2 + 50 / x + 20 / p.2)
        (p.2 - 50 / p.1 ^ 2) p.1 := by
    convert (hlin.add hquot).add hconst using 1 <;> ring
  exact h.deriv

private theorem partialY_z_of_ne (p : ℝ × ℝ) (hp : p.2 ≠ 0) :
    partialY z p = p.1 - 20 / p.2 ^ 2 := by
  change deriv (fun y : ℝ => p.1 * y + 50 / p.1 + 20 / y) p.2 =
    p.1 - 20 / p.2 ^ 2
  have hlin : HasDerivAt (fun y : ℝ => p.1 * y) p.1 p.2 := by
    convert (hasDerivAt_const p.2 p.1).mul (hasDerivAt_id p.2) using 1 <;> ring
  have hconst : HasDerivAt (fun _ : ℝ => 50 / p.1) 0 p.2 :=
    hasDerivAt_const p.2 (50 / p.1)
  have hquot := hasDerivAt_const_div_id (20 : ℝ) p.2 hp
  have h :
      HasDerivAt (fun y : ℝ => p.1 * y + 50 / p.1 + 20 / y)
        (p.1 - 20 / p.2 ^ 2) p.2 := by
    convert (hlin.add hconst).add hquot using 1 <;> ring
  exact h.deriv

private theorem z_bound_and_rigidity (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    30 ≤ z (x, y) ∧ (z (x, y) = 30 → x = 5 ∧ y = 2) := by
  let t : ℝ := Real.sqrt (y / 2)
  have hyhalf : 0 ≤ y / 2 := by positivity
  have ht : 0 < t := by
    dsimp [t]
    exact Real.sqrt_pos.2 (by positivity)
  have htsq : t ^ 2 = y / 2 := by
    dsimp [t]
    exact Real.sq_sqrt hyhalf
  have hyeq : y = 2 * t ^ 2 := by
    linarith
  have hid1 :
      x * (x * y / 10 + 5 / x - 2 * t) = (x * t - 5) ^ 2 / 5 := by
    rw [hyeq]
    field_simp [ne_of_gt hx]
    <;> ring
  have hfirst : 0 ≤ x * y / 10 + 5 / x - 2 * t := by
    have hmul :
        0 ≤ x * (x * y / 10 + 5 / x - 2 * t) := by
      rw [hid1]
      positivity
    by_contra hneg
    have hprodneg := mul_neg_of_pos_of_neg hx (lt_of_not_ge hneg)
    exact (not_lt_of_ge hmul) hprodneg
  have hid2 :
      t ^ 2 * (2 * t + 2 / y - 3) =
        (t - 1) ^ 2 * (2 * t + 1) := by
    rw [hyeq]
    field_simp [ne_of_gt ht]
    <;> ring
  have hsecond : 0 ≤ 2 * t + 2 / y - 3 := by
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
    have hmul : 0 ≤ t ^ 2 * (2 * t + 2 / y - 3) := by
      rw [hid2]
      positivity
    by_contra hneg
    have hprodneg := mul_neg_of_pos_of_neg ht2 (lt_of_not_ge hneg)
    exact (not_lt_of_ge hmul) hprodneg
  have hzscale :
      z (x, y) = 10 * (x * y / 10 + 5 / x + 2 / y) := by
    simp [z]
    ring
  have hnorm : 3 ≤ x * y / 10 + 5 / x + 2 / y := by
    nlinarith [hfirst, hsecond]
  constructor
  · rw [hzscale]
    nlinarith
  · intro hz30
    have hnormeq : x * y / 10 + 5 / x + 2 / y = 3 := by
      rw [hzscale] at hz30
      nlinarith
    have hd1 : x * y / 10 + 5 / x - 2 * t = 0 := by
      nlinarith [hfirst, hsecond]
    have hd2 : 2 * t + 2 / y - 3 = 0 := by
      nlinarith [hfirst, hsecond]
    have hprod2 : (t - 1) ^ 2 * (2 * t + 1) = 0 := by
      calc
        (t - 1) ^ 2 * (2 * t + 1) =
            t ^ 2 * (2 * t + 2 / y - 3) := hid2.symm
        _ = 0 := by rw [hd2, mul_zero]
    have hsqt : (t - 1) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hprod2 with h | h
      · exact h
      · exfalso
        exact (ne_of_gt (by nlinarith : 0 < 2 * t + 1)) h
    have htone : t = 1 := by
      nlinarith [sq_nonneg (t - 1)]
    have hyfinal : y = 2 := by
      rw [hyeq, htone]
      norm_num
    have hsquareDiv : (x * t - 5) ^ 2 / 5 = 0 := by
      calc
        (x * t - 5) ^ 2 / 5 =
            x * (x * y / 10 + 5 / x - 2 * t) := hid1.symm
        _ = 0 := by rw [hd1, mul_zero]
    have hsquare : (x * t - 5) ^ 2 = 0 := by
      nlinarith
    have hxt : x * t = 5 := by
      nlinarith [sq_nonneg (x * t - 5)]
    have hxfinal : x = 5 := by
      rw [htone] at hxt
      simpa using hxt
    exact ⟨hxfinal, hyfinal⟩

theorem gap1 :
    ∀ p : ℝ × ℝ, p ∈ ({basePoint} : Set (ℝ × ℝ)) →
      p ∈ positiveQuadrant ∧
      partialX z p = p.2 - 50 / p.1 ^ 2 ∧
      p.2 - 50 / p.1 ^ 2 = 0 ∧
      partialY z p = p.1 - 20 / p.2 ^ 2 ∧
      p.1 - 20 / p.2 ^ 2 = 0 := by
  intro p hp
  have hp' : p = basePoint := by
    simpa only [Set.mem_singleton_iff] using hp
  subst p
  have hx := partialX_z_of_ne basePoint (by norm_num [basePoint])
  have hy := partialY_z_of_ne basePoint (by norm_num [basePoint])
  refine ⟨by norm_num [positiveQuadrant, basePoint], hx, ?_, hy, ?_⟩
  · norm_num [basePoint]
  · norm_num [basePoint]

theorem gap2 :
    basePoint = (5, 2) := by
  rfl

theorem gap3 :
    hessianA = (4 / 5 : ℝ) := by
  change deriv (fun x : ℝ => partialX z (x, 2)) 5 = (4 / 5 : ℝ)
  have hpow : HasDerivAt (fun x : ℝ => x ^ 2) 10 5 := by
    have hfun :
        (id * id : ℝ → ℝ) = (fun x : ℝ => x ^ 2) := by
      funext x
      simp [pow_two]
    rw [← hfun]
    convert
      ((hasDerivAt_id (5 : ℝ)).mul (hasDerivAt_id (5 : ℝ))) using 1 <;>
      norm_num [id]
  have hquot :
      HasDerivAt (fun x : ℝ => 50 / x ^ 2) (-4 / 5 : ℝ) 5 := by
    convert (hasDerivAt_const (5 : ℝ) (50 : ℝ)).div hpow (by norm_num) using 1 <;>
      norm_num
  have hExplicit :
      HasDerivAt (fun x : ℝ => 2 - 50 / x ^ 2) (4 / 5 : ℝ) 5 := by
    convert (hasDerivAt_const (5 : ℝ) (2 : ℝ)).sub hquot using 1 <;>
      norm_num
  have hne : ∀ᶠ x : ℝ in nhds 5, x ≠ 0 :=
    eventually_ne_nhds (by norm_num)
  have heq :
      (fun x : ℝ => partialX z (x, 2)) =ᶠ[nhds 5]
        (fun x : ℝ => 2 - 50 / x ^ 2) := by
    exact hne.mono (fun x hx => by
      simpa using partialX_z_of_ne (x, 2) hx)
  exact (hExplicit.congr_of_eventuallyEq heq).deriv

theorem gap4 :
    hessianB = 1 := by
  change deriv (fun y : ℝ => partialX z (5, y)) 2 = 1
  have heq :
      (fun y : ℝ => partialX z (5, y)) = (fun y : ℝ => y - 2) := by
    funext y
    calc
      partialX z (5, y) = y - 50 / (5 : ℝ) ^ 2 :=
        partialX_z_of_ne (5, y) (by norm_num)
      _ = y - 2 := by norm_num
  rw [heq]
  simpa using ((hasDerivAt_id 2).sub_const 2).deriv

theorem gap5 :
    hessianC = 5 := by
  change deriv (fun y : ℝ => partialY z (5, y)) 2 = 5
  have hpow : HasDerivAt (fun y : ℝ => y ^ 2) 4 2 := by
    have hfun :
        (id * id : ℝ → ℝ) = (fun y : ℝ => y ^ 2) := by
      funext y
      simp [pow_two]
    rw [← hfun]
    convert
      ((hasDerivAt_id (2 : ℝ)).mul (hasDerivAt_id (2 : ℝ))) using 1 <;>
      norm_num [id]
  have hquot :
      HasDerivAt (fun y : ℝ => 20 / y ^ 2) (-5 : ℝ) 2 := by
    convert (hasDerivAt_const (2 : ℝ) (20 : ℝ)).div hpow (by norm_num) using 1 <;>
      norm_num
  have hExplicit :
      HasDerivAt (fun y : ℝ => 5 - 20 / y ^ 2) 5 2 := by
    convert (hasDerivAt_const (2 : ℝ) (5 : ℝ)).sub hquot using 1 <;>
      norm_num
  have hne : ∀ᶠ y : ℝ in nhds 2, y ≠ 0 :=
    eventually_ne_nhds (by norm_num)
  have heq :
      (fun y : ℝ => partialY z (5, y)) =ᶠ[nhds 2]
        (fun y : ℝ => 5 - 20 / y ^ 2) := by
    exact hne.mono (fun y hy => by
      simpa using partialY_z_of_ne (5, y) hy)
  exact (hExplicit.congr_of_eventuallyEq heq).deriv

theorem gap6 :
    hessianDiscriminant = 3 := by
  norm_num [hessianDiscriminant, gap3, gap4, gap5]

theorem gap7 :
    (3 : ℝ) > 0 := by
  norm_num

theorem gap8 :
    IsUniqueGlobalMinimizerOn z positiveQuadrant basePoint := by
  refine ⟨by norm_num [positiveQuadrant, basePoint], ?_, ?_⟩
  · intro q hq
    rcases q with ⟨x, y⟩
    change 0 < x ∧ 0 < y at hq
    have hbound := (z_bound_and_rigidity x y hq.1 hq.2).1
    have hbase : z basePoint = 30 := by
      norm_num [z, basePoint]
    rw [hbase]
    exact hbound
  · intro q hq hz
    rcases q with ⟨x, y⟩
    change 0 < x ∧ 0 < y at hq
    have hbase : z basePoint = 30 := by
      norm_num [z, basePoint]
    have hz30 : z (x, y) = 30 := hz.trans hbase
    obtain ⟨hx, hy⟩ :=
      (z_bound_and_rigidity x y hq.1 hq.2).2 hz30
    subst x
    subst y
    rfl

theorem gap9 :
    z basePoint = 30 := by
  norm_num [z, basePoint]

end

end ProofGap.Exercise3628
