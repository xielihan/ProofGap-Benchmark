import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise3636

noncomputable section

def z (p : ℝ × ℝ) : ℝ :=
  Real.sin p.1 + Real.cos p.2 + Real.cos (p.1 - p.2)

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

def box : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ Real.pi / 2 ∧
    0 ≤ p.2 ∧ p.2 ≤ Real.pi / 2}

def IsCriticalPointInBox (p : ℝ × ℝ) : Prop :=
  p ∈ box ∧ partialX z p = 0 ∧ partialY z p = 0

def basePoint : ℝ × ℝ :=
  (Real.pi / 3, Real.pi / 6)

def hessianA : ℝ :=
  partialXX z basePoint

def hessianB : ℝ :=
  partialXY z basePoint

def hessianC : ℝ :=
  partialYY z basePoint

def hessianDiscriminant : ℝ :=
  hessianA * hessianC - hessianB ^ 2

def IsUniqueGlobalMaximizerOn
    (g : ℝ × ℝ → ℝ) (s : Set (ℝ × ℝ)) (p : ℝ × ℝ) : Prop :=
  p ∈ s ∧ (∀ q ∈ s, g q ≤ g p) ∧
    (∀ q ∈ s, g q = g p → q = p)

private theorem partialX_z_formula (p : ℝ × ℝ) :
    partialX z p = Real.cos p.1 - Real.sin (p.1 - p.2) := by
  unfold partialX
  simpa [z] using
    (((Real.hasDerivAt_sin p.1).add_const (Real.cos p.2)).add
      ((Real.hasDerivAt_cos (p.1 - p.2)).comp p.1
        ((hasDerivAt_id p.1).sub_const p.2))).deriv

private theorem partialY_z_formula (p : ℝ × ℝ) :
    partialY z p = -Real.sin p.2 + Real.sin (p.1 - p.2) := by
  unfold partialY
  simpa [z] using
    (((Real.hasDerivAt_cos p.2).const_add (Real.sin p.1)).add
      ((Real.hasDerivAt_cos (p.1 - p.2)).comp p.2
        ((hasDerivAt_id p.2).const_sub p.1))).deriv

private theorem sin_pi_third_sub_sixth :
    Real.sin (Real.pi / 3 - Real.pi / 6) = 1 / 2 := by
  rw [show Real.pi / 3 - Real.pi / 6 = Real.pi / 6 by ring,
    Real.sin_pi_div_six]

private theorem cos_pi_third_sub_sixth :
    Real.cos (Real.pi / 3 - Real.pi / 6) = Real.sqrt 3 / 2 := by
  rw [show Real.pi / 3 - Real.pi / 6 = Real.pi / 6 by ring,
    Real.cos_pi_div_six]

private theorem z_basePoint_formula :
    z basePoint = (3 / 2 : ℝ) * Real.sqrt 3 := by
  unfold z basePoint
  change Real.sin (Real.pi / 3) + Real.cos (Real.pi / 6) +
      Real.cos (Real.pi / 3 - Real.pi / 6) =
    (3 / 2 : ℝ) * Real.sqrt 3
  rw [Real.sin_pi_div_three, Real.cos_pi_div_six,
    cos_pi_third_sub_sixth]
  ring

private theorem sine_triangle_bound (a b c : ℝ)
    (ha : a ∈ Set.Icc (0 : ℝ) Real.pi)
    (hb : b ∈ Set.Icc (0 : ℝ) Real.pi)
    (hc : c ∈ Set.Icc (0 : ℝ) Real.pi)
    (habc : a + b + c = Real.pi) :
    Real.sin a + Real.sin b + Real.sin c ≤
        (3 / 2 : ℝ) * Real.sqrt 3 ∧
      (Real.sin a + Real.sin b + Real.sin c =
          (3 / 2 : ℝ) * Real.sqrt 3 →
        a = Real.pi / 3 ∧ b = Real.pi / 3 ∧ c = Real.pi / 3) := by
  let s : ℝ := (a + b) / 2
  let d : ℝ := (a - b) / 2
  let u : ℝ := Real.cos s
  let v : ℝ := Real.sin s
  have hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    constructor
    · dsimp [s]
      linarith [ha.1, hb.1]
    · dsimp [s]
      linarith [habc, hc.1]
  have hd : d ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> dsimp [d] <;> linarith [ha.1, ha.2, hb.1, hb.2]
  have hv : 0 ≤ v := by
    dsimp [v]
    exact Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2, Real.pi_pos])
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩
  have hu1 : u ≤ 1 := by
    dsimp [u]
    exact Real.cos_le_one s
  have hcd : Real.cos d ≤ 1 := Real.cos_le_one d
  have htrig : v ^ 2 + u ^ 2 = 1 := by
    dsimp [u, v]
    nlinarith [Real.sin_sq_add_cos_sq s]
  have hsum : Real.sin a + Real.sin b + Real.sin c =
      2 * v * Real.cos d + 2 * v * u := by
    have hae : a = s + d := by dsimp [s, d]; ring
    have hbe : b = s - d := by dsimp [s, d]; ring
    have hce : c = Real.pi - 2 * s := by dsimp [s]; linarith [habc]
    rw [hae, hbe, hce, Real.sin_add, Real.sin_sub, Real.sin_pi_sub,
      Real.sin_two_mul]
    dsimp [u, v]
    ring
  have hlinear : Real.sin a + Real.sin b + Real.sin c ≤ 2 * v * (1 + u) := by
    rw [hsum]
    nlinarith
  have hqpos : 0 < 4 * u ^ 2 + 12 * u + 11 := by nlinarith [sq_nonneg (2 * u)]
  have hfactor : 0 ≤ (2 * u - 1) ^ 2 * (4 * u ^ 2 + 12 * u + 11) :=
    mul_nonneg (sq_nonneg _) (le_of_lt hqpos)
  have hsq : (2 * v * (1 + u)) ^ 2 ≤ (27 / 4 : ℝ) := by
    nlinarith
  have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have ht_nonneg : 0 ≤ 2 * v * (1 + u) := by positivity
  have hbound : 2 * v * (1 + u) ≤ (3 / 2 : ℝ) * Real.sqrt 3 := by
    have hsqrt_nonneg := Real.sqrt_nonneg 3
    nlinarith
  constructor
  · linarith
  · intro heq
    have ht_eq : 2 * v * (1 + u) = (3 / 2 : ℝ) * Real.sqrt 3 := by
      linarith
    have hfaczero : (2 * u - 1) ^ 2 * (4 * u ^ 2 + 12 * u + 11) = 0 := by
      nlinarith
    have hu : u = 1 / 2 := by
      have hz : (2 * u - 1) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hfaczero with h | h
        · exact h
        · exfalso
          exact (ne_of_gt hqpos) h
      nlinarith [sq_nonneg (2 * u - 1)]
    have hvpos : 0 < v := by
      by_contra hn
      have : v = 0 := le_antisymm (le_of_not_gt hn) hv
      rw [this] at ht_eq
      have hsqrt_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
      nlinarith
    have hcdone : Real.cos d = 1 := by
      rw [hsum] at heq
      nlinarith
    have habsd_mem : |d| ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor
      · exact abs_nonneg d
      · apply (abs_le).2
        constructor <;> linarith [hd.1, hd.2, Real.pi_pos]
    have hzero_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor
      · rfl
      · exact le_of_lt Real.pi_pos
    have habsd : |d| = 0 := by
      apply Real.strictAntiOn_cos.injOn habsd_mem hzero_mem
      simpa [Real.cos_abs] using hcdone
    have hd0 : d = 0 := abs_eq_zero.mp habsd
    have hs_pi : s = Real.pi / 3 := by
      have hthird : Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi := by
        constructor <;> linarith [Real.pi_pos]
      apply Real.strictAntiOn_cos.injOn
      · exact ⟨hs.1, by linarith [hs.2, Real.pi_pos]⟩
      · exact hthird
      · dsimp [u] at hu
        simpa [Real.cos_pi_div_three] using hu
    have hae : a = Real.pi / 3 := by dsimp [s, d] at hs_pi hd0; linarith
    have hbe : b = Real.pi / 3 := by dsimp [s, d] at hs_pi hd0; linarith
    have hce : c = Real.pi / 3 := by linarith [habc, hae, hbe]
    exact ⟨hae, hbe, hce⟩

theorem gap1 :
    ∀ p : ℝ × ℝ, IsCriticalPointInBox p →
      Real.cos p.1 = Real.sin p.2 := by
  intro p hp
  have hx := hp.2.1
  have hy := hp.2.2
  rw [partialX_z_formula] at hx
  rw [partialY_z_formula] at hy
  linarith

theorem gap2 :
    ∀ p : ℝ × ℝ, IsCriticalPointInBox p →
      p.2 = Real.pi / 2 - p.1 := by
  intro p hp
  have hbox := hp.1
  unfold box at hbox
  have heq : Real.sin (Real.pi / 2 - p.1) = Real.sin p.2 := by
    rw [Real.sin_pi_div_two_sub]
    exact gap1 p hp
  apply Real.strictMonoOn_sin.injOn
  · constructor <;> linarith [hbox.2.2.1, hbox.2.2.2, Real.pi_pos]
  · constructor <;> linarith [hbox.1, hbox.2.1, Real.pi_pos]
  · exact heq.symm

theorem gap3 :
    ∀ x : ℝ,
      Real.cos x - Real.sin (2 * x - Real.pi / 2) =
        Real.cos x + Real.cos (2 * x) := by
  intro x
  rw [Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

theorem gap4 :
    ∀ x : ℝ,
      Real.cos x + Real.cos (2 * x) =
        2 * Real.cos (x / 2) * Real.cos (3 * x / 2) := by
  intro x
  rw [Real.cos_add_cos]
  rw [show (x + 2 * x) / 2 = 3 * x / 2 by ring]
  rw [show (x - 2 * x) / 2 = -(x / 2) by ring, Real.cos_neg]
  ring

theorem gap5 :
    ∀ p : ℝ × ℝ, IsCriticalPointInBox p →
      2 * Real.cos (p.1 / 2) * Real.cos (3 * p.1 / 2) = 0 := by
  intro p hp
  have hx := hp.2.1
  rw [partialX_z_formula] at hx
  have hy := gap2 p hp
  rw [hy] at hx
  have harg : p.1 - (Real.pi / 2 - p.1) = 2 * p.1 - Real.pi / 2 := by ring
  rw [harg] at hx
  calc
    2 * Real.cos (p.1 / 2) * Real.cos (3 * p.1 / 2) =
        Real.cos p.1 + Real.cos (2 * p.1) := (gap4 p.1).symm
    _ = Real.cos p.1 - Real.sin (2 * p.1 - Real.pi / 2) := (gap3 p.1).symm
    _ = 0 := hx

theorem gap6 :
    ∀ p : ℝ × ℝ, IsCriticalPointInBox p →
      Real.cos p.1 - Real.sin (2 * p.1 - Real.pi / 2) = 0 := by
  intro p hp
  have hx := hp.2.1
  rw [partialX_z_formula] at hx
  have hy := gap2 p hp
  rw [hy] at hx
  have harg : p.1 - (Real.pi / 2 - p.1) = 2 * p.1 - Real.pi / 2 := by ring
  rw [harg] at hx
  exact hx

theorem gap7 :
    ∀ p : ℝ × ℝ, IsCriticalPointInBox p →
      Real.cos (p.1 / 2) ≠ 0 := by
  intro p hp
  apply ne_of_gt
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [hp.1.1, hp.1.2.1, Real.pi_pos]

theorem gap8 :
    ∀ p : ℝ × ℝ, IsCriticalPointInBox p →
      Real.cos (3 * p.1 / 2) = 0 := by
  intro p hp
  have hprod := gap5 p hp
  rcases mul_eq_zero.mp hprod with hleft | hright
  · exfalso
    exact (mul_ne_zero (by norm_num) (gap7 p hp)) hleft
  · exact hright

theorem gap9 :
    ∀ p : ℝ × ℝ, p ∈ ({basePoint} : Set (ℝ × ℝ)) →
      partialX z p = Real.cos p.1 - Real.sin (p.1 - p.2) ∧
      Real.cos p.1 - Real.sin (p.1 - p.2) = 0 ∧
      partialY z p = -Real.sin p.2 + Real.sin (p.1 - p.2) ∧
      -Real.sin p.2 + Real.sin (p.1 - p.2) = 0 := by
  intro p hp
  have hp' : p = basePoint := by simpa using hp
  subst p
  constructor
  · exact partialX_z_formula basePoint
  constructor
  · change Real.cos (Real.pi / 3) -
        Real.sin (Real.pi / 3 - Real.pi / 6) = 0
    rw [Real.cos_pi_div_three, sin_pi_third_sub_sixth]
    norm_num
  constructor
  · exact partialY_z_formula basePoint
  · change -Real.sin (Real.pi / 6) +
        Real.sin (Real.pi / 3 - Real.pi / 6) = 0
    rw [Real.sin_pi_div_six, sin_pi_third_sub_sixth]
    norm_num

theorem gap10 :
    basePoint = (Real.pi / 3, Real.pi / 6) := by
  rfl

theorem gap11 :
    ∀ p : ℝ × ℝ,
      partialXX z p = -Real.sin p.1 - Real.cos (p.1 - p.2) := by
  intro p
  unfold partialXX
  have hf : (fun x => partialX z (x, p.2)) =
      (fun x => Real.cos x - Real.sin (x - p.2)) := by
    funext x
    exact partialX_z_formula (x, p.2)
  rw [hf]
  simpa using
    ((Real.hasDerivAt_cos p.1).sub
      ((Real.hasDerivAt_sin (p.1 - p.2)).comp p.1
        ((hasDerivAt_id p.1).sub_const p.2))).deriv

theorem gap12 :
    ∀ p : ℝ × ℝ,
      partialYY z p = -Real.cos p.2 - Real.cos (p.1 - p.2) := by
  intro p
  unfold partialYY
  have hf : (fun y => partialY z (p.1, y)) =
      (fun y => -Real.sin y + Real.sin (p.1 - y)) := by
    funext y
    exact partialY_z_formula (p.1, y)
  rw [hf]
  simpa using
    (((Real.hasDerivAt_sin p.2).neg).add
      ((Real.hasDerivAt_sin (p.1 - p.2)).comp p.2
        ((hasDerivAt_id p.2).const_sub p.1))).deriv

theorem gap13 :
    ∀ p : ℝ × ℝ,
      partialXY z p = Real.cos (p.1 - p.2) := by
  intro p
  unfold partialXY
  have hf : (fun y => partialX z (p.1, y)) =
      (fun y => Real.cos p.1 - Real.sin (p.1 - y)) := by
    funext y
    exact partialX_z_formula (p.1, y)
  rw [hf]
  simpa using
    (((Real.hasDerivAt_sin (p.1 - p.2)).comp p.2
      ((hasDerivAt_id p.2).const_sub p.1)).const_sub (Real.cos p.1)).deriv

theorem gap14 :
    hessianA = -Real.sqrt 3 := by
  unfold hessianA
  rw [gap11]
  change -Real.sin (Real.pi / 3) -
      Real.cos (Real.pi / 3 - Real.pi / 6) = -Real.sqrt 3
  rw [Real.sin_pi_div_three, cos_pi_third_sub_sixth]
  ring

theorem gap15 :
    hessianB = Real.sqrt 3 / 2 := by
  unfold hessianB
  rw [gap13]
  change Real.cos (Real.pi / 3 - Real.pi / 6) = Real.sqrt 3 / 2
  exact cos_pi_third_sub_sixth

theorem gap16 :
    hessianC = -Real.sqrt 3 := by
  unfold hessianC
  rw [gap12]
  change -Real.cos (Real.pi / 6) -
      Real.cos (Real.pi / 3 - Real.pi / 6) = -Real.sqrt 3
  rw [Real.cos_pi_div_six, cos_pi_third_sub_sixth]
  ring

theorem gap17 :
    hessianDiscriminant = (9 / 4 : ℝ) := by
  unfold hessianDiscriminant
  rw [gap14, gap15, gap16]
  have hs : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  nlinarith

theorem gap18 :
    (9 / 4 : ℝ) > 0 := by
  norm_num

theorem gap19 :
    IsUniqueGlobalMaximizerOn z box basePoint := by
  have hbase : basePoint ∈ box := by
    unfold basePoint box
    simp only [Set.mem_setOf_eq, Prod.fst, Prod.snd]
    constructor
    · linarith [Real.pi_pos]
    constructor
    · linarith [Real.pi_pos]
    constructor
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  refine ⟨hbase, ?_, ?_⟩
  · intro q hq
    let a : ℝ := q.1
    let b : ℝ := Real.pi / 2 - q.2
    let c : ℝ := Real.pi / 2 - q.1 + q.2
    have ha : a ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor <;> dsimp [a] <;> linarith [hq.1, hq.2.1, Real.pi_pos]
    have hb : b ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor <;> dsimp [b] <;> linarith [hq.2.2.1, hq.2.2.2, Real.pi_pos]
    have hc : c ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor <;> dsimp [c] <;> linarith [hq.1, hq.2.1, hq.2.2.1, hq.2.2.2, Real.pi_pos]
    have habc : a + b + c = Real.pi := by dsimp [a, b, c]; ring
    have htri := sine_triangle_bound a b c ha hb hc habc
    have hcosb : Real.cos q.2 = Real.sin b := by
      dsimp [b]
      rw [Real.sin_pi_div_two_sub]
    have hcosc : Real.cos (q.1 - q.2) = Real.sin c := by
      dsimp [c]
      rw [show Real.pi / 2 - q.1 + q.2 =
          Real.pi / 2 - (q.1 - q.2) by ring, Real.sin_pi_div_two_sub]
    have hzq : z q = Real.sin a + Real.sin b + Real.sin c := by
      unfold z
      dsimp [a]
      rw [hcosb, hcosc]
    rw [hzq, z_basePoint_formula]
    exact htri.1
  · intro q hq heq
    let a : ℝ := q.1
    let b : ℝ := Real.pi / 2 - q.2
    let c : ℝ := Real.pi / 2 - q.1 + q.2
    have ha : a ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor <;> dsimp [a] <;> linarith [hq.1, hq.2.1, Real.pi_pos]
    have hb : b ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor <;> dsimp [b] <;> linarith [hq.2.2.1, hq.2.2.2, Real.pi_pos]
    have hc : c ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor <;> dsimp [c] <;> linarith [hq.1, hq.2.1, hq.2.2.1, hq.2.2.2, Real.pi_pos]
    have habc : a + b + c = Real.pi := by dsimp [a, b, c]; ring
    have hcosb : Real.cos q.2 = Real.sin b := by
      dsimp [b]
      rw [Real.sin_pi_div_two_sub]
    have hcosc : Real.cos (q.1 - q.2) = Real.sin c := by
      dsimp [c]
      rw [show Real.pi / 2 - q.1 + q.2 =
          Real.pi / 2 - (q.1 - q.2) by ring, Real.sin_pi_div_two_sub]
    have hzq : z q = Real.sin a + Real.sin b + Real.sin c := by
      unfold z
      dsimp [a]
      rw [hcosb, hcosc]
    have hmax : Real.sin a + Real.sin b + Real.sin c =
        (3 / 2 : ℝ) * Real.sqrt 3 := by
      rw [← hzq, ← z_basePoint_formula]
      exact heq
    have huniq := (sine_triangle_bound a b c ha hb hc habc).2 hmax
    rcases huniq with ⟨haeq, hbeq, hceq⟩
    apply Prod.ext
    · simpa [a, basePoint] using haeq
    · dsimp [b] at hbeq
      simp [basePoint]
      linarith [hbeq]

theorem gap20 :
    z basePoint = (3 / 2 : ℝ) * Real.sqrt 3 := by
  exact z_basePoint_formula

end

end ProofGap.Exercise3636
