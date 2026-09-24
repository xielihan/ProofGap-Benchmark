import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise3633

noncomputable section

def z (p : ℝ × ℝ) : ℝ :=
  Real.exp (p.1 ^ 2 - p.2) * (5 - 2 * p.1 + p.2)

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

def basePoint : ℝ × ℝ :=
  (1, -2)

def hessianA : ℝ :=
  partialXX z basePoint

def hessianB : ℝ :=
  partialXY z basePoint

def hessianC : ℝ :=
  partialYY z basePoint

def hessianDiscriminant : ℝ :=
  hessianA * hessianC - hessianB ^ 2

def IsLocalMinimum
    (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ q : ℝ × ℝ, ‖q - p‖ < ε → g p ≤ g q

def IsLocalMaximum
    (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ q : ℝ × ℝ, ‖q - p‖ < ε → g q ≤ g p

def localMinimumPoints : Set (ℝ × ℝ) :=
  {p | IsLocalMinimum z p}

def localMaximumPoints : Set (ℝ × ℝ) :=
  {p | IsLocalMaximum z p}

private theorem firstDerivatives (p : ℝ × ℝ) :
    HasDerivAt (fun x => z (x, p.2))
      (2 * Real.exp (p.1 ^ 2 - p.2) *
        (5 * p.1 - 2 * p.1 ^ 2 + p.1 * p.2 - 1)) p.1 ∧
    HasDerivAt (fun y => z (p.1, y))
      (Real.exp (p.1 ^ 2 - p.2) * (2 * p.1 - p.2 - 4)) p.2 := by
  unfold z
  have hxsq :
      HasDerivAt (fun x : ℝ => x ^ 2) (2 * p.1) p.1 := by
    simpa [pow_two, two_mul] using
      (hasDerivAt_id p.1).mul (hasDerivAt_id p.1)
  have hxinner :
      HasDerivAt (fun x : ℝ => x ^ 2 - p.2) (2 * p.1) p.1 :=
    hxsq.sub_const p.2
  have hxexp :
      HasDerivAt (fun x : ℝ => Real.exp (x ^ 2 - p.2))
        (Real.exp (p.1 ^ 2 - p.2) * (2 * p.1)) p.1 := by
    convert (Real.hasDerivAt_exp (p.1 ^ 2 - p.2)).comp p.1 hxinner using 1 <;>
      simp <;> ring
  have hxfactor :
      HasDerivAt (fun x : ℝ => 5 - 2 * x + p.2) (-2) p.1 := by
    convert
      (((hasDerivAt_const p.1 5).sub
        ((hasDerivAt_id p.1).const_mul 2)).add_const p.2)
      using 1 <;> simp <;> ring
  have hyinner :
      HasDerivAt (fun y : ℝ => p.1 ^ 2 - y) (-1) p.2 := by
    convert
      ((hasDerivAt_const p.2 (p.1 ^ 2)).sub (hasDerivAt_id p.2))
      using 1 <;> simp <;> ring
  have hyexp :
      HasDerivAt (fun y : ℝ => Real.exp (p.1 ^ 2 - y))
        (-Real.exp (p.1 ^ 2 - p.2)) p.2 := by
    convert (Real.hasDerivAt_exp (p.1 ^ 2 - p.2)).comp p.2 hyinner using 1 <;>
      simp <;> ring
  have hyfactor :
      HasDerivAt (fun y : ℝ => 5 - 2 * p.1 + y) 1 p.2 := by
    convert
      ((hasDerivAt_const p.2 (5 - 2 * p.1)).add (hasDerivAt_id p.2))
      using 1 <;> simp <;> ring
  constructor
  · convert hxexp.mul hxfactor using 1 <;> simp <;> ring
  · convert hyexp.mul hyfactor using 1 <;> simp <;> ring

theorem gap1 :
    ∀ p : ℝ × ℝ, p ∈ ({basePoint} : Set (ℝ × ℝ)) →
      partialX z p =
          2 * Real.exp (p.1 ^ 2 - p.2) *
            (5 * p.1 - 2 * p.1 ^ 2 + p.1 * p.2 - 1) ∧
      2 * Real.exp (p.1 ^ 2 - p.2) *
          (5 * p.1 - 2 * p.1 ^ 2 + p.1 * p.2 - 1) = 0 ∧
      partialY z p =
          Real.exp (p.1 ^ 2 - p.2) * (2 * p.1 - p.2 - 4) ∧
      Real.exp (p.1 ^ 2 - p.2) * (2 * p.1 - p.2 - 4) = 0 := by
  intro p hp
  have hp' : p = basePoint := by
    simpa only [Set.mem_singleton_iff] using hp
  subst p
  constructor
  · exact (firstDerivatives basePoint).1.deriv
  constructor
  · norm_num [basePoint]
  constructor
  · exact (firstDerivatives basePoint).2.deriv
  · norm_num [basePoint]

theorem gap2 :
    basePoint = (1, -2) := by
  rfl

theorem gap3 :
    ∀ p : ℝ × ℝ,
      partialXX z p =
        2 * Real.exp (p.1 ^ 2 - p.2) *
          (10 * p.1 ^ 2 - 4 * p.1 ^ 3 + 2 * p.1 ^ 2 * p.2 -
            6 * p.1 + p.2 + 5) := by
  intro p
  unfold partialXX
  rw [show
    (fun x => partialX z (x, p.2)) =
      (fun x =>
        2 * Real.exp (x ^ 2 - p.2) *
          (5 * x - 2 * x ^ 2 + x * p.2 - 1)) by
      funext x
      simpa [partialX] using (firstDerivatives (x, p.2)).1.deriv]
  have hxsq :
      HasDerivAt (fun x : ℝ => x ^ 2) (2 * p.1) p.1 := by
    simpa [pow_two, two_mul] using
      (hasDerivAt_id p.1).mul (hasDerivAt_id p.1)
  have hinner :
      HasDerivAt (fun x : ℝ => x ^ 2 - p.2) (2 * p.1) p.1 :=
    hxsq.sub_const p.2
  have hexp :
      HasDerivAt (fun x : ℝ => Real.exp (x ^ 2 - p.2))
        (Real.exp (p.1 ^ 2 - p.2) * (2 * p.1)) p.1 := by
    convert (Real.hasDerivAt_exp (p.1 ^ 2 - p.2)).comp p.1 hinner using 1 <;>
      simp <;> ring
  have hpoly :
      HasDerivAt
        (fun x : ℝ => 5 * x - 2 * x ^ 2 + x * p.2 - 1)
        (5 - 4 * p.1 + p.2) p.1 := by
    convert
      (((((hasDerivAt_id p.1).const_mul 5).sub
          (hxsq.const_mul 2)).add
        ((hasDerivAt_id p.1).mul_const p.2)).sub_const 1)
      using 1 <;> simp <;> ring
  have h := (hexp.const_mul 2).mul hpoly
  change
    deriv
      ((fun x : ℝ => 2 * Real.exp (x ^ 2 - p.2)) *
        (fun x : ℝ => 5 * x - 2 * x ^ 2 + x * p.2 - 1)) p.1 = _
  calc
    _ =
        2 * (Real.exp (p.1 ^ 2 - p.2) * (2 * p.1)) *
            (5 * p.1 - 2 * p.1 ^ 2 + p.1 * p.2 - 1) +
          2 * Real.exp (p.1 ^ 2 - p.2) * (5 - 4 * p.1 + p.2) :=
      h.deriv
    _ = _ := by ring

theorem gap4 :
    ∀ p : ℝ × ℝ,
      partialYY z p =
        Real.exp (p.1 ^ 2 - p.2) * (3 - 2 * p.1 + p.2) := by
  intro p
  unfold partialYY
  rw [show
    (fun y => partialY z (p.1, y)) =
      (fun y => Real.exp (p.1 ^ 2 - y) * (2 * p.1 - y - 4)) by
      funext y
      simpa [partialY] using (firstDerivatives (p.1, y)).2.deriv]
  have hinner :
      HasDerivAt (fun y : ℝ => p.1 ^ 2 - y) (-1) p.2 := by
    convert
      ((hasDerivAt_const p.2 (p.1 ^ 2)).sub (hasDerivAt_id p.2))
      using 1 <;> simp <;> ring
  have hexp :
      HasDerivAt (fun y : ℝ => Real.exp (p.1 ^ 2 - y))
        (-Real.exp (p.1 ^ 2 - p.2)) p.2 := by
    convert (Real.hasDerivAt_exp (p.1 ^ 2 - p.2)).comp p.2 hinner using 1 <;>
      simp <;> ring
  have hlinear :
      HasDerivAt (fun y : ℝ => 2 * p.1 - y - 4) (-1) p.2 := by
    convert
      (((hasDerivAt_const p.2 (2 * p.1)).sub
        (hasDerivAt_id p.2)).sub_const 4)
      using 1 <;> simp <;> ring
  have h := hexp.mul hlinear
  convert h.deriv using 1 <;> simp <;> ring

theorem gap5 :
    ∀ p : ℝ × ℝ,
      partialXY z p =
        2 * Real.exp (p.1 ^ 2 - p.2) *
          (2 * p.1 ^ 2 - p.1 * p.2 - 4 * p.1 + 1) := by
  intro p
  unfold partialXY
  rw [show
    (fun y => partialX z (p.1, y)) =
      (fun y =>
        2 * Real.exp (p.1 ^ 2 - y) *
          (5 * p.1 - 2 * p.1 ^ 2 + p.1 * y - 1)) by
      funext y
      simpa [partialX] using (firstDerivatives (p.1, y)).1.deriv]
  have hinner :
      HasDerivAt (fun y : ℝ => p.1 ^ 2 - y) (-1) p.2 := by
    convert
      ((hasDerivAt_const p.2 (p.1 ^ 2)).sub (hasDerivAt_id p.2))
      using 1 <;> simp <;> ring
  have hexp :
      HasDerivAt (fun y : ℝ => Real.exp (p.1 ^ 2 - y))
        (-Real.exp (p.1 ^ 2 - p.2)) p.2 := by
    convert (Real.hasDerivAt_exp (p.1 ^ 2 - p.2)).comp p.2 hinner using 1 <;>
      simp <;> ring
  have hpoly :
      HasDerivAt
        (fun y : ℝ => 5 * p.1 - 2 * p.1 ^ 2 + p.1 * y - 1)
        p.1 p.2 := by
    convert
      ((((hasDerivAt_const p.2 (5 * p.1)).sub
          (hasDerivAt_const p.2 (2 * p.1 ^ 2))).add
        ((hasDerivAt_id p.2).const_mul p.1)).sub_const 1)
      using 1 <;> simp <;> ring
  have h := (hexp.const_mul 2).mul hpoly
  change
    deriv
      ((fun y : ℝ => 2 * Real.exp (p.1 ^ 2 - y)) *
        (fun y : ℝ => 5 * p.1 - 2 * p.1 ^ 2 + p.1 * y - 1)) p.2 = _
  calc
    _ =
        2 * (-Real.exp (p.1 ^ 2 - p.2)) *
            (5 * p.1 - 2 * p.1 ^ 2 + p.1 * p.2 - 1) +
          2 * Real.exp (p.1 ^ 2 - p.2) * p.1 :=
      h.deriv
    _ = _ := by ring

theorem gap6 :
    hessianA = -2 * Real.exp 3 := by
  unfold hessianA
  rw [gap3 basePoint]
  norm_num [basePoint]

theorem gap7 :
    hessianB = 2 * Real.exp 3 := by
  unfold hessianB
  rw [gap5 basePoint]
  norm_num [basePoint]

theorem gap8 :
    hessianC = -Real.exp 3 := by
  unfold hessianC
  rw [gap4 basePoint]
  norm_num [basePoint]

theorem gap9 :
    hessianDiscriminant = -2 * Real.exp 6 := by
  have he : Real.exp 3 * Real.exp 3 = Real.exp 6 := by
    rw [← Real.exp_add]
    norm_num
  unfold hessianDiscriminant
  rw [gap6, gap7, gap8]
  calc
    (-2 * Real.exp 3) * (-Real.exp 3) - (2 * Real.exp 3) ^ 2 =
        -2 * (Real.exp 3 * Real.exp 3) := by ring
    _ = -2 * Real.exp 6 := by rw [he]

theorem gap10 :
    -2 * Real.exp 6 < 0 := by
  have h := Real.exp_pos 6
  nlinarith

theorem gap11 :
    localMaximumPoints = ∅ := by
  ext p
  rcases p with ⟨x, y⟩
  constructor
  · intro hp
    change IsLocalMaximum z (x, y) at hp
    rcases hp with ⟨ε, hε, hmax⟩
    have hxLocal : IsLocalMax (fun u => z (u, y)) x := by
      filter_upwards [Metric.ball_mem_nhds x hε] with u hu
      apply hmax (u, y)
      change max ‖u - x‖ ‖y - y‖ < ε
      simpa [Metric.mem_ball, dist_eq_norm] using hu
    have hyLocal : IsLocalMax (fun v => z (x, v)) y := by
      filter_upwards [Metric.ball_mem_nhds y hε] with v hv
      apply hmax (x, v)
      change max ‖x - x‖ ‖v - y‖ < ε
      simpa [Metric.mem_ball, dist_eq_norm] using hv
    have hdx : deriv (fun u => z (u, y)) x = 0 :=
      (show IsLocalExtr (fun u => z (u, y)) x from Or.inr hxLocal).deriv_eq_zero
    have hdy : deriv (fun v => z (x, v)) y = 0 :=
      (show IsLocalExtr (fun v => z (x, v)) y from Or.inr hyLocal).deriv_eq_zero
    rw [(firstDerivatives (x, y)).1.deriv] at hdx
    rw [(firstDerivatives (x, y)).2.deriv] at hdy
    have hxpoly : 5 * x - 2 * x ^ 2 + x * y - 1 = 0 := by
      exact (mul_eq_zero.mp hdx).resolve_left
        (mul_ne_zero (by norm_num) (ne_of_gt (Real.exp_pos _)))
    have hypoly : 2 * x - y - 4 = 0 := by
      exact (mul_eq_zero.mp hdy).resolve_left (ne_of_gt (Real.exp_pos _))
    have hyrel : y = 2 * x - 4 := by linarith
    rw [hyrel] at hxpoly
    have hxval : x = 1 := by nlinarith [hxpoly]
    have hyval : y = -2 := by rw [hyrel, hxval]; norm_num
    subst x
    subst y
    let t : ℝ := ε / 4
    have ht : 0 < t := by dsimp [t]; linarith
    have hdist :
        ‖((1 + t, -2 + 2 * t) : ℝ × ℝ) - (1, -2)‖ < ε := by
      change max ‖(1 + t) - 1‖ ‖(-2 + 2 * t) - (-2)‖ < ε
      have h2t : 0 < 2 * t := by positivity
      rw [show (1 + t) - 1 = t by ring,
        show (-2 + 2 * t) - (-2) = 2 * t by ring,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht, abs_of_pos h2t]
      have ht_le : t ≤ 2 * t := by linarith
      rw [max_eq_right ht_le]
      dsimp [t]
      linarith
    have hbound := hmax (1 + t, -2 + 2 * t) hdist
    have hzp : z (1, -2) = Real.exp 3 := by
      norm_num [z]
    have hzq : z (1 + t, -2 + 2 * t) = Real.exp (3 + t ^ 2) := by
      unfold z
      dsimp
      rw [show (1 + t) ^ 2 - (-2 + 2 * t) = 3 + t ^ 2 by ring,
        show 5 - 2 * (1 + t) + (-2 + 2 * t) = 1 by ring]
      ring
    rw [hzp, hzq] at hbound
    have hexp : Real.exp 3 < Real.exp (3 + t ^ 2) :=
      Real.exp_lt_exp.mpr (by nlinarith [sq_pos_of_pos ht])
    linarith
  · intro hp
    exact hp.elim

theorem gap12 :
    localMinimumPoints = ∅ := by
  ext p
  rcases p with ⟨x, y⟩
  constructor
  · intro hp
    change IsLocalMinimum z (x, y) at hp
    rcases hp with ⟨ε, hε, hmin⟩
    have hxLocal : IsLocalMin (fun u => z (u, y)) x := by
      filter_upwards [Metric.ball_mem_nhds x hε] with u hu
      apply hmin (u, y)
      change max ‖u - x‖ ‖y - y‖ < ε
      simpa [Metric.mem_ball, dist_eq_norm] using hu
    have hyLocal : IsLocalMin (fun v => z (x, v)) y := by
      filter_upwards [Metric.ball_mem_nhds y hε] with v hv
      apply hmin (x, v)
      change max ‖x - x‖ ‖v - y‖ < ε
      simpa [Metric.mem_ball, dist_eq_norm] using hv
    have hdx : deriv (fun u => z (u, y)) x = 0 :=
      (show IsLocalExtr (fun u => z (u, y)) x from Or.inl hxLocal).deriv_eq_zero
    have hdy : deriv (fun v => z (x, v)) y = 0 :=
      (show IsLocalExtr (fun v => z (x, v)) y from Or.inl hyLocal).deriv_eq_zero
    rw [(firstDerivatives (x, y)).1.deriv] at hdx
    rw [(firstDerivatives (x, y)).2.deriv] at hdy
    have hxpoly : 5 * x - 2 * x ^ 2 + x * y - 1 = 0 := by
      exact (mul_eq_zero.mp hdx).resolve_left
        (mul_ne_zero (by norm_num) (ne_of_gt (Real.exp_pos _)))
    have hypoly : 2 * x - y - 4 = 0 := by
      exact (mul_eq_zero.mp hdy).resolve_left (ne_of_gt (Real.exp_pos _))
    have hyrel : y = 2 * x - 4 := by linarith
    rw [hyrel] at hxpoly
    have hxval : x = 1 := by nlinarith [hxpoly]
    have hyval : y = -2 := by rw [hyrel, hxval]; norm_num
    subst x
    subst y
    let t : ℝ := ε / 2
    have ht : 0 < t := by dsimp [t]; linarith
    have hdist : ‖((1, -2 + t) : ℝ × ℝ) - (1, -2)‖ < ε := by
      change max ‖(1 : ℝ) - 1‖ ‖(-2 + t) - (-2)‖ < ε
      rw [show (1 : ℝ) - 1 = 0 by ring,
        show (-2 + t) - (-2) = t by ring, norm_zero,
        Real.norm_eq_abs, abs_of_pos ht]
      simp only [max_eq_right (le_of_lt ht)]
      dsimp [t]
      linarith
    have hbound := hmin (1, -2 + t) hdist
    have hzp : z (1, -2) = Real.exp 3 := by
      norm_num [z]
    have hzq : z (1, -2 + t) = Real.exp (3 - t) * (1 + t) := by
      unfold z
      dsimp
      congr 1 <;> ring
    have hlinear : 1 + t < Real.exp t := by
      simpa [add_comm] using Real.add_one_lt_exp (ne_of_gt ht)
    have hprod : Real.exp (3 - t) * (1 + t) < Real.exp 3 := by
      have hm := mul_lt_mul_of_pos_left hlinear (Real.exp_pos (3 - t))
      have heq : Real.exp (3 - t) * Real.exp t = Real.exp 3 := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [heq] at hm
      exact hm
    rw [hzp, hzq] at hbound
    linarith
  · intro hp
    exact hp.elim

end

end ProofGap.Exercise3633
