import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3626

noncomputable section

def z (p : ℝ × ℝ) : ℝ :=
  p.1 ^ 3 + p.2 ^ 3 - 3 * p.1 * p.2

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

def p₀ : ℝ × ℝ :=
  (0, 0)

def p₁ : ℝ × ℝ :=
  (1, 1)

def criticalPoints : Set (ℝ × ℝ) :=
  {p₀, p₁}

def hessianA (p : ℝ × ℝ) : ℝ :=
  partialXX z p

def hessianB (p : ℝ × ℝ) : ℝ :=
  partialXY z p

def hessianC (p : ℝ × ℝ) : ℝ :=
  partialYY z p

def hessianDiscriminant (p : ℝ × ℝ) : ℝ :=
  hessianA p * hessianC p - hessianB p ^ 2

def IsLocalMinimum
    (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ q : ℝ × ℝ, ‖q - p‖ < ε → g p ≤ g q

def IsLocalMaximum
    (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ q : ℝ × ℝ, ‖q - p‖ < ε → g q ≤ g p

private theorem partialX_z_formula (p : ℝ × ℝ) :
    partialX z p = 3 * p.1 ^ 2 - 3 * p.2 := by
  change deriv (fun x : ℝ => x ^ 3 + p.2 ^ 3 - 3 * x * p.2) p.1 = _
  have hcube :=
    ((hasDerivAt_id p.1).mul (hasDerivAt_id p.1)).mul
      (hasDerivAt_id p.1)
  have hlinear := (hasDerivAt_id p.1).const_mul (3 * p.2)
  have hd := ((hcube.add_const (p.2 ^ 3)).sub hlinear).deriv
  have hfun :
      (fun x : ℝ => x ^ 3 + p.2 ^ 3 - 3 * x * p.2) =
        ((fun x : ℝ =>
            ((((id : ℝ → ℝ) * (id : ℝ → ℝ)) *
                (id : ℝ → ℝ)) x) + p.2 ^ 3) -
          (fun y : ℝ => 3 * p.2 * ((id : ℝ → ℝ) y))) := by
    funext x
    change
      x ^ 3 + p.2 ^ 3 - 3 * x * p.2 =
        x * x * x + p.2 ^ 3 - 3 * p.2 * x
    ring
  calc
    deriv (fun x : ℝ => x ^ 3 + p.2 ^ 3 - 3 * x * p.2) p.1 =
        deriv
          ((fun x : ℝ =>
              ((((id : ℝ → ℝ) * (id : ℝ → ℝ)) *
                  (id : ℝ → ℝ)) x) + p.2 ^ 3) -
            (fun y : ℝ => 3 * p.2 * ((id : ℝ → ℝ) y)))
          p.1 :=
      congrArg (fun f : ℝ → ℝ => deriv f p.1) hfun
    _ = _ := hd
    _ = 3 * p.1 ^ 2 - 3 * p.2 := by
      change
        ((1 * p.1 + p.1 * 1) * p.1 + p.1 * p.1 * 1) -
            3 * p.2 * 1 =
          3 * p.1 ^ 2 - 3 * p.2
      ring

private theorem partialY_z_formula (p : ℝ × ℝ) :
    partialY z p = 3 * p.2 ^ 2 - 3 * p.1 := by
  change deriv (fun y : ℝ => p.1 ^ 3 + y ^ 3 - 3 * p.1 * y) p.2 = _
  have hcube :=
    ((hasDerivAt_id p.2).mul (hasDerivAt_id p.2)).mul
      (hasDerivAt_id p.2)
  have hlinear := (hasDerivAt_id p.2).const_mul (3 * p.1)
  have hd :=
    (((hasDerivAt_const p.2 (p.1 ^ 3)).add hcube).sub hlinear).deriv
  have hfun :
      (fun y : ℝ => p.1 ^ 3 + y ^ 3 - 3 * p.1 * y) =
        (((fun _ : ℝ => p.1 ^ 3) +
            (((id : ℝ → ℝ) * (id : ℝ → ℝ)) *
              (id : ℝ → ℝ))) -
          (fun y : ℝ => 3 * p.1 * ((id : ℝ → ℝ) y))) := by
    funext y
    change
      p.1 ^ 3 + y ^ 3 - 3 * p.1 * y =
        p.1 ^ 3 + y * y * y - 3 * p.1 * y
    ring
  calc
    deriv (fun y : ℝ => p.1 ^ 3 + y ^ 3 - 3 * p.1 * y) p.2 =
        deriv
          (((fun _ : ℝ => p.1 ^ 3) +
              (((id : ℝ → ℝ) * (id : ℝ → ℝ)) *
                (id : ℝ → ℝ))) -
            (fun y : ℝ => 3 * p.1 * ((id : ℝ → ℝ) y)))
          p.2 :=
      congrArg (fun f : ℝ → ℝ => deriv f p.2) hfun
    _ = _ := hd
    _ = 3 * p.2 ^ 2 - 3 * p.1 := by
      change
        0 + ((1 * p.2 + p.2 * 1) * p.2 + p.2 * p.2 * 1) -
            3 * p.1 * 1 =
          3 * p.2 ^ 2 - 3 * p.1
      ring

private theorem partialXX_z_formula (p : ℝ × ℝ) :
    partialXX z p = 6 * p.1 := by
  unfold partialXX
  simp only [partialX_z_formula]
  change deriv (fun x : ℝ => 3 * x ^ 2 - 3 * p.2) p.1 = 6 * p.1
  have hsq := (hasDerivAt_id p.1).mul (hasDerivAt_id p.1)
  have hd :=
    ((hsq.const_mul (3 : ℝ)).sub_const (3 * p.2)).deriv
  have hfun :
      (fun x : ℝ => 3 * x ^ 2 - 3 * p.2) =
        (fun x : ℝ =>
          3 * (((id : ℝ → ℝ) * (id : ℝ → ℝ)) x) - 3 * p.2) := by
    funext x
    change 3 * x ^ 2 - 3 * p.2 = 3 * (x * x) - 3 * p.2
    ring
  calc
    deriv (fun x : ℝ => 3 * x ^ 2 - 3 * p.2) p.1 =
        deriv
          (fun x : ℝ =>
            3 * (((id : ℝ → ℝ) * (id : ℝ → ℝ)) x) - 3 * p.2)
          p.1 :=
      congrArg (fun f : ℝ → ℝ => deriv f p.1) hfun
    _ = _ := hd
    _ = 6 * p.1 := by
      change 3 * (1 * p.1 + p.1 * 1) = 6 * p.1
      ring

private theorem partialXY_z_formula (p : ℝ × ℝ) :
    partialXY z p = -3 := by
  unfold partialXY
  simp only [partialX_z_formula]
  have hd :=
    ((hasDerivAt_const p.2 (3 * p.1 ^ 2)).sub
      ((hasDerivAt_id p.2).const_mul (3 : ℝ))).deriv
  convert hd using 1 <;> norm_num

private theorem partialYY_z_formula (p : ℝ × ℝ) :
    partialYY z p = 6 * p.2 := by
  unfold partialYY
  simp only [partialY_z_formula]
  change deriv (fun y : ℝ => 3 * y ^ 2 - 3 * p.1) p.2 = 6 * p.2
  have hsq := (hasDerivAt_id p.2).mul (hasDerivAt_id p.2)
  have hd :=
    ((hsq.const_mul (3 : ℝ)).sub_const (3 * p.1)).deriv
  have hfun :
      (fun y : ℝ => 3 * y ^ 2 - 3 * p.1) =
        (fun y : ℝ =>
          3 * (((id : ℝ → ℝ) * (id : ℝ → ℝ)) y) - 3 * p.1) := by
    funext y
    change 3 * y ^ 2 - 3 * p.1 = 3 * (y * y) - 3 * p.1
    ring
  calc
    deriv (fun y : ℝ => 3 * y ^ 2 - 3 * p.1) p.2 =
        deriv
          (fun y : ℝ =>
            3 * (((id : ℝ → ℝ) * (id : ℝ → ℝ)) y) - 3 * p.1)
          p.2 :=
      congrArg (fun f : ℝ → ℝ => deriv f p.2) hfun
    _ = _ := hd
    _ = 6 * p.2 := by
      change 3 * (1 * p.2 + p.2 * 1) = 6 * p.2
      ring

theorem gap1 :
    ∀ p : ℝ × ℝ, p ∈ criticalPoints →
      partialX z p = 3 * p.1 ^ 2 - 3 * p.2 ∧
      3 * p.1 ^ 2 - 3 * p.2 = 0 ∧
      partialY z p = 3 * p.2 ^ 2 - 3 * p.1 ∧
      3 * p.2 ^ 2 - 3 * p.1 = 0 := by
  intro p hp
  have hp' : p = p₀ ∨ p = p₁ := by
    simpa [criticalPoints] using hp
  rcases hp' with rfl | rfl
  · norm_num [partialX_z_formula, partialY_z_formula, p₀]
  · norm_num [partialX_z_formula, partialY_z_formula, p₁]

theorem gap2 :
    p₀ = (0, 0) := by
  rfl

theorem gap3 :
    p₁ = (1, 1) := by
  rfl

theorem gap4 :
    hessianA p₀ = 0 := by
  norm_num [hessianA, partialXX_z_formula, p₀]

theorem gap5 :
    hessianB p₀ = -3 := by
  norm_num [hessianB, partialXY_z_formula, p₀]

theorem gap6 :
    hessianC p₀ = 0 := by
  norm_num [hessianC, partialYY_z_formula, p₀]

theorem gap7 :
    hessianDiscriminant p₀ = -9 := by
  norm_num [hessianDiscriminant, gap4, gap5, gap6]

theorem gap8 :
    (-9 : ℝ) < 0 := by
  norm_num

theorem gap9 :
    ¬ IsLocalMaximum z p₀ := by
  intro h
  rcases h with ⟨ε, hε, hmax⟩
  let q : ℝ × ℝ := (ε / 2, 0)
  have hhalf : ε / 2 < ε := by
    linarith
  have hdist : ‖q - p₀‖ < ε := by
    simpa [q, p₀, Prod.norm_def, Real.norm_eq_abs, abs_of_pos hε] using
      (And.intro hhalf hε)
  have hz := hmax q hdist
  have hcube : 0 < (ε / 2) ^ 3 := by
    exact pow_pos (by linarith) _
  have hzq : z q = (ε / 2) ^ 3 := by
    simp [q, z]
  have hzp : z p₀ = 0 := by
    norm_num [z, p₀]
  rw [hzq, hzp] at hz
  exact (not_le_of_gt hcube) hz

theorem gap10 :
    ¬ IsLocalMinimum z p₀ := by
  intro h
  rcases h with ⟨ε, hε, hmin⟩
  let q : ℝ × ℝ := (-(ε / 2), 0)
  have hhalf : ε / 2 < ε := by
    linarith
  have hdist : ‖q - p₀‖ < ε := by
    simpa [q, p₀, Prod.norm_def, Real.norm_eq_abs, abs_of_pos hε] using
      (And.intro hhalf hε)
  have hz := hmin q hdist
  have hcube : 0 < (ε / 2) ^ 3 := by
    exact pow_pos (by linarith) _
  have hzq : z q = -(ε / 2) ^ 3 := by
    dsimp [q, z]
    ring
  have hzp : z p₀ = 0 := by
    norm_num [z, p₀]
  rw [hzp, hzq] at hz
  nlinarith

theorem gap11 :
    hessianA p₁ = 6 := by
  norm_num [hessianA, partialXX_z_formula, p₁]

theorem gap12 :
    hessianB p₁ = -3 := by
  norm_num [hessianB, partialXY_z_formula, p₁]

theorem gap13 :
    hessianC p₁ = 6 := by
  norm_num [hessianC, partialYY_z_formula, p₁]

theorem gap14 :
    hessianDiscriminant p₁ = 27 := by
  norm_num [hessianDiscriminant, gap11, gap12, gap13]

theorem gap15 :
    (27 : ℝ) > 0 := by
  norm_num

theorem gap16 :
    IsLocalMinimum z p₁ := by
  refine ⟨1, by norm_num, ?_⟩
  intro q hq
  have hpair : q - p₁ = (q.1 - 1, q.2 - 1) := by
    ext <;> simp [p₁]
  rw [hpair, Prod.norm_def] at hq
  have hxnorm : ‖q.1 - 1‖ < 1 :=
    lt_of_le_of_lt (le_max_left _ _) hq
  have hynorm : ‖q.2 - 1‖ < 1 :=
    lt_of_le_of_lt (le_max_right _ _) hq
  rw [Real.norm_eq_abs] at hxnorm hynorm
  have hx : 0 < q.1 := by
    have h := (abs_lt.mp hxnorm).1
    linarith
  have hy : 0 < q.2 := by
    have h := (abs_lt.mp hynorm).1
    linarith
  have hsum : 0 ≤ q.1 + q.2 + 1 := by
    linarith
  have hquad :
      0 ≤ q.1 ^ 2 + q.2 ^ 2 + 1 - q.1 * q.2 - q.1 - q.2 := by
    have hxy := sq_nonneg (q.1 - q.2)
    have hx1 := sq_nonneg (q.1 - 1)
    have hy1 := sq_nonneg (q.2 - 1)
    nlinarith
  have hfactor :
      z q + 1 =
        (q.1 + q.2 + 1) *
          (q.1 ^ 2 + q.2 ^ 2 + 1 - q.1 * q.2 - q.1 - q.2) := by
    simp only [z]
    ring
  have hnonneg : 0 ≤ z q + 1 := by
    rw [hfactor]
    exact mul_nonneg hsum hquad
  have hp : z p₁ = -1 := by
    norm_num [z, p₁]
  rw [hp]
  nlinarith

theorem gap17 :
    z p₁ = -1 := by
  norm_num [z, p₁]

end

end ProofGap.Exercise3626
