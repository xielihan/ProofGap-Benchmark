import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3635

noncomputable section

def z (p : ℝ × ℝ) : ℝ :=
  p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 -
    4 * Real.log p.1 - 10 * Real.log p.2

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
  (1, 2)

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

def Approx (a b ε : ℝ) : Prop :=
  |a - b| < ε

private theorem partialX_z_of_ne (x y : ℝ) (hx : x ≠ 0) :
    partialX z (x, y) = 2 * x + y - 4 / x := by
  unfold partialX
  change deriv
    (fun t : ℝ => t ^ 2 + t * y + y ^ 2 - 4 * Real.log t - 10 * Real.log y) x = _
  have h :=
    (((((hasDerivAt_id x).pow 2).add
      ((hasDerivAt_id x).mul_const y)).add
      (hasDerivAt_const x (y ^ 2))).sub
      ((Real.hasDerivAt_log hx).const_mul 4)).sub
      (hasDerivAt_const x (10 * Real.log y))
  convert h.deriv using 1 <;> simp [div_eq_mul_inv] <;> ring

private theorem partialY_z_of_ne (x y : ℝ) (hy : y ≠ 0) :
    partialY z (x, y) = x + 2 * y - 10 / y := by
  unfold partialY
  change deriv
    (fun t : ℝ => x ^ 2 + x * t + t ^ 2 - 4 * Real.log x - 10 * Real.log t) y = _
  have h1 := (hasDerivAt_const y (x ^ 2)).add
    ((hasDerivAt_id y).const_mul x)
  have h2 := h1.add ((hasDerivAt_id y).pow 2)
  have h3 := h2.sub (hasDerivAt_const y (4 * Real.log x))
  have h4 := h3.sub ((Real.hasDerivAt_log hy).const_mul 10)
  convert h4.deriv using 1 <;> simp [div_eq_mul_inv] <;> ring

private theorem exp_nat_mul_local (x : ℝ) : ∀ n : ℕ,
    Real.exp ((n : ℝ) * x) = (Real.exp x) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, Real.exp_add, ih, pow_succ]

private theorem pow_le_pow_nonneg_local {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) : ∀ n : ℕ, a ^ n ≤ b ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact mul_le_mul ih hab ha (pow_nonneg (ha.trans hab) n)

theorem gap1 :
    ∀ p : ℝ × ℝ, p ∈ ({basePoint} : Set (ℝ × ℝ)) →
      p ∈ positiveQuadrant ∧
      partialX z p = 2 * p.1 + p.2 - 4 / p.1 ∧
      2 * p.1 + p.2 - 4 / p.1 = 0 ∧
      partialY z p = p.1 + 2 * p.2 - 10 / p.2 ∧
      p.1 + 2 * p.2 - 10 / p.2 = 0 := by
  intro p hp
  have hp' : p = basePoint := by
    simpa using hp
  subst p
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [positiveQuadrant, basePoint]
  · simpa [basePoint] using partialX_z_of_ne (1 : ℝ) 2 (by norm_num)
  · norm_num [basePoint]
  · simpa [basePoint] using partialY_z_of_ne (1 : ℝ) 2 (by norm_num)
  · norm_num [basePoint]

theorem gap2 :
    basePoint = (1, 2) := by
  rfl

theorem gap3 :
    hessianA = 6 := by
  change deriv (fun x : ℝ => partialX z (x, 2)) 1 = 6
  have heq :
      (fun x : ℝ => partialX z (x, 2)) =ᶠ[nhds 1]
        (fun x : ℝ => 2 * x + 2 - 4 / x) := by
    filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < 1 by norm_num)
      (show (1 : ℝ) < 2 by norm_num)] with x hx
    exact partialX_z_of_ne x 2 (ne_of_gt hx.1)
  rw [heq.deriv_eq]
  have hd : HasDerivAt (fun x : ℝ => 2 * x + 2 - 4 / x) 6 1 := by
    convert ((((hasDerivAt_id (1 : ℝ)).const_mul 2).add_const 2).sub
      ((hasDerivAt_const (1 : ℝ) 4).div (hasDerivAt_id (1 : ℝ)) (by norm_num))) using 1 <;>
      norm_num
  exact hd.deriv

theorem gap4 :
    hessianB = 1 := by
  change deriv (fun y : ℝ => partialX z (1, y)) 2 = 1
  have heq :
      (fun y : ℝ => partialX z (1, y)) =
        (fun y : ℝ => 2 * 1 + y - 4 / 1) := by
    funext y
    exact partialX_z_of_ne 1 y (by norm_num)
  rw [heq]
  have hd : HasDerivAt (fun y : ℝ => 2 * 1 + y - 4 / 1) 1 2 := by
    convert (hasDerivAt_id (2 : ℝ)).sub_const 2 using 1 <;>
      norm_num <;> ring_nf
  exact hd.deriv

theorem gap5 :
    hessianC = (9 / 2 : ℝ) := by
  change deriv (fun y : ℝ => partialY z (1, y)) 2 = (9 / 2 : ℝ)
  have heq :
      (fun y : ℝ => partialY z (1, y)) =ᶠ[nhds 2]
        (fun y : ℝ => 1 + 2 * y - 10 / y) := by
    filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < 2 by norm_num)
      (show (2 : ℝ) < 3 by norm_num)] with y hy
    exact partialY_z_of_ne 1 y (ne_of_gt hy.1)
  rw [heq.deriv_eq]
  have hd : HasDerivAt (fun y : ℝ => 1 + 2 * y - 10 / y) (9 / 2) 2 := by
    convert (((hasDerivAt_const (2 : ℝ) 1).add
      ((hasDerivAt_id (2 : ℝ)).const_mul 2)).sub
      ((hasDerivAt_const (2 : ℝ) 10).div (hasDerivAt_id (2 : ℝ)) (by norm_num))) using 1 <;>
      norm_num [div_eq_mul_inv] <;> ring_nf
  exact hd.deriv

theorem gap6 :
    hessianDiscriminant = 26 := by
  norm_num [hessianDiscriminant, gap3, gap4, gap5]

theorem gap7 :
    (26 : ℝ) > 0 := by
  norm_num

theorem gap8 :
    IsUniqueGlobalMinimizerOn z positiveQuadrant basePoint := by
  unfold IsUniqueGlobalMinimizerOn
  refine ⟨?_, ?_, ?_⟩
  · norm_num [positiveQuadrant, basePoint]
  · intro q hq
    rcases q with ⟨x, y⟩
    change 0 < x ∧ 0 < y at hq
    rcases hq with ⟨hx, hy⟩
    have hlogx : Real.log x ≤ x - 1 :=
      Real.log_le_sub_one_of_pos hx
    have hratio : 0 < y / 2 := div_pos hy (by norm_num)
    have hlogy : Real.log y - Real.log 2 ≤ y / 2 - 1 := by
      have h := Real.log_le_sub_one_of_pos hratio
      rw [Real.log_div hy.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h
      exact h
    have hquad :
        0 ≤ (x - 1) ^ 2 + (x - 1) * (y - 2) + (y - 2) ^ 2 := by
      nlinarith [sq_nonneg (2 * (x - 1) + (y - 2)), sq_nonneg (y - 2)]
    norm_num [z, basePoint]
    nlinarith
  · intro q hq heq
    rcases q with ⟨x, y⟩
    change 0 < x ∧ 0 < y at hq
    rcases hq with ⟨hx, hy⟩
    have hlogx : Real.log x ≤ x - 1 :=
      Real.log_le_sub_one_of_pos hx
    have hratio : 0 < y / 2 := div_pos hy (by norm_num)
    have hlogy : Real.log y - Real.log 2 ≤ y / 2 - 1 := by
      have h := Real.log_le_sub_one_of_pos hratio
      rw [Real.log_div hy.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h
      exact h
    norm_num [z, basePoint] at heq
    have hquad :
        (x - 1) ^ 2 + (x - 1) * (y - 2) + (y - 2) ^ 2 ≤ 0 := by
      nlinarith
    have hs₁ := sq_nonneg (2 * (x - 1) + (y - 2))
    have hs₂ := sq_nonneg (y - 2)
    have hy2 : y = 2 := by
      nlinarith
    have hx1 : x = 1 := by
      nlinarith
    simp [basePoint, hx1, hy2]

theorem gap9 :
    z basePoint = 7 - 10 * Real.log 2 := by
  norm_num [z, basePoint]

theorem gap10 :
    Approx (7 - 10 * Real.log 2) 0.0685 (1 / 10000 : ℝ) := by
  have hexpLower : Real.exp (69314 / 100000 : ℝ) < 2 := by
    let t : ℝ := (69314 / 100000 : ℝ) / 65536
    let u : ℝ := (69314 / 100000 : ℝ) / 256
    have ht : Real.exp t < (1.000010576589 : ℝ) := by
      calc
        Real.exp t ≤ 1 / (1 - t) :=
          Real.exp_bound_div_one_sub_of_interval (by norm_num [t]) (by norm_num [t])
        _ < (1.000010576589 : ℝ) := by norm_num [t]
    have hmid : Real.exp u < (1.002711265 : ℝ) := by
      calc
        Real.exp u = (Real.exp t) ^ 256 := by
          rw [show u = (256 : ℝ) * t by norm_num [u, t]]
          exact exp_nat_mul_local t 256
        _ ≤ (1.000010576589 : ℝ) ^ 256 :=
          pow_le_pow_nonneg_local (le_of_lt (Real.exp_pos t)) (le_of_lt ht) 256
        _ < (1.002711265 : ℝ) := by norm_num
    have hpowLower₁ :
        (1.002711265 : ℝ) ^ 16 < (1.044273616 : ℝ) := by
      set_option maxRecDepth 4096 in
        norm_num
    have hpowLower₂ :
        (1.044273616 : ℝ) ^ 16 < 2 := by
      set_option maxRecDepth 4096 in
        norm_num
    calc
      Real.exp (69314 / 100000 : ℝ) = (Real.exp u) ^ 256 := by
        rw [show (69314 / 100000 : ℝ) = (256 : ℝ) * u by norm_num [u]]
        exact exp_nat_mul_local u 256
      _ ≤ (1.002711265 : ℝ) ^ 256 :=
        pow_le_pow_nonneg_local (le_of_lt (Real.exp_pos u)) (le_of_lt hmid) 256
      _ = ((1.002711265 : ℝ) ^ 16) ^ 16 := by
        rw [show (256 : ℕ) = 16 * 16 by norm_num, pow_mul]
      _ ≤ (1.044273616 : ℝ) ^ 16 :=
        pow_le_pow_nonneg_local
          (pow_nonneg (by norm_num) 16) (le_of_lt hpowLower₁) 16
      _ < 2 := hpowLower₂
  have hexpUpper : 2 < Real.exp (69316 / 100000 : ℝ) := by
    let t : ℝ := (69316 / 100000 : ℝ) / 65536
    let u : ℝ := (69316 / 100000 : ℝ) / 256
    have ht : 1 + t ≤ Real.exp t := by
      simpa [add_comm] using Real.add_one_le_exp t
    have hmid : (1.002711305 : ℝ) < Real.exp u := by
      calc
        (1.002711305 : ℝ) < (1 + t) ^ 256 := by norm_num [t]
        _ ≤ (Real.exp t) ^ 256 :=
          pow_le_pow_nonneg_local (by norm_num [t]) ht 256
        _ = Real.exp u := by
          rw [show u = (256 : ℝ) * t by norm_num [u, t]]
          symm
          exact exp_nat_mul_local t 256
    have hpowUpper₁ :
        (1.04427428 : ℝ) < (1.002711305 : ℝ) ^ 16 := by
      set_option maxRecDepth 4096 in
        norm_num
    have hpowUpper₂ :
        2 < (1.04427428 : ℝ) ^ 16 := by
      set_option maxRecDepth 4096 in
        norm_num
    calc
      2 < (1.04427428 : ℝ) ^ 16 := hpowUpper₂
      _ ≤ ((1.002711305 : ℝ) ^ 16) ^ 16 :=
        pow_le_pow_nonneg_local (by norm_num) (le_of_lt hpowUpper₁) 16
      _ = (1.002711305 : ℝ) ^ 256 := by
        rw [show (256 : ℕ) = 16 * 16 by norm_num, pow_mul]
      _ ≤ (Real.exp u) ^ 256 :=
        pow_le_pow_nonneg_local (by norm_num) (le_of_lt hmid) 256
      _ = Real.exp (69316 / 100000 : ℝ) := by
        rw [show (69316 / 100000 : ℝ) = (256 : ℝ) * u by norm_num [u]]
        symm
        exact exp_nat_mul_local u 256
  have hlogLower : (69314 / 100000 : ℝ) < Real.log 2 := by
    rw [← Real.exp_lt_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact hexpLower
  have hlogUpper : Real.log 2 < (69316 / 100000 : ℝ) := by
    rw [← Real.exp_lt_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact hexpUpper
  unfold Approx
  rw [abs_lt]
  constructor <;> norm_num at hlogLower hlogUpper ⊢ <;> linarith

end

end ProofGap.Exercise3635
