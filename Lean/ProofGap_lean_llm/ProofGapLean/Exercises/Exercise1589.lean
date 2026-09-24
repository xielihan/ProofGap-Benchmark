import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1589

noncomputable section

def denominator (k α : ℝ) := Real.cos α + k * Real.sin α
def force (P k α : ℝ) := k * P / denominator k α
def angleDomain := Set.Ioo (0 : ℝ) (Real.pi / 2)
def optimizer (k : ℝ) := Real.arctan k
def Optimal (P k α : ℝ) : Prop :=
  α ∈ angleDomain ∧ ∀ α₁ ∈ angleDomain, force P k α ≤ force P k α₁

private theorem optimizer_mem_angle (k : ℝ) (hk : 0 < k) :
    optimizer k ∈ angleDomain := by
  change 0 < Real.arctan k ∧ Real.arctan k < Real.pi / 2
  exact ⟨Real.arctan_pos.2 hk, Real.arctan_lt_pi_div_two k⟩

private theorem denominator_pos_of_angle (k α : ℝ) (hk : 0 < k)
    (hα : α ∈ angleDomain) : 0 < denominator k α := by
  change 0 < α ∧ α < Real.pi / 2 at hα
  have hsin : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi hα.1
      (by nlinarith [hα.2, Real.pi_pos])
  have hcos : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo
      ⟨by nlinarith [hα.1, Real.pi_pos], hα.2⟩
  unfold denominator
  nlinarith [mul_pos hk hsin]

private theorem denominator_sq_identity (k α : ℝ) :
    denominator k α ^ 2 +
        (Real.sin α - k * Real.cos α) ^ 2 = 1 + k ^ 2 := by
  unfold denominator
  calc
    (Real.cos α + k * Real.sin α) ^ 2 +
          (Real.sin α - k * Real.cos α) ^ 2 =
        (1 + k ^ 2) * (Real.sin α ^ 2 + Real.cos α ^ 2) := by
      ring
    _ = 1 + k ^ 2 := by
      rw [Real.sin_sq_add_cos_sq]
      ring

private theorem optimizer_denominator (k : ℝ) :
    denominator k (optimizer k) = Real.sqrt (1 + k ^ 2) := by
  have hx : 0 ≤ 1 + k ^ 2 := by nlinarith [sq_nonneg k]
  have hspos : 0 < Real.sqrt (1 + k ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith [sq_nonneg k])
  unfold denominator optimizer
  rw [Real.cos_arctan, Real.sin_arctan]
  field_simp [ne_of_gt hspos] <;> nlinarith [Real.sq_sqrt hx]

private theorem denominator_le_sqrt (k α : ℝ) :
    denominator k α ≤ Real.sqrt (1 + k ^ 2) := by
  have hx : 0 ≤ 1 + k ^ 2 := by nlinarith [sq_nonneg k]
  have hs : 0 ≤ Real.sqrt (1 + k ^ 2) := Real.sqrt_nonneg _
  have hid := denominator_sq_identity k α
  by_contra hle
  have hlt : Real.sqrt (1 + k ^ 2) < denominator k α :=
    lt_of_not_ge hle
  have hsum :
      0 < denominator k α + Real.sqrt (1 + k ^ 2) := by
    nlinarith
  have hprod :
      0 < (denominator k α - Real.sqrt (1 + k ^ 2)) *
          (denominator k α + Real.sqrt (1 + k ^ 2)) :=
    mul_pos (sub_pos.2 hlt) hsum
  nlinarith [Real.sq_sqrt hx,
    sq_nonneg (Real.sin α - k * Real.cos α)]

theorem gap1 (P k α : ℝ) (hP : 0 < P) (hk : 0 < k)
    (h : Optimal P k α) :
    force P k α * Real.cos α =
      k * (P - force P k α * Real.sin α) := by
  have hden : 0 < denominator k α :=
    denominator_pos_of_angle k α hk h.1
  have hden' : Real.cos α + k * Real.sin α ≠ 0 := by
    simpa [denominator] using ne_of_gt hden
  unfold force denominator
  field_simp [hden']
  ring
theorem gap2 (P k α : ℝ) :
    force P k α = k * P / denominator k α := by
  rfl
theorem gap3 (P k α : ℝ) (hP : 0 < P) (hk : 0 < k) :
    IsMaxOn (denominator k) angleDomain α →
      IsMinOn (force P k) angleDomain α := by
  intro hmax
  have hoptmem : optimizer k ∈ angleDomain := optimizer_mem_angle k hk
  have hopt_le : denominator k (optimizer k) ≤ denominator k α :=
    hmax hoptmem
  have hoptpos : 0 < denominator k (optimizer k) :=
    denominator_pos_of_angle k (optimizer k) hk hoptmem
  have hαpos : 0 < denominator k α := lt_of_lt_of_le hoptpos hopt_le
  intro y hy
  have hypos : 0 < denominator k y :=
    denominator_pos_of_angle k y hk hy
  have hnum : 0 < k * P := mul_pos hk hP
  unfold force
  exact (div_le_div_iff₀ hαpos hypos).2
    (mul_le_mul_of_nonneg_left (hmax hy) hnum.le)
theorem gap4 (P k α : ℝ) (hP : 0 < P) (hk : 0 < k) :
    IsMaxOn (denominator k) angleDomain α →
      IsMinOn (force P k) angleDomain α := by
  exact gap3 P k α hP hk
theorem gap5 (k α : ℝ) :
    deriv (denominator k) α = -Real.sin α + k * Real.cos α := by
  have hd : HasDerivAt (denominator k)
      (-Real.sin α + k * Real.cos α) α := by
    simpa [denominator] using
      (Real.hasDerivAt_cos α).add
        ((Real.hasDerivAt_sin α).const_mul k)
  exact hd.deriv
theorem gap6 (P k α : ℝ) (hP : 0 < P) (hk : 0 < k)
    (h : Optimal P k α) :
    -Real.sin α + k * Real.cos α = 0 := by
  have hαmem : α ∈ angleDomain := h.1
  have hoptmem : optimizer k ∈ angleDomain := optimizer_mem_angle k hk
  have hαpos : 0 < denominator k α :=
    denominator_pos_of_angle k α hk hαmem
  have hoptpos : 0 < denominator k (optimizer k) :=
    denominator_pos_of_angle k (optimizer k) hk hoptmem
  have hforce := h.2 (optimizer k) hoptmem
  unfold force at hforce
  have hcross :
      k * P * denominator k (optimizer k) ≤ k * P * denominator k α :=
    (div_le_div_iff₀ hαpos hoptpos).1 hforce
  have hnum : 0 < k * P := mul_pos hk hP
  have hden : denominator k (optimizer k) ≤ denominator k α := by
    by_contra hn
    have hlt : denominator k α < denominator k (optimizer k) :=
      lt_of_not_ge hn
    have hmul :
        k * P * denominator k α <
          k * P * denominator k (optimizer k) :=
      mul_lt_mul_of_pos_left hlt hnum
    exact (not_lt_of_ge hcross) hmul
  rw [optimizer_denominator] at hden
  have hupp : denominator k α ≤ Real.sqrt (1 + k ^ 2) :=
    denominator_le_sqrt k α
  have heq : denominator k α = Real.sqrt (1 + k ^ 2) :=
    le_antisymm hupp hden
  have hx : 0 ≤ 1 + k ^ 2 := by nlinarith [sq_nonneg k]
  have hid := denominator_sq_identity k α
  rw [heq] at hid
  have hz : (Real.sin α - k * Real.cos α) ^ 2 = 0 := by
    nlinarith [Real.sq_sqrt hx]
  have hzmul :
      (Real.sin α - k * Real.cos α) *
          (Real.sin α - k * Real.cos α) = 0 := by
    simpa [pow_two] using hz
  have hlin : Real.sin α - k * Real.cos α = 0 :=
    mul_self_eq_zero.mp hzmul
  linarith
theorem gap7 (P k α : ℝ) (hP : 0 < P) (hk : 0 < k)
    (h : Optimal P k α) :
    deriv (denominator k) α = 0 := by
  rw [gap5 k α]
  exact gap6 P k α hP hk h
theorem gap8 (P k α : ℝ) (hP : 0 < P) (hk : 0 < k)
    (h : Optimal P k α) : α = optimizer k := by
  have hαmem : α ∈ angleDomain := h.1
  change 0 < α ∧ α < Real.pi / 2 at hαmem
  have hcos : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo
      ⟨by nlinarith [Real.pi_pos], hαmem.2⟩
  have hsin : Real.sin α = k * Real.cos α := by
    linarith [gap6 P k α hP hk h]
  have htan : Real.tan α = k := by
    rw [Real.tan_eq_sin_div_cos]
    exact (div_eq_iff (ne_of_gt hcos)).2 hsin
  calc
    α = Real.arctan (Real.tan α) :=
      (Real.arctan_tan (by nlinarith [Real.pi_pos]) hαmem.2).symm
    _ = Real.arctan k := by rw [htan]
    _ = optimizer k := rfl
theorem gap9 (k : ℝ) (hk : 0 < k) :
    deriv (deriv (denominator k)) (optimizer k) =
      -Real.cos (optimizer k) - k * Real.sin (optimizer k) := by
  have hfun : deriv (denominator k) =
      fun x => -Real.sin x + k * Real.cos x := by
    funext x
    exact gap5 k x
  rw [hfun]
  have hd :
      HasDerivAt (fun x : ℝ => -Real.sin x + k * Real.cos x)
        (-Real.cos (optimizer k) - k * Real.sin (optimizer k))
        (optimizer k) := by
    convert
      (Real.hasDerivAt_sin (optimizer k)).neg.add
        ((Real.hasDerivAt_cos (optimizer k)).const_mul k) using 1 <;>
      ring
  exact hd.deriv
theorem gap10 (k : ℝ) (hk : 0 < k) :
    -Real.cos (optimizer k) - k * Real.sin (optimizer k) =
      -Real.sqrt (1 + k ^ 2) := by
  calc
    -Real.cos (optimizer k) - k * Real.sin (optimizer k) =
        -denominator k (optimizer k) := by
      unfold denominator
      ring
    _ = -Real.sqrt (1 + k ^ 2) := by
      rw [optimizer_denominator]
theorem gap11 (k : ℝ) (hk : 0 < k) : -Real.sqrt (1 + k ^ 2) < 0 := by
  have hx : 0 < 1 + k ^ 2 := by nlinarith [sq_nonneg k]
  exact neg_lt_zero.mpr (Real.sqrt_pos.2 hx)
theorem gap12 (k : ℝ) (hk : 0 < k) :
    deriv (deriv (denominator k)) (optimizer k) < 0 := by
  rw [gap9 k hk, gap10 k hk]
  exact gap11 k hk
theorem gap13 (k : ℝ) (hk : 0 < k) :
    IsMaxOn (denominator k) angleDomain (optimizer k) := by
  intro y hy
  rw [optimizer_denominator k]
  exact denominator_le_sqrt k y
theorem gap14 (P k : ℝ) (hP : 0 < P) (hk : 0 < k) :
    IsMinOn (force P k) angleDomain (optimizer k) := by
  exact gap3 P k (optimizer k) hP hk (gap13 k hk)
theorem gap15 (P k α : ℝ) (hP : 0 < P) (hk : 0 < k) :
    α = optimizer k ↔ Optimal P k α := by
  constructor
  · intro hα
    subst α
    refine ⟨optimizer_mem_angle k hk, ?_⟩
    intro y hy
    exact gap14 P k hP hk hy
  · intro hopt
    exact gap8 P k α hP hk hopt

end
end ProofGap.Exercise1589
