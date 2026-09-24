import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1934

noncomputable section

def nthRoot (n : ℕ) (x : ℝ) := Real.rpow x (1 / (n : ℝ))
def xOf (a b : ℝ) (n : ℕ) (t : ℝ) :=
  a + (a - b) / (t ^ n - 1)
def xBranch (a : ℝ) : Set ℝ := {x | x ≠ a}
def parameterBranch (n : ℕ) : Set ℝ := {t | 0 < t ∧ t ^ n ≠ 1}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def BranchwisePrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ u : Set ℝ, IsOpen u → IsPreconnected u → u ⊆ s →
    ∃ C : ℝ, ∀ x ∈ u, F x = p x + C}
def sourceIntegrand (a b : ℝ) (n : ℕ) (x : ℝ) :=
  1 / nthRoot n ((x - a) ^ (n + 1) * (x - b) ^ (n - 1))
def coalescedPrimitive (a x : ℝ) := -1 / (x - a)
def paramSourceIntegrand (a b : ℝ) (n : ℕ) (t : ℝ) :=
  sourceIntegrand a b n (xOf a b n t) * deriv (xOf a b n) t
def ConstantScaledFamily (a b : ℝ) (n : ℕ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn (parameterBranch n) (fun _ => 1),
    ∀ t ∈ parameterBranch n, F t = -(n : ℝ) / (a - b) * G t}
def linearPrimitive (a b : ℝ) (n : ℕ) (t : ℝ) :=
  -(n : ℝ) / (a - b) * t
def rootPrimitive (a b : ℝ) (n : ℕ) (t : ℝ) :=
  -(n : ℝ) / (a - b) *
    nthRoot n ((xOf a b n t - b) / (xOf a b n t - a))

private theorem nthRoot_pow_nat (n : ℕ) (hn : 0 < n) (y : ℝ) (hy : 0 ≤ y) :
    nthRoot n (y ^ n) = y := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  unfold nthRoot
  rw [← Real.rpow_natCast]
  change Real.rpow (Real.rpow y (n : ℝ)) (1 / (n : ℝ)) = y
  calc
    Real.rpow (Real.rpow y (n : ℝ)) (1 / (n : ℝ)) =
        Real.rpow y ((n : ℝ) * (1 / (n : ℝ))) := by
      exact (Real.rpow_mul hy (n : ℝ) (1 / (n : ℝ))).symm
    _ = y := by
      have hmul : (n : ℝ) * (1 / (n : ℝ)) = 1 := by
        field_simp
      rw [hmul]
      change y ^ (1 : ℝ) = y
      exact Real.rpow_one y

private theorem parameterBranch_isOpen (n : ℕ) : IsOpen (parameterBranch n) := by
  change IsOpen ({t : ℝ | 0 < t} ∩ {t : ℝ | t ^ n ≠ 1})
  exact (isOpen_lt continuous_const continuous_id).inter
    ((isClosed_singleton.preimage (continuous_id.pow n)).isOpen_compl)

private theorem parameterBranch_cover (n : ℕ) (hn : 0 < n) :
    ∀ x ∈ parameterBranch n,
      ∃ u : Set ℝ, IsOpen u ∧ IsPreconnected u ∧
        u ⊆ parameterBranch n ∧ x ∈ u := by
  intro x hx
  have hx1 : x ≠ 1 := by
    intro h
    apply hx.2
    simp [h]
  rcases lt_or_gt_of_ne hx1 with hlt | hgt
  · refine ⟨Set.Ioo 0 1, isOpen_Ioo, isPreconnected_Ioo, ?_, ⟨hx.1, hlt⟩⟩
    intro y hy
    refine ⟨hy.1, ?_⟩
    intro heq
    have hroot := nthRoot_pow_nat n hn y (le_of_lt hy.1)
    rw [heq] at hroot
    have hone : nthRoot n 1 = 1 := by simp [nthRoot]
    rw [hone] at hroot
    exact (ne_of_lt hy.2) hroot.symm
  · refine ⟨Set.Ioi 1, isOpen_Ioi, isPreconnected_Ioi, ?_, hgt⟩
    intro y hy
    refine ⟨lt_trans (by norm_num) hy, ?_⟩
    intro heq
    have hroot := nthRoot_pow_nat n hn y (le_of_lt (lt_trans (by norm_num) hy))
    rw [heq] at hroot
    have hone : nthRoot n 1 = 1 := by simp [nthRoot]
    rw [hone] at hroot
    exact (ne_of_gt hy) hroot.symm

private theorem antiderivatives_eq_branchwise
    (s : Set ℝ) (hsOpen : IsOpen s)
    (hcover : ∀ x ∈ s,
      ∃ u : Set ℝ, IsOpen u ∧ IsPreconnected u ∧ u ⊆ s ∧ x ∈ u)
    (f p : ℝ → ℝ)
    (hp : ∀ x ∈ s, HasDerivAt p (f x) x) :
    AntiderivativesOn s f = BranchwisePrimitiveFamilyOn s p := by
  ext F
  constructor
  · intro hF u huOpen huConn huSub
    by_cases huEmpty : u = ∅
    · subst u
      exact ⟨0, by simp⟩
    · obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr huEmpty
      refine ⟨F x₀ - p x₀, ?_⟩
      have hzero : ∀ x ∈ u,
          HasDerivAt (fun y => F y - p y) 0 x := by
        intro x hx
        convert (hF x (huSub hx)).sub (hp x (huSub hx)) using 1 <;> ring
      have hdiff : DifferentiableOn ℝ (fun y => F y - p y) u := by
        intro x hx
        exact (hzero x hx).differentiableAt.differentiableWithinAt
      have hderiv : ∀ x ∈ u, deriv (fun y => F y - p y) x = 0 := by
        intro x hx
        exact (hzero x hx).deriv
      intro x hx
      have heq := huOpen.is_const_of_deriv_eq_zero huConn hdiff hderiv hx hx₀
      linarith
  · intro hF x hx
    obtain ⟨u, huOpen, huConn, huSub, hxu⟩ := hcover x hx
    obtain ⟨C, hC⟩ := hF u huOpen huConn huSub
    have hev : F =ᶠ[nhds x] (fun y => p y + C) := by
      filter_upwards [huOpen.mem_nhds hxu] with y hy
      exact hC y hy
    have hpc : HasDerivAt (fun y => p y + C) (f x) x := by
      convert (hp x hx).add (hasDerivAt_const x C) using 1 <;>
        simp only [Pi.add_apply, add_zero]
    exact hpc.congr_of_eventuallyEq hev

private theorem scaled_antiderivatives_eq
    (s : Set ℝ) (hsOpen : IsOpen s) (c : ℝ) (hc : c ≠ 0) :
    {F : ℝ → ℝ | ∃ G ∈ AntiderivativesOn s (fun _ => 1),
      ∀ x ∈ s, F x = c * G x} =
      AntiderivativesOn s (fun _ => c) := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩ x hx
    have hev : F =ᶠ[nhds x] (fun y => c * G y) := by
      filter_upwards [hsOpen.mem_nhds hx] with y hy
      exact hFG y hy
    have hder : HasDerivAt (fun y => c * G y) c x := by
      simpa [mul_comm] using (hG x hx).const_mul c
    exact hder.congr_of_eventuallyEq hev
  · intro hF
    let G : ℝ → ℝ := fun x => F x / c
    refine ⟨G, ?_, ?_⟩
    · intro x hx
      dsimp [G]
      convert (hF x hx).div_const c using 1
      field_simp
    · intro x hx
      dsimp [G]
      field_simp

theorem gap1 (a b x : ℝ) (n : ℕ) (hn : 0 < n) (hab : a = b)
    (hx : x ≠ a) :
    sourceIntegrand a b n x = 1 / (x - a) ^ 2 := by
  subst b
  have hsum : n + 1 + (n - 1) = 2 * n := by omega
  have hpow :
      (x - a) ^ (n + 1) * (x - a) ^ (n - 1) =
        ((x - a) ^ 2) ^ n := by
    rw [← pow_add, hsum, pow_mul]
  rw [sourceIntegrand, hpow,
    nthRoot_pow_nat n hn ((x - a) ^ 2) (sq_nonneg (x - a))]
theorem gap2 (a b : ℝ) (n : ℕ) (hn : 0 < n) (hab : a = b) :
    AntiderivativesOn (xBranch a) (sourceIntegrand a b n) =
      BranchwisePrimitiveFamilyOn (xBranch a) (coalescedPrimitive a) := by
  have hopen : IsOpen (xBranch a) := by
    rw [xBranch]
    exact isOpen_ne
  have hcover : ∀ x ∈ xBranch a,
      ∃ u : Set ℝ, IsOpen u ∧ IsPreconnected u ∧ u ⊆ xBranch a ∧ x ∈ u := by
    intro x hx
    have hxa : x ≠ a := hx
    rcases lt_or_gt_of_ne hxa with hlt | hgt
    · refine ⟨Set.Iio a, isOpen_Iio, isPreconnected_Iio, ?_, hlt⟩
      intro y hy
      exact ne_of_lt hy
    · refine ⟨Set.Ioi a, isOpen_Ioi, isPreconnected_Ioi, ?_, hgt⟩
      intro y hy
      exact ne_of_gt hy
  apply antiderivatives_eq_branchwise (xBranch a) hopen hcover
  intro x hx
  have hsrc := gap1 a b x n hn hab hx
  have hder := (((hasDerivAt_id x).sub_const a).inv
    (sub_ne_zero.mpr hx)).neg
  have hfun : coalescedPrimitive a =
      -(fun y : ℝ => y - a)⁻¹ := by
    funext y
    simp [coalescedPrimitive, div_eq_mul_inv]
  rw [hsrc, hfun]
  have hcoef :
      -(-1 / (x - a) ^ 2) = 1 / (x - a) ^ 2 := by
    ring
  rw [← hcoef]
  exact hder
theorem gap3 (a b : ℝ) (n : ℕ) (hn : 0 < n) (hab : a ≠ b)
    (t : ℝ) (ht : t ∈ parameterBranch n) :
    xOf a b n t = a + (a - b) / (t ^ n - 1) := by
  rfl
theorem gap4 (a b : ℝ) (n : ℕ) (hn : 0 < n) (hab : a ≠ b)
    (t : ℝ) (ht : t ∈ parameterBranch n) :
    HasDerivAt (xOf a b n)
      (-(n : ℝ) * (a - b) * t ^ (n - 1) / (t ^ n - 1) ^ 2) t := by
  have hden : t ^ n - 1 ≠ 0 := sub_ne_zero.mpr ht.2
  have hquot := (hasDerivAt_const t (a - b)).div
    (((hasDerivAt_id t).pow n).sub_const 1) hden
  have h := hquot.const_add a
  convert h using 1 <;> simp [xOf] <;> field_simp [hden] <;> ring
theorem gap5 (a b : ℝ) (n : ℕ) (hn : 0 < n) (hab : a ≠ b)
    (t : ℝ) (ht : t ∈ parameterBranch n) :
    xOf a b n t - a = (a - b) / (t ^ n - 1) := by
  rw [gap3 a b n hn hab t ht]
  ring
theorem gap6 (a b : ℝ) (n : ℕ) (hn : 0 < n) (hab : a ≠ b)
    (t : ℝ) (ht : t ∈ parameterBranch n) :
    xOf a b n t - b = (a - b) * t ^ n / (t ^ n - 1) := by
  have hden : t ^ n - 1 ≠ 0 := sub_ne_zero.mpr ht.2
  rw [gap3 a b n hn hab t ht]
  field_simp [hden]
  ring
theorem gap7 (a b : ℝ) (n : ℕ) (hn : 0 < n) (hab : a ≠ b) :
    AntiderivativesOn (parameterBranch n) (paramSourceIntegrand a b n) =
      ConstantScaledFamily a b n := by
  let c : ℝ := -(n : ℝ) / (a - b)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hd0 : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hc0 : c ≠ 0 := div_ne_zero (neg_ne_zero.mpr hn0) hd0
  have hopen := parameterBranch_isOpen n
  have hpoint : ∀ t ∈ parameterBranch n,
      paramSourceIntegrand a b n t = c := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    have hden : t ^ n - 1 ≠ 0 := sub_ne_zero.mpr ht.2
    have hsum : n + 1 + (n - 1) = 2 * n := by omega
    have hdPow :
        (a - b) ^ (n + 1) * (a - b) ^ (n - 1) =
          ((a - b) ^ 2) ^ n := by
      rw [← pow_add, hsum, pow_mul]
    have htPow : (t ^ n) ^ (n - 1) = (t ^ (n - 1)) ^ n := by
      calc
        (t ^ n) ^ (n - 1) = t ^ (n * (n - 1)) := by rw [pow_mul]
        _ = t ^ ((n - 1) * n) := by rw [Nat.mul_comm n (n - 1)]
        _ = (t ^ (n - 1)) ^ n := by rw [pow_mul]
    have hnum :
        (a - b) ^ (n + 1) * ((a - b) * t ^ n) ^ (n - 1) =
          ((a - b) ^ 2 * t ^ (n - 1)) ^ n := by
      calc
        (a - b) ^ (n + 1) * ((a - b) * t ^ n) ^ (n - 1) =
            ((a - b) ^ (n + 1) * (a - b) ^ (n - 1)) *
              (t ^ n) ^ (n - 1) := by
                rw [mul_pow]
                ring
        _ = ((a - b) ^ 2) ^ n * (t ^ (n - 1)) ^ n := by
          rw [hdPow, htPow]
        _ = ((a - b) ^ 2 * t ^ (n - 1)) ^ n := by
          rw [mul_pow]
    have hdenPow :
        (t ^ n - 1) ^ (n + 1) * (t ^ n - 1) ^ (n - 1) =
          ((t ^ n - 1) ^ 2) ^ n := by
      rw [← pow_add, hsum, pow_mul]
    have hrad :
        (xOf a b n t - a) ^ (n + 1) *
            (xOf a b n t - b) ^ (n - 1) =
          (((a - b) ^ 2 * t ^ (n - 1) /
              (t ^ n - 1) ^ 2) ^ n) := by
      rw [gap5 a b n hn hab t ht, gap6 a b n hn hab t ht]
      calc
        ((a - b) / (t ^ n - 1)) ^ (n + 1) *
            ((a - b) * t ^ n / (t ^ n - 1)) ^ (n - 1) =
          ((a - b) ^ (n + 1) * ((a - b) * t ^ n) ^ (n - 1)) /
            ((t ^ n - 1) ^ (n + 1) * (t ^ n - 1) ^ (n - 1)) := by
              rw [div_pow, div_pow]
              field_simp [hden]
        _ = (((a - b) ^ 2 * t ^ (n - 1)) ^ n) /
            (((t ^ n - 1) ^ 2) ^ n) := by
              rw [hnum, hdenPow]
        _ = (((a - b) ^ 2 * t ^ (n - 1) /
            (t ^ n - 1) ^ 2) ^ n) := by
              rw [div_pow]
    have htPowNonneg : 0 ≤ t ^ (n - 1) :=
      pow_nonneg (le_of_lt ht.1) _
    have hdenSqNonneg : 0 ≤ (t ^ n - 1) ^ 2 := sq_nonneg _
    have hy : 0 ≤ (a - b) ^ 2 * t ^ (n - 1) / (t ^ n - 1) ^ 2 :=
      div_nonneg (mul_nonneg (sq_nonneg (a - b)) htPowNonneg) hdenSqNonneg
    have hdx := gap4 a b n hn hab t ht
    have hderiv := hdx.deriv
    rw [paramSourceIntegrand, sourceIntegrand, hrad,
      nthRoot_pow_nat n hn
        ((a - b) ^ 2 * t ^ (n - 1) / (t ^ n - 1) ^ 2) hy,
      hderiv]
    dsimp [c]
    field_simp [hd0, ht0, hden]
  calc
    AntiderivativesOn (parameterBranch n) (paramSourceIntegrand a b n) =
        AntiderivativesOn (parameterBranch n) (fun _ => c) := by
      ext F
      constructor
      · intro hF x hx
        simpa [hpoint x hx] using hF x hx
      · intro hF x hx
        simpa [hpoint x hx] using hF x hx
    _ = ConstantScaledFamily a b n := by
      simpa [ConstantScaledFamily, c] using
        (scaled_antiderivatives_eq (parameterBranch n) hopen c hc0).symm
theorem gap8 (a b : ℝ) (n : ℕ) (hn : 0 < n) (hab : a ≠ b) :
    ConstantScaledFamily a b n =
      BranchwisePrimitiveFamilyOn (parameterBranch n)
        (linearPrimitive a b n) := by
  let c : ℝ := -(n : ℝ) / (a - b)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hd0 : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hc0 : c ≠ 0 := div_ne_zero (neg_ne_zero.mpr hn0) hd0
  have hopen := parameterBranch_isOpen n
  have hscaled :
      ConstantScaledFamily a b n =
        AntiderivativesOn (parameterBranch n) (fun _ => c) := by
    simpa [ConstantScaledFamily, c] using
      scaled_antiderivatives_eq (parameterBranch n) hopen c hc0
  rw [hscaled]
  apply antiderivatives_eq_branchwise (parameterBranch n) hopen
    (parameterBranch_cover n hn)
  intro t ht
  have hlin : linearPrimitive a b n = fun y : ℝ => y * c := by
    funext y
    dsimp [linearPrimitive, c]
    ring
  rw [hlin]
  simpa using (hasDerivAt_id t).mul_const c
theorem gap9 (a b : ℝ) (n : ℕ) (hn : 0 < n) (hab : a ≠ b) :
    BranchwisePrimitiveFamilyOn (parameterBranch n) (linearPrimitive a b n) =
      BranchwisePrimitiveFamilyOn (parameterBranch n)
        (rootPrimitive a b n) := by
  have hroot : ∀ t ∈ parameterBranch n,
      rootPrimitive a b n t = linearPrimitive a b n t := by
    intro t ht
    have hden : t ^ n - 1 ≠ 0 := sub_ne_zero.mpr ht.2
    have hratio :
        (xOf a b n t - b) / (xOf a b n t - a) = t ^ n := by
      rw [gap5 a b n hn hab t ht, gap6 a b n hn hab t ht]
      field_simp [hden, sub_ne_zero.mpr hab]
    rw [rootPrimitive, linearPrimitive, hratio,
      nthRoot_pow_nat n hn t (le_of_lt ht.1)]
  ext F
  constructor
  · intro hF u huOpen huConn huSub
    rcases hF u huOpen huConn huSub with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    calc
      F x = linearPrimitive a b n x + C := hC x hx
      _ = rootPrimitive a b n x + C :=
        congrArg (fun z => z + C) (hroot x (huSub hx)).symm
  · intro hF u huOpen huConn huSub
    rcases hF u huOpen huConn huSub with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    calc
      F x = rootPrimitive a b n x + C := hC x hx
      _ = linearPrimitive a b n x + C :=
        congrArg (fun z => z + C) (hroot x (huSub hx))
theorem gap10 (a b : ℝ) (n : ℕ) (hn : 0 < n) (hab : a ≠ b) :
    AntiderivativesOn (parameterBranch n) (paramSourceIntegrand a b n) =
      BranchwisePrimitiveFamilyOn (parameterBranch n)
        (rootPrimitive a b n) := by
  rw [gap7 a b n hn hab, gap8 a b n hn hab, gap9 a b n hn hab]

end
end ProofGap.Exercise1934
