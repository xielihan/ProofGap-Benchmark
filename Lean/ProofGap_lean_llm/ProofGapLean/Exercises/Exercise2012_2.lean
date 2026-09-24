import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2012_2
noncomputable section

def branch : Set ℝ := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ branch, F x = p x + C}
def K (n : ℕ) := Family (fun x => 1 / Real.cos x ^ n)
def Recurrence (n : ℕ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ K (n - 2), ∃ C, ∀ x ∈ branch,
    F x = Real.sin x / (((n - 1 : ℕ) : ℝ) * Real.cos x ^ (n - 1)) +
      ((n - 2 : ℕ) : ℝ) / (n - 1) * G x + C}
def primitive1 (x : ℝ) := Real.log |Real.tan (x / 2 + Real.pi / 4)|
def primitive7 (x : ℝ) :=
  Real.sin x / (6 * Real.cos x ^ 6) +
    5 * Real.sin x / (24 * Real.cos x ^ 4) +
    5 * Real.sin x / (16 * Real.cos x ^ 2) +
    5 / 16 * Real.log |Real.tan (x / 2 + Real.pi / 4)|

private theorem zero_mem_branch : (0 : ℝ) ∈ branch := by
  rw [branch]
  constructor <;> have hp := Real.pi_pos <;> linarith

private theorem cos_ne_zero_of_mem_branch {x : ℝ} (hx : x ∈ branch) :
    Real.cos x ≠ 0 := by
  apply ne_of_gt
  apply Real.cos_pos_of_mem_Ioo
  simpa [branch] using hx

private theorem hasDerivAt_of_eq_on_branch
    {F p : ℝ → ℝ} {x d : ℝ} (hx : x ∈ branch)
    (hEq : ∀ y ∈ branch, F y = p y) (hp : HasDerivAt p d x) :
    HasDerivAt F d x := by
  have hnhds : branch ∈ nhds x := by
    apply isOpen_Ioo.mem_nhds
    simpa [branch] using hx
  have hEv : F =ᶠ[nhds x] p := by
    filter_upwards [hnhds] with y hy
    exact hEq y hy
  exact (hEv.hasDerivAt_iff).2 hp

private theorem exists_const_on_branch {q : ℝ → ℝ}
    (hq : ∀ x ∈ branch, HasDerivAt q 0 x) :
    ∃ C, ∀ x ∈ branch, q x = C := by
  have hdiff : DifferentiableOn ℝ q branch := by
    intro x hx
    exact (hq x hx).differentiableAt.differentiableWithinAt
  have hzero : ∀ x ∈ branch, deriv q x = 0 := by
    intro x hx
    exact (hq x hx).deriv
  have hopen : IsOpen branch := by
    simpa [branch] using isOpen_Ioo
  have hpre : IsPreconnected branch := by
    simpa [branch] using isPreconnected_Ioo
  refine ⟨q 0, ?_⟩
  intro x hx
  exact hopen.is_const_of_deriv_eq_zero hpre hdiff hzero hx zero_mem_branch

private theorem family_eq_translates {f p : ℝ → ℝ}
    (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    Family f = Translates p := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (f x) x at hF
    change ∃ C, ∀ x ∈ branch, F x = p x + C
    have hzero : ∀ x ∈ branch,
        HasDerivAt (fun y => F y - p y) 0 x := by
      intro x hx
      convert (hF x hx).sub (hp x hx) using 1 <;> ring
    obtain ⟨C, hC⟩ := exists_const_on_branch hzero
    refine ⟨C, ?_⟩
    intro x hx
    have h := hC x hx
    linarith
  · rintro ⟨C, hEq⟩
    change ∀ x ∈ branch, HasDerivAt F (f x) x
    intro x hx
    exact hasDerivAt_of_eq_on_branch hx hEq ((hp x hx).add_const C)

private theorem hasDerivAt_reduction_head (n : ℕ) (hn : 2 ≤ n)
    {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt
      (fun y => Real.sin y /
        (((n - 1 : ℕ) : ℝ) * Real.cos y ^ (n - 1)))
      (1 / Real.cos x ^ n -
        ((n - 2 : ℕ) : ℝ) / (n - 1) *
          (1 / Real.cos x ^ (n - 2))) x := by
  have hc : Real.cos x ≠ 0 := cos_ne_zero_of_mem_branch hx
  have hcast1 : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hcast2 : (((n - 2 : ℕ) : ℝ)) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub hn]
    norm_num
  have haC : (((n - 1 : ℕ) : ℝ) ≠ 0) := by
    exact_mod_cast (show n - 1 ≠ 0 by omega)
  have ha : (n : ℝ) - 1 ≠ 0 := by
    rw [← hcast1]
    exact haC
  have hab : (n : ℝ) - 1 = ((n : ℝ) - 2) + 1 := by ring
  have hp1 : Real.cos x ^ (n - 1) =
      Real.cos x ^ (n - 2) * Real.cos x := by
    have he : n - 1 = (n - 2) + 1 := by omega
    calc
      Real.cos x ^ (n - 1) = Real.cos x ^ ((n - 2) + 1) := by rw [he]
      _ = Real.cos x ^ (n - 2) * Real.cos x := by rw [pow_succ]
  have hpn : Real.cos x ^ n =
      Real.cos x ^ (n - 2) * Real.cos x ^ 2 := by
    have he : n = (n - 2) + 2 := by omega
    calc
      Real.cos x ^ n = Real.cos x ^ ((n - 2) + 2) :=
        congrArg (fun k : ℕ => Real.cos x ^ k) he
      _ = Real.cos x ^ (n - 2) * Real.cos x ^ 2 := by rw [pow_add]
  have hpow : HasDerivAt (fun y => Real.cos y ^ (n - 1))
      (-((n - 1 : ℕ) : ℝ) * Real.cos x ^ (n - 2) * Real.sin x) x := by
    convert (Real.hasDerivAt_cos x).pow (n - 1) using 1
    rw [show n - 1 - 1 = n - 2 by omega]
    ring
  have hden : HasDerivAt
      (fun y => ((n - 1 : ℕ) : ℝ) * Real.cos y ^ (n - 1))
      (-(((n - 1 : ℕ) : ℝ) ^ 2) * Real.cos x ^ (n - 2) *
        Real.sin x) x := by
    convert (hasDerivAt_const x ((n - 1 : ℕ) : ℝ)).mul hpow using 1 <;> ring
  have hden_ne :
      ((n - 1 : ℕ) : ℝ) * Real.cos x ^ (n - 1) ≠ 0 :=
    mul_ne_zero haC (pow_ne_zero _ hc)
  have hquot := (Real.hasDerivAt_sin x).div hden hden_ne
  convert hquot using 1
  have htrig : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [hcast1, hcast2, hpn, hp1]
  field_simp [ha, hc]
  rw [hab]
  ring_nf
  rw [htrig]
  ring

private theorem hasDerivAt_reduction (n : ℕ) (hn : 2 ≤ n)
    {G : ℝ → ℝ} {x : ℝ}
    (hG : HasDerivAt G (1 / Real.cos x ^ (n - 2)) x)
    (hx : x ∈ branch) :
    HasDerivAt
      (fun y => Real.sin y /
          (((n - 1 : ℕ) : ℝ) * Real.cos y ^ (n - 1)) +
        ((n - 2 : ℕ) : ℝ) / (n - 1) * G y)
      (1 / Real.cos x ^ n) x := by
  have hhead := hasDerivAt_reduction_head n hn hx
  have htail := hG.const_mul (((n - 2 : ℕ) : ℝ) / (n - 1))
  convert hhead.add htail using 1 <;> ring_nf

private theorem tan_half_shift_pos {x : ℝ} (hx : x ∈ branch) :
    0 < Real.tan (x / 2 + Real.pi / 4) := by
  have hx' : -(Real.pi / 2) < x ∧ x < Real.pi / 2 := by
    simpa [branch] using hx
  have hp := Real.pi_pos
  have hu0 : 0 < x / 2 + Real.pi / 4 := by linarith
  have hult : x / 2 + Real.pi / 4 < Real.pi / 2 := by linarith
  have hupi : x / 2 + Real.pi / 4 < Real.pi := by linarith
  have hs : 0 < Real.sin (x / 2 + Real.pi / 4) :=
    Real.sin_pos_of_pos_of_lt_pi hu0 hupi
  have hc : 0 < Real.cos (x / 2 + Real.pi / 4) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith
  rw [Real.tan_eq_sin_div_cos]
  exact div_pos hs hc

private theorem hasDerivAt_primitive1 :
    ∀ x ∈ branch, HasDerivAt primitive1 (1 / Real.cos x) x := by
  intro x hx
  let u : ℝ := x / 2 + Real.pi / 4
  have hp := Real.pi_pos
  have hx' : -(Real.pi / 2) < x ∧ x < Real.pi / 2 := by
    simpa [branch] using hx
  have hu0 : 0 < u := by
    dsimp [u]
    linarith
  have hult : u < Real.pi / 2 := by
    dsimp [u]
    linarith
  have hupi : u < Real.pi := by linarith
  have hs : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu0 hupi
  have hc : 0 < Real.cos u := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith
  have ht : 0 < Real.tan u := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hs hc
  have huDeriv : HasDerivAt (fun y => y / 2 + Real.pi / 4) (1 / 2) x := by
    simpa [div_eq_mul_inv, mul_comm] using
      (((hasDerivAt_id x).const_mul (2⁻¹ : ℝ)).add_const (Real.pi / 4))
  have htan := (Real.hasDerivAt_tan hc.ne').comp x huDeriv
  have hlog := (Real.hasDerivAt_log ht.ne').comp x htan
  have hcosx : Real.cos x = 2 * Real.sin u * Real.cos u := by
    have hang : 2 * u = x + Real.pi / 2 := by
      dsimp [u]
      ring
    calc
      Real.cos x = Real.sin (x + Real.pi / 2) := by
        rw [Real.sin_add]
        simp
      _ = Real.sin (2 * u) := by rw [hang]
      _ = 2 * Real.sin u * Real.cos u := by rw [Real.sin_two_mul]
  have hlog' : HasDerivAt
      (fun y => Real.log (Real.tan (y / 2 + Real.pi / 4)))
      (1 / Real.cos x) x := by
    convert hlog using 1
    dsimp [u] at hs hc ht hcosx ⊢
    rw [Real.tan_eq_sin_div_cos, hcosx]
    field_simp [hs.ne', hc.ne']
  apply hasDerivAt_of_eq_on_branch hx ?_ hlog'
  intro y hy
  rw [primitive1, abs_of_pos (tan_half_shift_pos hy)]

private theorem hasDerivAt_primitive7 :
    ∀ x ∈ branch, HasDerivAt primitive7 (1 / Real.cos x ^ 7) x := by
  intro x hx
  have h1 := hasDerivAt_primitive1 x hx
  have h1' : HasDerivAt primitive1 (1 / Real.cos x ^ (3 - 2)) x := by
    norm_num
    simpa using h1
  have h3 := hasDerivAt_reduction 3 (by omega) h1' hx
  have h5 := hasDerivAt_reduction 5 (by omega) h3 hx
  have h7 := hasDerivAt_reduction 7 (by omega) h5 hx
  convert h7 using 1
  funext y
  dsimp [primitive7, primitive1]
  ring

theorem gap1 (n : ℕ) : K n = Family (fun x => 1 / Real.cos x ^ n) := by
  rfl
theorem gap2 (n : ℕ) : K n = Family (fun x =>
    (Real.sin x ^ 2 + Real.cos x ^ 2) / Real.cos x ^ n) := by
  unfold K Family
  ext F
  constructor
  · intro h x hx
    simpa [Real.sin_sq_add_cos_sq] using h x hx
  · intro h x hx
    simpa [Real.sin_sq_add_cos_sq] using h x hx
theorem gap3 (n : ℕ) : K n = Family (fun x =>
    (Real.sin x ^ 2 + Real.cos x ^ 2) / Real.cos x ^ n) := by
  exact gap2 n
theorem gap4 (n : ℕ) (hn : 2 ≤ n) : K n = Recurrence n := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (1 / Real.cos x ^ n) x at hF
    change ∃ G ∈ K (n - 2), ∃ C, ∀ x ∈ branch,
      F x = Real.sin x / (((n - 1 : ℕ) : ℝ) * Real.cos x ^ (n - 1)) +
        ((n - 2 : ℕ) : ℝ) / (n - 1) * G x + C
    by_cases hn2 : n = 2
    · subst n
      refine ⟨fun x : ℝ => x, ?_, ?_⟩
      · change ∀ x ∈ branch,
          HasDerivAt (fun y : ℝ => y) (1 / Real.cos x ^ (2 - 2)) x
        intro x hx
        simpa using hasDerivAt_id x
      · let A : ℝ → ℝ := fun y =>
          Real.sin y / ((((2 - 1 : ℕ) : ℝ)) * Real.cos y ^ (2 - 1))
        have hzero : ∀ x ∈ branch, HasDerivAt (fun y => F y - A y) 0 x := by
          intro x hx
          have hA := hasDerivAt_reduction_head 2 (by omega) hx
          convert (hF x hx).sub hA using 1 <;> simp [A] <;> ring
        obtain ⟨C, hC⟩ := exists_const_on_branch hzero
        refine ⟨C, ?_⟩
        intro x hx
        have heq := hC x hx
        dsimp [A] at heq
        norm_num at heq ⊢
        linarith
    · have hn3 : 3 ≤ n := by omega
      have hcast1 : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]
        norm_num
      have hcast2 : (((n - 2 : ℕ) : ℝ)) = (n : ℝ) - 2 := by
        rw [Nat.cast_sub hn]
        norm_num
      have ha : (n : ℝ) - 1 ≠ 0 := by
        rw [← hcast1]
        exact_mod_cast (show n - 1 ≠ 0 by omega)
      have hb : (n : ℝ) - 2 ≠ 0 := by
        rw [← hcast2]
        exact_mod_cast (show n - 2 ≠ 0 by omega)
      let A : ℝ → ℝ := fun y =>
        Real.sin y / (((n - 1 : ℕ) : ℝ) * Real.cos y ^ (n - 1))
      let d : ℝ := (n - 1) / (n - 2)
      let G : ℝ → ℝ := fun y => d * (F y - A y)
      refine ⟨G, ?_, 0, ?_⟩
      · change ∀ x ∈ branch,
          HasDerivAt G (1 / Real.cos x ^ (n - 2)) x
        intro x hx
        have hc := cos_ne_zero_of_mem_branch hx
        have hA := hasDerivAt_reduction_head n hn hx
        have hsub := (hF x hx).sub hA
        have hscaled := hsub.const_mul d
        convert hscaled using 1
        dsimp [d]
        rw [hcast2]
        field_simp [ha, hb, hc] <;> ring
      · intro x hx
        have hc := cos_ne_zero_of_mem_branch hx
        dsimp [G, d, A]
        rw [hcast1, hcast2]
        field_simp [ha, hb, hc] <;> ring
  · intro hR
    rcases hR with ⟨G, hG, C, hEq⟩
    change ∀ x ∈ branch, HasDerivAt G (1 / Real.cos x ^ (n - 2)) x at hG
    change ∀ x ∈ branch, HasDerivAt F (1 / Real.cos x ^ n) x
    intro x hx
    have hred := hasDerivAt_reduction n hn (hG x hx) hx
    have hredC := hred.add_const C
    apply hasDerivAt_of_eq_on_branch hx hEq hredC
theorem gap5 (n : ℕ) (hn : 2 ≤ n) : K n = Recurrence n := by
  exact gap4 n hn
theorem gap6 (n : ℕ) (hn : 2 ≤ n) : K n = Recurrence n := by
  exact gap4 n hn
theorem gap7 : K 1 = Family (fun x => 1 / Real.cos x) := by
  simpa using (gap1 1)
theorem gap8 : Family (fun x => 1 / Real.cos x) = Translates primitive1 := by
  apply family_eq_translates
  exact hasDerivAt_primitive1
theorem gap9 : K 1 = Translates primitive1 := by
  exact gap7.trans gap8
theorem gap10 : K 7 = Family (fun x => 1 / Real.cos x ^ 7) := by
  exact gap1 7
theorem gap11 : K 7 = Translates primitive7 := by
  apply family_eq_translates
  exact hasDerivAt_primitive7
theorem gap12 : K 7 = Translates primitive7 := by
  exact gap11

end
end ProofGap.Exercise2012_2
