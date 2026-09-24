import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1922

noncomputable section

def t (a b x : ℝ) := (x + a) / (x + b)
def regularBranch (a b : ℝ) : Set ℝ := {x | x + a ≠ 0 ∧ x + b ≠ 0}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def BranchwisePrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ u : Set ℝ, IsOpen u → IsPreconnected u → u ⊆ s →
    ∃ C : ℝ, ∀ x ∈ u, F x = p x + C}
def integrand (a b : ℝ) (m n : ℕ) (x : ℝ) :=
  1 / ((x + a) ^ m * (x + b) ^ n)
def I (a b : ℝ) (m n : ℕ) :=
  AntiderivativesOn (regularBranch a b) (integrand a b m n)
def transformedIntegrand (a b : ℝ) (m n : ℕ) (x : ℝ) :=
  (1 - t a b x) ^ (m + n - 2) / (t a b x) ^ m * deriv (t a b) x
def TransformedFamily (a b : ℝ) (m n : ℕ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn (regularBranch a b) (transformedIntegrand a b m n),
    ∀ x ∈ regularBranch a b,
      F x = 1 / (b - a) ^ (m + n - 1) * G x}
def coalescedIntegrand (a : ℝ) (m n : ℕ) (x : ℝ) :=
  1 / (x + a) ^ (m + n)
def coalescedPrimitive (a : ℝ) (m n : ℕ) (x : ℝ) :=
  1 / (1 - (m : ℝ) - (n : ℝ)) *
    (x + a) ^ (1 - (m : ℤ) - (n : ℤ))
def tEx (x : ℝ) := (x - 2) / (x + 3)
def exampleBranch : Set ℝ := {x | x - 2 ≠ 0 ∧ x + 3 ≠ 0}
def exampleIntegrand (x : ℝ) := 1 / ((x - 2) ^ 2 * (x + 3) ^ 3)
def exampleTransformed (x : ℝ) :=
  (1 - tEx x) ^ 3 / (tEx x) ^ 2 * deriv tEx x
def exampleExpanded (x : ℝ) :=
  (1 / (tEx x) ^ 2 - 3 / tEx x + 3 - tEx x) * deriv tEx x
def ExampleTransformedFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn exampleBranch exampleTransformed,
    ∀ x ∈ exampleBranch, F x = 1 / (5 : ℝ) ^ 4 * G x}
def ExampleExpandedFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn exampleBranch exampleExpanded,
    ∀ x ∈ exampleBranch, F x = 1 / (5 : ℝ) ^ 4 * G x}
def examplePrimitiveT (x : ℝ) :=
  1 / 625 *
    (-1 / tEx x - 3 * Real.log |tEx x| + 3 * tEx x - (tEx x) ^ 2 / 2)
def examplePrimitiveX (x : ℝ) :=
  1 / 625 *
    (-(x + 3) / (x - 2) - 3 * Real.log |(x - 2) / (x + 3)| +
      3 * (x - 2) / (x + 3) - (x - 2) ^ 2 / (2 * (x + 3) ^ 2))

private theorem regularBranch_isOpen (a b : ℝ) :
    IsOpen (regularBranch a b) := by
  unfold regularBranch
  have ho : IsOpen {y : ℝ | y ≠ 0} := isOpen_ne
  exact (ho.preimage (continuous_id.add continuous_const)).inter
    (ho.preimage (continuous_id.add continuous_const))

private theorem antiderivatives_congr
    {s : Set ℝ} {f g : ℝ → ℝ} (hfg : ∀ x ∈ s, f x = g x) :
    AntiderivativesOn s f = AntiderivativesOn s g := by
  ext F
  constructor <;> intro h <;> intro x hx
  · simpa [hfg x hx] using h x hx
  · simpa [hfg x hx] using h x hx

private theorem antiderivatives_scale
    {s : Set ℝ} (hopen : IsOpen s) (f g : ℝ → ℝ) (k : ℝ) (hk : k ≠ 0)
    (hfg : ∀ x ∈ s, f x = k * g x) :
    AntiderivativesOn s f =
      {F | ∃ G ∈ AntiderivativesOn s g, ∀ x ∈ s, F x = k * G x} := by
  ext F
  constructor
  · intro hF
    refine ⟨fun x => F x / k, ?_, ?_⟩
    · intro x hx
      have h := (hF x hx).div_const k
      convert h using 1
      rw [hfg x hx]
      field_simp [hk]
    · intro x hx
      field_simp [hk]
  · rintro ⟨G, hG, hEq⟩
    intro x hx
    have heq : F =ᶠ[nhds x] fun y => k * G y := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hEq y hy
    have h := (hG x hx).const_mul k
    rw [← hfg x hx] at h
    exact h.congr_of_eventuallyEq heq

private theorem antiderivatives_eq_translates
    {s : Set ℝ} (hopen : IsOpen s) (hs : IsPreconnected s)
    (f p : ℝ → ℝ) (hp : ∀ x ∈ s, HasDerivAt p (f x) x) :
    AntiderivativesOn s f = PrimitiveFamilyOn s p := by
  ext F
  constructor
  · intro hF
    by_cases hne : s.Nonempty
    · rcases hne with ⟨x0, hx0⟩
      have hz : ∀ x ∈ s, HasDerivAt (fun y => F y - p y) 0 x := by
        intro x hx
        simpa using (hF x hx).sub (hp x hx)
      have hdiff : DifferentiableOn ℝ (fun y => F y - p y) s := by
        intro x hx
        exact (hz x hx).differentiableAt.differentiableWithinAt
      have hderiv : ∀ x ∈ s, deriv (fun y => F y - p y) x = 0 := by
        intro x hx
        exact (hz x hx).deriv
      refine ⟨F x0 - p x0, ?_⟩
      intro x hx
      have heq : F x - p x = F x0 - p x0 :=
        hopen.is_const_of_deriv_eq_zero hs hdiff hderiv
          (x := x) (y := x0) hx hx0
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hne ⟨x, hx⟩).elim
  · rintro ⟨C, hC⟩
    intro x hx
    have heq : F =ᶠ[nhds x] fun y => p y + C := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq

private theorem antiderivatives_eq_branchwise
    {s : Set ℝ} (hopen : IsOpen s) (f p : ℝ → ℝ)
    (hp : ∀ x ∈ s, HasDerivAt p (f x) x) :
    AntiderivativesOn s f = BranchwisePrimitiveFamilyOn s p := by
  ext F
  constructor
  · intro hF u huOpen huConn hus
    have heq := antiderivatives_eq_translates huOpen huConn f p
      (fun x hx => hp x (hus hx))
    change F ∈ PrimitiveFamilyOn u p
    rw [← heq]
    exact fun x hx => hF x (hus hx)
  · intro hF x hx
    rcases Metric.isOpen_iff.mp hopen x hx with ⟨ε, hε, hball⟩
    have hconn : IsPreconnected (Metric.ball x ε) :=
      (convex_ball x ε).isPreconnected
    rcases hF (Metric.ball x ε) Metric.isOpen_ball hconn hball with ⟨C, hC⟩
    have heq : F =ᶠ[nhds x] fun y => p y + C := by
      filter_upwards [Metric.ball_mem_nhds x hε] with y hy
      exact hC y hy
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq

theorem gap1 (a b x : ℝ) (hx : x + b ≠ 0) :
    1 - t a b x = (b - a) / (x + b) := by
  unfold t
  field_simp [hx]
  ring
theorem gap2 (a b x : ℝ) (hx : x + b ≠ 0) (hab : b ≠ a) :
    x + b = (b - a) / (1 - t a b x) := by
  rw [gap1 a b x hx]
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab
  field_simp [hx, hba]
theorem gap3 (a b x : ℝ) (hx : x + b ≠ 0) :
    HasDerivAt (t a b) ((b - a) / (x + b) ^ 2) x := by
  unfold t
  have h :=
    ((hasDerivAt_id x).add_const a).div
      ((hasDerivAt_id x).add_const b) hx
  convert h using 1 <;> simp only [id_eq] <;> ring
theorem gap4 (a b x : ℝ) (hx : x + b ≠ 0) (hab : b ≠ a) :
    (b - a) / (x + b) ^ 2 = (1 - t a b x) ^ 2 / (b - a) := by
  rw [gap1 a b x hx]
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab
  field_simp [hx, hba]
theorem gap5 (a b x : ℝ) (hx : x + b ≠ 0) (hab : b ≠ a) :
    deriv (t a b) x = (1 - t a b x) ^ 2 / (b - a) := by
  rw [(gap3 a b x hx).deriv, gap4 a b x hx hab]
theorem gap6 (a b x : ℝ) (hx : x + b ≠ 0) (hab : b ≠ a) :
    1 = (b - a) / (1 - t a b x) ^ 2 * deriv (t a b) x := by
  rw [gap5 a b x hx hab]
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab
  have ht : 1 - t a b x ≠ 0 := by
    rw [gap1 a b x hx]
    exact div_ne_zero hba hx
  field_simp [hba, ht]
theorem gap7 (a b x : ℝ) (hx : x + b ≠ 0) :
    x + a = t a b x * (x + b) := by
  unfold t
  field_simp [hx]
theorem gap8 (a b x : ℝ) (hx : x + b ≠ 0) (hab : b ≠ a) :
    t a b x * (x + b) = t a b x * (b - a) / (1 - t a b x) := by
  rw [gap2 a b x hx hab]
  ring
theorem gap9 (a b x : ℝ) (hx : x + b ≠ 0) (hab : b ≠ a) :
    x + a = t a b x * (b - a) / (1 - t a b x) := by
  rw [gap7 a b x hx, gap8 a b x hx hab]
theorem gap10 (a b : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hab : b ≠ a) :
    I a b m n = TransformedFamily a b m n := by
  unfold I TransformedFamily
  apply antiderivatives_scale (regularBranch_isOpen a b)
  · exact one_div_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hab))
  · intro x hx
    have hxa : x + a ≠ 0 := hx.1
    have hxb : x + b ≠ 0 := hx.2
    have hba : b - a ≠ 0 := sub_ne_zero.mpr hab
    have ht : t a b x ≠ 0 := div_ne_zero hxa hxb
    have h1t : 1 - t a b x ≠ 0 := by
      rw [gap1 a b x hxb]
      exact div_ne_zero hba hxb
    unfold integrand transformedIntegrand
    rw [(gap3 a b x hxb).deriv, gap1 a b x hxb]
    unfold t
    rw [show m + n - 1 = (m + n - 2) + 1 by omega, pow_succ]
    simp only [div_pow]
    field_simp [hxa, hxb, hba, ht, h1t]
    rw [← pow_add, ← pow_add]
    congr 1
    omega
theorem gap11 (a b : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hba : b = a) :
    I a b m n =
      AntiderivativesOn (regularBranch a b) (coalescedIntegrand a m n) := by
  subst b
  unfold I
  apply antiderivatives_congr
  intro x hx
  unfold integrand coalescedIntegrand
  rw [← pow_add]
theorem gap12 (a b : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hba : b = a) :
    AntiderivativesOn (regularBranch a b) (coalescedIntegrand a m n) =
      BranchwisePrimitiveFamilyOn (regularBranch a b)
        (coalescedPrimitive a m n) := by
  subst b
  apply antiderivatives_eq_branchwise (regularBranch_isOpen a a)
  intro x hx
  have hxa : x + a ≠ 0 := hx.1
  let p : ℤ := 1 - (m : ℤ) - (n : ℤ)
  have hb : HasDerivAt (fun y : ℝ => y + a) 1 x :=
    (hasDerivAt_id x).add_const a
  have hz :=
    (hasDerivAt_zpow p (x + a) (Or.inl hxa)).comp x hb
  have hraw :=
    hz.const_mul (1 / (1 - (m : ℝ) - (n : ℝ)))
  unfold coalescedPrimitive coalescedIntegrand
  change HasDerivAt
    (fun y => 1 / (1 - (m : ℝ) - (n : ℝ)) *
      (y + a) ^ p)
    (1 / (x + a) ^ (m + n)) x
  convert hraw using 1
  change 1 / (x + a) ^ (m + n) =
    1 / (1 - (m : ℝ) - (n : ℝ)) *
      ((p : ℝ) * (x + a) ^ (p - 1) * 1)
  have hcoef : 1 - (m : ℝ) - (n : ℝ) ≠ 0 := by
    have hmR : 1 ≤ (m : ℝ) := by exact_mod_cast hm
    have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hpCast : (p : ℝ) = 1 - (m : ℝ) - (n : ℝ) := by
    unfold p
    push_cast
    ring
  rw [hpCast]
  rw [show p - 1 = -((m + n : ℕ) : ℤ) by
    unfold p
    push_cast
    ring]
  rw [zpow_neg, zpow_natCast]
  field_simp [hxa, hcoef]
theorem gap13 (a b : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hba : b = a) :
    I a b m n =
      BranchwisePrimitiveFamilyOn (regularBranch a b)
        (coalescedPrimitive a m n) := by
  rw [gap11 a b m n hm hn hba, gap12 a b m n hm hn hba]
theorem gap14 :
    AntiderivativesOn exampleBranch exampleIntegrand = ExampleTransformedFamily := by
  have h :=
    gap10 (-2 : ℝ) 3 2 3 (by norm_num) (by norm_num) (by norm_num)
  unfold I TransformedFamily regularBranch integrand transformedIntegrand t at h
  unfold ExampleTransformedFamily exampleBranch exampleIntegrand
    exampleTransformed tEx
  norm_num at h ⊢
  simpa [sub_eq_add_neg] using h
theorem gap15 :
    ExampleTransformedFamily = ExampleExpandedFamily := by
  have hfun : ∀ x ∈ exampleBranch, exampleTransformed x = exampleExpanded x := by
    intro x hx
    have ht : tEx x ≠ 0 := by
      unfold tEx
      exact div_ne_zero hx.1 hx.2
    unfold exampleTransformed exampleExpanded
    field_simp [ht]
    ring
  have hanti :
      AntiderivativesOn exampleBranch exampleTransformed =
        AntiderivativesOn exampleBranch exampleExpanded :=
    antiderivatives_congr hfun
  unfold ExampleTransformedFamily ExampleExpandedFamily
  rw [hanti]
theorem gap16 :
    AntiderivativesOn exampleBranch exampleIntegrand = ExampleExpandedFamily := by
  rw [gap14, gap15]
theorem gap17 :
    AntiderivativesOn exampleBranch exampleIntegrand =
      BranchwisePrimitiveFamilyOn exampleBranch examplePrimitiveT := by
  apply antiderivatives_eq_branchwise
    (by
      simpa [regularBranch, exampleBranch, sub_eq_add_neg] using
        regularBranch_isOpen (-2 : ℝ) 3)
  intro x hx
  have hxm : x - 2 ≠ 0 := hx.1
  have hxp : x + 3 ≠ 0 := hx.2
  have ht : tEx x ≠ 0 := by
    unfold tEx
    exact div_ne_zero hxm hxp
  have htDeriv :
      HasDerivAt tEx (5 / (x + 3) ^ 2) x := by
    convert gap3 (-2 : ℝ) 3 x hxp using 1 <;>
      norm_num [tEx, t] <;> ring
  have hinv := htDeriv.inv ht
  have hlogRaw := (Real.hasDerivAt_log ht).comp x htDeriv
  have hlog :
      HasDerivAt (fun y => Real.log |tEx y|)
        ((5 / (x + 3) ^ 2) / tEx x) x := by
    simpa only [Function.comp_def, Real.log_abs, one_div, mul_comm,
      div_eq_mul_inv] using hlogRaw
  have hsq := htDeriv.pow 2
  have hraw :=
    ((((hinv.const_mul (-1 : ℝ)).sub
      (hlog.const_mul 3)).add
      (htDeriv.const_mul 3)).sub
      (hsq.div_const 2)).const_mul (1 / 625 : ℝ)
  unfold examplePrimitiveT
  convert hraw using 1
  unfold exampleIntegrand tEx
  norm_num
  field_simp [hxm, hxp]
  ring
theorem gap18 :
    AntiderivativesOn exampleBranch exampleIntegrand =
      BranchwisePrimitiveFamilyOn exampleBranch examplePrimitiveX := by
  rw [gap17]
  ext F
  constructor
  · intro hF u huOpen huConn hus
    rcases hF u huOpen huConn hus with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    have hbranch := hus hx
    have heq : examplePrimitiveT x = examplePrimitiveX x := by
      have hxm : x - 2 ≠ 0 := hbranch.1
      have hxp : x + 3 ≠ 0 := hbranch.2
      unfold examplePrimitiveT examplePrimitiveX tEx
      field_simp [hxm, hxp]
    rw [← heq]
    exact hC x hx
  · intro hF u huOpen huConn hus
    rcases hF u huOpen huConn hus with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    have hbranch := hus hx
    have heq : examplePrimitiveT x = examplePrimitiveX x := by
      have hxm : x - 2 ≠ 0 := hbranch.1
      have hxp : x + 3 ≠ 0 := hbranch.2
      unfold examplePrimitiveT examplePrimitiveX tEx
      field_simp [hxm, hxp]
    rw [heq]
    exact hC x hx

end
end ProofGap.Exercise1922
