import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Analysis.SpecialFunctions.PolynomialExp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1951

noncomputable section

inductive AlgebraicExpr where
  | const (c : ℝ)
  | var
  | add (u v : AlgebraicExpr)
  | mul (u v : AlgebraicExpr)
  | inv (u : AlgebraicExpr)
  | sqrt (u : AlgebraicExpr)

def AlgebraicExpr.eval : AlgebraicExpr → ℝ → ℝ
  | .const c, _ => c
  | .var, x => x
  | .add u v, x => u.eval x + v.eval x
  | .mul u v, x => u.eval x * v.eval x
  | .inv u, x => 1 / u.eval x
  | .sqrt u, x => Real.sqrt (u.eval x)

def q (a b c x : ℝ) := a * x ^ 2 + b * x + c
def numerator (a₁ b₁ c₁ x : ℝ) := a₁ * x ^ 2 + b₁ * x + c₁
def branch (a b c : ℝ) : Set ℝ := {x | 0 < q a b c x}
def integrand (a b c a₁ b₁ c₁ x : ℝ) :=
  numerator a₁ b₁ c₁ x / Real.sqrt (q a b c x)
def AlgebraicIntegrableOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ e : AlgebraicExpr, ∀ x ∈ s, HasDerivAt e.eval (f x) x
def reductionRhs (a b c A B lam x : ℝ) :=
  A * q a b c x + (a * x + b / 2) * (A * x + B) + lam
def ReductionIdentity (a b c a₁ b₁ c₁ A B lam : ℝ) : Prop :=
  ∀ x, numerator a₁ b₁ c₁ x = reductionRhs a b c A B lam x
def criterion (a b c a₁ b₁ c₁ : ℝ) : Prop :=
  a = 0 ∨
    8 * a ^ 2 * c₁ + 3 * a₁ * b ^ 2 =
      4 * a * (a₁ * c + b * b₁)

private def qExpr (a b c : ℝ) : AlgebraicExpr :=
  .add (.add (.mul (.const a) (.mul .var .var))
    (.mul (.const b) .var)) (.const c)

private def polyExpr (A B C : ℝ) : AlgebraicExpr :=
  .add (.add (.mul (.const A) (.mul .var .var))
    (.mul (.const B) .var)) (.const C)

private def cubicExpr (A B C : ℝ) : AlgebraicExpr :=
  .add (.add (.mul (.const A) (.mul (.mul .var .var) .var))
    (.mul (.const B) (.mul .var .var))) (.mul (.const C) .var)

private def linearSqrtExpr (A B a b c : ℝ) : AlgebraicExpr :=
  .mul (.add (.mul (.const A) .var) (.const B)) (.sqrt (qExpr a b c))

private def polySqrtExpr (A B C a b c : ℝ) : AlgebraicExpr :=
  .mul (polyExpr A B C) (.sqrt (qExpr a b c))

private theorem q_hasDerivAt (a b c x : ℝ) :
    HasDerivAt (q a b c) (2 * a * x + b) x := by
  have ha : HasDerivAt (fun y : ℝ => a * y ^ 2) (2 * a * x) x := by
    convert ((hasDerivAt_id x).pow 2).const_mul a using 1 <;>
      simp only [id_eq] <;> ring
  have hb : HasDerivAt (fun y : ℝ => b * y) b x := by
    convert (hasDerivAt_id x).const_mul b using 1 <;> ring
  have hc : HasDerivAt (fun _ : ℝ => c) 0 x := hasDerivAt_const x c
  simpa [q] using HasDerivAt.add (HasDerivAt.add ha hb) hc

private theorem reduction_algebraic
    (a b c a₁ b₁ c₁ A B : ℝ)
    (hred : ReductionIdentity a b c a₁ b₁ c₁ A B 0) :
    AlgebraicIntegrableOn (branch a b c)
      (integrand a b c a₁ b₁ c₁) := by
  refine ⟨linearSqrtExpr A B a b c, ?_⟩
  intro x hx
  have hq : 0 < q a b c x := hx
  have hs : Real.sqrt (q a b c x) ≠ 0 :=
    (Real.sqrt_pos.2 hq).ne'
  have hs2 : (Real.sqrt (q a b c x)) ^ 2 = q a b c x :=
    Real.sq_sqrt hq.le
  have hsder : HasDerivAt (fun y => Real.sqrt (q a b c y))
      ((2 * a * x + b) / (2 * Real.sqrt (q a b c x))) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x
      (q_hasDerivAt a b c x) using 1 <;> ring
  have hlin : HasDerivAt (fun y : ℝ => A * y + B) A x := by
    have hmul : HasDerivAt (fun y : ℝ => A * y) A x := by
      convert (hasDerivAt_id x).const_mul A using 1 <;> ring
    convert HasDerivAt.add hmul (hasDerivAt_const x B) using 1 <;> ring
  have h := hlin.mul hsder
  have hcoef :
      A * Real.sqrt (q a b c x) +
          (A * x + B) *
            ((2 * a * x + b) / (2 * Real.sqrt (q a b c x))) =
        integrand a b c a₁ b₁ c₁ x := by
    unfold integrand
    have hident := hred x
    unfold reductionRhs at hident
    rw [add_zero] at hident
    rw [hident]
    field_simp [hs]
    rw [hs2]
    ring
  have h' := h.congr_deriv hcoef
  apply h'.congr_of_eventuallyEq
  filter_upwards [] with y
  simp only [linearSqrtExpr, qExpr, AlgebraicExpr.eval]
  simp only [Pi.mul_apply]
  unfold q
  ring

open Filter Topology

local instance algRH : Algebra ℝ ℝ* :=
  Hyperreal.coeRingHom.toRingHom.toAlgebra

private def hseq (f : ℕ → ℝ) : ℝ* := Hyperreal.ofSeq f

private abbrev SeqBase (x : ℕ → ℝ) :=
  IntermediateField.adjoin ℝ
    (Set.range (fun _ : Unit => hseq x))

private def algAt (x : ℕ → ℝ) (z : ℝ*) : Prop :=
  @IsAlgebraic (SeqBase x) ℝ* inferInstance inferInstance
    (IntermediateField.toAlgebra (SeqBase x)) z

private lemma hseq_const (c : ℝ) :
    hseq (fun _ => c) = (c : ℝ*) := by
  rfl

private lemma hseq_add (f g : ℕ → ℝ) :
    hseq (fun n => f n + g n) = hseq f + hseq g := by
  rfl

private lemma hseq_mul (f g : ℕ → ℝ) :
    hseq (fun n => f n * g n) = hseq f * hseq g := by
  rfl

private lemma hseq_inv (f : ℕ → ℝ) :
    hseq (fun n => (f n)⁻¹) = (hseq f)⁻¹ := by
  rfl

private def evalSeq (x : ℕ → ℝ) (e : AlgebraicExpr) : ℝ* :=
  hseq (fun n => e.eval (x n))

private lemma evalSeq_const (x : ℕ → ℝ) (c : ℝ) :
    evalSeq x (.const c) = (c : ℝ*) := by
  rfl

private lemma evalSeq_var (x : ℕ → ℝ) :
    evalSeq x .var = hseq x := by
  rfl

private lemma evalSeq_add (x : ℕ → ℝ) (u v : AlgebraicExpr) :
    evalSeq x (.add u v) = evalSeq x u + evalSeq x v := by
  rfl

private lemma evalSeq_mul (x : ℕ → ℝ) (u v : AlgebraicExpr) :
    evalSeq x (.mul u v) = evalSeq x u * evalSeq x v := by
  rfl

private lemma evalSeq_inv (x : ℕ → ℝ) (u : AlgebraicExpr) :
    evalSeq x (.inv u) = (evalSeq x u)⁻¹ := by
  simpa [evalSeq, AlgebraicExpr.eval, one_div] using
    (hseq_inv (fun n => u.eval (x n)))

private lemma evalSeq_sqrt_sq_of_nonneg (x : ℕ → ℝ) (u : AlgebraicExpr)
    (hu : 0 ≤ evalSeq x u) :
    evalSeq x (.sqrt u) ^ 2 = evalSeq x u := by
  apply Filter.Germ.coe_eq.mpr
  have heu : ∀ᶠ n in Filter.hyperfilter ℕ, 0 ≤ u.eval (x n) := by
    exact Hyperreal.ofSeq_le_ofSeq.mp hu
  filter_upwards [heu] with n hn
  exact Real.sq_sqrt hn

private lemma evalSeq_sqrt_eq_zero_of_nonpos (x : ℕ → ℝ) (u : AlgebraicExpr)
    (hu : evalSeq x u ≤ 0) :
    evalSeq x (.sqrt u) = 0 := by
  apply Filter.Germ.coe_eq.mpr
  have heu : ∀ᶠ n in Filter.hyperfilter ℕ, u.eval (x n) ≤ 0 := by
    exact Hyperreal.ofSeq_le_ofSeq.mp hu
  filter_upwards [heu] with n hn
  exact Real.sqrt_eq_zero_of_nonpos hn

private lemma evalSeq_isAlgebraic (x : ℕ → ℝ) (e : AlgebraicExpr) :
    algAt x (evalSeq x e) := by
  letI algK : Algebra (SeqBase x) ℝ* :=
    IntermediateField.toAlgebra (SeqBase x)
  show @IsAlgebraic (SeqBase x) ℝ* inferInstance inferInstance algK
    (evalSeq x e)
  induction e with
  | const c =>
      rw [evalSeq_const]
      exact @isAlgebraic_algebraMap (SeqBase x) ℝ*
        inferInstance inferInstance algK inferInstance
        ⟨c, (SeqBase x).algebraMap_mem c⟩
  | var =>
      rw [evalSeq_var]
      let xK : SeqBase x :=
        ⟨hseq x, IntermediateField.subset_adjoin ℝ
          (Set.range (fun _ : Unit => hseq x))
          (Set.mem_range_self ())⟩
      refine ⟨Polynomial.X - Polynomial.C xK,
        Polynomial.X_sub_C_ne_zero xK, ?_⟩
      simp only [Polynomial.aeval_def, Polynomial.eval₂_sub,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      change hseq x - (xK : ℝ*) = 0
      simp [xK]
  | add u v hu hv =>
      rw [evalSeq_add]
      exact @IsAlgebraic.add (SeqBase x) ℝ*
        inferInstance inferInstance algK inferInstance _ _ hu hv
  | mul u v hu hv =>
      rw [evalSeq_mul]
      exact @IsAlgebraic.mul (SeqBase x) ℝ*
        inferInstance inferInstance algK inferInstance _ _ hu hv
  | inv u hu =>
      rw [evalSeq_inv]
      exact @IsAlgebraic.inv (SeqBase x) inferInstance ℝ*
        inferInstance algK _ hu
  | sqrt u hu =>
      by_cases hnonneg : 0 ≤ evalSeq x u
      · apply @IsAlgebraic.of_pow (SeqBase x) ℝ*
          inferInstance inferInstance algK _ 2 (by norm_num)
        rw [evalSeq_sqrt_sq_of_nonneg x u hnonneg]
        exact hu
      · have hnonpos : evalSeq x u ≤ 0 := le_of_lt (lt_of_not_ge hnonneg)
        rw [evalSeq_sqrt_eq_zero_of_nonpos x u hnonpos]
        exact @isAlgebraic_zero (SeqBase x) ℝ*
          inferInstance inferInstance algK inferInstance

private lemma evalSeq_isAlgebraic_of_var
    (K : IntermediateField ℝ ℝ*) (x : ℕ → ℝ)
    (hx :
      @IsAlgebraic K ℝ* inferInstance inferInstance
        (IntermediateField.toAlgebra K) (hseq x))
    (e : AlgebraicExpr) :
    @IsAlgebraic K ℝ* inferInstance inferInstance
      (IntermediateField.toAlgebra K) (evalSeq x e) := by
  letI algK : Algebra K ℝ* := IntermediateField.toAlgebra K
  show @IsAlgebraic K ℝ* inferInstance inferInstance algK
    (evalSeq x e)
  induction e with
  | const c =>
      rw [evalSeq_const]
      exact @isAlgebraic_algebraMap K ℝ*
        inferInstance inferInstance algK inferInstance
        ⟨c, K.algebraMap_mem c⟩
  | var =>
      simpa [evalSeq_var] using hx
  | add u v hu hv =>
      rw [evalSeq_add]
      exact @IsAlgebraic.add K ℝ*
        inferInstance inferInstance algK inferInstance _ _ hu hv
  | mul u v hu hv =>
      rw [evalSeq_mul]
      exact @IsAlgebraic.mul K ℝ*
        inferInstance inferInstance algK inferInstance _ _ hu hv
  | inv u hu =>
      rw [evalSeq_inv]
      exact @IsAlgebraic.inv K inferInstance ℝ*
        inferInstance algK _ hu
  | sqrt u hu =>
      by_cases hnonneg : 0 ≤ evalSeq x u
      · apply @IsAlgebraic.of_pow K ℝ*
          inferInstance inferInstance algK _ 2 (by norm_num)
        rw [evalSeq_sqrt_sq_of_nonneg x u hnonneg]
        exact hu
      · have hnonpos : evalSeq x u ≤ 0 :=
          le_of_lt (lt_of_not_ge hnonneg)
        rw [evalSeq_sqrt_eq_zero_of_nonpos x u hnonpos]
        exact @isAlgebraic_zero K ℝ*
          inferInstance inferInstance algK inferInstance

private def tSeq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private lemma hyperreal_const_isAlgebraic
    (K : IntermediateField ℝ ℝ*) (c : ℝ) :
    @IsAlgebraic K ℝ* inferInstance inferInstance
      (IntermediateField.toAlgebra K) (c : ℝ*) := by
  letI algK : Algebra K ℝ* := IntermediateField.toAlgebra K
  exact @isAlgebraic_algebraMap K ℝ*
    inferInstance inferInstance algK inferInstance
    ⟨c, K.algebraMap_mem c⟩

private lemma algAt_tSeq_of_eventually_eval_linear
    (z x : ℕ → ℝ) (r : AlgebraicExpr) (k C : ℝ)
    (hx : algAt z (hseq x)) (hk : k ≠ 0)
    (hev : ∀ᶠ n in Filter.hyperfilter ℕ,
      r.eval (x n) = k * tSeq n + C) :
    algAt z (hseq tSeq) := by
  let K := SeqBase z
  letI algK : Algebra K ℝ* := IntermediateField.toAlgebra K
  have hx' :
      @IsAlgebraic K ℝ* inferInstance inferInstance algK (hseq x) := by
    simpa [algAt, K] using hx
  have hr :
      @IsAlgebraic K ℝ* inferInstance inferInstance algK
        (evalSeq x r) :=
    evalSeq_isAlgebraic_of_var K x hx' r
  have heq :
      evalSeq x r =
        (k : ℝ*) * hseq tSeq + (C : ℝ*) := by
    apply Filter.Germ.coe_eq.mpr
    exact hev
  have hkalg :
      @IsAlgebraic K ℝ* inferInstance inferInstance algK (k : ℝ*) :=
    hyperreal_const_isAlgebraic K k
  have hCalg :
      @IsAlgebraic K ℝ* inferInstance inferInstance algK (C : ℝ*) :=
    hyperreal_const_isAlgebraic K C
  have hnegalg :
      @IsAlgebraic K ℝ* inferInstance inferInstance algK (-1 : ℝ*) :=
    hyperreal_const_isAlgebraic K (-1)
  have hsubalg :
      @IsAlgebraic K ℝ* inferInstance inferInstance algK
        (evalSeq x r + (-1 : ℝ*) * (C : ℝ*)) :=
    @IsAlgebraic.add K ℝ* inferInstance inferInstance algK
      inferInstance _ _
      hr
      (@IsAlgebraic.mul K ℝ* inferInstance inferInstance algK
        inferInstance _ _ hnegalg hCalg)
  have hsolved :
      @IsAlgebraic K ℝ* inferInstance inferInstance algK
        ((k : ℝ*)⁻¹ *
          (evalSeq x r + (-1 : ℝ*) * (C : ℝ*))) :=
    @IsAlgebraic.mul K ℝ* inferInstance inferInstance algK
      inferInstance _ _
      (@IsAlgebraic.inv K inferInstance ℝ* inferInstance algK _
        hkalg)
      hsubalg
  show @IsAlgebraic (SeqBase z) ℝ*
    inferInstance inferInstance
    (IntermediateField.toAlgebra (SeqBase z)) (hseq tSeq)
  convert hsolved using 1
  rw [heq]
  have hk' : (k : ℝ*) ≠ 0 := by exact_mod_cast hk
  field_simp [hk']
  ring

private lemma tSeq_tendsto_punctured :
    Tendsto tSeq (Filter.hyperfilter ℕ) (𝓝[≠] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      (Filter.hyperfilter ℕ) (𝓝 0)
    exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mono_left
      Nat.hyperfilter_le_atTop
  · filter_upwards [] with n
    change tSeq n ≠ 0
    unfold tSeq
    positivity

private lemma analytic_eq_zero_of_hseq_comp_tSeq_eq_zero
    (F : ℝ → ℝ) (hF : ∀ t, AnalyticAt ℝ F t)
    (hz : hseq (fun n => F (tSeq n)) = 0) :
    ∀ t, F t = 0 := by
  have hev : ∀ᶠ n in Filter.hyperfilter ℕ, F (tSeq n) = 0 := by
    exact Filter.Germ.coe_eq.mp hz
  have hfreqSource : ∃ᶠ n in Filter.hyperfilter ℕ, F (tSeq n) = 0 :=
    hev.frequently
  have hfreq : ∃ᶠ t in 𝓝[≠] (0 : ℝ), F t = 0 :=
    tSeq_tendsto_punctured.frequently_map tSeq
      (fun _ h => h) hfreqSource
  have hAnalyticOn : AnalyticOnNhd ℝ F Set.univ := fun t _ => hF t
  have hall := hAnalyticOn.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ 0) hfreq
  intro t
  exact hall (Set.mem_univ t)

private def hseqAlgHom : (ℕ → ℝ) →ₐ[ℝ] ℝ* where
  toRingHom :=
    Filter.Germ.coeRingHom (Filter.hyperfilter ℕ : Filter ℕ)
  commutes' r := by
    rfl

private lemma aeval_hseq_eq (v : Fin 2 → ℕ → ℝ)
    (p : MvPolynomial (Fin 2) ℝ) :
    MvPolynomial.aeval (fun i => hseq (v i)) p =
      hseq (fun n => MvPolynomial.aeval (fun i => v i n) p) := by
  calc
    MvPolynomial.aeval (fun i => hseq (v i)) p =
        hseqAlgHom (MvPolynomial.aeval v p) := by
          symm
          simpa [hseqAlgHom, hseq] using
            (MvPolynomial.comp_aeval_apply (f := v) hseqAlgHom p)
    _ = hseq (fun n => MvPolynomial.aeval (fun i => v i n) p) := by
      change hseq (MvPolynomial.aeval v p) =
        hseq (fun n => MvPolynomial.aeval (fun i => v i n) p)
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [] with n
      simpa only [Pi.evalRingHom_apply, MvPolynomial.coe_eval₂Hom,
        RingHom.coe_comp, Function.comp_apply, MvPolynomial.aeval_def] using
        (MvPolynomial.map_aeval v
          (Pi.evalRingHom (fun _ : ℕ => ℝ) n) p)

private def curveVars (g : ℝ → ℝ) : Fin 2 → ℕ → ℝ :=
  ![fun n => g (tSeq n), tSeq]

private def curvePair (g : ℝ → ℝ) : Fin 2 → ℝ* :=
  fun i => hseq (curveVars g i)

private lemma curvePair_algebraicIndependent
    (g : ℝ → ℝ) (hg : ∀ t, AnalyticAt ℝ g t)
    (hind : ∀ p : MvPolynomial (Fin 2) ℝ,
      (∀ t, MvPolynomial.aeval ![g t, t] p = 0) → p = 0) :
    AlgebraicIndependent ℝ (curvePair g) := by
  rw [algebraicIndependent_iff]
  intro p hp
  apply hind p
  apply analytic_eq_zero_of_hseq_comp_tSeq_eq_zero
  · intro t
    apply AnalyticAt.aeval_mvPolynomial
    intro i
    fin_cases i
    · simpa using hg t
    · simpa using (analyticAt_id : AnalyticAt ℝ (fun x : ℝ => x) t)
  · have hz' :
        hseq (fun n =>
          MvPolynomial.aeval (fun i => curveVars g i n) p) = 0 := by
      rw [← aeval_hseq_eq (curveVars g) p]
      exact hp
    convert hz' using 1
    congr 1
    funext n
    congr 2
    funext i
    fin_cases i <;> rfl

private def specializeFirst (p : MvPolynomial (Fin 2) ℝ) (x : ℝ) :
    Polynomial ℝ :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.C x, Polynomial.X] p

private lemma eval_specializeFirst (p : MvPolynomial (Fin 2) ℝ)
    (x y : ℝ) :
    Polynomial.eval y (specializeFirst p x) =
      MvPolynomial.eval ![x, y] p := by
  unfold specializeFirst
  change Polynomial.eval y
      (MvPolynomial.eval₂ Polynomial.C
        ![Polynomial.C x, Polynomial.X] p) =
    MvPolynomial.eval ![x, y] p
  rw [MvPolynomial.polynomial_eval_eval₂]
  have hcoeff :
      (Polynomial.evalRingHom y).comp Polynomial.C = RingHom.id ℝ := by
    ext r
    simp
  rw [hcoeff]
  apply MvPolynomial.eval₂_congr
  intro i _ _ _
  fin_cases i <;> simp

private lemma sin_functionally_algebraicIndependent
    (p : MvPolynomial (Fin 2) ℝ)
    (h : ∀ t, MvPolynomial.aeval ![Real.sin t, t] p = 0) :
    p = 0 := by
  have hspecialize : ∀ s, specializeFirst p (Real.sin s) = 0 := by
    intro s
    apply Polynomial.eq_zero_of_infinite_isRoot
    let points : ℕ → ℝ := fun n => s + (n : ℝ) * (2 * Real.pi)
    have hpoints : Function.Injective points := by
      intro m n hmn
      have hcast : (m : ℝ) = (n : ℝ) := by
        dsimp [points] at hmn
        nlinarith [Real.pi_pos]
      exact_mod_cast hcast
    apply (Set.infinite_range_of_injective hpoints).mono
    rintro y ⟨n, rfl⟩
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot]
    rw [eval_specializeFirst]
    have hperiod :
        Real.sin (s + (n : ℝ) * (2 * Real.pi)) = Real.sin s := by
      simpa using Real.sin_add_nat_mul_two_pi s n
    simpa [MvPolynomial.aeval_def, hperiod] using
      h (s + (n : ℝ) * (2 * Real.pi))
  let sets : Fin 2 → Set ℝ := ![Set.range Real.sin, Set.univ]
  apply MvPolynomial.funext_set sets
  · intro i
    fin_cases i
    · exact Real.range_sin_infinite
    · exact Set.infinite_univ
  · intro v hv
    obtain ⟨s, hs⟩ := hv 0 (Set.mem_univ 0)
    have heval := congrArg (Polynomial.eval (v 1)) (hspecialize s)
    rw [eval_specializeFirst] at heval
    have heval' :
        MvPolynomial.eval ![Real.sin s, v 1] p = 0 := by
      simpa using heval
    have hvEq : v = ![Real.sin s, v 1] := by
      funext i
      fin_cases i
      · exact hs.symm
      · rfl
    rw [hvEq]
    simpa using heval'

private lemma sin_curvePair_algebraicIndependent :
    AlgebraicIndependent ℝ (curvePair Real.sin) :=
  curvePair_algebraicIndependent Real.sin
    (fun _ => Real.analyticAt_sin)
    sin_functionally_algebraicIndependent

private def optionUnitEquivFinTwo : Option Unit ≃ Fin 2 where
  toFun o := o.elim 1 (fun _ => 0)
  invFun i := ![some (), none] i
  left_inv o := by
    rcases o with _ | u
    · rfl
    · rcases u
      rfl
  right_inv i := by
    fin_cases i <;> rfl

private lemma sin_tSeq_not_algAt :
    ¬ algAt (fun n => Real.sin (tSeq n)) (hseq tSeq) := by
  let xOne : Unit → ℝ* :=
    fun _ => hseq (fun n => Real.sin (tSeq n))
  have hopt :
      AlgebraicIndependent ℝ
        (fun o : Option Unit => o.elim (hseq tSeq) xOne) := by
    refine (algebraicIndependent_equiv'
      (R := ℝ) (A := ℝ*) optionUnitEquivFinTwo
      (f := curvePair Real.sin)
      (g := fun o : Option Unit => o.elim (hseq tSeq) xOne) ?_).mpr
        sin_curvePair_algebraicIndependent
    funext o
    rcases o with _ | u
    · rfl
    · rcases u
      rfl
  have hsplit :=
    (AlgebraicIndependent.option_iff
      (x := xOne) (a := hseq tSeq)).mp hopt
  intro halg
  have halgField :
      @IsAlgebraic
        (IntermediateField.adjoin ℝ (Set.range xOne)) ℝ*
        inferInstance inferInstance
        (IntermediateField.toAlgebra
          (IntermediateField.adjoin ℝ (Set.range xOne)))
        (hseq tSeq) := by
    simpa [algAt, SeqBase, xOne] using halg
  have halgAlg :=
    (IntermediateField.isAlgebraic_adjoin_iff
      (F := ℝ) (E := ℝ*) (S := ℝ*)
      (s := Set.range xOne)).mp
      halgField
  exact hsplit.2 halgAlg

private def polyExpEval (Q : Polynomial (Polynomial ℝ)) (t : ℝ) : ℝ :=
  Polynomial.eval₂ (Polynomial.evalRingHom t) (Real.exp t) Q

private lemma tendsto_poly_exp_term_div (P : Polynomial ℝ)
    (k d : ℕ) (hkd : k < d) :
    Tendsto
      (fun t => P.eval t * Real.exp t ^ k / Real.exp t ^ d)
      atTop (𝓝 0) := by
  have hbase := P.tendsto_div_exp_atTop
  have hdecay :=
    Real.tendsto_exp_neg_atTop_nhds_zero.pow (d - k - 1)
  have hprod :
      Tendsto
        (fun t => (P.eval t / Real.exp t) *
          (Real.exp (-t)) ^ (d - k - 1))
        atTop (𝓝 0) := by
    convert hbase.mul hdecay using 1 <;> simp
  apply hprod.congr'
  filter_upwards [] with t
  have he : Real.exp t ≠ 0 := Real.exp_ne_zero t
  have hc : d - k = (d - k - 1) + 1 := by omega
  rw [Real.exp_neg, inv_pow]
  field_simp [he]
  have hpow :
      Real.exp t ^ d =
        Real.exp t * Real.exp t ^ (d - k - 1) * Real.exp t ^ k := by
    calc
      Real.exp t ^ d =
          Real.exp t ^ (1 + (d - k - 1) + k) := by congr 1 <;> omega
      _ = Real.exp t * Real.exp t ^ (d - k - 1) *
          Real.exp t ^ k := by rw [pow_add, pow_add, pow_one]
  rw [hpow]
  ring

private lemma tendsto_polyExpEval_eraseLead_div
    (Q : Polynomial (Polynomial ℝ)) :
    Tendsto
      (fun t => polyExpEval Q.eraseLead t /
        Real.exp t ^ Q.natDegree)
      atTop (𝓝 0) := by
  have hsum :=
    tendsto_finset_sum Q.eraseLead.support fun k hk =>
      tendsto_poly_exp_term_div (Q.eraseLead.coeff k) k
        Q.natDegree (Polynomial.lt_natDegree_of_mem_eraseLead_support hk)
  simpa [polyExpEval, Polynomial.eval₂_eq_sum, Polynomial.sum,
    Finset.sum_div] using hsum

private lemma polyExpEval_not_identically_zero
    (Q : Polynomial (Polynomial ℝ)) (hQ : Q ≠ 0) :
    ¬ ∀ t, polyExpEval Q t = 0 := by
  intro hzero
  have hlead :
      ∀ t, Q.leadingCoeff.eval t =
        -(polyExpEval Q.eraseLead t /
          Real.exp t ^ Q.natDegree) := by
    intro t
    have hz := hzero t
    rw [← Q.eraseLead_add_C_mul_X_pow] at hz
    simp only [polyExpEval, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hz
    change
      polyExpEval Q.eraseLead t +
        Q.leadingCoeff.eval t * Real.exp t ^ Q.natDegree = 0 at hz
    have hden : Real.exp t ^ Q.natDegree ≠ 0 :=
      pow_ne_zero _ (Real.exp_ne_zero t)
    rw [← neg_div]
    apply (eq_div_iff hden).2
    linarith
  have htend :
      Tendsto (fun t => Q.leadingCoeff.eval t) atTop (𝓝 0) := by
    have hneg :
        Tendsto
          (fun t => -(polyExpEval Q.eraseLead t /
            Real.exp t ^ Q.natDegree))
          atTop (𝓝 0) := by
      simpa using (tendsto_polyExpEval_eraseLead_div Q).neg
    exact hneg.congr' (Eventually.of_forall fun t => (hlead t).symm)
  have hlc : Q.leadingCoeff = 0 :=
    Polynomial.leadingCoeff_eq_zero.mp
      ((Polynomial.tendsto_nhds_iff Q.leadingCoeff).mp htend).1
  exact (Polynomial.leadingCoeff_ne_zero.mpr hQ) hlc

private def unitEquivPUnit : Unit ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv u := by cases u; rfl

private def unitPolyEquiv :
    MvPolynomial Unit ℝ ≃ₐ[ℝ] Polynomial ℝ :=
  (MvPolynomial.renameEquiv ℝ unitEquivPUnit).trans
    (MvPolynomial.pUnitAlgEquiv ℝ)

private def optionUnitPolyEquiv :
    MvPolynomial (Option Unit) ℝ ≃ₐ[ℝ]
      Polynomial (Polynomial ℝ) :=
  (MvPolynomial.optionEquivLeft ℝ Unit).trans
    (Polynomial.mapAlgEquiv unitPolyEquiv)

private lemma eval_unitPolyEquiv (q : MvPolynomial Unit ℝ) (y : ℝ) :
    Polynomial.eval y (unitPolyEquiv q) =
      MvPolynomial.eval (fun _ : Unit => y) q := by
  change
    Polynomial.eval₂ (RingHom.id ℝ) y
        (MvPolynomial.pUnitAlgEquiv ℝ
          (MvPolynomial.rename unitEquivPUnit q)) =
      MvPolynomial.eval₂ (RingHom.id ℝ) (fun _ : Unit => y) q
  calc
    _ = MvPolynomial.eval₂ (RingHom.id ℝ)
          (fun _ : PUnit.{1} => y)
          (MvPolynomial.rename unitEquivPUnit q) := by
        simpa using
          (MvPolynomial.eval₂_pUnitAlgEquiv
            (f := MvPolynomial.rename unitEquivPUnit q)
            (φ := RingHom.id ℝ)
            (a := fun _ : PUnit.{1} => y))
    _ = _ := by
      rw [MvPolynomial.eval₂_rename]
      rfl

private lemma eval_optionUnitPolyEquiv
    (p : MvPolynomial (Option Unit) ℝ) (x y : ℝ) :
    Polynomial.eval₂ (Polynomial.evalRingHom y) x
        (optionUnitPolyEquiv p) =
      MvPolynomial.eval
        (fun o : Option Unit => o.elim x (fun _ => y)) p := by
  have hcoeff :
      (Polynomial.evalRingHom y).comp unitPolyEquiv.toRingHom =
        MvPolynomial.eval (fun _ : Unit => y) := by
    apply DFunLike.ext _ _
    intro q
    exact eval_unitPolyEquiv q y
  change
    Polynomial.eval₂ (Polynomial.evalRingHom y) x
        (Polynomial.map unitPolyEquiv.toRingHom
          (MvPolynomial.optionEquivLeft ℝ Unit p)) =
      _
  rw [Polynomial.eval₂_map, hcoeff]
  symm
  simpa [Polynomial.eval_map] using
    (MvPolynomial.optionEquivLeft_elim_eval ℝ Unit
      (fun _ : Unit => y) x p)

private lemma exp_option_functionally_algebraicIndependent
    (p : MvPolynomial (Option Unit) ℝ)
    (h : ∀ t,
      MvPolynomial.eval
        (fun o : Option Unit =>
          o.elim (Real.exp t) (fun _ => t)) p = 0) :
    p = 0 := by
  by_contra hp
  have hQ : optionUnitPolyEquiv p ≠ 0 :=
    by simpa using optionUnitPolyEquiv.injective.ne hp
  apply polyExpEval_not_identically_zero
    (optionUnitPolyEquiv p) hQ
  intro t
  rw [polyExpEval, eval_optionUnitPolyEquiv]
  exact h t

private def optionUnitEquivFinTwoExp : Option Unit ≃ Fin 2 where
  toFun o := o.elim 0 (fun _ => 1)
  invFun i := ![none, some ()] i
  left_inv o := by
    rcases o with _ | u
    · rfl
    · rcases u
      rfl
  right_inv i := by
    fin_cases i <;> rfl

private lemma exp_functionally_algebraicIndependent
    (p : MvPolynomial (Fin 2) ℝ)
    (h : ∀ t, MvPolynomial.aeval ![Real.exp t, t] p = 0) :
    p = 0 := by
  let E :
      MvPolynomial (Fin 2) ℝ ≃ₐ[ℝ]
        MvPolynomial (Option Unit) ℝ :=
    MvPolynomial.renameEquiv ℝ optionUnitEquivFinTwoExp.symm
  apply E.injective
  apply exp_option_functionally_algebraicIndependent
  intro t
  change
    MvPolynomial.eval
      (fun o : Option Unit =>
        o.elim (Real.exp t) (fun _ => t))
      (MvPolynomial.rename optionUnitEquivFinTwoExp.symm p) = 0
  rw [MvPolynomial.eval_rename]
  convert h t using 1
  congr 2
  funext i
  fin_cases i <;> rfl

private lemma exp_curvePair_algebraicIndependent :
    AlgebraicIndependent ℝ (curvePair Real.exp) :=
  curvePair_algebraicIndependent Real.exp
    (fun _ => analyticAt_rexp)
    exp_functionally_algebraicIndependent

private lemma exp_tSeq_not_algAt :
    ¬ algAt (fun n => Real.exp (tSeq n)) (hseq tSeq) := by
  let xOne : Unit → ℝ* :=
    fun _ => hseq (fun n => Real.exp (tSeq n))
  have hopt :
      AlgebraicIndependent ℝ
        (fun o : Option Unit => o.elim (hseq tSeq) xOne) := by
    refine (algebraicIndependent_equiv'
      (R := ℝ) (A := ℝ*) optionUnitEquivFinTwo
      (f := curvePair Real.exp)
      (g := fun o : Option Unit => o.elim (hseq tSeq) xOne) ?_).mpr
        exp_curvePair_algebraicIndependent
    funext o
    rcases o with _ | u
    · rfl
    · rcases u
      rfl
  have hsplit :=
    (AlgebraicIndependent.option_iff
      (x := xOne) (a := hseq tSeq)).mp hopt
  intro halg
  have halgField :
      @IsAlgebraic
        (IntermediateField.adjoin ℝ (Set.range xOne)) ℝ*
        inferInstance inferInstance
        (IntermediateField.toAlgebra
          (IntermediateField.adjoin ℝ (Set.range xOne)))
        (hseq tSeq) := by
    simpa [algAt, SeqBase, xOne] using halg
  have halgAlg :=
    (IntermediateField.isAlgebraic_adjoin_iff
      (F := ℝ) (E := ℝ*) (S := ℝ*)
      (s := Set.range xOne)).mp
      halgField
  exact hsplit.2 halgAlg

private def qExprAux (a b c : ℝ) : AlgebraicExpr :=
  .add (.add (.mul (.const a) (.mul .var .var))
    (.mul (.const b) .var)) (.const c)

private def linearSqrtExprAux (A B a b c : ℝ) : AlgebraicExpr :=
  .mul (.add (.mul (.const A) .var) (.const B))
    (.sqrt (qExprAux a b c))

private def residualExprAux (e : AlgebraicExpr)
    (A B a b c : ℝ) : AlgebraicExpr :=
  .add e (.mul (.const (-1)) (linearSqrtExprAux A B a b c))

private def affineExprAux (u r : ℝ) : AlgebraicExpr :=
  .add (.const u) (.mul (.const r) .var)

private def affineComposeExprAux (u r : ℝ)
    (v : AlgebraicExpr) : AlgebraicExpr :=
  .add (.const u) (.mul (.const r) v)

private def sinhExpExprAux : AlgebraicExpr :=
  .mul (.const (1 / 2))
    (.add .var (.mul (.const (-1)) (.inv .var)))

private def coshExpExprAux : AlgebraicExpr :=
  .mul (.const (1 / 2))
    (.add .var (.inv .var))

private lemma sinhExpExprAux_eval (t : ℝ) :
    sinhExpExprAux.eval (Real.exp t) = Real.sinh t := by
  simp only [sinhExpExprAux, AlgebraicExpr.eval]
  rw [Real.sinh_eq, Real.exp_neg]
  field_simp [Real.exp_ne_zero t]
  ring

private lemma coshExpExprAux_eval (t : ℝ) :
    coshExpExprAux.eval (Real.exp t) = Real.cosh t := by
  simp only [coshExpExprAux, AlgebraicExpr.eval]
  rw [Real.cosh_eq, Real.exp_neg]
  field_simp [Real.exp_ne_zero t]

private lemma q_hasDerivAt_aux (a b c x : ℝ) :
    HasDerivAt (q a b c) (2 * a * x + b) x := by
  have ha : HasDerivAt (fun y : ℝ => a * y ^ 2)
      (2 * a * x) x := by
    convert ((hasDerivAt_id x).pow 2).const_mul a using 1 <;>
      simp only [id_eq] <;> ring
  have hb : HasDerivAt (fun y : ℝ => b * y) b x := by
    convert (hasDerivAt_id x).const_mul b using 1 <;> ring
  have hc : HasDerivAt (fun _ : ℝ => c) 0 x :=
    hasDerivAt_const x c
  simpa [q] using HasDerivAt.add (HasDerivAt.add ha hb) hc

private lemma residual_hasDerivAt_aux
    (a b c a₁ b₁ c₁ A B lam : ℝ)
    (hred : ReductionIdentity a b c a₁ b₁ c₁ A B lam)
    (e : AlgebraicExpr) (x : ℝ) (hx : x ∈ branch a b c)
    (he : HasDerivAt e.eval
      (integrand a b c a₁ b₁ c₁ x) x) :
    HasDerivAt (residualExprAux e A B a b c).eval
      (lam / Real.sqrt (q a b c x)) x := by
  have hq : 0 < q a b c x := hx
  have hs : Real.sqrt (q a b c x) ≠ 0 :=
    (Real.sqrt_pos.2 hq).ne'
  have hs2 : Real.sqrt (q a b c x) ^ 2 = q a b c x :=
    Real.sq_sqrt hq.le
  have hsder :
      HasDerivAt (fun y => Real.sqrt (q a b c y))
        ((2 * a * x + b) /
          (2 * Real.sqrt (q a b c x))) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x
      (q_hasDerivAt_aux a b c x) using 1 <;> ring
  have hlin : HasDerivAt (fun y : ℝ => A * y + B) A x := by
    have hmul : HasDerivAt (fun y : ℝ => A * y) A x := by
      convert (hasDerivAt_id x).const_mul A using 1 <;> ring
    convert hmul.add (hasDerivAt_const x B) using 1 <;> ring
  have hprod := hlin.mul hsder
  have hcoef :
      integrand a b c a₁ b₁ c₁ x -
          (A * Real.sqrt (q a b c x) +
            (A * x + B) *
              ((2 * a * x + b) /
                (2 * Real.sqrt (q a b c x)))) =
        lam / Real.sqrt (q a b c x) := by
    unfold integrand
    rw [hred x]
    unfold reductionRhs
    field_simp [hs]
    rw [hs2]
    ring
  have h := he.sub hprod
  have h' := h.congr_deriv hcoef
  apply h'.congr_of_eventuallyEq
  filter_upwards [] with y
  change
    (residualExprAux e A B a b c).eval y =
      e.eval y - (A * y + B) * Real.sqrt (q a b c y)
  simp only [residualExprAux, linearSqrtExprAux, qExprAux,
    AlgebraicExpr.eval]
  have hqeq :
      a * (y * y) + b * y + c = q a b c y := by
    unfold q
    ring
  rw [hqeq]
  ring

private lemma lam_eq_zero_of_neg_aux
    (a b c a₁ b₁ c₁ A B lam : ℝ) (ha : a < 0)
    (hbranch : (branch a b c).Nonempty)
    (hred : ReductionIdentity a b c a₁ b₁ c₁ A B lam)
    (hint : AlgebraicIntegrableOn (branch a b c)
      (integrand a b c a₁ b₁ c₁)) :
    lam = 0 := by
  by_contra hlam
  obtain ⟨e, he⟩ := hint
  have ha0 : a ≠ 0 := ne_of_lt ha
  let u : ℝ := -b / (2 * a)
  let m : ℝ := c - b ^ 2 / (4 * a)
  have hcomplete : ∀ x,
      q a b c x = a * (x - u) ^ 2 + m := by
    intro x
    dsimp [u, m]
    unfold q
    field_simp [ha0]
    ring
  obtain ⟨x₀, hx₀⟩ := hbranch
  have hqx₀ : 0 < q a b c x₀ := by
    exact hx₀
  rw [hcomplete] at hqx₀
  have hm : 0 < m := by
    have hnonpos :
        a * (x₀ - u) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg ha.le (sq_nonneg _)
    linarith
  let r : ℝ := Real.sqrt (m / (-a))
  have hratio : 0 < m / (-a) :=
    div_pos hm (neg_pos.mpr ha)
  have hrpos : 0 < r := by
    dsimp [r]
    exact Real.sqrt_pos.2 hratio
  have hrsq : r ^ 2 = m / (-a) := by
    dsimp [r]
    exact Real.sq_sqrt hratio.le
  have hrrel : (-a) * r ^ 2 = m := by
    rw [hrsq]
    field_simp [ha0]
  have har : a * r ^ 2 = -m := by
    linarith [hrrel]
  let g : ℝ → ℝ := fun t => u + r * Real.sin t
  have hQg : ∀ t,
      q a b c (g t) = m * Real.cos t ^ 2 := by
    intro t
    calc
      q a b c (g t) =
          a * (g t - u) ^ 2 + m := hcomplete (g t)
      _ = a * r ^ 2 * Real.sin t ^ 2 + m := by
        dsimp [g]
        ring
      _ = -m * Real.sin t ^ 2 + m := by rw [har]
      _ = m * Real.cos t ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq t]
  have hgder : ∀ t,
      HasDerivAt g (r * Real.cos t) t := by
    intro t
    dsimp [g]
    convert (hasDerivAt_const t u).add
      ((Real.hasDerivAt_sin t).const_mul r) using 1 <;> ring
  let s : Set ℝ :=
    Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
  have hsqrt : ∀ t ∈ s,
      Real.sqrt (q a b c (g t)) =
        Real.sqrt m * Real.cos t := by
    intro t ht
    have hcos : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo ht
    have hqpos : 0 < q a b c (g t) := by
      rw [hQg]
      exact mul_pos hm (sq_pos_of_pos hcos)
    have hsq :=
      Real.sq_sqrt hqpos.le
    have hmsq :=
      Real.sq_sqrt hm.le
    have hsnonneg :
        0 ≤ Real.sqrt (q a b c (g t)) :=
      Real.sqrt_nonneg _
    have hrhsnonneg :
        0 ≤ Real.sqrt m * Real.cos t :=
      mul_nonneg (Real.sqrt_nonneg _) hcos.le
    have hrhssq :
        (Real.sqrt m * Real.cos t) ^ 2 =
          q a b c (g t) := by
      rw [hQg, mul_pow, hmsq]
    nlinarith [hsq, hrhssq]
  let k : ℝ := lam * r / Real.sqrt m
  have hk : k ≠ 0 := by
    dsimp [k]
    exact div_ne_zero (mul_ne_zero hlam hrpos.ne')
      (Real.sqrt_pos.2 hm).ne'
  let F : ℝ → ℝ :=
    fun t => (residualExprAux e A B a b c).eval (g t)
  have hFder : ∀ t ∈ s, HasDerivAt F k t := by
    intro t ht
    have hcos : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo ht
    have hqpos : 0 < q a b c (g t) := by
      rw [hQg]
      exact mul_pos hm (sq_pos_of_pos hcos)
    have hres :=
      residual_hasDerivAt_aux a b c a₁ b₁ c₁ A B lam
        hred e (g t) hqpos (he (g t) hqpos)
    have hcomp := hres.comp t (hgder t)
    have hcoef :
        (lam / Real.sqrt (q a b c (g t))) *
            (r * Real.cos t) = k := by
      rw [hsqrt t ht]
      dsimp [k]
      field_simp [(Real.sqrt_pos.2 hm).ne', hcos.ne']
    simpa [F, Function.comp_def] using
      hcomp.congr_deriv hcoef
  have hFdiff : DifferentiableOn ℝ F s := by
    intro t ht
    exact (hFder t ht).differentiableAt.differentiableWithinAt
  have hlinDer : ∀ t,
      HasDerivAt (fun y : ℝ => k * y) k t := by
    intro t
    convert (hasDerivAt_id t).const_mul k using 1 <;> ring
  have hlindiff :
      DifferentiableOn ℝ (fun y : ℝ => k * y) s := by
    intro t _
    exact (hlinDer t).differentiableAt.differentiableWithinAt
  have hderEq :
      s.EqOn (deriv F) (deriv fun y : ℝ => k * y) := by
    intro t ht
    exact (hFder t ht).deriv.trans (hlinDer t).deriv.symm
  obtain ⟨C, hC⟩ :=
    isOpen_Ioo.exists_eq_add_of_deriv_eq
      isPreconnected_Ioo hFdiff hlindiff hderEq
  have htend0 :
      Tendsto tSeq (Filter.hyperfilter ℕ) (𝓝 (0 : ℝ)) := by
    change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      (Filter.hyperfilter ℕ) (𝓝 0)
    exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mono_left
      Nat.hyperfilter_le_atTop
  have hzeroS : (0 : ℝ) ∈ s := by
    dsimp [s]
    constructor <;> linarith [Real.pi_pos]
  have hevS : ∀ᶠ n in Filter.hyperfilter ℕ, tSeq n ∈ s :=
    htend0.eventually (isOpen_Ioo.mem_nhds hzeroS)
  let z : ℕ → ℝ := fun n => Real.sin (tSeq n)
  let xseq : ℕ → ℝ := fun n => g (tSeq n)
  have hxseqEq :
      hseq xseq = evalSeq z (affineExprAux u r) := by
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [] with n
    rfl
  have hxalg : algAt z (hseq xseq) := by
    rw [hxseqEq]
    exact evalSeq_isAlgebraic z (affineExprAux u r)
  have hevLinear :
      ∀ᶠ n in Filter.hyperfilter ℕ,
        (residualExprAux e A B a b c).eval (xseq n) =
          k * tSeq n + C := by
    filter_upwards [hevS] with n hn
    simpa [F, xseq] using hC hn
  have htalg :=
    algAt_tSeq_of_eventually_eval_linear z xseq
      (residualExprAux e A B a b c) k C hxalg hk hevLinear
  apply sin_tSeq_not_algAt
  simpa [z] using htalg

private lemma exp_chart_forces_false_aux
    (rExpr xExpr : AlgebraicExpr) (g : ℝ → ℝ)
    (k : ℝ) (s : Set ℝ) (hk : k ≠ 0)
    (hsopen : IsOpen s) (hspre : IsPreconnected s)
    (hFder : ∀ t ∈ s,
      HasDerivAt (fun y => rExpr.eval (g y)) k t)
    (hevS : ∀ᶠ n in Filter.hyperfilter ℕ, tSeq n ∈ s)
    (hxExpr : ∀ t, xExpr.eval (Real.exp t) = g t) :
    False := by
  let F : ℝ → ℝ := fun t => rExpr.eval (g t)
  have hFdiff : DifferentiableOn ℝ F s := by
    intro t ht
    exact (hFder t ht).differentiableAt.differentiableWithinAt
  have hlinDer : ∀ t,
      HasDerivAt (fun y : ℝ => k * y) k t := by
    intro t
    convert (hasDerivAt_id t).const_mul k using 1 <;> ring
  have hlindiff :
      DifferentiableOn ℝ (fun y : ℝ => k * y) s := by
    intro t _
    exact (hlinDer t).differentiableAt.differentiableWithinAt
  have hderEq :
      s.EqOn (deriv F) (deriv fun y : ℝ => k * y) := by
    intro t ht
    exact (hFder t ht).deriv.trans (hlinDer t).deriv.symm
  obtain ⟨C, hC⟩ :=
    hsopen.exists_eq_add_of_deriv_eq
      hspre hFdiff hlindiff hderEq
  let z : ℕ → ℝ := fun n => Real.exp (tSeq n)
  let xseq : ℕ → ℝ := fun n => g (tSeq n)
  have hxseqEq :
      hseq xseq = evalSeq z xExpr := by
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [] with n
    exact (hxExpr (tSeq n)).symm
  have hxalg : algAt z (hseq xseq) := by
    rw [hxseqEq]
    exact evalSeq_isAlgebraic z xExpr
  have hevLinear :
      ∀ᶠ n in Filter.hyperfilter ℕ,
        rExpr.eval (xseq n) = k * tSeq n + C := by
    filter_upwards [hevS] with n hn
    simpa [F, xseq] using hC hn
  have htalg :=
    algAt_tSeq_of_eventually_eval_linear z xseq
      rExpr k C hxalg hk hevLinear
  apply exp_tSeq_not_algAt
  simpa [z] using htalg

private lemma lam_eq_zero_of_pos_aux
    (a b c a₁ b₁ c₁ A B lam : ℝ) (ha : 0 < a)
    (hred : ReductionIdentity a b c a₁ b₁ c₁ A B lam)
    (hint : AlgebraicIntegrableOn (branch a b c)
      (integrand a b c a₁ b₁ c₁)) :
    lam = 0 := by
  by_contra hlam
  obtain ⟨e, he⟩ := hint
  have ha0 : a ≠ 0 := ne_of_gt ha
  let u : ℝ := -b / (2 * a)
  let m : ℝ := c - b ^ 2 / (4 * a)
  have hcomplete : ∀ x,
      q a b c x = a * (x - u) ^ 2 + m := by
    intro x
    dsimp [u, m]
    unfold q
    field_simp [ha0]
    ring
  rcases lt_trichotomy m 0 with hmneg | hmzero | hmpos
  · let d : ℝ := -m
    have hd : 0 < d := by
      dsimp [d]
      linarith
    let r : ℝ := Real.sqrt (d / a)
    have hratio : 0 < d / a := div_pos hd ha
    have hrpos : 0 < r := by
      dsimp [r]
      exact Real.sqrt_pos.2 hratio
    have hrsq : r ^ 2 = d / a := by
      dsimp [r]
      exact Real.sq_sqrt hratio.le
    have har : a * r ^ 2 = d := by
      rw [hrsq]
      field_simp [ha0]
    have hmd : m = -d := by
      dsimp [d]
      ring
    let g : ℝ → ℝ := fun t => u + r * Real.cosh t
    have hQg : ∀ t,
        q a b c (g t) = d * Real.sinh t ^ 2 := by
      intro t
      calc
        q a b c (g t) =
            a * (g t - u) ^ 2 + m := hcomplete (g t)
        _ = a * r ^ 2 * Real.cosh t ^ 2 + m := by
          dsimp [g]
          ring
        _ = d * Real.cosh t ^ 2 - d := by
          rw [har, hmd]
          ring
        _ = d * Real.sinh t ^ 2 := by
          nlinarith [Real.cosh_sq_sub_sinh_sq t]
    have hgder : ∀ t,
        HasDerivAt g (r * Real.sinh t) t := by
      intro t
      dsimp [g]
      convert (hasDerivAt_const t u).add
        ((Real.hasDerivAt_cosh t).const_mul r) using 1 <;> ring
    let s : Set ℝ := Set.Ioi 0
    have hsqrt : ∀ t ∈ s,
        Real.sqrt (q a b c (g t)) =
          Real.sqrt d * Real.sinh t := by
      intro t ht
      have hsinh : 0 < Real.sinh t :=
        Real.sinh_pos_iff.mpr ht
      have hqpos : 0 < q a b c (g t) := by
        rw [hQg]
        exact mul_pos hd (sq_pos_of_pos hsinh)
      have hsq := Real.sq_sqrt hqpos.le
      have hdsq := Real.sq_sqrt hd.le
      have hsnonneg :
          0 ≤ Real.sqrt (q a b c (g t)) :=
        Real.sqrt_nonneg _
      have hrhsnonneg :
          0 ≤ Real.sqrt d * Real.sinh t :=
        mul_nonneg (Real.sqrt_nonneg _) hsinh.le
      have hrhssq :
          (Real.sqrt d * Real.sinh t) ^ 2 =
            q a b c (g t) := by
        rw [hQg, mul_pow, hdsq]
      nlinarith [hsq, hrhssq]
    let k : ℝ := lam * r / Real.sqrt d
    have hk : k ≠ 0 := by
      dsimp [k]
      exact div_ne_zero (mul_ne_zero hlam hrpos.ne')
        (Real.sqrt_pos.2 hd).ne'
    have hFder : ∀ t ∈ s,
        HasDerivAt
          (fun y =>
            (residualExprAux e A B a b c).eval (g y))
          k t := by
      intro t ht
      have hsinh : 0 < Real.sinh t :=
        Real.sinh_pos_iff.mpr ht
      have hqpos : 0 < q a b c (g t) := by
        rw [hQg]
        exact mul_pos hd (sq_pos_of_pos hsinh)
      have hres :=
        residual_hasDerivAt_aux a b c a₁ b₁ c₁ A B lam
          hred e (g t) hqpos (he (g t) hqpos)
      have hcomp := hres.comp t (hgder t)
      have hcoef :
          (lam / Real.sqrt (q a b c (g t))) *
              (r * Real.sinh t) = k := by
        rw [hsqrt t ht]
        dsimp [k]
        field_simp [(Real.sqrt_pos.2 hd).ne', hsinh.ne']
      simpa [Function.comp_def] using
        hcomp.congr_deriv hcoef
    have hevS :
        ∀ᶠ n in Filter.hyperfilter ℕ, tSeq n ∈ s := by
      filter_upwards [] with n
      dsimp [s, tSeq]
      change 0 < 1 / ((n : ℝ) + 1)
      positivity
    have hxExpr : ∀ t,
        (affineComposeExprAux u r coshExpExprAux).eval
            (Real.exp t) =
          g t := by
      intro t
      change u + r * coshExpExprAux.eval (Real.exp t) =
        u + r * Real.cosh t
      rw [coshExpExprAux_eval]
    exact exp_chart_forces_false_aux
      (residualExprAux e A B a b c)
      (affineComposeExprAux u r coshExpExprAux)
      g k s hk isOpen_Ioi isPreconnected_Ioi
      hFder hevS hxExpr
  · let g : ℝ → ℝ := fun t => u + Real.exp t
    have hQg : ∀ t,
        q a b c (g t) = a * Real.exp t ^ 2 := by
      intro t
      calc
        q a b c (g t) =
            a * (g t - u) ^ 2 + m := hcomplete (g t)
        _ = a * Real.exp t ^ 2 := by
          dsimp [g]
          rw [hmzero]
          ring
    have hgder : ∀ t,
        HasDerivAt g (Real.exp t) t := by
      intro t
      dsimp [g]
      convert (hasDerivAt_const t u).add
        (Real.hasDerivAt_exp t) using 1 <;> ring
    have hsqrt : ∀ t,
        Real.sqrt (q a b c (g t)) =
          Real.sqrt a * Real.exp t := by
      intro t
      have hexp : 0 < Real.exp t := Real.exp_pos t
      have hqpos : 0 < q a b c (g t) := by
        rw [hQg]
        exact mul_pos ha (sq_pos_of_pos hexp)
      have hsq := Real.sq_sqrt hqpos.le
      have hasq := Real.sq_sqrt ha.le
      have hsnonneg :
          0 ≤ Real.sqrt (q a b c (g t)) :=
        Real.sqrt_nonneg _
      have hrhsnonneg :
          0 ≤ Real.sqrt a * Real.exp t :=
        mul_nonneg (Real.sqrt_nonneg _) hexp.le
      have hrhssq :
          (Real.sqrt a * Real.exp t) ^ 2 =
            q a b c (g t) := by
        rw [hQg, mul_pow, hasq]
      nlinarith [hsq, hrhssq]
    let k : ℝ := lam / Real.sqrt a
    have hk : k ≠ 0 := by
      dsimp [k]
      exact div_ne_zero hlam (Real.sqrt_pos.2 ha).ne'
    have hFder : ∀ t ∈ (Set.univ : Set ℝ),
        HasDerivAt
          (fun y =>
            (residualExprAux e A B a b c).eval (g y))
          k t := by
      intro t _
      have hexp : 0 < Real.exp t := Real.exp_pos t
      have hqpos : 0 < q a b c (g t) := by
        rw [hQg]
        exact mul_pos ha (sq_pos_of_pos hexp)
      have hres :=
        residual_hasDerivAt_aux a b c a₁ b₁ c₁ A B lam
          hred e (g t) hqpos (he (g t) hqpos)
      have hcomp := hres.comp t (hgder t)
      have hcoef :
          (lam / Real.sqrt (q a b c (g t))) *
              Real.exp t = k := by
        rw [hsqrt t]
        dsimp [k]
        field_simp [(Real.sqrt_pos.2 ha).ne',
          (Real.exp_pos t).ne']
      simpa [Function.comp_def] using
        hcomp.congr_deriv hcoef
    have hevS :
        ∀ᶠ n in Filter.hyperfilter ℕ,
          tSeq n ∈ (Set.univ : Set ℝ) :=
      Eventually.of_forall fun _ => Set.mem_univ _
    have hxExpr : ∀ t,
        (affineExprAux u 1).eval (Real.exp t) = g t := by
      intro t
      change u + 1 * Real.exp t = u + Real.exp t
      ring
    exact exp_chart_forces_false_aux
      (residualExprAux e A B a b c)
      (affineExprAux u 1) g k Set.univ hk
      isOpen_univ isPreconnected_univ hFder hevS hxExpr
  · let r : ℝ := Real.sqrt (m / a)
    have hratio : 0 < m / a := div_pos hmpos ha
    have hrpos : 0 < r := by
      dsimp [r]
      exact Real.sqrt_pos.2 hratio
    have hrsq : r ^ 2 = m / a := by
      dsimp [r]
      exact Real.sq_sqrt hratio.le
    have har : a * r ^ 2 = m := by
      rw [hrsq]
      field_simp [ha0]
    let g : ℝ → ℝ := fun t => u + r * Real.sinh t
    have hQg : ∀ t,
        q a b c (g t) = m * Real.cosh t ^ 2 := by
      intro t
      calc
        q a b c (g t) =
            a * (g t - u) ^ 2 + m := hcomplete (g t)
        _ = a * r ^ 2 * Real.sinh t ^ 2 + m := by
          dsimp [g]
          ring
        _ = m * Real.sinh t ^ 2 + m := by rw [har]
        _ = m * Real.cosh t ^ 2 := by
          nlinarith [Real.cosh_sq_sub_sinh_sq t]
    have hgder : ∀ t,
        HasDerivAt g (r * Real.cosh t) t := by
      intro t
      dsimp [g]
      convert (hasDerivAt_const t u).add
        ((Real.hasDerivAt_sinh t).const_mul r) using 1 <;> ring
    have hsqrt : ∀ t,
        Real.sqrt (q a b c (g t)) =
          Real.sqrt m * Real.cosh t := by
      intro t
      have hcosh : 0 < Real.cosh t := Real.cosh_pos t
      have hqpos : 0 < q a b c (g t) := by
        rw [hQg]
        exact mul_pos hmpos (sq_pos_of_pos hcosh)
      have hsq := Real.sq_sqrt hqpos.le
      have hmsq := Real.sq_sqrt hmpos.le
      have hsnonneg :
          0 ≤ Real.sqrt (q a b c (g t)) :=
        Real.sqrt_nonneg _
      have hrhsnonneg :
          0 ≤ Real.sqrt m * Real.cosh t :=
        mul_nonneg (Real.sqrt_nonneg _) hcosh.le
      have hrhssq :
          (Real.sqrt m * Real.cosh t) ^ 2 =
            q a b c (g t) := by
        rw [hQg, mul_pow, hmsq]
      nlinarith [hsq, hrhssq]
    let k : ℝ := lam * r / Real.sqrt m
    have hk : k ≠ 0 := by
      dsimp [k]
      exact div_ne_zero (mul_ne_zero hlam hrpos.ne')
        (Real.sqrt_pos.2 hmpos).ne'
    have hFder : ∀ t ∈ (Set.univ : Set ℝ),
        HasDerivAt
          (fun y =>
            (residualExprAux e A B a b c).eval (g y))
          k t := by
      intro t _
      have hcosh : 0 < Real.cosh t := Real.cosh_pos t
      have hqpos : 0 < q a b c (g t) := by
        rw [hQg]
        exact mul_pos hmpos (sq_pos_of_pos hcosh)
      have hres :=
        residual_hasDerivAt_aux a b c a₁ b₁ c₁ A B lam
          hred e (g t) hqpos (he (g t) hqpos)
      have hcomp := hres.comp t (hgder t)
      have hcoef :
          (lam / Real.sqrt (q a b c (g t))) *
              (r * Real.cosh t) = k := by
        rw [hsqrt t]
        dsimp [k]
        field_simp [(Real.sqrt_pos.2 hmpos).ne',
          (Real.cosh_pos t).ne']
      simpa [Function.comp_def] using
        hcomp.congr_deriv hcoef
    have hevS :
        ∀ᶠ n in Filter.hyperfilter ℕ,
          tSeq n ∈ (Set.univ : Set ℝ) :=
      Eventually.of_forall fun _ => Set.mem_univ _
    have hxExpr : ∀ t,
        (affineComposeExprAux u r sinhExpExprAux).eval
            (Real.exp t) =
          g t := by
      intro t
      change u + r * sinhExpExprAux.eval (Real.exp t) =
        u + r * Real.sinh t
      rw [sinhExpExprAux_eval]
    exact exp_chart_forces_false_aux
      (residualExprAux e A B a b c)
      (affineComposeExprAux u r sinhExpExprAux)
      g k Set.univ hk isOpen_univ isPreconnected_univ
      hFder hevS hxExpr

private lemma gap1_necessity_aux
    (a b c a₁ b₁ c₁ A B lam : ℝ)
    (hbranch : (branch a b c).Nonempty)
    (hred : ReductionIdentity a b c a₁ b₁ c₁ A B lam)
    (hint : AlgebraicIntegrableOn (branch a b c)
      (integrand a b c a₁ b₁ c₁)) :
    a = 0 ∨ lam = 0 := by
  by_cases ha0 : a = 0
  · exact Or.inl ha0
  · right
    rcases lt_or_gt_of_ne ha0 with ha | ha
    · exact lam_eq_zero_of_neg_aux
        a b c a₁ b₁ c₁ A B lam ha hbranch hred hint
    · exact lam_eq_zero_of_pos_aux
        a b c a₁ b₁ c₁ A B lam ha hred hint

private theorem linear_case_algebraic_aux (a b c a₁ b₁ c₁ : ℝ) (ha : a = 0) :
    AlgebraicIntegrableOn (branch a b c) (integrand a b c a₁ b₁ c₁) := by
  subst a
  by_cases hb : b = 0
  · subst b
    let A := a₁ / (3 * Real.sqrt c)
    let B := b₁ / (2 * Real.sqrt c)
    let C := c₁ / Real.sqrt c
    refine ⟨cubicExpr A B C, ?_⟩
    intro x hx
    have hcpos : 0 < c := by simpa [branch, q] using hx
    have hs0 : Real.sqrt c ≠ 0 := (Real.sqrt_pos.2 hcpos).ne'
    have h :=
      (((hasDerivAt_id x).pow 3).const_mul A)
    have h3 : HasDerivAt (fun y : ℝ => A * y ^ 3) (3 * A * x ^ 2) x := by
      convert h using 1 <;> simp only [id_eq] <;> ring
    have h2 : HasDerivAt (fun y : ℝ => B * y ^ 2) (2 * B * x) x := by
      convert ((hasDerivAt_id x).pow 2).const_mul B using 1 <;>
        simp only [id_eq] <;> ring
    have h1 : HasDerivAt (fun y : ℝ => C * y) C x := by
      convert (hasDerivAt_id x).const_mul C using 1 <;> ring
    have hsum : HasDerivAt
        (fun y : ℝ => (A * y ^ 3 + B * y ^ 2) + C * y)
        ((3 * A * x ^ 2 + 2 * B * x) + C) x :=
      (h3.add h2).add h1
    have hcoef :
        A * (3 * x ^ 2) + B * (2 * x) + C =
          integrand 0 0 c a₁ b₁ c₁ x := by
      unfold integrand numerator q A B C
      field_simp [hs0]
      ring
    have h' := hsum.congr_deriv (by
      calc
        3 * A * x ^ 2 + 2 * B * x + C =
            A * (3 * x ^ 2) + B * (2 * x) + C := by ring
        _ = integrand 0 0 c a₁ b₁ c₁ x := hcoef)
    apply h'.congr_of_eventuallyEq
    filter_upwards [] with y
    simp only [cubicExpr, AlgebraicExpr.eval]
    ring
  · let A := 2 * a₁ / (5 * b)
    let B := 2 * (b₁ - 2 * A * c) / (3 * b)
    let C := 2 * (c₁ - B * c) / b
    refine ⟨polySqrtExpr A B C 0 b c, ?_⟩
    intro x hx
    have hq : 0 < q 0 b c x := hx
    have hs0 : Real.sqrt (q 0 b c x) ≠ 0 :=
      (Real.sqrt_pos.2 hq).ne'
    have hs2 : (Real.sqrt (q 0 b c x)) ^ 2 = q 0 b c x :=
      Real.sq_sqrt hq.le
    have hsder : HasDerivAt (fun y => Real.sqrt (q 0 b c y))
        (b / (2 * Real.sqrt (q 0 b c x))) x := by
      convert (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x
        (q_hasDerivAt 0 b c x) using 1 <;> ring
    have hp : HasDerivAt (fun y : ℝ => A * y ^ 2 + B * y + C)
        (2 * A * x + B) x := by
      have h2 : HasDerivAt (fun y : ℝ => A * y ^ 2) (2 * A * x) x := by
        convert ((hasDerivAt_id x).pow 2).const_mul A using 1 <;>
          simp only [id_eq] <;> ring
      have h1 : HasDerivAt (fun y : ℝ => B * y) B x := by
        convert (hasDerivAt_id x).const_mul B using 1 <;> ring
      convert HasDerivAt.add (HasDerivAt.add h2 h1)
        (hasDerivAt_const x C) using 1 <;> ring
    have h := hp.mul hsder
    have hcoef :
        (2 * A * x + B) * Real.sqrt (q 0 b c x) +
            (A * x ^ 2 + B * x + C) *
              (b / (2 * Real.sqrt (q 0 b c x))) =
          integrand 0 b c a₁ b₁ c₁ x := by
      unfold integrand numerator
      field_simp [hs0, hb]
      rw [hs2]
      unfold q
      dsimp [A, B, C]
      field_simp [hb]
      ring
    have h' := h.congr_deriv hcoef
    apply h'.congr_of_eventuallyEq
    filter_upwards [] with y
    simp only [polySqrtExpr, polyExpr, qExpr, AlgebraicExpr.eval]
    simp only [Pi.mul_apply]
    unfold q
    ring

theorem gap1 (a b c a₁ b₁ c₁ A B lam : ℝ)
    (hbranch : (branch a b c).Nonempty)
    (hred : ReductionIdentity a b c a₁ b₁ c₁ A B lam) :
    AlgebraicIntegrableOn (branch a b c) (integrand a b c a₁ b₁ c₁) ↔
      a = 0 ∨ lam = 0 := by
  constructor
  · intro hint
    exact gap1_necessity_aux
      a b c a₁ b₁ c₁ A B lam hbranch hred hint
  · rintro (ha | hlam)
    · exact linear_case_algebraic_aux a b c a₁ b₁ c₁ ha
    · rw [hlam] at hred
      exact reduction_algebraic a b c a₁ b₁ c₁ A B hred
theorem gap2 (a b c a₁ b₁ c₁ A B lam : ℝ) (ha : a ≠ 0)
    (hred : ReductionIdentity a b c a₁ b₁ c₁ A B lam) :
    A = a₁ / (2 * a) := by
  have h0 := hred 0
  have h1 := hred 1
  have hm := hred (-1)
  norm_num [numerator, reductionRhs, q] at h0 h1 hm
  have hlead : a₁ = 2 * a * A := by
    linarith
  field_simp [ha]
  linarith
theorem gap3 (a b c a₁ b₁ c₁ A B lam : ℝ) (ha : a ≠ 0)
    (hred : ReductionIdentity a b c a₁ b₁ c₁ A B lam) :
    B = (4 * a * b₁ - 3 * a₁ * b) / (4 * a ^ 2) := by
  have hA := gap2 a b c a₁ b₁ c₁ A B lam ha hred
  have h1 := hred 1
  have hm := hred (-1)
  norm_num [numerator, reductionRhs, q] at h1 hm
  rw [hA] at h1 hm
  field_simp [ha] at h1 hm ⊢
  linarith
theorem gap4 (a b c a₁ b₁ c₁ A B lam : ℝ) (ha : a ≠ 0)
    (hred : ReductionIdentity a b c a₁ b₁ c₁ A B lam) :
    lam =
      (8 * a ^ 2 * c₁ + 3 * a₁ * b ^ 2 -
        4 * a * (a₁ * c + b * b₁)) / (8 * a ^ 2) := by
  have hA := gap2 a b c a₁ b₁ c₁ A B lam ha hred
  have hB := gap3 a b c a₁ b₁ c₁ A B lam ha hred
  have h0 := hred 0
  norm_num [numerator, reductionRhs, q] at h0
  rw [hA, hB] at h0
  field_simp [ha] at h0 ⊢
  linarith
theorem gap5 (a b c a₁ b₁ c₁ A B lam : ℝ) (ha : a ≠ 0)
    (hc : 8 * a ^ 2 * c₁ + 3 * a₁ * b ^ 2 =
      4 * a * (a₁ * c + b * b₁))
    (hred : ReductionIdentity a b c a₁ b₁ c₁ A B lam) :
    lam = 0 := by
  rw [gap4 a b c a₁ b₁ c₁ A B lam ha hred]
  rw [hc]
  ring
theorem gap6 (a b c a₁ b₁ c₁ : ℝ) (ha : a ≠ 0)
    (hc : 8 * a ^ 2 * c₁ + 3 * a₁ * b ^ 2 =
      4 * a * (a₁ * c + b * b₁)) :
    AlgebraicIntegrableOn (branch a b c) (integrand a b c a₁ b₁ c₁) := by
  let A := a₁ / (2 * a)
  let B := (4 * a * b₁ - 3 * a₁ * b) / (4 * a ^ 2)
  apply reduction_algebraic a b c a₁ b₁ c₁ A B
  intro x
  unfold numerator reductionRhs q A B
  field_simp [ha]
  nlinarith
theorem gap7 (a b c a₁ b₁ c₁ : ℝ) (ha : a = 0) :
    AlgebraicIntegrableOn (branch a b c) (integrand a b c a₁ b₁ c₁) := by
  subst a
  by_cases hb : b = 0
  · subst b
    let A := a₁ / (3 * Real.sqrt c)
    let B := b₁ / (2 * Real.sqrt c)
    let C := c₁ / Real.sqrt c
    refine ⟨cubicExpr A B C, ?_⟩
    intro x hx
    have hcpos : 0 < c := by simpa [branch, q] using hx
    have hs0 : Real.sqrt c ≠ 0 := (Real.sqrt_pos.2 hcpos).ne'
    have h :=
      (((hasDerivAt_id x).pow 3).const_mul A)
    have h3 : HasDerivAt (fun y : ℝ => A * y ^ 3) (3 * A * x ^ 2) x := by
      convert h using 1 <;> simp only [id_eq] <;> ring
    have h2 : HasDerivAt (fun y : ℝ => B * y ^ 2) (2 * B * x) x := by
      convert ((hasDerivAt_id x).pow 2).const_mul B using 1 <;>
        simp only [id_eq] <;> ring
    have h1 : HasDerivAt (fun y : ℝ => C * y) C x := by
      convert (hasDerivAt_id x).const_mul C using 1 <;> ring
    have hsum : HasDerivAt
        (fun y : ℝ => (A * y ^ 3 + B * y ^ 2) + C * y)
        ((3 * A * x ^ 2 + 2 * B * x) + C) x :=
      (h3.add h2).add h1
    have hcoef :
        A * (3 * x ^ 2) + B * (2 * x) + C =
          integrand 0 0 c a₁ b₁ c₁ x := by
      unfold integrand numerator q A B C
      field_simp [hs0]
      ring
    have h' := hsum.congr_deriv (by
      calc
        3 * A * x ^ 2 + 2 * B * x + C =
            A * (3 * x ^ 2) + B * (2 * x) + C := by ring
        _ = integrand 0 0 c a₁ b₁ c₁ x := hcoef)
    apply h'.congr_of_eventuallyEq
    filter_upwards [] with y
    simp only [cubicExpr, AlgebraicExpr.eval]
    ring
  · let A := 2 * a₁ / (5 * b)
    let B := 2 * (b₁ - 2 * A * c) / (3 * b)
    let C := 2 * (c₁ - B * c) / b
    refine ⟨polySqrtExpr A B C 0 b c, ?_⟩
    intro x hx
    have hq : 0 < q 0 b c x := hx
    have hs0 : Real.sqrt (q 0 b c x) ≠ 0 :=
      (Real.sqrt_pos.2 hq).ne'
    have hs2 : (Real.sqrt (q 0 b c x)) ^ 2 = q 0 b c x :=
      Real.sq_sqrt hq.le
    have hsder : HasDerivAt (fun y => Real.sqrt (q 0 b c y))
        (b / (2 * Real.sqrt (q 0 b c x))) x := by
      convert (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x
        (q_hasDerivAt 0 b c x) using 1 <;> ring
    have hp : HasDerivAt (fun y : ℝ => A * y ^ 2 + B * y + C)
        (2 * A * x + B) x := by
      have h2 : HasDerivAt (fun y : ℝ => A * y ^ 2) (2 * A * x) x := by
        convert ((hasDerivAt_id x).pow 2).const_mul A using 1 <;>
          simp only [id_eq] <;> ring
      have h1 : HasDerivAt (fun y : ℝ => B * y) B x := by
        convert (hasDerivAt_id x).const_mul B using 1 <;> ring
      convert HasDerivAt.add (HasDerivAt.add h2 h1)
        (hasDerivAt_const x C) using 1 <;> ring
    have h := hp.mul hsder
    have hcoef :
        (2 * A * x + B) * Real.sqrt (q 0 b c x) +
            (A * x ^ 2 + B * x + C) *
              (b / (2 * Real.sqrt (q 0 b c x))) =
          integrand 0 b c a₁ b₁ c₁ x := by
      unfold integrand numerator
      field_simp [hs0, hb]
      rw [hs2]
      unfold q
      dsimp [A, B, C]
      field_simp [hb]
      ring
    have h' := h.congr_deriv hcoef
    apply h'.congr_of_eventuallyEq
    filter_upwards [] with y
    simp only [polySqrtExpr, polyExpr, qExpr, AlgebraicExpr.eval]
    simp only [Pi.mul_apply]
    unfold q
    ring
theorem gap8 (a b c a₁ b₁ c₁ : ℝ)
    (hbranch : (branch a b c).Nonempty) :
    criterion a b c a₁ b₁ c₁ ↔
      AlgebraicIntegrableOn (branch a b c) (integrand a b c a₁ b₁ c₁) := by
  constructor
  · intro hcrit
    rcases hcrit with ha | hcoeff
    · exact gap7 a b c a₁ b₁ c₁ ha
    · by_cases ha : a = 0
      · exact gap7 a b c a₁ b₁ c₁ ha
      · exact gap6 a b c a₁ b₁ c₁ ha hcoeff
  · intro hint
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      let A := a₁ / (2 * a)
      let B := (4 * a * b₁ - 3 * a₁ * b) / (4 * a ^ 2)
      let lam :=
        (8 * a ^ 2 * c₁ + 3 * a₁ * b ^ 2 -
          4 * a * (a₁ * c + b * b₁)) / (8 * a ^ 2)
      have hred : ReductionIdentity a b c a₁ b₁ c₁ A B lam := by
        intro x
        unfold numerator reductionRhs q A B lam
        field_simp [ha]
        ring
      have hnecessary :=
        (gap1 a b c a₁ b₁ c₁ A B lam hbranch hred).mp hint
      have hlam : lam = 0 := hnecessary.resolve_left ha
      unfold lam at hlam
      field_simp [ha] at hlam
      linarith

end
end ProofGap.Exercise1951
