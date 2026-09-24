import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1136

noncomputable section

def rpow (x a : ℝ) : ℝ := Real.rpow x a
def y (u v : ℝ → ℝ) (m n x : ℝ) : ℝ :=
  rpow (u x) m * rpow (v x) n

def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun t => deriv f t) x

def TwiceDifferentiableAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε > 0,
    DifferentiableOn ℝ f (Set.Ioo (x - ε) (x + ε)) ∧
      DifferentiableAt ℝ (fun t => deriv f t) x

def expanded (u v : ℝ → ℝ) (m n x : ℝ) : ℝ :=
  m * (m - 1) * rpow (u x) (m - 2) * rpow (v x) n * deriv u x ^ 2 +
    m * rpow (u x) (m - 1) *
      (rpow (v x) n * secondDeriv u x +
        n * rpow (v x) (n - 1) * deriv u x * deriv v x) +
    m * n * rpow (u x) (m - 1) * rpow (v x) (n - 1) *
      deriv u x * deriv v x +
    n * (n - 1) * rpow (u x) m * rpow (v x) (n - 2) * deriv v x ^ 2 +
    n * rpow (u x) m * rpow (v x) (n - 1) * secondDeriv v x

def finalForm (u v : ℝ → ℝ) (m n x : ℝ) : ℝ :=
  rpow (u x) (m - 2) * rpow (v x) (n - 2) *
    (m * (m - 1) * v x ^ 2 * deriv u x ^ 2 +
      2 * m * n * u x * v x * deriv u x * deriv v x +
      n * (n - 1) * u x ^ 2 * deriv v x ^ 2 +
      u x * v x *
        (m * v x * secondDeriv u x + n * u x * secondDeriv v x))

private theorem rpow_step (a s : ℝ) (ha : 0 < a) :
    rpow a s = rpow a (s - 1) * a := by
  have hs : rpow a s = Real.exp (Real.log a * s) := by
    unfold rpow
    exact Real.rpow_def_of_pos ha s
  have hsm : rpow a (s - 1) = Real.exp (Real.log a * (s - 1)) := by
    unfold rpow
    exact Real.rpow_def_of_pos ha (s - 1)
  calc
    rpow a s = Real.exp (Real.log a * s) := hs
    _ = Real.exp (Real.log a * (s - 1)) * Real.exp (Real.log a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = rpow a (s - 1) * a :=
      congrArg₂ (fun p q : ℝ => p * q) hsm.symm (Real.exp_log ha)

private theorem rpow_sub_one_step (a s : ℝ) (ha : 0 < a) :
    rpow a (s - 1) = rpow a (s - 2) * a := by
  convert rpow_step a (s - 1) ha using 1 <;> ring

private theorem hasDerivAt_rpow_comp {f : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hpos : 0 < f x) (a : ℝ) :
    HasDerivAt (fun t => rpow (f t) a)
      (a * rpow (f x) (a - 1) * deriv f x) x := by
  unfold rpow
  convert (Real.hasDerivAt_rpow_const (p := a)
    (Or.inl (ne_of_gt hpos))).comp x hf.hasDerivAt using 1 <;> ring

theorem gap1 (u v : ℝ → ℝ) (m n x : ℝ)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (hupos : 0 < u x) (hvpos : 0 < v x) :
    deriv (y u v m n) x =
      m * rpow (u x) (m - 1) * rpow (v x) n * deriv u x +
        n * rpow (u x) m * rpow (v x) (n - 1) * deriv v x := by
  unfold y
  have hu' := hasDerivAt_rpow_comp hu hupos m
  have hv' := hasDerivAt_rpow_comp hv hvpos n
  convert (hu'.mul hv').deriv using 1 <;> ring

theorem gap2 (u v : ℝ → ℝ) (m n x : ℝ)
    (hu : TwiceDifferentiableAt u x) (hv : TwiceDifferentiableAt v x)
    (hupos : 0 < u x) (hvpos : 0 < v x) :
    secondDeriv (y u v m n) x = expanded u v m n x := by
  rcases hu with ⟨εu, hεu, huOn, huDeriv⟩
  rcases hv with ⟨εv, hεv, hvOn, hvDeriv⟩
  have hxu : x ∈ Set.Ioo (x - εu) (x + εu) := by
    constructor <;> linarith
  have hxv : x ∈ Set.Ioo (x - εv) (x + εv) := by
    constructor <;> linarith
  have hIu : Set.Ioo (x - εu) (x + εu) ∈ nhds x :=
    Ioo_mem_nhds hxu.1 hxu.2
  have hIv : Set.Ioo (x - εv) (x + εv) ∈ nhds x :=
    Ioo_mem_nhds hxv.1 hxv.2
  have huAt : DifferentiableAt ℝ u x :=
    (huOn x hxu).differentiableAt hIu
  have hvAt : DifferentiableAt ℝ v x :=
    (hvOn x hxv).differentiableAt hIv
  have huPosN : ∀ᶠ t in nhds x, 0 < u t :=
    huAt.continuousAt.eventually (Ioi_mem_nhds hupos)
  have hvPosN : ∀ᶠ t in nhds x, 0 < v t :=
    hvAt.continuousAt.eventually (Ioi_mem_nhds hvpos)
  let F : ℝ → ℝ := fun t =>
    m * rpow (u t) (m - 1) * rpow (v t) n * deriv u t +
      n * rpow (u t) m * rpow (v t) (n - 1) * deriv v t
  have heq : (fun t => deriv (y u v m n) t) =ᶠ[nhds x] F := by
    filter_upwards [hIu, hIv, huPosN, hvPosN] with t htu htv hut hvt
    dsimp [F]
    exact gap1 u v m n t
      ((huOn t htu).differentiableAt (Ioo_mem_nhds htu.1 htu.2))
      ((hvOn t htv).differentiableAt (Ioo_mem_nhds htv.1 htv.2)) hut hvt
  have hdu : HasDerivAt (fun t => deriv u t) (secondDeriv u x) x := by
    simpa only [secondDeriv] using huDeriv.hasDerivAt
  have hdv : HasDerivAt (fun t => deriv v t) (secondDeriv v x) x := by
    simpa only [secondDeriv] using hvDeriv.hasDerivAt
  have hUm1 : HasDerivAt (fun t => rpow (u t) (m - 1))
      ((m - 1) * rpow (u x) (m - 2) * deriv u x) x := by
    convert hasDerivAt_rpow_comp huAt hupos (m - 1) using 1 <;> ring
  have hUm := hasDerivAt_rpow_comp huAt hupos m
  have hVn := hasDerivAt_rpow_comp hvAt hvpos n
  have hVn1 : HasDerivAt (fun t => rpow (v t) (n - 1))
      ((n - 1) * rpow (v x) (n - 2) * deriv v x) x := by
    convert hasDerivAt_rpow_comp hvAt hvpos (n - 1) using 1 <;> ring
  have hA := ((hUm1.mul hVn).mul hdu).const_mul m
  have hB := ((hUm.mul hVn1).mul hdv).const_mul n
  have hF : HasDerivAt F (expanded u v m n x) x := by
    dsimp [F]
    convert hA.add hB using 1
    · funext t
      simp only [Pi.add_apply, Pi.mul_apply]
      ring
    · unfold expanded secondDeriv
      simp only [Pi.mul_apply]
      ring
  unfold secondDeriv
  calc
    deriv (fun t => deriv (y u v m n) t) x = deriv F x := heq.deriv_eq
    _ = expanded u v m n x := hF.deriv

theorem gap3 (u v : ℝ → ℝ) (m n x : ℝ)
    (hupos : 0 < u x) (hvpos : 0 < v x) :
    expanded u v m n x = finalForm u v m n x := by
  unfold expanded finalForm
  rw [rpow_step (u x) m hupos, rpow_step (v x) n hvpos,
    rpow_sub_one_step (u x) m hupos,
    rpow_sub_one_step (v x) n hvpos]
  ring

theorem gap4 (u v : ℝ → ℝ) (m n x : ℝ)
    (hu : TwiceDifferentiableAt u x) (hv : TwiceDifferentiableAt v x)
    (hupos : 0 < u x) (hvpos : 0 < v x) :
    secondDeriv (y u v m n) x = finalForm u v m n x := by
  calc
    secondDeriv (y u v m n) x = expanded u v m n x :=
      gap2 u v m n x hu hv hupos hvpos
    _ = finalForm u v m n x := gap3 u v m n x hupos hvpos

end

end ProofGap.Exercise1136
