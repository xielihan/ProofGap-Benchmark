import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3391

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f x t) y

def differential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX f x y * dx + partialY f x y * dy

def secondDifferential (f : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  partialXX f x y * dx ^ 2 +
    2 * partialXY f x y * dx * dy +
    partialYY f x y * dy ^ 2

def solvedDifferential (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  -((1 - y * z x y) * dx + (1 - x * z x y) * dy) / (1 - x * y)

def firstSecondForm (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  -(2 / (1 - x * y) ^ 2) *
    (y * (1 - y * z x y) * dx ^ 2 +
      (x + y - z x y * (1 + x * y)) * dx * dy +
      x * (1 - x * z x y) * dy ^ 2)

def alternateSecondForm (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  -(2 *
    (y * (1 - y * z x y) * dx ^ 2 -
      2 * z x y * dx * dy +
      x * (1 - x * z x y) * dy ^ 2)) / (1 - x * y) ^ 2

private lemma differentiableAt_pair_left (a c : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => (t, c)) a := by
  have hi : DifferentiableAt ℝ (fun t : ℝ => t) a := differentiableAt_id
  have hc : DifferentiableAt ℝ (fun _ : ℝ => c) a := differentiableAt_const c
  exact hi.prodMk hc

private lemma differentiableAt_pair_right (a c : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => (c, t)) a := by
  have hc : DifferentiableAt ℝ (fun _ : ℝ => c) a := differentiableAt_const c
  have hi : DifferentiableAt ℝ (fun t : ℝ => t) a := differentiableAt_id
  exact hc.prodMk hi

private lemma implicitDenominator_ne (u v w : ℝ)
    (h : u * v * w = u + v + w) : u * v - 1 ≠ 0 := by
  intro hd
  have huv : u * v = 1 := by linarith
  have hsum : u + v = 0 := by
    calc
      u + v = u * v * w - w := by linarith [h]
      _ = (u * v - 1) * w := by ring
      _ = 0 := by rw [hd]; ring
  have hv : v = -u := by linarith
  rw [hv] at huv
  nlinarith [sq_nonneg u]

private lemma implicitSolution_hasDerivAt_x (u v : ℝ)
    (h : u * v - 1 ≠ 0) :
    HasDerivAt (fun t : ℝ => (t + v) / (t * v - 1))
      (-(1 + v ^ 2) / (u * v - 1) ^ 2) u := by
  have hn : HasDerivAt (fun t : ℝ => t + v) 1 u := by
    convert (hasDerivAt_id u).add
      (hasDerivAt_const (x := u) (c := v)) using 1 <;> ring_nf
  have hd : HasDerivAt (fun t : ℝ => t * v - 1) v u := by
    convert ((hasDerivAt_id u).mul
      (hasDerivAt_const (x := u) (c := v))).sub
        (hasDerivAt_const (x := u) (c := (1 : ℝ))) using 1 <;> ring_nf
  convert hn.div hd h using 1 <;> field_simp [h] <;> ring_nf

private lemma implicitSolution_hasDerivAt_y (u v : ℝ)
    (h : u * v - 1 ≠ 0) :
    HasDerivAt (fun t : ℝ => (u + t) / (u * t - 1))
      (-(1 + u ^ 2) / (u * v - 1) ^ 2) v := by
  have hn : HasDerivAt (fun t : ℝ => u + t) 1 v := by
    convert (hasDerivAt_const (x := v) (c := u)).add
      (hasDerivAt_id v) using 1 <;> ring_nf
  have hd : HasDerivAt (fun t : ℝ => u * t - 1) u v := by
    convert ((hasDerivAt_const (x := v) (c := u)).mul
      (hasDerivAt_id v)).sub
        (hasDerivAt_const (x := v) (c := (1 : ℝ))) using 1 <;> ring_nf
  convert hn.div hd h using 1 <;> field_simp [h] <;> ring_nf

private lemma implicitSolutionX_hasDerivAt_x (u v : ℝ)
    (h : u * v - 1 ≠ 0) :
    HasDerivAt (fun t : ℝ => -(1 + v ^ 2) / (t * v - 1) ^ 2)
      (2 * v * (1 + v ^ 2) / (u * v - 1) ^ 3) u := by
  have hn : HasDerivAt (fun _ : ℝ => -(1 + v ^ 2)) 0 u :=
    hasDerivAt_const (x := u) (c := -(1 + v ^ 2))
  have hb : HasDerivAt (fun t : ℝ => t * v - 1) v u := by
    convert ((hasDerivAt_id u).mul
      (hasDerivAt_const (x := u) (c := v))).sub
        (hasDerivAt_const (x := u) (c := (1 : ℝ))) using 1 <;> ring_nf
  have hd : HasDerivAt (fun t : ℝ => (t * v - 1) ^ 2)
      (2 * v * (u * v - 1)) u := by
    convert hb.mul hb using 1
    · funext t
      simp [pow_two]
    · ring
  convert hn.div hd (pow_ne_zero 2 h) using 1 <;>
    field_simp [h] <;> ring_nf

private lemma implicitSolutionX_hasDerivAt_y (u v : ℝ)
    (h : u * v - 1 ≠ 0) :
    HasDerivAt (fun t : ℝ => -(1 + t ^ 2) / (u * t - 1) ^ 2)
      (2 * (u + v) / (u * v - 1) ^ 3) v := by
  have hi : HasDerivAt (fun t : ℝ => t) 1 v := hasDerivAt_id v
  have hs : HasDerivAt (fun t : ℝ => t ^ 2) (2 * v) v := by
    convert hi.mul hi using 1
    · funext t
      simp [pow_two]
    · ring
  have hn : HasDerivAt (fun t : ℝ => -(1 + t ^ 2)) (-2 * v) v := by
    convert ((hasDerivAt_const (x := v) (c := (1 : ℝ))).add hs).neg using 1 <;> ring_nf
  have hb : HasDerivAt (fun t : ℝ => u * t - 1) u v := by
    convert ((hasDerivAt_const (x := v) (c := u)).mul
      (hasDerivAt_id v)).sub
        (hasDerivAt_const (x := v) (c := (1 : ℝ))) using 1 <;> ring_nf
  have hd : HasDerivAt (fun t : ℝ => (u * t - 1) ^ 2)
      (2 * u * (u * v - 1)) v := by
    convert hb.mul hb using 1
    · funext t
      simp [pow_two]
    · ring
  convert hn.div hd (pow_ne_zero 2 h) using 1 <;>
    field_simp [h] <;> ring_nf

private lemma implicitSolutionY_hasDerivAt_y (u v : ℝ)
    (h : u * v - 1 ≠ 0) :
    HasDerivAt (fun t : ℝ => -(1 + u ^ 2) / (u * t - 1) ^ 2)
      (2 * u * (1 + u ^ 2) / (u * v - 1) ^ 3) v := by
  have hn : HasDerivAt (fun _ : ℝ => -(1 + u ^ 2)) 0 v :=
    hasDerivAt_const (x := v) (c := -(1 + u ^ 2))
  have hb : HasDerivAt (fun t : ℝ => u * t - 1) u v := by
    convert ((hasDerivAt_const (x := v) (c := u)).mul
      (hasDerivAt_id v)).sub
        (hasDerivAt_const (x := v) (c := (1 : ℝ))) using 1 <;> ring_nf
  have hd : HasDerivAt (fun t : ℝ => (u * t - 1) ^ 2)
      (2 * u * (u * v - 1)) v := by
    convert hb.mul hb using 1
    · funext t
      simp [pow_two]
    · ring
  convert hn.div hd (pow_ne_zero 2 h) using 1 <;>
    field_simp [h] <;> ring_nf

theorem gap1 (x y dx dy : ℝ) (z : ℝ → ℝ → ℝ)
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hImplicit :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        p.1 * p.2 * z p.1 p.2 = p.1 + p.2 + z p.1 p.2) :
    y * z x y * dx + x * z x y * dy +
      x * y * differential z x y dx dy =
        dx + dy + differential z x y dx dy := by
  have hxMap : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x :=
    differentiableAt_pair_left x y
  have hyMap : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y :=
    differentiableAt_pair_right y x
  have hxDiff : DifferentiableAt ℝ (fun t : ℝ => z t y) x := by
    simpa [Function.uncurry] using hzDiff.comp x hxMap
  have hyDiff : DifferentiableAt ℝ (fun t : ℝ => z x t) y := by
    simpa [Function.uncurry] using hzDiff.comp y hyMap
  have hxPair := hxMap.continuousAt.tendsto
  have hyPair := hyMap.continuousAt.tendsto
  have hxEq :
      (fun t : ℝ => t * y * z t y) =ᶠ[nhds x]
        (fun t : ℝ => t + y + z t y) := by
    filter_upwards [hxPair.eventually hImplicit] with t ht
    simpa using ht
  have hyEq :
      (fun t : ℝ => x * t * z x t) =ᶠ[nhds y]
        (fun t : ℝ => x + t + z x t) := by
    filter_upwards [hyPair.eventually hImplicit] with t ht
    simpa using ht
  have hxLeft :
      HasDerivAt (fun t : ℝ => t * y * z t y)
        (y * z x y + x * y * partialX z x y) x := by
    simpa [partialX] using
      (((hasDerivAt_id x).mul
        (hasDerivAt_const (x := x) (c := y))).mul hxDiff.hasDerivAt)
  have hxRight :
      HasDerivAt (fun t : ℝ => t + y + z t y)
        (1 + partialX z x y) x := by
    simpa [partialX] using
      (((hasDerivAt_id x).add
        (hasDerivAt_const (x := x) (c := y))).add hxDiff.hasDerivAt)
  have hyLeft :
      HasDerivAt (fun t : ℝ => x * t * z x t)
        (x * z x y + x * y * partialY z x y) y := by
    simpa [partialY] using
      (((hasDerivAt_const (x := y) (c := x)).mul
        (hasDerivAt_id y)).mul hyDiff.hasDerivAt)
  have hyRight :
      HasDerivAt (fun t : ℝ => x + t + z x t)
        (1 + partialY z x y) y := by
    simpa [partialY] using
      (((hasDerivAt_const (x := y) (c := x)).add
        (hasDerivAt_id y)).add hyDiff.hasDerivAt)
  have hxRelation :
      y * z x y + x * y * partialX z x y = 1 + partialX z x y := by
    calc
      y * z x y + x * y * partialX z x y =
          deriv (fun t : ℝ => t * y * z t y) x := hxLeft.deriv.symm
      _ = deriv (fun t : ℝ => t + y + z t y) x := hxEq.deriv_eq
      _ = 1 + partialX z x y := hxRight.deriv
  have hyRelation :
      x * z x y + x * y * partialY z x y = 1 + partialY z x y := by
    calc
      x * z x y + x * y * partialY z x y =
          deriv (fun t : ℝ => x * t * z x t) y := hyLeft.deriv.symm
      _ = deriv (fun t : ℝ => x + t + z x t) y := hyEq.deriv_eq
      _ = 1 + partialY z x y := hyRight.deriv
  unfold differential
  calc
    y * z x y * dx + x * z x y * dy +
          x * y * (partialX z x y * dx + partialY z x y * dy) =
        (y * z x y + x * y * partialX z x y) * dx +
          (x * z x y + x * y * partialY z x y) * dy := by ring
    _ = (1 + partialX z x y) * dx +
          (1 + partialY z x y) * dy := by rw [hxRelation, hyRelation]
    _ = dx + dy +
          (partialX z x y * dx + partialY z x y * dy) := by ring

theorem gap2 (x y dx dy : ℝ) (z : ℝ → ℝ → ℝ)
    (hNonzero : 1 - x * y ≠ 0)
    (hFirst :
      y * z x y * dx + x * z x y * dy +
        x * y * differential z x y dx dy =
          dx + dy + differential z x y dx dy) :
    differential z x y dx dy =
      solvedDifferential z x y dx dy := by
  unfold solvedDifferential
  apply (eq_div_iff hNonzero).2
  ring_nf at hFirst ⊢
  linarith

theorem gap3 (x y dx dy : ℝ) (z : ℝ → ℝ → ℝ)
    (hzC2 : ContDiffAt ℝ 2 (Function.uncurry z) (x, y))
    (hImplicit :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        p.1 * p.2 * z p.1 p.2 = p.1 + p.2 + z p.1 p.2) :
    2 * z x y * dx * dy +
      2 * x * dy * differential z x y dx dy +
      2 * y * dx * differential z x y dx dy +
      x * y * secondDifferential z x y dx dy =
        secondDifferential z x y dx dy := by
  let S : Set (ℝ × ℝ) :=
    {p | p.1 * p.2 * z p.1 p.2 = p.1 + p.2 + z p.1 p.2}
  have hS : S ∈ nhds (x, y) := by
    simpa [S] using hImplicit
  have hxyInt : (x, y) ∈ interior S :=
    mem_interior_iff_mem_nhds.mpr hS
  have hEquation : ∀ {u v : ℝ}, (u, v) ∈ interior S →
      u * v * z u v = u + v + z u v := by
    intro u v huv
    have hmem : (u, v) ∈ S :=
      (show interior S ⊆ S from interior_subset) huv
    simpa [S] using hmem
  have hSol : ∀ (u v : ℝ), (u, v) ∈ interior S →
      z u v = (u + v) / (u * v - 1) := by
    intro u v huv
    have heq : u * v * z u v = u + v + z u v := hEquation huv
    apply (eq_div_iff (implicitDenominator_ne u v (z u v) heq)).2
    nlinarith
  have hZX : ∀ (u v : ℝ), (u, v) ∈ interior S →
      (fun t : ℝ => z t v) =ᶠ[nhds u]
        (fun t : ℝ => (t + v) / (t * v - 1)) := by
    intro u v huv
    have hmap : Filter.Tendsto (fun t : ℝ => (t, v))
        (nhds u) (nhds (u, v)) :=
      (differentiableAt_pair_left u v).continuousAt.tendsto
    filter_upwards [hmap.eventually (isOpen_interior.mem_nhds huv)] with t ht
    exact hSol t v ht
  have hZY : ∀ (u v : ℝ), (u, v) ∈ interior S →
      (fun t : ℝ => z u t) =ᶠ[nhds v]
        (fun t : ℝ => (u + t) / (u * t - 1)) := by
    intro u v huv
    have hmap : Filter.Tendsto (fun t : ℝ => (u, t))
        (nhds v) (nhds (u, v)) :=
      (differentiableAt_pair_right v u).continuousAt.tendsto
    filter_upwards [hmap.eventually (isOpen_interior.mem_nhds huv)] with t ht
    exact hSol u t ht
  have hbaseEq : x * y * z x y = x + y + z x y :=
    hEquation hxyInt
  have hd : x * y - 1 ≠ 0 :=
    implicitDenominator_ne x y (z x y) hbaseEq
  have hz : z x y = (x + y) / (x * y - 1) := hSol x y hxyInt
  have hxMap : Filter.Tendsto (fun t : ℝ => (t, y))
      (nhds x) (nhds (x, y)) :=
    (differentiableAt_pair_left x y).continuousAt.tendsto
  have hxNear : ∀ᶠ u : ℝ in nhds x, (u, y) ∈ interior S :=
    hxMap.eventually (isOpen_interior.mem_nhds hxyInt)
  have hyMap : Filter.Tendsto (fun t : ℝ => (x, t))
      (nhds y) (nhds (x, y)) :=
    (differentiableAt_pair_right y x).continuousAt.tendsto
  have hyNear : ∀ᶠ v : ℝ in nhds y, (x, v) ∈ interior S :=
    hyMap.eventually (isOpen_interior.mem_nhds hxyInt)
  have hPXNearX :
      (fun u : ℝ => partialX z u y) =ᶠ[nhds x]
        (fun u : ℝ => -(1 + y ^ 2) / (u * y - 1) ^ 2) := by
    filter_upwards [hxNear] with u hu
    have heq : u * y * z u y = u + y + z u y := hEquation hu
    have hdu : u * y - 1 ≠ 0 :=
      implicitDenominator_ne u y (z u y) heq
    unfold partialX
    calc
      deriv (fun t : ℝ => z t y) u =
          deriv (fun t : ℝ => (t + y) / (t * y - 1)) u :=
        (hZX u y hu).deriv_eq
      _ = -(1 + y ^ 2) / (u * y - 1) ^ 2 :=
        (implicitSolution_hasDerivAt_x u y hdu).deriv
  have hPXNearY :
      (fun v : ℝ => partialX z x v) =ᶠ[nhds y]
        (fun v : ℝ => -(1 + v ^ 2) / (x * v - 1) ^ 2) := by
    filter_upwards [hyNear] with v hv
    have heq : x * v * z x v = x + v + z x v := hEquation hv
    have hdv : x * v - 1 ≠ 0 :=
      implicitDenominator_ne x v (z x v) heq
    unfold partialX
    calc
      deriv (fun t : ℝ => z t v) x =
          deriv (fun t : ℝ => (t + v) / (t * v - 1)) x :=
        (hZX x v hv).deriv_eq
      _ = -(1 + v ^ 2) / (x * v - 1) ^ 2 :=
        (implicitSolution_hasDerivAt_x x v hdv).deriv
  have hPYNearY :
      (fun v : ℝ => partialY z x v) =ᶠ[nhds y]
        (fun v : ℝ => -(1 + x ^ 2) / (x * v - 1) ^ 2) := by
    filter_upwards [hyNear] with v hv
    have heq : x * v * z x v = x + v + z x v := hEquation hv
    have hdv : x * v - 1 ≠ 0 :=
      implicitDenominator_ne x v (z x v) heq
    unfold partialY
    calc
      deriv (fun t : ℝ => z x t) v =
          deriv (fun t : ℝ => (x + t) / (x * t - 1)) v :=
        (hZY x v hv).deriv_eq
      _ = -(1 + x ^ 2) / (x * v - 1) ^ 2 :=
        (implicitSolution_hasDerivAt_y x v hdv).deriv
  have hPX : partialX z x y = -(1 + y ^ 2) / (x * y - 1) ^ 2 := by
    unfold partialX
    calc
      deriv (fun t : ℝ => z t y) x =
          deriv (fun t : ℝ => (t + y) / (t * y - 1)) x :=
        (hZX x y hxyInt).deriv_eq
      _ = -(1 + y ^ 2) / (x * y - 1) ^ 2 :=
        (implicitSolution_hasDerivAt_x x y hd).deriv
  have hPY : partialY z x y = -(1 + x ^ 2) / (x * y - 1) ^ 2 := by
    unfold partialY
    calc
      deriv (fun t : ℝ => z x t) y =
          deriv (fun t : ℝ => (x + t) / (x * t - 1)) y :=
        (hZY x y hxyInt).deriv_eq
      _ = -(1 + x ^ 2) / (x * y - 1) ^ 2 :=
        (implicitSolution_hasDerivAt_y x y hd).deriv
  have hPXX :
      partialXX z x y = 2 * y * (1 + y ^ 2) / (x * y - 1) ^ 3 := by
    unfold partialXX
    calc
      deriv (fun t : ℝ => partialX z t y) x =
          deriv (fun t : ℝ => -(1 + y ^ 2) / (t * y - 1) ^ 2) x :=
        hPXNearX.deriv_eq
      _ = 2 * y * (1 + y ^ 2) / (x * y - 1) ^ 3 :=
        (implicitSolutionX_hasDerivAt_x x y hd).deriv
  have hPXY :
      partialXY z x y = 2 * (x + y) / (x * y - 1) ^ 3 := by
    unfold partialXY
    calc
      deriv (fun t : ℝ => partialX z x t) y =
          deriv (fun t : ℝ => -(1 + t ^ 2) / (x * t - 1) ^ 2) y :=
        hPXNearY.deriv_eq
      _ = 2 * (x + y) / (x * y - 1) ^ 3 :=
        (implicitSolutionX_hasDerivAt_y x y hd).deriv
  have hPYY :
      partialYY z x y = 2 * x * (1 + x ^ 2) / (x * y - 1) ^ 3 := by
    unfold partialYY
    calc
      deriv (fun t : ℝ => partialY z x t) y =
          deriv (fun t : ℝ => -(1 + x ^ 2) / (x * t - 1) ^ 2) y :=
        hPYNearY.deriv_eq
      _ = 2 * x * (1 + x ^ 2) / (x * y - 1) ^ 3 :=
        (implicitSolutionY_hasDerivAt_y x y hd).deriv
  unfold differential secondDifferential
  rw [hz, hPX, hPY, hPXX, hPXY, hPYY]
  field_simp [hd] <;> ring

theorem gap4 (x y dx dy : ℝ) (z : ℝ → ℝ → ℝ)
    (hNonzero : 1 - x * y ≠ 0)
    (hImplicit : x * y * z x y = x + y + z x y)
    (hFirst :
      differential z x y dx dy =
        solvedDifferential z x y dx dy)
    (hSecond :
      2 * z x y * dx * dy +
        2 * x * dy * differential z x y dx dy +
        2 * y * dx * differential z x y dx dy +
        x * y * secondDifferential z x y dx dy =
          secondDifferential z x y dx dy) :
    secondDifferential z x y dx dy =
      firstSecondForm z x y dx dy := by
  have hCross :
      x + y - z x y * (1 + x * y) = -2 * z x y := by
    ring_nf at hImplicit ⊢
    linarith
  have hSolvedSecond :
      secondDifferential z x y dx dy =
        (2 * z x y * dx * dy +
          2 * x * dy * differential z x y dx dy +
          2 * y * dx * differential z x y dx dy) / (1 - x * y) := by
    apply (eq_div_iff hNonzero).2
    ring_nf at hSecond ⊢
    linarith
  rw [hSolvedSecond, hFirst]
  unfold solvedDifferential firstSecondForm
  rw [hCross]
  field_simp [hNonzero]
  linear_combination (-dx * dy) * hCross

theorem gap5 (x y dx dy : ℝ) (z : ℝ → ℝ → ℝ)
    (hImplicit : x * y * z x y = x + y + z x y) :
    firstSecondForm z x y dx dy =
      alternateSecondForm z x y dx dy := by
  have hCross :
      x + y - z x y * (1 + x * y) = -2 * z x y := by
    ring_nf at hImplicit ⊢
    linarith
  unfold firstSecondForm alternateSecondForm
  rw [hCross]
  ring

theorem gap6 (x y dx dy : ℝ) (z : ℝ → ℝ → ℝ)
    (hFirstForm :
      secondDifferential z x y dx dy =
        firstSecondForm z x y dx dy)
    (hEquivalentForms :
      firstSecondForm z x y dx dy =
        alternateSecondForm z x y dx dy) :
    secondDifferential z x y dx dy =
      alternateSecondForm z x y dx dy := by
  exact hFirstForm.trans hEquivalentForms

end

end ProofGap.Exercise3391
