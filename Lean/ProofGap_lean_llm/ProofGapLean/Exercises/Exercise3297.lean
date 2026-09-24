import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3297

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def nthDifferential (n : ℕ) (u : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ) : ℝ :=
  iterDeriv n
    (fun s => u (x + s * dx) (y + s * dy) (z + s * dz)) 0

def partial1 (f : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => f t b) a

def partial2 (f : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => f a t) b

def partial11 (f : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  (deriv^[2]) (fun t => f t b) a

def partial12 (f : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => partial1 f a t) b

def partial22 (f : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  (deriv^[2]) (fun t => f a t) b

def uncurry₂ (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => f p.1 p.2

def coordinateSum (x y z : ℝ) : ℝ :=
  x + y + z

def squareSum (x y z : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 + z ^ 2

def directionSum (dx dy dz : ℝ) : ℝ :=
  dx + dy + dz

def radialPairing (x y z dx dy dz : ℝ) : ℝ :=
  x * dx + y * dy + z * dz

private theorem partial1_eq_fderiv (f : ℝ → ℝ → ℝ) {a b : ℝ}
    (hf : DifferentiableAt ℝ (uncurry₂ f) (a, b)) :
    partial1 f a b = fderiv ℝ (uncurry₂ f) (a, b) (1, 0) := by
  have h :=
    hf.hasFDerivAt.comp a
      ((hasDerivAt_id a).prodMk
        (hasDerivAt_const (x := a) (c := b)))
  simpa [partial1, uncurry₂, Function.comp_def] using h.hasDerivAt.deriv

private theorem partial2_eq_fderiv (f : ℝ → ℝ → ℝ) {a b : ℝ}
    (hf : DifferentiableAt ℝ (uncurry₂ f) (a, b)) :
    partial2 f a b = fderiv ℝ (uncurry₂ f) (a, b) (0, 1) := by
  have h :=
    hf.hasFDerivAt.comp b
      ((hasDerivAt_const (x := b) (c := a)).prodMk
        (hasDerivAt_id b))
  simpa [partial2, uncurry₂, Function.comp_def] using h.hasDerivAt.deriv

private theorem hasDerivAt_uncurry₂_chain (f : ℝ → ℝ → ℝ)
    {A B : ℝ → ℝ} {s dA dB : ℝ}
    (hf : DifferentiableAt ℝ (uncurry₂ f) (A s, B s))
    (hA : HasDerivAt A dA s) (hB : HasDerivAt B dB s) :
    HasDerivAt (fun t => f (A t) (B t))
      (partial1 f (A s) (B s) * dA + partial2 f (A s) (B s) * dB) s := by
  have hcomp := hf.hasFDerivAt.comp s (hA.prodMk hB)
  have hd : HasDerivAt (fun t => f (A t) (B t))
      (fderiv ℝ (uncurry₂ f) (A s, B s) (dA, dB)) s := by
    simpa [uncurry₂, Function.comp_def] using hcomp.hasDerivAt
  convert hd using 1
  rw [show (dA, dB) = dA • (1, 0) + dB • (0, 1) by ext <;> simp]
  rw [map_add, map_smul, map_smul]
  rw [← partial1_eq_fderiv f hf, ← partial2_eq_fderiv f hf]
  simp [smul_eq_mul]
  ring

theorem gap1 (u : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (coordinateSum x y z) (squareSum x y z))
    (hf : ContDiff ℝ 1 (uncurry₂ f))
    (x y z dx dy dz : ℝ) :
    nthDifferential 1 u x y z dx dy dz =
      partial1 f (coordinateSum x y z) (squareSum x y z) *
          directionSum dx dy dz +
        2 * partial2 f (coordinateSum x y z) (squareSum x y z) *
          radialPairing x y z dx dy dz := by
  have hfd : Differentiable ℝ (uncurry₂ f) :=
    hf.differentiable (by decide)
  change deriv (fun s => u (x + s * dx) (y + s * dy) (z + s * dz)) 0 = _
  simp_rw [hu]
  unfold coordinateSum squareSum directionSum radialPairing
  have hx : HasDerivAt (fun s : ℝ => x + s * dx) dx 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const dx).const_add x
  have hy : HasDerivAt (fun s : ℝ => y + s * dy) dy 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const dy).const_add y
  have hz : HasDerivAt (fun s : ℝ => z + s * dz) dz 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const dz).const_add z
  have hA : HasDerivAt
      (fun s : ℝ => x + s * dx + (y + s * dy) + (z + s * dz))
      (dx + dy + dz) 0 :=
    (hx.add hy).add hz
  have hB : HasDerivAt
      (fun s : ℝ => (x + s * dx) ^ 2 + (y + s * dy) ^ 2 +
        (z + s * dz) ^ 2)
      (2 * (x * dx + y * dy + z * dz)) 0 := by
    convert ((hx.pow 2).add (hy.pow 2)).add (hz.pow 2) using 1 <;> ring
  convert (hasDerivAt_uncurry₂_chain f hfd.differentiableAt hA hB).deriv using 1 <;> ring

theorem gap2 (u : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (coordinateSum x y z) (squareSum x y z))
    (hf : ContDiff ℝ 2 (uncurry₂ f))
    (x y z dx dy dz : ℝ) :
    nthDifferential 2 u x y z dx dy dz =
      partial11 f (coordinateSum x y z) (squareSum x y z) *
          (directionSum dx dy dz) ^ 2 +
        4 * partial12 f (coordinateSum x y z) (squareSum x y z) *
          directionSum dx dy dz * radialPairing x y z dx dy dz +
        4 * partial22 f (coordinateSum x y z) (squareSum x y z) *
          (radialPairing x y z dx dy dz) ^ 2 +
        2 * partial2 f (coordinateSum x y z) (squareSum x y z) *
          (dx ^ 2 + dy ^ 2 + dz ^ 2) := by
  have hF : Differentiable ℝ (uncurry₂ f) :=
    hf.differentiable (by decide)
  have hDFc : ContDiff ℝ 1 (fderiv ℝ (uncurry₂ f)) :=
    hf.fderiv_right (by norm_num)
  have hDF : Differentiable ℝ (fderiv ℝ (uncurry₂ f)) :=
    hDFc.differentiable (by decide)
  change deriv (deriv (fun s => u (x + s * dx) (y + s * dy)
    (z + s * dz))) 0 = _
  simp_rw [hu]
  unfold coordinateSum squareSum directionSum radialPairing
    partial11 partial12 partial22
  let A : ℝ → ℝ := fun s => x + s * dx + (y + s * dy) + (z + s * dz)
  let B : ℝ → ℝ := fun s => (x + s * dx) ^ 2 + (y + s * dy) ^ 2 +
    (z + s * dz) ^ 2
  let R : ℝ → ℝ := fun s =>
    (x + s * dx) * dx + (y + s * dy) * dy + (z + s * dz) * dz
  let ds : ℝ := dx + dy + dz
  let q : ℝ := dx ^ 2 + dy ^ 2 + dz ^ 2
  have hA (s : ℝ) : HasDerivAt A ds s := by
    dsimp [A, ds]
    have hx : HasDerivAt (fun t : ℝ => x + t * dx) dx s := by
      simpa using ((hasDerivAt_id s).mul_const dx).const_add x
    have hy : HasDerivAt (fun t : ℝ => y + t * dy) dy s := by
      simpa using ((hasDerivAt_id s).mul_const dy).const_add y
    have hz : HasDerivAt (fun t : ℝ => z + t * dz) dz s := by
      simpa using ((hasDerivAt_id s).mul_const dz).const_add z
    exact (hx.add hy).add hz
  have hB (s : ℝ) : HasDerivAt B (2 * R s) s := by
    dsimp [B, R]
    have hx : HasDerivAt (fun t : ℝ => x + t * dx) dx s := by
      simpa using ((hasDerivAt_id s).mul_const dx).const_add x
    have hy : HasDerivAt (fun t : ℝ => y + t * dy) dy s := by
      simpa using ((hasDerivAt_id s).mul_const dy).const_add y
    have hz : HasDerivAt (fun t : ℝ => z + t * dz) dz s := by
      simpa using ((hasDerivAt_id s).mul_const dz).const_add z
    convert ((hx.pow 2).add (hy.pow 2)).add (hz.pow 2) using 1 <;> ring
  have hR : HasDerivAt R q 0 := by
    dsimp [R, q]
    have hx : HasDerivAt (fun t : ℝ => (x + t * dx) * dx) (dx ^ 2) 0 := by
      convert (((hasDerivAt_id (0 : ℝ)).mul_const dx).const_add x).mul_const dx using 1 <;> ring
    have hy : HasDerivAt (fun t : ℝ => (y + t * dy) * dy) (dy ^ 2) 0 := by
      convert (((hasDerivAt_id (0 : ℝ)).mul_const dy).const_add y).mul_const dy using 1 <;> ring
    have hz : HasDerivAt (fun t : ℝ => (z + t * dz) * dz) (dz ^ 2) 0 := by
      convert (((hasDerivAt_id (0 : ℝ)).mul_const dz).const_add z).mul_const dz using 1 <;> ring
    exact (hx.add hy).add hz
  have hline :
      deriv (fun s => f (A s) (B s)) =
        fun s => partial1 f (A s) (B s) * ds +
          partial2 f (A s) (B s) * (2 * R s) := by
    funext s
    exact (hasDerivAt_uncurry₂_chain f hF.differentiableAt (hA s) (hB s)).deriv
  rw [show (fun s =>
      f (x + s * dx + (y + s * dy) + (z + s * dz))
        ((x + s * dx) ^ 2 + (y + s * dy) ^ 2 + (z + s * dz) ^ 2)) =
      fun s => f (A s) (B s) by rfl]
  rw [hline]
  let p : ℝ × ℝ := (A 0, B 0)
  let v : ℝ × ℝ := (ds, 2 * R 0)
  let e₁ : ℝ × ℝ := (1, 0)
  let e₂ : ℝ × ℝ := (0, 1)
  let H := fderiv ℝ (fderiv ℝ (uncurry₂ f)) p
  have hpF := (hA 0).prodMk (hB 0)
  have hp1D : HasDerivAt (fun s => partial1 f (A s) (B s)) (H v e₁) 0 := by
    have hL : HasDerivAt
        (fun s => fderiv ℝ (uncurry₂ f) (A s, B s)) (H v) 0 := by
      simpa [H, p, v, Function.comp_def] using
        (hDF.differentiableAt.hasFDerivAt.comp (0 : ℝ) hpF).hasDerivAt
    have he := hL.clm_apply (hasDerivAt_const (x := (0 : ℝ)) (c := e₁))
    have he' : HasDerivAt
        (fun s => fderiv ℝ (uncurry₂ f) (A s, B s) e₁) (H v e₁) 0 := by
      simpa using he
    convert he' using 1
    funext s
    exact partial1_eq_fderiv f hF.differentiableAt
  have hp2D : HasDerivAt (fun s => partial2 f (A s) (B s)) (H v e₂) 0 := by
    have hL : HasDerivAt
        (fun s => fderiv ℝ (uncurry₂ f) (A s, B s)) (H v) 0 := by
      simpa [H, p, v, Function.comp_def] using
        (hDF.differentiableAt.hasFDerivAt.comp (0 : ℝ) hpF).hasDerivAt
    have he := hL.clm_apply (hasDerivAt_const (x := (0 : ℝ)) (c := e₂))
    have he' : HasDerivAt
        (fun s => fderiv ℝ (uncurry₂ f) (A s, B s) e₂) (H v e₂) 0 := by
      simpa using he
    convert he' using 1
    funext s
    exact partial2_eq_fderiv f hF.differentiableAt
  have h11 : (deriv^[2]) (fun t => f t (B 0)) (A 0) = H e₁ e₁ := by
    have hPF :=
      (hasDerivAt_id (A 0)).prodMk
        (hasDerivAt_const (x := A 0) (c := B 0))
    have hL : HasDerivAt
        (fun t => fderiv ℝ (uncurry₂ f) (t, B 0)) (H e₁) (A 0) := by
      simpa [H, p, e₁, Function.comp_def] using
        (hDF.differentiableAt.hasFDerivAt.comp (A 0) hPF).hasDerivAt
    have he := hL.clm_apply (hasDerivAt_const (x := A 0) (c := e₁))
    have he' : HasDerivAt (fun t => partial1 f t (B 0)) (H e₁ e₁) (A 0) := by
      have he'' : HasDerivAt
          (fun t => fderiv ℝ (uncurry₂ f) (t, B 0) e₁) (H e₁ e₁) (A 0) := by
        simpa using he
      convert he'' using 1
      funext t
      exact partial1_eq_fderiv f hF.differentiableAt
    simpa [Function.iterate_succ_apply, partial1] using he'.deriv
  have h12 : partial12 f (A 0) (B 0) = H e₂ e₁ := by
    have hPF :=
      (hasDerivAt_const (x := B 0) (c := A 0)).prodMk
        (hasDerivAt_id (B 0))
    have hL : HasDerivAt
        (fun t => fderiv ℝ (uncurry₂ f) (A 0, t)) (H e₂) (B 0) := by
      simpa [H, p, e₂, Function.comp_def] using
        (hDF.differentiableAt.hasFDerivAt.comp (B 0) hPF).hasDerivAt
    have he := hL.clm_apply (hasDerivAt_const (x := B 0) (c := e₁))
    have he' : HasDerivAt (fun t => partial1 f (A 0) t) (H e₂ e₁) (B 0) := by
      have he'' : HasDerivAt
          (fun t => fderiv ℝ (uncurry₂ f) (A 0, t) e₁) (H e₂ e₁) (B 0) := by
        simpa using he
      convert he'' using 1
      funext t
      exact partial1_eq_fderiv f hF.differentiableAt
    exact he'.deriv
  have h22 : (deriv^[2]) (fun t => f (A 0) t) (B 0) = H e₂ e₂ := by
    have hPF :=
      (hasDerivAt_const (x := B 0) (c := A 0)).prodMk
        (hasDerivAt_id (B 0))
    have hL : HasDerivAt
        (fun t => fderiv ℝ (uncurry₂ f) (A 0, t)) (H e₂) (B 0) := by
      simpa [H, p, e₂, Function.comp_def] using
        (hDF.differentiableAt.hasFDerivAt.comp (B 0) hPF).hasDerivAt
    have he := hL.clm_apply (hasDerivAt_const (x := B 0) (c := e₂))
    have he' : HasDerivAt (fun t => partial2 f (A 0) t) (H e₂ e₂) (B 0) := by
      have he'' : HasDerivAt
          (fun t => fderiv ℝ (uncurry₂ f) (A 0, t) e₂) (H e₂ e₂) (B 0) := by
        simpa using he
      convert he'' using 1
      funext t
      exact partial2_eq_fderiv f hF.differentiableAt
    simpa [Function.iterate_succ_apply, partial2] using he'.deriv
  have hsymm : H e₁ e₂ = H e₂ e₁ := by
    have hfirst : ∀ᶠ q : ℝ × ℝ in nhds p,
        HasFDerivAt (uncurry₂ f) (fderiv ℝ (uncurry₂ f) q) q := by
      exact Filter.Eventually.of_forall fun q => (hF q).hasFDerivAt
    have hsecond : HasFDerivAt (fderiv ℝ (uncurry₂ f)) H p := by
      simpa [H] using (hDF p).hasFDerivAt
    exact second_derivative_symmetric_of_eventually hfirst hsecond e₁ e₂
  have hv1 : H v e₁ = H e₁ e₁ * ds + H e₂ e₁ * (2 * R 0) := by
    rw [show v = ds • e₁ + (2 * R 0) • e₂ by ext <;> simp [v, e₁, e₂]]
    rw [map_add, map_smul, map_smul]
    simp [smul_eq_mul]
    ring
  have hv2 : H v e₂ = H e₂ e₁ * ds + H e₂ e₂ * (2 * R 0) := by
    rw [show v = ds • e₁ + (2 * R 0) • e₂ by ext <;> simp [v, e₁, e₂]]
    rw [map_add, map_smul, map_smul]
    simp [smul_eq_mul, hsymm]
    ring
  have hvel : HasDerivAt (fun s => 2 * R s) (2 * q) 0 := by
    convert hR.const_mul 2 using 1 <;> ring
  have htotal := (hp1D.mul_const ds).add (hp2D.mul hvel)
  have hder := htotal.deriv
  rw [hv1, hv2] at hder
  dsimp [A, B, R, ds, q, p, v, e₁, e₂, H] at h11 h12 h22 hder ⊢
  rw [← h11, ← h12, ← h22] at hder
  simp only [partial12] at hder
  convert hder using 1 <;> ring

end

end ProofGap.Exercise3297
