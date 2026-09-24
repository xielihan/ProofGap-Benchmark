import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3324

noncomputable section

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g s y) x

def partialY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g x s) y

def partialFirst (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => g s y z) x

def partialSecond (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => g x s z) y

def partialThird (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => g x y s) z

def u (n α β : ℝ) (φ : ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  Real.rpow x n *
    φ (y / Real.rpow x α) (z / Real.rpow x β)

private theorem deriv_comp_uncurry
    (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiff ℝ 1 (Function.uncurry φ))
    {P Q : ℝ → ℝ} {x p' q' : ℝ}
    (hP : HasDerivAt P p' x) (hQ : HasDerivAt Q q' x) :
    HasDerivAt (fun t => φ (P t) (Q t))
      (partialX φ (P x) (Q x) * p' +
        partialY φ (P x) (Q x) * q') x := by
  let L := fderiv ℝ (Function.uncurry φ) (P x, Q x)
  have hφdiff : Differentiable ℝ (Function.uncurry φ) :=
    hφ.differentiable (by norm_num)
  have hF : HasFDerivAt (Function.uncurry φ) L (P x, Q x) := by
    exact hφdiff.differentiableAt.hasFDerivAt
  have hcomp : HasDerivAt (fun t => φ (P t) (Q t)) (L (p', q')) x := by
    have hc := hF.comp x (hP.hasFDerivAt.prodMk hQ.hasFDerivAt)
    convert hc.hasDerivAt using 1 <;>
      simp [Function.comp_def, Function.uncurry]
  have hpxDeriv : HasDerivAt (fun s => φ s (Q x)) (L (1, 0)) (P x) := by
    have hc := hF.comp (P x)
      ((hasDerivAt_id (𝕜 := ℝ) (P x)).hasFDerivAt.prodMk
        (hasDerivAt_const (x := P x) (c := Q x)).hasFDerivAt)
    convert hc.hasDerivAt using 1 <;>
      simp [Function.comp_def, Function.uncurry]
  have hpyDeriv : HasDerivAt (fun s => φ (P x) s) (L (0, 1)) (Q x) := by
    have hc := hF.comp (Q x)
      ((hasDerivAt_const (x := Q x) (c := P x)).hasFDerivAt.prodMk
        (hasDerivAt_id (𝕜 := ℝ) (Q x)).hasFDerivAt)
    convert hc.hasDerivAt using 1 <;>
      simp [Function.comp_def, Function.uncurry]
  have hpx : partialX φ (P x) (Q x) = L (1, 0) := by
    exact hpxDeriv.deriv
  have hpy : partialY φ (P x) (Q x) = L (0, 1) := by
    exact hpyDeriv.deriv
  have hL :
      L (p', q') =
        partialX φ (P x) (Q x) * p' +
          partialY φ (P x) (Q x) * q' := by
    calc
      L (p', q') = L (p' • (1, 0) + q' • (0, 1)) := by
        congr 1
        ext <;> simp
      _ = p' • L (1, 0) + q' • L (0, 1) := by
        rw [map_add, map_smul, map_smul]
      _ = partialX φ (P x) (Q x) * p' +
          partialY φ (P x) (Q x) * q' := by
        rw [← hpx, ← hpy]
        simp [mul_comm]
  rw [hL] at hcomp
  exact hcomp

theorem gap1 (n α β : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiff ℝ 1 (Function.uncurry φ)) :
    ∀ x y z, 0 < x →
      x * partialFirst (u n α β φ) x y z +
          α * y * partialSecond (u n α β φ) x y z +
          β * z * partialThird (u n α β φ) x y z =
        n * Real.rpow x n *
            φ (y / Real.rpow x α) (z / Real.rpow x β) -
          α * Real.rpow x (n - α) * y *
            partialX φ (y / Real.rpow x α) (z / Real.rpow x β) -
          β * Real.rpow x (n - β) * z *
            partialY φ (y / Real.rpow x α) (z / Real.rpow x β) +
          α * y * Real.rpow x (n - α) *
            partialX φ (y / Real.rpow x α) (z / Real.rpow x β) +
          β * z * Real.rpow x (n - β) *
            partialY φ (y / Real.rpow x α) (z / Real.rpow x β) := by
  intro x y z hx
  let N := Real.rpow x n
  let A := Real.rpow x α
  let B := Real.rpow x β
  let Dn := Real.rpow x (n - 1)
  let Da := Real.rpow x (α - 1)
  let Db := Real.rpow x (β - 1)
  let F := φ (y / A) (z / B)
  let Fx := partialX φ (y / A) (z / B)
  let Fy := partialY φ (y / A) (z / B)
  have hAne : A ≠ 0 := by
    exact ne_of_gt (Real.rpow_pos_of_pos hx α)
  have hBne : B ≠ 0 := by
    exact ne_of_gt (Real.rpow_pos_of_pos hx β)
  have hn : HasDerivAt (fun t : ℝ => Real.rpow t n) (n * Dn) x := by
    exact Real.hasDerivAt_rpow_const (p := n) (Or.inl hx.ne')
  have ha : HasDerivAt (fun t : ℝ => Real.rpow t α) (α * Da) x := by
    exact Real.hasDerivAt_rpow_const (p := α) (Or.inl hx.ne')
  have hb : HasDerivAt (fun t : ℝ => Real.rpow t β) (β * Db) x := by
    exact Real.hasDerivAt_rpow_const (p := β) (Or.inl hx.ne')
  have hpa : HasDerivAt (fun t : ℝ => y / Real.rpow t α)
      (-(y * (α * Da) / A ^ 2)) x := by
    have hc : HasDerivAt (fun _ : ℝ => y) 0 x :=
      hasDerivAt_const (x := x) (c := y)
    convert hc.div ha hAne using 1 <;> ring
  have hpb : HasDerivAt (fun t : ℝ => z / Real.rpow t β)
      (-(z * (β * Db) / B ^ 2)) x := by
    have hc : HasDerivAt (fun _ : ℝ => z) 0 x :=
      hasDerivAt_const (x := x) (c := z)
    convert hc.div hb hBne using 1 <;> ring
  have hinner := deriv_comp_uncurry φ hφ hpa hpb
  have hfirst :
      partialFirst (u n α β φ) x y z =
        (n * Dn) * F +
          N * (Fx * (-(y * (α * Da) / A ^ 2)) +
            Fy * (-(z * (β * Db) / B ^ 2))) := by
    simpa [partialFirst, u, N, A, B, Dn, Da, Db, F, Fx, Fy] using
      (hn.mul hinner).deriv
  have hpy : HasDerivAt (fun t : ℝ => t / A) (1 / A) y := by
    convert (hasDerivAt_id y).div_const A using 1 <;> ring
  have hqy : HasDerivAt (fun _ : ℝ => z / B) 0 y :=
    hasDerivAt_const (x := y) (c := z / B)
  have hinnerY := deriv_comp_uncurry φ hφ hpy hqy
  have hsecond :
      partialSecond (u n α β φ) x y z = (N / A) * Fx := by
    have hc : HasDerivAt (fun _ : ℝ => N) 0 y :=
      hasDerivAt_const (x := y) (c := N)
    have hd := (hc.mul hinnerY).deriv
    change deriv (fun t : ℝ => N * φ (t / A) (z / B)) y =
      0 * φ (y / A) (z / B) +
        N * (Fx * (1 / A) + Fy * 0) at hd
    change deriv (fun t : ℝ => N * φ (t / A) (z / B)) y =
      (N / A) * Fx
    rw [hd]
    ring
  have hpz : HasDerivAt (fun _ : ℝ => y / A) 0 z :=
    hasDerivAt_const (x := z) (c := y / A)
  have hqz : HasDerivAt (fun t : ℝ => t / B) (1 / B) z := by
    convert (hasDerivAt_id z).div_const B using 1 <;> ring
  have hinnerZ := deriv_comp_uncurry φ hφ hpz hqz
  have hthird :
      partialThird (u n α β φ) x y z = (N / B) * Fy := by
    have hc : HasDerivAt (fun _ : ℝ => N) 0 z :=
      hasDerivAt_const (x := z) (c := N)
    have hd := (hc.mul hinnerZ).deriv
    change deriv (fun t : ℝ => N * φ (y / A) (t / B)) z =
      0 * φ (y / A) (z / B) +
        N * (Fx * 0 + Fy * (1 / B)) at hd
    change deriv (fun t : ℝ => N * φ (y / A) (t / B)) z =
      (N / B) * Fy
    rw [hd]
    ring
  have hxn : x * Dn = N := by
    have hr : Dn = N / x := by
      simpa [Dn, N] using (Real.rpow_sub hx n 1)
    calc
      x * Dn = x * (N / x) := by rw [hr]
      _ = N := by field_simp [hx.ne']
  have hxa : x * Da = A := by
    have hr : Da = A / x := by
      simpa [Da, A] using (Real.rpow_sub hx α 1)
    calc
      x * Da = x * (A / x) := by rw [hr]
      _ = A := by field_simp [hx.ne']
  have hxb : x * Db = B := by
    have hr : Db = B / x := by
      simpa [Db, B] using (Real.rpow_sub hx β 1)
    calc
      x * Db = x * (B / x) := by rw [hr]
      _ = B := by field_simp [hx.ne']
  have hsubA : Real.rpow x (n - α) = N / A := by
    simpa [N, A] using Real.rpow_sub hx n α
  have hsubB : Real.rpow x (n - β) = N / B := by
    simpa [N, B] using Real.rpow_sub hx n β
  have hbaseA :
      x * N * (-(y * (α * Da) / A ^ 2)) = -α * (N / A) * y := by
    calc
      x * N * (-(y * (α * Da) / A ^ 2)) =
          -α * y * N * (x * Da) / A ^ 2 := by ring
      _ = -α * y * N * A / A ^ 2 := by rw [hxa]
      _ = -α * (N / A) * y := by field_simp [hAne] <;> ring
  have hbaseB :
      x * N * (-(z * (β * Db) / B ^ 2)) = -β * (N / B) * z := by
    calc
      x * N * (-(z * (β * Db) / B ^ 2)) =
          -β * z * N * (x * Db) / B ^ 2 := by ring
      _ = -β * z * N * B / B ^ 2 := by rw [hxb]
      _ = -β * (N / B) * z := by field_simp [hBne] <;> ring
  have htermN : x * ((n * Dn) * F) = n * N * F := by
    calc
      x * ((n * Dn) * F) = n * F * (x * Dn) := by ring
      _ = n * F * N := by rw [hxn]
      _ = n * N * F := by ring
  have hxf :
      x * partialFirst (u n α β φ) x y z =
        n * N * F - α * (N / A) * y * Fx - β * (N / B) * z * Fy := by
    rw [hfirst]
    calc
      x * ((n * Dn) * F +
          N * (Fx * (-(y * (α * Da) / A ^ 2)) +
            Fy * (-(z * (β * Db) / B ^ 2)))) =
          x * ((n * Dn) * F) +
            (x * N * (-(y * (α * Da) / A ^ 2))) * Fx +
            (x * N * (-(z * (β * Db) / B ^ 2))) * Fy := by ring
      _ = n * N * F - α * (N / A) * y * Fx - β * (N / B) * z * Fy := by
        rw [htermN, hbaseA, hbaseB]
        ring
  rw [hxf, hsecond, hthird, hsubA, hsubB]
  dsimp [N, A, B, F, Fx, Fy]
  ring

theorem gap2 (n α β : ℝ) (φ : ℝ → ℝ → ℝ) :
    ∀ x y z, 0 < x →
      n * Real.rpow x n *
            φ (y / Real.rpow x α) (z / Real.rpow x β) -
          α * Real.rpow x (n - α) * y *
            partialX φ (y / Real.rpow x α) (z / Real.rpow x β) -
          β * Real.rpow x (n - β) * z *
            partialY φ (y / Real.rpow x α) (z / Real.rpow x β) +
          α * y * Real.rpow x (n - α) *
            partialX φ (y / Real.rpow x α) (z / Real.rpow x β) +
          β * z * Real.rpow x (n - β) *
            partialY φ (y / Real.rpow x α) (z / Real.rpow x β) =
        n * Real.rpow x n *
          φ (y / Real.rpow x α) (z / Real.rpow x β) := by
  intro x y z hx
  ring

theorem gap3 (n α β : ℝ) (φ : ℝ → ℝ → ℝ) :
    ∀ x y z, 0 < x →
      n * Real.rpow x n *
          φ (y / Real.rpow x α) (z / Real.rpow x β) =
        n * u n α β φ x y z := by
  intro x y z hx
  simp only [u, mul_assoc]

theorem gap4 (n α β : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiff ℝ 1 (Function.uncurry φ)) :
    ∀ x y z, 0 < x →
      x * partialFirst (u n α β φ) x y z +
          α * y * partialSecond (u n α β φ) x y z +
          β * z * partialThird (u n α β φ) x y z =
        n * u n α β φ x y z := by
  intro x y z hx
  calc
    x * partialFirst (u n α β φ) x y z +
          α * y * partialSecond (u n α β φ) x y z +
          β * z * partialThird (u n α β φ) x y z =
        n * Real.rpow x n *
            φ (y / Real.rpow x α) (z / Real.rpow x β) -
          α * Real.rpow x (n - α) * y *
            partialX φ (y / Real.rpow x α) (z / Real.rpow x β) -
          β * Real.rpow x (n - β) * z *
            partialY φ (y / Real.rpow x α) (z / Real.rpow x β) +
          α * y * Real.rpow x (n - α) *
            partialX φ (y / Real.rpow x α) (z / Real.rpow x β) +
          β * z * Real.rpow x (n - β) *
            partialY φ (y / Real.rpow x α) (z / Real.rpow x β) :=
      gap1 n α β φ hφ x y z hx
    _ = n * Real.rpow x n *
          φ (y / Real.rpow x α) (z / Real.rpow x β) :=
      gap2 n α β φ x y z hx
    _ = n * u n α β φ x y z :=
      gap3 n α β φ x y z hx

theorem gap5 (n α β : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiff ℝ 1 (Function.uncurry φ)) :
    ∀ x y z, 0 < x →
      x * partialFirst (u n α β φ) x y z +
          α * y * partialSecond (u n α β φ) x y z +
          β * z * partialThird (u n α β φ) x y z =
        n * u n α β φ x y z := by
  exact gap4 n α β φ hφ

end

end ProofGap.Exercise3324
