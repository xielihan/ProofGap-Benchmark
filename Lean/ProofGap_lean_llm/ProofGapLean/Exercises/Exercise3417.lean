import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3417

noncomputable section

def partialX (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => u s y) x

def partialY (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => u x s) y

def f1 (f : ℝ → ℝ → ℝ → ℝ → ℝ) (x y z t : ℝ) : ℝ :=
  deriv (fun s => f s y z t) x

def f2 (f : ℝ → ℝ → ℝ → ℝ → ℝ) (x y z t : ℝ) : ℝ :=
  deriv (fun s => f x s z t) y

def f3 (f : ℝ → ℝ → ℝ → ℝ → ℝ) (x y z t : ℝ) : ℝ :=
  deriv (fun s => f x y s t) z

def f4 (f : ℝ → ℝ → ℝ → ℝ → ℝ) (x y z t : ℝ) : ℝ :=
  deriv (fun s => f x y z s) t

def g1 (g : ℝ → ℝ → ℝ → ℝ) (y z t : ℝ) : ℝ :=
  deriv (fun s => g s z t) y

def g2 (g : ℝ → ℝ → ℝ → ℝ) (y z t : ℝ) : ℝ :=
  deriv (fun s => g y s t) z

def g3 (g : ℝ → ℝ → ℝ → ℝ) (y z t : ℝ) : ℝ :=
  deriv (fun s => g y z s) t

def h1 (h : ℝ → ℝ → ℝ) (z t : ℝ) : ℝ :=
  deriv (fun s => h s t) z

def h2 (h : ℝ → ℝ → ℝ) (z t : ℝ) : ℝ :=
  deriv (fun s => h z s) t

def firstDerivative (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv q x

def minor1 (g : ℝ → ℝ → ℝ → ℝ) (h : ℝ → ℝ → ℝ)
    (y z t : ℝ) : ℝ :=
  g2 g y z t * h2 h z t - g3 g y z t * h1 h z t

def minor2 (f : ℝ → ℝ → ℝ → ℝ → ℝ) (h : ℝ → ℝ → ℝ)
    (x y z t : ℝ) : ℝ :=
  h1 h z t * f4 f x y z t - h2 h z t * f3 f x y z t

private theorem deriv_pair_curve
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : ℝ → E} {b : ℝ → F} {q : ℝ} {da : E} {db : F}
    (ha : HasDerivAt a da q) (hb : HasDerivAt b db q) :
    HasDerivAt (fun s => (a s, b s)) (da, db) q := by
  have hp : HasFDerivAt (fun s => (a s, b s))
      ((ContinuousLinearMap.toSpanSingleton ℝ da).prod
        (ContinuousLinearMap.toSpanSingleton ℝ db)) q :=
    ha.prodMk hb
  simpa using hp.hasDerivAt

private theorem deriv_chain_four
    (f : ℝ → ℝ → ℝ → ℝ → ℝ) (a b c d : ℝ → ℝ) (q da db dc dd : ℝ)
    (hf : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × (ℝ × ℝ)) =>
        f p.1 p.2.1 p.2.2.1 p.2.2.2)
      (a q, (b q, (c q, d q))))
    (ha : HasDerivAt a da q) (hb : HasDerivAt b db q)
    (hc : HasDerivAt c dc q) (hd : HasDerivAt d dd q) :
    deriv (fun s => f (a s) (b s) (c s) (d s)) q =
      f1 f (a q) (b q) (c q) (d q) * da +
      f2 f (a q) (b q) (c q) (d q) * db +
      f3 f (a q) (b q) (c q) (d q) * dc +
      f4 f (a q) (b q) (c q) (d q) * dd := by
  let F : ℝ × (ℝ × (ℝ × ℝ)) → ℝ :=
    fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2
  let A := fderiv ℝ F (a q, (b q, (c q, d q)))
  have hinner : HasDerivAt
      (fun s : ℝ => (a s, (b s, (c s, d s))))
      (da, (db, (dc, dd))) q := by
    simpa using
      (deriv_pair_curve ha
        (deriv_pair_curve hb (deriv_pair_curve hc hd)))
  have hall : HasDerivAt (fun s => f (a s) (b s) (c s) (d s))
      (A (da, (db, (dc, dd)))) q := by
    simpa [A, F, Function.comp_def] using
      hf.hasFDerivAt.comp_hasDerivAt q hinner
  have hinner1 : HasDerivAt
      (fun s : ℝ => (s, (b q, (c q, d q))))
      (1, (0, (0, 0))) (a q) := by
    simpa using
      (deriv_pair_curve (hasDerivAt_id (a q))
        (deriv_pair_curve (hasDerivAt_const (a q) (b q))
          (deriv_pair_curve (hasDerivAt_const (a q) (c q))
            (hasDerivAt_const (a q) (d q)))))
  have hinner2 : HasDerivAt
      (fun s : ℝ => (a q, (s, (c q, d q))))
      (0, (1, (0, 0))) (b q) := by
    simpa using
      (deriv_pair_curve (hasDerivAt_const (b q) (a q))
        (deriv_pair_curve (hasDerivAt_id (b q))
          (deriv_pair_curve (hasDerivAt_const (b q) (c q))
            (hasDerivAt_const (b q) (d q)))))
  have hinner3 : HasDerivAt
      (fun s : ℝ => (a q, (b q, (s, d q))))
      (0, (0, (1, 0))) (c q) := by
    simpa using
      (deriv_pair_curve (hasDerivAt_const (c q) (a q))
        (deriv_pair_curve (hasDerivAt_const (c q) (b q))
          (deriv_pair_curve (hasDerivAt_id (c q))
            (hasDerivAt_const (c q) (d q)))))
  have hinner4 : HasDerivAt
      (fun s : ℝ => (a q, (b q, (c q, s))))
      (0, (0, (0, 1))) (d q) := by
    simpa using
      (deriv_pair_curve (hasDerivAt_const (d q) (a q))
        (deriv_pair_curve (hasDerivAt_const (d q) (b q))
          (deriv_pair_curve (hasDerivAt_const (d q) (c q))
            (hasDerivAt_id (d q)))))
  have hx1 : HasDerivAt (fun s => f s (b q) (c q) (d q))
      (A (1, (0, (0, 0)))) (a q) := by
    simpa [A, F, Function.comp_def] using
      hf.hasFDerivAt.comp_hasDerivAt (a q) hinner1
  have hx2 : HasDerivAt (fun s => f (a q) s (c q) (d q))
      (A (0, (1, (0, 0)))) (b q) := by
    simpa [A, F, Function.comp_def] using
      hf.hasFDerivAt.comp_hasDerivAt (b q) hinner2
  have hx3 : HasDerivAt (fun s => f (a q) (b q) s (d q))
      (A (0, (0, (1, 0)))) (c q) := by
    simpa [A, F, Function.comp_def] using
      hf.hasFDerivAt.comp_hasDerivAt (c q) hinner3
  have hx4 : HasDerivAt (fun s => f (a q) (b q) (c q) s)
      (A (0, (0, (0, 1)))) (d q) := by
    simpa [A, F, Function.comp_def] using
      hf.hasFDerivAt.comp_hasDerivAt (d q) hinner4
  have hd1 : f1 f (a q) (b q) (c q) (d q) = A (1, (0, (0, 0))) := by
    unfold f1
    exact hx1.deriv
  have hd2 : f2 f (a q) (b q) (c q) (d q) = A (0, (1, (0, 0))) := by
    unfold f2
    exact hx2.deriv
  have hd3 : f3 f (a q) (b q) (c q) (d q) = A (0, (0, (1, 0))) := by
    unfold f3
    exact hx3.deriv
  have hd4 : f4 f (a q) (b q) (c q) (d q) = A (0, (0, (0, 1))) := by
    unfold f4
    exact hx4.deriv
  rw [hall.deriv, hd1, hd2, hd3, hd4]
  have hv : (da, (db, (dc, dd))) =
      da • (1, (0, (0, 0))) + db • (0, (1, (0, 0))) +
        dc • (0, (0, (1, 0))) + dd • (0, (0, (0, 1))) := by
    simp
  rw [hv]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

private theorem deriv_chain_three
    (g : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ → ℝ) (q da db dc : ℝ)
    (hg : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => g p.1 p.2.1 p.2.2)
      (a q, (b q, c q)))
    (ha : HasDerivAt a da q) (hb : HasDerivAt b db q)
    (hc : HasDerivAt c dc q) :
    deriv (fun s => g (a s) (b s) (c s)) q =
      g1 g (a q) (b q) (c q) * da +
      g2 g (a q) (b q) (c q) * db +
      g3 g (a q) (b q) (c q) * dc := by
  let G : ℝ × (ℝ × ℝ) → ℝ := fun p => g p.1 p.2.1 p.2.2
  let A := fderiv ℝ G (a q, (b q, c q))
  have hinner : HasDerivAt
      (fun s : ℝ => (a s, (b s, c s))) (da, (db, dc)) q := by
    simpa using
      (deriv_pair_curve ha (deriv_pair_curve hb hc))
  have hall : HasDerivAt (fun s => g (a s) (b s) (c s))
      (A (da, (db, dc))) q := by
    simpa [A, G, Function.comp_def] using
      hg.hasFDerivAt.comp_hasDerivAt q hinner
  have hinner1 : HasDerivAt
      (fun s : ℝ => (s, (b q, c q))) (1, (0, 0)) (a q) := by
    simpa using
      (deriv_pair_curve (hasDerivAt_id (a q))
        (deriv_pair_curve (hasDerivAt_const (a q) (b q))
          (hasDerivAt_const (a q) (c q))))
  have hinner2 : HasDerivAt
      (fun s : ℝ => (a q, (s, c q))) (0, (1, 0)) (b q) := by
    simpa using
      (deriv_pair_curve (hasDerivAt_const (b q) (a q))
        (deriv_pair_curve (hasDerivAt_id (b q))
          (hasDerivAt_const (b q) (c q))))
  have hinner3 : HasDerivAt
      (fun s : ℝ => (a q, (b q, s))) (0, (0, 1)) (c q) := by
    simpa using
      (deriv_pair_curve (hasDerivAt_const (c q) (a q))
        (deriv_pair_curve (hasDerivAt_const (c q) (b q))
          (hasDerivAt_id (c q))))
  have hx1 : HasDerivAt (fun s => g s (b q) (c q))
      (A (1, (0, 0))) (a q) := by
    simpa [A, G, Function.comp_def] using
      hg.hasFDerivAt.comp_hasDerivAt (a q) hinner1
  have hx2 : HasDerivAt (fun s => g (a q) s (c q))
      (A (0, (1, 0))) (b q) := by
    simpa [A, G, Function.comp_def] using
      hg.hasFDerivAt.comp_hasDerivAt (b q) hinner2
  have hx3 : HasDerivAt (fun s => g (a q) (b q) s)
      (A (0, (0, 1))) (c q) := by
    simpa [A, G, Function.comp_def] using
      hg.hasFDerivAt.comp_hasDerivAt (c q) hinner3
  have hd1 : g1 g (a q) (b q) (c q) = A (1, (0, 0)) := by
    unfold g1
    exact hx1.deriv
  have hd2 : g2 g (a q) (b q) (c q) = A (0, (1, 0)) := by
    unfold g2
    exact hx2.deriv
  have hd3 : g3 g (a q) (b q) (c q) = A (0, (0, 1)) := by
    unfold g3
    exact hx3.deriv
  rw [hall.deriv, hd1, hd2, hd3]
  have hv : (da, (db, dc)) =
      da • (1, (0, 0)) + db • (0, (1, 0)) + dc • (0, (0, 1)) := by
    simp
  rw [hv]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

private theorem deriv_chain_two
    (h : ℝ → ℝ → ℝ) (a b : ℝ → ℝ) (q da db : ℝ)
    (hh : DifferentiableAt ℝ (Function.uncurry h) (a q, b q))
    (ha : HasDerivAt a da q) (hb : HasDerivAt b db q) :
    deriv (fun s => h (a s) (b s)) q =
      h1 h (a q) (b q) * da + h2 h (a q) (b q) * db := by
  let H : ℝ × ℝ → ℝ := Function.uncurry h
  let A := fderiv ℝ H (a q, b q)
  have hinner : HasDerivAt
      (fun s : ℝ => (a s, b s)) (da, db) q := by
    simpa using (deriv_pair_curve ha hb)
  have hall : HasDerivAt (fun s => h (a s) (b s)) (A (da, db)) q := by
    simpa [A, H, Function.comp_def, Function.uncurry] using
      hh.hasFDerivAt.comp_hasDerivAt q hinner
  have hinner1 : HasDerivAt
      (fun s : ℝ => (s, b q)) (1, 0) (a q) := by
    simpa using
      (deriv_pair_curve (hasDerivAt_id (a q))
        (hasDerivAt_const (a q) (b q)))
  have hinner2 : HasDerivAt
      (fun s : ℝ => (a q, s)) (0, 1) (b q) := by
    simpa using
      (deriv_pair_curve (hasDerivAt_const (b q) (a q))
        (hasDerivAt_id (b q)))
  have hx1 : HasDerivAt (fun s => h s (b q)) (A (1, 0)) (a q) := by
    simpa [A, H, Function.comp_def, Function.uncurry] using
      hh.hasFDerivAt.comp_hasDerivAt (a q) hinner1
  have hx2 : HasDerivAt (fun s => h (a q) s) (A (0, 1)) (b q) := by
    simpa [A, H, Function.comp_def, Function.uncurry] using
      hh.hasFDerivAt.comp_hasDerivAt (b q) hinner2
  have hd1 : h1 h (a q) (b q) = A (1, 0) := by
    unfold h1
    exact hx1.deriv
  have hd2 : h2 h (a q) (b q) = A (0, 1) := by
    unfold h2
    exact hx2.deriv
  rw [hall.deriv, hd1, hd2]
  have hv : (da, db) = da • (1, 0) + db • (0, 1) := by
    simp
  rw [hv]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

theorem gap1 (f : ℝ → ℝ → ℝ → ℝ → ℝ)
    (u : ℝ → ℝ → ℝ) (z t : ℝ → ℝ) (x y dx dy : ℝ)
    (hfDiff : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × (ℝ × ℝ)) =>
        f p.1 p.2.1 p.2.2.1 p.2.2.2) (x, (y, (z y, t y))))
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hzDiff : DifferentiableAt ℝ z y)
    (htDiff : DifferentiableAt ℝ t y)
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      u p.1 p.2 = f p.1 p.2 (z p.2) (t p.2)) :
    partialX u x y * dx + partialY u x y * dy =
      f1 f x y (z y) (t y) * dx +
        f2 f x y (z y) (t y) * dy +
        f3 f x y (z y) (t y) * (firstDerivative z y * dy) +
        f4 f x y (z y) (t y) * (firstDerivative t y * dy) := by
  have hmapX :
      Filter.Tendsto (fun s : ℝ => (s, y)) (nhds x) (nhds (x, y)) := by
    simpa using
      (deriv_pair_curve (hasDerivAt_id x)
        (hasDerivAt_const x y)).continuousAt
  have hmapY :
      Filter.Tendsto (fun s : ℝ => (x, s)) (nhds y) (nhds (x, y)) := by
    simpa using
      (deriv_pair_curve (hasDerivAt_const y x)
        (hasDerivAt_id y)).continuousAt
  have hEqX :
      (fun s : ℝ => u s y) =ᶠ[nhds x]
        (fun s : ℝ => f s y (z y) (t y)) := by
    simpa using hmapX.eventually hU
  have hEqY :
      (fun s : ℝ => u x s) =ᶠ[nhds y]
        (fun s : ℝ => f x s (z s) (t s)) := by
    simpa using hmapY.eventually hU
  have hPX : partialX u x y = f1 f x y (z y) (t y) := by
    unfold partialX
    calc
      deriv (fun s : ℝ => u s y) x =
          deriv (fun s : ℝ => f s y (z y) (t y)) x := hEqX.deriv_eq
      _ = f1 f x y (z y) (t y) := by
        simpa using
          (deriv_chain_four f
            (fun s : ℝ => s) (fun _ : ℝ => y)
            (fun _ : ℝ => z y) (fun _ : ℝ => t y)
            x 1 0 0 0 hfDiff
            (hasDerivAt_id x) (hasDerivAt_const x y)
            (hasDerivAt_const x (z y)) (hasDerivAt_const x (t y)))
  have hPY :
      partialY u x y =
        f2 f x y (z y) (t y) +
          f3 f x y (z y) (t y) * firstDerivative z y +
          f4 f x y (z y) (t y) * firstDerivative t y := by
    unfold partialY
    calc
      deriv (fun s : ℝ => u x s) y =
          deriv (fun s : ℝ => f x s (z s) (t s)) y := hEqY.deriv_eq
      _ = f2 f x y (z y) (t y) +
          f3 f x y (z y) (t y) * firstDerivative z y +
          f4 f x y (z y) (t y) * firstDerivative t y := by
        simpa [firstDerivative] using
          (deriv_chain_four f
            (fun _ : ℝ => x) (fun s : ℝ => s) z t
            y 0 1 (deriv z y) (deriv t y) hfDiff
            (hasDerivAt_const y x) (hasDerivAt_id y)
            hzDiff.hasDerivAt htDiff.hasDerivAt)
  rw [hPX, hPY]
  ring

theorem gap2 (g : ℝ → ℝ → ℝ → ℝ) (z t : ℝ → ℝ) (y dy : ℝ)
    (hgDiff : DifferentiableAt ℝ
      (fun p : ℝ × (ℝ × ℝ) => g p.1 p.2.1 p.2.2)
      (y, (z y, t y)))
    (hzDiff : DifferentiableAt ℝ z y)
    (htDiff : DifferentiableAt ℝ t y)
    (hG : ∀ᶠ s in nhds y, g s (z s) (t s) = 0) :
    0 = g1 g y (z y) (t y) * dy +
      g2 g y (z y) (t y) * (firstDerivative z y * dy) +
      g3 g y (z y) (t y) * (firstDerivative t y * dy) := by
  have hEq :
      (fun s : ℝ => g s (z s) (t s)) =ᶠ[nhds y]
        (fun _ : ℝ => 0) := hG
  have hZero : deriv (fun s : ℝ => g s (z s) (t s)) y = 0 := by
    calc
      deriv (fun s : ℝ => g s (z s) (t s)) y =
          deriv (fun _ : ℝ => 0) y := hEq.deriv_eq
      _ = 0 := by simp
  have hChain :=
    deriv_chain_three g (fun s : ℝ => s) z t y
      1 (deriv z y) (deriv t y) hgDiff
      (hasDerivAt_id y) hzDiff.hasDerivAt htDiff.hasDerivAt
  have hBase :
      0 = g1 g y (z y) (t y) +
        g2 g y (z y) (t y) * deriv z y +
        g3 g y (z y) (t y) * deriv t y := by
    calc
      0 = deriv (fun s : ℝ => g s (z s) (t s)) y := hZero.symm
      _ = g1 g y (z y) (t y) +
          g2 g y (z y) (t y) * deriv z y +
          g3 g y (z y) (t y) * deriv t y := by
        simpa using hChain
  calc
    0 = (0 : ℝ) * dy := by ring
    _ = (g1 g y (z y) (t y) +
          g2 g y (z y) (t y) * deriv z y +
          g3 g y (z y) (t y) * deriv t y) * dy :=
      congrArg (fun r : ℝ => r * dy) hBase
    _ = g1 g y (z y) (t y) * dy +
        g2 g y (z y) (t y) * (firstDerivative z y * dy) +
        g3 g y (z y) (t y) * (firstDerivative t y * dy) := by
      unfold firstDerivative
      ring

theorem gap3 (h : ℝ → ℝ → ℝ) (z t : ℝ → ℝ) (y dy : ℝ)
    (hhDiff : DifferentiableAt ℝ (Function.uncurry h) (z y, t y))
    (hzDiff : DifferentiableAt ℝ z y)
    (htDiff : DifferentiableAt ℝ t y)
    (hH : ∀ᶠ s in nhds y, h (z s) (t s) = 0) :
    0 = h1 h (z y) (t y) * (firstDerivative z y * dy) +
      h2 h (z y) (t y) * (firstDerivative t y * dy) := by
  have hEq :
      (fun s : ℝ => h (z s) (t s)) =ᶠ[nhds y]
        (fun _ : ℝ => 0) := hH
  have hZero : deriv (fun s : ℝ => h (z s) (t s)) y = 0 := by
    calc
      deriv (fun s : ℝ => h (z s) (t s)) y =
          deriv (fun _ : ℝ => 0) y := hEq.deriv_eq
      _ = 0 := by simp
  have hChain :=
    deriv_chain_two h z t y (deriv z y) (deriv t y)
      hhDiff hzDiff.hasDerivAt htDiff.hasDerivAt
  have hBase :
      0 = h1 h (z y) (t y) * deriv z y +
        h2 h (z y) (t y) * deriv t y := by
    calc
      0 = deriv (fun s : ℝ => h (z s) (t s)) y := hZero.symm
      _ = h1 h (z y) (t y) * deriv z y +
          h2 h (z y) (t y) * deriv t y := by
        simpa using hChain
  calc
    0 = (0 : ℝ) * dy := by ring
    _ = (h1 h (z y) (t y) * deriv z y +
          h2 h (z y) (t y) * deriv t y) * dy :=
      congrArg (fun r : ℝ => r * dy) hBase
    _ = h1 h (z y) (t y) * (firstDerivative z y * dy) +
        h2 h (z y) (t y) * (firstDerivative t y * dy) := by
      unfold firstDerivative
      ring

theorem gap4 (g : ℝ → ℝ → ℝ → ℝ) (h : ℝ → ℝ → ℝ)
    (z t : ℝ → ℝ) (y : ℝ)
    (hI : minor1 g h y (z y) (t y) ≠ 0)
    (hG : 0 = g1 g y (z y) (t y) +
      g2 g y (z y) (t y) * firstDerivative z y +
      g3 g y (z y) (t y) * firstDerivative t y)
    (hH : 0 = h1 h (z y) (t y) * firstDerivative z y +
      h2 h (z y) (t y) * firstDerivative t y) :
    firstDerivative z y =
      -g1 g y (z y) (t y) * h2 h (z y) (t y) /
        minor1 g h y (z y) (t y) := by
  apply (eq_div_iff hI).2
  have hgMul :=
    congrArg (fun r : ℝ => r * h2 h (z y) (t y)) hG
  have hhMul :=
    congrArg (fun r : ℝ => r * g3 g y (z y) (t y)) hH
  unfold minor1 at *
  ring_nf at hgMul hhMul ⊢
  linarith

theorem gap5 (g : ℝ → ℝ → ℝ → ℝ) (h : ℝ → ℝ → ℝ)
    (z t : ℝ → ℝ) (y : ℝ)
    (hI : minor1 g h y (z y) (t y) ≠ 0)
    (hG : 0 = g1 g y (z y) (t y) +
      g2 g y (z y) (t y) * firstDerivative z y +
      g3 g y (z y) (t y) * firstDerivative t y)
    (hH : 0 = h1 h (z y) (t y) * firstDerivative z y +
      h2 h (z y) (t y) * firstDerivative t y) :
    firstDerivative t y =
      g1 g y (z y) (t y) * h1 h (z y) (t y) /
        minor1 g h y (z y) (t y) := by
  apply (eq_div_iff hI).2
  have hgMul :=
    congrArg (fun r : ℝ => r * h1 h (z y) (t y)) hG
  have hhMul :=
    congrArg (fun r : ℝ => r * g2 g y (z y) (t y)) hH
  unfold minor1 at *
  ring_nf at hgMul hhMul ⊢
  linarith

theorem gap6 (f : ℝ → ℝ → ℝ → ℝ → ℝ)
    (g : ℝ → ℝ → ℝ → ℝ) (h : ℝ → ℝ → ℝ)
    (u : ℝ → ℝ → ℝ) (z t : ℝ → ℝ) (x y dx dy : ℝ)
    (hI : minor1 g h y (z y) (t y) ≠ 0)
    (hChain : partialX u x y * dx + partialY u x y * dy =
      f1 f x y (z y) (t y) * dx +
        f2 f x y (z y) (t y) * dy +
        f3 f x y (z y) (t y) * (firstDerivative z y * dy) +
        f4 f x y (z y) (t y) * (firstDerivative t y * dy))
    (hZ : firstDerivative z y =
      -g1 g y (z y) (t y) * h2 h (z y) (t y) /
        minor1 g h y (z y) (t y))
    (hT : firstDerivative t y =
      g1 g y (z y) (t y) * h1 h (z y) (t y) /
        minor1 g h y (z y) (t y)) :
    partialX u x y * dx + partialY u x y * dy =
      f1 f x y (z y) (t y) * dx +
        f2 f x y (z y) (t y) * dy -
        (g1 g y (z y) (t y) / minor1 g h y (z y) (t y)) *
          (f3 f x y (z y) (t y) * h2 h (z y) (t y) -
            f4 f x y (z y) (t y) * h1 h (z y) (t y)) * dy := by
  calc
    partialX u x y * dx + partialY u x y * dy =
        f1 f x y (z y) (t y) * dx +
          f2 f x y (z y) (t y) * dy +
          f3 f x y (z y) (t y) * (firstDerivative z y * dy) +
          f4 f x y (z y) (t y) * (firstDerivative t y * dy) := hChain
    _ = f1 f x y (z y) (t y) * dx +
        f2 f x y (z y) (t y) * dy -
        (g1 g y (z y) (t y) / minor1 g h y (z y) (t y)) *
          (f3 f x y (z y) (t y) * h2 h (z y) (t y) -
            f4 f x y (z y) (t y) * h1 h (z y) (t y)) * dy := by
      rw [hZ, hT]
      field_simp [hI]
      ring

theorem gap7 (f : ℝ → ℝ → ℝ → ℝ → ℝ)
    (g : ℝ → ℝ → ℝ → ℝ) (h : ℝ → ℝ → ℝ)
    (u : ℝ → ℝ → ℝ) (z t : ℝ → ℝ) (x y : ℝ)
    (hI : minor1 g h y (z y) (t y) ≠ 0)
    (hAll : ∀ dx dy : ℝ,
      partialX u x y * dx + partialY u x y * dy =
        f1 f x y (z y) (t y) * dx +
          f2 f x y (z y) (t y) * dy -
          (g1 g y (z y) (t y) / minor1 g h y (z y) (t y)) *
            (f3 f x y (z y) (t y) * h2 h (z y) (t y) -
              f4 f x y (z y) (t y) * h1 h (z y) (t y)) * dy) :
    partialX u x y = f1 f x y (z y) (t y) := by
  simpa using hAll 1 0

theorem gap8 (f : ℝ → ℝ → ℝ → ℝ → ℝ)
    (g : ℝ → ℝ → ℝ → ℝ) (h : ℝ → ℝ → ℝ)
    (u : ℝ → ℝ → ℝ) (z t : ℝ → ℝ) (x y : ℝ)
    (hI : minor1 g h y (z y) (t y) ≠ 0)
    (hAll : ∀ dx dy : ℝ,
      partialX u x y * dx + partialY u x y * dy =
        f1 f x y (z y) (t y) * dx +
          f2 f x y (z y) (t y) * dy -
          (g1 g y (z y) (t y) / minor1 g h y (z y) (t y)) *
            (f3 f x y (z y) (t y) * h2 h (z y) (t y) -
              f4 f x y (z y) (t y) * h1 h (z y) (t y)) * dy) :
    partialY u x y =
      f2 f x y (z y) (t y) +
        g1 g y (z y) (t y) *
          (minor2 f h x y (z y) (t y) /
            minor1 g h y (z y) (t y)) := by
  calc
    partialY u x y =
        f2 f x y (z y) (t y) -
          (g1 g y (z y) (t y) / minor1 g h y (z y) (t y)) *
            (f3 f x y (z y) (t y) * h2 h (z y) (t y) -
              f4 f x y (z y) (t y) * h1 h (z y) (t y)) := by
      simpa using hAll 0 1
    _ = f2 f x y (z y) (t y) +
        g1 g y (z y) (t y) *
          (minor2 f h x y (z y) (t y) /
            minor1 g h y (z y) (t y)) := by
      unfold minor2
      field_simp [hI]
      ring

end

end ProofGap.Exercise3417
