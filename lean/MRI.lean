/-
  MRI — Lean 4 formalization of "Sheaf Bandwidth" (companion to paper v0.1).

  `lake build` passes the entire library (8326 jobs, 0 sorry / 0 admit / 0 warning).

  The finite-dimensional operator / sheaf core of the three main results is mechanized:
    • paper §3 thm:triangle-equiv     (Triangle Equivalence)
    • paper §5 thm:strict-equality    (sheafBW on Samps, strict equality on the full-rank locus)
    • paper §5 prop:sheafBW-unitary   (sheafBW unitary invariance)
  along with the supporting definitions / lemmas / corollaries in the formalized scope.

  Full paper ↔ Lean correspondence: `lean/CROSSREF.md`.
-/

-- §1 Cell complex + cellular sheaf foundation
import MRI.Cellular.Complex            -- Complex1D structure
import MRI.Cellular.Sheaf              -- CellularSheaf            (paper def:finite-dim-sheaf)
import MRI.Cellular.Sections           -- discrepancy + globalSections
import MRI.Cellular.Inner              -- Cochain0/1 via PiLp 2    (paper def:cochain-space)
import MRI.Cellular.Coboundary         -- coboundary + coboundaryHilbert  (paper def:coboundary)

-- §2 Sampling sheaf
import MRI.Cellular.Sampling           -- Xsamp + Samps + canonical isometry + prop:delta-equals-A

-- §3 Spectral theory + strict equality
import MRI.Cellular.Spectral           -- gammaPlus + GammaPlus + sheafBW
import MRI.Cellular.SamplingSpectral   -- thm:strict-equality + full-rank / boundary forms

-- §4 Triangle Equivalence
import MRI.Cellular.Variational        -- (a)⇔(b) Riesz form + Rayleigh quotient bridges
import MRI.Cellular.TriangleEquivalence -- thm:triangle-equiv (TFAE (a)⇔(b)⇔(c))

-- §5 Closed Hilbert complex + L⁰ spectrum
import MRI.Cellular.HilbertComplex     -- thm:closed-hilbert-complex (d) + lem:L0-spectrum

-- §6 Unitary sheaf morphism + sheafBW invariance
import MRI.Cellular.Unitary            -- prop:sheafBW-unitary

/-
  Not formalized (explicitly disclaimed):
  • paper §5.7 def:unitary-subcat + prop:unitary-groupoid
      — category-theoretic packaging;core invariance is captured by
        `prop:sheafBW-unitary` (`Unitary.sheafBW_eq`).
  • paper §6 three physical instances + def:sampling-map + def:integration-map
      — physical correspondences (B-spline FE / quadrature / Bloch–Floquet),
        not mathematical theorems.
  • paper §6 Empirical Proposition 8b
      — empirical (2 quantitative evidence channels + 1 heuristic);
        not promoted to theorem status.

  See `lean/CROSSREF.md` §C (informal-only).
-/
