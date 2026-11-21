module

public import Morrey.General

/-!
# Šverák 1992, Lemma 1: quasiconvexity tested with periodic maps

V. Šverák, *Rank-one convexity does not imply quasiconvexity*, Proc. Roy. Soc. Edinburgh 120A
(1992), 185–189, Section 2, Lemma 1. Quasiconvexity is taken on the unit cube `Ω = (0, 1)^n`, the
domain of the paper's proof ("Since `u_ε` is smooth and compactly supported in `(0, 1)^n`").

* `lemma1_witness`: the "only if" part, as the paper proves it: from a smooth periodic `u`, the
  maps `u_ε (x) = ε² η_ε (x) u (x / ε²)`, smooth with compact support in `(0, 1)^n`, have
  `∫ f (A + ∇u_ε) → ∫_{[0,1]^n} f (A + ∇u)` as `ε → 0`. So a periodic map with
  `∫ f (A + ∇u) < f (A)` gives a compactly supported one.
* `lemma1`: the equivalence.
-/

@[expose] public section

open MeasureTheory Morrey

namespace Sverak

/-- `u : ℝ^n → ℝ^m` is periodic with respect to `ℤ^n`. -/
def IsPeriodic {m n : ℕ} (u : (Fin n → ℝ) → Fin m → ℝ) : Prop :=
  ∀ (x : Fin n → ℝ) (z : Fin n → ℤ), u (x + fun i => (z i : ℝ)) = u x

/-- The core of the proof of **Lemma 1** (`sv-lemma1`), "only if" part: for a continuous `f`, a
smooth `ℤ^n`-periodic `u` with `∫_{[0,1]^n} f (A + ∇u) < f (A)` yields a smooth map `φ` with
compact support in `(0, 1)^n` and `∫ f (A + ∇φ) < f (A)` (one of the paper's `u_ε`). -/
theorem lemma1_witness {m n : ℕ} {f : Matrix (Fin m) (Fin n) ℝ → ℝ} (hf : Continuous f)
    {A : Matrix (Fin m) (Fin n) ℝ} {u : (Fin n → ℝ) → Fin m → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (hper : IsPeriodic u)
    (hlt : ∫ x in unitCube n, f (A + jac u x) < f A) :
    ∃ φ : (Fin n → ℝ) → Fin m → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ unitCube n ∧ ∫ x in unitCube n, f (A + jac φ x) < f A := by
  sorry

/-- **Lemma 1** (`sv-lemma1`). A continuous function `f : M^{m×n} → ℝ` is quasiconvex if and only
if `∫_{[0,1]^n} f (A + D u (x)) dx ≥ f (A)` for each `A ∈ M^{m×n}` and each smooth `u : ℝ^n → ℝ^m`
which is periodic with respect to `ℤ^n`. -/
theorem lemma1 {m n : ℕ} {f : Matrix (Fin m) (Fin n) ℝ → ℝ} (hf : Continuous f) :
    QuasiconvexOn (unitCube n) f ↔
      ∀ (A : Matrix (Fin m) (Fin n) ℝ) (u : (Fin n → ℝ) → Fin m → ℝ),
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u → IsPeriodic u →
          f A ≤ ∫ x in unitCube n, f (A + jac u x) := by
  sorry

end Sverak
