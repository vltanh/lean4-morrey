module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Complex.Basic

/-!
# Burkholder's function for the exponent `6`

D. L. Burkholder, *Sharp inequalities for martingales and stochastic integrals*, Colloque Paul
Lévy, Astérisque 157–158 (1988), proof of Theorem 1.1 (see also V. Vasyunin and A. Volberg 2010).
Cassese uses two properties of `u (a, b) = α (|b| − 5 |a|) (|a| + |b|)^5`, `α = 6 (5/6)^5`, for
complex `a`, `b` (the proof of Proposition 4.2, (13) and (14)). Large but feasible (class L of the
inventory); until the user decides, a proposition with no proof, a hypothesis of every statement
whose proof uses it.
-/

@[expose] public section

namespace External.Burkholder

/-- Burkholder's function for the exponent `6`: `u (a, b) = α (|b| − 5 |a|) (|a| + |b|)^5` with
`α = 6 (5/6)^5 = 5^5 / 6^4`. -/
noncomputable def u6 (a b : ℂ) : ℝ :=
  5 ^ 5 / 6 ^ 4 * (‖b‖ - 5 * ‖a‖) * (‖a‖ + ‖b‖) ^ 5

/-- **Equations (13), (14)** (`eq:scalar-properties`, `eq:scalar-zigzag`) of Cassese, citing
Burkholder 1988 (proof of Theorem 1.1) and Vasyunin–Volberg:
`u (a, b) ≥ |b|^6 − 5^6 |a|^6`, and `t ↦ u (a + t h, b + t ε h)` is concave for all complex
`a`, `b`, `h` and `|ε| ≤ 1`. -/
def ScalarFunction : Prop :=
  (∀ a b : ℂ, ‖b‖ ^ 6 - 5 ^ 6 * ‖a‖ ^ 6 ≤ u6 a b) ∧
    ∀ a b h ε : ℂ, ‖ε‖ ≤ 1 →
      ConcaveOn ℝ Set.univ fun t : ℝ => u6 (a + (t : ℂ) * h) (b + (t : ℂ) * ε * h)

end External.Burkholder
