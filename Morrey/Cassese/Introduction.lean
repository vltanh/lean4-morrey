module

public import Morrey.Cassese.Sverak
public import Morrey.Cassese.TwoByM
public import Morrey.Cassese.TwoByThree
public import Morrey.Cassese.Square
public import Morrey.Cassese.FourByTwo

/-!
# Section 1: Morrey's problem, the main theorems and the landscape

The main theorems of the paper, as stated in the introduction (Theorem 1.1 is Kirchheim and
Kristensen's, quoted for context: `External.KirchheimKristensen.Theorem1_1`), and the claims of
the introduction about the landscape of Morrey's problem:

* `MorreyPositive d m`: Morrey's problem has a positive answer in `d × m` (every rank-one convex
  integrand on `ℝ^{d×m}` is quasiconvex); `HomMorreyPositive p d m`: the homogeneous Morrey problem
  (Kirchheim–Kristensen) has a positive answer in `d × m` at the exponent `p` (every `p`-homogeneous
  rank-one convex integrand is quasiconvex at `0`);
* the monotonicity of both problems in the dimensions (lines 105–107 and 209–210), and the
  triviality of the case `min (d, m) ≤ 1` (lines 108–109);
* Theorems 1.2–1.5 and Corollary 1.6;
* the combined statement of lines 251–254: with Šverák's example (`Cassese.sverak_example`),
  Theorem 1.3 leaves `2 × 2` as the only nontrivial dimension in which Morrey's problem may have a
  positive answer (`morrey_landscape`); and, with Corollary 5.3, the same for the homogeneous
  problem at `p = 4` (lines 254–256 and 2137–2142, `homMorrey_landscape`).

Conditional statements. The results of other works that are out of reach of this project (or
whose construction the user has not yet decided on) are hypotheses, named after their sources,
of every statement whose proof uses them: see each docstring.
-/

@[expose] public section

open scoped Matrix

namespace Cassese

/-- Morrey's problem has a positive answer in `d × m`: every rank-one convex integrand
`f : ℝ^{d×m} → ℝ` is quasiconvex. -/
def MorreyPositive (d m : ℕ) : Prop :=
  ∀ f : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand f → RankOneConvex f → Quasiconvex f

/-- The homogeneous Morrey problem has a positive answer in `d × m` at the exponent `p`: every
`p`-homogeneous rank-one convex integrand `f : ℝ^{d×m} → ℝ` is quasiconvex at `0`. -/
def HomMorreyPositive (p : ℝ) (d m : ℕ) : Prop :=
  ∀ f : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand f → IsPHomogeneous p f → RankOneConvex f →
    QuasiconvexAt f 0

/-- **Monotonicity of Morrey's problem** (`cs-monotone`, lines 105–107): a positive answer in
`d × m` implies a positive answer in `d' × m'` whenever `d' ≤ d` and `m' ≤ m` (equivalently,
failure propagates upwards). -/
theorem morreyPositive_mono {d m d' m' : ℕ} (hd : d' ≤ d) (hm : m' ≤ m)
    (h : MorreyPositive d m) : MorreyPositive d' m' := by
  sorry

/-- **Monotonicity of the homogeneous Morrey problem** (`cs-hom-monotone`, lines 209–210): as in
the original problem, failure propagates upwards in the dimensions; that is, a positive answer in
`d × m` implies one in `d' × m'` for `d' ≤ d`, `m' ≤ m`. -/
theorem homMorreyPositive_mono {p : ℝ} (hp : 1 < p) {d m d' m' : ℕ} (hd : d' ≤ d) (hm : m' ≤ m)
    (h : HomMorreyPositive p d m) : HomMorreyPositive p d' m' := by
  sorry

/-- **Both notions reduce to convexity when min {d, m} = 1** (`cs-min-one`, lines 108–109):
rank-one convexity is convexity. -/
theorem rankOneConvex_iff_convexOn_of_min_eq_one {d m : ℕ} (h : min d m = 1)
    (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : RankOneConvex f ↔ ConvexOn ℝ Set.univ f := by
  sorry

/-- **Both notions reduce to convexity when min {d, m} = 1** (`cs-min-one`, lines 108–109):
quasiconvexity of an integrand is convexity. -/
theorem quasiconvex_iff_convexOn_of_min_eq_one {d m : ℕ} (h : min d m = 1)
    {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : IsIntegrand f) :
    Quasiconvex f ↔ ConvexOn ℝ Set.univ f := by
  sorry

/-- **Only min {d, m} ≥ 2 is nontrivial** (`cs-min-one`, lines 108–109): Morrey's problem has a
positive answer in `d × m` when `min {d, m} ≤ 1`. -/
theorem morreyPositive_of_min_le_one {d m : ℕ} (h : min d m ≤ 1) : MorreyPositive d m := by
  sorry

/-- **Theorem 1.2** (`thm:morrey`): for `p ∈ (1, ∞)` there is `m₀ (p)` such that for every
`m ≥ m₀ (p)` there is a `p`-homogeneous, rank-one convex and nowhere quasiconvex integrand
`f : ℝ^{2×m} → ℝ`. Conditional on Proposition 2.7 (1) (UMD extrapolation, HNVW), (3) (`L^p` is UMD,
Pisier) and (5) (complex UMD, Yaroslavtsev), through the finiteness of `UMD_{ℂ,p} (ℓ_q)`. -/
theorem theorem1_2 (hP : PisierLpUMD) (hH : HNVWExtrapolation)
    (hY : YaroslavtsevComplexUMD) {p : ℝ} (hp : 1 < p) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ f : Matrix (Fin 2) (Fin m) ℝ → ℝ,
      IsIntegrand f ∧ IsPHomogeneous p f ∧ RankOneConvex f ∧ NowhereQuasiconvex f := by
  sorry

/-- **Theorem 1.3**, first assertion (`thm:2x4`): there is a homogeneous quartic polynomial
`P : ℝ^{2×3} → ℝ` which is rank-one convex but nowhere quasiconvex. Conditional on Burkholder's
inequality (Theorem 2.3), which the proof uses through Lemma 5.1 (2). -/
theorem theorem1_3_a (hB : BurkholderInequality) :
    ∃ P : Matrix (Fin 2) (Fin 3) ℝ → ℝ,
      IsHomogeneousPolynomial 4 P ∧ RankOneConvex P ∧ NowhereQuasiconvex P := by
  sorry

/-- **Theorem 1.3**, second assertion (`thm:2x4`): for `p` sufficiently close to `4` there is a
`p`-homogeneous integrand `P : ℝ^{2×3} → ℝ` which is rank-one convex but nowhere quasiconvex.
Conditional on Burkholder's inequality (Theorem 2.3). -/
theorem theorem1_3_b (hB : BurkholderInequality) :
    ∃ ε > 0, ∀ p : ℝ, |p - 4| < ε → ∃ f : Matrix (Fin 2) (Fin 3) ℝ → ℝ,
      IsIntegrand f ∧ IsPHomogeneous p f ∧ RankOneConvex f ∧ NowhereQuasiconvex f := by
  sorry

/-- **Theorem 1.4** (`thm:main`): for `p ∈ (1, ∞)` there is `d₀ (p)` such that for every
`d ≥ d₀ (p)` there is a conjugation- and transposition-invariant, `p`-homogeneous integrand
`f : ℝ^{d×d} → ℝ` which is rank-one convex but nowhere quasiconvex. Conditional on
Proposition 2.7 (1), (2) (UMD extrapolation, HNVW; the UMD constant of `S_q`, Randrianantoanina),
Proposition 2.8 (decoupling, Cox–Veraar), Proposition 6.3 (non-commutative Khintchine, Pisier–Xu),
Proposition 6.4 (Kahane–Khintchine, HNVW) and Burkholder's square function inequality
(Theorem 2.3 (2)), which the proofs of Propositions 6.2 and 6.5 use. -/
theorem theorem1_4 (hH : HNVWExtrapolation)
    (hR : RandrianantoaninaSchattenUMD) (hCV : CoxVeraarDecoupling)
    (hPX : PisierXuKhintchine) (hKK : KahaneKhintchine)
    (hS : BurkholderSquareFunction) {p : ℝ} (hp : 1 < p) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∃ f : Matrix (Fin d) (Fin d) ℝ → ℝ,
      IsIntegrand f ∧ IsConjugationInvariant f ∧ IsTranspositionInvariant f ∧
        IsPHomogeneous p f ∧ RankOneConvex f ∧ NowhereQuasiconvex f := by
  sorry

/-- **Theorem 1.5** (`thm:lowdim`): for every `p ∈ (1, ∞) ∖ {2}` there is a `p`-homogeneous
integrand `f : ℝ^{4×2} → ℝ` which is rank-one convex but nowhere quasiconvex. Conditional on
Burkholder's inequality (Theorem 2.3, through Proposition 7.1), transference for homogeneous
multipliers (HNVW I, Corollary 5.7.6, through Proposition 7.2) and Dragičević's lower bound
`‖𝓑²‖_{L^p} > p* − 1` (Theorem 7.1). -/
theorem theorem1_5 (hB : BurkholderInequality)
    (hT : HNVWTransference) (hD : DragicevicLowerBound) {p : ℝ}
    (hp : 1 < p) (hp2 : p ≠ 2) :
    ∃ f : Matrix (Fin 4) (Fin 2) ℝ → ℝ,
      IsIntegrand f ∧ IsPHomogeneous p f ∧ RankOneConvex f ∧ NowhereQuasiconvex f := by
  sorry

/-- **Corollary 1.6** (`cor:1-hom`): there is a `1`-homogeneous rank-one convex integrand
`f : ℝ^{4×4} → [0, ∞)` which is not quasiconvex at a matrix of rank `2`. Conditional as
Theorem 1.5, which its proof uses (at some `p ∈ (1, 2)`). -/
theorem corollary1_6 (hB : BurkholderInequality)
    (hT : HNVWTransference) (hD : DragicevicLowerBound) :
    ∃ f : Matrix (Fin 4) (Fin 4) ℝ → ℝ, IsIntegrand f ∧ (∀ A, 0 ≤ f A) ∧ IsPHomogeneous 1 f ∧
      RankOneConvex f ∧ ∃ A : Matrix (Fin 4) (Fin 4) ℝ, A.rank = 2 ∧ ¬ QuasiconvexAt f A := by
  sorry

/-- **The 2 × 2 landscape** (`cs-landscape`, lines 251–254): "this result [Theorem 1.3] complements
Šverák's to prove that the only nontrivial instance in which Morrey's problem may have a positive
answer is `2 × 2`": for `d, m ≥ 2` with `(d, m) ≠ (2, 2)` there is a rank-one convex integrand on
`ℝ^{d×m}` that is not quasiconvex. Conditional on Burkholder's inequality, through Theorem 1.3. -/
theorem morrey_landscape (hB : BurkholderInequality) {d m : ℕ} (hd : 2 ≤ d)
    (hm : 2 ≤ m) (h22 : ¬ (d = 2 ∧ m = 2)) :
    ∃ f : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand f ∧ RankOneConvex f ∧ ¬ Quasiconvex f := by
  sorry

/-- **The homogeneous landscape** (`cs-hom-landscape`, lines 254–256 and 2137–2142): with
Corollary 5.3, the homogeneous Morrey problem (at `p = 4`) has a negative answer in every
nontrivial dimension except possibly `2 × 2`: for `d, m ≥ 2` with `(d, m) ≠ (2, 2)` there is a
`4`-homogeneous rank-one convex integrand on `ℝ^{d×m}` that is not quasiconvex at `0`.
Conditional on Burkholder's inequality, through Theorem 1.3 and Corollary 5.3. -/
theorem homMorrey_landscape (hB : BurkholderInequality) {d m : ℕ}
    (hd : 2 ≤ d) (hm : 2 ≤ m) (h22 : ¬ (d = 2 ∧ m = 2)) :
    ∃ f : Matrix (Fin d) (Fin m) ℝ → ℝ,
      IsIntegrand f ∧ IsPHomogeneous 4 f ∧ RankOneConvex f ∧ ¬ QuasiconvexAt f 0 := by
  sorry

end Cassese
