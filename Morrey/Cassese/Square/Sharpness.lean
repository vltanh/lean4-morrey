module

public import Morrey.Cassese.Square.Hermite
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The sharpness of Burkholder's constant for dyadic martingale transforms

`burkholderSharpness_holds`: for `p ∈ (1, ∞)` and `K < p* − 1` there are a dyadic (Paley–Walsh)
martingale `f_N = Σ_{k<N} ε_k φ_k` and predictable signs `σ_k` with
`‖Σ_{k<N} σ_k ε_k φ_k‖_{L^p} > K ‖f_N‖_{L^p}` (`BurkholderSharpness`, used for the lower bound of
Corollary 6.3).

The construction (the standard extremal examples, here in a dyadic form with an explicit
potential). The process `(F, G)`, `G` the `±1` transform of `F`, starts with `(±1, ±1)` and splits
to `(0, ±2)` (kept) or `(±2, 0)` (stopped). From then on it runs `M` rounds of `j + 1` steps,
with `θ = 2^{−j} / p`:

* on the axis `F = 0` (the first step of a round) it moves by `±θ G` along a line of slope `−1`,
  to `(θ|G|, (1 ∓ θ)|G|)` in absolute values;
* then (the `j` other steps) it doubles `|F|` or returns to the axis, along the line
  `|F| + |G| = S` (step `F`, sign `σ = −sgn F sgn G`): after `j` doublings it is at `|F| = |G₀| / p`,
  `|G| ≥ (p − 1) |F|`, and stops there.

For a payoff `P (|F|, |G|)` with `P (0, y) ≥ c₀ y^p` and `P (x, S − x) ≥ κ x^p` at the stopping
points, the potential that is `c_L |G|^p` on the axis with `L` rounds to go, its linear
interpolation along the ladders, and `P` at the stopped paths is a submartingale
(`bs_pot_step`), with `c_{L+1} = (1 − 2^{−j}) ((1 + (1 + 2θ)^p) / 2) c_L + 2^{−j} κ p^{−p}`; so
`E P (|F_N|, |G_N|) ≥ (P (2, 0) + 2^p c_M) / 2` (`bs_main`). The coefficients `c_L` grow like
`κ p^{−p} 2^j` (`1 − p²θ² ≤ (1 − 2^{−j}) (1 + (1 + 2θ)^p) / 2`, Bernoulli). For `p ≥ 2` the payoff
is `|G|^p − K^p |F|^p` (`f = F`, `g = G`); for `p < 2` it is `|F|^p − K^p |G|^p`, with the roles
of the martingale and its transform exchanged (`f = G`, `g = F`), and there
`(1 − 2^{−j}) (1 + (1 + 2θ)^p) / 2 ≤ 1` (Bernoulli for the exponent `p − 1 ∈ (0, 1)`) controls the
negative payoff `−K^p |G|^p` of the paths still on the axis.

Helpers have the prefix `bs`.
-/

@[expose] public section

namespace Cassese

/-- The sharpness of Burkholder's constant for dyadic martingale transforms, as used for the
lower bound of Corollary 6.3: for `p ∈ (1, ∞)` and `K < p* − 1` there are a real dyadic martingale
`f_N = Σ_{k<N} ε_k φ_k` (predictable `φ_k`) and predictable signs `σ_k` with
`‖Σ_{k<N} σ_k ε_k φ_k‖_{L^p} > K ‖f_N‖_{L^p}`.

How the paper cites it: the proof of Corollary 6.3 (TeX lines 2624–2633) takes "a dyadic
martingale `f_n` and `g_n` a `±1` transform of it" and says "by choosing the martingale-transform
pair suitably (see also [Cassese 2025, *Martingales, laminates and minimal Korn inequalities*,
J. Math. Pures Appl. 213]), this construction shows `C^{rc} (d) ≥ 4* − 1 = 3`"; it names no
source for the sharpness itself. The sharpness of `p* − 1` for dyadic (Paley–Walsh) martingales
is D. L. Burkholder, *An elementary proof of an inequality of R. E. A. C. Paley*, Bull. London
Math. Soc. 17 (1985); it also follows from the sharpness for general martingale transforms
(Burkholder, Ann. Probab. 12 (1984): `UMD_p (ℝ) = p* − 1`) and Proposition 2.7 (4)
(`HNVWDyadicUMD`, HNVW I, Theorem 4.2.5: the dyadic UMD constant is the UMD constant) with
`X = ℝ`. Neither Burkholder paper was consulted. Proved here (`burkholderSharpness_holds`), by an
explicit dyadic construction with a potential function (module docstring). -/
def BurkholderSharpness : Prop :=
  ∀ p : ℝ, 1 < p → ∀ K : ℝ, K < pStar p - 1 →
    ∃ (N : ℕ) (φ σ : Fin N → (Fin N → Bool) → ℝ), IsPredictable φ ∧ IsPredictable σ ∧
      (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) ∧
      K * lpNormWith (fun x => |x|) p (mart φ N) <
        lpNormWith (fun x => |x|) p (mart (fun k ε => σ k ε * φ k ε) N)

/-! ### The schedule and the process -/

/-- The schedule from time `2` on: `(round, step within the round)`, with rounds of `j + 1`
steps. -/
def bsSched (j : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | t + 1 => if (bsSched j t).2 = j then ((bsSched j t).1 + 1, 0)
      else ((bsSched j t).1, (bsSched j t).2 + 1)

theorem bsSched_snd_le (j t : ℕ) : (bsSched j t).2 ≤ j := by
  induction t with
  | zero => simp [bsSched]
  | succ t ih =>
    simp only [bsSched]
    split_ifs with h
    · simp
    · simp only; omega

theorem bsSched_add (j m : ℕ) : ∀ i, i ≤ j → bsSched j (m * (j + 1) + i) = (m, i) := by
  induction m with
  | zero =>
    intro i hi
    induction i with
    | zero => simp [bsSched]
    | succ i ih =>
      rw [Nat.zero_mul, Nat.zero_add] at ih ⊢
      rw [bsSched, ih (by omega), ite_eq_right (by simp only; omega)]
  | succ m ihm =>
    intro i hi
    induction i with
    | zero =>
      have e : (m + 1) * (j + 1) + 0 = (m * (j + 1) + j) + 1 := by ring
      rw [e, bsSched, ihm j le_rfl, ite_eq_left rfl]
    | succ i ih =>
      rw [← Nat.add_assoc, bsSched, ih (by omega), ite_eq_right (by simp only; omega)]

theorem bsSched_end (j M : ℕ) : bsSched j (M * (j + 1)) = (M, 0) := by
  simpa using bsSched_add j M 0 (Nat.zero_le _)

theorem bsSched_eq (j t : ℕ) : (bsSched j t).1 * (j + 1) + (bsSched j t).2 = t := by
  induction t with
  | zero => simp [bsSched]
  | succ t ih =>
    simp only [bsSched]
    split_ifs with h
    · simp only; rw [h] at ih; linarith
    · simp only; omega

theorem bsSched_fst_lt {j M t : ℕ} (ht : t < M * (j + 1)) : (bsSched j t).1 < M := by
  by_contra h
  have h1 := bsSched_eq j t
  have : M * (j + 1) ≤ (bsSched j t).1 * (j + 1) := Nat.mul_le_mul_right _ (not_lt.1 h)
  omega

/-- The sign of a real number, `sgn 0 = 1`. -/
noncomputable def bsSgn (x : ℝ) : ℝ := if x < 0 then -1 else 1

theorem bsSgn_mul_self (x : ℝ) : bsSgn x * x = |x| := by
  unfold bsSgn; split_ifs with h
  · rw [abs_of_neg h]; ring
  · rw [abs_of_nonneg (not_lt.1 h)]; ring

theorem bsSgn_mul_abs (x : ℝ) : bsSgn x * |x| = x := by
  unfold bsSgn; split_ifs with h
  · rw [abs_of_neg h]; ring
  · rw [abs_of_nonneg (not_lt.1 h)]; ring

theorem bsSgn_cases (x : ℝ) : bsSgn x = 1 ∨ bsSgn x = -1 := by
  unfold bsSgn; split_ifs <;> simp

theorem bsSgn_abs (x : ℝ) : |bsSgn x| = 1 := by
  rcases bsSgn_cases x with h | h <;> rw [h] <;> simp

/-- The state of the process: the martingale `F`, its transform `G`, and whether the path still
runs. -/
structure BsState where
  F : ℝ
  G : ℝ
  alive : Bool

/-- The step `(φ, σ)` at time `k` from the state `s`. -/
noncomputable def bsStep (θ : ℝ) (j : ℕ) : ℕ → BsState → ℝ × ℝ
  | 0, _ => (1, 1)
  | 1, s => (s.F, -1)
  | k + 2, s => if (bsSched j k).2 = 0 then ((if s.alive then θ * s.G else 0), -1)
      else ((if s.alive then s.F else 0), -(bsSgn s.F * bsSgn s.G))

/-- The steps at which the paths off the axis stop: the initial split and the last step of each
round. -/
def bsEnds (j : ℕ) : ℕ → Prop
  | 0 => False
  | 1 => True
  | k + 2 => (bsSched j k).2 = j

open Classical in
/-- One step of the process, with the sign `e = ±1`. -/
noncomputable def bsNext (θ : ℝ) (j k : ℕ) (s : BsState) (e : ℝ) : BsState :=
  ⟨s.F + e * (bsStep θ j k s).1, s.G + e * ((bsStep θ j k s).2 * (bsStep θ j k s).1),
    if bsEnds j k ∧ s.F + e * (bsStep θ j k s).1 ≠ 0 then false else s.alive⟩

/-- The state at time `k`. -/
noncomputable def bsState (θ : ℝ) (j N : ℕ) : ℕ → (Fin N → Bool) → BsState
  | 0, _ => ⟨0, 0, true⟩
  | k + 1, ε => bsNext θ j k (bsState θ j N k ε) (if h : k < N then coin (ε ⟨k, h⟩) else 1)

/-- The increments `φ_k`. -/
noncomputable def bsPhi (θ : ℝ) (j N : ℕ) (k : Fin N) (ε : Fin N → Bool) : ℝ :=
  (bsStep θ j k (bsState θ j N k ε)).1

/-- The signs `σ_k` of the transform. -/
noncomputable def bsSig (θ : ℝ) (j N : ℕ) (k : Fin N) (ε : Fin N → Bool) : ℝ :=
  (bsStep θ j k (bsState θ j N k ε)).2

theorem bsState_congr (θ : ℝ) (j N : ℕ) :
    ∀ (k : ℕ) (ε ε' : Fin N → Bool), (∀ i : Fin N, i.val < k → ε i = ε' i) →
      bsState θ j N k ε = bsState θ j N k ε' := by
  intro k
  induction k with
  | zero => intro ε ε' _; rfl
  | succ k ih =>
    intro ε ε' h
    simp only [bsState]
    rw [ih ε ε' fun i hi => h i (by omega)]
    congr 1
    split_ifs with hk
    · rw [h ⟨k, hk⟩ (by simp)]
    · rfl

theorem bsPhi_predictable (θ : ℝ) (j N : ℕ) : IsPredictable (bsPhi θ j N) := by
  intro k ε ε' h
  simp only [bsPhi]
  rw [bsState_congr θ j N k ε ε' fun i hi => h i (Fin.lt_def.2 hi)]

theorem bsSig_predictable (θ : ℝ) (j N : ℕ) : IsPredictable (bsSig θ j N) := by
  intro k ε ε' h
  simp only [bsSig]
  rw [bsState_congr θ j N k ε ε' fun i hi => h i (Fin.lt_def.2 hi)]

theorem bsStep_snd_cases (θ : ℝ) (j k : ℕ) (s : BsState) :
    (bsStep θ j k s).2 = 1 ∨ (bsStep θ j k s).2 = -1 := by
  match k with
  | 0 => simp [bsStep]
  | 1 => simp [bsStep]
  | k + 2 =>
    by_cases h : (bsSched j k).2 = 0
    · simp [bsStep, h]
    · simp only [bsStep, h, ite_false]
      rcases bsSgn_cases s.F with h1 | h1 <;> rcases bsSgn_cases s.G with h2 | h2 <;>
        simp [h1, h2]

theorem bsSig_cases (θ : ℝ) (j N : ℕ) (k : Fin N) (ε : Fin N → Bool) :
    bsSig θ j N k ε = 1 ∨ bsSig θ j N k ε = -1 :=
  bsStep_snd_cases θ j k _

/-- The martingale is the first coordinate of the state. -/
theorem bs_mart_F (θ : ℝ) (j N : ℕ) (ε : Fin N → Bool) :
    ∀ n, n ≤ N → mart (bsPhi θ j N) n ε = (bsState θ j N n ε).F := by
  intro n
  induction n with
  | zero => intro _; simp [mart, bsState]
  | succ n ih =>
    intro hn
    have hn' : n < N := by omega
    have h1 : mart (bsPhi θ j N) (n + 1) ε =
        mart (bsPhi θ j N) n ε + coin (ε ⟨n, hn'⟩) * bsPhi θ j N ⟨n, hn'⟩ ε := by
      simp only [mart, smul_eq_mul]; exact square_sum_filter_succ hn' _
    rw [h1, ih hn'.le]
    simp only [bsState, dite_eq_left hn', bsNext, bsPhi]

/-- The transform is the second coordinate of the state. -/
theorem bs_mart_G (θ : ℝ) (j N : ℕ) (ε : Fin N → Bool) :
    ∀ n, n ≤ N →
      mart (fun k ε => bsSig θ j N k ε * bsPhi θ j N k ε) n ε = (bsState θ j N n ε).G := by
  intro n
  induction n with
  | zero => intro _; simp [mart, bsState]
  | succ n ih =>
    intro hn
    have hn' : n < N := by omega
    have h1 : mart (fun k ε => bsSig θ j N k ε * bsPhi θ j N k ε) (n + 1) ε =
        mart (fun k ε => bsSig θ j N k ε * bsPhi θ j N k ε) n ε +
          coin (ε ⟨n, hn'⟩) * (bsSig θ j N ⟨n, hn'⟩ ε * bsPhi θ j N ⟨n, hn'⟩ ε) := by
      simp only [mart, smul_eq_mul]; exact square_sum_filter_succ hn' _
    rw [h1, ih hn'.le]
    simp only [bsState, dite_eq_left hn', bsNext, bsPhi, bsSig]


/-! ### The steps of the process -/

section Steps

variable {θ : ℝ} {j : ℕ}

theorem bsNext_zero (s : BsState) (e : ℝ) :
    bsNext θ j 0 s e = ⟨s.F + e, s.G + e, s.alive⟩ := by
  simp [bsNext, bsStep, bsEnds]

theorem bsNext_one (s : BsState) (e : ℝ) :
    bsNext θ j 1 s e = ⟨s.F + e * s.F, s.G - e * s.F,
      if s.F + e * s.F ≠ 0 then false else s.alive⟩ := by
  simp only [bsNext, bsStep, bsEnds, true_and]
  congr 1; ring

/-- A stopped path does not move. -/
theorem bsNext_dead (k : ℕ) (s : BsState) (h : s.alive = false) (e : ℝ) :
    bsNext θ j (k + 2) s e = s := by
  have hs : (bsStep θ j (k + 2) s).1 = 0 := by
    simp only [bsStep, h]; split_ifs <;> simp_all
  rcases s with ⟨F, G, a⟩
  simp only at h
  subst h
  simp only [bsNext, hs, mul_zero, add_zero, ite_self]

/-- The first step of a round, from the axis. -/
theorem bsNext_axis (hj : j ≠ 0) (k : ℕ) (s : BsState) (hal : s.alive = true)
    (hi : (bsSched j k).2 = 0) (e : ℝ) :
    bsNext θ j (k + 2) s e = ⟨s.F + e * (θ * s.G), s.G - e * (θ * s.G), true⟩ := by
  simp only [bsNext, bsStep, bsEnds, hi, hal, ite_true, Ne.symm hj, false_and, ite_false]
  congr 1; ring

/-- A step of a ladder. -/
theorem bsNext_ladder (k : ℕ) (s : BsState) (hal : s.alive = true) (hi : (bsSched j k).2 ≠ 0)
    (e : ℝ) :
    bsNext θ j (k + 2) s e = ⟨s.F + e * s.F, s.G - e * (bsSgn s.G * |s.F|),
      if (bsSched j k).2 = j ∧ s.F + e * s.F ≠ 0 then false else true⟩ := by
  simp only [bsNext, bsStep, bsEnds, hi, hal, ite_true, ite_false]
  congr 1
  rw [← bsSgn_mul_self s.F]; ring

end Steps

/-! ### The potential -/

/-- The coefficients `c_L` of the potential on the axis, `L` rounds before the end. -/
noncomputable def bsC (c₀ a b : ℝ) : ℕ → ℝ
  | 0 => c₀
  | L + 1 => a * bsC c₀ a b L + b

/-- The potential at time `k`: `w₀` at times `0, 1`; the payoff `P (|F|, |G|)` at stopped paths;
`c_L |G|^p` on the axis (`L` rounds to go); and along a ladder, at the step `i` of the round, with
`λ = 2^{−(j − i + 1)}`, the interpolation `(1 − λ) c_L (|F| + |G|)^p + λ κ (|F| / λ)^p` between the
axis and the stopping point `|F| / λ`. -/
noncomputable def bsPot (P : ℝ → ℝ → ℝ) (c : ℕ → ℝ) (κ p w₀ : ℝ) (j M : ℕ) :
    ℕ → BsState → ℝ
  | 0, _ => w₀
  | 1, _ => w₀
  | k + 2, s =>
    if s.alive = false then P |s.F| |s.G|
    else if (bsSched j k).2 = 0 then c (M - (bsSched j k).1) * |s.G| ^ p
    else if s.F = 0 then c (M - (bsSched j k).1 - 1) * |s.G| ^ p
    else (1 - (1 / 2 : ℝ) ^ (j - (bsSched j k).2 + 1)) * c (M - (bsSched j k).1 - 1) *
        (|s.F| + |s.G|) ^ p +
      (1 / 2 : ℝ) ^ (j - (bsSched j k).2 + 1) * κ *
        (|s.F| / (1 / 2 : ℝ) ^ (j - (bsSched j k).2 + 1)) ^ p

/-- The invariant of the reachable states. -/
def bsInv (θ p : ℝ) (j : ℕ) : ℕ → BsState → Prop
  | 0, s => s.F = 0 ∧ s.G = 0 ∧ s.alive = true
  | 1, s => s.alive = true ∧ s.G = s.F ∧ |s.F| = 1
  | k + 2, s => s.alive = true →
      ((bsSched j k).2 = 0 → s.F = 0) ∧
      ((bsSched j k).2 ≠ 0 → s.F ≠ 0 →
        p * (|s.F| / (1 / 2 : ℝ) ^ (j - (bsSched j k).2 + 1)) ≤ |s.F| + |s.G| ∧
        |s.F| + |s.G| ≤ (1 + 2 * θ) * p * (|s.F| / (1 / 2 : ℝ) ^ (j - (bsSched j k).2 + 1)))

theorem bsSched_succ (j k : ℕ) : bsSched j (k + 1) = if (bsSched j k).2 = j then
    ((bsSched j k).1 + 1, 0) else ((bsSched j k).1, (bsSched j k).2 + 1) := rfl

section Pot

variable {P : ℝ → ℝ → ℝ} {θ κ p c₀ : ℝ} {j M : ℕ}

/-- `|e x| = |x|` for `e = ±1`. -/
theorem bs_abs_mul_sign {e : ℝ} (he : e = 1 ∨ e = -1) (x : ℝ) : |e * x| = |x| := by
  rcases he with rfl | rfl <;> simp

/-- The invariant is preserved. -/
theorem bs_inv_step (hp : 1 ≤ p) (hj : 1 ≤ j) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hθ : (1 / 2 : ℝ) ^ j = p * θ) (k : ℕ) (s : BsState) (hs : bsInv θ p j k s)
    {e : ℝ} (he : e = 1 ∨ e = -1) : bsInv θ p j (k + 1) (bsNext θ j k s e) := by
  match k with
  | 0 =>
    obtain ⟨hF, hG, hal⟩ := hs
    rw [bsNext_zero]
    refine ⟨hal, by simp only [hF, hG], ?_⟩
    simp only [hF, zero_add]
    rcases he with rfl | rfl <;> simp
  | 1 =>
    obtain ⟨hal, hGF, hF1⟩ := hs
    rw [bsNext_one]
    intro hal'
    have h0 : s.F + e * s.F = 0 := by
      by_contra h
      simp only [h, ne_eq, not_false_eq_true, ite_true] at hal'
      exact Bool.false_ne_true hal'
    refine ⟨fun _ => h0, fun hi => absurd ?_ hi⟩
    simp [bsSched]
  | k + 2 =>
    intro hal'
    by_cases hal : s.alive = true
    swap
    · have : s.alive = false := by simpa using hal
      rw [bsNext_dead k s this] at hal'
      exact absurd hal' (by simp [this])
    obtain ⟨hax, hlad⟩ := hs hal
    have hsucc := bsSched_succ j k
    by_cases hi : (bsSched j k).2 = 0
    · -- the first step of a round
      have hF := hax hi
      have hne : (bsSched j k).2 ≠ j := by rw [hi]; omega
      rw [bsNext_axis (by omega) k s hal hi]
      rw [hsucc, ite_eq_right hne]
      simp only [hi, zero_add, one_ne_zero, IsEmpty.forall_iff, true_and, ne_eq,
        not_false_eq_true, forall_const, hF]
      intro hF'
      have hl : (1 / 2 : ℝ) ^ (j - 1 + 1) = p * θ := by rw [Nat.sub_add_cancel hj, hθ]
      rw [hl]
      have hp0 : 0 < p := by linarith
      have hG : |e * (θ * s.G)| = θ * |s.G| := by
        rw [bs_abs_mul_sign he, abs_mul, abs_of_pos hθ0]
      have hG' : |s.G - e * (θ * s.G)| = (1 - e * θ) * |s.G| := by
        rw [show s.G - e * (θ * s.G) = (1 - e * θ) * s.G by ring, abs_mul,
          abs_of_nonneg (by rcases he with rfl | rfl <;> linarith)]
      have hX : θ * |s.G| / (p * θ) = |s.G| / p := by field_simp
      have hpp : p * (|s.G| / p) = |s.G| := by field_simp
      rw [hG, hG', hX, hpp, mul_assoc (1 + 2 * θ), hpp]
      constructor
      · rcases he with rfl | rfl <;> nlinarith [abs_nonneg s.G]
      · rcases he with rfl | rfl <;> nlinarith [abs_nonneg s.G]
    · -- a step of a ladder
      rw [bsNext_ladder k s hal hi] at hal' ⊢
      have hal'' := hal'
      by_cases hF : s.F = 0
      · simp only [hF, mul_zero, add_zero]
        rw [hsucc]
        split_ifs with hj' <;> simp
      · obtain ⟨h1, h2⟩ := hlad hi hF
        have hij : (bsSched j k).2 ≤ j := bsSched_snd_le j k
        by_cases hij' : (bsSched j k).2 = j
        · -- the last step: only the paths back on the axis survive
          have h0 : s.F + e * s.F = 0 := by
            by_contra h
            simp only [hij', h, ne_eq, not_false_eq_true, and_self, ite_true] at hal''
            exact Bool.false_ne_true hal''
          rw [hsucc, ite_eq_left hij']
          exact ⟨fun _ => h0, fun h => absurd rfl h⟩
        · rw [hsucc, ite_eq_right hij']
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, IsEmpty.forall_iff, true_and,
            ne_eq, not_false_eq_true, forall_const]
          intro hF'
          have he1 : e = 1 := by
            rcases he with rfl | rfl
            · rfl
            · exact absurd (by ring) hF'
          subst he1
          have hl : (1 / 2 : ℝ) ^ (j - ((bsSched j k).2 + 1) + 1) =
              2 * (1 / 2 : ℝ) ^ (j - (bsSched j k).2 + 1) := by
            rw [show j - (bsSched j k).2 + 1 = (j - ((bsSched j k).2 + 1) + 1) + 1 by omega,
              pow_succ]; ring
          have hl0 : 0 < (1 / 2 : ℝ) ^ (j - (bsSched j k).2 + 1) := by positivity
          have hl2 : (1 / 2 : ℝ) ^ (j - (bsSched j k).2 + 1) ≤ 1 / 2 := by
            calc (1 / 2 : ℝ) ^ (j - (bsSched j k).2 + 1) ≤ (1 / 2) ^ 1 :=
                  pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
              _ = 1 / 2 := by norm_num
          set l := (1 / 2 : ℝ) ^ (j - (bsSched j k).2 + 1) with hldef
          have hx0 : 0 < |s.F| := abs_pos.2 hF
          -- `|G| ≥ |F|` on the ladder
          have hGF : |s.F| ≤ |s.G| := by
            have : 2 * |s.F| ≤ |s.F| / l := by
              rw [le_div_iff₀ hl0]; nlinarith
            nlinarith
          have hF2 : |s.F + 1 * s.F| = 2 * |s.F| := by
            rw [one_mul, ← two_mul, abs_mul, abs_two]
          have hG2 : |s.G - 1 * (bsSgn s.G * |s.F|)| = |s.G| - |s.F| := by
            have e1 : s.G - 1 * (bsSgn s.G * |s.F|) = bsSgn s.G * (|s.G| - |s.F|) := by
              rw [mul_sub, bsSgn_mul_abs]; ring
            rw [e1, abs_mul, bsSgn_abs, one_mul, abs_of_nonneg (sub_nonneg.2 hGF)]
          rw [hF2, hG2, hl, mul_div_mul_left _ _ two_ne_zero]
          constructor <;> linarith


theorem bsPot_dead {c : ℕ → ℝ} {w₀ : ℝ} (k : ℕ) (s : BsState) (h : s.alive = false) :
    bsPot P c κ p w₀ j M (k + 2) s = P |s.F| |s.G| := by
  simp [bsPot, h]

theorem bsPot_axis {c : ℕ → ℝ} {w₀ : ℝ} (k : ℕ) (s : BsState) (h : s.alive = true)
    (hi : (bsSched j k).2 = 0) :
    bsPot P c κ p w₀ j M (k + 2) s = c (M - (bsSched j k).1) * |s.G| ^ p := by
  simp [bsPot, h, hi]

theorem bsPot_lad0 {c : ℕ → ℝ} {w₀ : ℝ} (k : ℕ) (s : BsState) (h : s.alive = true)
    (hi : (bsSched j k).2 ≠ 0) (hF : s.F = 0) :
    bsPot P c κ p w₀ j M (k + 2) s = c (M - (bsSched j k).1 - 1) * |s.G| ^ p := by
  simp [bsPot, h, hi, hF]

theorem bsPot_lad {c : ℕ → ℝ} {w₀ : ℝ} (k : ℕ) (s : BsState) (h : s.alive = true)
    (hi : (bsSched j k).2 ≠ 0) (hF : s.F ≠ 0) :
    bsPot P c κ p w₀ j M (k + 2) s =
      (1 - (1 / 2 : ℝ) ^ (j - (bsSched j k).2 + 1)) * c (M - (bsSched j k).1 - 1) *
          (|s.F| + |s.G|) ^ p +
        (1 / 2 : ℝ) ^ (j - (bsSched j k).2 + 1) * κ *
          (|s.F| / (1 / 2 : ℝ) ^ (j - (bsSched j k).2 + 1)) ^ p := by
  simp [bsPot, h, hi, hF]

/-- The potential is a submartingale along the process: at every reachable state, its value is
at most the mean of its values at the two successors. -/
theorem bs_pot_step (hp : 1 ≤ p) (hj : 1 ≤ j) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hθ : (1 / 2 : ℝ) ^ j = p * θ) {c : ℕ → ℝ} {w₀ : ℝ}
    (hc : ∀ L, c (L + 1) = (1 - (1 / 2 : ℝ) ^ j) * ((1 + (1 + 2 * θ) ^ p) / 2) * c L +
      (1 / 2 : ℝ) ^ j * κ * (1 / p) ^ p)
    (htop : ∀ x S, 0 < x → p * x ≤ S → S ≤ (1 + 2 * θ) * p * x → κ * x ^ p ≤ P x (S - x))
    (hw₀ : w₀ = (P 2 0 + c M * 2 ^ p) / 2)
    (k : ℕ) (hk : k < M * (j + 1) + 2) (s : BsState) (hs : bsInv θ p j k s) :
    bsPot P c κ p w₀ j M k s ≤
      (bsPot P c κ p w₀ j M (k + 1) (bsNext θ j k s 1) +
        bsPot P c κ p w₀ j M (k + 1) (bsNext θ j k s (-1))) / 2 := by
  have hp0 : 0 < p := by linarith
  match k with
  | 0 => simp only [bsPot]; linarith
  | 1 =>
    obtain ⟨hal, hGF, hF1⟩ := hs
    have hF0 : s.F ≠ 0 := by intro h; rw [h, abs_zero] at hF1; exact zero_ne_one hF1
    have h1 : s.F + 1 * s.F ≠ 0 := by intro h; apply hF0; linarith
    have h2 : s.F + -1 * s.F = 0 := by ring
    have hA : bsPot P c κ p w₀ j M (0 + 2) (bsNext θ j 1 s 1) = P 2 0 := by
      rw [bsNext_one]
      simp only [ne_eq, h1, not_false_eq_true, ite_true]
      rw [bsPot_dead 0 _ rfl]
      simp only
      rw [hGF, show s.F + 1 * s.F = 2 * s.F by ring, show s.F - 1 * s.F = 0 by ring, abs_mul,
        hF1, abs_zero, abs_two, mul_one]
    have hB : bsPot P c κ p w₀ j M (0 + 2) (bsNext θ j 1 s (-1)) = c M * 2 ^ p := by
      rw [bsNext_one]
      simp only [h2, ne_eq, not_true_eq_false, ite_false]
      rw [bsPot_axis 0 ⟨0, s.G - -1 * s.F, s.alive⟩ hal rfl]
      simp only [bsSched, Nat.sub_zero]
      rw [hGF, show s.F - -1 * s.F = 2 * s.F by ring, abs_mul, hF1, abs_two, mul_one]
    show w₀ ≤ (bsPot P c κ p w₀ j M (0 + 2) _ + bsPot P c κ p w₀ j M (0 + 2) _) / 2
    rw [hA, hB, hw₀]
  | k + 2 =>
    have hk' : k < M * (j + 1) := by omega
    have hm : (bsSched j k).1 < M := bsSched_fst_lt hk'
    have hsucc := bsSched_succ j k
    rw [show k + 2 + 1 = k + 1 + 2 from rfl]
    by_cases hal : s.alive = true
    swap
    · have hd : s.alive = false := by simpa using hal
      rw [bsNext_dead k s hd, bsNext_dead k s hd, bsPot_dead _ s hd, bsPot_dead _ s hd]
      linarith
    obtain ⟨hax, hlad⟩ := hs hal
    set m := (bsSched j k).1 with hmdef
    set L := M - m - 1 with hLdef
    have hML : M - m = L + 1 := by omega
    by_cases hi : (bsSched j k).2 = 0
    · -- the first step of a round, from the axis
      have hF := hax hi
      have hne : (bsSched j k).2 ≠ j := by rw [hi]; omega
      have hs1 : bsSched j (k + 1) = (m, 1) := by rw [hsucc, ite_eq_right hne, hi]
      rw [bsNext_axis (by omega) k s hal hi, bsNext_axis (by omega) k s hal hi,
        bsPot_axis k s hal hi, hML]
      simp only [hF, zero_add]
      by_cases hG : s.G = 0
      · have h0 : ∀ e : ℝ, bsPot P c κ p w₀ j M (k + 1 + 2)
            ⟨e * (θ * s.G), s.G - e * (θ * s.G), true⟩ = 0 := fun e => by
          rw [bsPot_lad0 (k + 1) _ rfl (by rw [hs1]; simp) (by simp [hG])]
          simp [hG, Real.zero_rpow hp0.ne']
        rw [h0, h0, hG, abs_zero, Real.zero_rpow hp0.ne']
        simp
      · have hl : (1 / 2 : ℝ) ^ (j - (bsSched j (k + 1)).2 + 1) = p * θ := by
          rw [hs1]; simp only; rw [Nat.sub_add_cancel hj, hθ]
        have hval : ∀ e : ℝ, (e = 1 ∨ e = -1) → bsPot P c κ p w₀ j M (k + 1 + 2)
            ⟨e * (θ * s.G), s.G - e * (θ * s.G), true⟩ =
              (1 - p * θ) * c L * ((1 + θ - e * θ) * |s.G|) ^ p +
                p * θ * κ * ((1 / p) * |s.G|) ^ p := by
          intro e he
          have hne0 : e * (θ * s.G) ≠ 0 := by
            refine mul_ne_zero ?_ (mul_ne_zero hθ0.ne' hG)
            rcases he with rfl | rfl <;> norm_num
          rw [bsPot_lad (k + 1) _ rfl (by rw [hs1]; simp) hne0, hl, hs1]
          simp only
          have hG1 : |e * (θ * s.G)| = θ * |s.G| := by
            rw [bs_abs_mul_sign he, abs_mul, abs_of_pos hθ0]
          have hG2 : |s.G - e * (θ * s.G)| = (1 - e * θ) * |s.G| := by
            rw [show s.G - e * (θ * s.G) = (1 - e * θ) * s.G by ring, abs_mul,
              abs_of_nonneg (by rcases he with rfl | rfl <;> linarith)]
          rw [hG1, hG2, ← hLdef,
            show θ * |s.G| + (1 - e * θ) * |s.G| = (1 + θ - e * θ) * |s.G| by ring,
            show θ * |s.G| / (p * θ) = 1 / p * |s.G| by field_simp]
        have hGp : 0 ≤ |s.G| := abs_nonneg _
        have e1 : ((1 + 2 * θ) * |s.G|) ^ p = (1 + 2 * θ) ^ p * |s.G| ^ p :=
          Real.mul_rpow (by linarith) hGp
        have e2 : ((1 / p) * |s.G|) ^ p = (1 / p) ^ p * |s.G| ^ p :=
          Real.mul_rpow (by positivity) hGp
        rw [hval 1 (Or.inl rfl), hval (-1) (Or.inr rfl), hc L, hθ,
          show (1 + θ - 1 * θ) = (1 : ℝ) by ring, show (1 + θ - -1 * θ) = 1 + 2 * θ by ring, e1,
          e2, one_mul]
        apply le_of_eq; ring
    · -- a step of a ladder
      rw [bsNext_ladder k s hal hi, bsNext_ladder k s hal hi]
      have hij : (bsSched j k).2 ≤ j := bsSched_snd_le j k
      by_cases hF : s.F = 0
      · -- a path back on the axis waits
        simp only [hF, mul_zero, add_zero, abs_zero, sub_zero, ne_eq, not_true_eq_false,
          and_false, ite_false]
        rw [bsPot_lad0 k s hal hi hF]
        by_cases hij' : (bsSched j k).2 = j
        · have hs1 : bsSched j (k + 1) = (m + 1, 0) := by rw [hsucc, ite_eq_left hij']
          rw [bsPot_axis (k + 1) _ rfl (by rw [hs1]), hs1]
          simp only
          rw [show M - (m + 1) = M - m - 1 by omega]
          linarith
        · have hs1 : bsSched j (k + 1) = (m, (bsSched j k).2 + 1) := by
            rw [hsucc, ite_eq_right hij']
          rw [bsPot_lad0 (k + 1) _ rfl (by rw [hs1]; simp) rfl, hs1]
          linarith
      · obtain ⟨h1, h2⟩ := hlad hi hF
        rw [bsPot_lad k s hal hi hF]
        set i := (bsSched j k).2 with hidef
        set l := (1 / 2 : ℝ) ^ (j - i + 1) with hldef
        have hl0 : 0 < l := by positivity
        have hl2 : l ≤ 1 / 2 := by
          calc l ≤ (1 / 2 : ℝ) ^ 1 :=
                pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
            _ = 1 / 2 := by norm_num
        have hx0 : 0 < |s.F| := abs_pos.2 hF
        have hGF : |s.F| ≤ |s.G| := by
          have : 2 * |s.F| ≤ |s.F| / l := by rw [le_div_iff₀ hl0]; nlinarith
          nlinarith
        have hF2 : |s.F + 1 * s.F| = 2 * |s.F| := by
          rw [one_mul, ← two_mul, abs_mul, abs_two]
        have hG2 : |s.G - 1 * (bsSgn s.G * |s.F|)| = |s.G| - |s.F| := by
          have e1 : s.G - 1 * (bsSgn s.G * |s.F|) = bsSgn s.G * (|s.G| - |s.F|) := by
            rw [mul_sub, bsSgn_mul_abs]; ring
          rw [e1, abs_mul, bsSgn_abs, one_mul, abs_of_nonneg (sub_nonneg.2 hGF)]
        have hG3 : |s.G - -1 * (bsSgn s.G * |s.F|)| = |s.G| + |s.F| := by
          have e1 : s.G - -1 * (bsSgn s.G * |s.F|) = bsSgn s.G * (|s.G| + |s.F|) := by
            rw [mul_add, bsSgn_mul_abs]; ring
          rw [e1, abs_mul, bsSgn_abs, one_mul, abs_of_nonneg (by positivity)]
        have hF3 : s.F + -1 * s.F = 0 := by ring
        have hF1 : s.F + 1 * s.F ≠ 0 := by
          rw [one_mul, ← two_mul]; exact mul_ne_zero two_ne_zero hF
        simp only [hF3, ne_eq, not_true_eq_false, and_false, ite_false]
        by_cases hij' : i = j
        · -- the last step: the path stops at `|F| = 2 |F_prev|`, or returns to the axis
          have hs1 : bsSched j (k + 1) = (m + 1, 0) := by rw [hsucc, ite_eq_left hij']
          have hl1 : l = 1 / 2 := by rw [hldef, hij', Nat.sub_self]; norm_num
          simp only [hij', hF1, not_false_eq_true, and_self, ite_true]
          rw [bsPot_dead (k + 1) _ rfl, bsPot_axis (k + 1) _ rfl (by rw [hs1]), hs1]
          simp only
          rw [hF2, hG2, hG3, show M - (m + 1) = M - m - 1 by omega, ← hLdef, hl1]
          have hx : |s.F| / (1 / 2) = 2 * |s.F| := by field_simp
          rw [hl1, hx] at h1 h2
          have htop' := htop (2 * |s.F|) (|s.F| + |s.G|) (by positivity) h1 h2
          rw [show |s.F| + |s.G| - 2 * |s.F| = |s.G| - |s.F| by ring] at htop'
          rw [hx, show |s.G| + |s.F| = |s.F| + |s.G| by ring]
          linarith
        · -- a middle step: the path doubles `|F|` or returns to the axis
          have hs1 : bsSched j (k + 1) = (m, i + 1) := by rw [hsucc, ite_eq_right hij']
          simp only [hij', false_and, ite_false]
          rw [bsPot_lad (k + 1) _ rfl (by rw [hs1]; simp) hF1, bsPot_lad0 (k + 1) _ rfl
            (by rw [hs1]; simp) rfl, hs1]
          simp only
          have hl' : (1 / 2 : ℝ) ^ (j - (i + 1) + 1) = 2 * l := by
            rw [hldef, show j - i + 1 = (j - (i + 1) + 1) + 1 by omega, pow_succ]; ring
          rw [hl', hF2, hG2, hG3, ← hLdef]
          have hx : 2 * |s.F| / (2 * l) = |s.F| / l := by field_simp
          rw [hx, show 2 * |s.F| + (|s.G| - |s.F|) = |s.F| + |s.G| by ring,
            show |s.G| + |s.F| = |s.F| + |s.G| by ring]
          apply le_of_eq; ring


theorem bs_coin_cases (b : Bool) : coin b = 1 ∨ coin b = -1 := by
  cases b <;> simp [coin]

/-- **The potential argument**: with `N = M (j + 1) + 2`,
`(P (2, 0) + 2^p c_M) / 2 ≤ E P (|F_N|, |G_N|)`. -/
theorem bs_main (hp : 1 ≤ p) (hj : 1 ≤ j) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hθ : (1 / 2 : ℝ) ^ j = p * θ) {c : ℕ → ℝ}
    (hc : ∀ L, c (L + 1) = (1 - (1 / 2 : ℝ) ^ j) * ((1 + (1 + 2 * θ) ^ p) / 2) * c L +
      (1 / 2 : ℝ) ^ j * κ * (1 / p) ^ p)
    (htop : ∀ x S, 0 < x → p * x ≤ S → S ≤ (1 + 2 * θ) * p * x → κ * x ^ p ≤ P x (S - x))
    (h0 : ∀ y, 0 ≤ y → c 0 * y ^ p ≤ P 0 y) :
    (P 2 0 + c M * 2 ^ p) / 2 ≤
      avg (fun ε : Fin (M * (j + 1) + 2) → Bool =>
        P |(bsState θ j (M * (j + 1) + 2) (M * (j + 1) + 2) ε).F|
          |(bsState θ j (M * (j + 1) + 2) (M * (j + 1) + 2) ε).G|) := by
  set N := M * (j + 1) + 2 with hN
  set w₀ := (P 2 0 + c M * 2 ^ p) / 2 with hw₀
  -- the invariant along the process
  have hinv : ∀ k, k ≤ N → ∀ ε, bsInv θ p j k (bsState θ j N k ε) := by
    intro k
    induction k with
    | zero => intro _ ε; exact ⟨rfl, rfl, rfl⟩
    | succ k ih =>
      intro hk ε
      have hk' : k < N := by omega
      have e : bsState θ j N (k + 1) ε = bsNext θ j k (bsState θ j N k ε) (coin (ε ⟨k, hk'⟩)) := by
        simp only [bsState, dite_eq_left hk']
      rw [e]
      exact bs_inv_step hp hj hθ0 hθ1 hθ k _ (ih hk'.le ε) (bs_coin_cases _)
  -- the potential increases on average
  have hstep : ∀ k, k < N → avg (fun ε => bsPot P c κ p w₀ j M k (bsState θ j N k ε)) ≤
      avg (fun ε => bsPot P c κ p w₀ j M (k + 1) (bsState θ j N (k + 1) ε)) := by
    intro k hk
    set K : Fin N := ⟨k, hk⟩ with hK
    set g := fun ε => bsPot P c κ p w₀ j M (k + 1) (bsState θ j N (k + 1) ε) with hgdef
    have hflip : ∀ ε, bsState θ j N k (rad_flip K ε) = bsState θ j N k ε := fun ε =>
      bsState_congr θ j N k _ _ fun i hi =>
        rad_flip_apply_ne (fun h => by rw [h] at hi; exact lt_irrefl _ hi) ε
    have hg : ∀ ε, g ε = bsPot P c κ p w₀ j M (k + 1)
        (bsNext θ j k (bsState θ j N k ε) (coin (ε K))) := fun ε => by
      simp only [g, bsState, dite_eq_left hk, hK]
    have hg' : ∀ ε, g (rad_flip K ε) = bsPot P c κ p w₀ j M (k + 1)
        (bsNext θ j k (bsState θ j N k ε) (-coin (ε K))) := fun ε => by
      rw [hg, hflip, square_coin_flip]
    calc avg (fun ε => bsPot P c κ p w₀ j M k (bsState θ j N k ε))
        ≤ avg (fun ε => (g ε + g (rad_flip K ε)) / 2) := by
          refine rad_avg_mono fun ε => ?_
          rw [hg, hg']
          have := bs_pot_step hp hj hθ0 hθ1 hθ hc htop hw₀ k hk _ (hinv k hk.le ε)
          rcases bs_coin_cases (ε K) with h | h
          · rw [h]; exact this
          · rw [h, neg_neg]; linarith
      _ = avg g := by
          simp only [div_eq_mul_inv, mul_comm _ (2 : ℝ)⁻¹]
          rw [rad_avg_mul_left, rad_avg_add, square_avg_flip K g]; ring
  have hchain : ∀ k, k ≤ N → w₀ ≤ avg (fun ε => bsPot P c κ p w₀ j M k (bsState θ j N k ε)) := by
    intro k
    induction k with
    | zero =>
      intro _
      have : (fun ε : Fin N → Bool => bsPot P c κ p w₀ j M 0 (bsState θ j N 0 ε)) =
          fun _ => w₀ := rfl
      rw [this, square_avg_const]
    | succ k ih => intro hk; exact (ih (by omega)).trans (hstep k (by omega))
  refine (hchain N le_rfl).trans (rad_avg_mono fun ε => ?_)
  -- at the end, the potential is at most the payoff
  have hend := bsSched_end j M
  have hI := hinv N le_rfl ε
  set s := bsState θ j N N ε
  by_cases hal : s.alive = true
  · have hF : s.F = 0 := (hI hal).1 (by rw [hend])
    rw [hN, bsPot_axis (M * (j + 1)) s hal (by rw [hend]), hend]
    simp only [Nat.sub_self, hF, abs_zero]
    exact h0 _ (abs_nonneg _)
  · have hd : s.alive = false := by simpa using hal
    rw [hN, bsPot_dead (M * (j + 1)) s hd]

end Pot


/-! ### The coefficients and the choice of the parameters -/

/-- The coefficients grow: with `0 ≤ a₀ ≤ a`, `a₀ < 1`, `b ≥ 0` and `c* = b / (1 − a₀)`,
`c₀ + c* (1 − a₀^L) ≤ c_L`, if `c₀ = 0`, or if `c₀ ≤ 0` and `a ≤ 1`. -/
theorem bsC_ge {a a₀ b c₀ : ℝ} (ha₀ : 0 ≤ a₀) (ha : a₀ ≤ a) (ha1 : a₀ < 1) (hb : 0 ≤ b)
    (hc₀ : c₀ = 0 ∨ (c₀ ≤ 0 ∧ a ≤ 1)) (L : ℕ) :
    c₀ + b / (1 - a₀) * (1 - a₀ ^ L) ≤ bsC c₀ a b L := by
  have h1 : 0 < 1 - a₀ := by linarith
  set cs := b / (1 - a₀) with hcs
  have hcs0 : 0 ≤ cs := div_nonneg hb h1.le
  have hb' : b = (1 - a₀) * cs := by rw [hcs]; field_simp
  induction L with
  | zero => simp [bsC]
  | succ L ih =>
    have hd0 : 0 ≤ cs * (1 - a₀ ^ L) :=
      mul_nonneg hcs0 (sub_nonneg.2 (pow_le_one₀ ha₀ ha1.le))
    simp only [bsC]
    have key : a * bsC c₀ a b L ≥ c₀ + a₀ * (cs * (1 - a₀ ^ L)) := by
      rcases hc₀ with h | ⟨h, ha'⟩
      · subst h
        have : 0 ≤ bsC 0 a b L := by linarith
        calc a * bsC 0 a b L ≥ a₀ * bsC 0 a b L := mul_le_mul_of_nonneg_right ha this
          _ ≥ a₀ * (cs * (1 - a₀ ^ L)) := mul_le_mul_of_nonneg_left (by linarith) ha₀
          _ = 0 + a₀ * (cs * (1 - a₀ ^ L)) := by ring
      · have ha0 : 0 ≤ a := ha₀.trans ha
        calc a * bsC c₀ a b L ≥ a * (c₀ + cs * (1 - a₀ ^ L)) := mul_le_mul_of_nonneg_left ih ha0
          _ = a * c₀ + a * (cs * (1 - a₀ ^ L)) := by ring
          _ ≥ c₀ + a₀ * (cs * (1 - a₀ ^ L)) := by
              have : a * c₀ ≥ c₀ := by nlinarith
              have : a * (cs * (1 - a₀ ^ L)) ≥ a₀ * (cs * (1 - a₀ ^ L)) :=
                mul_le_mul_of_nonneg_right ha hd0
              linarith
    have e : c₀ + cs * (1 - a₀ ^ (L + 1)) =
        (c₀ + a₀ * (cs * (1 - a₀ ^ L))) + (1 - a₀) * cs := by ring
    rw [e, ← hb']
    linarith [key]

/-- `1 − (pθ)² ≤ (1 − pθ) (1 + (1 + 2θ)^p) / 2` (Bernoulli, `p ≥ 1`). -/
theorem bs_a_ge {p θ : ℝ} (hp : 1 ≤ p) (hθ0 : 0 ≤ θ) (hpθ : p * θ ≤ 1) :
    1 - (p * θ) ^ 2 ≤ (1 - p * θ) * ((1 + (1 + 2 * θ) ^ p) / 2) := by
  have hb := one_add_mul_self_le_rpow_one_add (s := 2 * θ) (by linarith) hp
  have : 1 + p * θ ≤ (1 + (1 + 2 * θ) ^ p) / 2 := by linarith
  nlinarith

/-- `(1 − pθ) (1 + (1 + 2θ)^p) / 2 ≤ 1` for `p ∈ [1, 2]` (Bernoulli for the exponent
`p − 1 ∈ [0, 1]`). -/
theorem bs_a_le {p θ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hθ0 : 0 ≤ θ) (hpθ : p * θ ≤ 1) :
    (1 - p * θ) * ((1 + (1 + 2 * θ) ^ p) / 2) ≤ 1 := by
  have h12 : 0 < 1 + 2 * θ := by linarith
  have hsplit : (1 + 2 * θ) ^ p = (1 + 2 * θ) * (1 + 2 * θ) ^ (p - 1) := by
    rw [← Real.rpow_one_add' h12.le (by linarith), add_sub_cancel]
  have hb := rpow_one_add_le_one_add_mul_self (s := 2 * θ) (by linarith) (p := p - 1)
    (by linarith) (by linarith)
  have h3 : (1 + 2 * θ) ^ p ≤ (1 + 2 * θ) * (1 + (p - 1) * (2 * θ)) := by
    rw [hsplit]; exact mul_le_mul_of_nonneg_left hb h12.le
  have h4 : 0 ≤ 1 - p * θ := by linarith
  have h5 : (1 + (1 + 2 * θ) ^ p) / 2 ≤ 1 + p * θ + 2 * (p - 1) * θ ^ 2 := by nlinarith
  calc (1 - p * θ) * ((1 + (1 + 2 * θ) ^ p) / 2)
      ≤ (1 - p * θ) * (1 + p * θ + 2 * (p - 1) * θ ^ 2) := mul_le_mul_of_nonneg_left h5 h4
    _ = 1 - ((p - 1) ^ 2 + 1) * θ ^ 2 - 2 * p * (p - 1) * θ ^ 3 := by ring
    _ ≤ 1 := by
        have h6 : 0 ≤ ((p - 1) ^ 2 + 1) * θ ^ 2 := by positivity
        have h7 : 0 ≤ 2 * p * (p - 1) * θ ^ 3 := by
          have : 0 ≤ p - 1 := by linarith
          positivity
        linarith

/-- From `E (|g|^p − K^p |f|^p) > 0`: `K ‖f‖_p < ‖g‖_p`. -/
theorem bs_lp_lt {N : ℕ} (f g : (Fin N → Bool) → ℝ) {p K : ℝ} (hp : 0 < p) (hK : 0 ≤ K)
    (h : 0 < avg (fun ε => |g ε| ^ p - K ^ p * |f ε| ^ p)) :
    K * lpNormWith (fun x => |x|) p f < lpNormWith (fun x => |x|) p g := by
  rw [rad_avg_sub, rad_avg_mul_left] at h
  have hA : 0 ≤ avg fun ε => |f ε| ^ p := rad_avg_nonneg fun ε => Real.rpow_nonneg (abs_nonneg _) _
  have hKp : 0 ≤ K ^ p := Real.rpow_nonneg hK _
  unfold lpNormWith
  have hK1 : (K ^ p) ^ (1 / p) = K := by
    rw [← Real.rpow_mul hK, mul_one_div_cancel hp.ne', Real.rpow_one]
  calc K * (avg fun ε => |f ε| ^ p) ^ (1 / p)
      = (K ^ p * avg fun ε => |f ε| ^ p) ^ (1 / p) := by rw [Real.mul_rpow hKp hA, hK1]
    _ < _ := Real.rpow_lt_rpow (mul_nonneg hKp hA) (by linarith) (by positivity)


/-- The construction with its parameters: let `p ≥ 1`, `κ > 0`, `T ≥ 0`, `τ > 0`, and a payoff
`P` with `P (0, y) ≥ c₀ y^p` and, whenever `θ > 0` and `pθ ≤ τ`, `P (x, S − x) ≥ κ x^p` at the
stopping points (`x > 0`, `p x ≤ S ≤ (1 + 2θ) p x`); let `c₀ = 0`, or `c₀ ≤ 0` and `p ≤ 2`. Then
for some `θ`, `j` and `M` (`j` with `2^{−j} < min (τ, κ p^{−p} / (2 (T + 1)))`, `θ = 2^{−j} / p`,
and `M` with `(1 − 4^{−j})^M < 1/2`), with `N = M (j + 1) + 2`,
`(P (2, 0) + 2^p (c₀ + T + 1)) / 2 ≤ E P (|F_N|, |G_N|)`: the coefficient `c_M` is at least
`c₀ + c* / 2` with `c* = κ p^{−p} 2^j > 2 (T + 1)` (`bsC_ge`, `bs_a_ge`, `bs_a_le`). -/
theorem bs_exists {p κ c₀ T τ : ℝ} (hp : 1 ≤ p) (hκ : 0 < κ) (hT : 0 ≤ T) (hτ : 0 < τ)
    (hc₀ : c₀ = 0 ∨ (c₀ ≤ 0 ∧ p ≤ 2)) (P : ℝ → ℝ → ℝ)
    (htop : ∀ θ : ℝ, 0 < θ → p * θ ≤ τ → ∀ x S, 0 < x → p * x ≤ S → S ≤ (1 + 2 * θ) * p * x →
      κ * x ^ p ≤ P x (S - x))
    (h0 : ∀ y, 0 ≤ y → c₀ * y ^ p ≤ P 0 y) :
    ∃ θ : ℝ, ∃ j M : ℕ, (P 2 0 + (c₀ + T + 1) * 2 ^ p) / 2 ≤
      avg (fun ε : Fin (M * (j + 1) + 2) → Bool =>
        P |(bsState θ j (M * (j + 1) + 2) (M * (j + 1) + 2) ε).F|
          |(bsState θ j (M * (j + 1) + 2) (M * (j + 1) + 2) ε).G|) := by
  have hp0 : 0 < p := by linarith
  have hB : 0 < κ * (1 / p) ^ p / (2 * (T + 1)) := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (lt_min hτ hB) (by norm_num : (1 / 2 : ℝ) < 1)
  set j := n + 1 with hjdef
  set u : ℝ := (1 / 2 : ℝ) ^ j with hudef
  have hu0 : 0 < u := by positivity
  have hun : u ≤ (1 / 2) ^ n := by
    rw [hudef, pow_succ]; have : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
    linarith
  have hu2 : u ≤ 1 / 2 := by
    rw [hudef, pow_succ]
    have : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have huτ : u < τ := lt_of_le_of_lt hun (lt_of_lt_of_le hn (min_le_left _ _))
  have huB : u < κ * (1 / p) ^ p / (2 * (T + 1)) :=
    lt_of_le_of_lt hun (lt_of_lt_of_le hn (min_le_right _ _))
  set θ := u / p with hθdef
  have hθ0 : 0 < θ := by positivity
  have hθ : u = p * θ := by rw [hθdef]; field_simp
  have hθ1 : θ ≤ 1 := by rw [hθdef, div_le_one hp0]; linarith
  have hpθ : p * θ ≤ 1 := by rw [← hθ]; linarith
  set a := (1 - u) * ((1 + (1 + 2 * θ) ^ p) / 2) with hadef
  set b := u * κ * (1 / p) ^ p with hbdef
  set a₀ := 1 - u ^ 2 with ha₀def
  have ha₀0 : 0 ≤ a₀ := by nlinarith
  have ha₀1 : a₀ < 1 := by have := pow_pos hu0 2; linarith
  have ha : a₀ ≤ a := by
    have := bs_a_ge hp hθ0.le hpθ
    rw [← hθ] at this; exact this
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) ha₀1
  refine ⟨θ, j, M, ?_⟩
  have hmain := bs_main (P := P) (κ := κ) (M := M) hp (by omega : 1 ≤ j) hθ0 hθ1 hθ
    (c := bsC c₀ a b) (fun L => rfl) (htop θ hθ0 (by rw [← hθ]; exact huτ.le)) h0
  refine le_trans ?_ hmain
  -- `c_M ≥ c₀ + c* / 2 > c₀ + T + 1`, `c* = b / (1 − a₀) = κ p^{−p} 2^j`
  have hcs : b / (1 - a₀) = κ * (1 / p) ^ p / u := by
    rw [hbdef, ha₀def]; field_simp; ring
  have hcsT : 2 * (T + 1) < b / (1 - a₀) := by
    rw [hcs, lt_div_iff₀ hu0]
    rw [lt_div_iff₀ (by positivity)] at huB
    linarith
  have hc₀' : c₀ = 0 ∨ (c₀ ≤ 0 ∧ a ≤ 1) := by
    rcases hc₀ with h | ⟨h, hp2⟩
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      have := bs_a_le hp hp2 hθ0.le hpθ
      rw [← hθ] at this; exact this
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  have hge := bsC_ge (b := b) ha₀0 ha ha₀1 hb0 hc₀' M
  have hcM : c₀ + T + 1 ≤ bsC c₀ a b M := by
    have h1 : 1 / 2 ≤ 1 - a₀ ^ M := by linarith
    have h2 : 0 ≤ b / (1 - a₀) := by linarith
    nlinarith
  have h2p : 0 ≤ (2 : ℝ) ^ p := by positivity
  nlinarith

/-- **The sharpness of Burkholder's constant for dyadic martingale transforms** (Burkholder
1985; the statement `BurkholderSharpness`). For `K < p* − 1` (wlog `K ≥ 0`), the process of this
file: for `p ≥ 2` (`p* − 1 = p − 1`) with the payoff `|G|^p − K^p |F|^p`, `κ = (p − 1)^p − K^p`,
`f = F`, `g = G`; for `p < 2` (`p* − 1 = 1 / (p − 1)`) with the payoff `|F|^p − K^p |G|^p`,
`κ = 1 − q₀^p` for `q₀ = (1 + K (p − 1)) / 2 < 1`, and the roles exchanged, `f = G`, `g = F`
(`G` is the `±1` transform of `F`, and `F` that of `G`). In both cases
`E (|g_N|^p − K^p |f_N|^p) > 0` (`bs_exists`), so `‖g_N‖_p > K ‖f_N‖_p`. -/
theorem burkholderSharpness_holds : BurkholderSharpness := by
  intro p hp K hK
  set K₁ := max K 0 with hK₁
  have hK₁0 : 0 ≤ K₁ := le_max_right _ _
  have hKK₁ : K ≤ K₁ := le_max_left _ _
  have hps : p ≤ pStar p := le_max_left _ _
  have hK₁s : K₁ < pStar p - 1 := max_lt hK (by linarith)
  have hp0 : 0 < p := by linarith
  have hK₁p : 0 ≤ K₁ ^ p := Real.rpow_nonneg hK₁0 _
  have hz : (0 : ℝ) ^ p = 0 := Real.zero_rpow hp0.ne'
  -- it suffices to treat `K₁ = max K 0`
  suffices h : ∃ (N : ℕ) (φ σ : Fin N → (Fin N → Bool) → ℝ), IsPredictable φ ∧
      IsPredictable σ ∧ (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) ∧
      K₁ * lpNormWith (fun x => |x|) p (mart φ N) <
        lpNormWith (fun x => |x|) p (mart (fun k ε => σ k ε * φ k ε) N) by
    obtain ⟨N, φ, σ, h1, h2, h3, h4⟩ := h
    refine ⟨N, φ, σ, h1, h2, h3, lt_of_le_of_lt (mul_le_mul_of_nonneg_right hKK₁ ?_) h4⟩
    exact Real.rpow_nonneg (rad_avg_nonneg fun ε => Real.rpow_nonneg (abs_nonneg _) _) _
  rcases le_or_gt 2 p with hp2 | hp2
  · -- `p ≥ 2`: `p* − 1 = p − 1`, the payoff `|G|^p − K^p |F|^p`
    have hpS : pStar p = p := max_eq_left (by rw [div_le_iff₀ (by linarith)]; nlinarith)
    rw [hpS] at hK₁s
    have hκ : 0 < (p - 1) ^ p - K₁ ^ p := sub_pos.2 (Real.rpow_lt_rpow hK₁0 hK₁s hp0)
    obtain ⟨θ, j, M, hE⟩ := bs_exists (κ := (p - 1) ^ p - K₁ ^ p) (c₀ := 0) (T := K₁ ^ p)
      (τ := 1) hp.le hκ hK₁p one_pos (Or.inl rfl) (fun x y => y ^ p - K₁ ^ p * x ^ p)
      (fun θ _ _ x S hx h1 _ => by
        have hS : (p - 1) * x ≤ S - x := by linarith
        have := Real.rpow_le_rpow (by nlinarith) hS hp0.le
        rw [Real.mul_rpow (by linarith) hx.le] at this
        nlinarith)
      (fun y hy => by simp only [hz, mul_zero, sub_zero, zero_mul]; exact Real.rpow_nonneg hy _)
    set N := M * (j + 1) + 2
    refine ⟨N, bsPhi θ j N, bsSig θ j N, bsPhi_predictable θ j N, bsSig_predictable θ j N,
      bsSig_cases θ j N, bs_lp_lt _ _ hp0 hK₁0 ?_⟩
    have e : (fun ε => |mart (fun k ε => bsSig θ j N k ε * bsPhi θ j N k ε) N ε| ^ p -
        K₁ ^ p * |mart (bsPhi θ j N) N ε| ^ p) = fun ε =>
          |(bsState θ j N N ε).G| ^ p - K₁ ^ p * |(bsState θ j N N ε).F| ^ p := by
      funext ε; rw [bs_mart_F θ j N ε N le_rfl, bs_mart_G θ j N ε N le_rfl]
    rw [e]
    refine lt_of_lt_of_le ?_ hE
    simp only [hz, zero_sub, zero_add]
    have : (0 : ℝ) < 2 ^ p := by positivity
    nlinarith
  · -- `p < 2`: `p* − 1 = 1 / (p − 1)`, the payoff `|F|^p − K^p |G|^p`, roles exchanged
    have hpS : pStar p = p / (p - 1) :=
      max_eq_right (by rw [le_div_iff₀ (by linarith)]; nlinarith)
    rw [hpS] at hK₁s
    have hK₁q : K₁ * (p - 1) < 1 := by
      have h1 : p / (p - 1) - 1 = 1 / (p - 1) := by field_simp; ring
      rw [h1, lt_div_iff₀ (by linarith)] at hK₁s
      exact hK₁s
    set q₀ := (1 + K₁ * (p - 1)) / 2 with hq₀
    have hq₀0 : 0 ≤ q₀ := by have : 0 ≤ K₁ * (p - 1) := mul_nonneg hK₁0 (by linarith); linarith
    have hq₀1 : q₀ < 1 := by linarith
    have hκ : 0 < 1 - q₀ ^ p := sub_pos.2 (Real.rpow_lt_one hq₀0 hq₀1 hp0)
    have hτ : 0 < (1 - K₁ * (p - 1)) / (4 * (K₁ + 1)) := by
      apply div_pos <;> linarith
    obtain ⟨θ, j, M, hE⟩ := bs_exists (κ := 1 - q₀ ^ p) (c₀ := -K₁ ^ p) (T := K₁ ^ p)
      (τ := (1 - K₁ * (p - 1)) / (4 * (K₁ + 1))) hp.le hκ hK₁p hτ
      (Or.inr ⟨by linarith, hp2.le⟩) (fun x y => x ^ p - K₁ ^ p * y ^ p)
      (fun θ hθ0 hθτ x S hx h1 h2 => by
        have hS0 : 0 ≤ S - x := by nlinarith
        -- `K (S − x) ≤ K (p − 1 + 2pθ) x ≤ q₀ x`
        have hKθ : K₁ * (2 * (p * θ)) ≤ q₀ - K₁ * (p - 1) := by
          rw [le_div_iff₀ (by linarith)] at hθτ
          have : K₁ * (p * θ) * 4 ≤ (1 - K₁ * (p - 1)) := by nlinarith
          rw [hq₀]; nlinarith
        have hKS : K₁ * (S - x) ≤ q₀ * x := by
          have : S - x ≤ (p - 1 + 2 * (p * θ)) * x := by nlinarith
          calc K₁ * (S - x) ≤ K₁ * ((p - 1 + 2 * (p * θ)) * x) :=
                mul_le_mul_of_nonneg_left this hK₁0
            _ = (K₁ * (p - 1) + K₁ * (2 * (p * θ))) * x := by ring
            _ ≤ q₀ * x := mul_le_mul_of_nonneg_right (by linarith) hx.le
        have := Real.rpow_le_rpow (mul_nonneg hK₁0 hS0) hKS hp0.le
        rw [Real.mul_rpow hK₁0 hS0, Real.mul_rpow hq₀0 hx.le] at this
        show (1 - q₀ ^ p) * x ^ p ≤ x ^ p - K₁ ^ p * (S - x) ^ p
        nlinarith)
      (fun y hy => by simp only [hz]; linarith)
    set N := M * (j + 1) + 2
    have hσσ : (fun k ε => bsSig θ j N k ε * (bsSig θ j N k ε * bsPhi θ j N k ε)) =
        bsPhi θ j N := by
      funext k ε
      rcases bsSig_cases θ j N k ε with h | h <;> rw [h] <;> ring
    refine ⟨N, fun k ε => bsSig θ j N k ε * bsPhi θ j N k ε, bsSig θ j N,
      fun k ε ε' h => by
        simp only; rw [bsSig_predictable θ j N k ε ε' h, bsPhi_predictable θ j N k ε ε' h],
      bsSig_predictable θ j N, bsSig_cases θ j N, ?_⟩
    rw [hσσ]
    refine bs_lp_lt _ _ hp0 hK₁0 ?_
    have e : (fun ε => |mart (bsPhi θ j N) N ε| ^ p - K₁ ^ p *
        |mart (fun k ε => bsSig θ j N k ε * bsPhi θ j N k ε) N ε| ^ p) = fun ε =>
          |(bsState θ j N N ε).F| ^ p - K₁ ^ p * |(bsState θ j N N ε).G| ^ p := by
      funext ε; rw [bs_mart_F θ j N ε N le_rfl, bs_mart_G θ j N ε N le_rfl]
    rw [e]
    refine lt_of_lt_of_le ?_ hE
    simp only [hz, mul_zero, sub_zero]
    have : (0 : ℝ) < 2 ^ p := by positivity
    nlinarith

end Cassese
