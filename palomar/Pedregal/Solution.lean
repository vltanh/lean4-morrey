module

public import Morrey.Pedregal.NonEmptiness.Counterexample
public import Morrey.Pedregal.Reduction
public import Morrey.Pedregal.Introduction
public import Morrey.Pedregal.Checks
public import Morrey.Pedregal.LevelOne

/-!
# Solution

The statements of `Challenge.lean`, word for word, proved from the library. This module imports
the whole library and is its root.
-/

@[expose] public section

namespace PedregalChallenge

open Pedregal

theorem corollary7_2_false :
    ¬ ∀ l : ℕ, 1 ≤ l → ∀ (S : TriMold l) (u v : (Fin 2 → ℝ) → ℝ), u ∈ PL l → v ∈ PL l →
      ∀ t ∈ Theta S, (T S u v t).Nonempty :=
  Pedregal.corollary7_2_false

theorem exists_T_eq_empty :
    ∃ (S : TriMold 1) (u v : (Fin 2 → ℝ) → ℝ), u ∈ PL 1 ∧ v ∈ PL 1 ∧
      ∃ t ∈ Theta S, T S u v t = ∅ :=
  ⟨TriMold.canonical 1, uCex, vCex, uCex_mem, vCex_mem, tCex, tCex_mem, T_cex_eq_empty⟩

theorem theorem1_1_of_nonempty {l : ℕ} (S : TriMold l) {u v : (Fin 2 → ℝ) → ℝ}
    (hu : u ∈ PL l) (hv : v ∈ PL l) (hne : ∀ t ∈ Theta S, (T S u v t).Nonempty) :
    IsLaminate (gradMeasure l u v) :=
  Pedregal.theorem1_1_of_nonempty S hu hv hne

theorem theorem1_1_part1_levelOne {u v : (Fin 2 → ℝ) → ℝ} (hu : u ∈ PL 1) (hv : v ∈ PL 1) :
    IsLaminate (gradMeasure 1 u v) :=
  Pedregal.theorem1_1_part1_levelOne hu hv

theorem mem_T_self {l : ℕ} (S : TriMold l) (u : (Fin 2 → ℝ) → ℝ) {t : Leaf l → ℝ}
    (ht : t ∈ Theta S) : t ∈ T S u u t :=
  Pedregal.mem_T_self S u ht

theorem card_C {l : ℕ} (S : TriMold l) (s : Tri l) : (S.C s).card = 6 :=
  TriMold.card_C S s

end PedregalChallenge
