module

public import Pedregal.Map

/-!
# Checks of the definitions

Facts that tie the definitions to what is expected of them, stated in the Challenge so that a
reader can see that the definitions mean what they should.

* `mem_T_self`: when `v = u`, every `t ∈ Θ_l` is a fixed point of `𝐓` (the decomposition
  directions are the same).
-/

@[expose] public section

namespace Pedregal

/-- When `v = u`, every `t ∈ Θ_l` lies in `𝐓(t)`. -/
theorem mem_T_self {l : ℕ} (S : TriMold l) (u : (Fin 2 → ℝ) → ℝ) {t : Leaf l → ℝ}
    (ht : t ∈ Theta S) : t ∈ T S u u t :=
  ⟨ht, fun _ _ _ => by unfold Parallel; ring⟩

end Pedregal
