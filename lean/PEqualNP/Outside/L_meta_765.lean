import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L112
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_765_aux

open PEqualNP.MetaComplexity

-- A circuit with at most s gates is a circuit with at most t gates when s is at most t.
theorem size_mono (n : ℕ) (f : (Fin n → Bool) → Bool) (s t : ℕ) (hst : s ≤ t) :
    HasCircuitSize n f s → HasCircuitSize n f t := by
  rintro ⟨C, h1, h2, h3⟩
  exact ⟨C, h1, le_trans h2 hst, h3⟩

-- The function of the statement is an AND of two fresh inputs, placed first, OR the
-- known function on the remaining 4 inputs.
theorem fun_eq :
    (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) =
      (fun x : Fin (2 + 4) → Bool =>
        (x (Fin.castAdd 4 0) && x (Fin.castAdd 4 1)) || ((x (Fin.natAdd 2 0) && x (Fin.natAdd 2 1)) || (x (Fin.natAdd 2 1) && x (Fin.natAdd 2 2)) || (x (Fin.natAdd 2 2) && x (Fin.natAdd 2 3)) || (x (Fin.natAdd 2 3) && x (Fin.natAdd 2 0)))) := by
  funext x
  simp only [Bool.or_assoc]
  rfl

-- The known function is not constant.
theorem nonconst : ∃ y y' : Fin 4 → Bool,
    (fun y : Fin 4 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 0)) y ≠
      (fun y : Fin 4 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 0)) y' :=
  ⟨fun _ => false, fun _ => true, by simp⟩

-- Two more gates than the known function: L-meta-153 and then the known exact size.
theorem key (t : ℕ) :
    HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) (t + 2) ↔ 3 ≤ t := by
  have h := (PEqualNP.MetaComplexity.L153 4 t
    (fun y : Fin 4 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 0)) nonconst).trans
    (PEqualNP.MetaComplexity.L112 t)
  rw [fun_eq]
  exact h

theorem main : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s ↔ 5 ≤ s := by
  intro s
  constructor
  · intro h
    by_contra hlt
    have h2 := size_mono _ _ s (2 + 2) (by omega) h
    have h3 := (key 2).mp h2
    omega
  · intro h
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
    exact (key t).mpr (by omega)

end PEqualNP.Outside.L_meta_765_aux

theorem PEqualNP.Outside.L_meta_765 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s ↔ 5 ≤ s :=
  PEqualNP.Outside.L_meta_765_aux.main
