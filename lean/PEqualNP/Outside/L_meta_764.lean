import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_764_aux

open PEqualNP.MetaComplexity

-- A circuit with at most s gates is a circuit with at most t gates when s is at most t.
theorem size_mono (n : ℕ) (f : (Fin n → Bool) → Bool) (s t : ℕ) (hst : s ≤ t) :
    HasCircuitSize n f s → HasCircuitSize n f t := by
  rintro ⟨C, h1, h2, h3⟩
  exact ⟨C, h1, le_trans h2 hst, h3⟩

-- The function of the statement is an AND of two fresh inputs, placed first, OR the
-- known function on the remaining 3 inputs.
theorem fun_eq :
    (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) =
      (fun x : Fin (2 + 3) → Bool =>
        (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) || ((x (Fin.natAdd 2 0) && x (Fin.natAdd 2 1)) || (x (Fin.natAdd 2 1) && x (Fin.natAdd 2 2)) || (x (Fin.natAdd 2 0) && x (Fin.natAdd 2 2)))) := by
  funext x
  simp only [Bool.or_assoc]
  rfl

-- The known function is not constant.
theorem nonconst : ∃ y y' : Fin 3 → Bool,
    (fun y : Fin 3 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)) y ≠
      (fun y : Fin 3 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)) y' :=
  ⟨fun _ => false, fun _ => true, by simp⟩

-- Two more gates than the known function: L-meta-153 and then the known exact size.
theorem key (t : ℕ) :
    HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) (t + 2) ↔ 4 ≤ t := by
  have h := (PEqualNP.MetaComplexity.L153 3 t
    (fun y : Fin 3 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)) nonconst).trans
    (PEqualNP.MetaComplexity.L100 t)
  rw [fun_eq]
  exact h

theorem main : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔ 6 ≤ s := by
  intro s
  constructor
  · intro h
    by_contra hlt
    have h2 := size_mono _ _ s (3 + 2) (by omega) h
    have h3 := (key 3).mp h2
    omega
  · intro h
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
    exact (key t).mpr (by omega)

end PEqualNP.Outside.L_meta_764_aux

theorem PEqualNP.Outside.L_meta_764 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔ 6 ≤ s :=
  PEqualNP.Outside.L_meta_764_aux.main
