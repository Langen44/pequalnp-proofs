import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_805_aux

open PEqualNP.CircuitLowerBounds

-- The circuit of the statement.
def circ : Circuit :=
  { gates := [⟨GateOp.or, [6, 0]⟩, ⟨GateOp.or, [5, 2]⟩, ⟨GateOp.and, [7, 4]⟩, ⟨GateOp.or, [3, 9]⟩,
      ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.and, [10, 13]⟩,
      ⟨GateOp.or, [12, 14]⟩], output := 15 }

-- The edge function written on seven Boolean values.
def edgeFn (a b c d e f g : Bool) : Bool :=
  (a && b) || (a && e) || (b && c) || (c && d) || (d && e) || (d && f) || (e && g)

-- The circuit agrees with the edge function on all 128 inputs.
theorem eval_eq : ∀ a b c d e f g : Bool,
    circ.eval [a, b, c, d, e, f, g] = edgeFn a b c d e f g := by
  decide

theorem ofFn_seven (x : Fin 7 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
  simp [List.ofFn_succ]

theorem edge_iff (x : Fin 7 → Bool) :
    (∃ u v : Fin 7, (u.val, v.val) ∈
        ([(0, 1), (0, 4), (1, 2), (2, 3), (3, 4), (3, 5), (4, 6)] : List (ℕ × ℕ)) ∧
        x u = true ∧ x v = true) ↔
      edgeFn (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) = true := by
  constructor
  · rintro ⟨u, v, hmem, hu, hv⟩
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain rfl : u = 0 := Fin.ext h1
      obtain rfl : v = 1 := Fin.ext h2
      simp [edgeFn, hu, hv]
    · obtain rfl : u = 0 := Fin.ext h1
      obtain rfl : v = 4 := Fin.ext h2
      simp [edgeFn, hu, hv]
    · obtain rfl : u = 1 := Fin.ext h1
      obtain rfl : v = 2 := Fin.ext h2
      simp [edgeFn, hu, hv]
    · obtain rfl : u = 2 := Fin.ext h1
      obtain rfl : v = 3 := Fin.ext h2
      simp [edgeFn, hu, hv]
    · obtain rfl : u = 3 := Fin.ext h1
      obtain rfl : v = 4 := Fin.ext h2
      simp [edgeFn, hu, hv]
    · obtain rfl : u = 3 := Fin.ext h1
      obtain rfl : v = 5 := Fin.ext h2
      simp [edgeFn, hu, hv]
    · obtain rfl : u = 4 := Fin.ext h1
      obtain rfl : v = 6 := Fin.ext h2
      simp [edgeFn, hu, hv]
  · intro h
    simp only [edgeFn, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with (((((h | h) | h) | h) | h) | h) | h
    · exact ⟨0, 1, by simp, h.1, h.2⟩
    · exact ⟨0, 4, by simp, h.1, h.2⟩
    · exact ⟨1, 2, by simp, h.1, h.2⟩
    · exact ⟨2, 3, by simp, h.1, h.2⟩
    · exact ⟨3, 4, by simp, h.1, h.2⟩
    · exact ⟨3, 5, by simp, h.1, h.2⟩
    · exact ⟨4, 6, by simp, h.1, h.2⟩

end PEqualNP.Outside.L_meta_805_aux

theorem PEqualNP.Outside.L_meta_805 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 14]⟩], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 9 ∧ (∀ x : Fin 7 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 7, (u.val, v.val) ∈ ([(0, 1), (0, 4), (1, 2), (2, 3), (3, 4), (3, 5), (4, 6)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    rw [PEqualNP.Outside.L_meta_805_aux.edge_iff x, PEqualNP.Outside.L_meta_805_aux.ofFn_seven x]
    exact (PEqualNP.Outside.L_meta_805_aux.eval_eq (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)) ▸ Iff.rfl
