import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_749_aux

open PEqualNP.CircuitLowerBounds

-- The wire list of a gate list on an input, with the output index fixed at zero.
def W (L : List Gate) (x : List Bool) : List Bool := Circuit.wires ⟨L, 0⟩ x

-- One gate appended to a wire list.
def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem W_eq (L : List Gate) (x : List Bool) : W L x = L.foldl stepW x := rfl

theorem W_nil (x : List Bool) : W [] x = x := rfl

theorem W_take_succ (L : List Gate) (j : ℕ) (g : Gate) (h : L[j]? = some g) (x : List Bool) :
    W (L.take (j + 1)) x = stepW (W (L.take j) x) g := by
  rw [W_eq, W_eq, List.take_add_one, h, List.foldl_append]
  rfl

-- Pointwise order on wire lists of equal length.
def le (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i : ℕ, w.getD i false = true → w'.getD i false = true

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (hm : ∀ i : ℕ, w.getD i false = true → w'.getD i false = true) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true →
      g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with ho | ho
  · rw [ho]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map]
    intro hall b hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact hm i (hall _ ⟨i, hi, rfl⟩)
  · rw [ho]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨_, ⟨i, hi, rfl⟩, hm i hb⟩

theorem getD_append_single (w : List Bool) (a : Bool) (i : ℕ) :
    (w ++ [a]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then a else false := by
  by_cases h1 : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1, h1]
  · by_cases h2 : i = w.length
    · subst h2
      simp [List.getD_eq_getElem?_getD]
    · have h3 : w.length + 1 ≤ i := by omega
      have h4 : (w ++ [a])[i]? = none := List.getElem?_eq_none (by simpa using h3)
      simp [List.getD_eq_getElem?_getD, h4, h1, h2]

theorem le_step (w w' : List Bool) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : le w w') : le (stepW w g) (stepW w' g) := by
  obtain ⟨hl, hm⟩ := h
  refine ⟨by simp [stepW, hl], ?_⟩
  intro i
  unfold stepW
  rw [getD_append_single, getD_append_single, hl]
  split_ifs with h1 h2
  · exact hm i
  · exact eval_mono g hg w w' hm
  · exact fun h => h

theorem le_ofFn {n : ℕ} (x x' : Fin n → Bool) (h : ∀ p, x p = true → x' p = true) :
    le (List.ofFn x) (List.ofFn x') := by
  refine ⟨by simp, ?_⟩
  intro i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs with hi
  · simpa using h ⟨i, hi⟩
  · simp

theorem head_mono (inputs : List ℕ) (w w' : List Bool)
    (hm : ∀ i : ℕ, w.getD i false = true → w'.getD i false = true) :
    (inputs.map (fun i => w.getD i false)).headD false = true →
      (inputs.map (fun i => w'.getD i false)).headD false = true := by
  cases inputs with
  | nil => simp
  | cons i rest => simpa using hm i

theorem main (n : ℕ) (C C' : List Gate) (X : Set (Fin n → Bool)) (y : Fin n → Bool)
    (hC : ∀ g ∈ C, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hy : y ∈ X) (hmin : ∀ u ∈ X, ∀ p : Fin n, y p = true → u p = true)
    (H : ∀ (j1 : ℕ) (g1 : Gate), C[j1]? = some g1 → g1.op = GateOp.not →
      ((g1.inputs.map (fun i1 => (W (C.take j1) (List.ofFn y)).getD i1 false)).headD false)
        = false →
      ∀ z ∈ X,
        ((g1.inputs.map (fun i2 => (W (C.take j1) (List.ofFn z)).getD i2 false)).headD false)
          = false)
    (hC' : ∀ (j2 : ℕ) (g2 : Gate), C[j2]? = some g2 →
      (g2.op = GateOp.not →
        (((g2.inputs.map (fun i3 => (W (C.take j2) (List.ofFn y)).getD i3 false)).headD false)
            = true →
          C'[j2]? = some ({ op := GateOp.or, inputs := [] } : Gate)) ∧
        (((g2.inputs.map (fun i4 => (W (C.take j2) (List.ofFn y)).getD i4 false)).headD false)
            = false →
          C'[j2]? = some ({ op := GateOp.and, inputs := [] } : Gate))) ∧
      (g2.op ≠ GateOp.not → C'[j2]? = some g2)) :
    ∀ j : ℕ, j ≤ C.length →
      (∀ x ∈ X, W (C'.take j) (List.ofFn x) = W (C.take j) (List.ofFn x)) ∧
      (∀ x x' : Fin n → Bool, (∀ p, x p = true → x' p = true) →
        le (W (C'.take j) (List.ofFn x)) (W (C'.take j) (List.ofFn x'))) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun x _ => by simp [W_nil], fun x x' h => ?_⟩
    simpa [W_nil] using le_ofFn x x' h
  | succ j ih =>
    intro hj
    have hjlt : j < C.length := hj
    obtain ⟨iha, ihm⟩ := ih (Nat.le_of_lt hjlt)
    obtain ⟨g, hg⟩ : ∃ g, C[j]? = some g := ⟨C[j], List.getElem?_eq_getElem hjlt⟩
    have hgmem : g ∈ C := List.mem_of_getElem? hg
    have hgC := (hC g hgmem).1
    by_cases hnot : g.op = GateOp.not
    · have key := (hC' j g hg).1 hnot
      have hstepC : ∀ x : Fin n → Bool, W (C.take (j + 1)) (List.ofFn x) =
          W (C.take j) (List.ofFn x) ++
            [!((g.inputs.map (fun i => (W (C.take j) (List.ofFn x)).getD i false)).headD
              false)] := by
        intro x
        rw [W_take_succ C j g hg]
        simp [stepW, hnot, GateOp.eval]
      cases hvy : (g.inputs.map (fun i => (W (C.take j) (List.ofFn y)).getD i false)).headD
          false with
      | true =>
        have hg2 := key.1 hvy
        refine ⟨?_, ?_⟩
        · intro x hx
          have h1 : (g.inputs.map (fun i => (W (C'.take j) (List.ofFn y)).getD i false)).headD
              false = true := by
            rw [iha y hy]
            exact hvy
          have h2 := head_mono g.inputs _ _ (ihm y x (hmin x hx)).2 h1
          rw [iha x hx] at h2
          rw [hstepC x, W_take_succ C' j _ hg2, iha x hx, h2]
          simp [stepW, GateOp.eval]
        · intro x x' h
          rw [W_take_succ C' j _ hg2, W_take_succ C' j _ hg2]
          exact le_step _ _ _ (Or.inr rfl) (ihm x x' h)
      | false =>
        have hg2 := key.2 hvy
        refine ⟨?_, ?_⟩
        · intro x hx
          have h2 := H j g hg hnot hvy x hx
          rw [hstepC x, W_take_succ C' j _ hg2, iha x hx, h2]
          simp [stepW, GateOp.eval]
        · intro x x' h
          rw [W_take_succ C' j _ hg2, W_take_succ C' j _ hg2]
          exact le_step _ _ _ (Or.inl rfl) (ihm x x' h)
    · have hg2 := (hC' j g hg).2 hnot
      have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
        rcases hgC with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hnot
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [W_take_succ C j g hg, W_take_succ C' j g hg2, iha x hx]
      · intro x x' h
        rw [W_take_succ C' j g hg2, W_take_succ C' j g hg2]
        exact le_step _ _ _ hop (ihm x x' h)

end PEqualNP.Outside.L_meta_749_aux

theorem PEqualNP.Outside.L_meta_749 : ∀ (n : ℕ) (C C' : List PEqualNP.CircuitLowerBounds.Gate) (X : Set (Fin n → Bool)) (y : Fin n → Bool), (∀ g ∈ C, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → y ∈ X → (∀ u ∈ X, ∀ p : Fin n, y p = true → u p = true) → (∀ (j1 : ℕ) (g1 : PEqualNP.CircuitLowerBounds.Gate), C[j1]? = some g1 → g1.op = PEqualNP.CircuitLowerBounds.GateOp.not → ((g1.inputs.map (fun i1 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn y)).getD i1 false)).headD false) = false → ∀ z ∈ X, ((g1.inputs.map (fun i2 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn z)).getD i2 false)).headD false) = false) → C'.length = C.length → (∀ (j2 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate), C[j2]? = some g2 → (g2.op = PEqualNP.CircuitLowerBounds.GateOp.not → (((g2.inputs.map (fun i3 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i3 false)).headD false) = true → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate)) ∧ (((g2.inputs.map (fun i4 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i4 false)).headD false) = false → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate))) ∧ (g2.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → C'[j2]? = some g2)) → ∀ x ∈ X, ∀ w : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C', 0⟩ (List.ofFn x)).getD w false = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C, 0⟩ (List.ofFn x)).getD w false := by
  intro n C C' X y hC hy hmin H hlen hC' x hx w
  have hmain := (PEqualNP.Outside.L_meta_749_aux.main n C C' X y hC hy hmin H hC' C.length le_rfl).1 x hx
  rw [List.take_of_length_le (le_of_eq hlen), List.take_of_length_le le_rfl] at hmain
  exact congrArg (fun l => l.getD w false) hmain
