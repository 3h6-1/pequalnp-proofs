import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1638

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ) : Bool :=
  Circuit.eval ⟨gates, w⟩ (List.ofFn x)

theorem val_input {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (i : Fin N) :
    val gates x i.val = x i := by
  change (wiresFrom gates (List.ofFn x)).getD i.val false = x i
  rw [prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {N : ℕ} (gates : List Gate) (x : Fin N → Bool) {w : ℕ}
    (hw : N + gates.length ≤ w) : val gates x w = false := by
  change (wiresFrom gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hw)

theorem val_gate {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (i : Fin gates.length)
    (hw : ∀ w ∈ (gates.get i).inputs, w < N + i.val) :
    val gates x (N + i.val) = (gates.get i).op.eval ((gates.get i).inputs.map (val gates x)) := by
  let g := gates.get i
  have hsplit : gates = (gates.take i.val ++ [g]) ++ gates.drop (i.val+1) := by
    conv_lhs => rw [← List.take_append_drop (i.val+1) gates]
    rw [List.take_succ_eq_append_getElem i.isLt] <;> rfl
  let ws := wiresFrom (gates.take i.val) (List.ofFn x)
  have len : ws.length = N + i.val := by
    simp [ws, wiresFrom_length, List.length_take]
  have reads (w : ℕ) (hi : w ∈ g.inputs) : val gates x w = ws.getD w false := by
    change (wiresFrom gates (List.ofFn x)).getD w false = ws.getD w false
    conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
    apply prefix_val _ ws w
    rw [len]
    exact hw _ hi
  have mapped : (g.inputs.map fun w => ws.getD w false) = g.inputs.map (val gates x) :=
    List.map_congr_left fun w hi => (reads w hi).symm
  change (wiresFrom gates (List.ofFn x)).getD (N+i.val) false = g.op.eval (g.inputs.map (val gates x))
  have eqw := congrArg (fun gs => wiresFrom gs (List.ofFn x)) hsplit
  rw [eqw, List.append_assoc, wiresFrom_append]
  change (wiresFrom (gates.drop (i.val+1))
    (ws ++ [g.op.eval (g.inputs.map fun w => ws.getD w false)])).getD (N+i.val) false = _
  rw [prefix_val _ _ _ (by simp [len]), ← len, mapped]
  simp [len]

theorem reach_hit {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (r : Fin N)
    (R : ℕ → Prop) (ops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hw : ∀ i : Fin gates.length, ∀ e ∈ (gates.get i).inputs, e < N + i.val)
    (hin : ∀ p : Fin N, R p.val → x p = true → p = r)
    (closed : ∀ i : Fin gates.length, R (N + i.val) → (gates.get i).op = GateOp.or →
      ∀ e ∈ (gates.get i).inputs, R e)
    (w : ℕ) (hrw : R w) (ht : val gates x w = true) :
    R r.val ∨ ∃ a : ℕ, R a ∧
      (∃ i : Fin gates.length, a = N + i.val ∧ (gates.get i).op = GateOp.and) ∧
      val gates x a = true := by
  induction w using Nat.strongRecOn with
  | ind w ih =>
    by_cases hi : w < N
    · let p : Fin N := ⟨w, hi⟩
      have ht' : val gates x p.val = true := ht
      rw [val_input] at ht'
      have hp := hin p hrw ht'
      exact Or.inl (hp ▸ hrw : R r.val)
    · by_cases hlen : w < N + gates.length
      · let i : Fin gates.length := ⟨w - N, by omega⟩
        have heq : N + i.val = w := by dsimp [i]; omega
        have hR : R (N + i.val) := heq.symm ▸ hrw
        have hval : val gates x (N + i.val) = true := heq.symm ▸ ht
        rcases ops (gates.get i) (List.get_mem _ _) with hand | hor
        · exact Or.inr ⟨w, hrw, ⟨i, heq.symm, hand⟩, ht⟩
        · rw [val_gate gates x i (hw i), hor] at hval
          simp [GateOp.eval] at hval
          obtain ⟨e, he, heval⟩ := hval
          exact ih e (heq ▸ hw i e he) (closed i hR hor e he) heval
      · have hf := val_beyond gates x (w := w) (by omega)
        simp [hf] at ht

end PEqualNP.Outside.L_meta_1638

theorem PEqualNP.Outside.L_meta_1638 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 1 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    (∀ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → Y ∈ S) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false) ∧
    (∀ p : Fin N, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (p : ℕ) ∈ S) → p ∈ L i0) ∧
    (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true →
      (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (r : ℕ) ∈ S) ∨ ∃ a : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → a ∈ S) ∧ (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) ∧
    (∀ (a : Fin gates.length) (c : ℕ), (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      c ∈ (gates.get a).inputs → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      ∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) := by
  intro q m N L i0 T0 _ _ _ _ _ _ _ _ _ gates u hop _ hwire hzero
  let Reach (w : ℕ) := ∀ S : Set ℕ, u ∈ S →
    (∀ i : Fin gates.length, N + i.val ∈ S →
      (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      ∀ e ∈ (gates.get i).inputs, e ∈ S) → w ∈ S
  let base := fun v : Fin N => decide (v ∉ L i0)
  have hroot : Reach u := fun _ hu _ => hu
  have hdown (i : Fin gates.length) (h : Reach (N + i.val))
      (ho : (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or)
      (e : ℕ) (he : e ∈ (gates.get i).inputs) : Reach e := by
    intro S hu hS
    exact hS i (h S hu hS) ho e he
  have allFalse (Y : ℕ) (hY : Reach Y) : PEqualNP.Outside.L_meta_1638.val gates base Y = false := by
    apply hY {w | PEqualNP.Outside.L_meta_1638.val gates base w = false} hzero
    intro i hi ho e he
    change PEqualNP.Outside.L_meta_1638.val gates base (N + i.val) = false at hi
    rw [PEqualNP.Outside.L_meta_1638.val_gate gates base i (hwire i), ho] at hi
    change PEqualNP.Outside.L_meta_1638.val gates base e = false
    cases h : PEqualNP.Outside.L_meta_1638.val gates base e with
    | false => rfl
    | true =>
      have ht : ((gates.get i).inputs.map (PEqualNP.Outside.L_meta_1638.val gates base)).any id = true :=
        List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨e, he, h⟩, rfl⟩
      exact Bool.noConfusion (ht.symm.trans hi)
  have points (p : Fin N) (h : Reach p.val) : p ∈ L i0 := by
    have hf := allFalse p.val h
    rw [PEqualNP.Outside.L_meta_1638.val_input] at hf
    simpa [base] using hf
  refine ⟨allFalse, points, ?_, ?_⟩
  · intro r _ hat
    exact PEqualNP.Outside.L_meta_1638.reach_hit gates (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) r Reach
      (fun g hg => (hop g hg).1) hwire
      (by
        intro p hp htrue
        simpa [points p hp] using htrue)
      hdown u hroot hat
  · intro a c hand _ hc _ r _ ha
    change PEqualNP.Outside.L_meta_1638.val gates _ (N + a.val) = true at ha
    rw [PEqualNP.Outside.L_meta_1638.val_gate gates _ a (hwire a), hand] at ha
    exact (List.all_eq_true.mp ha) _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
