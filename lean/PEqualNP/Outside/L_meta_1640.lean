import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1640

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

end PEqualNP.Outside.L_meta_1640

open PEqualNP.Outside.L_meta_1640 PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_1640 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 1 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (ch : Fin gates.length → ℕ),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false → (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) →
    (∀ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r2 ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r2))) = true) → ch a ∈ (gates.get a).inputs ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, ch a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false) →
    (∀ r ∈ L i0 \ T0, (∀ S : Set ℕ, o ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (r : ℕ) ∈ S) ∨
      ∃ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r2 ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r2))) = true) ∧ (∀ S : Set ℕ, ch a ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (r : ℕ) ∈ S)) ∧
    (∀ a : Fin gates.length, o = N + (a : ℕ) → (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r2 ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r2))) = true)) := by
  classical
  intro q m N L i0 T0 _ _ hmq _ hcard _ _ _ hT gates o ch hops _ hwire hz hon hchoose
  let base (v : Fin N) := decide (v ∉ L i0)
  let flip (r v : Fin N) := decide (v ∉ L i0 ∨ v = r)
  let R (s w : ℕ) := ∀ S : Set ℕ, s ∈ S →
    (∀ i : Fin gates.length, N + i.val ∈ S → (gates.get i).op = GateOp.or →
      ∀ e ∈ (gates.get i).inputs, e ∈ S) → w ∈ S
  let M (a : Fin gates.length) := (gates.get a).op = GateOp.and ∧
    val gates base (N + a.val) = false ∧
    ∃ r ∈ L i0 \ T0, val gates (flip r) (N + a.val) = true
  let Good (w : ℕ) := R o w ∨ ∃ a : Fin gates.length, M a ∧ R (ch a) w
  have reflR (s : ℕ) : R s s := fun _ h _ => h
  have stepR {s : ℕ} (i : Fin gates.length) (h : R s (N + i.val))
      (ho : (gates.get i).op = GateOp.or) (e : ℕ) (he : e ∈ (gates.get i).inputs) : R s e := by
    intro S hs hS
    exact hS i (h S hs hS) ho e he
  change (∀ r ∈ L i0 \ T0, Good r.val) ∧
    (∀ a : Fin gates.length, o = N + a.val → (gates.get a).op = GateOp.and → M a)
  constructor
  · intro r hr
    have descend (w : ℕ) : Good w → val gates base w = false →
        val gates (flip r) w = true → Good r.val := by
      induction w using Nat.strongRecOn with
      | ind w ih =>
        intro hg hf ht
        by_cases raw : w < N
        · let p : Fin N := ⟨w, raw⟩
          have hp : base p = false := (val_input gates base p).symm.trans hf
          have hp' : p ∈ L i0 := by simpa [base] using hp
          have ht' : flip r p = true := (val_input gates (flip r) p).symm.trans ht
          have eqr : p = r := by simpa [flip, hp'] using ht'
          exact eqr ▸ (show Good p.val from hg)
        by_cases live : w < N + gates.length
        · let i : Fin gates.length := ⟨w - N, by omega⟩
          have heq : N + i.val = w := by dsimp [i]; omega
          have fi : val gates base (N + i.val) = false := heq.symm ▸ hf
          have ti : val gates (flip r) (N + i.val) = true := heq.symm ▸ ht
          rcases (hops (gates.get i) (List.get_mem _ _)).1 with ha | ho
          · have mi : M i := ⟨ha, fi, r, hr, ti⟩
            obtain ⟨hc, hcf⟩ := hchoose i mi
            rw [val_gate gates (flip r) i (hwire i), ha] at ti
            have hct : val gates (flip r) (ch i) = true :=
              (List.all_eq_true.mp ti) _ (List.mem_map.mpr ⟨ch i, hc, rfl⟩)
            exact ih (ch i) (heq ▸ hwire i _ hc) (Or.inr ⟨i, mi, reflR _⟩) hcf hct
          · rw [val_gate gates (flip r) i (hwire i), ho] at ti
            simp [GateOp.eval] at ti
            obtain ⟨e, he, het⟩ := ti
            have gef : Good e := by
              have gi : Good (N + i.val) := heq.symm ▸ hg
              rcases gi with one | ⟨a, ma, ra⟩
              · exact Or.inl (stepR i one ho e he)
              · exact Or.inr ⟨a, ma, stepR i ra ho e he⟩
            rw [val_gate gates base i (hwire i), ho] at fi
            have hef : val gates base e = false := by
              cases h : val gates base e with
              | false => rfl
              | true =>
                have bad : ((gates.get i).inputs.map (val gates base)).any id = true :=
                  List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨e, he, h⟩, rfl⟩
                exact Bool.noConfusion (bad.symm.trans fi)
            exact ih e (heq ▸ hwire i _ he) gef hef het
        · have out := val_beyond gates (flip r) (w := w) (by omega)
          simp [out] at ht
    exact descend o (Or.inl (reflR _)) hz (hon r hr)
  · intro a heq ha
    have hlt : T0.card < (L i0).card := by rw [hT, hcard]; omega
    obtain ⟨r, hr⟩ := Finset.sdiff_nonempty_of_card_lt_card hlt
    exact ⟨ha, heq ▸ hz, r, hr, heq ▸ hon r hr⟩
