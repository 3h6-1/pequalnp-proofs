import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1634

open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [ite_eq_left h1, List.getElem?_append_left h1]
  · rw [ite_eq_right h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [ite_eq_right h2]
      have : t - l.length ≠ 0 := by omega
      simp [this]

def Le (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi; exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hi hv⟩

theorem W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : Le x y) : Le (W gs x) (W gs y) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : (W gs x).length = (W gs y).length := by simp [W_length, hl]
    rw [W_snoc, getD_snoc] at ht ⊢
    rw [← hlen]
    by_cases h1 : t < (W gs x).length
    · rw [ite_eq_left h1] at ht ⊢; exact ih t ht
    · rw [ite_eq_right h1] at ht ⊢
      by_cases h2 : t = (W gs x).length
      · rw [ite_eq_left h2] at ht ⊢
        exact eval_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [ite_eq_right h2] at ht; simp at ht

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (k : ℕ) :
    (List.ofFn f).getD k false = if h : k < n then f ⟨k, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : k < n <;> simp [h]

theorem wire_mono {N : ℕ} (gs : List Gate) (w : ℕ) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin N → Bool) (h : ∀ v, x v = true → y v = true) :
    Circuit.eval ⟨gs, w⟩ (List.ofFn x) = true → Circuit.eval ⟨gs, w⟩ (List.ofFn y) = true := by
  apply W_mono gs hm _ _ (by simp) _ w
  intro i hi
  rw [ofFn_getD] at hi ⊢
  by_cases hiN : i < N
  · rw [dite_eq_left hiN] at hi ⊢
    exact h _ hi
  · simp [hiN] at hi

theorem one_side {N : ℕ} (A B : Finset (Fin N)) (U : Fin N → Fin N → Bool)
    (f : (Fin N → Bool) → Bool)
    (mono : ∀ x y : Fin N → Bool, (∀ v, x v = true → y v = true) → f x = true → f y = true)
    (meet : (A ∩ B).card = 1)
    (off : f (fun v => decide (v ∉ B)) = false)
    (two : 2 ≤ (A.filter (fun p => f (U p) = true)).card) :
    ∃ p ∈ A \ B, ∃ v ∈ B, U p v = true := by
  classical
  have hex : ∃ p ∈ A.filter (fun p => f (U p) = true), p ∉ B := by
    by_contra h
    have sub : A.filter (fun p => f (U p) = true) ⊆ A ∩ B := by
      intro p hp
      refine Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hp).1, ?_⟩
      by_contra hnot
      exact h ⟨p, hp, hnot⟩
    have hle := Finset.card_le_card sub
    omega
  obtain ⟨p, hp, hpB⟩ := hex
  obtain ⟨hpA, hval⟩ := Finset.mem_filter.mp hp
  refine ⟨p, Finset.mem_sdiff.mpr ⟨hpA, hpB⟩, ?_⟩
  by_contra h
  have hsub : ∀ v, U p v = true → decide (v ∉ B) = true := by
    intro v hv
    apply decide_eq_true
    intro hvB
    exact h ⟨v, hvB, hv⟩
  have htrue := mono (U p) (fun v => decide (v ∉ B)) hsub hval
  exact Bool.noConfusion (off.symm.trans htrue)

end PEqualNP.Outside.L_meta_1634

theorem PEqualNP.Outside.L_meta_1634 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ (w : ℕ) (t u : Fin N), t ≠ u → ev w (fun v : Fin N => decide (v ∉ L t)) = false → ev w (fun v : Fin N => decide (v ∉ L u)) = false →
      2 ≤ ((L t).filter (fun p => ev w (T t p) = true)).card → 2 ≤ ((L u).filter (fun p => ev w (T u p) = true)).card →
      (∃ p ∈ L t \ L u, ∃ v ∈ L u, T t p v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, T u p v = true) := by
  intro q N L i0 p0 p1 _ _ _ meet _ _ _ _ T _ gates hops _ _ ev hev w t u hne ht hu hct hcu
  have hm : ∀ x y : Fin N → Bool, (∀ v, x v = true → y v = true) →
      ev w x = true → ev w y = true := by
    intro x y hxy
    rw [hev, hev]
    exact PEqualNP.Outside.L_meta_1634.wire_mono gates w (fun g hg => (hops g hg).1) x y hxy
  exact ⟨PEqualNP.Outside.L_meta_1634.one_side (L t) (L u) (T t) (ev w) hm (meet t u hne) hu hct,
    PEqualNP.Outside.L_meta_1634.one_side (L u) (L t) (T u) (ev w) hm (meet u t hne.symm) ht hcu⟩
