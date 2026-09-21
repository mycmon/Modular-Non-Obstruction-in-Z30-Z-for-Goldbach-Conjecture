import Mathlib

open ZMod

/-- 1. Cas p = 2 : La classe 0 est la somme des deux unités (1 + 1). -/
lemma local_goldbach_two (c : ZMod 2) (hc : c = 0) :
    ∃ (r1 : Units (ZMod 2)) (r2 : Units (ZMod 2)), (r1 : ZMod 2) + (r2 : ZMod 2) = c := by
  use 1, 1
  subst hc
  decide

/-- Lemme auxiliaire généralisé pour éviter l'échec de réécriture dépendante. -/
lemma local_goldbach_two_gen (p_val : ℕ) (hp : p_val = 2) (c_val : ZMod p_val) (hc : c_val = 0) :
    ∃ (r1 : Units (ZMod p_val)) (r2 : Units (ZMod p_val)), (r1 : ZMod p_val) + (r2 : ZMod p_val) = c_val := by
  subst hp
  exact local_goldbach_two c_val hc

/-- 2. Cas p ≥ 3 : Toute classe c dans ZMod p se décompose en deux unités. -/
lemma local_goldbach_odd (p : ℕ) [hp : Fact p.Prime] (hp3 : p ≥ 3) (c : ZMod p) :
    ∃ (r1 : Units (ZMod p)) (r2 : Units (ZMod p)), (r1 : ZMod p) + (r2 : ZMod p) = c := by
  let forbidden : Finset (ZMod p) := {0, c}
  
  have h_forb : forbidden.card ≤ 2 := by
    have h_ins := Finset.card_insert_le 0 ({c} : Finset (ZMod p))
    rw [Finset.card_singleton] at h_ins
    omega

  have h_univ : (Finset.univ : Finset (ZMod p)).card = p := ZMod.card p

  have h_nonempty : ∃ x : ZMod p, x ∉ forbidden := by
    by_contra h
    have h_sub : (Finset.univ : Finset (ZMod p)) ⊆ forbidden := by
      intro x _
      by_contra hx
      exact h ⟨x, hx⟩
    have h_le := Finset.card_le_card h_sub
    rw [h_univ] at h_le
    omega

  rcases h_nonempty with ⟨x, hx⟩
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  have hx0 : x ≠ 0 := hx.1
  have hxc : x ≠ c := hx.2
  have hy0 : c - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxc)

  let u1 : Units (ZMod p) := Units.mk0 x hx0
  let u2 : Units (ZMod p) := Units.mk0 (c - x) hy0
  use u1, u2
  change x + (c - x) = c
  ring

/-- 3. Théorème de relèvement structurel général sur produit cartésien. -/
theorem goldbach_local_primorial_general 
    (k : ℕ) (p : Fin k → ℕ) [∀ i, Fact (p i).Prime]
    (_hp_two : ∃ i, p i = 2)
    (hp_odd : ∀ i, p i ≠ 2 → p i ≥ 3)
    (c : ∀ i, ZMod (p i))
    (hc_even : ∀ i, p i = 2 → c i = 0) :
    ∃ (r1 r2 : ∀ i, Units (ZMod (p i))), 
      (fun i => (r1 i : ZMod (p i)) + (r2 i : ZMod (p i))) = c := by
  have h_comp : ∀ i, ∃ (u1 u2 : Units (ZMod (p i))), (u1 : ZMod (p i)) + (u2 : ZMod (p i)) = c i := by
    intro i
    by_cases hp2 : p i = 2
    · have hc0 : c i = 0 := hc_even i hp2
      exact local_goldbach_two_gen (p i) hp2 (c i) hc0
    · have hp3 : p i ≥ 3 := hp_odd i hp2
      exact local_goldbach_odd (p i) hp3 (c i)

  choose r1 r2 hr using h_comp
  use r1, r2
  funext i
  exact hr i

