import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

/-! Formal proof of the Imbalance Conjecture, including Erdős–Gallai sufficiency. -/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
open Finset BigOperators
namespace ErdosGallai

/-- Exact degree-multiset realization by a finite simple graph. -/
def Graphic (s : Multiset ℕ) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    (Finset.univ.val.map (fun v => G.degree v)) = s
noncomputable def addV {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T : Finset V) : SimpleGraph (V ⊕ Unit) where
  Adj x y :=
    match x, y with
    | Sum.inl a, Sum.inl b => G.Adj a b
    | Sum.inl a, Sum.inr _ => a ∈ T
    | Sum.inr _, Sum.inl b => b ∈ T
    | Sum.inr _, Sum.inr _ => False
  symm := by rintro (a|a) (b|b) h <;> simp_all [G.adj_symm]
  loopless := ⟨by rintro (a|a) h <;> simp_all⟩
instance addVDec {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) : DecidableRel (addV G T).Adj := by
  intro x y; cases x <;> cases y <;> simp only [addV] <;> infer_instance
@[simp] lemma addV_adj_ll {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (T : Finset V)
    (a b : V) : (addV G T).Adj (Sum.inl a) (Sum.inl b) ↔ G.Adj a b := Iff.rfl
@[simp] lemma addV_adj_lr {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (T : Finset V)
    (a : V) (u : Unit) : (addV G T).Adj (Sum.inl a) (Sum.inr u) ↔ a ∈ T := Iff.rfl
@[simp] lemma addV_adj_rl {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (T : Finset V)
    (b : V) (u : Unit) : (addV G T).Adj (Sum.inr u) (Sum.inl b) ↔ b ∈ T := Iff.rfl
lemma addV_degree_new {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (T : Finset V) : (addV G T).degree (Sum.inr ()) = T.card := by
  rw [SimpleGraph.degree]
  rw [show (addV G T).neighborFinset (Sum.inr ()) = T.map ⟨Sum.inl, Sum.inl_injective⟩ from ?_]
  · rw [Finset.card_map]
  · ext x; cases x <;> simp [SimpleGraph.mem_neighborFinset]
lemma addV_degree_old {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (T : Finset V) (a : V) :
    (addV G T).degree (Sum.inl a) = G.degree a + (if a ∈ T then 1 else 0) := by
  rw [SimpleGraph.degree, SimpleGraph.degree]
  rw [show (addV G T).neighborFinset (Sum.inl a)
        = (G.neighborFinset a).map ⟨Sum.inl, Sum.inl_injective⟩
          ∪ (if a ∈ T then {Sum.inr ()} else ∅) from ?_]
  · rw [Finset.card_union_of_disjoint, Finset.card_map]
    · split <;> simp
    · by_cases h : a ∈ T <;> simp [h]
  · ext x; cases x <;> by_cases h : a ∈ T <;>
      simp [SimpleGraph.mem_neighborFinset, h]
lemma exists_submultiset_map {α β : Type} (f : α → β) (s : Multiset α) (c : Multiset β)
    (h : c ≤ s.map f) : ∃ s' ≤ s, s'.map f = c := by
  induction s using Multiset.induction generalizing c with
  | empty => simp only [Multiset.map_zero, Multiset.le_zero] at h; exact ⟨0, le_refl _, by simp [h]⟩
  | cons a s ih =>
    rw [Multiset.map_cons] at h
    by_cases hmem : f a ∈ c
    · obtain ⟨c', rfl⟩ := Multiset.exists_cons_of_mem hmem
      have hc' : c' ≤ s.map f := (Multiset.cons_le_cons_iff (f a)).mp h
      obtain ⟨s', hs', hs'eq⟩ := ih c' hc'
      exact ⟨a ::ₘ s', Multiset.cons_le_cons a hs', by simp [hs'eq]⟩
    · have hcs : c ≤ s.map f := by
        rcases Multiset.le_cons_of_notMem hmem |>.mp h with h'
        exact h'
      obtain ⟨s', hs', hs'eq⟩ := ih c hcs
      exact ⟨s', le_trans hs' (Multiset.le_cons_self s a), hs'eq⟩
lemma graphic_add (t c : Multiset ℕ) (hc : c ≤ t) (h : Graphic t) :
    Graphic (c.card ::ₘ ((t - c) + c.map (· + 1))) := by
  classical
  obtain ⟨V, _, _, G, hGdec, hG⟩ := h
  rw [← hG] at hc
  obtain ⟨s', hs'le, hs'eq⟩ := exists_submultiset_map (fun v => G.degree v) Finset.univ.val c hc
  have hnd : s'.Nodup := Multiset.nodup_of_le hs'le Finset.univ.nodup
  refine ⟨V ⊕ Unit, inferInstance, inferInstance, addV G ⟨s', hnd⟩, inferInstance, ?_⟩
  set S : Finset V := ⟨s', hnd⟩ with hS
  have hcval : S.val.map (fun v => G.degree v) = c := hs'eq
  have hcard : S.card = c.card := by rw [Finset.card, hS, ← hs'eq, Multiset.card_map]
  have hdecomp : ((Finset.univ : Finset (V ⊕ Unit)).val.map (fun v => (addV G S).degree v))
      = (Finset.univ.val.map (fun a : V => (addV G S).degree (Sum.inl a)))
        + {(addV G S).degree (Sum.inr ())} := by
    have h1 : (Finset.univ : Finset (V ⊕ Unit)).val =
        (Finset.univ.val.map (Sum.inl : V → V ⊕ Unit))
          + (Finset.univ.val.map (Sum.inr : Unit → V ⊕ Unit)) := rfl
    rw [h1, Multiset.map_add, Multiset.map_map, Multiset.map_map]; congr 1
  rw [hdecomp, addV_degree_new]
  simp only [addV_degree_old]
  rw [hcard]
  have hmanip : Finset.univ.val.map (fun a => G.degree a + if a ∈ S then 1 else 0)
      = (t - c) + c.map (· + 1) := by
    have hpart : (Finset.univ.val : Multiset V)
        = Finset.univ.val.filter (· ∈ S) + Finset.univ.val.filter (fun a => a ∉ S) :=
      (Multiset.filter_add_not _ _).symm
    have hSfil : Finset.univ.val.filter (· ∈ S) = S.val := by
      rw [← Finset.filter_val, Finset.filter_mem_eq_inter, Finset.univ_inter]
    conv_lhs => rw [hpart]
    rw [Multiset.map_add]
    have hA : (Finset.univ.val.filter (· ∈ S)).map (fun a => G.degree a + if a ∈ S then 1 else 0)
        = c.map (· + 1) := by
      rw [hSfil, ← hcval, Multiset.map_map]
      apply Multiset.map_congr rfl
      intro x hx; rw [Finset.mem_val] at hx; simp [hx]
    have hB : (Finset.univ.val.filter (fun a => a ∉ S)).map
          (fun a => G.degree a + if a ∈ S then 1 else 0)
        = t - c := by
      have hBmap : (Finset.univ.val.filter (fun a => a ∉ S)).map
            (fun a => G.degree a + if a ∈ S then 1 else 0)
          = (Finset.univ.val.filter (fun a => a ∉ S)).map (fun v => G.degree v) := by
        apply Multiset.map_congr rfl
        intro x hx
        have : x ∉ S := by simpa using (Multiset.mem_filter.mp hx).2
        simp [this]
      rw [hBmap]
      have hsum : c + (Finset.univ.val.filter (fun a => a ∉ S)).map (fun v => G.degree v) = t := by
        rw [← hcval, ← Multiset.map_add, ← hSfil, ← hpart, hG]
      rw [← hsum, add_tsub_cancel_left]
    rw [hA, hB, add_comm]
  rw [hmanip, add_comm, Multiset.singleton_add]
lemma graphic_replicate_zero (n : ℕ) : Graphic (Multiset.replicate n 0) := by
  refine ⟨Fin n, inferInstance, inferInstance, ⊥, inferInstance, ?_⟩
  have h : (fun v : Fin n => (⊥ : SimpleGraph (Fin n)).degree v) = fun _ => 0 := by
    funext v; exact SimpleGraph.bot_degree v
  rw [h, Multiset.map_const']
  congr 1
  simp
/-- The `k`-th Erdős–Gallai inequality for a descending list. -/
def EGineq (l : List ℕ) (k : ℕ) : Prop :=
  (l.take k).sum ≤ k * (k - 1) + ((l.drop k).map (fun d => min k d)).sum
def hhDec : List ℕ → List ℕ
  | [] => []
  | Δ :: rest => (rest.take Δ).map (· - 1) ++ rest.drop Δ
def geB (a b : ℕ) : Bool := decide (b ≤ a)
def hhSort (l : List ℕ) : List ℕ := (hhDec l).mergeSort geB
lemma hhSort_perm (l : List ℕ) : (hhSort l).Perm (hhDec l) :=
  List.mergeSort_perm _ _
lemma hhSort_sorted (l : List ℕ) : (hhSort l).Pairwise (· ≥ ·) := by
  have h := List.pairwise_mergeSort (le := geB)
    (by intro a b c; simp [geB]; omega) (by intro a b; simp [geB]; omega) (hhDec l)
  refine h.imp ?_
  intro a b hab; simp only [geB, decide_eq_true_eq] at hab; exact hab
lemma hhSort_coe (l : List ℕ) : ((hhSort l : List ℕ) : Multiset ℕ) = (hhDec l : Multiset ℕ) :=
  Multiset.coe_eq_coe.mpr (hhSort_perm l)
lemma head_le_of_EG1 (Δ : ℕ) (rest : List ℕ) (h : EGineq (Δ :: rest) 1) :
    Δ ≤ ((rest.map (fun d => min 1 d)).sum) := by
  simp only [EGineq, List.drop_succ_cons, List.drop_zero] at h
  simpa using h
lemma pos_prefix : ∀ (rest : List ℕ), rest.Pairwise (· ≥ ·) → ∀ (Δ : ℕ),
    Δ ≤ (rest.map (fun d => min 1 d)).sum → ∀ x ∈ rest.take Δ, 1 ≤ x := by
  intro rest
  induction rest with
  | nil => intro _ Δ _ x hx; simp at hx
  | cons r rs ih =>
    intro hsr Δ hΔ x hx
    have hrs : rs.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hsr).2
    have hrge : ∀ y ∈ rs, r ≥ y := (List.pairwise_cons.mp hsr).1
    cases Δ with
    | zero => simp at hx
    | succ m =>
      have hr1 : 1 ≤ r := by
        by_contra hc
        push Not at hc
        have hr0 : r = 0 := by omega
        have hrs0 : (rs.map (fun d => min 1 d)).sum = 0 := by
          apply List.sum_eq_zero
          intro y hy
          rw [List.mem_map] at hy
          obtain ⟨z, hz, rfl⟩ := hy
          have := hrge z hz
          omega
        simp [List.map_cons, hr0, hrs0] at hΔ
      rw [List.take_succ_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hr1
      · have hΔ' : m ≤ (rs.map (fun d => min 1 d)).sum := by
          simp only [List.map_cons, List.sum_cons] at hΔ
          have : min 1 r = 1 := by omega
          omega
        exact ih hrs m hΔ' x hx
lemma take_pos (Δ : ℕ) (rest : List ℕ) (hsort : (Δ :: rest).Pairwise (· ≥ ·))
    (hΔ : Δ ≤ ((rest.map (fun d => min 1 d)).sum)) :
    (Δ ≤ rest.length) ∧ (∀ x ∈ rest.take Δ, 1 ≤ x) := by
  have hsr : rest.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hsort).2
  refine ⟨?_, pos_prefix rest hsr Δ hΔ⟩
  have hle : (rest.map (fun d => min 1 d)).sum ≤ rest.length := by
    have := List.sum_le_card_nsmul (rest.map (fun d => min 1 d)) 1 (by
      intro x hx; rw [List.mem_map] at hx; obtain ⟨z, _, rfl⟩ := hx; exact min_le_left _ _)
    simpa using this
  omega
lemma map_pred_sum (L : List ℕ) (h : ∀ x ∈ L, 1 ≤ x) :
    (L.map (· - 1)).sum + L.length = L.sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha : 1 ≤ a := h a (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega
lemma hhSort_sum (Δ : ℕ) (rest : List ℕ) (hΔlen : Δ ≤ rest.length)
    (hpos : ∀ x ∈ rest.take Δ, 1 ≤ x) :
    (hhSort (Δ :: rest)).sum + 2 * Δ = (Δ :: rest).sum := by
  have hperm : (hhSort (Δ :: rest)).Perm (hhDec (Δ :: rest)) := List.mergeSort_perm _ _
  rw [hperm.sum_eq]
  unfold hhDec
  rw [List.sum_append]
  have hlen : (rest.take Δ).length = Δ := by rw [List.length_take]; omega
  have key := map_pred_sum (rest.take Δ) hpos
  rw [hlen] at key
  have hsplit : (rest.take Δ).sum + (rest.drop Δ).sum = rest.sum := by
    rw [← List.sum_append, List.take_append_drop]
  simp only [List.sum_cons]
  omega
lemma hhSort_length (Δ : ℕ) (rest : List ℕ) :
    (hhSort (Δ :: rest)).length = rest.length := by
  unfold hhSort hhDec
  rw [List.length_mergeSort, List.length_append, List.length_map, List.length_take,
    List.length_drop]
  omega
lemma graphic_reconstruct (Δ : ℕ) (rest : List ℕ) (hΔlen : Δ ≤ rest.length)
    (hpos : ∀ x ∈ rest.take Δ, 1 ≤ x)
    (h : Graphic ((hhSort (Δ :: rest) : List ℕ) : Multiset ℕ)) :
    Graphic ((Δ :: rest : List ℕ) : Multiset ℕ) := by
  rw [hhSort_coe] at h
  set t : Multiset ℕ := (hhDec (Δ :: rest) : Multiset ℕ) with ht
  set c : Multiset ℕ := (((rest.take Δ).map (· - 1) : List ℕ) : Multiset ℕ) with hcdef
  have htc : t = c + ((rest.drop Δ : List ℕ) : Multiset ℕ) := by
    rw [ht, hcdef]; show ((hhDec (Δ :: rest) : List ℕ) : Multiset ℕ) = _
    unfold hhDec; rw [← Multiset.coe_add]
  have hcle : c ≤ t := by rw [htc]; exact Multiset.le_add_right _ _
  have hccard : c.card = Δ := by
    rw [hcdef, Multiset.coe_card, List.length_map, List.length_take]; omega
  have htsub : t - c = ((rest.drop Δ : List ℕ) : Multiset ℕ) := by
    rw [htc, add_tsub_cancel_left]
  have hcmap : c.map (· + 1) = ((rest.take Δ : List ℕ) : Multiset ℕ) := by
    rw [hcdef, Multiset.map_coe]; congr 1
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (rest.take Δ)]
    apply List.map_congr_left
    intro x hx; have := hpos x hx
    simp only [Function.comp, id]; omega
  have hfinal := graphic_add t c hcle h
  rw [hccard, htsub, hcmap] at hfinal
  have heq : (Δ ::ₘ (((rest.drop Δ : List ℕ) : Multiset ℕ) + ((rest.take Δ : List ℕ) : Multiset ℕ)))
      = ((Δ :: rest : List ℕ) : Multiset ℕ) := by
    rw [add_comm, Multiset.coe_add, List.take_append_drop, ← Multiset.cons_coe]
  rw [heq] at hfinal
  exact hfinal
universe u v

lemma exists_submultiset_map_u {α : Type u} {β : Type v}
    (f : α → β) (s : Multiset α) (c : Multiset β)
    (h : c ≤ s.map f) : ∃ s' ≤ s, s'.map f = c := by
  induction s using Multiset.induction generalizing c with
  | empty =>
      simp only [Multiset.map_zero, Multiset.le_zero] at h
      exact ⟨0, le_refl _, by simp [h]⟩
  | cons a s ih =>
    rw [Multiset.map_cons] at h
    by_cases hmem : f a ∈ c
    · obtain ⟨c', rfl⟩ := Multiset.exists_cons_of_mem hmem
      have hc' : c' ≤ s.map f :=
        (Multiset.cons_le_cons_iff (f a)).mp h
      obtain ⟨s', hs', hs'eq⟩ := ih c' hc'
      exact ⟨a ::ₘ s', Multiset.cons_le_cons a hs',
        by simp [hs'eq]⟩
    · have hcs : c ≤ s.map f := by
        exact Multiset.le_cons_of_notMem hmem |>.mp h
      obtain ⟨s', hs', hs'eq⟩ := ih c hcs
      exact ⟨s', le_trans hs' (Multiset.le_cons_self s a), hs'eq⟩

lemma eg_next_of_small (a tail : List ℕ) (d k : ℕ)
    (hlen : a.length = k - 1) (hk : 1 < k) (hd : d < k)
    (hprev : EGineq (a ++ d :: tail) (k - 1)) :
    EGineq (a ++ d :: tail) k := by
  have hmin_d : min (k - 1) d = d := by omega
  have htail :
      ((tail.map (fun x => min (k - 1) x)).sum) ≤
        (tail.map (fun x => min k x)).sum := by
    apply List.sum_le_sum
    intro x hx
    omega
  have hk_eq : k = a.length + 1 := by omega
  subst k
  simp [EGineq] at hprev ⊢
  have hmin_d' : min a.length d = d := by simpa using hmin_d
  have htail' :
      (tail.map (fun x => min a.length x)).sum ≤
        (tail.map (fun x => min (a.length + 1) x)).sum := by
    simpa using htail
  rw [hmin_d'] at hprev
  have hdle : d ≤ a.length := by omega
  have hquad :
      a.length * (a.length - 1) + 2 * a.length =
        (a.length + 1) * a.length := by
    calc
      a.length * (a.length - 1) + 2 * a.length =
          a.length * ((a.length - 1) + 2) := by ring
      _ = a.length * (a.length + 1) := by
        congr 1
        omega
      _ = (a.length + 1) * a.length := Nat.mul_comm _ _
  calc
    a.sum + d ≤
        (a.length * (a.length - 1) + d +
          (tail.map (fun x => min a.length x)).sum) + d := by omega
    _ = a.length * (a.length - 1) + 2 * d +
          (tail.map (fun x => min a.length x)).sum := by omega
    _ ≤ a.length * (a.length - 1) + 2 * a.length +
          (tail.map (fun x => min (a.length + 1) x)).sum := by omega
    _ = (a.length + 1) * a.length +
          (tail.map (fun x => min (a.length + 1) x)).sum := by
            rw [hquad]

lemma eg_all_of_critical (l : List ℕ)
    (hcrit : ∀ (a tail : List ℕ) (d k : ℕ),
      l = a ++ d :: tail → a.length = k - 1 → k ≤ d → EGineq l k) :
    ∀ k, 1 ≤ k → k ≤ l.length → EGineq l k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk hkle
      have hdrop_ne : l.drop (k - 1) ≠ [] := by
        intro hnil
        have hlen_drop : (l.drop (k - 1)).length = l.length - (k - 1) := by
          simp
        rw [hnil] at hlen_drop
        simp only [List.length_nil] at hlen_drop
        omega
      cases hdt : l.drop (k - 1) with
      | nil => exact (hdrop_ne hdt).elim
      | cons d tail =>
          let a := l.take (k - 1)
          have ha_len : a.length = k - 1 := by
            simp [a, List.length_take]
            omega
          have hl : l = a ++ d :: tail := by
            dsimp [a]
            rw [← hdt]
            exact (List.take_append_drop (k - 1) l).symm
          by_cases hkd : k ≤ d
          · exact hcrit a tail d k hl ha_len hkd
          · have hdk : d < k := by omega
            by_cases hk1 : k = 1
            · subst k
              have hd0 : d = 0 := by omega
              subst d
              have ha0 : a = [] := List.eq_nil_of_length_eq_zero (by omega)
              subst a
              rw [hl]
              simp [EGineq]
            · have hkgt : 1 < k := by omega
              have hprev : EGineq l (k - 1) :=
                ih (k - 1) (by omega) (by omega) (by omega)
              rw [hl] at hprev ⊢
              exact eg_next_of_small a tail d k ha_len hkgt hdk hprev

lemma exists_gt_le_split (k : ℕ) (l : List ℕ)
    (hsort : l.Pairwise (· ≥ ·)) :
    ∃ H L : List ℕ, l = H ++ L ∧
      (∀ x ∈ H, k < x) ∧ (∀ x ∈ L, x ≤ k) := by
  induction l with
  | nil =>
      exact ⟨[], [], rfl, by simp, by simp⟩
  | cons x xs ih =>
      have hxs : xs.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hsort).2
      by_cases hx : k < x
      · obtain ⟨H, L, hHL, hH, hL⟩ := ih hxs
        exact ⟨x :: H, L, by simp [hHL], by
          intro y hy
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact hx
          · exact hH y hy, hL⟩
      · refine ⟨[], x :: xs, rfl, by simp, ?_⟩
        intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · omega
        · have hxy : x ≥ y := (List.pairwise_cons.mp hsort).1 y hy
          omega

lemma mergeSort_ge_pairwise (l : List ℕ) :
    (l.mergeSort geB).Pairwise (· ≥ ·) := by
  have h := List.pairwise_mergeSort (le := geB)
    (by intro a b c; simp [geB]; omega)
    (by intro a b; simp [geB]; omega) l
  refine h.imp ?_
  intro a b hab
  simp only [geB, decide_eq_true_eq] at hab
  exact hab

lemma sort_eq_high_append (l hi lo : List ℕ)
    (hl : l = hi ++ lo)
    (hhi : hi.Pairwise (· ≥ ·))
    (hcross : ∀ x ∈ hi, ∀ y ∈ lo, x ≥ y) :
    l.mergeSort geB = hi ++ lo.mergeSort geB := by
  have hright : (hi ++ lo.mergeSort geB).Pairwise (· ≥ ·) := by
    rw [List.pairwise_append]
    refine ⟨hhi, mergeSort_ge_pairwise lo, ?_⟩
    intro x hx y hy
    apply hcross x hx y
    exact (List.mergeSort_perm lo geB).mem_iff.mp hy
  have hp : (l.mergeSort geB).Perm (hi ++ lo.mergeSort geB) := by
    have hp₁ : (l.mergeSort geB).Perm (hi ++ lo) := by
      simpa [hl] using List.mergeSort_perm l geB
    have hp₂ : (hi ++ lo).Perm (hi ++ lo.mergeSort geB) :=
      (List.Perm.append_left hi (List.mergeSort_perm lo geB)).symm
    exact hp₁.trans hp₂
  exact hp.eq_of_pairwise' (mergeSort_ge_pairwise l) hright

lemma pred_pairwise (l : List ℕ) (hsort : l.Pairwise (· ≥ ·)) :
    (l.map (· - 1)).Pairwise (· ≥ ·) := by
  rw [List.pairwise_map]
  exact hsort.imp (by intro a b hab; omega)

lemma hhDec_split_of_high_le (Δ : ℕ) (rest H L : List ℕ)
    (hrest : rest = H ++ L) (hm : H.length ≤ Δ) :
    hhDec (Δ :: rest) =
      H.map (· - 1) ++
        ((L.take (Δ - H.length)).map (· - 1) ++
          L.drop (Δ - H.length)) := by
  simp only [hhDec]
  rw [hrest, List.take_append, List.drop_append]
  have htake : H.take Δ = H := (List.take_eq_self_iff H).mpr hm
  have hdrop : H.drop Δ = [] := List.drop_eq_nil_iff.mpr hm
  rw [htake, hdrop]
  simp only [List.map_append, List.nil_append]
  rw [List.append_assoc]

lemma map_min_sum_of_high_le (Δ k : ℕ) (rest H L : List ℕ)
    (hrest : rest = H ++ L)
    (hm : H.length ≤ Δ)
    (hH : ∀ x ∈ H, k < x)
    (hL : ∀ x ∈ L, x ≤ k)
    (hΔlen : Δ ≤ rest.length)
    (hpos : ∀ x ∈ rest.take Δ, 1 ≤ x) :
    ((hhSort (Δ :: rest)).map (fun x => min k x)).sum +
        (Δ - H.length) =
      k * H.length + L.sum := by
  have hdec := hhDec_split_of_high_le Δ rest H L hrest hm
  have hperm := (hhSort_perm (Δ :: rest)).map (fun x => min k x)
  rw [hdec] at hperm
  rw [hperm.sum_eq]
  have ha : Δ - H.length ≤ L.length := by
    have hlen : rest.length = H.length + L.length := by simp [hrest]
    omega
  have hposL : ∀ x ∈ L.take (Δ - H.length), 1 ≤ x := by
    intro x hx
    apply hpos x
    rw [hrest, List.take_append]
    have htake : H.take Δ = H := (List.take_eq_self_iff H).mpr hm
    rw [htake]
    simp only [List.mem_append]
    exact Or.inr (by simpa using hx)
  have hpredL := map_pred_sum (L.take (Δ - H.length)) hposL
  have hlenL : (L.take (Δ - H.length)).length = Δ - H.length := by
    simp [List.length_take, ha]
  rw [hlenL] at hpredL
  have hsplitL :
      (L.take (Δ - H.length)).sum +
        (L.drop (Δ - H.length)).sum = L.sum :=
    List.sum_take_add_sum_drop L (Δ - H.length)
  simp only [List.map_append, List.sum_append]
  have hmapH :
      ((H.map (· - 1)).map (fun x => min k x)).sum =
        k * H.length := by
    calc
      ((H.map (· - 1)).map (fun x => min k x)).sum =
          (H.map (fun _ => k)).sum := by
            congr 1
            rw [List.map_map]
            apply List.map_congr_left
            intro x hx
            have := hH x hx
            simp only [Function.comp_apply]
            omega
      _ = k * H.length := by simp [Nat.mul_comm]
  have hmapTake :
      (((L.take (Δ - H.length)).map (· - 1)).map
          (fun x => min k x)).sum =
        ((L.take (Δ - H.length)).map (· - 1)).sum := by
    rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro y hy
    have hyL : y ∈ L := List.mem_of_mem_take hy
    have := hL y hyL
    simp only [Function.comp_apply]
    omega
  have hmapDrop :
      ((L.drop (Δ - H.length)).map (fun x => min k x)).sum =
        (L.drop (Δ - H.length)).sum := by
    congr 1
    conv_rhs => rw [← List.map_id (L.drop (Δ - H.length))]
    apply List.map_congr_left
    intro x hx
    have hxL : x ∈ L := List.mem_of_mem_drop hx
    have := hL x hxL
    simp only [id_eq]
    omega
  rw [hmapH, hmapTake, hmapDrop]
  omega

lemma hhSort_split_of_high_le (Δ k : ℕ) (rest H L : List ℕ)
    (hrest : rest = H ++ L)
    (hm : H.length ≤ Δ)
    (hsortH : H.Pairwise (· ≥ ·))
    (hH : ∀ x ∈ H, k < x)
    (hL : ∀ x ∈ L, x ≤ k) :
    hhSort (Δ :: rest) =
      H.map (· - 1) ++
        (((L.take (Δ - H.length)).map (· - 1) ++
          L.drop (Δ - H.length)).mergeSort geB) := by
  let low :=
    (L.take (Δ - H.length)).map (· - 1) ++
      L.drop (Δ - H.length)
  have hdec :
      hhDec (Δ :: rest) = H.map (· - 1) ++ low := by
    exact hhDec_split_of_high_le Δ rest H L hrest hm
  have hcross :
      ∀ x ∈ H.map (· - 1), ∀ y ∈ low, x ≥ y := by
    intro x hx y hy
    simp only [List.mem_map] at hx
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    have hxk : k ≤ x₀ - 1 := by
      have := hH x₀ hx₀
      omega
    dsimp [low] at hy
    simp only [List.mem_append, List.mem_map] at hy
    rcases hy with ⟨y₀, hy₀, rfl⟩ | hy
    · have hyL : y₀ ∈ L := List.mem_of_mem_take hy₀
      have := hL y₀ hyL
      omega
    · have hyL : y ∈ L := List.mem_of_mem_drop hy
      exact (hL y hyL).trans hxk
  unfold hhSort
  exact sort_eq_high_append (hhDec (Δ :: rest))
    (H.map (· - 1)) low hdec (pred_pairwise H hsortH) hcross

lemma map_min_hhSort_eq_of_take_high (Δ k : ℕ) (rest : List ℕ)
    (hhigh : ∀ x ∈ rest.take Δ, k < x) :
    ((hhSort (Δ :: rest)).map (fun x => min k x)).sum =
      (rest.map (fun x => min k x)).sum := by
  have hperm := (hhSort_perm (Δ :: rest)).map (fun x => min k x)
  rw [hperm.sum_eq]
  simp only [hhDec, List.map_append, List.sum_append, List.map_map]
  have htake :
      ((rest.take Δ).map ((fun x => min k x) ∘ (· - 1))).sum =
        ((rest.take Δ).map (fun x => min k x)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro x hx
    have := hhigh x hx
    simp only [Function.comp_apply]
    omega
  rw [htake]
  rw [← List.sum_append, ← List.map_append, List.take_append_drop]

lemma map_min_sum_split (k : ℕ) (rest H L : List ℕ)
    (hrest : rest = H ++ L)
    (hH : ∀ x ∈ H, k < x)
    (hL : ∀ x ∈ L, x ≤ k) :
    (rest.map (fun x => min k x)).sum =
      k * H.length + L.sum := by
  rw [hrest, List.map_append, List.sum_append]
  have hmapH : (H.map (fun x => min k x)).sum = k * H.length := by
    calc
      (H.map (fun x => min k x)).sum =
          (H.map (fun _ => k)).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro x hx
            have := hH x hx
            omega
      _ = k * H.length := by simp [Nat.mul_comm]
  have hmapL : (L.map (fun x => min k x)).sum = L.sum := by
    conv_rhs => rw [← List.map_id L]
    apply congrArg List.sum
    apply List.map_congr_left
    intro x hx
    have := hL x hx
    simp only [id_eq]
    omega
  rw [hmapH, hmapL]

lemma hhSort_entry_le_head (Δ : ℕ) (rest : List ℕ)
    (hsort : (Δ :: rest).Pairwise (· ≥ ·)) :
    ∀ x ∈ hhSort (Δ :: rest), x ≤ Δ := by
  intro x hx
  have hxdec : x ∈ hhDec (Δ :: rest) :=
    (hhSort_perm (Δ :: rest)).mem_iff.mp hx
  simp only [hhDec, List.mem_append, List.mem_map] at hxdec
  rcases hxdec with ⟨y, hy, rfl⟩ | hx
  · have hyrest : y ∈ rest := List.mem_of_mem_take hy
    have hyΔ := (List.pairwise_cons.mp hsort).1 y hyrest
    omega
  · have hxrest : x ∈ rest := List.mem_of_mem_drop hx
    exact (List.pairwise_cons.mp hsort).1 x hxrest

lemma hhSort_take_sum_le (Δ k : ℕ) (rest : List ℕ)
    (hsort : (Δ :: rest).Pairwise (· ≥ ·))
    (hkle : k ≤ (hhSort (Δ :: rest)).length) :
    ((hhSort (Δ :: rest)).take k).sum ≤ k * Δ := by
  have hbound :
      ∀ x ∈ (hhSort (Δ :: rest)).take k, x ≤ Δ := by
    intro x hx
    exact hhSort_entry_le_head Δ rest hsort x (List.mem_of_mem_take hx)
  have hsum :=
    List.sum_le_card_nsmul ((hhSort (Δ :: rest)).take k) Δ hbound
  have hlen :
      ((hhSort (Δ :: rest)).take k).length = k := by
    simp [List.length_take, hkle]
  simpa [hlen] using hsum

lemma take_ge_of_sorted_decomp (l a tail : List ℕ) (d k : ℕ)
    (hsort : l.Pairwise (· ≥ ·))
    (hl : l = a ++ d :: tail)
    (hlen : a.length = k - 1)
    (hk : 1 ≤ k)
    (hkd : k ≤ d) :
    ∀ x ∈ l.take k, k ≤ x := by
  have hk_eq : k = a.length + 1 := by omega
  subst k
  have hsort' : (a ++ d :: tail).Pairwise (· ≥ ·) := by
    simpa [hl] using hsort
  have hcross :
      ∀ x ∈ a, ∀ y ∈ d :: tail, x ≥ y :=
    (List.pairwise_append.mp hsort').2.2
  have htake : (a ++ d :: tail).take (a.length + 1) = a ++ [d] := by
    rw [List.take_append]
    simp
  rw [hl, htake]
  intro x hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact hkd.trans (hcross x hx d (by simp))
  · exact hkd

lemma eg_of_take_add_le_map_min (l : List ℕ) (k : ℕ)
    (hk : 1 ≤ k)
    (hkle : k ≤ l.length)
    (hprefix : ∀ x ∈ l.take k, k ≤ x)
    (hcap :
      (l.take k).sum + k ≤
        (l.map (fun x => min k x)).sum) :
    EGineq l k := by
  have htake_len : (l.take k).length = k := by
    simp [List.length_take, hkle]
  have hprefix_cap :
      ((l.take k).map (fun x => min k x)).sum = k * k := by
    calc
      ((l.take k).map (fun x => min k x)).sum =
          ((l.take k).map (fun _ => k)).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro x hx
            have := hprefix x hx
            omega
      _ = k * k := by
        rw [List.map_const', htake_len, List.sum_const_nat]
  have hmap_split :
      (l.map (fun x => min k x)).sum =
        k * k + ((l.drop k).map (fun x => min k x)).sum := by
    calc
      (l.map (fun x => min k x)).sum =
          ((l.take k ++ l.drop k).map (fun x => min k x)).sum := by
            rw [List.take_append_drop]
      _ = k * k + ((l.drop k).map (fun x => min k x)).sum := by
            rw [List.map_append, List.sum_append, hprefix_cap]
  rw [hmap_split] at hcap
  unfold EGineq
  have hkk : k * k = k * (k - 1) + k := by
    calc
      k * k = k * ((k - 1) + 1) := by
        congr 1
        omega
      _ = k * (k - 1) + k := by rw [Nat.mul_add, Nat.mul_one]
  omega

lemma hhSort_take_sum_add_eq_high_take_sum
    (Δ k : ℕ) (rest H L : List ℕ)
    (hrest : rest = H ++ L)
    (hm : H.length ≤ Δ)
    (hk : k ≤ H.length)
    (hsortH : H.Pairwise (· ≥ ·))
    (hH : ∀ x ∈ H, k < x)
    (hL : ∀ x ∈ L, x ≤ k) :
    ((hhSort (Δ :: rest)).take k).sum + k =
      (H.take k).sum := by
  have hsplit :=
    hhSort_split_of_high_le Δ k rest H L hrest hm hsortH hH hL
  have htake :
      (hhSort (Δ :: rest)).take k =
        (H.take k).map (· - 1) := by
    rw [hsplit, List.take_append_of_le_length]
    · rw [← List.map_take]
    · simpa using hk
  rw [htake]
  have hpos : ∀ x ∈ H.take k, 1 ≤ x := by
    intro x hx
    have hxH : x ∈ H := List.mem_of_mem_take hx
    have := hH x hxH
    omega
  have hpred := map_pred_sum (H.take k) hpos
  have hlen : (H.take k).length = k := by
    simp [List.length_take, hk]
  simpa [hlen] using hpred

lemma hhSort_take_sum_high_short
    (Δ k : ℕ) (rest H L : List ℕ)
    (hrest : rest = H ++ L)
    (hm : H.length ≤ Δ)
    (hmk : H.length < k)
    (hkle : k ≤ (hhSort (Δ :: rest)).length)
    (hsortH : H.Pairwise (· ≥ ·))
    (hH : ∀ x ∈ H, k < x)
    (hL : ∀ x ∈ L, x ≤ k)
    (hprefix :
      ∀ x ∈ (hhSort (Δ :: rest)).take k, k ≤ x) :
    ((hhSort (Δ :: rest)).take k).sum + H.length =
      H.sum + k * (k - H.length) := by
  let low :=
    (L.take (Δ - H.length)).map (· - 1) ++
      L.drop (Δ - H.length)
  let slow := low.mergeSort geB
  have hsplit :
      hhSort (Δ :: rest) = H.map (· - 1) ++ slow := by
    exact hhSort_split_of_high_le Δ k rest H L hrest hm hsortH hH hL
  have hlow : ∀ y ∈ low, y ≤ k := by
    intro y hy
    dsimp [low] at hy
    simp only [List.mem_append, List.mem_map] at hy
    rcases hy with ⟨z, hz, rfl⟩ | hy
    · have hzL : z ∈ L := List.mem_of_mem_take hz
      have := hL z hzL
      omega
    · exact hL y (List.mem_of_mem_drop hy)
  have hslow : ∀ y ∈ slow, y ≤ k := by
    intro y hy
    apply hlow y
    exact (List.mergeSort_perm low geB).mem_iff.mp hy
  have htake :
      (hhSort (Δ :: rest)).take k =
        H.map (· - 1) ++ slow.take (k - H.length) := by
    rw [hsplit, List.take_append]
    have htakeH : (H.map (· - 1)).take k = H.map (· - 1) := by
      apply (List.take_eq_self_iff _).mpr
      simpa using Nat.le_of_lt hmk
    rw [htakeH]
    simp only [List.length_map]
  have htail_len :
      (slow.take (k - H.length)).length = k - H.length := by
    have hlenSplit :
        (hhSort (Δ :: rest)).length = H.length + slow.length := by
      rw [hsplit]
      simp
    have : k - H.length ≤ slow.length := by omega
    simp [List.length_take, this]
  have htail_eq :
      slow.take (k - H.length) =
        (slow.take (k - H.length)).map (fun _ => k) := by
    conv_lhs => rw [← List.map_id (slow.take (k - H.length))]
    apply List.map_congr_left
    intro y hy
    have hyTake : y ∈ (hhSort (Δ :: rest)).take k := by
      rw [htake]
      exact List.mem_append_right _ hy
    have hyge := hprefix y hyTake
    have hyle := hslow y (List.mem_of_mem_take hy)
    simp only [id_eq]
    omega
  rw [htake, List.sum_append, htail_eq]
  have htail_sum :
      ((slow.take (k - H.length)).map (fun _ => k)).sum =
        k * (k - H.length) := by
    rw [List.map_const', htail_len, List.sum_const_nat, Nat.mul_comm]
  rw [htail_sum]
  have hposH : ∀ x ∈ H, 1 ≤ x := by
    intro x hx
    have := hH x hx
    omega
  have hpredH := map_pred_sum H hposH
  omega

lemma count_mul_le_sum (k : ℕ) : ∀ l : List ℕ, k * l.count k ≤ l.sum := by
  intro l
  induction l with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : x = k
      · subst x
        simp only [List.count_cons, beq_self_eq_true, if_true,
          List.sum_cons, Nat.mul_add, Nat.mul_one]
        omega
      · simp only [List.count_cons, beq_eq_false_iff_ne.mpr hx,
          List.sum_cons]
        exact ih.trans (Nat.le_add_left _ _)

lemma low_sum_resource
    (Δ k : ℕ) (rest H L : List ℕ)
    (hrest : rest = H ++ L)
    (hm : H.length ≤ Δ)
    (hmk : H.length < k)
    (hk : 1 ≤ k)
    (hΔlen : Δ ≤ rest.length)
    (hsortH : H.Pairwise (· ≥ ·))
    (hsortL : L.Pairwise (· ≥ ·))
    (hH : ∀ x ∈ H, k < x)
    (hL : ∀ x ∈ L, x ≤ k)
    (hprefix :
      ∀ x ∈ (hhSort (Δ :: rest)).take k, k ≤ x)
    (hkle : k ≤ (hhSort (Δ :: rest)).length) :
    k * ((Δ - H.length) + (k - H.length)) ≤ L.sum := by
  let a := Δ - H.length
  let t := k - H.length
  let low := (L.take a).map (· - 1) ++ L.drop a
  let slow := low.mergeSort geB
  have htpos : 1 ≤ t := by dsimp [t]; omega
  have haL : a ≤ L.length := by
    have hlen : rest.length = H.length + L.length := by simp [hrest]
    dsimp [a]
    omega
  have hsplit :
      hhSort (Δ :: rest) = H.map (· - 1) ++ slow := by
    exact hhSort_split_of_high_le Δ k rest H L hrest hm hsortH hH hL
  have htake :
      (hhSort (Δ :: rest)).take k =
        H.map (· - 1) ++ slow.take t := by
    rw [hsplit, List.take_append]
    have htakeH : (H.map (· - 1)).take k = H.map (· - 1) := by
      apply (List.take_eq_self_iff _).mpr
      simpa using Nat.le_of_lt hmk
    rw [htakeH]
    simp only [List.length_map]
    rfl
  have hslow_le : ∀ y ∈ slow, y ≤ k := by
    intro y hy
    have hylow : y ∈ low :=
      (List.mergeSort_perm low geB).mem_iff.mp hy
    dsimp [low] at hylow
    simp only [List.mem_append, List.mem_map] at hylow
    rcases hylow with ⟨z, hz, rfl⟩ | hy
    · have hzL : z ∈ L := List.mem_of_mem_take hz
      have := hL z hzL
      omega
    · exact hL y (List.mem_of_mem_drop hy)
  have htail_len : (slow.take t).length = t := by
    have hlenSplit :
        (hhSort (Δ :: rest)).length = H.length + slow.length := by
      rw [hsplit]
      simp
    have htlen : t ≤ slow.length := by dsimp [t]; omega
    simp [List.length_take, htlen]
  have htail_all : ∀ y ∈ slow.take t, y = k := by
    intro y hy
    have hyTake : y ∈ (hhSort (Δ :: rest)).take k := by
      rw [htake]
      exact List.mem_append_right _ hy
    have hyge := hprefix y hyTake
    have hyle := hslow_le y (List.mem_of_mem_take hy)
    omega
  have hcount_tail : (slow.take t).count k = t := by
    rw [List.count_eq_length.mpr]
    · exact htail_len
    · intro y hy
      exact (htail_all y hy).symm
  have hcount_slow : t ≤ slow.count k := by
    rw [← hcount_tail]
    exact (List.take_prefix t slow).sublist.count_le k
  have hcount_low : slow.count k = low.count k :=
    (List.mergeSort_perm low geB).count k
  have hnot_take : k ∉ (L.take a).map (· - 1) := by
    intro hmem
    simp only [List.mem_map] at hmem
    obtain ⟨z, hz, hzk⟩ := hmem
    have hzL : z ∈ L := List.mem_of_mem_take hz
    have := hL z hzL
    omega
  have hcount_low_drop : low.count k = (L.drop a).count k := by
    dsimp [low]
    rw [List.count_append, List.count_eq_zero.mpr hnot_take, zero_add]
  have htcount : t ≤ (L.drop a).count k := by
    rw [hcount_low, hcount_low_drop] at hcount_slow
    exact hcount_slow
  have hkdrop : k ∈ L.drop a := by
    apply List.count_pos_iff.mp
    omega
  have htake_all : ∀ x ∈ L.take a, x = k := by
    intro x hx
    have hxge : x ≥ k :=
      hsortL.rel_of_mem_take_of_mem_drop hx hkdrop
    have hxle := hL x (List.mem_of_mem_take hx)
    omega
  have htake_len : (L.take a).length = a := by
    simp [List.length_take, haL]
  have htake_sum : (L.take a).sum = k * a := by
    have heq : L.take a = (L.take a).map (fun _ => k) := by
      conv_lhs => rw [← List.map_id (L.take a)]
      apply List.map_congr_left
      intro x hx
      simp only [id_eq]
      exact htake_all x hx
    rw [heq, List.map_const', htake_len, List.sum_const_nat,
      Nat.mul_comm]
  have hdrop_sum : k * t ≤ (L.drop a).sum := by
    exact (Nat.mul_le_mul_left k htcount).trans
      (count_mul_le_sum k (L.drop a))
  have hsplit_sum := List.sum_take_add_sum_drop L a
  calc
    k * (a + t) = k * a + k * t := by rw [Nat.mul_add]
    _ ≤ (L.take a).sum + (L.drop a).sum := by
      rw [htake_sum]
      exact Nat.add_le_add_left hdrop_sum _
    _ = L.sum := hsplit_sum

lemma eg_high_bound
    (Δ k : ℕ) (rest H L : List ℕ)
    (hrest : rest = H ++ L)
    (hkH : k ≤ H.length)
    (hH : ∀ x ∈ H, k < x)
    (hL : ∀ x ∈ L, x ≤ k)
    (hEG : EGineq (Δ :: rest) (k + 1)) :
    Δ + (H.take k).sum ≤ (k + 1) * H.length + L.sum := by
  have htakeRest : rest.take k = H.take k := by
    rw [hrest, List.take_append_of_le_length hkH]
  have hdropRest : rest.drop k = H.drop k ++ L := by
    rw [hrest, List.drop_append_of_le_length hkH]
  have hmapH :
      ((H.drop k).map (fun x => min (k + 1) x)).sum =
        (k + 1) * (H.length - k) := by
    calc
      ((H.drop k).map (fun x => min (k + 1) x)).sum =
          ((H.drop k).map (fun _ => k + 1)).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro x hx
            have hxH : x ∈ H := List.mem_of_mem_drop hx
            have := hH x hxH
            omega
      _ = (k + 1) * (H.length - k) := by
            rw [List.map_const', List.length_drop,
              List.sum_const_nat, Nat.mul_comm]
  have hmapL :
      (L.map (fun x => min (k + 1) x)).sum = L.sum := by
    conv_rhs => rw [← List.map_id L]
    apply congrArg List.sum
    apply List.map_congr_left
    intro x hx
    have := hL x hx
    simp only [id_eq]
    omega
  unfold EGineq at hEG
  simp only [List.take_succ_cons, List.drop_succ_cons,
    List.sum_cons] at hEG
  rw [htakeRest, hdropRest, List.map_append, List.sum_append,
    hmapH, hmapL] at hEG
  have hmul :
      (k + 1) * k + (k + 1) * (H.length - k) =
        (k + 1) * H.length := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have hpred : k + 1 - 1 = k := by omega
  rw [hpred] at hEG
  calc
    Δ + (H.take k).sum ≤
        (k + 1) * k + ((k + 1) * (H.length - k) + L.sum) := hEG
    _ = (k + 1) * H.length + L.sum := by
      rw [← Nat.add_assoc, hmul]

/-- Evenness is necessary: without it, `[1,1,1]` reduces to `[1,0]`. -/
lemma eg_hhSort (Δ : ℕ) (rest : List ℕ)
    (hsort : (Δ :: rest).Pairwise (· ≥ ·))
    (hΔlen : Δ ≤ rest.length)
    (hpos : ∀ x ∈ rest.take Δ, 1 ≤ x)
    (heven : Even (Δ :: rest).sum)
    (hEG : ∀ k, 1 ≤ k → k ≤ (Δ :: rest).length →
      EGineq (Δ :: rest) k) :
    ∀ k, 1 ≤ k → k ≤ (hhSort (Δ :: rest)).length →
      EGineq (hhSort (Δ :: rest)) k := by
  let e := hhSort (Δ :: rest)
  have hsortE : e.Pairwise (· ≥ ·) := hhSort_sorted _
  apply eg_all_of_critical e
  intro a tail d k heq hlen hkd
  by_cases hk0 : k = 0
  · subst k
    simp [EGineq]
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  have hkle : k ≤ e.length := by
    rw [heq]
    simp only [List.length_append, List.length_cons]
    omega
  have hprefix : ∀ x ∈ e.take k, k ≤ x :=
    take_ge_of_sorted_decomp e a tail d k hsortE heq hlen hk hkd
  apply eg_of_take_add_le_map_min e k hk hkle hprefix
  change
    ((hhSort (Δ :: rest)).take k).sum + k ≤
      ((hhSort (Δ :: rest)).map (fun x => min k x)).sum
  have hdmem : d ∈ e := by
    rw [heq]
    simp
  have hdΔ : d ≤ Δ := by
    exact hhSort_entry_le_head Δ rest hsort d hdmem
  have hkΔ : k ≤ Δ := hkd.trans hdΔ
  have hsortRest : rest.Pairwise (· ≥ ·) :=
    (List.pairwise_cons.mp hsort).2
  obtain ⟨H, L, hrest, hH, hL⟩ :=
    exists_gt_le_split k rest hsortRest
  have hsortHL : (H ++ L).Pairwise (· ≥ ·) := by
    simpa [hrest] using hsortRest
  have hsortH : H.Pairwise (· ≥ ·) :=
    (List.pairwise_append.mp hsortHL).1
  have hsortL : L.Pairwise (· ≥ ·) :=
    (List.pairwise_append.mp hsortHL).2.1
  by_cases hmΔ : H.length ≤ Δ
  · have hcap :=
      map_min_sum_of_high_le Δ k rest H L hrest hmΔ hH hL
        hΔlen hpos
    by_cases hkH : k ≤ H.length
    · have htake :=
        hhSort_take_sum_add_eq_high_take_sum
          Δ k rest H L hrest hmΔ hkH hsortH hH hL
      have hEGkp :
          EGineq (Δ :: rest) (k + 1) :=
        hEG (k + 1) (by omega) (by
          rw [hhSort_length] at hkle
          simp only [List.length_cons]
          omega)
      have hbound :=
        eg_high_bound Δ k rest H L hrest hkH hH hL hEGkp
      have hsub : (Δ - H.length) + H.length = Δ :=
        Nat.sub_add_cancel hmΔ
      have hmul : (k + 1) * H.length =
          k * H.length + H.length := by
        rw [Nat.add_mul, Nat.one_mul]
      omega
    · have hHk : H.length < k := by omega
      have htake :=
        hhSort_take_sum_high_short
          Δ k rest H L hrest hmΔ hHk hkle hsortH hH hL hprefix
      have hresource :=
        low_sum_resource Δ k rest H L hrest hmΔ hHk hk hΔlen
          hsortH hsortL hH hL hprefix hkle
      have hHbound : H.sum ≤ H.length * Δ := by
        have hAll : ∀ x ∈ H, x ≤ Δ := by
          intro x hx
          have hxrest : x ∈ rest := by
            rw [hrest]
            exact List.mem_append_left L hx
          exact (List.pairwise_cons.mp hsort).1 x hxrest
        exact List.sum_le_card_nsmul H Δ hAll
      have haeq : (Δ - H.length) + H.length = Δ :=
        Nat.sub_add_cancel hmΔ
      have hteq : (k - H.length) + H.length = k :=
        Nat.sub_add_cancel (Nat.le_of_lt hHk)
      by_cases hk1 : k = 1
      · subst k
        have hH0 : H.length = 0 := by omega
        have hHnil : H = [] := List.eq_nil_of_length_eq_zero hH0
        subst H
        simp only [List.length_nil, List.sum_nil, Nat.sub_zero,
          Nat.mul_zero, zero_add, Nat.one_mul] at htake hresource hcap
        simp only [List.nil_append] at hrest
        obtain ⟨q, hq⟩ := heven
        simp only [List.sum_cons, hrest] at hq
        have hcapEven : Even
            (((hhSort (Δ :: rest)).map (fun x => min 1 x)).sum) := by
          have hΔq : Δ ≤ q := by omega
          refine ⟨q - Δ, ?_⟩
          omega
        obtain ⟨r, hr⟩ := hcapEven
        omega
      · have hk2 : 2 ≤ k := by omega
        have ht1 : 1 ≤ k - H.length := by omega
        have ht_le : k - H.length ≤ k := Nat.sub_le _ _
        have hnonneg :
            2 * (k - H.length) ≤
              Δ * ((k - H.length) - 1) + k := by
          calc
            2 * (k - H.length) ≤
                k * (k - H.length) :=
              Nat.mul_le_mul_right (k - H.length) hk2
            _ = k * ((k - H.length) - 1) + k := by
              calc
                k * (k - H.length) =
                    k * (((k - H.length) - 1) + 1) := by
                      congr 1
                      omega
                _ = k * ((k - H.length) - 1) + k := by
                      rw [Nat.mul_add, Nat.mul_one]
            _ ≤ Δ * ((k - H.length) - 1) + k := by
              exact Nat.add_le_add_right
                (Nat.mul_le_mul_right
                  ((k - H.length) - 1) hkΔ) k
        nlinarith
  · have hΔm : Δ < H.length := by omega
    have htakeHigh : ∀ x ∈ rest.take Δ, k < x := by
      intro x hx
      rw [hrest, List.take_append_of_le_length
        (Nat.le_of_lt hΔm)] at hx
      exact hH x (List.mem_of_mem_take hx)
    have hcapUnchanged :=
      map_min_hhSort_eq_of_take_high Δ k rest htakeHigh
    have hcapSplit := map_min_sum_split k rest H L hrest hH hL
    have htakeBound := hhSort_take_sum_le Δ k rest hsort hkle
    have hΔsucc : Δ + 1 ≤ H.length := by omega
    have hmul : k * Δ + k = k * (Δ + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    have hmulLe : k * (Δ + 1) ≤ k * H.length :=
      Nat.mul_le_mul_left k hΔsucc
    rw [hcapUnchanged, hcapSplit]
    omega

lemma eg_suff_aux : ∀ (N : ℕ) (l : List ℕ),
    l.sum = N → l.Pairwise (· ≥ ·) → Even l.sum →
    (∀ k, 1 ≤ k → k ≤ l.length → EGineq l k) →
    Graphic (l : Multiset ℕ) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro l hN hsort heven hEG
    match l, hN, hsort, heven, hEG with
    | [], _, _, _, _ =>
        simpa using graphic_replicate_zero 0
    | Δ :: rest, hN, hsort, heven, hEG =>
      by_cases hΔ0 : Δ = 0
      · subst hΔ0
        have hz : ∀ x ∈ (0 :: rest : List ℕ), x = 0 := by
          intro x hx
          rcases List.mem_cons.mp hx with h | h
          · exact h
          · have := (List.pairwise_cons.mp hsort).1 x h
            omega
        have hrep : ((0 :: rest : List ℕ) : Multiset ℕ) =
            Multiset.replicate (0 :: rest : List ℕ).length 0 := by
          rw [← Multiset.coe_replicate]
          congr 1
          exact (List.eq_replicate_iff.mpr ⟨rfl, hz⟩)
        rw [hrep]
        exact graphic_replicate_zero _
      · have hΔ1 : 1 ≤ Δ := Nat.one_le_iff_ne_zero.mpr hΔ0
        have hEG1 : EGineq (Δ :: rest) 1 :=
          hEG 1 (le_refl 1) (by simp)
        have hb := head_le_of_EG1 Δ rest hEG1
        obtain ⟨hΔlen, hpos⟩ := take_pos Δ rest hsort hb
        have hsum := hhSort_sum Δ rest hΔlen hpos
        simp only [List.sum_cons] at hN hsum
        have hlt : (hhSort (Δ :: rest)).sum < N := by omega
        have hl'even : Even (hhSort (Δ :: rest)).sum := by
          obtain ⟨m, hm⟩ := heven
          refine ⟨m - Δ, ?_⟩
          simp only [List.sum_cons] at hm
          omega
        have hl'EG :=
          eg_hhSort Δ rest hsort hΔlen hpos heven hEG
        have hgr := ih (hhSort (Δ :: rest)).sum hlt
          (hhSort (Δ :: rest)) rfl (hhSort_sorted _) hl'even hl'EG
        exact graphic_reconstruct Δ rest hΔlen hpos hgr

theorem erdos_gallai_sufficiency (l : List ℕ)
    (hsort : l.Pairwise (· ≥ ·))
    (heven : Even l.sum)
    (hEG : ∀ k, 1 ≤ k → k ≤ l.length → EGineq l k) :
    Graphic (l : Multiset ℕ) :=
  eg_suff_aux l.sum l rfl hsort heven hEG

def FinsetEG {α : Type*} [DecidableEq α]
    (E : Finset α) (d : α → ℕ) : Prop :=
  Even (∑ i ∈ E, d i) ∧
    ∀ A : Finset α, A ⊆ E →
      ∑ i ∈ A, d i ≤
        #A * (#A - 1) + ∑ i ∈ E \ A, min #A (d i)

theorem graphic_of_finsetEG {α : Type*} [DecidableEq α]
    (E : Finset α) (d : α → ℕ) (hcond : FinsetEG E d) :
    Graphic (E.val.map d) := by
  classical
  let s : Multiset ℕ := E.val.map d
  let l : List ℕ := s.sort (· ≥ ·)
  have hlcoe : (l : Multiset ℕ) = s := by
    exact Multiset.sort_eq s (· ≥ ·)
  have hlsort : l.Pairwise (· ≥ ·) := by
    exact Multiset.pairwise_sort s (· ≥ ·)
  have hlsum : l.sum = ∑ i ∈ E, d i := by
    change (l : Multiset ℕ).sum = _
    rw [hlcoe]
    rfl
  have hleven : Even l.sum := by
    rw [hlsum]
    exact hcond.1
  change Graphic s
  rw [← hlcoe]
  apply erdos_gallai_sufficiency l hlsort hleven
  intro k hk hkle
  let c : Multiset ℕ := (l.take k : List ℕ)
  have hcle : c ≤ E.val.map d := by
    have htakele : ((l.take k : List ℕ) : Multiset ℕ) ≤
        (l : Multiset ℕ) := by
      exact Multiset.coe_le.mpr
        (List.take_prefix k l).sublist.subperm
    simpa [c, hlcoe, s] using htakele
  obtain ⟨s', hs'le, hs'map⟩ :=
    exists_submultiset_map_u (α := α) (β := ℕ) d E.val c hcle
  have hs'nodup : s'.Nodup :=
    Multiset.nodup_of_le hs'le E.nodup
  let A : Finset α := ⟨s', hs'nodup⟩
  have hAE : A ⊆ E := by
    intro x hx
    exact Multiset.mem_of_le hs'le hx
  have hAcard : #A = k := by
    change s'.card = k
    calc
      s'.card = (s'.map d).card := by
        rw [Multiset.card_map]
      _ = c.card := congrArg Multiset.card hs'map
      _ = (l.take k).length := by rfl
      _ = k := by simp [List.length_take, hkle]
  have hAsum : (∑ i ∈ A, d i) = (l.take k).sum := by
    change (A.val.map d).sum = (l.take k).sum
    change (s'.map d).sum = (l.take k).sum
    rw [hs'map]
    rfl
  have hEAdecomp : A.val + (E \ A).val = E.val := by
    rw [Finset.sdiff_val]
    exact add_tsub_cancel_of_le hs'le
  have hmapdecomp :
      A.val.map d + (E \ A).val.map d = E.val.map d := by
    rw [← Multiset.map_add, hEAdecomp]
  have hlistdecomp :
      c + ((l.drop k : List ℕ) : Multiset ℕ) = E.val.map d := by
    change
      ((l.take k : List ℕ) : Multiset ℕ) +
        ((l.drop k : List ℕ) : Multiset ℕ) = E.val.map d
    rw [Multiset.coe_add, List.take_append_drop, hlcoe]
  have hcompmap :
      (E \ A).val.map d = ((l.drop k : List ℕ) : Multiset ℕ) := by
    apply add_left_cancel (a := c)
    calc
      c + (E \ A).val.map d =
          A.val.map d + (E \ A).val.map d := by rw [hs'map]
      _ = E.val.map d := hmapdecomp
      _ = c + ((l.drop k : List ℕ) : Multiset ℕ) :=
        hlistdecomp.symm
  have hcompsum :
      (∑ i ∈ E \ A, min k (d i)) =
        ((l.drop k).map (fun x => min k x)).sum := by
    change
      ((E \ A).val.map (fun i => min k (d i))).sum =
        ((l.drop k).map (fun x => min k x)).sum
    have hfun :
        (fun i => min k (d i)) = (fun x => min k x) ∘ d := rfl
    rw [hfun, ← Multiset.map_map, hcompmap, Multiset.map_coe]
    exact Multiset.sum_coe _
  have hineq := hcond.2 A hAE
  rw [hAcard, hAsum, hcompsum] at hineq
  exact hineq

end ErdosGallai

open scoped symmDiff

open Finset

namespace Imbalance

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def LocallyIrregular : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → G.degree u ≠ G.degree v

def edgeImbalance : Sym2 V → ℕ :=
  Sym2.lift ⟨fun u v ↦ Nat.dist (G.degree u) (G.degree v),
    fun u v ↦ Nat.dist_comm (G.degree u) (G.degree v)⟩

omit [DecidableEq V] in
@[simp]
theorem edgeImbalance_mk (u v : V) :
    edgeImbalance G s(u, v) = Nat.dist (G.degree u) (G.degree v) :=
  rfl

omit [DecidableEq V] in
theorem edgeImbalance_pos (hLI : LocallyIrregular G) {e : Sym2 V}
    (he : e ∈ G.edgeFinset) : 0 < edgeImbalance G e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      rw [edgeImbalance_mk]
      exact Nat.dist_pos_of_ne (hLI (by simpa using he))

omit [DecidableEq V] in
theorem one_le_edgeImbalance (hLI : LocallyIrregular G) {e : Sym2 V}
    (he : e ∈ G.edgeFinset) : 1 ≤ edgeImbalance G e :=
  edgeImbalance_pos G hLI he

omit [DecidableEq V] in
theorem edgeImbalance_le_maxDegree_sub_one (hLI : LocallyIrregular G) {e : Sym2 V}
    (he : e ∈ G.edgeFinset) : edgeImbalance G e ≤ G.maxDegree - 1 := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : G.Adj u v := by simpa using he
      have hu_pos : 0 < G.degree u := huv.degree_pos_left
      have hv_pos : 0 < G.degree v := huv.degree_pos_right
      have hu_max := G.degree_le_maxDegree u
      have hv_max := G.degree_le_maxDegree v
      have hne := hLI huv
      rw [edgeImbalance_mk, Nat.dist_eq_max_sub_min]
      omega

def selectedNeighbors (A : Finset (Sym2 V)) (x : V) : Finset V :=
  (G.neighborFinset x).filter fun z ↦ s(x, z) ∈ A

def unselectedNeighbors (A : Finset (Sym2 V)) (x : V) : Finset V :=
  (G.neighborFinset x).filter fun z ↦ s(x, z) ∉ A

theorem card_selectedNeighbors_le (A : Finset (Sym2 V)) (x : V) :
    #(selectedNeighbors G A x) ≤ #A := by
  classical
  let f : V → Sym2 V := fun z ↦ s(x, z)
  have hinj : Set.InjOn f ↑(selectedNeighbors G A x) := by
    intro z _ w _ h
    exact Sym2.congr_right.mp h
  have hcard :
      #((selectedNeighbors G A x).image f) = #(selectedNeighbors G A x) :=
    Finset.card_image_iff.mpr hinj
  have hsub : (selectedNeighbors G A x).image f ⊆ A := by
    intro e he
    simp only [Finset.mem_image] at he
    obtain ⟨z, hz, rfl⟩ := he
    exact (Finset.mem_filter.mp hz).2
  rw [← hcard]
  exact Finset.card_le_card hsub

theorem card_selected_add_card_unselected (A : Finset (Sym2 V)) (x : V) :
    #(selectedNeighbors G A x) + #(unselectedNeighbors G A x) = G.degree x := by
  classical
  simpa [selectedNeighbors, unselectedNeighbors] using
    (Finset.card_filter_add_card_filter_not
      (s := G.neighborFinset x) (p := fun z ↦ s(x, z) ∈ A))

theorem card_unselectedNeighbors (A : Finset (Sym2 V)) (x : V) :
    #(unselectedNeighbors G A x) = G.degree x - #(selectedNeighbors G A x) := by
  have h := card_selected_add_card_unselected G A x
  omega

def escapeNeighbors (R : Finset V) (x z : V) : Finset V :=
  G.neighborFinset z \ insert x R

theorem card_escapeNeighbors_ge (R : Finset V) (x z : V)
    (hzR : z ∈ R) (hxR : x ∉ R) :
    G.degree z - #R ≤ #(escapeNeighbors G R x z) := by
  classical
  let inside := G.neighborFinset z ∩ insert x R
  have hinside : inside ⊆ insert x (R.erase z) := by
    intro w hw
    have hwn : w ∈ G.neighborFinset z := (Finset.mem_inter.mp hw).1
    have hwS : w ∈ insert x R := (Finset.mem_inter.mp hw).2
    have hwz : w ≠ z := by
      intro hwz
      subst w
      exact G.notMem_neighborFinset_self z hwn
    rcases Finset.mem_insert.mp hwS with rfl | hwR
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwz, hwR⟩)
  have hcard_inside : #inside ≤ #R := by
    have hRpos : 0 < #R := Finset.card_pos.mpr ⟨z, hzR⟩
    calc
      #inside ≤ #(insert x (R.erase z)) := Finset.card_le_card hinside
      _ = #R := by
        rw [Finset.card_insert_of_notMem, Finset.card_erase_of_mem hzR]
        · omega
        · exact fun hx ↦ hxR (Finset.mem_of_mem_erase hx)
  have hdegree : #(G.neighborFinset z) = G.degree z :=
    G.card_neighborFinset_eq_degree z
  have hcard_escape :
      #(escapeNeighbors G R x z) =
        G.degree z - #(insert x R ∩ G.neighborFinset z) := by
    simp only [escapeNeighbors, Finset.card_sdiff, hdegree]
  have hinter :
      #(insert x R ∩ G.neighborFinset z) = #inside := by
    simp only [inside, Finset.inter_comm]
  rw [hcard_escape, hinter]
  omega

def escapePairs (R : Finset V) (x : V) : Finset (Σ _z : V, V) :=
  R.sigma fun z ↦ escapeNeighbors G R x z

def escapeEdge : (Σ _z : V, V) → Sym2 V :=
  fun p ↦ s(p.1, p.2)

def escapeEdges (R : Finset V) (x : V) : Finset (Sym2 V) :=
  (escapePairs G R x).image escapeEdge

theorem escapeEdge_injOn (R : Finset V) (x : V) :
    Set.InjOn (escapeEdge (V := V))
      (↑(escapePairs G R x) : Set (Σ _z : V, V)) := by
  classical
  rintro ⟨z, w⟩ hzw ⟨z', w'⟩ hz'w' heq
  have hzR : z ∈ R := (Finset.mem_sigma.mp hzw).1
  have hwout : w ∉ insert x R :=
    (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hzw).2).2
  have hz'R : z' ∈ R := (Finset.mem_sigma.mp hz'w').1
  have hw'out : w' ∉ insert x R :=
    (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hz'w').2).2
  change s(z, w) = s(z', w') at heq
  rcases Sym2.eq_iff.mp heq with hsame | hswap
  · rcases hsame with ⟨rfl, rfl⟩
    rfl
  · rcases hswap with ⟨hzw', hwz'⟩
    exfalso
    apply hwout
    exact Finset.mem_insert_of_mem (hwz' ▸ hz'R)

theorem card_escapeEdges (R : Finset V) (x : V) :
    #(escapeEdges G R x) = ∑ z ∈ R, #(escapeNeighbors G R x z) := by
  classical
  rw [escapeEdges, Finset.card_image_iff.mpr (escapeEdge_injOn G R x)]
  exact Finset.card_sigma _ _

theorem card_escapeEdges_ge (R : Finset V) (x : V) (hxR : x ∉ R) :
    ∑ z ∈ R, (G.degree z - #R) ≤ #(escapeEdges G R x) := by
  rw [card_escapeEdges]
  exact Finset.sum_le_sum fun z hz ↦ card_escapeNeighbors_ge G R x z hz hxR

theorem escapeEdges_subset_edgeFinset (R : Finset V) (x : V) :
    escapeEdges G R x ⊆ G.edgeFinset := by
  classical
  intro e he
  simp only [escapeEdges, Finset.mem_image] at he
  obtain ⟨⟨z, w⟩, hzw, rfl⟩ := he
  have hwn :
      w ∈ G.neighborFinset z :=
    (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hzw).2).1
  simpa [escapeEdge] using (G.mem_neighborFinset z w).mp hwn

theorem escapeEdges_not_incident (R : Finset V) (x : V) (hxR : x ∉ R) :
    ∀ e ∈ escapeEdges G R x, x ∉ e := by
  classical
  intro e he
  simp only [escapeEdges, Finset.mem_image] at he
  obtain ⟨⟨z, w⟩, hzw, rfl⟩ := he
  have hzR : z ∈ R := (Finset.mem_sigma.mp hzw).1
  have hwout : w ∉ insert x R :=
    (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hzw).2).2
  simp only [escapeEdge, Sym2.mem_iff]
  push Not
  exact ⟨fun h ↦ hxR (h ▸ hzR),
    fun h ↦ hwout (Finset.mem_insert.mpr (Or.inl h.symm))⟩

def edgesFrom (x : V) (S : Finset V) : Finset (Sym2 V) :=
  S.image fun z ↦ s(x, z)

omit [Fintype V] in
theorem card_edgesFrom (x : V) (S : Finset V) :
    #(edgesFrom x S) = #S := by
  classical
  rw [edgesFrom, Finset.card_image_iff]
  intro z _ w _ h
  exact Sym2.congr_right.mp h

omit [Fintype V] in
theorem sum_edgesFrom (x : V) (S : Finset V) (f : Sym2 V → ℕ) :
    ∑ e ∈ edgesFrom x S, f e = ∑ z ∈ S, f s(x, z) := by
  classical
  rw [edgesFrom, Finset.sum_image]
  intro z _ w _ h
  exact Sym2.congr_right.mp h

omit [Fintype V] in
theorem edgesFrom_mem_center (x : V) (S : Finset V) :
    ∀ e ∈ edgesFrom x S, x ∈ e := by
  classical
  intro e he
  simp only [edgesFrom, Finset.mem_image] at he
  obtain ⟨z, _, rfl⟩ := he
  simp

theorem edgesFrom_subset_edgeFinset (x : V) (S : Finset V)
    (hS : S ⊆ G.neighborFinset x) :
    edgesFrom x S ⊆ G.edgeFinset := by
  classical
  intro e he
  simp only [edgesFrom, Finset.mem_image] at he
  obtain ⟨z, hz, rfl⟩ := he
  have hadj : G.Adj x z := (G.mem_neighborFinset x z).mp (hS hz)
  simpa using hadj

theorem edgesFrom_unselected_subset (A : Finset (Sym2 V)) (x : V)
    (S : Finset V) (hS : S ⊆ unselectedNeighbors G A x) :
    edgesFrom x S ⊆ G.edgeFinset \ A := by
  intro e he
  have hedge := edgesFrom_subset_edgeFinset G x S
    (fun z hz ↦ (Finset.mem_filter.mp (hS hz)).1) he
  classical
  simp only [edgesFrom, Finset.mem_image] at he
  obtain ⟨z, hz, rfl⟩ := he
  exact Finset.mem_sdiff.mpr
    ⟨hedge, (Finset.mem_filter.mp (hS hz)).2⟩

theorem selectedEdges_subset (A : Finset (Sym2 V)) (x : V) :
    edgesFrom x (selectedNeighbors G A x) ⊆ A := by
  classical
  intro e he
  simp only [edgesFrom, Finset.mem_image] at he
  obtain ⟨z, hz, rfl⟩ := he
  exact (Finset.mem_filter.mp hz).2

omit [DecidableEq V] in
theorem edgeImbalance_from_max (hLI : LocallyIrregular G)
    {x z : V} (hx : G.degree x = G.maxDegree) (hxz : G.Adj x z) :
    edgeImbalance G s(x, z) = G.maxDegree - G.degree z := by
  have hzle := G.degree_le_maxDegree z
  have hzne : G.degree z ≠ G.maxDegree := by
    intro h
    apply hLI hxz
    omega
  rw [edgeImbalance_mk, hx, Nat.dist_eq_sub_of_le_right hzle]

omit [DecidableEq V] in
theorem reservoir_capacity_identity (hLI : LocallyIrregular G)
    {x z : V} (hx : G.degree x = G.maxDegree) (hxz : G.Adj x z)
    {k : ℕ} (hkD : k < G.maxDegree) :
    min k (edgeImbalance G s(x, z)) +
        (G.degree z - (G.maxDegree - k)) = k := by
  rw [edgeImbalance_from_max G hLI hx hxz]
  have hzle := G.degree_le_maxDegree z
  have hzne : G.degree z ≠ G.maxDegree := by
    intro h
    apply hLI hxz
    omega
  have hzlt : G.degree z < G.maxDegree := lt_of_le_of_ne hzle hzne
  by_cases hcap : k ≤ G.maxDegree - G.degree z
  · rw [min_eq_left hcap]
    omega
  · rw [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hcap))]
    omega

theorem card_selected_escapeEdges_le (A : Finset (Sym2 V))
    (R : Finset V) (x : V) (hxR : x ∉ R) :
    #(escapeEdges G R x ∩ A) ≤ #A - #(selectedNeighbors G A x) := by
  classical
  let Sx := edgesFrom x (selectedNeighbors G A x)
  let FA := escapeEdges G R x ∩ A
  have hSxA : Sx ⊆ A := selectedEdges_subset G A x
  have hFAA : FA ⊆ A := Finset.inter_subset_right
  have hdisj : Disjoint FA Sx := by
    rw [Finset.disjoint_left]
    intro e heFA heSx
    have heF : e ∈ escapeEdges G R x := (Finset.mem_inter.mp heFA).1
    have hxnot : x ∉ e := escapeEdges_not_incident G R x hxR e heF
    have hxmem : x ∈ e := edgesFrom_mem_center x _ e heSx
    exact hxnot hxmem
  have hunion : FA ∪ Sx ⊆ A := Finset.union_subset hFAA hSxA
  have hcard_union : #FA + #Sx ≤ #A := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hunion
  have hcardSx : #Sx = #(selectedNeighbors G A x) :=
    card_edgesFrom x _
  change #FA ≤ #A - #(selectedNeighbors G A x)
  omega

theorem escape_shortfall_le_unselected_capacity
    (hLI : LocallyIrregular G) (A : Finset (Sym2 V))
    (R : Finset V) (x : V) (hxR : x ∉ R) (hApos : 0 < #A) :
    (∑ z ∈ R, (G.degree z - #R)) ≤
      (#A - #(selectedNeighbors G A x)) +
        ∑ e ∈ escapeEdges G R x \ A, min #A (edgeImbalance G e) := by
  classical
  let F := escapeEdges G R x
  let t := #A - #(selectedNeighbors G A x)
  have hrho : (∑ z ∈ R, (G.degree z - #R)) ≤ #F :=
    card_escapeEdges_ge G R x hxR
  have hselected : #(F ∩ A) ≤ t :=
    card_selected_escapeEdges_le G A R x hxR
  have hpartition : #(F \ A) + #(A ∩ F) = #F := by
    simpa [Finset.inter_comm] using
      (Finset.card_sdiff_add_card_inter F A)
  have hcap : #(F \ A) ≤
      ∑ e ∈ F \ A, min #A (edgeImbalance G e) := by
    calc
      #(F \ A) = ∑ _e ∈ F \ A, 1 := by simp
      _ ≤ ∑ e ∈ F \ A, min #A (edgeImbalance G e) := by
        exact Finset.sum_le_sum fun e he ↦ by
          have heG : e ∈ G.edgeFinset :=
            escapeEdges_subset_edgeFinset G R x (Finset.mem_sdiff.mp he).1
          exact le_min
            (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hApos))
            (Nat.one_le_iff_ne_zero.mpr
              (Nat.ne_of_gt (edgeImbalance_pos G hLI heG)))
  change (∑ z ∈ R, (G.degree z - #R)) ≤
    t + ∑ e ∈ F \ A, min #A (edgeImbalance G e)
  have hinter : #(A ∩ F) ≤ t := by
    simpa [Finset.inter_comm] using hselected
  omega

theorem reservoir_escape
    (hLI : LocallyIrregular G) (A : Finset (Sym2 V)) :
    #A * (G.maxDegree - #A) ≤
      ∑ e ∈ G.edgeFinset \ A, min #A (edgeImbalance G e) := by
  classical
  by_cases hAempty : A = ∅
  · simp [hAempty]
  have hApos : 0 < #A := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hAempty)
  by_cases hDk : G.maxDegree ≤ #A
  · simp [Nat.sub_eq_zero_of_le hDk]
  have hkD : #A < G.maxDegree := Nat.lt_of_not_ge hDk
  letI : Nonempty V := by
    by_contra hV
    letI : IsEmpty V := not_nonempty_iff.mp hV
    have hzero : G.maxDegree = 0 := G.maxDegree_of_isEmpty
    omega
  obtain ⟨x, hxmax⟩ := G.exists_maximal_degree_vertex
  have hx : G.degree x = G.maxDegree := hxmax.symm
  let N := unselectedNeighbors G A x
  let a := #(selectedNeighbors G A x)
  have hale : a ≤ #A := card_selectedNeighbors_le G A x
  have hNcard : #N = G.maxDegree - a := by
    dsimp [N, a]
    rw [card_unselectedNeighbors, hx]
  have hrle : G.maxDegree - #A ≤ #N := by omega
  obtain ⟨R, hRN, hRcard⟩ :=
    Finset.exists_subset_card_eq (s := N) hrle
  let X := N \ R
  have hxR : x ∉ R := by
    intro hxmem
    have hxN := hRN hxmem
    have hxneighbor :
        x ∈ G.neighborFinset x := (Finset.mem_filter.mp hxN).1
    exact G.notMem_neighborFinset_self x hxneighbor
  have hXN : X ⊆ N := Finset.sdiff_subset
  have hRX : Disjoint R X := Finset.disjoint_sdiff
  have hXcard : #X = #A - a := by
    have := Finset.card_sdiff_of_subset hRN
    dsimp [X] at this ⊢
    omega
  let c : Sym2 V → ℕ := fun e ↦ min #A (edgeImbalance G e)
  let rho := ∑ z ∈ R, (G.degree z - #R)
  let ER := edgesFrom x R
  let EX := edgesFrom x X
  let FB := escapeEdges G R x \ A
  have hRneighbor : R ⊆ G.neighborFinset x := by
    intro z hz
    exact (Finset.mem_filter.mp (hRN hz)).1
  have hXneighbor : X ⊆ G.neighborFinset x := by
    intro z hz
    exact (Finset.mem_filter.mp (hXN hz)).1
  have hRtail : ER ⊆ G.edgeFinset \ A := by
    exact edgesFrom_unselected_subset G A x R hRN
  have hXtail : EX ⊆ G.edgeFinset \ A := by
    exact edgesFrom_unselected_subset G A x X hXN
  have hFtail : FB ⊆ G.edgeFinset \ A := by
    intro e he
    have he' := Finset.mem_sdiff.mp he
    exact Finset.mem_sdiff.mpr
      ⟨escapeEdges_subset_edgeFinset G R x he'.1, he'.2⟩
  have hEREX : Disjoint ER EX := by
    rw [Finset.disjoint_left]
    intro e heR heX
    simp only [ER, EX, edgesFrom, Finset.mem_image] at heR heX
    obtain ⟨z, hzR, rfl⟩ := heR
    obtain ⟨w, hwX, heq⟩ := heX
    have hzw : z = w := Sym2.congr_right.mp heq.symm
    subst w
    exact (Finset.disjoint_left.mp hRX) hzR hwX
  have hERF : Disjoint ER FB := by
    rw [Finset.disjoint_left]
    intro e heR heF
    have hxmem : x ∈ e := edgesFrom_mem_center x R e heR
    have heEscape : e ∈ escapeEdges G R x :=
      (Finset.mem_sdiff.mp heF).1
    exact escapeEdges_not_incident G R x hxR e heEscape hxmem
  have hEXF : Disjoint EX FB := by
    rw [Finset.disjoint_left]
    intro e heX heF
    have hxmem : x ∈ e := edgesFrom_mem_center x X e heX
    have heEscape : e ∈ escapeEdges G R x :=
      (Finset.mem_sdiff.mp heF).1
    exact escapeEdges_not_incident G R x hxR e heEscape hxmem
  have hsource :
      (∑ e ∈ ER, c e) + (∑ e ∈ EX, c e) + (∑ e ∈ FB, c e) ≤
        ∑ e ∈ G.edgeFinset \ A, c e := by
    have hdisj_union : Disjoint (ER ∪ EX) FB :=
      Finset.disjoint_union_left.mpr ⟨hERF, hEXF⟩
    calc
      (∑ e ∈ ER, c e) + (∑ e ∈ EX, c e) + (∑ e ∈ FB, c e) =
          (∑ e ∈ ER ∪ EX, c e) + (∑ e ∈ FB, c e) := by
            rw [Finset.sum_union hEREX]
      _ = ∑ e ∈ (ER ∪ EX) ∪ FB, c e :=
        (Finset.sum_union hdisj_union).symm
      _ ≤ ∑ e ∈ G.edgeFinset \ A, c e :=
        Finset.sum_le_sum_of_subset
          (Finset.union_subset (Finset.union_subset hRtail hXtail) hFtail)
  have hreservoir :
      (∑ e ∈ ER, c e) + rho = #R * #A := by
    rw [sum_edgesFrom]
    rw [← Finset.sum_add_distrib]
    calc
      ∑ z ∈ R, (c s(x, z) + (G.degree z - #R)) =
          ∑ _z ∈ R, #A := by
            apply Finset.sum_congr rfl
            intro z hzR
            have hxz : G.Adj x z :=
              (G.mem_neighborFinset x z).mp (hRneighbor hzR)
            simpa [c, hRcard] using
              (reservoir_capacity_identity G hLI hx hxz hkD)
      _ = #R * #A := by simp
  have hXcap : #X ≤ ∑ e ∈ EX, c e := by
    rw [← card_edgesFrom x X]
    calc
      #EX = ∑ _e ∈ EX, 1 := by simp
      _ ≤ ∑ e ∈ EX, c e := by
        exact Finset.sum_le_sum fun e he ↦ by
          have heG : e ∈ G.edgeFinset :=
            (Finset.mem_sdiff.mp (hXtail he)).1
          exact le_min
            (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hApos))
            (one_le_edgeImbalance G hLI heG)
  have hEscape :
      rho ≤ (#A - a) + ∑ e ∈ FB, c e := by
    simpa [rho, FB, c, a] using
      (escape_shortfall_le_unselected_capacity G hLI A R x hxR hApos)
  have hnumeric :
      #R * #A ≤
        (∑ e ∈ ER, c e) + (∑ e ∈ EX, c e) + (∑ e ∈ FB, c e) := by
    omega
  calc
    #A * (G.maxDegree - #A) = #R * #A := by
      rw [hRcard, Nat.mul_comm]
    _ ≤ (∑ e ∈ ER, c e) + (∑ e ∈ EX, c e) + (∑ e ∈ FB, c e) :=
      hnumeric
    _ ≤ ∑ e ∈ G.edgeFinset \ A, c e := hsource

def edgeDegreeSum (e : Sym2 V) : ℕ :=
  ∑ v ∈ e.toFinset, G.degree v

theorem edgeDegreeSum_mk_of_ne {u v : V} (huv : u ≠ v) :
    edgeDegreeSum G s(u, v) = G.degree u + G.degree v := by
  rw [edgeDegreeSum, Sym2.toFinset_mk_eq]
  simp [huv]

theorem natCast_dist_zmod_two (a b : ℕ) :
    (Nat.dist a b : ZMod 2) = (a : ZMod 2) + b := by
  rw [← Nat.cast_add, ZMod.natCast_eq_natCast_iff']
  unfold Nat.dist
  omega

theorem edgeImbalance_cast_eq_edgeDegreeSum_cast {e : Sym2 V}
    (he : e ∈ G.edgeFinset) :
    (edgeImbalance G e : ZMod 2) = (edgeDegreeSum G e : ZMod 2) := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : u ≠ v := (G.mem_edgeFinset.mp he).ne
      rw [edgeImbalance_mk, edgeDegreeSum_mk_of_ne G huv, Nat.cast_add]
      exact natCast_dist_zmod_two _ _

theorem sum_edgeDegreeSum :
    ∑ e ∈ G.edgeFinset, edgeDegreeSum G e =
      ∑ v : V, G.degree v * G.degree v := by
  classical
  calc
    ∑ e ∈ G.edgeFinset, edgeDegreeSum G e =
        ∑ e ∈ G.edgeFinset,
          ∑ v : V, if v ∈ e then G.degree v else 0 := by
            apply Finset.sum_congr rfl
            intro e _
            rw [edgeDegreeSum]
            rw [← Finset.sum_filter]
            apply Finset.sum_congr
            · ext v
              simp
            · simp
    _ = ∑ v : V,
          ∑ e ∈ G.edgeFinset, if v ∈ e then G.degree v else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ v : V, ∑ e ∈ G.incidenceFinset v, G.degree v := by
            apply Finset.sum_congr rfl
            intro v _
            rw [← Finset.sum_filter]
            congr 1
            exact (G.incidenceFinset_eq_filter v).symm
    _ = ∑ v : V, G.degree v * G.degree v := by
            apply Finset.sum_congr rfl
            intro v _
            simp [G.card_incidenceFinset_eq_degree v]

theorem imbalance_sum_even :
    Even (∑ e ∈ G.edgeFinset, edgeImbalance G e) := by
  have hsquare (q : ZMod 2) : q * q = q := by
    fin_cases q <;> decide
  rw [← ZMod.natCast_eq_zero_iff_even]
  calc
    ((∑ e ∈ G.edgeFinset, edgeImbalance G e : ℕ) : ZMod 2) =
        ∑ e ∈ G.edgeFinset, (edgeImbalance G e : ZMod 2) := by
          simp
    _ = ∑ e ∈ G.edgeFinset, (edgeDegreeSum G e : ZMod 2) := by
          apply Finset.sum_congr rfl
          intro e he
          exact edgeImbalance_cast_eq_edgeDegreeSum_cast G he
    _ = ((∑ e ∈ G.edgeFinset, edgeDegreeSum G e : ℕ) : ZMod 2) := by
          simp
    _ = ((∑ v : V, G.degree v * G.degree v : ℕ) : ZMod 2) := by
          rw [sum_edgeDegreeSum]
    _ = ∑ v : V, (G.degree v : ZMod 2) * G.degree v := by
          simp
    _ = ∑ v : V, (G.degree v : ZMod 2) := by
          apply Finset.sum_congr rfl
          intro v _
          exact hsquare _
    _ = ((∑ v : V, G.degree v : ℕ) : ZMod 2) := by simp
    _ = ((2 * #G.edgeFinset : ℕ) : ZMod 2) := by
          rw [G.sum_degrees_eq_twice_card_edges]
    _ = 0 := by
          rw [Nat.cast_mul, ZMod.natCast_self]
          simp

theorem edge_subset_erdosGallai
    (hLI : LocallyIrregular G) (A : Finset (Sym2 V))
    (hA : A ⊆ G.edgeFinset) :
    ∑ e ∈ A, edgeImbalance G e ≤
      #A * (#A - 1) +
        ∑ e ∈ G.edgeFinset \ A, min #A (edgeImbalance G e) := by
  classical
  by_cases hAempty : A = ∅
  · simp [hAempty]
  have hApos : 0 < #A :=
    Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hAempty)
  have himb :
      ∑ e ∈ A, edgeImbalance G e ≤ #A * (G.maxDegree - 1) := by
    calc
      ∑ e ∈ A, edgeImbalance G e ≤
          ∑ _e ∈ A, (G.maxDegree - 1) := by
            exact Finset.sum_le_sum fun e he ↦
              edgeImbalance_le_maxDegree_sub_one G hLI (hA he)
      _ = #A * (G.maxDegree - 1) := by simp
  by_cases hDk : G.maxDegree ≤ #A
  · have hdeg : G.maxDegree - 1 ≤ #A - 1 := by omega
    exact himb.trans <| (Nat.mul_le_mul_left #A hdeg).trans <|
      Nat.le_add_right _ _
  · have hkD : #A < G.maxDegree := Nat.lt_of_not_ge hDk
    have hsplit :
        G.maxDegree - 1 = (#A - 1) + (G.maxDegree - #A) := by
      omega
    have hres := reservoir_escape G hLI A
    rw [hsplit, Nat.mul_add] at himb
    omega

def imbalanceMultiset : Multiset ℕ :=
  G.edgeFinset.val.map (edgeImbalance G)

theorem imbalance_finsetEG (hLI : LocallyIrregular G) :
    ErdosGallai.FinsetEG G.edgeFinset (edgeImbalance G) := by
  constructor
  · exact imbalance_sum_even G
  · intro A hA
    exact edge_subset_erdosGallai G hLI A hA

theorem imbalanceMultiset_graphic (hLI : LocallyIrregular G) :
    ErdosGallai.Graphic (imbalanceMultiset G) := by
  simpa [imbalanceMultiset] using
    ErdosGallai.graphic_of_finsetEG
      G.edgeFinset (edgeImbalance G) (imbalance_finsetEG G hLI)

/-- The edge-imbalance multiset of a finite locally irregular graph is graphic. -/
theorem imbalanceConjecture (hLI : LocallyIrregular G) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (H : SimpleGraph W) (_ : DecidableRel H.Adj),
      Finset.univ.val.map (fun w => H.degree w) = imbalanceMultiset G :=
  imbalanceMultiset_graphic G hLI

end Imbalance
