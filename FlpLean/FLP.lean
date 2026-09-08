import FlpLean.Runs

namespace FLP

variable {n : Nat} {State Msg : Type} [DecidableEq Msg] (P : Protocol n State Msg)

/-- 合意 (agreement): 到達可能な配置で 2 つの異なる値が決定されることはない。 -/
def Agreement : Prop := ∀ c, reach0 P c → ¬ (decided P c true ∧ decided P c false)

open Classical in
noncomputable def bivBlock (hT : FinTerm P) (hn : 0 < n) (e : Event n Msg)
    (x : Config n State Msg) : List (Event n Msg) :=
  if h : reach0 P x ∧ bivalent P x ∧ enabled P x e then
    Classical.choose (bivalent_step P hT hn h.1 h.2.1 e h.2.2)
  else []

theorem bivBlock_spec (hT : FinTerm P) (hn : 0 < n) :
    BlockSpec P (bivBlock P hT hn) (fun x => reach0 P x ∧ bivalent P x) (fun _ => True) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e x hx
    unfold bivBlock
    split
    · rename_i h
      exact (Classical.choose_spec (bivalent_step P hT hn h.1 h.2.1 e h.2.2)).1
    · trivial
  · intro e x hx
    unfold bivBlock
    split
    · rename_i h
      have hs := Classical.choose_spec (bivalent_step P hT hn h.1 h.2.1 e h.2.2)
      exact ⟨reach0_of_reach P hx.1 (reach_of_run P hs.1), hs.2.2⟩
    · exact hx
  · intro e x hx he _
    unfold bivBlock
    rw [dif_pos ⟨hx.1, hx.2, he⟩]
    exact (Classical.choose_spec (bivalent_step P hT hn hx.1 hx.2 e he)).2.1
  · intros
    trivial

/-- **FLP 不可能性定理**:
非同期メッセージ通信モデルにおいて、合意 (Agreement)・非自明性 (Nontrivial)・
1 故障許容の停止性 (Terminating) をすべて満たすプロトコルは存在しない。
`g` はイベント集合の可算性 (メッセージが可算個) を表す。 -/
theorem flp_impossibility (hn : 0 < n) (g : Nat → Event n Msg) (hg : ∀ e, ∃ m, g m = e)
    (hAgree : Agreement P) (hNT : Nontrivial P) (hTerm : Terminating P) : False := by
  have hT : FinTerm P := finTerm_of_terminating P g hg hTerm
  obtain ⟨v, hbv⟩ := exists_bivalent_init P hT hNT
  have spec := bivBlock_spec P hT hn
  have h0 : reach0 P (init P v) ∧ bivalent P (init P v) := ⟨⟨v, reach_refl P _⟩, hbv⟩
  let r := seqRun g spec (init P v) h0
  have hfair := fun k e he => cfgSeq_fair (c₀ := init P v) g spec h0 hg k e he trivial
  have hadm : r.admissible := by
    intro q _ _
    left
    refine ⟨?_, ?_⟩
    · intro k
      obtain ⟨j, hj, hm⟩ := hfair k (q, none) (enabled_none P _ q)
      exact ⟨j, hj, (q, none), hm, rfl⟩
    · intro k e _ he
      exact hfair k e he
  obtain ⟨k, w, hw⟩ := hTerm r ⟨v, rfl⟩ hadm
  obtain ⟨hr, hb⟩ := cfgSeq_inv (c₀ := init P v) g spec h0 k
  obtain ⟨σ, hσ, hd⟩ := (bivalent_iff P _).1 hb (!w)
  have hw' := decided_run P hw σ
  apply hAgree _ (reach0_of_reach P hr (reach_of_run P hσ))
  cases w
  · exact ⟨hd, hw'⟩
  · exact ⟨hw', hd⟩

/-- メッセージ集合が可算 (全射 `dec : ℕ → Msg`) ならイベント集合も可算。 -/
def eventEnum (hn : 0 < n) (dec : Nat → Msg) (m : Nat) : Event n Msg :=
  (⟨m % n, Nat.mod_lt _ hn⟩, if m / n = 0 then none else some (dec (m / n - 1)))

omit [DecidableEq Msg] in
theorem eventEnum_surj (hn : 0 < n) (dec : Nat → Msg) (hdec : ∀ x, ∃ a, dec a = x) :
    ∀ e, ∃ m, eventEnum hn dec m = e := by
  intro ⟨p, om⟩
  cases om with
  | none =>
    refine ⟨p.val, ?_⟩
    unfold eventEnum
    have h1 : p.val % n = p.val := Nat.mod_eq_of_lt p.isLt
    have h2 : p.val / n = 0 := Nat.div_eq_of_lt p.isLt
    simp [h1, h2]
  | some x =>
    obtain ⟨a, rfl⟩ := hdec x
    refine ⟨p.val + (a + 1) * n, ?_⟩
    unfold eventEnum
    have h1 : (p.val + (a + 1) * n) % n = p.val := by
      rw [Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt p.isLt
    have h2 : (p.val + (a + 1) * n) / n = a + 1 := by
      rw [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt p.isLt]
      omega
    simp [h1, h2]

/-- 可算なメッセージ集合上の FLP 不可能性定理。 -/
theorem flp_impossibility_countable (hn : 0 < n) (dec : Nat → Msg) (hdec : ∀ x, ∃ a, dec a = x)
    (hAgree : Agreement P) (hNT : Nontrivial P) (hTerm : Terminating P) : False :=
  flp_impossibility P hn (eventEnum hn dec) (eventEnum_surj hn dec hdec) hAgree hNT hTerm

end FLP
