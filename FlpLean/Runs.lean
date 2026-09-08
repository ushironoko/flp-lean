import FlpLean.Bivalence

namespace FLP

variable {n : Nat} {State Msg : Type} [DecidableEq Msg] (P : Protocol n State Msg)

structure OmegaRun where
  cfg : Nat → Config n State Msg
  sched : Nat → List (Event n Msg)
  step : ∀ k, cfg (k + 1) = run P (cfg k) (sched k)
  app : ∀ k, applicable P (cfg k) (sched k)

namespace OmegaRun

variable {P}

/-- プロセス q は無限回ステップし、q 宛の有効なイベントはいつか必ず実行される。 -/
def correct (r : OmegaRun P) (q : Fin n) : Prop :=
  (∀ k, ∃ j, k ≤ j ∧ ∃ e ∈ r.sched j, e.1 = q) ∧
  (∀ k (e : Event n Msg), e.1 = q → enabled P (r.cfg k) e → ∃ j, k ≤ j ∧ e ∈ r.sched j)

/-- 高々1つのプロセスしか故障しない。 -/
def admissible (r : OmegaRun P) : Prop :=
  ∀ q q' : Fin n, q ≠ q' → r.correct q ∨ r.correct q'

def decides (r : OmegaRun P) : Prop := ∃ k v, decided P (r.cfg k) v

def initial (r : OmegaRun P) : Prop := ∃ v, r.cfg 0 = init P v

end OmegaRun

/-- 停止性(1故障許容): 初期配置から始まる admissible run はすべて決定に至る。 -/
def Terminating : Prop := ∀ r : OmegaRun P, r.initial → r.admissible → r.decides

section Construct

variable (g : Nat → Event n Msg) (block : Event n Msg → Config n State Msg → List (Event n Msg))

structure BlockSpec (Inv : Config n State Msg → Prop) (Q : Event n Msg → Prop) : Prop where
  app : ∀ e x, Inv x → applicable P x (block e x)
  inv : ∀ e x, Inv x → Inv (run P x (block e x))
  last : ∀ e x, Inv x → enabled P x e → Q e → e ∈ block e x
  filt : ∀ e x, ∀ f ∈ block e x, Q f

def procList : List (Event n Msg) → Config n State Msg → List (Event n Msg)
  | [], _ => []
  | e :: es, x => block e x ++ procList es (run P x (block e x))

def stageSched (k : Nat) (x : Config n State Msg) : List (Event n Msg) :=
  procList P block ((List.range (k + 1)).map g) x

def cfgSeq (c₀ : Config n State Msg) : Nat → Config n State Msg
  | 0 => c₀
  | k + 1 => run P (cfgSeq c₀ k) (stageSched P g block k (cfgSeq c₀ k))

theorem cfgSeq_zero (c₀ : Config n State Msg) : cfgSeq P g block c₀ 0 = c₀ := rfl

theorem cfgSeq_succ (c₀ : Config n State Msg) (k : Nat) :
    cfgSeq P g block c₀ (k + 1) =
      run P (cfgSeq P g block c₀ k) (stageSched P g block k (cfgSeq P g block c₀ k)) := rfl

variable {Inv : Config n State Msg → Prop} {Q : Event n Msg → Prop}
variable {P block}

theorem procList_app (spec : BlockSpec P block Inv Q) (es : List (Event n Msg)) :
    ∀ x, Inv x → applicable P x (procList P block es x) := by
  induction es with
  | nil => intros; trivial
  | cons e es ih =>
    intro x hx
    simp only [procList]
    exact (applicable_append P _ _ _).2 ⟨spec.app e x hx, ih _ (spec.inv e x hx)⟩

theorem procList_inv (spec : BlockSpec P block Inv Q) (es : List (Event n Msg)) :
    ∀ x, Inv x → Inv (run P x (procList P block es x)) := by
  induction es with
  | nil => intros; assumption
  | cons e es ih =>
    intro x hx
    simp only [procList]
    rw [run_append]
    exact ih _ (spec.inv e x hx)

theorem procList_filt (spec : BlockSpec P block Inv Q) (es : List (Event n Msg)) :
    ∀ x, ∀ f ∈ procList P block es x, Q f := by
  induction es with
  | nil => intro x f hf; simp [procList] at hf
  | cons e es ih =>
    intro x f hf
    simp only [procList] at hf
    rcases List.mem_append.1 hf with h | h
    · exact spec.filt e x f h
    · exact ih _ f h

theorem procList_mem (spec : BlockSpec P block Inv Q) (es : List (Event n Msg)) :
    ∀ x, Inv x → ∀ e ∈ es, enabled P x e → Q e → e ∈ procList P block es x := by
  induction es with
  | nil => intro x _ e he; simp at he
  | cons f es ih =>
    intro x hx e he hen hq
    simp only [procList]
    rcases List.mem_cons.1 he with rfl | he'
    · exact List.mem_append_left _ (spec.last e x hx hen hq)
    · by_cases hb : e ∈ block f x
      · exact List.mem_append_left _ hb
      · have hen' : enabled P (run P x (block f x)) e :=
          enabled_run_of_notin P hen (spec.app f x hx) (fun g hg h => hb (h ▸ hg))
        exact List.mem_append_right _ (ih _ (spec.inv f x hx) e he' hen' hq)

variable {c₀ : Config n State Msg}

theorem cfgSeq_inv (spec : BlockSpec P block Inv Q) (h0 : Inv c₀) :
    ∀ k, Inv (cfgSeq P g block c₀ k) := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih => exact procList_inv spec _ _ ih

theorem stage_app (spec : BlockSpec P block Inv Q) (h0 : Inv c₀) (k : Nat) :
    applicable P (cfgSeq P g block c₀ k) (stageSched P g block k (cfgSeq P g block c₀ k)) :=
  procList_app spec _ _ (cfgSeq_inv g spec h0 k)

theorem stage_filt (spec : BlockSpec P block Inv Q) (k : Nat) (x : Config n State Msg) :
    ∀ f ∈ stageSched P g block k x, Q f :=
  procList_filt spec _ x

theorem cfgSeq_reach (spec : BlockSpec P block Inv Q) (h0 : Inv c₀) (k : Nat) :
    ∃ τ, applicable P c₀ τ ∧ (∀ f ∈ τ, Q f) ∧ run P c₀ τ = cfgSeq P g block c₀ k := by
  induction k with
  | zero => exact ⟨[], trivial, by simp, rfl⟩
  | succ k ih =>
    obtain ⟨τ, hτ, hQ, hrun⟩ := ih
    refine ⟨τ ++ stageSched P g block k (cfgSeq P g block c₀ k), ?_, ?_, ?_⟩
    · rw [applicable_append, hrun]
      exact ⟨hτ, stage_app g spec h0 k⟩
    · intro f hf
      rcases List.mem_append.1 hf with h | h
      · exact hQ f h
      · exact stage_filt g spec k _ f h
    · rw [run_append, hrun]
      rfl

theorem cfgSeq_enabled_or (spec : BlockSpec P block Inv Q) (h0 : Inv c₀) (k : Nat)
    (e : Event n Msg) (he : enabled P (cfgSeq P g block c₀ k) e) :
    ∀ d, (∃ j, k ≤ j ∧ j < k + d ∧ e ∈ stageSched P g block j (cfgSeq P g block c₀ j)) ∨
      enabled P (cfgSeq P g block c₀ (k + d)) e := by
  intro d
  induction d with
  | zero => exact Or.inr he
  | succ d ih =>
    rcases ih with ⟨j, hj1, hj2, hm⟩ | hen
    · exact Or.inl ⟨j, hj1, by omega, hm⟩
    · by_cases hm : e ∈ stageSched P g block (k + d) (cfgSeq P g block c₀ (k + d))
      · exact Or.inl ⟨k + d, by omega, by omega, hm⟩
      · right
        rw [← Nat.add_assoc, cfgSeq_succ]
        exact enabled_run_of_notin P hen (stage_app g spec h0 (k + d)) (fun f hf h => hm (h ▸ hf))

theorem cfgSeq_fair (spec : BlockSpec P block Inv Q) (h0 : Inv c₀) (hg : ∀ e, ∃ m, g m = e)
    (k : Nat) (e : Event n Msg) (he : enabled P (cfgSeq P g block c₀ k) e) (hq : Q e) :
    ∃ j, k ≤ j ∧ e ∈ stageSched P g block j (cfgSeq P g block c₀ j) := by
  obtain ⟨m, rfl⟩ := hg e
  rcases cfgSeq_enabled_or g spec h0 k (g m) he m with ⟨j, hj1, _, hm⟩ | hen
  · exact ⟨j, hj1, hm⟩
  · refine ⟨k + m, by omega, ?_⟩
    apply procList_mem spec _ _ (cfgSeq_inv g spec h0 (k + m)) (g m) _ hen hq
    exact List.mem_map.2 ⟨m, List.mem_range.2 (by omega), rfl⟩

def seqRun (spec : BlockSpec P block Inv Q) (c₀ : Config n State Msg) (h0 : Inv c₀) :
    OmegaRun P where
  cfg := cfgSeq P g block c₀
  sched := fun k => stageSched P g block k (cfgSeq P g block c₀ k)
  step := fun _ => rfl
  app := fun k => stage_app g spec h0 k

def prefixRun (spec : BlockSpec P block Inv Q) (c₀ : Config n State Msg)
    (ρ : List (Event n Msg)) (hρ : applicable P c₀ ρ) (h0 : Inv (run P c₀ ρ)) : OmegaRun P where
  cfg := fun k => match k with
    | 0 => c₀
    | k + 1 => cfgSeq P g block (run P c₀ ρ) k
  sched := fun k => match k with
    | 0 => ρ
    | k + 1 => stageSched P g block k (cfgSeq P g block (run P c₀ ρ) k)
  step := fun k => by cases k <;> rfl
  app := fun k => by
    cases k with
    | zero => exact hρ
    | succ k => exact stage_app g spec h0 k

end Construct

open Classical in
noncomputable def crashBlock (p : Fin n) (e : Event n Msg) (x : Config n State Msg) : List (Event n Msg) :=
  if enabled P x e ∧ e.1 ≠ p then [e] else []

theorem crashBlock_spec (p : Fin n) :
    BlockSpec P (crashBlock P p) (fun _ => True) (fun e => e.1 ≠ p) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e x _
    unfold crashBlock
    split
    · rename_i h
      simp [h.1]
    · trivial
  · intros
    trivial
  · intro e x _ he hq
    unfold crashBlock
    rw [if_pos ⟨he, hq⟩]
    simp
  · intro e x f hf
    unfold crashBlock at hf
    split at hf
    · rename_i h
      simp at hf
      subst hf
      exact h.2
    · simp at hf

/-- 1故障許容の停止性から有限形の停止性 (FinTerm) を導く。
プロセス p を最初から故障させ、他のプロセスに対して公平なスケジューラを構成する。 -/
theorem finTerm_of_terminating (g : Nat → Event n Msg) (hg : ∀ e, ∃ m, g m = e)
    (hTerm : Terminating P) : FinTerm P := by
  intro c hr p
  obtain ⟨v, ρ, hρ, rfl⟩ := hr
  have spec := crashBlock_spec P p
  let r := prefixRun g spec (init P v) ρ hρ trivial
  have hfair := fun k e he hq =>
    cfgSeq_fair (c₀ := run P (init P v) ρ) g spec trivial hg k e he hq
  have hcorrect : ∀ q, q ≠ p → r.correct q := by
    intro q hq
    refine ⟨?_, ?_⟩
    · intro k
      obtain ⟨j, hj, hm⟩ := hfair k (q, none) (enabled_none P _ q) hq
      exact ⟨j + 1, by omega, (q, none), hm, rfl⟩
    · intro k e heq he
      have hqe : e.1 ≠ p := by rw [heq]; exact hq
      cases k with
      | zero =>
        by_cases hm : e ∈ ρ
        · exact ⟨0, Nat.le_refl _, hm⟩
        · have he' : enabled P (run P (init P v) ρ) e :=
            enabled_run_of_notin P he hρ (fun f hf h => hm (h ▸ hf))
          obtain ⟨j, hj, hm'⟩ := hfair 0 e he' hqe
          exact ⟨j + 1, by omega, hm'⟩
      | succ k =>
        obtain ⟨j, hj, hm'⟩ := hfair k e he hqe
        exact ⟨j + 1, by omega, hm'⟩
  have hadm : r.admissible := by
    intro q q' hqq'
    by_cases hqp : q = p
    · subst hqp
      exact Or.inr (hcorrect q' (Ne.symm hqq'))
    · exact Or.inl (hcorrect q hqp)
  obtain ⟨k, w, hw⟩ := hTerm r ⟨v, rfl⟩ hadm
  cases k with
  | zero => exact absurd hw (not_decided_init P v w)
  | succ k =>
    obtain ⟨τ, hτ, hQ, hrun⟩ := cfgSeq_reach (c₀ := run P (init P v) ρ) g spec trivial k
    exact ⟨τ, hτ, hQ, w, by rw [hrun]; exact hw⟩

end FLP
