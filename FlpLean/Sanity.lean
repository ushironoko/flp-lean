import FlpLean.FLP

/-!
主定理の仮定 (Agreement / Nontrivial / Terminating) がそれぞれ個別には充足可能であり、
どの 2 つの組も同時に充足可能であることを具体的なプロトコルで確認する。
これにより `flp_impossibility` が仮定の不整合から自明に導かれたものではないことを示す。
-/

namespace FLP
namespace Sanity

variable {n : Nat} {State Msg : Type} [DecidableEq Msg] (P : Protocol n State Msg)

theorem decided_run_of_mem (hstep : ∀ p s m, ∃ v, P.out (P.step p s m).1 = some v)
    {c : Config n State Msg} {σ : List (Event n Msg)} {e : Event n Msg} (he : e ∈ σ) :
    ∃ v, decided P (run P c σ) v := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem he
  obtain ⟨v, hv⟩ := hstep e.1 ((run P c s).st e.1) e.2
  refine ⟨v, ?_⟩
  rw [run_append, run_cons]
  apply decided_run
  exact ⟨e.1, by rw [apply_st]; simp [hv]⟩

theorem terminating_of_step_decides (hn : 2 ≤ n)
    (hstep : ∀ p s m, ∃ v, P.out (P.step p s m).1 = some v) : Terminating P := by
  intro r _ hadm
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
  rcases hadm _ _ h01 with hc | hc <;>
  · obtain ⟨j, _, e, he, _⟩ := hc.1 0
    obtain ⟨v, hv⟩ := decided_run_of_mem P hstep (c := r.cfg j) he
    exact ⟨j + 1, v, by rw [r.step]; exact hv⟩

/-- 例1: 最初のステップで常に false を決定する。Agreement と Terminating を満たすが Nontrivial でない。 -/
def constP (n : Nat) (hn : 0 < n) : Protocol n Bool Unit where
  dest := fun _ => ⟨0, hn⟩
  step := fun _ _ _ => (true, [])
  out := fun s => if s then some false else none
  initSt := fun _ _ => false
  out_init := by intros; rfl
  out_stable := by
    intro p s m v h
    cases s <;> simp_all

theorem constP_agreement (hn : 0 < n) : Agreement (constP n hn) := by
  intro c _ ⟨⟨p, hp⟩, _⟩
  revert hp
  cases c.st p <;> simp [constP]

theorem constP_terminating (hn : 2 ≤ n) : Terminating (constP n (by omega)) :=
  terminating_of_step_decides _ hn (fun _ _ _ => ⟨false, rfl⟩)

theorem constP_not_nontrivial (hn : 0 < n) : ¬ Nontrivial (constP n hn) := by
  intro h
  obtain ⟨w, σ, _, p, hp⟩ := h true
  revert hp
  cases (run (constP n hn) (init (constP n hn) w) σ).st p <;> simp [constP]

/-- 例2: 各プロセスが最初のステップで自分の入力を決定する。Nontrivial と Terminating を満たすが Agreement でない。 -/
def ownP (n : Nat) (hn : 0 < n) : Protocol n (Bool × Bool) Unit where
  dest := fun _ => ⟨0, hn⟩
  step := fun _ s _ => ((s.1, true), [])
  out := fun s => if s.2 then some s.1 else none
  initSt := fun _ b => (b, false)
  out_init := by intros; rfl
  out_stable := by
    intro p s m v h
    obtain ⟨a, b⟩ := s
    cases b <;> simp_all

theorem ownP_nontrivial (hn : 0 < n) : Nontrivial (ownP n hn) := by
  intro v
  refine ⟨fun _ => v, [(⟨0, hn⟩, none)], by simp, ⟨0, hn⟩, ?_⟩
  simp [run, apply_st, ownP, init]

theorem ownP_terminating (hn : 2 ≤ n) : Terminating (ownP n (by omega)) :=
  terminating_of_step_decides _ hn (fun _ s _ => ⟨s.1, rfl⟩)

theorem ownP_not_agreement (hn : 2 ≤ n) : ¬ Agreement (ownP n (by omega)) := by
  intro h
  let P := ownP n (by omega : 0 < n)
  let v : Fin n → Bool := fun i => decide (i.val = 1)
  let σ : List (Event n Unit) := [(⟨0, by omega⟩, none), (⟨1, by omega⟩, none)]
  have hσ : applicable P (init P v) σ := by simp [σ]
  apply h (run P (init P v) σ) ⟨v, reach_of_run P hσ⟩
  refine ⟨⟨⟨1, by omega⟩, ?_⟩, ⟨⟨0, by omega⟩, ?_⟩⟩
  · simp [P, σ, v, run, apply_st, ownP, init]
  · simp [P, σ, v, run, apply_st, ownP, init]

/-- 例3: プロセス 0 だけが最初のステップで自分の入力を決定し、他は決定しない。
Agreement と Nontrivial を満たす。したがって主定理より Terminating ではあり得ない。 -/
def leaderP (n : Nat) (hn : 0 < n) : Protocol n (Bool × Bool) Unit where
  dest := fun _ => ⟨0, hn⟩
  step := fun p s _ => ((s.1, s.2 || decide (p = ⟨0, hn⟩)), [])
  out := fun s => if s.2 then some s.1 else none
  initSt := fun _ b => (b, false)
  out_init := by intros; rfl
  out_stable := by
    intro p s m v h
    obtain ⟨a, b⟩ := s
    cases b <;> simp_all

theorem leaderP_inv (hn : 0 < n) (v : Fin n → Bool) (σ : List (Event n Unit)) :
    ∀ c : Config n (Bool × Bool) Unit,
      ((∀ q, (c.st q).1 = v q) ∧ (∀ q, q ≠ ⟨0, hn⟩ → (c.st q).2 = false)) →
      ((∀ q, ((run (leaderP n hn) c σ).st q).1 = v q) ∧
        (∀ q, q ≠ ⟨0, hn⟩ → ((run (leaderP n hn) c σ).st q).2 = false)) := by
  induction σ with
  | nil => intro c h; exact h
  | cons e σ ih =>
    intro c ⟨h1, h2⟩
    rw [run_cons]
    apply ih
    refine ⟨?_, ?_⟩
    · intro q
      rw [apply_st]
      by_cases hq : q = e.1
      · subst hq; simp [leaderP, h1]
      · simp [hq, h1]
    · intro q hq
      rw [apply_st]
      by_cases hqe : q = e.1
      · subst hqe
        simp [leaderP, h2 _ hq, hq]
      · simp [hqe, h2 q hq]

theorem leaderP_agreement (hn : 0 < n) : Agreement (leaderP n hn) := by
  rintro c ⟨v, σ, -, rfl⟩ ⟨⟨p, hp⟩, ⟨p', hp'⟩⟩
  have hinv := leaderP_inv hn v σ (init (leaderP n hn) v)
    ⟨fun q => rfl, fun q _ => rfl⟩
  have key : ∀ q w, (leaderP n hn).out ((run (leaderP n hn) (init (leaderP n hn) v) σ).st q) = some w →
      w = v ⟨0, hn⟩ := by
    intro q w hw
    have hout : ∀ s : Bool × Bool, (leaderP n hn).out s = if s.2 then some s.1 else none :=
      fun _ => rfl
    rw [hout] at hw
    by_cases hq : q = ⟨0, hn⟩
    · subst hq
      have h1 := hinv.1 ⟨0, hn⟩
      split at hw
      · have := Option.some.inj hw
        rw [← this]
        exact h1
      · cases hw
    · rw [hinv.2 q hq] at hw
      simp at hw
  have := key p true hp
  have := key p' false hp'
  simp_all

theorem leaderP_nontrivial (hn : 0 < n) : Nontrivial (leaderP n hn) := by
  intro v
  refine ⟨fun _ => v, [(⟨0, hn⟩, none)], by simp, ⟨0, hn⟩, ?_⟩
  simp [run, apply_st, leaderP, init]

/-- 主定理の帰結: 例3 のプロトコルは 1 故障許容の停止性を満たさない。 -/
theorem leaderP_not_terminating (hn : 0 < n) : ¬ Terminating (leaderP n hn) :=
  fun hT => flp_impossibility_countable (leaderP n hn) hn (fun _ => ()) (fun x => ⟨0, by cases x; rfl⟩)
    (leaderP_agreement hn) (leaderP_nontrivial hn) hT

end Sanity
end FLP
