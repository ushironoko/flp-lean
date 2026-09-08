namespace FLP

structure Protocol (n : Nat) (State Msg : Type) where
  dest : Msg → Fin n
  step : Fin n → State → Option Msg → State × List Msg
  out : State → Option Bool
  initSt : Fin n → Bool → State
  out_init : ∀ p b, out (initSt p b) = none
  out_stable : ∀ p s m v, out s = some v → out (step p s m).1 = some v

structure Config (n : Nat) (State Msg : Type) where
  st : Fin n → State
  buf : Msg → Nat

abbrev Event (n : Nat) (Msg : Type) := Fin n × Option Msg

variable {n : Nat} {State Msg : Type} [DecidableEq Msg]

omit [DecidableEq Msg] in
theorem Config.ext {c c' : Config n State Msg} (h1 : c.st = c'.st) (h2 : c.buf = c'.buf) :
    c = c' := by
  cases c; cases c'; cases h1; cases h2; rfl

def count : List Msg → Msg → Nat
  | [], _ => 0
  | m :: ms, x => (if m = x then 1 else 0) + count ms x

def upd (f : Fin n → State) (p : Fin n) (s : State) : Fin n → State :=
  fun q => if q = p then s else f q

@[simp] theorem upd_same (f : Fin n → State) (p : Fin n) (s : State) : upd f p s p = s := by
  simp [upd]

@[simp] theorem upd_ne (f : Fin n → State) (p q : Fin n) (s : State) (h : q ≠ p) :
    upd f p s q = f q := by
  simp [upd, h]

variable (P : Protocol n State Msg)

def enabled : Config n State Msg → Event n Msg → Prop
  | _, (_, none) => True
  | c, (p, some m) => P.dest m = p ∧ 0 < c.buf m

omit [DecidableEq Msg] in
@[simp] theorem enabled_none (c : Config n State Msg) (p : Fin n) : enabled P c (p, none) := by
  simp [enabled]

omit [DecidableEq Msg] in
@[simp] theorem enabled_some (c : Config n State Msg) (p : Fin n) (m : Msg) :
    enabled P c (p, some m) ↔ P.dest m = p ∧ 0 < c.buf m := Iff.rfl

def apply (c : Config n State Msg) (e : Event n Msg) : Config n State Msg :=
  { st := upd c.st e.1 (P.step e.1 (c.st e.1) e.2).1
    buf := fun x => (c.buf x - (if e.2 = some x then 1 else 0)) + count (P.step e.1 (c.st e.1) e.2).2 x }

theorem apply_st (c : Config n State Msg) (e : Event n Msg) (q : Fin n) :
    (apply P c e).st q = if q = e.1 then (P.step e.1 (c.st e.1) e.2).1 else c.st q := by
  simp [apply, upd]

theorem apply_st_ne (c : Config n State Msg) (e : Event n Msg) (q : Fin n) (h : q ≠ e.1) :
    (apply P c e).st q = c.st q := by
  simp [apply_st, h]

theorem apply_buf (c : Config n State Msg) (e : Event n Msg) (x : Msg) :
    (apply P c e).buf x =
      (c.buf x - (if e.2 = some x then 1 else 0)) + count (P.step e.1 (c.st e.1) e.2).2 x := rfl

def run : Config n State Msg → List (Event n Msg) → Config n State Msg
  | c, [] => c
  | c, e :: σ => run (apply P c e) σ

def applicable : Config n State Msg → List (Event n Msg) → Prop
  | _, [] => True
  | c, e :: σ => enabled P c e ∧ applicable (apply P c e) σ

@[simp] theorem run_nil (c : Config n State Msg) : run P c [] = c := rfl
@[simp] theorem run_cons (c : Config n State Msg) (e : Event n Msg) (σ : List (Event n Msg)) :
    run P c (e :: σ) = run P (apply P c e) σ := rfl
@[simp] theorem applicable_nil (c : Config n State Msg) : applicable P c [] := trivial
@[simp] theorem applicable_cons (c : Config n State Msg) (e : Event n Msg) (σ : List (Event n Msg)) :
    applicable P c (e :: σ) ↔ enabled P c e ∧ applicable P (apply P c e) σ := Iff.rfl

theorem run_append (c : Config n State Msg) (σ τ : List (Event n Msg)) :
    run P c (σ ++ τ) = run P (run P c σ) τ := by
  induction σ generalizing c with
  | nil => rfl
  | cons e σ ih => simp [ih]

theorem applicable_append (c : Config n State Msg) (σ τ : List (Event n Msg)) :
    applicable P c (σ ++ τ) ↔ applicable P c σ ∧ applicable P (run P c σ) τ := by
  induction σ generalizing c with
  | nil => simp
  | cons e σ ih => simp [ih, and_assoc]

theorem run_single (c : Config n State Msg) (e : Event n Msg) : run P c [e] = apply P c e := rfl

theorem applicable_single (c : Config n State Msg) (e : Event n Msg) :
    applicable P c [e] ↔ enabled P c e := by simp

def reach (c c' : Config n State Msg) : Prop :=
  ∃ σ, applicable P c σ ∧ run P c σ = c'

theorem reach_refl (c : Config n State Msg) : reach P c c := ⟨[], trivial, rfl⟩

theorem reach_trans {a b c : Config n State Msg} (h1 : reach P a b) (h2 : reach P b c) :
    reach P a c := by
  obtain ⟨σ, hσ, rfl⟩ := h1
  obtain ⟨τ, hτ, rfl⟩ := h2
  exact ⟨σ ++ τ, (applicable_append P _ _ _).2 ⟨hσ, hτ⟩, run_append P _ _ _⟩

theorem reach_of_run {c : Config n State Msg} {σ : List (Event n Msg)} (h : applicable P c σ) :
    reach P c (run P c σ) := ⟨σ, h, rfl⟩

theorem reach_apply {c : Config n State Msg} {e : Event n Msg} (h : enabled P c e) :
    reach P c (apply P c e) := ⟨[e], by simp [h], rfl⟩

def init (v : Fin n → Bool) : Config n State Msg :=
  { st := fun p => P.initSt p (v p), buf := fun _ => 0 }

def reach0 (c : Config n State Msg) : Prop := ∃ v, reach P (init P v) c

theorem reach0_of_reach {c c' : Config n State Msg} (h : reach0 P c) (h' : reach P c c') :
    reach0 P c' := by
  obtain ⟨v, hv⟩ := h
  exact ⟨v, reach_trans P hv h'⟩

def decided (c : Config n State Msg) (v : Bool) : Prop := ∃ p, P.out (c.st p) = some v

theorem decided_apply {c : Config n State Msg} {v : Bool} (h : decided P c v) (e : Event n Msg) :
    decided P (apply P c e) v := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p, ?_⟩
  rw [apply_st]
  by_cases hpe : p = e.1
  · subst hpe
    simp
    exact P.out_stable _ _ _ _ hp
  · simp [hpe, hp]

theorem decided_run {c : Config n State Msg} {v : Bool} (h : decided P c v) (σ : List (Event n Msg)) :
    decided P (run P c σ) v := by
  induction σ generalizing c with
  | nil => exact h
  | cons e σ ih => exact ih (decided_apply P h e)

theorem decided_reach {c c' : Config n State Msg} {v : Bool} (h : decided P c v) (hr : reach P c c') :
    decided P c' v := by
  obtain ⟨σ, _, rfl⟩ := hr
  exact decided_run P h σ

omit [DecidableEq Msg] in
theorem not_decided_init (v : Fin n → Bool) (w : Bool) : ¬ decided P (init P v) w := by
  rintro ⟨p, hp⟩
  simp [init, P.out_init] at hp

theorem enabled_apply_of_ne {c : Config n State Msg} {e e' : Event n Msg}
    (he : enabled P c e) (he' : enabled P c e') (hne : e' ≠ e) : enabled P (apply P c e') e := by
  obtain ⟨p, om⟩ := e
  cases om with
  | none => simp
  | some m =>
    obtain ⟨hd, hb⟩ := he
    refine ⟨hd, ?_⟩
    rw [apply_buf]
    have : (if e'.2 = some m then 1 else 0) = 0 := by
      obtain ⟨q, om'⟩ := e'
      cases om' with
      | none => simp
      | some m' =>
        simp only
        by_cases hm : m' = m
        · subst hm
          obtain ⟨hd', _⟩ := he'
          exact absurd (by rw [← hd, ← hd']) hne
        · simp [hm]
    omega

theorem enabled_run_of_notin {c : Config n State Msg} {e : Event n Msg} {σ : List (Event n Msg)}
    (he : enabled P c e) (hσ : applicable P c σ) (hn : ∀ f ∈ σ, f ≠ e) : enabled P (run P c σ) e := by
  induction σ generalizing c with
  | nil => exact he
  | cons f σ ih =>
    obtain ⟨hf, hσ⟩ := hσ
    exact ih (enabled_apply_of_ne P he hf (hn f (List.mem_cons_self ..))) hσ
      (fun g hg => hn g (List.mem_cons_of_mem _ hg))

theorem apply_comm {c : Config n State Msg} {e e' : Event n Msg} (hp : e.1 ≠ e'.1)
    (he : enabled P c e) (he' : enabled P c e') :
    apply P (apply P c e) e' = apply P (apply P c e') e := by
  obtain ⟨p, om⟩ := e
  obtain ⟨q, om'⟩ := e'
  simp only at hp
  have h1 : (apply P c (p, om)).st q = c.st q := apply_st_ne P c (p, om) q (Ne.symm hp)
  have h2 : (apply P c (q, om')).st p = c.st p := apply_st_ne P c (q, om') p hp
  apply Config.ext
  · funext r
    simp only [apply_st]
    by_cases hr1 : r = p
    · subst hr1
      simp [hp]
    · by_cases hr2 : r = q
      · subst hr2
        simp [Ne.symm hp]
      · simp [hr1, hr2]
  · funext x
    rw [apply_buf, apply_buf, apply_buf, apply_buf]
    simp only [h1, h2]
    by_cases ha : om = some x <;> by_cases hb : om' = some x
    · subst ha; subst hb
      exact absurd (he.1.symm.trans he'.1) hp
    · subst ha
      have := he.2
      simp [hb]
      omega
    · subst hb
      have := he'.2
      simp [ha]
      omega
    · simp [ha, hb]
      omega

end FLP
