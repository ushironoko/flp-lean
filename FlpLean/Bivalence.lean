import FlpLean.Model

namespace FLP

variable {n : Nat} {State Msg : Type} [DecidableEq Msg] (P : Protocol n State Msg)

def canDecide (c : Config n State Msg) (v : Bool) : Prop :=
  ∃ σ, applicable P c σ ∧ decided P (run P c σ) v

def bivalent (c : Config n State Msg) : Prop := canDecide P c true ∧ canDecide P c false

def valent (c : Config n State Msg) (v : Bool) : Prop :=
  ∀ σ, applicable P c σ → ∀ w, decided P (run P c σ) w → w = v

def FinTerm : Prop :=
  ∀ c, reach0 P c → ∀ p : Fin n,
    ∃ τ, applicable P c τ ∧ (∀ f ∈ τ, f.1 ≠ p) ∧ ∃ w, decided P (run P c τ) w

def Nontrivial : Prop := ∀ v : Bool, ∃ w : Fin n → Bool, canDecide P (init P w) v

theorem canDecide_of_decided {c : Config n State Msg} {v : Bool} (h : decided P c v) :
    canDecide P c v := ⟨[], trivial, h⟩

theorem canDecide_of_reach {c c' : Config n State Msg} {v : Bool} (h : reach P c c')
    (h' : canDecide P c' v) : canDecide P c v := by
  obtain ⟨σ, hσ, rfl⟩ := h
  obtain ⟨τ, hτ, hd⟩ := h'
  exact ⟨σ ++ τ, (applicable_append P _ _ _).2 ⟨hσ, hτ⟩, by rw [run_append]; exact hd⟩

theorem valent_of_reach {c c' : Config n State Msg} {v : Bool} (h : reach P c c')
    (h' : valent P c v) : valent P c' v := by
  intro τ hτ w hw
  obtain ⟨σ, hσ, rfl⟩ := h
  exact h' (σ ++ τ) ((applicable_append P _ _ _).2 ⟨hσ, hτ⟩) w (by rw [run_append]; exact hw)

theorem bivalent_iff (c : Config n State Msg) : bivalent P c ↔ ∀ v, canDecide P c v := by
  constructor
  · rintro ⟨h1, h0⟩ v
    cases v <;> assumption
  · intro h
    exact ⟨h true, h false⟩

theorem valent_of_not_bivalent {c : Config n State Msg} {v : Bool} (hb : ¬ bivalent P c)
    (h : canDecide P c v) : valent P c v := by
  intro σ hσ w hw
  refine Classical.byContradiction fun hne => ?_
  have hcw : canDecide P c w := ⟨σ, hσ, hw⟩
  apply hb
  rw [bivalent_iff]
  intro u
  cases u <;> cases v <;> cases w <;> simp_all

theorem exists_valent {c : Config n State Msg} (hT : FinTerm P) (hn : 0 < n) (hr : reach0 P c)
    (hb : ¬ bivalent P c) : ∃ v, valent P c v := by
  obtain ⟨τ, hτ, -, w, hw⟩ := hT c hr ⟨0, hn⟩
  exact ⟨w, valent_of_not_bivalent P hb ⟨τ, hτ, hw⟩⟩

theorem valent_unique {c : Config n State Msg} (hT : FinTerm P) (hn : 0 < n) (hr : reach0 P c)
    {v w : Bool} (hv : valent P c v) (hw : valent P c w) : v = w := by
  obtain ⟨τ, hτ, -, u, hu⟩ := hT c hr ⟨0, hn⟩
  rw [← hv τ hτ u hu, ← hw τ hτ u hu]

theorem valent_of_not_valent {c : Config n State Msg} (hT : FinTerm P) (hn : 0 < n)
    (hr : reach0 P c) (hb : ¬ bivalent P c) {v : Bool} (h : ¬ valent P c v) :
    valent P c (!v) := by
  obtain ⟨w, hw⟩ := exists_valent P hT hn hr hb
  have : w = !v := by cases v <;> cases w <;> simp_all
  subst this
  exact hw

theorem exists_first_mem {α : Type} {a : α} {l : List α} (h : a ∈ l) :
    ∃ s t, l = s ++ a :: t ∧ a ∉ s := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.1 h with rfl | h'
    · exact ⟨[], l, rfl, by simp⟩
    · by_cases hab : b = a
      · subst hab
        exact ⟨[], l, rfl, by simp⟩
      · obtain ⟨s, t, rfl, hs⟩ := ih h'
        exact ⟨b :: s, t, rfl, by simp [hs, Ne.symm hab]⟩

theorem exists_switch {α : Type} (Q : List α → Prop) (l : List α) (h0 : Q []) (hl : ¬ Q l) :
    ∃ s a t, l = s ++ a :: t ∧ Q s ∧ ¬ Q (s ++ [a]) := by
  induction l generalizing Q with
  | nil => exact absurd h0 hl
  | cons b l ih =>
    by_cases hb : Q [b]
    · obtain ⟨s, a, t, rfl, hs, hsa⟩ := ih (fun t => Q (b :: t)) hb hl
      exact ⟨b :: s, a, t, rfl, hs, hsa⟩
    · exact ⟨[], b, l, rfl, h0, hb⟩

theorem run_apply_comm {c : Config n State Msg} {e : Event n Msg} {τ : List (Event n Msg)}
    (he : enabled P c e) (hτ : applicable P c τ) (hp : ∀ f ∈ τ, f.1 ≠ e.1) :
    applicable P (apply P c e) τ ∧ run P (apply P c e) τ = apply P (run P c τ) e := by
  induction τ generalizing c with
  | nil => exact ⟨trivial, rfl⟩
  | cons f τ ih =>
    obtain ⟨hf, hτ⟩ := hτ
    have hfe : f.1 ≠ e.1 := hp f (List.mem_cons_self ..)
    have hne : f ≠ e := fun h => hfe (h ▸ rfl)
    have he' : enabled P (apply P c f) e := enabled_apply_of_ne P he hf hne
    have hf' : enabled P (apply P c e) f := enabled_apply_of_ne P hf he (Ne.symm hne)
    have hcomm : apply P (apply P c e) f = apply P (apply P c f) e :=
      apply_comm P (Ne.symm hfe) he hf
    obtain ⟨ih1, ih2⟩ := ih he' hτ (fun g hg => hp g (List.mem_cons_of_mem _ hg))
    refine ⟨?_, ?_⟩
    · show enabled P (apply P c e) f ∧ applicable P (apply P (apply P c e) f) τ
      rw [hcomm]
      exact ⟨hf', ih1⟩
    · simp only [run_cons]
      rw [hcomm]
      exact ih2

/-- FLP Lemma 3: 両価な配置 c と c で有効なイベント e に対し、
e を含むスケジュールで再び両価な配置に到達できる。 -/
theorem bivalent_step (hT : FinTerm P) (hn : 0 < n) {c : Config n State Msg} (hr : reach0 P c)
    (hb : bivalent P c) (e : Event n Msg) (he : enabled P c e) :
    ∃ σ, applicable P c σ ∧ e ∈ σ ∧ bivalent P (run P c σ) := by
  refine Classical.byContradiction fun hcon => ?_
  have H : ∀ σ, applicable P c σ → (∀ f ∈ σ, f ≠ e) → ¬ bivalent P (run P c (σ ++ [e])) := by
    intro σ hσ hfree hbiv
    exact hcon ⟨σ ++ [e],
      (applicable_append P _ _ _).2 ⟨hσ, by simpa using enabled_run_of_notin P he hσ hfree⟩,
      by simp, hbiv⟩
  have hD : ∀ σ, applicable P c σ → (∀ f ∈ σ, f ≠ e) → reach0 P (run P c (σ ++ [e])) := by
    intro σ hσ hfree
    exact reach0_of_reach P hr (reach_of_run P
      ((applicable_append P _ _ _).2 ⟨hσ, by simpa using enabled_run_of_notin P he hσ hfree⟩))
  have step1 : ∀ v, ∃ σ, applicable P c σ ∧ (∀ f ∈ σ, f ≠ e) ∧
      valent P (run P c (σ ++ [e])) v := by
    intro v
    obtain ⟨ρ, hρ, hdec⟩ := (bivalent_iff P c).1 hb v
    by_cases hmem : e ∈ ρ
    · obtain ⟨s, t, rfl, hs⟩ := exists_first_mem hmem
      have hs' : ∀ f ∈ s, f ≠ e := fun f hf h => hs (h ▸ hf)
      have happ := (applicable_append P _ _ _).1 hρ
      have hcd' : canDecide P (run P c (s ++ [e])) v := by
        refine ⟨t, ?_, ?_⟩
        · rw [run_append]
          exact happ.2.2
        · rw [← run_append, List.append_assoc]
          exact hdec
      exact ⟨s, happ.1, hs', valent_of_not_bivalent P (H s happ.1 hs') hcd'⟩
    · have hfree : ∀ f ∈ ρ, f ≠ e := fun f hf h => hmem (h ▸ hf)
      have hcd' : canDecide P (run P c (ρ ++ [e])) v :=
        canDecide_of_decided P (by rw [run_append]; exact decided_run P hdec [e])
      exact ⟨ρ, hρ, hfree, valent_of_not_bivalent P (H ρ hρ hfree) hcd'⟩
  obtain ⟨v0, hv0⟩ : ∃ v0, valent P (run P c ([] ++ [e])) v0 :=
    exists_valent P hT hn (hD [] trivial (by simp)) (H [] trivial (by simp))
  obtain ⟨σ1, hσ1, hfree1, hval1⟩ := step1 (!v0)
  have hnotQ : ¬ valent P (run P c (σ1 ++ [e])) v0 := by
    intro h
    have := valent_unique P hT hn (hD σ1 hσ1 hfree1) h hval1
    cases v0 <;> simp at this
  obtain ⟨τ, e', rest, rfl, hQτ, hQτe'⟩ :=
    exists_switch (fun τ => valent P (run P c (τ ++ [e])) v0) σ1 hv0 hnotQ
  have hτapp : applicable P c τ := ((applicable_append P _ _ _).1 hσ1).1
  have hrest : applicable P (run P c τ) (e' :: rest) := ((applicable_append P _ _ _).1 hσ1).2
  have he'en : enabled P (run P c τ) e' := hrest.1
  have hτfree : ∀ f ∈ τ, f ≠ e := fun f hf => hfree1 f (by simp [hf])
  have he'ne : e' ≠ e := hfree1 e' (by simp)
  have hτe'free : ∀ f ∈ τ ++ [e'], f ≠ e := by
    intro f hf
    rcases List.mem_append.1 hf with h | h
    · exact hτfree f h
    · simp at h
      subst h
      exact he'ne
  have hτe'app : applicable P c (τ ++ [e']) :=
    (applicable_append P _ _ _).2 ⟨hτapp, by simp [he'en]⟩
  have hc0r : reach0 P (run P c τ) := reach0_of_reach P hr (reach_of_run P hτapp)
  have hee : enabled P (run P c τ) e := enabled_run_of_notin P he hτapp hτfree
  have hee' : enabled P (apply P (run P c τ) e') e := enabled_apply_of_ne P hee he'en he'ne
  have hval0 : valent P (apply P (run P c τ) e) v0 := by simpa [run_append] using hQτ
  have hval1' : valent P (apply P (apply P (run P c τ) e') e) (!v0) := by
    have := valent_of_not_valent P hT hn (hD (τ ++ [e']) hτe'app hτe'free)
      (H (τ ++ [e']) hτe'app hτe'free) hQτe'
    simpa [run_append] using this
  have hd1r : reach0 P (apply P (apply P (run P c τ) e') e) :=
    reach0_of_reach P hc0r (reach_trans P (reach_apply P he'en) (reach_apply P hee'))
  by_cases hpp : e'.1 = e.1
  · obtain ⟨ρ, hρ, hρfree, w, hw⟩ := hT (run P c τ) hc0r e.1
    obtain ⟨hρe, hrun_e⟩ := run_apply_comm P hee hρ hρfree
    have hρ' : ∀ f ∈ ρ, f.1 ≠ e'.1 := by rw [hpp]; exact hρfree
    obtain ⟨hρe', hrun_e'⟩ := run_apply_comm P he'en hρ hρ'
    obtain ⟨hρee', hrun_ee'⟩ := run_apply_comm P hee' hρe' hρfree
    have hw1 : w = v0 := hval0 ρ hρe w (by rw [hrun_e]; exact decided_apply P hw e)
    have hw2 : w = !v0 := hval1' ρ hρee' w
      (by rw [hrun_ee', hrun_e']; exact decided_apply P (decided_apply P hw e') e)
    rw [hw1] at hw2
    cases v0 <;> simp at hw2
  · have hcomm : apply P (apply P (run P c τ) e) e' = apply P (apply P (run P c τ) e') e :=
      apply_comm P (Ne.symm hpp) hee he'en
    have he'd0 : enabled P (apply P (run P c τ) e) e' :=
      enabled_apply_of_ne P he'en hee (Ne.symm he'ne)
    have hreach : reach P (apply P (run P c τ) e) (apply P (apply P (run P c τ) e') e) := by
      rw [← hcomm]
      exact reach_apply P he'd0
    have := valent_unique P hT hn hd1r (valent_of_reach P hreach hval0) hval1'
    cases v0 <;> simp at this

def agreeExcept (p : Fin n) (c c' : Config n State Msg) : Prop :=
  c.buf = c'.buf ∧ ∀ q, q ≠ p → c.st q = c'.st q

omit [DecidableEq Msg] in
theorem enabled_of_agree {p : Fin n} {c c' : Config n State Msg} (h : agreeExcept p c c')
    (e : Event n Msg) : enabled P c e ↔ enabled P c' e := by
  obtain ⟨q, om⟩ := e
  cases om with
  | none => simp
  | some m => simp [h.1]

theorem agree_apply {p : Fin n} {c c' : Config n State Msg} (h : agreeExcept p c c')
    {e : Event n Msg} (hp : e.1 ≠ p) : agreeExcept p (apply P c e) (apply P c' e) := by
  have hs : c.st e.1 = c'.st e.1 := h.2 e.1 hp
  refine ⟨?_, ?_⟩
  · funext x
    rw [apply_buf, apply_buf, hs, h.1]
  · intro q hq
    rw [apply_st, apply_st, hs]
    by_cases hqe : q = e.1
    · simp [hqe]
    · simp [hqe, h.2 q hq]

theorem agree_run {p : Fin n} {c c' : Config n State Msg} (h : agreeExcept p c c')
    {σ : List (Event n Msg)} (hσ : ∀ f ∈ σ, f.1 ≠ p) :
    agreeExcept p (run P c σ) (run P c' σ) := by
  induction σ generalizing c c' with
  | nil => exact h
  | cons f σ ih =>
    exact ih (agree_apply P h (hσ f (List.mem_cons_self ..)))
      (fun g hg => hσ g (List.mem_cons_of_mem _ hg))

theorem applicable_of_agree {p : Fin n} {c c' : Config n State Msg} (h : agreeExcept p c c')
    {σ : List (Event n Msg)} (hσ : ∀ f ∈ σ, f.1 ≠ p) (ha : applicable P c σ) :
    applicable P c' σ := by
  induction σ generalizing c c' with
  | nil => trivial
  | cons f σ ih =>
    obtain ⟨hf, ha⟩ := ha
    exact ⟨(enabled_of_agree P h f).1 hf,
      ih (agree_apply P h (hσ f (List.mem_cons_self ..)))
        (fun g hg => hσ g (List.mem_cons_of_mem _ hg)) ha⟩

theorem st_run_of_free {p : Fin n} {c : Config n State Msg} {σ : List (Event n Msg)}
    (hσ : ∀ f ∈ σ, f.1 ≠ p) : (run P c σ).st p = c.st p := by
  induction σ generalizing c with
  | nil => rfl
  | cons f σ ih =>
    rw [run_cons, ih (fun g hg => hσ g (List.mem_cons_of_mem _ hg)),
      apply_st_ne P c f p (Ne.symm (hσ f (List.mem_cons_self ..)))]

omit [DecidableEq Msg] in
theorem decided_of_agree {p : Fin n} {c c' : Config n State Msg} {v : Bool}
    (h : agreeExcept p c c') (hc : P.out (c.st p) = none) (hd : decided P c v) :
    decided P c' v := by
  obtain ⟨q, hq⟩ := hd
  have hqp : q ≠ p := by
    intro hqp
    subst hqp
    rw [hc] at hq
    cases hq
  exact ⟨q, by rw [← h.2 q hqp]; exact hq⟩

theorem valent_init_adj (hT : FinTerm P) {v v' : Fin n → Bool} (p : Fin n)
    (hvv : ∀ q, q ≠ p → v q = v' q) (hnb : ¬ bivalent P (init P v')) {w : Bool}
    (hw : valent P (init P v) w) : valent P (init P v') w := by
  obtain ⟨τ, hτ, hfree, u, hu⟩ := hT (init P v) ⟨v, reach_refl P _⟩ p
  have hagree0 : agreeExcept p (init P v) (init P v') :=
    ⟨rfl, fun q hq => by simp [init, hvv q hq]⟩
  have hagree := agree_run P hagree0 hfree
  have hpst : P.out ((run P (init P v) τ).st p) = none := by
    rw [st_run_of_free P hfree]
    simp [init, P.out_init]
  have hu' : decided P (run P (init P v') τ) u := decided_of_agree P hagree hpst hu
  have hτ' : applicable P (init P v') τ := applicable_of_agree P hagree0 hfree hτ
  have huw : u = w := hw τ hτ u hu
  subst huw
  exact valent_of_not_bivalent P hnb ⟨τ, hτ', hu'⟩

def mix (v0 v1 : Fin n → Bool) (k : Nat) : Fin n → Bool :=
  fun i => if i.val < k then v1 i else v0 i

theorem mix_zero (v0 v1 : Fin n → Bool) : mix v0 v1 0 = v0 := by
  funext i
  simp [mix]

theorem mix_n (v0 v1 : Fin n → Bool) : mix v0 v1 n = v1 := by
  funext i
  simp [mix, i.isLt]

theorem mix_adj (v0 v1 : Fin n → Bool) (k : Nat) :
    ∀ q : Fin n, q.val ≠ k → mix v0 v1 k q = mix v0 v1 (k + 1) q := by
  intro q hq
  simp only [mix]
  by_cases h : q.val < k
  · simp [h, Nat.lt_succ_of_lt h]
  · simp [h, show ¬ q.val < k + 1 by omega]

theorem valent_init_chain (hT : FinTerm P) (hall : ∀ v, ¬ bivalent P (init P v))
    (v0 v1 : Fin n → Bool) {w : Bool} (hw : valent P (init P v0) w) :
    ∀ k, valent P (init P (mix v0 v1 k)) w := by
  intro k
  induction k with
  | zero =>
    rw [mix_zero]
    exact hw
  | succ k ih =>
    by_cases hk : k < n
    · exact valent_init_adj P hT ⟨k, hk⟩
        (fun q hq => mix_adj v0 v1 k q (fun h => hq (Fin.ext h))) (hall _) ih
    · have : mix v0 v1 (k + 1) = mix v0 v1 k := by
        funext i
        have := i.isLt
        simp only [mix]
        simp [show i.val < k by omega, show i.val < k + 1 by omega]
      rw [this]
      exact ih

/-- FLP Lemma 2: 両価な初期配置が存在する。 -/
theorem exists_bivalent_init (hT : FinTerm P) (hNT : Nontrivial P) :
    ∃ v, bivalent P (init P v) := by
  refine Classical.byContradiction fun hcon => ?_
  have hall : ∀ v, ¬ bivalent P (init P v) := fun v hv => hcon ⟨v, hv⟩
  obtain ⟨v0, h0⟩ := hNT false
  obtain ⟨v1, h1⟩ := hNT true
  have hval0 : valent P (init P v0) false := valent_of_not_bivalent P (hall v0) h0
  have hval1 := valent_init_chain P hT hall v0 v1 hval0 n
  rw [mix_n] at hval1
  obtain ⟨σ, hσ, hd⟩ := h1
  have := hval1 σ hσ true hd
  simp at this

end FLP
