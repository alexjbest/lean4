axiom q : Nat → Prop
axiom p : Nat → Prop
axiom q_eq_p : q = p

example (h : ¬ q 0) : ¬ p 0 := by
  trace_state
  /-
     h : ¬ q 0
     ⊢ ¬ p 0
  -/
  simp [h] at h
  /-
     h : ¬ q 0
     ⊢ ¬ p 0
  -/
  trace_state
  rw [← q_eq_p]
  assumption
