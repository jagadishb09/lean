variables p q r : Prop

-- commutativity of ∧ and ∨
example : p ∨ q ↔ q ∨ p := 
iff.intro
(assume h : p ∨ q,
  or.elim h (λ hp, or.inr hp) (λ hq, or.inl hq))
(assume h : q ∨ p,
  or.elim h (λ hp, or.inr hp) (λ hq, or.inl hq))

example : p ∨ q ↔ q ∨ p := 
iff.intro
(assume h : p ∨ q,
  or.elim h (λ hp, or.inr hp) (λ hq, or.inl hq))
(assume h : q ∨ p,
  or.elim h (λ hp, or.inr hp) (λ hq, or.inl hq))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
iff.intro
(assume hpqr : (p ∧ q) ∧ r,
  have hpq : p ∧ q, from and.left hpqr,
  have hp : p, from and.left hpq,
  have hq : q, from and.right hpq,
  have hr : r, from and.right hpqr,
  show p ∧ (q ∧ r), from and.intro hp (and.intro hq hr))
(assume hpqr1 : p ∧ (q ∧ r),
  have hqr : q ∧ r, from and.right hpqr1,
  have hp : p, from and.left hpqr1,
  have hq : q, from and.left hqr,
  have hr : r, from and.right hqr,
  show (p ∧ q) ∧ r, from (and.intro (and.intro hp hq) hr))


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
iff.intro
(assume hpqr : (p ∨ q) ∨ r,
hpqr.elim
 (assume hpq : p ∨ q , or.inr hpq)
 (assume hpq1 : r , or.inr hpq1)
)
(assume hpqr1 : p ∨ (q ∨ r),
sorry
)

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ false ↔ p := sorry
example : p ∧ false ↔ false := sorry
example : (p → q) → (¬q → ¬p) := sorry

