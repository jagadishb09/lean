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
   or.elim hpqr
      (assume hpq : p ∨ q,
          or.elim hpq
           (assume hp : p,
              show p ∨ (q ∨ r), from or.inl hp)
            (assume hq : q,
              have hqr : q ∨ r, from or.inl hq,
              show p ∨ (q ∨ r), from or.inr hqr))
      (assume hr : r,
        have hqr : q ∨ r, from or.inr hr,
        show p ∨ (q ∨ r), from or.inr hqr)
)
(assume hpqr1 : p ∨ (q ∨ r), 
   or.elim hpqr1
      (assume hp : p,
        have hpq : p ∨ q, from or.inl hp,
        show (p ∨ q) ∨ r, from or.inl hpq)
      (assume hqr : q ∨ r,
        or.elim hqr
          (assume hq : q,
            have hpq : p ∨ q, from or.inr hq,
            show (p ∨ q) ∨ r, from or.inl hpq)
          (assume hr : r,
            show (p ∨ q) ∨ r, from or.inr hr))
)

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
iff.intro
(assume hpqr: p ∧ (q ∨ r), 
  have hp : p, from hpqr.left,
  or.elim (hpqr.right)
    (assume hq : q,
      have hpq : p ∧ q, from and.intro hp hq,
      show (p ∧ q) ∨ (p ∧ r), from or.inl hpq
    )
    (assume hr : r,
      have hpr : p ∧ r, from and.intro hp hr,
      show (p ∧ q) ∨ (p ∧ r), from or.inr hpr
    )
)
(assume hpqr1: (p ∧ q) ∨ (p ∧ r), 
  or.elim hpqr1
    (assume hpq: p ∧ q, 
      have hp : p, from hpq.left,
      have hq : q, from hpq.right,
      show p ∧ (q ∨ r), from ⟨hp, or.inl hq⟩
    )  
    (assume hpr : p ∧ r,
       have hp : p, from hpr.left,
       have hr : r, from hpr.right,
       show p ∧ (q ∨ r), from ⟨hp, or.inr hr⟩))
       
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
iff.intro
(assume hpqr: p ∨ (q ∧ r), 
  or.elim hpqr
  (sorry)
  (sorry)
)
(assume hpqr1: (p ∨ q) ∧ (p ∨ r), 
  sorry
)

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
begin
apply iff.intro,
{
  intro hpqr,
  intro hpq,
  apply hpqr, from hpq.left, from hpq.right
},
{
 intro hpqr,
 intro hp,
 intro hq,
 apply hpqr, from (and.intro hp hq)
},
end



example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
begin
apply iff.intro,
{
  intro hpqr,
  split,
   {
     intro hp,
     apply hpqr, left, exact hp
   },
   {
     intro hq,
     apply hpqr, right, exact hq
   },
},
{
 intro hprqr,
 intro hpq,
 cases hprqr with hpr hqr,
        cases hpq with hp hq,
 {
   apply hpr, exact hp,
 },
 {
   apply hqr, exact hq,
 },
},
end
-- done

--working
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
begin
apply iff.intro,
{
  intro hpq,
  split,
  {
    intro hp,
    show false, from absurd hp hpq,
  },
  {
    sorry
  },
},
{
  sorry
},
end  
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ false ↔ p := sorry
example : p ∧ false ↔ false := sorry
example : (p → q) → (¬q → ¬p) := sorry

