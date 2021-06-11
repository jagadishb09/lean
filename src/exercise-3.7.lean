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
      show p ∧ (q ∨ r), from ⟨hp, or.inl hq⟩ -- ⟨
    )  
    (assume hpr : p ∧ r,
       have hp : p, from hpr.left,
       have hr : r, from hpr.right,
       show p ∧ (q ∨ r), from ⟨hp, or.inr hr⟩))

--- new       
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

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
begin
apply iff.intro,
{
  intro hpq,
  split,
  {
    intro hp,
    apply hpq, left, exact hp,
  },
  {
    intro hq,
    apply hpq, right, exact hq,
  },
},
{
  intro hpq,
  cases hpq with hnp hnq,
   {
     intro hpq1,
     cases hpq1 with hp1 hq1,
     {
       apply hnp, exact hp1,
     },
     apply hnq, exact hq1,
   },
},
end  

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
begin
intro hnpq,
cases hnpq with hnp hnq,
{
  intro hnpq1, -- what is this doing?
  apply hnp, exact hnpq1.left,
},
intro hnpq2,
apply hnq, exact hnpq2.right,
end

example : ¬(p ∧ ¬p) := 
begin
intro hnp,
cases hnp,
apply hnp_right, exact hnp_left,
end

example : p ∧ ¬q → ¬(p → q) := 
begin
intro hpq,
intro hinpq,
have hp : p, from and.left hpq,
cases hpq,
apply hpq_right, apply hinpq, apply hp,
end

example : ¬p → (p → q) := 
begin
  intro hnp,
  intro hnp1,
  contradiction,
end

example : (¬p ∨ q) → (p → q) := 
begin
  intro hpq,
  intro hpq1,
  cases hpq,
  {
    contradiction
  },
  exact hpq,
end

example : p ∨ false ↔ p := 
begin
  apply iff.intro,
  {
    intro hpf,
    cases hpf,
    exact hpf,
    contradiction,
  },
  {
    intro hp,
    show p ∨ false, from or.inl hp, -- how is it true?
  },
end


example : p ∧ false ↔ false := 
begin
apply iff.intro,
intro hpf,
have hp : p, from hpf.left,
show false, from hpf.right,
intro hpf1,
cases hpf1, -- what is this doing?
end

theorem t1 : p → q → p := λ hp : p, λ hq : q, hp

example : (p → q) → (¬q → ¬p) := 
begin
intro hpq,
intro hpq1,
have hq : q, apply hpq,
 { 
    --have hp : p, from (and.intro t1, hpq)
 },
contradiction,

end

