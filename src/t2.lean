/- Yair Gueta : 208624908 : t2
    Exercise 2
-/
open classical
variables p q r s : Prop


-- commutativity of ∧ and ∨
example : p ∨ q ↔ q ∨ p := 
iff.intro
  (assume hpq : p ∨ q,
    or.elim hpq
      (assume hp : p,
        show q ∨ p, from or.inr hp)
      (assume hq : q,
        show q ∨ p,  from or.inl hq))
  (assume hqp : q ∨ p,
    or.elim hqp
      (assume hq : q,
        show p ∨ q, from or.inr hq)
      (assume hp : p,
        show p ∨ q, from or.inl hp))

-- associativity of ∧ and ∨
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
iff.intro
  (assume hpq_r : (p ∨ q) ∨ r,
    hpq_r.elim
      (assume hpq : p ∨ q, 
        or.elim hpq
          (assume hp : p,
            show p ∨ (q ∨ r), from or.inl hp)
          (assume hq : q,
            have hqr : q ∨ r, from or.inl hq,
            show p ∨ (q ∨ r), from or.inr hqr))
      (assume hr : r,
        have hqr : q ∨ r, from or.inr hr,
        show p ∨ (q ∨ r), from or.inr hqr))
  (assume hp_qr : p ∨ (q ∨ r),
    hp_qr.elim
      (assume hp : p,
        have hpq : p ∨ q, from or.inl hp,
        show (p ∨ q) ∨ r, from or.inl hpq)
      (assume hqr : q ∨ r,
        hqr.elim
          (assume hq : q,
            have hpq : p ∨ q, from or.inr hq,
            show (p ∨ q) ∨ r, from or.inl hpq)
          (assume hr : r,
            show (p ∨ q) ∨ r, from or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
iff.intro
  (assume h : p ∧ (q ∨ r),
    have hp : p, from h.left,
    h.right.elim
      (assume hq : q,
        have hpq : p ∧ q, from ⟨hp, hq⟩,
        show (p ∧ q) ∨ (p ∧ r), from or.inl hpq)
      (assume hr : r,
        have hpr : p ∧ r, from ⟨hp, hr⟩,
        show (p ∧ q) ∨ (p ∧ r), from or.inr hpr)
  )
  (assume h : (p ∧ q) ∨ (p ∧ r),
    h.elim
      (assume hpq : p ∧ q,
        have hp : p, from hpq.left,
        have hq : q, from hpq.right,
        show p ∧ (q ∨ r), from ⟨hp, or.inl hq⟩)
      (assume hpr : p ∧ r,
        have hp : p, from hpr.left,
        have hr : r, from hpr.right,
        show p ∧ (q ∨ r), from ⟨hp, or.inr hr⟩)
  )

-- other properties
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
iff.intro 
  (assume h : ¬(p ∨ q),
    have np : ¬p, from 
      assume hp : p,
      show false, from h (or.inl hp),
    have nq : ¬q, from
      assume hq : q, 
      show false, from h (or.inr hq),
    show ¬p ∧ ¬q, from ⟨np, nq⟩)
  (assume h : ¬p ∧ ¬q,
    show ¬(p ∨ q), from
      assume hpq : p ∨ q,
      hpq.elim
        (assume hp : p, 
          show false, from h.left hp)
        (assume hq : q, 
          show false, from h.right hq)
  )

example : p ∧ false ↔ false := 
iff.intro
  (assume h : p ∧ false,
    show false, from h.right)
  (assume h : false, 
    show p ∧ false, from ⟨false.elim(h) , h⟩)

example : (p → q) → (¬q → ¬p) := 
assume hpq : p → q,
  assume hnq : ¬q,
    assume hp : p,
      have hq : q, from hpq hp,
      show false, from hnq hq



-- classical
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := 
assume h : (p → r ∨ s),
  by_cases
    (assume hp : p, 
      have hrs : r ∨ s, from h hp,
      show ((p → r) ∨ (p → s)), from 
        hrs.elim
          (assume hr : r, 
            show ((p → r) ∨ (p → s)), from or.inl (λ hhp : p, hr))
          (assume hs : s, 
            show ((p → r) ∨ (p → s)), from or.inr (λ hhp : p, hs))
    )
    (assume hnp : ¬p, 
      have hpr : p → r, from 
        (assume hp : p, 
        show r, from absurd hp hnp),
      show ((p → r) ∨ (p → s)), from or.inl hpr)

example : ¬(p ∧ q) → ¬p ∨ ¬q := 
assume h : ¬(p ∧ q),
  by_cases
    (assume hp : p,
      have hnq : ¬q, from 
        assume hq : q, 
        show false, from h ⟨hp, hq⟩,
      show ¬p ∨ ¬q, from or.inr hnq)
    (assume hnp : ¬p, or.inl hnp)

example : ¬(p → q) → p ∧ ¬q := 
assume h : ¬(p → q),
  by_cases
    (assume hp : p, 
      have hnq : ¬q, from 
        assume hq : q, 
        have hpq : p → q, from λ hhp : p, hq,
        show false, from h hpq,
      show p ∧ ¬q, from ⟨hp, hnq⟩)
    (assume hnp : ¬p, 
      have hpq : p → q, from 
        assume hp : p, absurd hp hnp,
      show p ∧ ¬q, from absurd hpq h)