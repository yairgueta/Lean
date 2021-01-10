/- Yair Gueta : 208624908 : t4
    Exercise 4
-/


---- Question 1

--- Chapter 3:
namespace C3
variables p q r : Prop
-- First proof first try:
example : p ∨ false ↔ p := 
begin
  simp,
end

-- First proof 2nd try:
example : p ∨ false ↔ p := 
begin
  apply iff.intro,
    intro h,
      apply or.elim h,
      intro hp, 
      exact hp,
    intro hfalse,
    apply false.elim,
    exact hfalse,
  intro hp,
  exact or.inl hp,
end

example : p ∧ false ↔ false := 
begin
  apply iff.intro,
    intro h,
    exact h.right,
  intro hf,
  exact false.elim hf,
end

example : (p → q) → (¬q → ¬p) := 
begin
  intro h,
  intro hnq,
  apply not.intro,
  intro hp,
  exact absurd (h hp) hnq
end

end C3


--- Chapter 4:
namespace C4
open classical
variables (α : Type*) (p q : α → Prop)
variable r : Prop

example : α → ((∀ x : α, r) ↔ r) := 
begin
  intro ha,
  apply iff.intro,
    intro h,
    exact h ha,
  intro h,
  intro haa,
  exact h,
end

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
begin
  apply iff.intro,
    intro h,
    apply or.elim (em r),
      intro hr,
      exact or.inr hr,
    intro hnr,
    left,
      intro l,
      cases (h l) with a b,
        exact a,
      show p l, from absurd b hnr,
  intro h,
  intro hx,
  cases h with h₁ h₂,
    exact or.inl (h₁ hx),
  exact or.inr h₂,
end

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := 
begin
  apply iff.intro,
    intro h,
    intro hr,
    intro hx,
    exact (h hx) hr,
  intro h,
  intro hx,
  intro hr,
  exact (h hr) hx, 
end

end C4


--- Question 2:
example (p q r : Prop) (hp : p) :
(p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
by {repeat {split}, repeat{left, assumption}, repeat{right, left, assumption}, repeat{right, right, assumption}}