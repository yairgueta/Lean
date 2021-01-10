/- Yair Gueta : 208624908 : t3
    Exercise 3
-/
import data.nat.basic
import data.real.basic

variables (α : Type*) (p q : α → Prop)

---- Q1 ----
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
iff.intro
    (assume h :∀ x, p x ∧ q x,
        have h₁ : ∀ x, p x, from 
            assume y,
            show p y, from (h y).left,
        have ∀ x, q x, from
            assume k,
            show q k, from (h k).right,
        ⟨h₁, this⟩)
    (assume h : (∀ x, p x) ∧ (∀ x, q x),
        assume z,
            ⟨h.left z, h.right z⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
assume h₁ : ∀ x, p x → q x,
assume h₂ : ∀ x, p x,
assume y,
    have hpq : p y → q y, from h₁ y,
    hpq (h₂ y)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
assume h : (∀ x, p x) ∨ (∀ x, q x),
assume x,
    h.elim
        (assume : (∀ x, p x),
            or.inl (this x))
        (assume : (∀ x, q x),
            or.inr (this x))


---- Q2 ----
open classical
variable r : Prop

example : α → ((∀ x : α, r) ↔ r) := 
assume y: α,
iff.intro
    (assume : (∀ x : α, r), this y)
    (assume hr : r, 
        assume y : α, hr)


example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
iff.intro
    (assume h : ∀ x, p x ∨ r,
     by_cases
     (assume hr : r, 
        show (∀ x, p x) ∨ r, from or.inr hr)
     (assume hnr : ¬r, 
        suffices (∀ x, p x), from or.inl this,
        assume y, (h y).elim (assume hpy : p y, hpy)(assume hr:r, absurd hr hnr)
        ))
    (assume h : (∀ x, p x) ∨ r,
        h.elim
        (assume ah : ∀ x, p x,
         assume y, or.inl (ah y))
        (assume hr : r, 
         assume y, or.inr hr))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := 
iff.intro
  (assume h : ∀ x, r → p x,
   assume hr : r, assume y, (h y) hr)
  (assume h : r → ∀ x, p x, assume y, assume hr : r, h hr y)


---- Q3 ----
variables (men : Type*) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
  false := 
  have hb : shaves barber barber ↔ ¬ shaves barber barber, from h barber,
  by_cases
    (assume hsb : shaves barber barber, hb.elim_left hsb hsb)
    (assume hnsb : ¬ shaves barber barber, hnsb (hb.elim_right hnsb))

---- Q4 ----
namespace Q4
    def even (n : ℕ) : Prop := 2 ∣ n

    def prime (n : ℕ) : Prop := ∀ (m : ℕ), (m > 1) → (m < n) → ¬ ∃(l : ℕ), m*l = n 

    def infinitely_many_primes : Prop := ∀ (n : ℕ), ∃ (p : ℕ), p > n → prime p

    def Fermat_prime (n : ℕ) : Prop := ∃ (m : ℕ), prime n ↔ (n = 2^(2^m)+1)

    def infinitely_many_Fermat_primes : Prop := ∀ (n : ℕ), ∃ (p : ℕ), p > n → Fermat_prime p

    def goldbach_conjecture : Prop := 
        ∀ (n : ℕ), (even n) → (n > 2) → (∃ (m l : ℕ ), prime m → prime l → m+l=n)

    def Goldbach's_weak_conjecture : Prop := 
        ∀ (n : ℕ), (even n) → (n > 5) → (∃ (m₁ m₂ m₃ : ℕ ), 
            prime m₁ → prime m₂ → prime m₃ → m₁+m₂+m₃=n)

    def Fermat's_last_theorem : Prop := ∀ (n : ℕ), n > 2 → ¬ (∃ (x y z : ℕ), x^n+y^n=z^n)
end Q4


---- Q6 ----
variables log exp     : real → real
variable  log_exp_eq : ∀ x, log (exp x) = x
variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable  exp_pos    : ∀ x, exp x > 0
variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

-- this ensures the assumptions are available in tactic proofs
include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : real) :
  exp (x + y + z) = exp x * exp y * exp z :=
by rw [exp_add, exp_add]

example (y : real) (h : y > 0)  : exp (log y) = y :=
exp_log_eq h

theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y :=
    by rw [←log_exp_eq(log x + log y),exp_add,exp_log_eq hx,exp_log_eq hy]

    
