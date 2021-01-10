/- Yair Gueta : 208624908 : t1
Exercises
1. Define the function Do_Twice, as described in Section 2.4.
2. Define the functions curry and uncurry, as described in Section 2.4.
3. Above, we used the example vec α n for vectors of elements of type α
   of length n. Declare a constant vec_add that could represent a 
   function that adds two vectors of natural numbers of the same length,
   and a constant vec_reverse that can represent a function that 
   reverses its argument. Use implicit arguments for parameters that 
   can be inferred. Declare some variables and check some expressions 
   involving the constants that you have declared.
4. Similarly, declare a constant matrix so that matrix α m n could
   represent the type of m by n matrices. Declare some constants to 
   represent functions on this type, such as matrix addition and 
   multiplication, and (using vec) multiplication of a matrix by a 
   vector. Once again, declare some variables and check some 
   expressions involving the constants that you have declared.-/

def double : ℕ → ℕ := λ x, x + x
def square : ℕ → ℕ := λ x, x * x
def do_twice : (ℕ → ℕ) → ℕ → ℕ := λ f x, f (f x)


-- chapter 2 ex 1: 
def Do_twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) := λ F f, F (F f)
#check Do_twice
#check Do_twice do_twice
#check Do_twice do_twice double
#eval Do_twice do_twice double 2


-- chapter 2 ex 2:
def curry (α β γ : Type*) (f : α × β → γ) : α → β → γ := λ a : α, (λ b : β, f (a,b))
def uncurry (α β γ : Type*) (f : α → β → γ) : α × β → γ := λ cr : α × β, f cr.1 cr.2

constants f g : ℕ → ℕ → ℕ 
constants f' g' : ℕ × ℕ → ℕ 
#check uncurry ℕ ℕ ℕ f
#check uncurry ℕ ℕ ℕ g
#check curry ℕ ℕ ℕ f'
#check curry ℕ ℕ ℕ g'

def sum1 (a b : ℕ ) : ℕ := a+b
def sum2 (t : ℕ×ℕ ) : ℕ := t.1+t.2

#check sum1
#check uncurry ℕ ℕ ℕ sum1
#eval sum1 3 7
#eval uncurry ℕ ℕ ℕ sum1 (3,7) 

#check sum2
#check curry ℕ ℕ ℕ sum2
#eval sum2 (3,7)
#eval curry ℕ ℕ ℕ sum2 3 7 


-- chapter 2 ex 3:
universe u
constant vec : Type u → ℕ → Type u

namespace vec
  constant empty : Π α : Type u, vec α 0
  constant cons :
    Π (α : Type u) (n : ℕ), α → vec α n → vec α (n + 1)
  constant append :
    Π (α : Type u) (n m : ℕ),  vec α m → vec α n → vec α (n + m)
  constant vec_add        : Π {α : Type} {n : ℕ} (v1 v2 : vec α n), vec α n
  constant vec_reverse    : Π {α : Type} {n : ℕ} (v : vec α n), vec α n
  
end vec



constants v1 v2 : vec ℕ 5
constants v3 v4 : vec ℕ 7
#check vec.vec_add
#check vec.vec_add v1
#check vec.vec_add v1 v2
-- #check vec.vec_add v1 v3 
-- #check vec.vec_add v4 v2
#check vec.vec_add v3 v4

#check vec.vec_reverse v1
#check vec.vec_reverse v3
-- #check vec.vec_reverse v1 v2
-- #check vec.vec_reverse v1 v3

