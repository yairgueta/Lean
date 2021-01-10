/- Yair Gueta : 208624908 : t4
    Exercise 4
-/
import data.int.basic

variable  U : Type
variables R : U → U → Prop

-- Question 9:
example : (∃ x, ∀ y, R x y) → ∀ y, ∃ x, R x y :=
begin
  intro,
  cases a with x,
  intro,
  existsi x, exact a_h y
end


-- Question 10:
theorem foo {A : Type} {a b c : A} : a = b → c = b → a = c :=
begin
  intros, exact a_1.trans a_2.symm,
end 

-- notice that you can now use foo as a rule. The curly braces mean that
-- you do not have to give A, a, b, or c

section
  variable A : Type
  variables a b c : A

  example (h1 : a = b) (h2 : c = b) : a = c :=
  foo h1 h2
end

section
  variable {A : Type}
  variables {a b c : A}

  -- replace the sorry with a proof, using foo and rfl, without using eq.symm.
  theorem my_symm (h : b = a) : a = b :=
  by exact foo (eq.refl a) h
  
  -- now use foo and my_symm to prove transitivity
  theorem my_trans (h1 : a = b) (h2 : b = c) : a = c :=
  by exact foo h1 (my_symm h2)
end

-- Question 11:
-- these are the axioms for a commutative ring

#check @add_assoc
#check @add_comm
#check @add_zero
#check @zero_add
#check @mul_assoc
#check @mul_comm
#check @mul_one
#check @one_mul
#check @left_distrib
#check @right_distrib
#check @add_left_neg
#check @add_right_neg
#check @sub_eq_add_neg

variables x y z : int

theorem t1 : x - x = 0 :=
calc
x - x = x + -x : by rw sub_eq_add_neg
    ... = 0      : by rw add_right_neg

theorem t2 (h : x + y = x + z) : y = z :=
calc
y     = 0 + y        : by rw zero_add
    ... = (-x + x) + y : by rw add_left_neg
    ... = -x + (x + y) : by rw add_assoc
    ... = -x + (x + z) : by rw h
    ... = (-x + x) + z : by rw add_assoc
    ... = 0 + z        : by rw add_left_neg
    ... = z            : by rw zero_add

theorem t3 (h : x + y = z + y) : x = z :=
calc
x     = x + 0        : by rw add_zero
    ... = x + (y + -y) : by rw ← add_right_neg
    ... = (x + y) + -y : by rw add_assoc
    ... = (z + y) + -y : by rw h
    ... = z + (y + -y) : by rw add_assoc
    ... = z + 0        : by rw add_right_neg
    ... = z            : by rw add_zero

theorem t4 (h : x + y = 0) : x = -y :=
calc
x     = x + 0        : by rw add_zero
    ... = x + (y + -y) : by rw add_right_neg
    ... = (x + y) + -y : by rw add_assoc
    ... = 0 + -y       : by rw h
    ... = -y           : by rw zero_add

theorem t5 : x * 0 = 0 :=
have h1 : x * 0 + x * 0 = x * 0 + 0, from
calc
    x * 0 + x * 0 = x * (0 + 0) : by rw mul_add
            ... = x * 0       : by rw add_zero
            ... = x * 0 + 0   : by rw add_zero,
show x * 0 = 0, from t2 _ _ _ h1

theorem t6 : x * (-y) = -(x * y) :=
have h1 : x * (-y) + x * y = 0, from
calc
    x * (-y) + x * y = x * (-y + y) : by rw mul_add
                ... = x * 0        : by rw add_left_neg
                ... = 0            : by rw t5 x,
show x * (-y) = -(x * y), from t4 _ _ h1

theorem t7 : x + x = 2 * x :=
calc
x + x = 1 * x + 1 * x : by rw one_mul
    ... = (1 + 1) * x   : by rw add_mul
    ... = 2 * x         : rfl