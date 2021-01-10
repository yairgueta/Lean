namespace hidden


open nat

def pred (n : nat) : nat :=
nat.rec_on n
	(zero)
	(λ n pred_n : nat, n)

#reduce pred (succ zero)

example (n : nat) : pred (succ n) = n :=
nat.rec_on n
	(show pred (succ zero) = zero, from rfl)
	(assume n, 
		assume ih, 
		show pred (succ (succ n)) = succ n, from rfl)


def trun_sub (n m : nat) : nat :=
nat.rec_on m n (λ m nmm : nat, pred nmm)


end hidden


namespace hidden
-- BEGIN
open nat
inductive list (α : Type*)
| nil {} : list
| cons : α → list → list

namespace list

variable {α : Type*}

notation h :: t  := cons h t
notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l

def append (s t : list α) : list α :=
list.rec t (λ x l u, x::u) s

notation s ++ t := append s t

theorem nil_append (t : list α) : nil ++ t = t := rfl

theorem cons_append (x : α) (s t : list α) :
  x::s ++ t = x::(s ++ t) := rfl

theorem append_nil (t : list α) : t ++ nil = t := 
list.rec_on t (rfl)
(begin
	intros, 
	rw cons_append,
	rw ih	
end)

def length (s : list α) : ℕ :=
list.rec 0 (λ a spa u, u+1) s

#reduce length [1,2,3,4]

theorem length_append (s t : list α) : length (s ++ t) = length s + length t :=
list.rec_on s
(calc 
 length (nil ++ t) = length t : by rw nil_append
 ... = 0 + length t : by rw nat.zero_add
 ... = length nil + length t : rfl)
(assume a, assume a_1, assume ih,
	calc 
	(a :: a_1 ++ t).length = (a :: (a_1 ++ t)).length : by rw cons_append
	... = (a_1 ++ t).length +1 : rfl
	... = a_1.length + t.length + 1 : by rw ih
	... = (1+ a_1.length )+ t.length : by repeat {rw nat.add_comm, rw nat.add_assoc}
	... = (a_1.length+1) + t.length : by simp [nat.add_comm]
	... = (a::a_1).length + t.length : rfl
)

def reverse (s : list α) : list α :=
list.rec nil (λ a spa rev, rev++[a]) s

theorem nil_reverse : nil.reverse = @nil α := rfl

#reduce reverse [2,6,9,2,1,5]

example (t : list α ) : t.reverse.length = t.length :=
list.rec_on t (by rw nil_reverse) 
(assume a, assume a_1, assume ih, calc 
(a :: a_1).reverse.length = (a_1.reverse ++ [a]).length : rfl
... = a_1.reverse.length + [a].length : by rw length_append
... = a_1.length + 1 : by repeat {rw ih, apply rfl}
... = (a::a_1).length : rfl)


theorem rev_append (l s : list α) : (l++s).reverse = s.reverse++l.reverse :=
list.rec_on l 
(calc
(nil ++ s).reverse = s.reverse : by rw nil_append
... = s.reverse ++ nil : by rw append_nil
... = s.reverse ++ nil.reverse : by rw nil_reverse) 
(assume a, assume a_1, assume ih, calc
(a :: a_1 ++ s).reverse = (a :: (a_1 ++ s)).reverse : rfl
... = (a_1 ++ s).reverse ++ [a] : rfl
... = s.reverse ++ a_1.reverse ++ [a] : by rw ih
... = s.reverse ++ (a_1.reverse ++ [a]) : _
... = s.reverse ++ (a :: a_1).reverse : rfl) 

example (t : list α) : t.reverse.reverse = t :=
list.rec_on t (rfl) 
(assume a, assume a_1, assume ih, calc 
(a :: a_1).reverse.reverse = ((a_1.reverse)++[a]).reverse : rfl
... = [a].reverse++a_1.reverse.reverse : by rw rev_append
... = [a]++a_1.reverse.reverse : rfl
... = [a]++a_1 : by rw ih
... = a :: a_1 : rfl)




end list
-- END
end hidden


