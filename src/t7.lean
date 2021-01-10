open function

#print surjective
#check @exists.intro

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}
open function

lemma surjective_comp {g : β → γ} {f : α → β}
  (hg : surjective g) (hf : surjective f) :
surjective (g ∘ f) 
| y :=  ⟨ exists.elim (hg y), hf (exists.elim (hg y)) ⟩ 


namespace hidden
inductive my_nat : Type
| zero : my_nat
| succ : my_nat → my_nat

namespace my_nat
notation `ze` := my_nat.zero
notation a `+o` := my_nat.succ a
notation `one` := ze +o

def add : my_nat → my_nat → my_nat 
| n ze := n
| n (m +o) := (add n m) +o

notation a `pl` b := add a b
local infix ` + ` := add
#check ze pl (ze +o)

def mult : my_nat → my_nat → my_nat 
| n ze := ze
| n (m +o) := (mult n m) + n

notation a `mul` b := mult a b
local infix ` * ` := mult

def exp : my_nat → my_nat → my_nat
| n ze := one
| n (m +o) := (exp n m) * n

theorem zero_add : ∀ (n : my_nat), ze + n = n 
| ze := rfl
| (n +o) := congr_arg succ (zero_add n)

end my_nat
end hidden


namespace hidden

inductive list (α : Type*)
| nil {} : list
| cons : α → list → list

namespace list

notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l

notation h :: t  := cons h t

def append (s t : list α) : list α :=
list.rec_on s t (λ x l u, x::u)

notation s ++ t := append s t

theorem nil_append (t : list α) : nil ++ t = t := rfl

theorem cons_append (x : α) (s t : list α) : x::s ++ t = x::(s ++ t) := rfl

-- BEGIN
theorem append_nil (t : list α) : t ++ nil = t := sorry

theorem append_assoc (r s t : list α) :
  r ++ s ++ t = r ++ (s ++ t) := sorry
-- END

def rev : list α → list α 
| nil := nil
| (h :: t) := (rev t) ++ [h]

#reduce [1,2,5,4,6,3]
#reduce rev [1,2,5,4,6,3]

theorem rev_rev : ∀(l : list α ), rev (rev l) = l
| nil := rfl
| (h :: t) := sorry


end list

end hidden