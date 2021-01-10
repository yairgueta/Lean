import data.finset
import data.set

inductive word (S : Type*) 
| ε {} : word
| concat : S → word → word

namespace word
open list

variable {S : Type*}
notation σ ⬝ w := concat σ w

def concat_words : word S → word S → word S
| ε w := w
| (σ⬝w) w2 := σ⬝ (concat_words w w2) 

notation w1 ⬝ w2 := concat_words w1 w2

def word.mk : list S → word S 
| nil := ε 
| (h :: t) := h ⬝ (word.mk t)

end word

structure language {S : Type} :=
(l : set (word S))

namespace language
end language


structure automaton (states_type : Type*) :=
(S : Type)
(Q : finset states_type) 
(q₀ : states_type) 
(δ : (states_type × S) → states_type)
(F : finset states_type)
(hq_0 : q₀ ∈ Q) 
(hF : F ⊆ Q)

namespace automaton

inductive S1
| a : S1 
| b : S1

open S1
open word 
def A1 : automaton ℤ :=
{
	S := S1,
	Q := {0,1,2,3},
	q₀ := 0,
	δ := λ x, match x with 
	| (0, a) := 1
	| (0, b) := 0
	| (1, a) := 2
	| (1, b) := 0
	| (2, a) := 2
	| (2, b) := 3
	| (3, _) := 3
	| _ := 0
	end,
	F := {3},
	hq_0 := by simp,
	hF := by simp,
}

def read_word_from_state {states_type : Type*} (A : automaton states_type) 
: states_type → word A.S → states_type
| qt 		ε 			:= qt
| qt 		(σ ⬝ w)  := read_word_from_state (A.δ ⟨qt, σ⟩) w

#reduce read_word_from_state A1 0 ( word.mk [a,a,b,b,b,a])

def read_word {states_type : Type* } (A : automaton states_type) 
(w : word A.S) : states_type := read_word_from_state A A.q₀ w

#reduce read_word A1 (word.mk [a,a,a,a,b,a,a,b,a])

def is_word_accepted {states_type : Type* } (A : automaton states_type) 
(w : word A.S) : bool := if ((read_word A w) ∈ A.F) then tt else ff
							
#reduce is_word_accepted A1 (word.mk [a,a,a,b,a,a,b,a])


end automaton


