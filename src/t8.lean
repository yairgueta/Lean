universe u

inductive vector (α : Type u) : nat → Type u
| nil {} : vector 0
| cons   : Π {n}, α → vector n → vector (n+1)

namespace vector
local notation h :: t := cons h t

def append_tail {α : Type*} : Π {n : ℕ}, vector α n → α → vector α (n+1)
| 0		 	nil 		a := a :: nil
| (n+1)	(a::v)	b := a::(append_tail v b)

-- theorem simp_length {α : Type*} : ∀ {n m: ℕ}, vector α (n + 1 + m) = vector α (n + (m + 1)) 
-- := sorry


def append {α : Type*} : Π {n m : ℕ},  vector α n → vector α m → vector α (n+m)
| 0				0 				nil 			nil				:= nil
| (n+1)		m					(a::v)		u					:=  by repeat {rw nat.add_comm}; exact a::(append v u)
| 0			 	(m+1)			nil				u 				:= by repeat {rw nat.add_comm}; exact u

end vector


inductive aexpr : Type
| const : ℕ → aexpr
| var : ℕ → aexpr
| plus : aexpr → aexpr → aexpr
| times : aexpr → aexpr → aexpr

open aexpr

def sample_aexpr : aexpr :=
plus (times (var 0) (const 7)) (times (const 2) (var 1))

def aeval (v : ℕ → ℕ) : aexpr → ℕ
| (const n)    := n
| (var n)      := v n
| (plus e₁ e₂)  := aeval e₁ + aeval e₂ 
| (times e₁ e₂) := aeval e₁ * aeval e₂

def sample_val : ℕ → ℕ
| 0 := 5
| 1 := 6
| _ := 0

#eval aeval sample_val sample_aexpr

def simp_const : aexpr → aexpr
| (plus (const n₁) (const n₂))  := const (n₁ + n₂)
| (times (const n₁) (const n₂)) := const (n₁ * n₂)
| e                             := e

def sample_aexpr1 : aexpr :=
plus (times (const 0) (const 7)) (times (const 2) (const 1))

#reduce simp_const (times (const 0) (const 7))
#reduce simp_const (plus (times (const 0) (const 7)) (times (const 2) (const 1)))


def fuse : aexpr → aexpr
| (plus e₁ e₂) 		:= simp_const (plus (simp_const e₁) (simp_const e₂))
| (times  e₁ e₂) 	:= simp_const (times (simp_const e₁) (simp_const e₂))
| e               := simp_const e

#reduce fuse (times (const 0) (const 7))
#reduce fuse (plus (times (const 0) (const 7)) (times (const 2) (const 1)))

theorem simp_const_eq (v : ℕ → ℕ) :
  ∀ e : aexpr, aeval v (simp_const e) = aeval v e
| e := have h: simp_const e = e, by simp [simp_const e], 
| (const _) := rfl
| (var _) := rfl
| (plus (const _) (const _))  		:= rfl
| (times (const _) (const _)) 		:= rfl



theorem fuse_eq (v : ℕ → ℕ) :
  ∀ e : aexpr, aeval v (fuse e) = aeval v e :=
sorry
