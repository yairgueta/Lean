import tactic
open tactic

/-!
## Exercise 1
Write a `contradiction` tactic.
The tactic should look through the hypotheses in the local context
trying to find two that contradict each other,
i.e. proving `P` and `¬ P` for some proposition `P`.
It should use this contradiction to close the goal.
Bonus: handle `P → false` as well as `¬ P`.
This exercise is to practice manipulating the hypotheses and goal.
Note: this exists as `tactic.interactive.contradiction`.
-/

meta def contr_single : expr → expr → tactic unit
| `(%%a → false) `(%%b) := 
	if (a=b) then do skip
	else do failed
| `(¬ %%a) `(%%b) :=
	if (a=b) then do skip
	else do failed
| a b := do failed

meta def helper (hyp : expr) (ctx_s : expr): tactic unit :=
do hyp_tp ← infer_type hyp,
	ctx_s_type ← infer_type ctx_s,
	contr_single hyp_tp ctx_s_type

meta def contr_single_ctx (hyp : expr) (ctx :  list expr): tactic unit :=
ctx.mmap' (λ x, do {helper hyp x, exact (hyp x)} <|> skip)
	

meta def tactic.interactive.contr : tactic unit :=
do
  ctx ← local_context,
	ctx.mmap' (λ x, (contr_single_ctx x ctx))


example (P Q R : Prop) (hp : P) (hq : Q) (hr : ¬ R) (hnq : ¬ Q) : false :=
by contr

example (P Q R : Prop) (hnq : ¬ Q) (hp : P) (hq : Q) (hr : ¬ R) : 0 = 1 :=
by contr


example (P Q R : Prop) (hp : P) (hq : Q) (hr : ¬ R) (hnq : Q → false) : false :=
by contr

