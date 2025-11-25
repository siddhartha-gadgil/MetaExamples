/-!
This is a property where we can decide `P n` for each `n`, but we cannot decide
whether `∀ n, P n` holds or not.
-/
variable (P : Nat → Prop) [DecidablePred P]

/-!
The main construction for undecidability of definitional equality:
* If `∀ n, P n` is true, then `f 0` reduces to `f 1`, `f 2`, ... but not to `()`.
* If `∃ n, ¬ P n` is true, then `f n` reduces to `()`.
Thus, `f 0` is definitionally equal to `()` if and only if `∃ n, ¬ P n`.
-/
noncomputable def f (n : Nat) :
    Acc (fun x1 x2 ↦ x1 > x2) n → Unit :=
  Acc.rec (fun n _ h ↦ if (P n) then h (n + 1) (Nat.le_refl (n + 1)) else ())

-- Experimenmts with `Acc` and `inv`

/-- info: f (P : Nat → Prop) [DecidablePred P] (n : Nat) : Acc (fun x1 x2 ↦ x1 > x2) n → Unit -/
#guard_msgs in
#check f

variable {α : Type} {r : α → α → Prop} (x : α)

def inv : Acc r x → ∀y: α, (r y x) → Acc r y
| .intro _ f => f

#check inv

example : a = Acc.intro x (inv x a) := rfl

#check DecidablePred



partial def f₀ (n: Nat) : Acc (· > ·) n → Unit := fun h ↦
  if (P n) then f₀ (n + 1) (inv n h (n + 1) (by simp)) else ()

#check Acc.rec

#check f₀
