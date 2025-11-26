variable {α : Type} {r : α → α → Prop} (x : α)

/--
Inverse function for accessibility. Given a proof that `x` is accessible, we obtain a proof that forall `y` such that we have `r y x`,  `y` is accessible.
-/
def inv : Acc r x → ∀y : α, (r y x) → Acc r y
| .intro _ f => f

/-- info: inv {α : Type} {r : α → α → Prop} (x : α) : Acc r x → ∀ (y : α), r y x → Acc r y -/
#guard_msgs in
#check inv

/--
An example showing that `inv` works as intended.
-/
theorem inv_eq (a : Acc r x) : a = Acc.intro x (inv x a) := rfl

/-!
This is a property where we can decide `P n` for each `n`, but we cannot decide
whether `∀ n, P n` holds or not.
-/
variable (P : Nat → Prop) [DecidablePred P]

namespace ToUnit
/-!
A first attempt at the main construction for undecidability of definitional equality:
* Let `p` be a proof that `n + 1 > n` for each `n`.
* Define `f` by recursion on accessibility of `n` with respect to `>`:
  - If `P n` is true, then `f P n h = f P (n + 1) (h (n + 1) (p n))
  - If `P n` is false, then `f P n h = ()`
* If `∀ n, P n` is true, then
  - `f P 0 h₀ = f P 1 (inv 0 a₀ 1 (p 0))`
  - `f P 2 (inv 1 (inv 0 a₀ 1 (p 0)) 2 (p 1))`, ... but not to `()`, where `h₀` is a (non-existent) proof of `Acc (· > ·) 0`.\
* The above reduction depends on `h₀ = Acc.intro 0 (inv 0 h₀)`, and similarly for `h₁`, `h₂`, ...
* If `∃ n, ¬ P n` is true, then `f 0 h₀` reduces to `()`.
Thus, `f 0` is definitionally equal to `()` if and only if `∃ n, ¬ P n` the definition of `f`.
-/

/--
info: Acc.rec : ((x : Nat) → (∀ (y : Nat), y > x → Acc (fun x1 x2 ↦ x1 > x2) y) → ((y : Nat) → y > x → Unit) → Unit) →
  {a : Nat} → Acc (fun x1 x2 ↦ x1 > x2) a → Unit
-/
#guard_msgs in
#check Acc.rec (α := Nat) (r := (· > ·)) (motive := fun _  _ => Unit)

noncomputable def f (P : Nat → Prop) [DecidablePred P] (n : Nat)  :
    Acc (· > ·) n → Unit :=
  Acc.rec (fun n _ g ↦ if (P n) then g (n + 1) (Nat.le_refl (n + 1)) else ())

/--
info: ToUnit.f (P : Nat → Prop) [DecidablePred P] (n : Nat) : Acc (fun x1 x2 ↦ x1 > x2) n → Unit
-/
#guard_msgs in
#check f

def p (n : Nat) : n + 1 > n := Nat.le_refl (n + 1)

example (n: Nat)
  (h: ∀ (y : Nat), y > n → Acc (fun x1 x2 ↦ x1 > x2) y) :
    f P n (Acc.intro n h) =
      if (P n) then f P (n + 1) (h (n + 1) (p n)) else () := rfl

example (n: Nat) (a: Acc (· > ·) n):
    f P n (Acc.intro n (inv n a)) =
      if (P n) then f P (n + 1) (inv n a (n + 1) (p n)) else () := rfl

example (n: Nat) (a: Acc (· > ·) n)
    (_ : P n) :
    f P n (Acc.intro n (inv n a)) =
      f P (n + 1) (inv n a (n + 1) (p n)) := rfl

example (a₀ : Acc (· > ·) 0) (_ : P 0) :
    f P 0 a₀ =
      f P 1 (inv 0 a₀ 1 (p 0))  := rfl

example (a₀ : Acc (· > ·) 0)
    (_ : ¬ P 0) :
    f P 0 a₀ = () := rfl

example (a₀ : Acc (· > ·) 0)
    (_ : P 0) (_ : P 1) :
    f P 0 a₀ =
      f P 2 (inv 1 (inv 0 a₀ 1 (p 0)) 2 (p 1)) := rfl

example (a₀ : Acc (· > ·) 0)
    (_ : P 0) (_ : ¬ P 1) :
    f P 0 a₀ = () := rfl

example (a₀ : Acc (· > ·) 0)
    (_ : P 0) (_ : P 1) (_ : P 2) :
    f P 0 a₀ =
      f P 3 (inv 2 (inv 1 (inv 0 a₀ 1 (p 0)) 2 (p 1)) 3 (p 2)) := rfl



-- Extra stuff
partial def f₀ (n: Nat) : Acc (· > ·) n → Unit := fun h ↦
  if (P n) then f₀ (n + 1) (inv n h (n + 1) (by simp)) else ()

/--
info: ToUnit.f₀ (P : Nat → Prop) [DecidablePred P] (n : Nat) : Acc (fun x1 x2 ↦ x1 > x2) n → Unit
-/
#guard_msgs in
#check f₀

end ToUnit

namespace ToBool

/-!
A first attempt at the main construction for undecidability of definitional equality:
* Let `p` be a proof that `n + 1 > n` for each `n`.
* Define `f` by recursion on accessibility of `n` with respect to `>`:
  - If `P n` is true, then `f P n h = f P (n + 1) (h (n + 1) (p n))
  - If `P n` is false, then `f P n h = ()`
* If `∀ n, P n` is true, then
  - `f P 0 h₀ = f P 1 (inv 0 a₀ 1 (p 0))`
  - `f P 2 (inv 1 (inv 0 a₀ 1 (p 0)) 2 (p 1))`, ... but not to `()`, where `h₀` is a (non-existent) proof of `Acc (· > ·) 0`.\
* The above reduction depends on `h₀ = Acc.intro 0 (inv 0 h₀)`, and similarly for `h₁`, `h₂`, ...
* If `∃ n, ¬ P n` is true, then `f 0 h₀` reduces to `()`.
Thus, `f 0` is definitionally equal to `()` if and only if `∃ n, ¬ P n` the definition of `f`.
-/

/--
info: Acc.rec : ((x : Nat) → (∀ (y : Nat), y > x → Acc (fun x1 x2 ↦ x1 > x2) y) → ((y : Nat) → y > x → Bool) → Bool) →
  {a : Nat} → Acc (fun x1 x2 ↦ x1 > x2) a → Bool
-/
#guard_msgs in
#check Acc.rec (α := Nat) (r := (· > ·)) (motive := fun _  _ => Bool)

noncomputable def f (P : Nat → Prop) [DecidablePred P] (n : Nat)  :
    Acc (· > ·) n → Bool :=
  Acc.rec (fun n _ g ↦ if (P n) then g (n + 1) (Nat.le_refl (n + 1)) else true)

/--
info: ToBool.f (P : Nat → Prop) [DecidablePred P] (n : Nat) : Acc (fun x1 x2 ↦ x1 > x2) n → Bool
-/
#guard_msgs in
#check f

def p (n : Nat) : n + 1 > n := Nat.le_refl (n + 1)

example (n: Nat)
  (h: ∀ (y : Nat), y > n → Acc (fun x1 x2 ↦ x1 > x2) y) :
    f P n (Acc.intro n h) =
      if (P n) then f P (n + 1) (h (n + 1) (p n)) else true := rfl

theorem conditional_expand (n: Nat) (a: Acc (· > ·) n):
    f P n (Acc.intro n (inv n a)) =
      if (P n) then f P (n + 1) (inv n a (n + 1) (p n)) else true := rfl

example (n: Nat) (a: Acc (· > ·) n)
    (hP : P n) :
    f P n (Acc.intro n (inv n a)) =
      f P (n + 1) (inv n a (n + 1) (p n)) := by
  rw [conditional_expand P n a]
  rw [if_pos hP]

example (a₀ : Acc (· > ·) 0) (hP : P 0) :
    f P 0 a₀ =
      f P 1 (inv 0 a₀ 1 (p 0))  := by
       rw [inv_eq 0 a₀, conditional_expand, if_pos hP]
       assumption


example (a₀ : Acc (· > ·) 0) (hP : ¬ P 0) :
    f P 0 a₀ = true := by
  rw [inv_eq 0 a₀, conditional_expand, if_neg hP]
  assumption

example (a₀ : Acc (· > ·) 0)(a₁ : Acc (· > ·) 1)
    (hP₀ : P 0) (hP₁ : P 1) :
    f P 0 a₀ =
      f P 2 (inv 1 (inv 0 a₀ 1 (p 0)) 2 (p 1)) := by
        rw [inv_eq 0 a₀, conditional_expand, if_pos hP₀]
        rw [inv_eq 1 (inv 0 a₀ 1 (p 0)), conditional_expand, if_pos hP₁]
        simp only [gt_iff_lt, Nat.zero_add]
        assumption
        assumption

end ToBool
