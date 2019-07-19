def foo1 (α : unit → Type*) (x : unit) (y : α x) : y = y :=
  match x with
  | unit.star := rfl
  end
def foo3 (α : unit → Type*) (x : unit) (y : α x) : y = y :=
begin
  revert x,
  refine punit.rec _,
  -- refl will not work here
  intros, refl
end

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
  intro h,
   cases h with hp hqr,
   cases hqr with hq hr,
     left, constructor, repeat { assumption },
     right, constructor, repeat { assumption },
  intro h,
    cases h with hpq hpr,
      cases hpq with hp hq,
        constructor, exact hp, left, exact hq,
      cases hpr with hp hr,
        constructor, exact hp, right, exact hr
end

def foo2 (α : unit → Type*) (x : unit) (y : α x) : y = y :=
  match x, y with
  | unit.star, _ := rfl
  end

section
  parameter x : ℕ
  include x
  def foo := nat.zero
end

#check foo
