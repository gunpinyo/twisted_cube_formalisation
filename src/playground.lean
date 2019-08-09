import category_theory.category
import utils

-- #check Σ obj : Type*, category obj

def inhabited.set (α : Type*) : inhabited (set α) :=
by unfold set; apply_instance

#print inhabited.set
  -- λ (α : Type u), eq.mpr _ (pi.inhabited α)
#reduce inhabited.set ℕ
  -- {default := λ (a : ℕ), true}


#print add_comm_group
#print classes
#print instances inhabited
#reduce (by apply_instance : inhabited ℕ)
#print set
namespace hidden
-- BEGIN
instance Prop_inhabited : inhabited Prop :=
⟨true⟩
-- inhabited.mk true

instance : inhabited bool :=
inhabited.mk ff

instance bool_inhabited : inhabited bool :=
inhabited.mk tt

instance nat_inhabited : inhabited nat :=
inhabited.mk 0

instance unit_inhabited : inhabited unit :=
inhabited.mk ()
-- END

def default (α : Type) [s : inhabited α] : α :=
@inhabited.default α s

#reduce default bool

end hidden


namespace foo
def bxor_bxor_id (x y : bool) : bxor x (bxor x y) = y :=
  begin cases x, simp, simp, end

example (f : ℕ → ℕ) (y : ℕ) (P : ℕ → Type) : ((λ x : ℕ, f x) y) = ((λ x : ℕ, f x) y) :=
  begin dsimp, end

example (P : bool → Type) (a : bool) :
    (Π b, P (bxor b (bxor b a))) → P a  :=
  begin
    intro h,
    rw bxor_bxor_id at h,
    -- intro x,
    -- rw nat.add_comm, exact h x,
  end
end

example (x : ℕ) (h : x = 3)  : x + x + x = 9 :=
begin
  set y := x with ←h_xy,
/-
x : ℕ,
y : ℕ := x,
h_xy : x = y,
h : y = 3
⊢ y + y + y = 9
-/
end

def foo (n : ℕ) (i : fin n) (v : bitvec n) : bool × fin n :=
  ((match n, i, v with
   | 0,      i, _ := _
   | (_ +1), i, v := v.head end), _)


def product_of_units : ℕ → Type
| 0      := empty
| (n +1) := unit ⊕ (product_of_units n)

example (n : ℕ) : product_of_units (n +1) :=
  begin
    unfold product_of_units,
    left, exact ()
  end


structure graph :=
  (nodes  : Type)
  (edges  : Type)
  (srctrg : bool → edges → nodes)

def prism_graph (G : graph) : graph :=
  { nodes  := bool × G.nodes
  , edges  := (bool × G.edges) ⊕ G.nodes
  , srctrg := λ b e, match e with
                     | (sum.inl (b', e)) := (b, G.srctrg b' e)
                     | (sum.inr v)       := (b, v)
                     end
  }

def cube_graph : ℕ → graph
| 0      := ⟨unit, unit, (λ _ _, ())⟩
| (n +1) := prism_graph (cube_graph n)

example : nat.zero = nat.zero := by simp
#check fin.elim0
example (n : ℕ) (b : bool) (v : (cube_graph n).nodes) :
      (graph.srctrg (cube_graph (n +1)) b (sum.inr v)) = (b, v) :=
  begin conv begin
    whnf,


  end end


#print foo
def prism_graph.srctrg (b : bool) : prism_graph.edges G → prism_graph.nodes G
| (sum.inl (ff, e)) := (ff, G.srctrg (bxor tw b) e)
| (sum.inl (tt, e)) := (tt, G.srctrg b e)
| (sum.inr v)       := (b, v)


def foo : bool → Type := λ _, unit
namespace bar
section
  parameter b : bool
  include b
  def foo' := foo b
  #check foo' -- Type
  example : Type := by exact foo'
end

section
  parameter twisted : bool
  include twisted

  def cg  := cube_graph twisted
  def cg' := cube_graph_alt twisted

  def foo : unit :=
    begin
      have : (cg 0).nodes,
        exact (),
      exact (),
    end
end
end bar

example (α β : Type) (p : α = β) : (unit → α) = (unit → β) :=
  begin rw p end

example (α : Type) : Π (x y : α), x == y → x == y
| a .(a) rfl = r

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

section
  parameters (α : Type) (x y : α)
  #check x = y
end

def uip (α : Type) (x y : α) (p q : x = y) : Π b : bool, p = q := λ _, rfl

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
