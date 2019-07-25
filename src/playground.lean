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
