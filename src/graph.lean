import utils
import data.vector2

structure graph :=
  (nodes  : Type _)
  (edges  : Type _)
  (srctrg : bool → edges → nodes)

namespace graph
  def source (G : graph) : G.edges → G.nodes := G.srctrg ff
  def target (G : graph) : G.edges → G.nodes := G.srctrg tt

  structure hom (G G' : graph) :=
    (nodes_map  : G.nodes → G'.nodes)
    (edges_map  : G.edges → G'.edges)
    (srctrg_map : ∀ (b : bool) (e : G.edges),
                    nodes_map (G.srctrg b e) = G'.srctrg b (edges_map e))

  def id {G : graph} : hom G G :=
    { nodes_map  := id
    , edges_map  := id
    , srctrg_map := λ _ _, rfl
    }

  def comp {G G' G'' : graph} (F : hom G G') (F' : hom G' G'') : hom G G'' :=
    { nodes_map  := F'.nodes_map ∘ F.nodes_map
    , edges_map  := F'.edges_map ∘ F.edges_map
    , srctrg_map := λ b e, by {simp, rw F.srctrg_map, rw F'.srctrg_map}
    }

end graph

def reverse_graph (G : graph) : graph :=
  { nodes  := G.nodes
  , edges  := G.edges
  , srctrg := (λ b, G.srctrg (not b))
  }

def singleton_reflexive_graph : graph :=
  { nodes  := unit
  , edges  := unit
  , srctrg := (λ _ _, unit.star)
  }

def prism_graph_aux (twisted : bool) (G : graph) : graph :=
  { nodes  := bool × G.nodes
  , edges  := (bool × G.edges) + G.nodes
  , srctrg := λ b e', match e' with
                      | sum.inl (ff, e) := (ff, G.srctrg (bxor twisted b) e)
                      | sum.inl (tt, e) := (tt, G.srctrg b e)
                      | sum.inr v       := (b, v)
                      end
  }
def standard_prism_graph : graph → graph := prism_graph_aux ff
def twisted_prism_graph  : graph → graph := prism_graph_aux tt

def standard_cube_graph : ℕ → graph
| 0     := singleton_reflexive_graph
| (n+1) := standard_prism_graph (standard_cube_graph n)
def twisted_cube_graph : ℕ → graph
| nat.zero     := singleton_reflexive_graph
| (nat.succ n) := twisted_prism_graph (twisted_cube_graph n)

def standard_cube_graph_alt (n : ℕ) : graph :=
  { nodes  := bitvec n
  , edges  := bitvec n + (match n with
                          | nat.zero      := empty
                          | (nat.succ n') := fin n × bitvec n'
                          end : Type _)
  , srctrg := λ b e, match n, e with
                     | _,            sum.inl v      := v
                     | (nat.succ _), sum.inr (i, v) := v.insert_nth b i
                     end
  }

def standard_cube_graph_to_alt :
      Π (n : ℕ), graph.hom (standard_cube_graph n) (standard_cube_graph_alt n)
| nat.zero     := { nodes_map  := λ _, vector.nil
                  , edges_map  := λ _, sum.inl vector.nil
                  , srctrg_map := λ b e, rfl
                  }
| (nat.succ n) := let ih_hom := standard_cube_graph_to_alt n in
                  { nodes_map  := λ ⟨b, v⟩, (ih_hom.nodes_map v).cons b
                  , edges_map  := λ e',
    match e' with
    | sum.inl ⟨b, e⟩ :=
        match n, ih_hom.edges_map e with
        | _,            sum.inl v      := sum.inl (b :: v)
        | (nat.succ _), sum.inr (i, v) := sum.inr ⟨fin.succ i, b :: v⟩
        end
    | sum.inr v      := sum.inr (⟨0, nat.zero_lt_succ n⟩, ih_hom.nodes_map v)
    end
                  , srctrg_map := λ b' e',
    match e' with
    | sum.inl ⟨b, e⟩ := {!!}
    | sum.inr v      := {!!}
    end
                  }
