import utils
import data.vector2

set_option trace.check true
-- import category_theory.category
-- #print ≫
-- #print
-- #print has_bind.and_then
-- set_option pp.beta true
set_option pp.coercions true
-- attribute [reducible] vector.cons

structure graph :=
  (nodes    : Type)
  (edges    : Type)
  (srctrg   : bool → edges → nodes)
  (edge_ext : ∀ e e' : edges, (∀ b, srctrg b e = srctrg b e') → e = e')

def graph.source (G : graph) : G.edges → G.nodes := G.srctrg ff
def graph.target (G : graph) : G.edges → G.nodes := G.srctrg tt

def graph.eq {G G' : graph}
       (nodes_eq : G.nodes = G'.nodes)
       (edges_eq : G.edges = G'.edges)
       (srctrg_eq : G.srctrg == G'.srctrg)
      : G = G' :=
  begin
    cases G  with n  e  st,
    cases G' with n' e' st',
    cases nodes_eq,
    cases edges_eq,
    cases srctrg_eq,
    refl
  end

structure graph.hom (G G' : graph) :=
  (nodes_map  : G.nodes → G'.nodes)
  (edges_map  : G.edges → G'.edges)
  (srctrg_map : ∀ (b : bool) (e : G.edges),
                  nodes_map (G.srctrg b e) = G'.srctrg b (edges_map e))

def graph.hom.eq {G G' : graph} {F F' : graph.hom G G'}
       (nodes_map_eq : F.nodes_map = F'.nodes_map)
       (edges_map_eq : F.edges_map = F'.edges_map)
      : F = F' :=
  begin
    cases F  with nm  em  stm,
    cases F' with nm' em' stm',
    cases nodes_map_eq,
    cases edges_map_eq,
    refl
  end

def graph.hom.id {G : graph} : graph.hom G G :=
  { nodes_map  := id
  , edges_map  := id
  , srctrg_map := λ _ _, rfl
  }

def graph.hom.comp {G G' G'' : graph}
        (F  : graph.hom G G')
        (F' : graph.hom G' G'')
      : graph.hom G G'' :=
  { nodes_map  := F'.nodes_map ∘ F.nodes_map
  , edges_map  := F'.edges_map ∘ F.edges_map
  , srctrg_map := λ b e, by {simp, rw F.srctrg_map, rw F'.srctrg_map}
  }

def reverse_graph (G : graph) : graph :=
  { nodes    := G.nodes
  , edges    := G.edges
  , srctrg   := (λ b, G.srctrg (not b))
  , edge_ext := λ e e' p, G.edge_ext e e'
                  (λ b, match b with ff := p tt | tt := p ff end)
  }

def singleton_reflexive_graph : graph :=
  { nodes    := punit
  , edges    := punit
  , srctrg   := (λ _ _, ())
  , edge_ext := λ e e' _, match e, e' with (), () := rfl end
  }
