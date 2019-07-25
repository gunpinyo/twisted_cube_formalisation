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
  (nodes  : Type)
  (edges  : Type)
  (srctrg : bool → edges → nodes)

namespace graph
  def source (G : graph) : G.edges → G.nodes := G.srctrg ff
  def target (G : graph) : G.edges → G.nodes := G.srctrg tt

  def eq {G G' : graph}
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

  structure hom (G G' : graph) :=
    (nodes_map  : G.nodes → G'.nodes)
    (edges_map  : G.edges → G'.edges)
    (srctrg_map : ∀ (b : bool) (e : G.edges),
                    nodes_map (G.srctrg b e) = G'.srctrg b (edges_map e))

  namespace hom
    def eq {G G' : graph} {F F' : hom G G'}
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

  end hom
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
