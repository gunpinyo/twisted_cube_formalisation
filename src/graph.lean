import data.vector2
import utils
import category

structure graph :=
  (nodes    : Type)
  (edges    : Type)
  (srctrg   : bool → edges → nodes)
  (edge_ext : ∀ e e' : edges, (∀ b, srctrg b e = srctrg b e') → e = e')

namespace graph
  def source (G : graph) : G.edges → G.nodes := G.srctrg ff
  def target (G : graph) : G.edges → G.nodes := G.srctrg tt

  def eq {G G' : graph}
          (nodes_eq : G.nodes = G'.nodes)
          (edges_eq : G.edges = G'.edges)
          (srctrg_eq : G.srctrg == G'.srctrg)
        : G = G' :=
    begin
      cases G  with n  e  st, cases G' with n' e' st',
      cases nodes_eq, cases edges_eq, cases srctrg_eq, refl
    end
end graph

namespace graph_cat

  structure hom (G G' : graph) :=
    (nodes_map  : G.nodes → G'.nodes)
    (edges_map  : G.edges → G'.edges)
    (srctrg_map : ∀ (b : bool) (e : G.edges),
                    nodes_map (G.srctrg b e) = G'.srctrg b (edges_map e))

  def hom.eq {G G' : graph} {F F' : hom G G'}
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

    def id (G : graph) : hom G G :=
      { nodes_map  := id
      , edges_map  := id
      , srctrg_map := λ _ _, rfl
      }

    def comp {G G' G'' : graph}
          (F  : hom G G') (F' : hom G' G'') : hom G G'' :=
      { nodes_map  := F'.nodes_map ∘ F.nodes_map
      , edges_map  := F'.edges_map ∘ F.edges_map
      , srctrg_map := λ b e, by {simp, rw F.srctrg_map, rw F'.srctrg_map}
      }

    def id_l {G G' : graph} (F : hom G G')
          : comp (id G) F  = F :=
      hom.eq rfl rfl

    def id_r {G G' : graph} (F : hom G G')
          : comp F (id G') = F :=
      hom.eq rfl rfl

    def assoc {G G' G'' G''' : graph}
          (F   : hom G   G')
          (F'  : hom G'  G'')
          (F'' : hom G'' G''') : comp (comp F F') F'' = comp F (comp F' F'') :=
      hom.eq rfl rfl
end graph_cat

def graph_cat : category :=
  { obj   := graph
  , hom   := graph_cat.hom
  , id    := graph_cat.id
  , comp  := @graph_cat.comp
  , id_l  := @graph_cat.id_l
  , id_r  := @graph_cat.id_r
  , assoc := @graph_cat.assoc
  }

def reverse_graph (G : graph) : graph :=
  { nodes    := G.nodes
  , edges    := G.edges
  , srctrg   := (λ b, G.srctrg (not b))
  , edge_ext := λ e e' p, G.edge_ext e e'
                  (λ b, match b with ff := p tt | tt := p ff end)
  }

def singleton_reflexive_graph : graph :=
  { nodes    := unit
  , edges    := unit
  , srctrg   := (λ _ _, ())
  , edge_ext := λ e e' _, match e, e' with (), () := rfl end
  }
