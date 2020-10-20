import data.vector2
import utils
import category

structure graph : Type 1 :=
  (nodes    : Type)
  (edges    : Type)
  (srctrg   : bool → edges → nodes)
  -- `edge_ext` asserts that every graph we consider does not have multi-edge
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

  @[class]
  def has_deceq_node (G : graph) : Type := decidable_eq G.nodes

  def to_rel (G : graph) : G.nodes → G.nodes → Prop :=
        λ v v', ∃ e : G.edges, G.source e = v ∧ G.target e = v'

  @[class]
  def has_dec_rel (G : graph) : Type := decidable_rel G.to_rel

  -- TODO: define an instance of for `prism_graph` `cube_graph` `cube_graph_alt`
  -- in `generic_cube_graph.lean`
end graph

namespace graph_cat
  structure hom (G G' : graph) : Type :=
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

namespace graph
  def reverse (G : graph) : graph :=
    { nodes    := G.nodes
    , edges    := G.edges
    , srctrg   := (λ b, G.srctrg (bnot b))
    , edge_ext := λ e e' p, G.edge_ext e e'
        (begin intro b, let h := p (bnot b), simp at h, assumption end)
    }

  def singleton_reflexive : graph :=
    { nodes    := unit
    , edges    := unit
    , srctrg   := (λ _ _, ())
    , edge_ext := λ e e' _, begin cases e, cases e', refl end
    }

  def path_graph (n : ℕ) : graph :=
    { nodes    := fin (n +1)
    , edges    := fin n
    , srctrg   := λ b e, match b with
                         | ff := e.cast_succ
                         | tt := e.succ
                         end
    , edge_ext := begin
                    induction n with n IH, { intro e, exact e.elim0 },
                    intros e e' p, cases e, cases e',
                    cases e_val,
                    { cases e'_val, {exact fin.eq_of_veq rfl},
                      replace p := p tt,
                      simp [path_graph._match_1, fin.succ] at p, contradiction,},
                    cases e'_val,
                    { replace p := p tt,
                      simp [path_graph._match_1, fin.succ] at p,
                      contradiction,},
                    let e  := fin.mk_from_succ e_val  e_is_lt,
                    let e' := fin.mk_from_succ e'_val e'_is_lt,
                    suffices : ∀ b, path_graph._match_1 n e  b
                                  = path_graph._match_1 n e' b,
                    { simp, exact fin.veq_of_eq (IH e e' this),},
                    intro b, replace p := p b, cases b,
                    { simp [path_graph._match_1] at p |-,
                      exact fin.eq_of_veq p},
                    { simp [path_graph._match_1] at p |-,
                      replace p := fin.succ_injection p, simp at p, congr,
                      exact fin.eq_of_veq p},
                  end
    }

  def path (G : graph) (len : ℕ) := graph_cat.hom (path_graph len) G

  def path.source {G : graph} {n : ℕ} (P : path G n) : G.nodes :=
        P.nodes_map fin.zero

  def path.target {G : graph} {n : ℕ} (P : path G n) : G.nodes :=
        P.nodes_map (fin.last n)

  def path.from_node (G : graph) (v : G.nodes) : path G 0 :=
        { nodes_map  := λ i, match i with
                             | ⟨0,    _⟩ := v
                             | ⟨i +1, p⟩ := fin.elim_out_of_bound p
                             end
        , edges_map  := fin.elim0
        , srctrg_map := λ b e, e.elim0
        }

  def path.from_edge (G : graph) (e : G.edges) : path G 1 :=
        { nodes_map  := λ i, match i with
                             | ⟨0,    _⟩ := G.source e
                             | ⟨1,    _⟩ := G.target e
                             | ⟨i +2, p⟩ := fin.elim_out_of_bound p
                             end
        , edges_map  := λ i, match i with
                             | ⟨0,    _⟩ := e
                             | ⟨i +1, p⟩ := fin.elim_out_of_bound p
                             end
        , srctrg_map := λ b e', match b, e' with
                               | ff, ⟨0,    _⟩ :=
            begin -- TODO: currently here
              dsimp [path_graph, graph.srctrg],
              change fin.cast_succ ⟨0, _⟩ with ⟨0, _⟩
              dsimp [fin.cast_succ, fin.cast_add, fin.cast_le, fin.cast_lt],
              simp [path.from_edge._match_1, path.from_edge._match_2, graph.srctrg], refl,
            end
                               | tt, ⟨0,    _⟩ := _
                               | _,  ⟨i +1, p⟩ := fin.elim_out_of_bound p
                               end
        }

  -- structure Hamiltonian_path (G : graph) (n : ℕ) :=
  --   (path      : path G n)
  --   (nodes_bij : function.bijective path.nodes_map)

  -- -- TODO:
  -- structure unique_Hamiltonian_path (G : graph) extends Hamiltonian_path G :=
  --   (unique : subsingleton (Hamiltonian_path.mk len mor nodes_bij))

end graph
