import utils
import data.vector2

-- set_option trace.check true
-- import category_theory.category
-- #print ≫
-- #print
-- #print has_bind.and_then
-- set_option pp.beta true
-- attribute [reducible] vector.cons

structure graph :=
  (nodes  : Type*)
  (edges  : Type*)
  (srctrg : bool → edges → nodes)

namespace graph
  def source (G : graph) : G.edges → G.nodes := G.srctrg ff
  def target (G : graph) : G.edges → G.nodes := G.srctrg tt

  -- def eq : ∀ {G G' : graph}
  --            (nodes_eq : G.nodes = G'.nodes)
  --            (edges_eq : G.edges = G'.edges)
  --            (srctrg_eq : ∀ (b : bool) (e : G.edges) (e' : G'.edges),
  --                          e == e' → G.srctrg b e == G'.srctrg b e'),
  --          G = G'
  -- | ⟨n, e, st⟩ ⟨.(n), .(e), .(st)⟩ rfl rfl := _

  -- section
  --   parameters {G G' : graph}
  --   parameter nodes_eq : G.nodes = G'.nodes
  --   parameter edges_eq : G.edges = G'.edges
  --   -- variable srctrg_eq : ∀ (b : bool) (e : G.edges) (e' : G'.edges),
  --   --                        e == e' → G.srctrg b e == G'.srctrg b e'
  --   variable srctrg_eq : G.srctrg == G'.srctrg


  --   #check @eq.rec_on
  --   #check srctrg_eq
  -- end


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

section
  parameter twisted : bool
  parameter G : graph

  def prism_graph.nodes := bool × G.nodes
  def prism_graph.edges := (bool × G.edges) ⊕ G.nodes

  def prism_graph.srctrg (b : bool) : prism_graph.edges → prism_graph.nodes
  | (sum.inl (ff, e)) := (ff, G.srctrg (bxor twisted b) e)
  | (sum.inl (tt, e)) := (tt, G.srctrg b e)
  | (sum.inr v)       := (b, v)

  def prism_graph : graph :=
    { nodes  := prism_graph.nodes
    , edges  := prism_graph.edges
    , srctrg := prism_graph.srctrg
    }
end
def standard_prism_graph : graph → graph := prism_graph ff
def twisted_prism_graph  : graph → graph := prism_graph tt

def cube_graph (twisted : bool) : ℕ → graph
| 0      := singleton_reflexive_graph
| (n +1) := prism_graph twisted (cube_graph n)

def standard_cube_graph : ℕ → graph := cube_graph ff
def twisted_cube_graph  : ℕ → graph := cube_graph tt

section
  parameter twisted : bool
  parameter n : ℕ

  def cube_graph_alt.nodes := bitvec n
  def cube_graph_alt.edges := bitvec n ⊕ (fin n × match n with
                                                  | 0       := empty
                                                  | (n' +1) := bitvec n'
                                                  end)

  def cube_graph_alt.num_zeros_is_odd : Π {n : ℕ}, fin (n +1) → bitvec n → bool
  | 0      _         _                      := ff
  | (n +1) ⟨0,    _⟩ _                      := ff
  | (n +1) ⟨i +1, p_succ_i⟩ ⟨b :: l, p_b_l⟩ :=
      have p_i : i < (n +1), from
        nat.pred_le_pred p_succ_i,
      have p_l : list.length l = n, from
        suffices p_b_l' : list.length l +1 = n +1, from
          congr_arg nat.pred p_b_l',
        begin
          simp at p_b_l,
          rw [add_comm],
          exact p_b_l,
        end,
      bxor b (cube_graph_alt.num_zeros_is_odd ⟨i, p_i⟩ ⟨l, p_l⟩)

  def cube_graph_alt.srctrg (b : bool) :
        cube_graph_alt.edges → cube_graph_alt.nodes
  | (sum.inl v)      := v
  | (sum.inr iv)     := match n, iv with
                        | (_ +1), (i, v) :=
                            let b' := if twisted then
                                        cube_graph_alt.num_zeros_is_odd i v
                                      else b
                            in vector.insert_nth b' i v
                        end

  def cube_graph_alt : graph :=
    { nodes  := cube_graph_alt.nodes
    , edges  := cube_graph_alt.edges
    , srctrg := cube_graph_alt.srctrg
    }
end

def standard_cube_graph_alt : ℕ → graph := cube_graph_alt ff
def twisted_cube_graph_alt  : ℕ → graph := cube_graph_alt tt


namespace cube_graph_to_cube_graph_alt
section
  -- parameter twisted : bool

  def cg  := standard_cube_graph
  def cg' := standard_cube_graph_alt

  def nodes_map : Π {n : ℕ}, (cg n).nodes → (cg' n).nodes
  | 0      _      := vector.nil
  | (n +1) (b, v) := b :: (nodes_map v)

  def edges_map : Π {n : ℕ}, (cg n).edges → (cg' n).edges
  | 0      _                := sum.inl vector.nil
  | (n +1) (sum.inl (b, e)) :=
      match edges_map e with
      | sum.inl v       := sum.inl (b :: v)
      | sum.inr (i, v') := match n, v' with
                           | _ +1, v := sum.inr (fin.succ i, b :: v)
                           end
      end
  | (n +1) (sum.inr v)      := sum.inr (fin.zero, nodes_map v)

  section
    parameters (n : ℕ) (b : bool) (v : (cube_graph twisted n).nodes)
    #reduce nodes_map ((cg (nat.succ n)).srctrg b (sum.inr v))
    #reduce (cg' (nat.succ n)).srctrg tt (edges_map (sum.inr v))
  end

  def srctrg_map : Π (n : ℕ) (b : bool) (e : (cg n).edges),
        nodes_map ((cg n).srctrg b e) = (cg' n).srctrg b (edges_map e)
  | (nat.succ n) b (sum.inr v)       :=
      begin
        transitivity (b :: nodes_map v),
          refl,
        -- have (cg (nat.succ n)).srctrg b (sum.inr v) = v,

      end
  | 0      _ _                 := rfl
  | (n +1) b (sum.inl (ff, e)) := {! srctrg_map n b e !}
  | (n +1) b (sum.inl (tt, e)) := sorry

  --     calc  nodes_map ((cg (n +1)).srctrg b (sum.inl (tt, e)))
  --         = nodes_map (tt, (cg n).srctrg b e)
  --             : rfl
  --     ... = tt :: (nodes_map ((cg n).srctrg b e))
  --             : rfl
  --     ... = tt :: ((cg' n).srctrg b (edges_map e))
  --             : by rw (srctrg_map n b e)
  --     ... = (cg' (n +1)).srctrg b (edges_map (sum.inl (tt, e)))
  --             : begin simp, exact
  --     (match n, edges_map n e with
  --     | n,           sum.inl v      :=
  --         begin
  --           simp,
  --           have aux : (cg' n).srctrg b (sum.inl v) = v,
  --             reflexivity,
  --           rw aux,
  --           reflexivity
  --         end
  --     | nat.succ n', sum.inr (i, v) := --_-- sorry
  --          begin
  --           simp,
  --           -- have aux : edges_map._match_2 tt n (i, v) = vector.insert_nth b i v
  --          end
  --     end),
  --               end
  --     -- begin
  --     --   simp, induction (n, edges_map n e), simp,
  --     --   simp,
  --     --   -- unfold cg at *,

  --     -- end
  --     -- (sorry : nodes_map (nat.succ n) (tt, (cg n).srctrg b e)
  --     --    = (cg' (nat.succ n)).srctrg b (edges_map (nat.succ n) (sum.inl (tt, e))))

end
end cube_graph_to_cube_graph_alt
