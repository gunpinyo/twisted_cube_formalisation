import utils
import data.vector2

set_option trace.check true
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

def generic_prism_graph (twisted : bool) (G : graph) : graph :=
  { nodes  := bool × G.nodes
  , edges  := (bool × G.edges) ⊕ G.nodes
  , srctrg := λ b e', match e' with
                      | sum.inl (ff, e) := (ff, G.srctrg (bxor twisted b) e)
                      | sum.inl (tt, e) := (tt, G.srctrg b e)
                      | sum.inr v       := (b, v)
                      end
  }
def standard_prism_graph : graph → graph := generic_prism_graph ff
def twisted_prism_graph  : graph → graph := generic_prism_graph tt

def standard_cube_graph : ℕ → graph
| nat.zero     := singleton_reflexive_graph
| (nat.succ n) := standard_prism_graph (standard_cube_graph n)
def twisted_cube_graph : ℕ → graph
| nat.zero     := singleton_reflexive_graph
| (nat.succ n) := twisted_prism_graph (twisted_cube_graph n)


@[simp]
def standard_cube_graph_alt (n : ℕ) : graph :=
  { nodes  := bitvec n
    -- it is fine to use `nat.pred` because when `n = 0` it is
    -- inhabitable anyway due to `fin 0 ≃ empty`
  , edges  := bitvec n ⊕ (fin n × bitvec (nat.pred n))
  , srctrg := λ b e, match n, e with
                     | _,          sum.inl v      := v
                     | nat.zero,   sum.inr (i, _) := i.elim0
                     | nat.succ _, sum.inr (i, v) := v.insert_nth b i
                     end
  }

namespace standard_cube_graph_to_alt
  def scg  := standard_cube_graph
  def scg' := standard_cube_graph_alt

  @[simp]
  def nodes_map : Π (n : ℕ), (scg n).nodes → (scg' n).nodes
  | nat.zero     _      := vector.nil
  | (nat.succ n) (b, v) := (nodes_map n v).my_cons b

  @[simp]
  def edges_map : Π (n : ℕ), (scg n).edges → (scg' n).edges
  | nat.zero     _                := sum.inl vector.nil
  | (nat.succ n) (sum.inl (b, e)) :=
      match n, edges_map n e with
      | _,          sum.inl v      := sum.inl (v.my_cons b)
      | nat.zero,   sum.inr (i, _) := i.elim0
      | nat.succ _, sum.inr (i, v) := sum.inr (fin.succ i, v.my_cons b)
      end
  | (nat.succ n) (sum.inr v)      := sum.inr (fin.zero, nodes_map n v)

  def srctrg_map : Π (n : ℕ) (b : bool) (e : (scg n).edges),
    nodes_map n ((scg n).srctrg b e) = (scg' n).srctrg b (edges_map n e)
  | nat.zero     _ _                 := rfl
  | (nat.succ n) b (sum.inl (ff, e)) := {! srctrg_map n b e !}
  | (nat.succ n) b (sum.inl (tt, e)) :=
      match n, e with
      | nat.zero :=      sorry
      | (nat.succ n') := sorry
      end
      -- calc  nodes_map (nat.succ n)
      --                 ((scg (nat.succ n)).srctrg b (sum.inl (tt, e)))
      --     = nodes_map (nat.succ n) (tt, (scg n).srctrg b e)
      --         : rfl
      -- ... = (nodes_map n ((scg n).srctrg b e)).my_cons tt
      --         : rfl
      -- ... = ((scg' n).srctrg b (edges_map n e)).my_cons tt
      --         : by rw (srctrg_map n b e)
      -- ... = (scg' (nat.succ n)).srctrg b (edges_map (nat.succ n) (sum.inl (tt, e)))
      --         : begin simp, exact
      -- (match edges_map n e with
      -- | sum.inl v      :=
      --     begin
      --       simp,
      --       have aux : (scg' n).srctrg b (sum.inl v) = v,
      --         reflexivity,
      --       rw aux,
      --       reflexivity
      --     end
      -- | sum.inr (i, v') :=
      --     begin
      --       cases n,
      --     end
      --     -- sorry
      --                      -- match n, v' with
      --                      -- | nat.succ _, v := _
      --      -- begin
      --      --  simp,
      --      --  -- have aux : edges_map._match_2 tt n (i, v) = vector.insert_nth b i v
      --      -- end
      --                      -- end
      -- end),
      --           end



      -- begin
      --   simp, induction (n, edges_map n e), simp,
      --   simp,
      --   -- unfold scg at *,

      -- end
      -- (sorry : nodes_map (nat.succ n) (tt, (scg n).srctrg b e)
      --    = (scg' (nat.succ n)).srctrg b (edges_map (nat.succ n) (sum.inl (tt, e))))
  | (nat.succ n) b (sum.inr v)       := rfl

-- variable (n : ℕ)
-- variables (b b' : bool)
-- variable (e : (standard_cube_graph n).edges)
-- #reduce nodes_map (nat.succ n) ((scg (nat.succ n)).srctrg b (sum.inl (b', e)))
-- #reduce (scg' (nat.succ n)).srctrg b (edges_map (nat.succ n) (sum.inl (b', e)))



--   def main (n : ℕ) : graph.hom (scg n) (scg n)
--   { nodes_map  := nodes_map n
--   , edges_map  := edges_map n
--   , srctrg_map := λ b' e',
--       match e' with
--       | sum.inl ⟨b, e⟩ := _
--           -- match n, ih_hom.edges_map e with
--           -- | _,            sum.inl v      := _
--           -- | (nat.succ _), sum.inr (i, v) := _
--           -- end
--       | sum.inr v      := rfl
--       end
--                     }

-- end standard_cube_graph_to_alt

-- #check Π (n : ℕ), (graph.hom (standard_cube_graph n) (standard_cube_graph_alt n)).nodes_map
-- #check graph.hom.nodes_map
-- @[simp]
-- def standard_cube_graph_to_alt :
--       Π (n : ℕ), graph.hom (standard_cube_graph n) (standard_cube_graph_alt n)
-- | nat.zero     := { nodes_map  := _ -- λ _, vector.nil
--                   , edges_map  := λ _, sum.inl vector.nil
--                   , srctrg_map := λ b e, rfl
--                   }
-- | (nat.succ n) := let ih_hom := standard_cube_graph_to_alt n in
--                   { nodes_map  := λ ⟨b, v⟩, (ih_hom.nodes_map v).my_cons b
--                   , edges_map  := λ e',
--     match e' with
--     | sum.inl ⟨b, e⟩ :=
--         match n, ih_hom.edges_map e with
--         | _,            sum.inl v      := sum.inl (v.my_cons b)
--         | (nat.succ _), sum.inr (i, v) := sum.inr ⟨fin.succ i, v.my_cons b⟩
--         end
--     | sum.inr v      := sum.inr (fin.zero, ih_hom.nodes_map v)
--     end
--                   , srctrg_map := λ b' e',
--     match e' with
--     | sum.inl ⟨b, e⟩ := _
--         -- match n, ih_hom.edges_map e with
--         -- | _,            sum.inl v      := _
--         -- | (nat.succ _), sum.inr (i, v) := _
--         -- end
--     | sum.inr v      := rfl
--     end
--                   }

-- variable standard_cube_graph_to_alt : Π (n : ℕ), graph.hom (standard_cube_graph n) (standard_cube_graph_alt n)
-- variable n : ℕ
-- variable ih_hom : graph.hom (standard_cube_graph n) (standard_cube_graph_alt n)
-- variable b' : bool
-- variable e' : (standard_cube_graph (nat.succ n)).edges
-- variable b : bool
-- variable e : (standard_cube_graph n).edges

-- #reduce _root_.standard_cube_graph_to_alt._match_1 n ih_hom
--       ((standard_cube_graph (nat.succ n)).srctrg b' (sum.inl (b, e)))
-- -- =
-- --     (standard_cube_graph_alt (nat.succ n)).srctrg b'
-- --       (_root_.standard_cube_graph_to_alt._match_2 n ih_hom (sum.inl (b, e)))
