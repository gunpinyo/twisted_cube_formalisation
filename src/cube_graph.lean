import graph

section
  variable tw : bool
  variable G : graph

  def prism_graph.nodes := bool × G.nodes
  def prism_graph.edges := (bool × G.edges) ⊕ G.nodes

  def prism_graph.srctrg (b : bool) : prism_graph.edges G → prism_graph.nodes G
  | (sum.inl (b', e)) := (b', G.srctrg (bxor (band b' tw) b) e)
  | (sum.inr v)       := (b, v)

  def prism_graph : graph :=
    { nodes  := prism_graph.nodes G
    , edges  := prism_graph.edges G
    , srctrg := prism_graph.srctrg tw G
    }
end
def standard_prism_graph : graph → graph := prism_graph ff
def twisted_prism_graph  : graph → graph := prism_graph tt

def cube_graph (tw : bool) : ℕ → graph
| 0      := singleton_reflexive_graph
| (n +1) := prism_graph tw (cube_graph n)

def standard_cube_graph : ℕ → graph := cube_graph ff
def twisted_cube_graph  : ℕ → graph := cube_graph tt

section
  variable tw : bool
  variable n : ℕ

  def cube_graph_alt.nodes := bitvec n
  def cube_graph_alt.edges := bitvec n ⊕ (fin n × bitvec (nat.pred n))

  def cube_graph_alt.num_zeros_is_odd :
        Π {n : ℕ} (i : fin (n +1)) (v : bitvec n), bool
  | 0      _         _                      := ff
  | (n +1) ⟨0,    _⟩ _                      := ff
  | (n +1) ⟨i +1, p_succ_i⟩ v :=
      have p_i : i < (n +1), from
        nat.pred_le_pred p_succ_i,
      bxor (v.head) (cube_graph_alt.num_zeros_is_odd ⟨i, p_i⟩ v.tail)

  def cube_graph_alt.srctrg (b : bool) :
        cube_graph_alt.edges n → cube_graph_alt.nodes n
  | (sum.inl v)      := v
  | (sum.inr (i, v)) := match n, i, v with
                        | 0,      i, v := i.elim0
                        | (_ +1), i, v :=
                            let tw_bit := cube_graph_alt.num_zeros_is_odd i v
                             in vector.insert_nth (bxor (band tw tw_bit) b) i v
                        end

  def cube_graph_alt.srctrg.fin_zero (b : bool)
                                     (v : cube_graph_alt.nodes n) :
        b :: v = cube_graph_alt.srctrg tw (n +1) b (sum.inr (fin.zero, v)) :=
    begin
      cases v with l p,
      transitivity vector.insert_nth b fin.zero ⟨l, p⟩,
      { unfold vector.cons,
        unfold vector.insert_nth,
        refl,},
      unfold cube_graph_alt.srctrg,
      suffices : cube_graph_alt.num_zeros_is_odd fin.zero ⟨l, p⟩ = ff,
      { rw this,
        simp,},
      transitivity cube_graph_alt.num_zeros_is_odd fin.zero ⟨l, p⟩,
        refl,
      cases n,
        refl,
      unfold fin.zero,
      refl,
    end

  def cube_graph_alt : graph :=
    { nodes  := cube_graph_alt.nodes n
    , edges  := cube_graph_alt.edges n
    , srctrg := cube_graph_alt.srctrg tw n
    }
end

def standard_cube_graph_alt : ℕ → graph := cube_graph_alt ff
def twisted_cube_graph_alt  : ℕ → graph := cube_graph_alt tt


namespace cube_graph_to_cube_graph_alt
section
  variable tw : bool

  def nodes_map : Π (n : ℕ), (cube_graph tw n).nodes
                           → (cube_graph_alt tw n).nodes
  | 0      _      := vector.nil
  | (n +1) (b, v) := b :: (nodes_map n v)

  def edges_map : Π (n : ℕ), (cube_graph tw n).edges
                           → (cube_graph_alt tw n).edges
  | 0      _                := sum.inl vector.nil
  | (n +1) (sum.inl (b, e)) :=
      match edges_map n e with
      | sum.inl v       := sum.inl (b :: v)
      | sum.inr (i, v) := match n, i, v with
                          | 0,      i, v := i.elim0
                          | (_ +1), i, v := sum.inr (fin.succ i, b :: v)
                          end
      end
  | (n +1) (sum.inr v)      := sum.inr (fin.zero, nodes_map tw n v)

  def srctrg_map (n : ℕ) (b : bool) (e : (cube_graph tw n).edges)
        : nodes_map tw n ((cube_graph tw n).srctrg b e)
        = (cube_graph_alt tw n).srctrg b (edges_map tw n e) :=
    begin
      revert b,
      induction n with n IH,
      { intro,
        refl,},
      intro b,
      cases e with be v,
      { cases be with b' e,
        dunfold cube_graph,
        dsimp [prism_graph],
        dunfold prism_graph.srctrg,
        dunfold nodes_map,
        dunfold edges_map,
        rw [IH],
        dsimp [cube_graph_alt],
        symmetry,
        cases edges_map tw n e with v iv,
        { dsimp [edges_map._match_1],
          dsimp [cube_graph_alt.srctrg],
          refl
        },
        { cases n,
          { cases iv with i,
            exact fin.elim0 i,},
          cases iv with i v,
          dunfold edges_map._match_1,
          dunfold edges_map._match_2,
          dsimp [cube_graph_alt.srctrg],
          simp,
          rw vector.insert_nth_succ,
          cases tw,
            simp,
          simp,
          cases i with i_val i_p,
          unfold fin.succ,
          unfold cube_graph_alt.num_zeros_is_odd,
          simp,
          refl,
        },
      },
      { transitivity (b :: nodes_map tw n v),
          refl,
        have : (edges_map tw (n +1) (sum.inr v)
                 : (cube_graph_alt tw (n +1)).edges)
             = (sum.inr (fin.zero, nodes_map tw n v)),
          refl,
        rw this,
        transitivity cube_graph_alt.srctrg tw (n +1) b
                       (sum.inr (fin.zero, nodes_map tw n v)),
          rw cube_graph_alt.srctrg.fin_zero,
        refl,
      }
    end

end
end cube_graph_to_cube_graph_alt

def cube_graph_to_cube_graph_alt (tw : bool) (n : ℕ)
      : graph.hom (cube_graph tw n) (cube_graph_alt tw n) :=
  { nodes_map  := cube_graph_to_cube_graph_alt.nodes_map tw n
  , edges_map  := cube_graph_to_cube_graph_alt.edges_map tw n
  , srctrg_map := cube_graph_to_cube_graph_alt.srctrg_map tw n
  }
