import utils

structure graph : Type 1 :=
  (node : Type)
  (edge : Type)
  (src  : edge → node)
  (trg  : edge → node)

namespace graph
  protected def ext (G G' : graph)
                    (node : G.node = G'.node)
                    (edge : G.edge = G'.edge)
                    (src  : G.src == G'.src)
                    (trg  : G.trg == G'.trg)
                  : G = G' :=
    begin
      cases G  with v e s t, cases G' with v' e' s' t',
      cases node, cases edge, cases src, cases trg, refl
    end

  protected def srctrg (G : graph) : bool → G.edge → G.node
  | ff := G.src
  | tt := G.trg

  protected def make (node : Type) (edge : Type)
                     (srctrg : bool → edge → node) : graph :=
    { node := node, edge := edge, src := srctrg ff, trg := srctrg tt }

  def has_srctrg_as (G : graph) (e : G.edge) (s t : G.node) : Prop :=
    G.src e = s ∧ G.trg e = t

  def composable (G : graph) (e e' : G.edge) : Prop :=
    G.trg e = G.src e'

  @[class]
  def has_deceq_node (G : graph) : Type :=
    decidable_eq G.node

  @[class]
  def reflexive_struct (G : graph) : Type :=
    Π v : G.node, subtype.mk ⟨G.edge, _⟩

  #check subtype

  def reflexive_closure (G : graph) : graph :=
    graph.make G.node (G.edge ⊕ G.node)
      (λ b, sum.elim (cond b G.trg G.src) id)

  instance reflexive_closure_is_reflexive_struct (G : graph) :
      reflexive_struct (reflexive_closure G) :=
    begin
      dsimp [reflexive_struct, reflexive_closure, graph.make, has_srctrg_as],
      intro v, fapply subtype.mk, exact sum.inr v, simp,
    end

  @[class]
  def symmetric_struct (G : graph) : Type :=
    Π e : G.edge, {e' : G.edge // G.has_srctrg_as e' (G.trg e) (G.src e)}

  def symmetric_closure (G : graph) : graph :=
    graph.make G.node (G.edge ⊕ G.edge)
      (λ b, sum.elim (G.srctrg b) (G.srctrg (bnot b)))

  instance symmetric_closure_is_symmetric_struct (G : graph) :
      symmetric_struct (symmetric_closure G) :=
    begin
      dsimp [symmetric_struct, symmetric_closure, graph.make],
      intro e, cases e,
      {fapply subtype.mk, exact sum.inr e, simp [has_srctrg_as]},
      {fapply subtype.mk, exact sum.inl e, simp [has_srctrg_as]}
    end

  inductive nonempty_path (G : graph) : G.node → G.node → Type
  | from_edge : Π e : G.edge, nonempty_path (G.src e) (G.trg e)
  | compose   : Π {v v' v'' : G.node}
                  (p  : nonempty_path v  v')
                  (p' : nonempty_path v' v''),
                    nonempty_path v v''

  structure nonempty_path_with_srctrg (G : graph) : Type :=
    (src trg : G.node) (p : nonempty_path G src trg)

  @[class]
  def transitive_struct (G : graph) : Type :=
    Π e e' : G.edge, G.composable e e' →
      {e'': G.edge // G.has_srctrg_as e'' (G.src e) (G.trg e')}

  def transitive_closure (G : graph) : graph :=
    graph.make G.node (nonempty_path_with_srctrg G)
      (λ b e, cond b e.src e.trg)

  instance transitive_closure_is_transitive_struct (G : graph) :
      transitive_struct (transitive_closure G) :=
    begin
      dsimp [transitive_struct, transitive_closure, graph.make],
      intro v, fapply subtype.mk, exact sum.inr v, simp,
    end

end graph

structure graph_hom (G H : graph) : Type :=
  (node : G.node → H.node)
  (edge : G.edge → H.edge)
  (scr  : ∀ e : G.edge, node (G.src e) = H.src (edge e))
  (trg  : ∀ e : G.edge, node (G.trg e) = H.trg (edge e))
