import utils
import data.vector2

-- def graph : Type _ := Σ (α : Type _), α → α → Prop

structure graph :=
  (nodes : Type _)
  (edges : nodes → nodes → Prop)

#check sigma.eq

namespace graph

  protected structure hom (G G' : graph) :=
    (v_map : G.nodes → G'.nodes)
    (e_map : ∀ (s t : G.nodes),
               G.edges s t → G'.edges (v_map s) (v_map t))

  protected def id {G : graph} : hom G G :=
    { v_map := id
    , e_map := λ _ _, id
    }

  protected def comp {G G' G'': graph} (F  : hom G G')
                                       (F' : hom G' G'') : hom G G'' :=
    { v_map := F'.v_map ∘ F.v_map
    , e_map := λ s t, (F'.e_map (F.v_map s) (F.v_map t)) ∘ (F.e_map s t)
    }

end graph

def prism_graph_aux (twisted : bool) (G : graph) : graph :=
   { nodes := bool × G.nodes
   , edges := λ s' t', match s', t' with
                       | ⟨ff, s⟩, ⟨ff, t⟩ := if twisted then G.edges t s
                                                        else G.edges s t
                       | ⟨tt, s⟩, ⟨tt, t⟩ := G.edges s t
                       | ⟨ff, s⟩, ⟨tt, t⟩ := s = t
                       | ⟨tt, s⟩, ⟨ss, t⟩ := false
                       end
   }

def singleton_reflexive_graph : graph :=
  { nodes := unit
  , edges := λ s t, true
  }

def standard_prism_graph : graph → graph := prism_graph_aux ff
def twisted_prism_graph  : graph → graph := prism_graph_aux tt

def standard_cube_graph : ℕ → graph
| nat.zero     := singleton_reflexive_graph
| (nat.succ n) := standard_prism_graph (standard_cube_graph n)

def twisted_cube_graph : ℕ → graph
| nat.zero     := singleton_reflexive_graph
| (nat.succ n) := twisted_prism_graph (twisted_cube_graph n)

def standard_cube_graph_alt (n : ℕ) : graph :=
  { nodes := bitvec n
  , edges := λ s t, s = t ∨
                     (∃ i : fin n, (s.remove_nth i = t.remove_nth i)
                                    ∧ s.nth i = ff ∧ t.nth i = not (s.nth i))

def standard_cube_graph_to_alt :
      Π (n : ℕ), graph.hom (standard_cube_graph n) (standard_cube_graph_alt n)
| nat.zero     := { v_map := λ _, vector.nil
                  , e_map := λ s t e, or.inl rfl
                  }
| (nat.succ n) := let ih_hom := standard_cube_graph_to_alt n in
                  { v_map := λ ⟨b, v⟩, vector.cons b (ih_hom.v_map v)
                  , e_map := λ s' t' e', (match s', t', e' with
    | ⟨ff, s⟩, ⟨ff, t⟩, e   := _-- let test :=ih_hom.e_map s t e in _
                               -- match ih_hom.e_map s t e with
                               -- | or.inl p := or.inl _--{!congr_arg (vector.cons ff) p !}--(congr_arg (vector.cons ff) p)
                               -- | or.inr _ := _
                               -- end
    | ⟨tt, s⟩, ⟨tt, t⟩, e   := (match ih_hom.e_map s t e with
        | or.inl p := or.inl (congr_arg (vector.cons tt) p)
        | or.inr _ := _
        end : (standard_cube_graph_alt (nat.succ n)).edges
                (tt :: ih_hom.v_map s) (tt :: ih_hom.v_map t))
    | ⟨ff, s⟩, ⟨tt, t⟩, rfl := _
    | ⟨tt, s⟩, ⟨ff, t⟩, e   := false.elim e
    end)
                  }

variables a b : ℕ
variable h : a = b
#check congr_arg (λ v, (ff, v)) h
#reduce (λ (v : ℕ), (ff, v)) a = (λ (v : ℕ), (ff, v)) b
#check vector.cons ff


#print true
