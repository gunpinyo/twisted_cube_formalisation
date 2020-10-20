import generic_cube_graph

def twprism_graph            : graph → graph := prism_graph tt
def twcube_graph     (n : ℕ) : graph := cube_graph tt n
def twcube_graph_alt (n : ℕ) : graph := cube_graph_alt tt n

section
variable n : ℕ
def twcg_to_twcg' : graph_cat.hom (twcube_graph n) (twcube_graph_alt n)
      := cg_to_cg' tt n
def twcg'_to_twcg : graph_cat.hom (twcube_graph_alt n) (twcube_graph n)
      := cg'_to_cg tt n
def twcg_iso_twcg' : graph_cat.iso (twcube_graph n) (twcube_graph_alt n)
      := cg_iso_cg' tt n
end

def twcube_graph_cat : category := cube_graph_cat tt
