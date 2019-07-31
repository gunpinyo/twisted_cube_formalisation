import graph

section
  variable tw : bool
  variable G : graph

  def prism_graph.nodes := bool × G.nodes
  def prism_graph.edges := (bool × G.edges) ⊕ G.nodes

  def prism_graph.srctrg (b : bool) : prism_graph.edges G → prism_graph.nodes G
  | (sum.inl (b', e)) := (b', G.srctrg (bxor (band b' tw) b) e)
  | (sum.inr v)       := (b, v)

  def prism_graph.edge_ext :
        ∀ (tw : bool) (G : graph) (e e' : prism_graph.edges G),
          (∀ b, prism_graph.srctrg tw G b e = prism_graph.srctrg tw G b e') →
        e = e'
  | tw G (sum.inl (ff, e)) (sum.inl (ff, e')) p :=
       begin congr, apply G.edge_ext e e',
             cases tw, all_goals { simp [prism_graph.srctrg] at p, assumption,},
       end
  | tw G (sum.inl (ff, e)) (sum.inl (tt, e')) p :=
       begin simp [prism_graph.srctrg] at p, contradiction, end
  | tw G (sum.inl (tt, e)) (sum.inl (ff, e')) p :=
       begin simp [prism_graph.srctrg] at p, contradiction, end
  | tw G (sum.inl (tt, e)) (sum.inl (tt, e')) p :=
       begin
         congr, apply G.edge_ext e e',
         cases tw, { simp [prism_graph.srctrg] at p, assumption,},
         simp [prism_graph.srctrg] at p,
         intro b, cases b, exact p tt, exact p ff,
       end
  | tw G (sum.inl (b, e)) (sum.inr v')        p :=
       begin let pnb := p (not b), cases b,
             all_goals { simp [prism_graph.srctrg] at pnb, contradiction}, end
  | tw G (sum.inr v)      (sum.inl (b', e'))  p :=
       begin let pnb := p (not b'), cases b',
             all_goals { simp [prism_graph.srctrg] at pnb, contradiction}, end
  | tw G (sum.inr v)      (sum.inr v')        p :=
       begin simp [prism_graph.srctrg] at p, congr, assumption, end

  def prism_graph : graph :=
    { nodes    := prism_graph.nodes G
    , edges    := prism_graph.edges G
    , srctrg   := prism_graph.srctrg tw G
    , edge_ext := prism_graph.edge_ext tw G
    }
end

def cube_graph (tw : bool) : ℕ → graph
| 0      := singleton_reflexive_graph
| (n +1) := prism_graph tw (cube_graph n)

section
  variable tw : bool
  variable n : ℕ

  def cube_graph_alt.nodes := bitvec n
  def cube_graph_alt.edges := bitvec n ⊕ (fin n × bitvec (nat.pred n))

  def cube_graph_alt.num_zeros_is_odd :
        Π {n : ℕ} (i : fin (n +1)) (v : bitvec n), bool
  | 0      _ _ := ff
  | (n +1) i v := fin.maybe_pred_rec ff (λ i',
                    bxor (v.head) (cube_graph_alt.num_zeros_is_odd i' v.tail)) i

  def cube_graph_alt.srctrg (b : bool) :
        cube_graph_alt.edges n → cube_graph_alt.nodes n
  | (sum.inl v)      := v
  | (sum.inr (i, v)) := match n, i, v with
                        | 0,      i, v := i.elim0
                        | (_ +1), i, v :=
                            let tw_bit := cube_graph_alt.num_zeros_is_odd i v
                             in vector.insert_nth (bxor (band tw tw_bit) b) i v
                        end

  private def cube_graph_alt.edge_ext_helper : ∀ (n : ℕ) (i : fin (n +1))
        (v : bitvec n) (v' : bitvec (n +1)),
        (∀ b, v.insert_nth b i = v') → false
  | 0       i          v v' p :=
      begin
        let p' := p (bnot v'.head),
        cases i, cases i_val, swap,
        {exact nat.not_succ_le_zero i_val (nat.le_of_lt_succ i_is_lt),},
        simp [fin.to_zero, vector.insert_nth_zero] at p',
        let p'' := (vector.cons_injection p').1, simp at p'',
        exact bnot_self p'',
      end
  | (n +1) ⟨0,    pz⟩  v v' p :=
      begin
        let p' := p (bnot v'.head),
        simp [fin.to_zero, vector.insert_nth_zero] at p',
        let p'' := (vector.cons_injection p').1, simp at p'',
        exact bnot_self p'',
      end
  | (n +1) ⟨i +1, psi⟩ v v' p :=
      begin
        let fin_i : fin (n +1) := ⟨i, nat.pred_le_pred psi⟩,
        have : ∀ b, vector.insert_nth b fin_i (vector.tail v) = vector.tail v',
        { intro b, let p' := congr_arg vector.tail (p b),
          rw [fin.to_succ, vector.insert_nth_succ] at p', assumption,},
        exact cube_graph_alt.edge_ext_helper n fin_i v.tail v'.tail this,
      end

  def cube_graph_alt.edge_ext :
        ∀ (tw : bool) (n : ℕ) (e e' : cube_graph_alt.edges n),
          (∀ b, cube_graph_alt.srctrg tw n b e
              = cube_graph_alt.srctrg tw n b e') →
        e = e'
  | tw n      (sum.inl v)                (sum.inl v')                  p :=
      begin simp [cube_graph_alt.srctrg] at p, congr, assumption, end
  | tw (n +1) (sum.inl v)                (sum.inr (i',            v')) p :=
      begin
        exfalso, simp [cube_graph_alt.srctrg] at p,
        refine cube_graph_alt.edge_ext_helper n i' v' v _, intro b, symmetry,
        let p' := p (bxor (band tw (cube_graph_alt.num_zeros_is_odd i' v')) b),
        rwa [bxor_comm, bxor_bxor_id] at p',
      end
  | tw (n +1) (sum.inr (i,           v)) (sum.inl v')                  p :=
      begin
        exfalso, simp [cube_graph_alt.srctrg] at p,
        refine cube_graph_alt.edge_ext_helper n i v v' _, intro b,
        let p' := p (bxor (band tw (cube_graph_alt.num_zeros_is_odd i v)) b),
        rwa [bxor_comm, bxor_bxor_id] at p',
      end
  | tw (n +1) (sum.inr (⟨0,    pi⟩,  v)) (sum.inr (⟨0,     pi'⟩,  v')) p :=
      begin
        simp [cube_graph_alt.srctrg, vector.insert_nth, list.insert_nth] at p,
        congr, exact subtype.eq (p tt).2
      end
  | tw 1      (sum.inr (⟨0,    pz⟩,  v)) (sum.inr (⟨i' +1, psi'⟩, v')) p :=
      begin exfalso, exact nat.not_lt_zero i' (nat.pred_le_pred psi') end
  | tw 1      (sum.inr (⟨i +1, psi⟩, v)) (sum.inr (⟨0,     pz'⟩,  v')) p :=
      begin exfalso, exact nat.not_lt_zero i  (nat.pred_le_pred psi)  end
  | tw 1      (sum.inr (⟨i +1, psi⟩, v)) (sum.inr (⟨i' +1, psi'⟩, v')) p :=
      begin exfalso, exact nat.not_lt_zero i  (nat.pred_le_pred psi)  end
  | tw (n +2) (sum.inr (⟨0,    pz⟩,  v)) (sum.inr (⟨i' +1, psi'⟩, v')) p :=
      begin
        exfalso, let p' := p (bnot v'.head),
        simp [cube_graph_alt.srctrg, fin.to_succ, fin.to_zero] at p',
        rw [vector.insert_nth_succ, vector.insert_nth_zero] at p',
        simp [vector.insert_nth, list.insert_nth] at p',
        let p'' := (vector.cons_injection p').1,
        simp [fin.zero, cube_graph_alt.num_zeros_is_odd,
              fin.maybe_pred_rec] at p'', exact bnot_self p'',
      end
  | tw (n +2) (sum.inr (⟨i +1, psi⟩, v)) (sum.inr (⟨0,     pz'⟩,  v')) p :=
      begin
        exfalso, let p' := p (bnot v.head),
        simp [cube_graph_alt.srctrg, fin.to_succ, fin.to_zero] at p',
        rw [vector.insert_nth_succ, vector.insert_nth_zero] at p',
        simp [vector.insert_nth, list.insert_nth] at p',
        let p'' := (vector.cons_injection p').1,
        simp [fin.zero, cube_graph_alt.num_zeros_is_odd,
              fin.maybe_pred_rec] at p'', exact bnot_self (eq.symm p''),
      end
  | tw (n +2) (sum.inr (⟨i +1, psi⟩, v)) (sum.inr (⟨i' +1, psi'⟩, v')) p :=
      begin
        let fin_i  : fin (n +1) := ⟨i, nat.pred_le_pred psi⟩,
        let fin_i' : fin (n +1) := ⟨i', nat.pred_le_pred psi'⟩,
        simp [fin.to_succ] at p,
        suffices : ∀ b, v.head = v'.head ∧
            cube_graph_alt.srctrg tw (n + 1) b (sum.inr (fin_i,  v.tail)) =
            cube_graph_alt.srctrg tw (n + 1) b (sum.inr (fin_i', v'.tail)),
        { let e_eq := cube_graph_alt.edge_ext tw (n + 1)
                        (sum.inr (fin_i, v.tail)) (sum.inr (fin_i', v'.tail))
                        (λ b, (this b).2),
          injection e_eq with e_eq',
          injection e_eq' with i_i'_fin_eq v_v'_tail_eq,
          congr, {injection i_i'_fin_eq,},
          rw [←v.cons_head_tail, ←v'.cons_head_tail],
          rw [(this tt).1, v_v'_tail_eq],},
        suffices : ∀ (fin_i : fin (n +1)) (v : bitvec (n +1)) (b : bool),
            cube_graph_alt.srctrg tw (n + 2) b
              (sum.inr (fin.succ fin_i, v)) =
            v.head :: cube_graph_alt.srctrg tw (n + 1) (bxor (band tw v.head) b)
              (sum.inr (fin_i, v.tail)),
        { intro b,
          let p' := p (bxor (band tw v.head) b),
          rw [this, this] at p',
          let p'' := vector.cons_injection p',
          simp at p'',
          rw [←p''.1, bxor_bxor_id] at p',
          rw [←p''.1] at |-,
          exact vector.cons_injection p',},
        clear p fin_i fin_i' psi psi' i i' v v',
        intros fin_i v b,
        simp [cube_graph_alt.srctrg],
        rw ←vector.insert_nth_succ,
        cases tw, {simp,}, simp,
        suffices : cube_graph_alt.num_zeros_is_odd (fin.succ fin_i) v
                 = bxor (vector.head v)
                     (cube_graph_alt.num_zeros_is_odd fin_i (vector.tail v)),
          {rw this,},
        rw ←vector.cons_head_tail v,
        cases fin_i with i pi,
        simp [fin.succ, cube_graph_alt.num_zeros_is_odd, fin.maybe_pred_rec],
        refl,
      end

  def cube_graph_alt : graph :=
    { nodes    := cube_graph_alt.nodes n
    , edges    := cube_graph_alt.edges n
    , srctrg   := cube_graph_alt.srctrg tw n
    , edge_ext := cube_graph_alt.edge_ext tw n
    }
end

def standard_cube_graph_alt : ℕ → graph := cube_graph_alt ff
def twisted_cube_graph_alt  : ℕ → graph := cube_graph_alt tt

namespace cg_to_cg'
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
      | sum.inl v      := sum.inl (b :: v)
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
      revert b, induction n with n IH, { intro, refl,}, intro b,
      cases e with be v,
      { cases be with b' e,
        dsimp [cube_graph, prism_graph, prism_graph.srctrg,
               nodes_map, edges_map],
        rw [IH], dsimp [cube_graph_alt],
        cases edges_map tw n e with v iv,
        { dsimp [edges_map._match_1, cube_graph_alt.srctrg], refl,},
        { cases n, { cases iv with i, exact i.elim0,},
          cases iv with i v,
          dsimp [edges_map._match_1, edges_map._match_2, cube_graph_alt.srctrg],
          rw vector.insert_nth_succ,
          cases tw, {simp,}, simp,
          suffices : cube_graph_alt.num_zeros_is_odd (fin.succ i) (b' :: v)
                   = bxor b' (cube_graph_alt.num_zeros_is_odd i v), rw this,
          cases i with i_val i_p, cases v with v_l v_p,
          simp [fin.succ, vector.cons, cube_graph_alt.num_zeros_is_odd],
          refl,},},
      { transitivity (b :: nodes_map tw n v), refl,
        have : (edges_map tw (n +1) (sum.inr v)
                 : (cube_graph_alt tw (n +1)).edges)
             = (sum.inr (fin.zero, nodes_map tw n v)), refl, rw this,
        transitivity cube_graph_alt.srctrg tw (n +1) b
                       (sum.inr (fin.zero, nodes_map tw n v)),
        swap, {refl,},
        simp [cube_graph_alt.srctrg], rw [vector.insert_nth_zero], congr,
        induction n with n IH, {simp [cube_graph_alt.num_zeros_is_odd],},
        simp [fin.zero, cube_graph_alt.num_zeros_is_odd, fin.maybe_pred_rec],},
    end
end
end cg_to_cg'

def cg_to_cg' (tw : bool) (n : ℕ)
      : graph.hom (cube_graph tw n) (cube_graph_alt tw n) :=
  { nodes_map  := cg_to_cg'.nodes_map tw n
  , edges_map  := cg_to_cg'.edges_map tw n
  , srctrg_map := cg_to_cg'.srctrg_map tw n
  }

namespace cg'_to_cg
section
  variable tw : bool

  def nodes_map : Π (n : ℕ), (cube_graph_alt tw n).nodes
                           → (cube_graph tw n).nodes
  | 0      _ := unit.star
  | (n +1) v := (v.head, nodes_map n v.tail)

  def edges_map : Π (n : ℕ), (cube_graph_alt tw n).edges
                           → (cube_graph tw n).edges
  | 0      _                := unit.star
  | (n +1) (sum.inl v)      := sum.inl (v.head, edges_map n (sum.inl v.tail))
  | (n +1) (sum.inr (i, v)) := fin.maybe_pred_rec (sum.inr (nodes_map tw n v))
      (λ i' : fin n, sum.inl (match n, i', v with
                              | 0,      i', _ := i'.elim0
                              | (_ +1), _,  v := v.head
                              end, edges_map n (sum.inr (i', v.tail)))) i

  def srctrg_map : ∀ (n : ℕ) (b : bool) (e : (cube_graph_alt tw n).edges),
          nodes_map tw n ((cube_graph_alt tw n).srctrg b e)
        = (cube_graph tw n).srctrg b (edges_map tw n e)
  | 0      b e                          := rfl
  | (n +1) b (sum.inl v)                :=
      begin
        dsimp [cube_graph_alt, cube_graph_alt.srctrg],
        cases v with b'l p, cases b'l with b' l, {simp at p, contradiction,},
        simp [nodes_map, edges_map, vector.head, vector.tail],
        dunfold cube_graph, dunfold prism_graph, simp [prism_graph.srctrg],
        rw ←srctrg_map, congr,
      end
  | 1      b (sum.inr (i, v)) :=
      begin
        cases i with i_val i_is_lt, cases i_val with i'_val,
        swap, { exfalso,
          exact nat.not_succ_le_zero i'_val (nat.le_of_lt_succ i_is_lt),},
        dsimp [cube_graph_alt, cube_graph_alt.srctrg],
        rw [vector.eq_nil v, fin.to_zero, vector.insert_nth_zero],
        simp [nodes_map, fin.zero, cube_graph_alt.num_zeros_is_odd],
        simp [edges_map, fin.zero, fin.maybe_pred_rec],
        dsimp [cube_graph, prism_graph, prism_graph.srctrg, nodes_map], refl,
      end
  | (n +2) b (sum.inr (⟨0,    pz⟩,  v)) :=
      begin
        dsimp [cube_graph_alt, cube_graph_alt.srctrg],
        rw [fin.to_zero, vector.insert_nth_zero], simp [nodes_map],
        simp [fin.zero, cube_graph_alt.num_zeros_is_odd, fin.maybe_pred_rec],
        unfold1 edges_map,
        simp [fin.zero, fin.maybe_pred_rec, edges_map._match_1],
        dsimp [cube_graph, prism_graph, prism_graph.srctrg, nodes_map], refl,
      end
  | (n +2) b (sum.inr (⟨i +1, psi⟩, v)) :=
      begin
        dsimp [cube_graph_alt, cube_graph_alt.srctrg],
        rw [fin.to_succ, vector.insert_nth_succ],
        unfold1 nodes_map, simp [vector.head, fin.succ],
        simp [cube_graph_alt.num_zeros_is_odd, fin.maybe_pred_rec], symmetry,
        unfold1 edges_map, simp [fin.maybe_pred_rec, edges_map._match_1],
        dsimp [cube_graph, prism_graph, prism_graph.srctrg], congr,
        transitivity (cube_graph tw (n +1)).srctrg (bxor (vector.head v && tw) b)
          (edges_map tw (n + 1) (sum.inr (⟨i, _⟩, vector.tail v))), refl,
        rw ←srctrg_map, dsimp [cube_graph_alt, cube_graph_alt.srctrg], simp,
        have : ∀ a b c, bxor (band a b) (band a c) = band a (bxor b c),
        { intros a b c, cases a, refl, simp,}, rw this,
      end
end
end cg'_to_cg

def cg'_to_cg (tw : bool) (n : ℕ)
      : graph.hom (cube_graph_alt tw n) (cube_graph tw n) :=
  { nodes_map  := cg'_to_cg.nodes_map tw n
  , edges_map  := cg'_to_cg.edges_map tw n
  , srctrg_map := cg'_to_cg.srctrg_map tw n
  }

section
  variable tw : bool

  def cg'_cg_cg'_eq_id.nodes_map_eq : ∀ (n : ℕ) (v : (cube_graph tw n).nodes),
        cg'_to_cg.nodes_map tw n (cg_to_cg'.nodes_map tw n v) = v
  | 0      v      := begin cases v, refl end
  | (n +1) (b, v) := begin simp [cg_to_cg'.nodes_map, cg'_to_cg.nodes_map],
                           exact cg'_cg_cg'_eq_id.nodes_map_eq n v end

  def cg_cg'_cg_eq_id.nodes_map_eq : ∀ (n : ℕ)(v : (cube_graph_alt tw n).nodes),
        cg_to_cg'.nodes_map tw n (cg'_to_cg.nodes_map tw n v) = v
  | 0      v := begin change vector bool 0 at v, rw vector.eq_nil v,
                      simp [cg'_to_cg.nodes_map, cg_to_cg'.nodes_map], end
  | (n +1) v := begin simp [cg'_to_cg.nodes_map, cg_to_cg'.nodes_map],
                      rw cg_cg'_cg_eq_id.nodes_map_eq, simp, end

  def cg'_cg_cg'_eq_id.edges_map_eq : ∀ (n : ℕ) (e : (cube_graph tw n).edges),
        cg'_to_cg.edges_map tw n (cg_to_cg'.edges_map tw n e) = e
  | 0      e                := begin cases e, refl end
  | (n +1) (sum.inl (b, e)) :=
       begin
         transitivity sum.inl (b, cg'_to_cg.edges_map tw n
                                    (cg_to_cg'.edges_map tw n e)), swap,
         { congr, exact cg'_cg_cg'_eq_id.edges_map_eq n e,},
         set e' := cg_to_cg'.edges_map tw n e with ←e'_prop,
         unfold cg_to_cg'.edges_map,
         rcases cg_to_cg'.edges_map tw n e with ⟨v⟩ | ⟨i, v⟩,
         { intro e'_prop,
           unfold cg_to_cg'.edges_map._match_1, unfold cg'_to_cg.edges_map,
           rw [vector.head_cons, vector.tail_cons], congr, assumption,},
         intro e'_prop, unfold cg_to_cg'.edges_map._match_1,
         cases n with n, {exact i.elim0,}, unfold cg_to_cg'.edges_map._match_2,
         cases i, unfold fin.succ, unfold1 cg'_to_cg.edges_map,
         unfold fin.maybe_pred_rec,
         congr, { unfold cg'_to_cg.edges_map._match_1, simp,}, simp, assumption,
       end
  | (n +1) (sum.inr v)      :=
       begin
         simp [cg_to_cg'.edges_map, cg'_to_cg.edges_map],
         simp [fin.zero, fin.maybe_pred_rec],
         exact cg'_cg_cg'_eq_id.nodes_map_eq tw n v,
       end

  def cg_cg'_cg_eq_id.edges_map_eq (n : ℕ) (e : (cube_graph_alt tw n).edges) :
        cg_to_cg'.edges_map tw n (cg'_to_cg.edges_map tw n e) = e :=
    begin
      induction n with n IH,
      { dsimp [cg'_to_cg.edges_map, cg_to_cg'.edges_map],
        rcases e with ⟨⟩ | ⟨i, v⟩, {congr,}, exact i.elim0,},
      rcases e with ⟨v⟩ | ⟨i, v⟩,
      { rcases v with ⟨bl, p⟩, rcases bl with ⟨⟩ | ⟨b, l⟩, {contradiction,},
        dsimp [cg'_to_cg.edges_map, vector.head, vector.tail,
               cg_to_cg'.edges_map],
        rw IH, unfold cg_to_cg'.edges_map._match_1, refl,},
      cases i, rcases i_val with ⟨⟩ | ⟨i'_val⟩,
      { dsimp [cg'_to_cg.edges_map, fin.maybe_pred_rec, cg_to_cg'.edges_map],
        congr, apply cg_cg'_cg_eq_id.nodes_map_eq,},
      cases n,
      { exfalso, exact nat.not_succ_le_zero i'_val (nat.le_of_lt_succ i_is_lt)},
      rcases v with ⟨bl, p⟩, rcases bl with ⟨⟩ | ⟨b, l⟩, {contradiction,},
      unfold1 cg'_to_cg.edges_map, unfold1 cg'_to_cg.edges_map._match_1,
      unfold1 fin.maybe_pred_rec,
      simp [vector.head, vector.tail, cg_to_cg'.edges_map], rw IH,
      simp [cg_to_cg'.edges_map._match_1, cg_to_cg'.edges_map._match_2],
      split, {refl,}, refl,
    end

    def cg'_cg_cg'_eq_id (n : ℕ) :
          graph.hom.comp (cg_to_cg' tw n) (cg'_to_cg tw n) = graph.hom.id :=
      graph.hom.eq (funext (cg'_cg_cg'_eq_id.nodes_map_eq tw n))
                   (funext (cg'_cg_cg'_eq_id.edges_map_eq tw n))

    def cg_cg'_cg_eq_id (n : ℕ) :
          graph.hom.comp (cg'_to_cg tw n) (cg_to_cg' tw n) = graph.hom.id :=
      graph.hom.eq (funext (cg_cg'_cg_eq_id.nodes_map_eq tw n))
                   (funext (cg_cg'_cg_eq_id.edges_map_eq tw n))
end
