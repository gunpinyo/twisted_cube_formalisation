import data.bitvec
import data.vector2

-- def function.comp_n_times {α : Type*} (f : α → α) : ℕ → α → α
-- | 0      := id
-- | (n +1) := f ∘ (function.comp_n_times n)

def bxor_bxor_id (a b : bool) : bxor a (bxor a b) = b :=
  begin cases a, simp, simp, end

def bxor_comm (a b : bool) : bxor a b = bxor b a :=
  begin cases a, simp, simp, end

def bnot_self {a : bool} : ¬ (bnot a = a) :=
  begin intro p, cases a, all_goals {contradiction}, end

-- def nat.add_le_add {n m l : ℕ} : n + l ≤ m + l → n ≤ m :=
--   begin intro p, induction l with l IH, {assumption,}, simp at p, assumption end

section
variable {n : ℕ}

def fin.zero : fin (n +1) := ⟨0, nat.zero_lt_succ n⟩

@[simp]
def fin.mk_from_succ (i : ℕ) (p_succ_i : i +1 < n +1) : fin n :=
      ⟨i, nat.pred_le_pred p_succ_i⟩

def fin.succ_injection {i i' : fin n} : i.succ = i'.succ → i = i' :=
      begin cases i, cases i', intro p, simp [fin.succ] at p |-, assumption, end

def fin.to_zero {p : 0 < n +1} :
      (⟨0, p⟩ : fin (n +1)) = fin.zero := rfl
def fin.to_succ {i : ℕ} {p : i +1 < n +1} :
      (⟨i +1, p⟩ : fin (n +1)) = (fin.mk_from_succ i p).succ := rfl

def fin.elim_out_of_bound {α : Sort*} {i m : ℕ} (p : i + m < m) : α :=
      begin
        exfalso, induction m with m IH,
        {simp at p, exact nat.not_lt_zero i p,},
        have : i + nat.succ m = nat.succ (i + m), {refl,}, rw this at p,
        exact IH (nat.le_of_succ_le_succ p),
      end
end

@[simp]
def fin.maybe_pred_rec {n : ℕ} {α : Type*} (a : α) (f : fin n → α)
      : fin (n +1) → α
| ⟨0,    _⟩                := a
| ⟨i +1, succ_i_lt_succ_n⟩ := f ⟨i, nat.pred_le_pred succ_i_lt_succ_n⟩


def hetero_to_homo_eq {α β : Type} {x : α} {y : β} :
          Π p : x == y, (eq.rec_on (type_eq_of_heq (p : x == y)) x : β) = y :=
  assume h,
  by cases h; refl

section
variables {α : Type*} {n : ℕ} {a : α}
variables {v : vector α n} {sv sv' : vector α (n +1)}

def vector.cons_injection :
      sv = sv' → sv.head = sv'.head ∧ sv.tail = sv'.tail :=
  begin
    rw [←sv.cons_head_tail, ←sv'.cons_head_tail],
    rw [vector.head_cons, vector.tail_cons, vector.head_cons, vector.tail_cons],
    cases vector.tail sv  with l  p, cases vector.tail sv' with l' p',
    simp [vector.cons], exact λ x y, ⟨x, y⟩,
  end

def vector.insert_nth_zero : v.insert_nth a fin.zero = a :: v :=
  begin
    cases v with l p,
    simp [fin.zero, vector.insert_nth, vector.cons, list.insert_nth],
  end

def vector.insert_nth_succ {i : fin (n +1)}
      : sv.insert_nth a i.succ = sv.head :: (sv.tail).insert_nth a i :=
  begin
    rw [←sv.cons_head_tail, vector.head_cons, vector.tail_cons],
    cases sv.tail with l p, cases i with i_val i_lt,
    unfold fin.succ, apply vector.eq,
    simp [vector.insert_nth, list.insert_nth, vector.cons],
  end

end
