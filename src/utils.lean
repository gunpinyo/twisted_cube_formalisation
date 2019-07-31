import data.bitvec
import data.vector2

def bxor_bxor_id (a b : bool) : bxor a (bxor a b) = b :=
  begin cases a, simp, simp, end

def bxor_comm (a b : bool) : bxor a b = bxor b a :=
  begin cases a, simp, simp, end

def bnot_self {a : bool} : ¬ (bnot a = a) :=
  begin intro p, cases a, all_goals {contradiction}, end

namespace fin

def zero {n : ℕ} : fin (n +1) := ⟨0, nat.zero_lt_succ n⟩

def to_zero {n : ℕ} {p : 0 < n +1} :
      (⟨0, p⟩ : fin (n +1)) = fin.zero := rfl
def to_succ {n i : ℕ} {p : i +1 < n +1} :
      (⟨i +1, p⟩ : fin (n +1)) = fin.succ ⟨i, nat.pred_le_pred p⟩ := rfl

def maybe_pred_rec {n : ℕ} {α : Type*} (a : α) (f : fin n → α)
      : fin (n +1) → α
| ⟨0,    _⟩                := a
| ⟨i +1, succ_i_lt_succ_n⟩ := f ⟨i, nat.pred_le_pred succ_i_lt_succ_n⟩

end fin

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
    cases vector.tail sv  with l  p,
    cases vector.tail sv' with l' p',
    simp [vector.cons], exact λ x y, ⟨x, y⟩,
  end

def vector.insert_nth_zero : v.insert_nth a fin.zero = a :: v :=
  begin
    cases v with l p,
    simp [fin.zero, vector.insert_nth, vector.cons, list.insert_nth],
  end

def vector.insert_nth_succ {i : fin (n +1)}
      : sv.insert_nth a (fin.succ i) = sv.head :: (sv.tail).insert_nth a i :=
  begin
    rw [←sv.cons_head_tail, vector.head_cons, vector.tail_cons],
    cases sv.tail with l p,
    cases i with i_val i_lt,
    unfold fin.succ, apply vector.eq,
    simp [vector.insert_nth, list.insert_nth, vector.cons],
  end

end
