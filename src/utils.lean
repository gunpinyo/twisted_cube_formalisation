import data.bitvec
import data.vector2

namespace fin

def zero {n : ℕ} : fin (nat.succ n) := ⟨nat.zero, nat.zero_lt_succ n⟩

end fin

def hetero_to_homo_eq {α β : Type} {x : α} {y : β} :
          Π p : x == y, (eq.rec_on (type_eq_of_heq (p : x == y)) x : β) = y :=
  assume h,
  by cases h; refl


def vector.insert_nth_succ {α : Type*} {n : ℕ} (a : α) (v : vector α n)
                    (b : α) (i : fin (n +1))
      : vector.insert_nth b (fin.succ i) (a :: v)
          = a :: vector.insert_nth b i v :=
  begin
    cases v with l p,
    cases i with i_val i_lt,
    unfold vector.cons,
    unfold fin.succ,
    apply vector.eq,
    dunfold vector.insert_nth,
    simp,
    dunfold list.insert_nth,
    dunfold list.modify_nth_tail,
    refl
  end
