import data.bitvec
import data.vector2

notation α + β := sum α β

namespace fin

def zero {n : ℕ} : fin (nat.succ n) := ⟨nat.zero, nat.zero_lt_succ n⟩

end fin

namespace vector
variable {n : ℕ}
variable {α : Type _}

def my_cons (a : α) (v : vector α n) : vector α (nat.succ n) :=
  v.insert_nth a fin.zero

def eq_from_list : Π {a b : vector α n}, a.val = b.val → a = b
| ⟨l, p⟩ ⟨.(l), .(p)⟩ rfl := rfl

-- def my_insert_nth (a : α) : fin (nat.succ n) → vector α n
--                                              → vector α (nat.succ n)
-- | fin.succ ()

end vector
