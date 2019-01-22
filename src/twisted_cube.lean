import category_theory.category

universe u

inductive intv : Type u
| const : bool → intv
| unk   : intv

def cube (n : ℕ) : Type (u + 1) :=
  fin n → intv

def num_unk {n : ℕ} (f : cube n) (i : fin n) : ℕ :=
  match i.val with
  | zero    := zero
  | succ i' := match f ⟨i', _⟩ with
               | const _ := num_unk f i'
               | unk     := succ (num_unk f i')
               end
  end
