-- import utils
variable b : bool
#check b.rec_on
#check nat.add
inductive fin' : ℕ → Type
| zero : fin' 0
| succ : Π {n : ℕ}, fin' n → fin' (n +1)

-- example : ∀ (n : ℕ) (i : fin n), i.cast_succ = (↑i : fin (n +1)) :=

-- def foo (n : ℕ) : fin n → bool
-- | 0      := false
-- | (i +1) := true

-- def fin_cycle : Π n : ℕ, fin n → fin n
-- | (n +1) ⟨0,    _⟩ := fin.last n
-- | (n +1) ⟨i +1, p⟩ := let fin_i : fin n := ⟨i, nat.pred_le_pred p⟩
--                        in {! !} --fin.succ (fin.succ (fin_double n fin_i))

def fin_is_even : Π n : ℕ, fin n → bool
| 0      i                        := i.elim0
| (n +1) ⟨0,    _⟩                := true
| (n +1) ⟨i_val +1, succ_i_is_lt⟩ :=
     let i : fin n := ⟨i_val, nat.pred_le_pred succ_i_is_lt⟩
      in bnot (fin_is_even n i)

@[pattern]
def fin.zero {n : ℕ} : fin (n +1) := ⟨0, nat.zero_lt_succ n⟩

attribute [pattern] fin.succ

def fin_is_even' : Π n : ℕ, fin n → bool
| 0      i            := i.elim0
| (n +1) fin.zero     := true
| (n +1) (fin.succ i) := bnot (fin_is_even' n i)

I still have another question regarding `fin`.  Sometimes, I want to use pattern matching on `i : fin n` in the same way as one will do in `ℕ` but since the inductive part is in `i.val` so I need to do as follows:

```lean
def fin_is_even : Π n : ℕ, fin n → bool
| 0      i                        := i.elim0
| (n +1) ⟨0,    _⟩                := true
| (n +1) ⟨i_val +1, succ_i_is_lt⟩ :=hwere
      in bnot (fin_is_even n i)
```

Ok, it works but in practice, I find it quite annoying to write `let i : fin n := ⟨i_val, nat.pred_le_pred succ_i_is_lt⟩` every time whereas `i` should be obtained directly from something like `fin.succ i`. Therefore, I try to use `@[pattern]` to help me with this as follows:

```lean
@[pattern]
def fin.zero {n : ℕ} : fin (n +1) := ⟨0, nat.zero_lt_succ n⟩

attribute [pattern] fin.succ

def fin_is_even' : Π n : ℕ, fin n → bool
| 0      i            := i.elim0
| (n +1) fin.zero     := true
| (n +1) (fin.succ i) := bnot (fin_is_even n i)
```

However I get an error, what is wrong with my code?  Did I misunderstand anything about `@[pattern]`?

section
@[pattern]
def fin_zero {n : ℕ} : fin (n +1) := ⟨0, nat.zero_lt_succ n⟩

@[pattern]
def fin_succ {n : ℕ} : fin n → fin n.succ
| ⟨a, h⟩ := ⟨a.succ, nat.succ_lt_succ h⟩

def fin_is_zero (n : ℕ) : fin n → bool
| fin_zero     := false
| (fin_succ i) := true
end
