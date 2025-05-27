-- This is an example of lean file for proving theorems.


theorem eq_symm {alpha : Type} {a b : alpha} (h : a = b) : b = a :=
  Eq.symm h
