Inductive result (T S : Type) :=
| Result : T -> S -> result T S.

Arguments Result [T S].
