module Semantic where

import Sintax

eval1 :: Expr -> Expr
eval1 (V x) = error "Have a free variable in the evaluation."
eval1 (I n) = I n
eval1 (B b) = B b
eval1 (Add (I n) (I m)) = I (n + m)
eval1 (Add (I n) e2) = Add (I n) (eval1 e2)
eval1 (Add e1 e2) = Add (eval1 e1) e2
eval1 (Mul (I n) (I m)) = I (n * m)
eval1 (Mul (I n) e2) = Mul (I n) (eval1 e2)
eval1 (Mul e1 e2) = Mul (eval1 e1) e2
eval1 (Succ (I n)) = I (n+1)
eval1 (Succ e) = Succ (eval1 e)
eval1 (Pred (I n)) = I (n-1)
eval1 (Pred e) = Pred (eval1 e)
eval1 (And (B b1) (B b2)) = B (b1 && b2)
eval1 (And (B b1) e2) = And (B b1) (eval1 e2)
eval1 (And e1 e2) = And (eval1 e1) e2
eval1 (Or (B b1) (B b2)) = B (b1 || b2)
eval1 (Or (B b1) e2) = Or (B b1) (eval1 e2)
eval1 (Or e1 e2) = Or (eval1 e1) e2
eval1 (Not (B b)) = B (not b)
eval1 (Not e) = Not (eval1 e)
eval1 (Lt (I n) (I m)) = B (n < n)
eval1 (Lt (I n) e2) = Lt (I n) (eval1 e2)
eval1 (Lt e1 e2) = Lt (eval1 e1) e2
eval1 (Gt (I n) (I m)) = B (n > m)
eval1 (Gt (I n) e2) = Gt (I n) (eval1 e2)
eval1 (Gt e1 e2) = Gt (eval1 e1) e2
eval1 (Eq (I n) (I m)) = B (n == m)
eval1 (Eq (I n) e2) = Eq (I n) (eval1 e2)
eval1 (Eq e1 e2) = Eq (eval1 e1) e2
eval1 (If (B b) e1 e2) = if b
                         then e1
                         else e2
eval1 (If e e1 e2) = If (eval1 e) e1 e2
eval1 (Let x (I n) e2) = subst e2 (x,(I n))
eval1 (Let x (B b) e2) = subst e2 (x,(B b))
eval1 (Let x e1 e2) = Let x (eval1 e1) e2

evals :: Expr -> Expr
evals (I n) = (I n)
evals (B b) = (B b)
evals o@(Add e1 e2) = if e1 /= (B True) && e2 /= (B True)
                      then evals(eval1(o))
                      else o
evals o@(Mul e1 e2) = evals(eval1(o))
evals o@(Succ e) = evals(eval1(o))
evals o@(Pred e) = evals(eval1(o))
evals o@(And e1 e2) = evals(eval1(o))
evals o@(Or e1 e2) = evals(eval1(o))
evals o@(Not e) = evals(eval1(o))
evals o@(Lt e1 e2) = evals(eval1(o))
evals o@(Gt e1 e2) = evals(eval1(o))
evals o@(Eq e1 e2) = evals(eval1(o))
evals o@(If b e1 e2) = evals(eval1(o))
