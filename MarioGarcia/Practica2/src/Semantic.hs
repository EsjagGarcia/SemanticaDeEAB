module Semantic where

import Sintax

-- Semántica dinámica. --

{--
    Función evals:
-}

eval1 :: Expr -> Expr
eval1 (V x) = error "Have a free variable in the evaluation."
eval1 (I n) = error "Parse error in the parameters"
eval1 (B b) = error "Parse error in the parameters"

-- Evaluación de Add.

eval1 (Add (I n) (I m)) = I (n + m)
eval1 (Add (I n) e2) = Add (I n) (eval1 e2)
eval1 (Add e1 e2) = Add (eval1 e2) e2

-- Evaluación de Mul.

eval1 (Mul (I n) (I m)) = I (n * m)
eval1 (Mul (I n) e2) = Mul (I n) (eval1 e2)
eval1 bloq@(Mul e1 e2) = if e1 == x || e2 == x
                         then bloq
                         else Mul (eval1 e1) e2
                         where x = (B True) where x = (B False)

-- Evaluación de Succ.

eval1 (Succ (I n)) = I (n+1)
eval1 bloq@(Succ (B b)) = bloq
eval1 (Succ e) = Succ (eval1 e)

-- Evaluación de Pred.

eval1 (Pred (I 0)) = I 0
eval1 (Pred (I n)) = I (n-1)
eval1 bloq@(Pred (B b)) = bloq
eval1 (Pred e) = Pred (eval1 e)

-- Evaluación de And.

eval1 (And (B b1) (B b2)) = B (b1 && b2)
eval1 bloq@(And (I n) e) = bloq
eval1 bloq@(And e (I m)) = bloq
eval1 (And (B b1) e2) = And (B b1) (eval1 e2)
eval1 (And e1 e2) = And (eval1 e1) e2

-- Evaluación de Or.

eval1 (Or (B b1) (B b2)) = B (b1 || b2)
eval1 bloq@(Or (I n) e) = bloq
eval1 bloq@(Or e (I m)) = bloq
eval1 (Or (B b1) e2) = Or (B b1) (eval1 e2)
eval1 (Or e1 e2) = Or (eval1 e1) e2

-- Evaluación de Not.

eval1 (Not (B b)) = B (not b)
eval1 bloq@(Not (I n)) = bloq
eval1 (Not e) = Not (eval1 e)

-- Evaluación de las relaciones.

eval1 (Lt (I n) (I m)) = B (n < n)
eval1 (Lt (I n) e2) = Lt (I n) (eval1 e2)
eval1 bloq@(Lt e1 e2) = if e1 == x || e2 == x
                    then bloq
                    else Lt (eval1 e1) e2
                    where x = (B True) where x = (B False)

-- Evaluación de la relación Lt.

eval1 (Gt (I n) (I m)) = B (n > m)
eval1 (Gt (I n) e2) = Gt (I n) (eval1 e2)
eval1 bloq@(Gt e1 e2) = if e1 == x || e2 == x
                    then bloq
                    else Gt (eval1 e1) e2
                    where x = (B True) where x = (B False)

-- Evaluación de la relación Gt.

eval1 (Eq (I n) (I m)) = B (n == m)
eval1 (Eq (I n) e2) = Eq (I n) (eval1 e2)
eval1 bloq@(Eq e1 e2) = if e1 == x || e2 == x
                    then bloq
                    else Eq (eval1 e1) e2
                    where x = (B True) where x = (B False)

-- Evaluación del If.

eval1 (If (B b) e1 e2) = if b
                         then e1
                         else e2
eval1 bloq@(If (I n) e1 e2) = bloq
eval1 (If e e1 e2) = If (eval1 e) e1 e2

-- Evaluación del Let.

eval1 (Let x (I n) e2) = subst e2 (x,(I n))
eval1 (Let x (B b) e2) = subst e2 (x,(B b))
eval1 (Let x e1 e2) = Let x (eval1 e1) e2

{--
    Función evals.
-}

evals :: Expr -> Expr
evals (I n) = (I n)
evals (B b) = (B b)
evals expr = if (eval1 expr) == expr
             then expr
             else evals(eval1(expr))

{--
    Función eval.
-}

eval :: Expr -> Expr
eval expr = if final(evals expr)
            then evals expr
            else error "Parse error in parameters."

final :: Expr -> Bool
final (I n) = True
final (B b) = True
final e = False

-- Semántica estática.

data Type = Integer | Boolean deriving(Eq)

type Decl = (Identifier, Type)
type TypCtxt = [Decl]

vt :: TypCtxt -> Expr -> Type -> Bool
vt [] (V x) t = False
vt ((x,t):xs) (V x1) t1 = if x == x1 && t == t1
                          then True
                          else vt xs (V x1) t1
vt _ (I n) t = t == Integer
vt _ (B b) t = t == Boolean
vt c (Add e1 e2) Integer = (vt c e1 Integer) && (vt c e2 Integer)
vt c (Mul e1 e2) Integer = (vt c e1 Integer) && (vt c e2 Integer)
vt c (Succ e) Integer = (vt c e Integer)
vt c (Pred e) Integer = (vt c e Integer)
vt c (And e1 e2) Boolean = (vt c e1 Boolean) && (vt c e2 Boolean)
vt c (Or e1 e2) Boolean = (vt c e1 Boolean) && (vt c e2 Boolean)
vt c (Not e) Boolean = (vt c e Boolean)
vt c (Lt e1 e2) Boolean = (vt c e1 Integer) && (vt c e2 Integer)
vt c (Gt e1 e2) Boolean = (vt c e1 Integer) && (vt c e2 Integer)
vt c (Eq e1 e2) Boolean = (vt c e1 Integer) && (vt c e2 Integer)
vt c (If b et ef) t = (vt c b Boolean) && (vt c et t) && (vt c ef t)
vt c (Let x e1 e2) s = if (vt c e1 Integer)
                        then vt ((x,Integer):c) e2 s
                        else vt ((x,Boolean):c) e2 s
