module Sintax where

import Data.List

-- Usamos un Identificador de variables. --

type Identifier = String

-- Definimos la síntaxis abstracta para nuestro lenguaje. --

data Expr = V Identifier | I Int | B Bool
           | Add Expr Expr | Mul Expr Expr
           | Succ Expr | Pred Expr
           | And Expr Expr | Or Expr Expr
           | Not Expr
           | Lt Expr Expr | Gt Expr Expr | Eq Expr Expr
           | If Expr Expr Expr
           | Let Identifier Expr Expr
           deriving (Eq)

{--
   Instancia de Show que imprime las expresiones de nuestra síntaxis abstracta
   en síntaxis abstracta de orden superior para poder ser más facil de visuali-
   zar y de comprenderlas.
-}

instance Show Expr where
 show e = case e of
   (V x) -> "var[" ++ x ++ "]"
   (I n) -> "num[" ++ (show n) ++ "]"
   (B b) -> "bool[" ++ (show b) ++ "]"
   (Add e1 e2) -> "add(" ++ (show e1) ++ "," ++ (show e2) ++ ")"
   (Mul e1 e2) -> "mul(" ++ (show e1) ++ "," ++ (show e2) ++ ")"
   (Succ e) -> "succ(" ++ (show e) ++ ")"
   (Pred e) -> "pred(" ++ (show e) ++ ")"
   (Not e) -> "not(" ++ (show e) ++ ")"
   (And e1 e2) -> "and(" ++ (show e1) ++ "," ++ (show e2) ++ ")"
   (Or e1 e2) -> "or(" ++ (show e1) ++ "," ++ (show e2) ++ ")"
   (Lt e1 e2) -> "lt(" ++ (show e1) ++ "," ++ (show e2) ++ ")"
   (Gt e1 e2) -> "gt(" ++ (show e1) ++ "," ++ (show e2) ++ ")"
   (Eq e1 e2) -> "eq(" ++ (show e1) ++ "," ++ (show e2) ++ ")"
   (If e1 e2 e3) -> "if(" ++ (show e1) ++ "," ++ (show e2) ++ "," ++ (show e3) ++ ")"
   (Let x e1 e2) -> "let(" ++ (show e1) ++ "," ++ x ++ "." ++ (show e2) ++ ")"

type Substitution = (Identifier, Expr)

{--
   1) frVars: obtiene las variables libres de una expresión.
-}

frVars :: Expr -> [Identifier]
frVars (V x) = [x]
frVars (I n) = []
frVars (B b) = []
frVars (Add e1 e2) = union (frVars e1) (frVars e2)
frVars (Mul e1 e2) = union (frVars e1) (frVars e2)
frVars (Succ e) = (frVars e)
frVars (Pred e) = (frVars e)
frVars (Not e) = (frVars e)
frVars (And e1 e2) = union (frVars e1) (frVars e2)
frVars (Or e1 e2) = union (frVars e1) (frVars e2)
frVars (Lt e1 e2) = union (frVars e1) (frVars e2)
frVars (Gt e1 e2) = union (frVars e1) (frVars e2)
frVars (Eq e1 e2) = union (frVars e1) (frVars e2)
frVars (If e1 e2 e3) = union (union (frVars e1) (frVars e2)) (frVars e3)
frVars (Let x e1 e2) = union (frVars e1) (delete x (frVars e2))

{--
   2) subst: sustituye de ser posible el valor de x por la expresión r en todas
   sus ocurrencias en la expresión, para lograrlo, definimos la función recursi-
   vamente sobre cada regla de la definición de las expresiones de nuestro len-
   guaje.
-}
subst :: Expr -> Substitution -> Expr
subst (V x) (y,r) = if x == y
                    then r
                    else (V x)
subst (I n) (_,_) = (I n)
subst (B b) (_,_) = (B b)
subst (Add e1 e2) s = Add (subst e1 s) (subst e2 s)
subst (Mul e1 e2) s = Mul (subst e1 s) (subst e2 s)
subst (Succ e) s = Succ (subst e s)
subst (Pred e) s = Pred (subst e s)
subst (Not e) s = Not (subst e s)
subst (And e1 e2) s = And (subst e1 s) (subst e2 s)
subst (Or e1 e2) s = Or (subst e1 s) (subst e2 s)
subst (Lt e1 e2) s = Lt (subst e1 s) (subst e2 s)
subst (Gt e1 e2) s = Gt (subst e1 s) (subst e2 s)
subst (Eq e1 e2) s = Eq (subst e1 s) (subst e2 s)
subst (If e1 e2 e3) s = If (subst e1 s) (subst e2 s) (subst e3 s)
subst (Let z e1 e2) es@(x,r) = if x == z
                               then Let z (subst e1 es) e2
                               else if (notElem z (frVars r))
                                    then Let z (subst e1 es) (subst e2 es)
                                    else error "Could not apply the substitution."

{--
   3) alphaEq: Dadas dos expresiones nos dice sí son alfa equivalentes, es decir
   que son las mismas expresiones difiriento solamente en los nombres de sus va-
   riables ligadas.
-}
alphaEq :: Expr -> Expr -> Bool
alphaEq (V x) (V y) = True -- Aquí que pedo???
alphaEq (I n) (I m) = n == m
alphaEq (B b) (B c) = b == c
alphaEq e@(Add e1 e2) f@(Add f1 f2) = ((frVars e) == (frVars f)) && (alphaEq e1 f1) && (alphaEq e2 f2)
alphaEq e@(Mul e1 e2) f@(Mul f1 f2) = ((frVars e) == (frVars f)) && (alphaEq e1 f1) && (alphaEq e2 f2)
alphaEq e@(Succ e1) f@(Succ f1) = ((frVars e) == (frVars f)) && (alphaEq e1 f1)
alphaEq e@(Pred e1) f@(Pred f1) = ((frVars e) == (frVars f)) && (alphaEq e1 f1)
alphaEq e@(Not e1) f@(Not f1) = ((frVars e) == (frVars f)) && (alphaEq e1 f1)
alphaEq e@(And e1 e2) f@(And f1 f2) = ((frVars e) == (frVars f)) && (alphaEq e1 f1) && (alphaEq e2 f2)
alphaEq e@(Or e1 e2) f@(Or f1 f2) = ((frVars e) == (frVars f)) && (alphaEq e1 f1) && (alphaEq e2 f2)
alphaEq e@(Lt e1 e2) f@(Lt f1 f2) = ((frVars e) == (frVars f)) && (alphaEq e1 f1) && (alphaEq e2 f2)
alphaEq e@(Gt e1 e2) f@(Gt f1 f2) = ((frVars e) == (frVars f)) && (alphaEq e1 f1) && (alphaEq e2 f2)
alphaEq e@(Eq e1 e2) f@(Eq f1 f2) = ((frVars e) == (frVars f)) && (alphaEq e1 f1) && (alphaEq e2 f2)
alphaEq e@(If e1 e2 e3) f@(If f1 f2 f3) = ((frVars e) == (frVars f)) && (alphaEq e1 f1) && (alphaEq e2 f2) && (alphaEq e3 f3)
alphaEq e@(Let x e1 e2) f@(Let y f1 f2) = if x == y
                                          then (alphaEq e1 f1) && (alphaEq e2 f2) && ((frVars e) == (frVars f))
                                          else (alphaEq e1 f1) && (alphaEq e2 (subst f2 (y,V x))) && ((frVars e) == (frVars f))
alphaEq _ _ = False
