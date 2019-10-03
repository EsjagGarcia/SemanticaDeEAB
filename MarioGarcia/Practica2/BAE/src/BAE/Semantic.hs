module BAE.Semantic where

import BAE.Sintax

----------------------------- Semántica dinámica. ------------------------------

{--
    Función eval1:

    La función implementa la definición de un paso de ejecución para las expre-
    siones del lenguaje Aritmético-Booleanas.
-}

eval1 :: Expr -> Expr

eval1 (V x) = error "Have a free variable in the evaluation."
eval1 (I n) = error "Error in the parameters"
eval1 (B b) = error "Error in the parameters"

eval1 (Add (I n) (I m)) = I (n + m)
eval1 (Add _ (B b)) = error "[Add] expected two Integer."
eval1 (Add (I n) e2) = Add (I n) (eval1 e2)
eval1 (Add (B b) _) = error "[Add] expected two Integer."
eval1 (Add e1 e2) = Add (eval1 e1) e2

eval1 (Mul (I n) (I m)) = I (n * m)
eval1 (Mul _ (B b)) = error "[Mul] expected two Integer."
eval1 (Mul (I n) e2) = Mul (I n) (eval1 e2)
eval1 (Mul (B b) _) = error "[Mul] expected two Integer."
eval1 (Mul e1 e2) = Mul (eval1 e1) e2

eval1 (Succ (I n)) = I (n+1)
eval1 (Succ (B b)) = error "[Succ] expected two Integer."
eval1 (Succ e) = Succ (eval1 e)

eval1 (Pred (I 0)) = I 0
eval1 (Pred (I n)) = I (n-1)
eval1 (Pred (B b)) = error "[Pred] expected two Integer."
eval1 (Pred e) = Pred (eval1 e)

eval1 (And (B b1) (B b2)) = B (b1 && b2)
eval1 (And _ (I m)) = error "[And] expected two Boolean."
eval1 (And (B b1) e2) = And (B b1) (eval1 e2)
eval1 (And (I n) _) = error "[And] expected two Boolean."
eval1 (And e1 e2) = And (eval1 e1) e2

eval1 (Or (B b1) (B b2)) = B (b1 || b2)
eval1 (Or _ (I m)) = error "[Or] expected two Boolean."
eval1 (Or (B b1) e2) = Or (B b1) (eval1 e2)
eval1 (Or (I n) _) = error "[Or] expected two Boolean."
eval1 (Or e1 e2) = Or (eval1 e1) e2

eval1 (Not (B b)) = B (not b)
eval1 (Not (I n)) = error "[Not] expected two Integer."
eval1 (Not e) = Not (eval1 e)

eval1 (Lt (I n) (I m)) = B (n < m)
eval1 (Lt _ (B b2)) = error "[Lt] expected two Integer."
eval1 (Lt (I n) e2) = Lt (I n) (eval1 e2)
eval1 (Lt (B b1) _) = error "[Lt] expected two Integer."
eval1 (Lt e1 e2) = Lt (eval1 e1) e2

eval1 (Gt (I n) (I m)) = B (n > m)
eval1 (Gt _ (B b2)) = error "[Gt] expected two Integer."
eval1 (Gt (I n) e2) = Gt (I n) (eval1 e2)
eval1 (Gt (B b1) _) = error "[Gt] expected two Integer."
eval1 (Gt e1 e2) = Gt (eval1 e1) e2

eval1 (Eq (I n) (I m)) = B (n == m)
eval1 (Eq _ (B b2)) = error "[Eq] expected two Integer."
eval1 (Eq (I n) e2) = Eq (I n) (eval1 e2)
eval1 (Eq (B b1) _) = error "[Eq] expected two Integer."
eval1 (Eq e1 e2) = Eq (eval1 e1) e2

eval1 (If (B b) e1 e2) = if b
                         then e1
                         else e2
eval1 (If (I n) e1 e2) = error "[If] expected a boolean condition."
eval1 (If e e1 e2) = If (eval1 e) e1 e2

-- Haciendo una evaluación perezosa.

eval1 (Let x e1 e2) = subst e2 (x,e1)

{--
    isBloqued:

    Determina sí un estado está bloqueado, esto ocurre cuando no sé puede seguir
    evaluando la expresión.
-}

isBloqued :: Expr -> Bool
isBloqued (I n) = True
isBloqued (B b) = True
isBloqued (V x) = True
isBloqued (Add (B b) _) = True
isBloqued (Add _ (B b)) = True
isBloqued (Mul (B b) _) = True
isBloqued (Mul _ (B b)) = True
isBloqued (Succ (B b)) = True
isBloqued (Pred (B b)) = True
isBloqued (And (I n) _) = True
isBloqued (And _ (I n)) = True
isBloqued (Or (I n) _) = True
isBloqued (Or _ (I n)) = True
isBloqued (Not (I n)) = True
isBloqued (Lt (B b) _) = True
isBloqued (Lt _ (B b)) = True
isBloqued (Gt (B b) _) = True
isBloqued (Gt _ (B b)) = True
isBloqued (Eq (B b) _) = True
isBloqued (Eq _ (B b)) = True
isBloqued (If (I n) _ _) = True
isBloqued _ = False

{--
    Función evals:

    La función implementa la cerradura, devolviendo la evaluación de la expre-
    sión de entrada hasta un estado bloqueado, sin importar si este es inicial o
    final.
-}

evals :: Expr -> Expr
evals expr = if isBloqued expr
             then expr
             else evals(eval1(expr))

{--
    isFinal:

    El programa decide si un estado es final. Esto es si y solo si dicho estado
    esta bloqueado y es un valor.
-}

isFinal :: Expr -> Bool
isFinal (I n) = True
isFinal (B b) = True
isFinal e = False

{--
    evale:

    Evalua una expresión hasta llegar a un estado final, de no ocurrir esto, sig-
    nifica que ha ocurrido un error de ejecución, en cuyo caso, devolvemos dicho
    error.
-}
evale :: Expr -> Expr
evale expr = if isFinal(evals expr)
             then evals expr
             else evale(eval1 expr)

-------------------------- Semántica estática. ----------------------------------

-- Dos tipos posibles, entero y booleano. Que necesitamos que sean comparables.

data Type = Integer | Boolean
            deriving(Eq)

type Decl = (Identifier, Type)
type TypCtxt = [Decl]

{--
    vt:

    Verifica el tipo de una expresión de manera que para cada caso, aplicando pa-
    ra cada caso, la regla que le corresponda.
-}
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
vt c (Let x e1 e2) t = if (vt c e1 Integer)
                       then vt ((x,Integer):c) e2 t
                       else vt ((x,Boolean):c) e2 t
vt _ _ _ = error "Error in types."

{--
    eval:

    Primero verifica que el tipo de la expresión sea el correcto. Sí es correcto,
    entonces hace la evaluación. En caso de que no lo sea, devuelve un error re-
    lacionado con los tipos de las entradas.
-}
eval :: Expr -> Type -> Expr
eval e t = if vt [] e t
           then evale e
           else error "Error in the type of parameters."
