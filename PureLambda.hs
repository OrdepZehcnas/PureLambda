{-|
Module      : PureLambda
Description : An implementation of the beta reduction of the Pure Lambda Calculus
Copyright   : (c) Fernando A. Galicia Mendoza, 2019
License     : GPL-3
Maintainer  : fernandogamen@ciencias.unam.mx
Stability   : experimental-education
Portability : POSIX

This script contains the functions to calculate the reduction of abstractions
of the Pure Lambda Calculus.
It's important to observe that the reduction strategy is a simulation of the
non-determinism of the following rule:

t1 -> t1' t2 -> t2'
---------------------
t1 t2 -> t1' t2'

We analize which of the terms is in normal form, e.g. if the t1 is in normal
form then we reduce the other term. In other words, we substitute the previous rule
with the two following:

(t1 is normal) t2 -> t2'
---------------------
t1 t2 -> t1 t2'

(t2 is normal) t1 -> t1'
---------------------
t1 t2 -> t1' t2
-}
module PureLambda where

  import Data.List
  import Data.Char

  -- | Type that represents the set of possible variable names.
  type Name = String

  data Lambda = V Name -- ^ Constructor for the variables.
              | App Lambda Lambda -- ^ Constructor for the applications.
              | L Name Lambda -- ^ Constructor for the abstractions.
              | Let Name Lambda Lambda -- ^ Constructor for the let.
              | LetFun Name Name Lambda Lambda -- ^ Constructor for the name functions.

  -- Instance for a pretty/decent print.
  instance Show Lambda where
    show l = case l of
      V x -> x
      App t s -> "("++show t++" <+> "++show s++")"
      L x t -> "(lam "++x++" -> "++show t++")"
      Let x t1 t2 -> "let \n"++x++":="++show t1++"\nin\n"++show t2++"\nend"
      LetFun f x t1 t2 -> "let fun \n"++f++" "++x++" "++" => "++show t1++"\nin\n"++show t2++"\nend"

  -- | Type that represents the substitution.
  type Subst = (Name,Lambda)

  -- | The desugar function unfold the definitions of let and letfun
  desugar :: Lambda -> Lambda
  desugar x = x

  -- | The fv function takes an abstraction and returns their free variables.
  fv :: Lambda -> [Name]
  fv (V x) = [x]
  fv (App t s) = fv t `union` fv s
  fv (L x t) = fv t\\[x]


  {-|
  The newId function creates a new variable with the following conditions:
  1. If at the end of the variable is not a number then the function 
  add the number 0 at the end of the variable.
  2. If at the end of the variable is a number then the function
  replace the original number with its sucessor.
  -} 
  newId :: Name -> Name
  newId x = splitName x ""

  {-|
  The splitName function tries to split strings of the form "vn" returning
  the pair (v,n) where "v" could be any string but "n" is a string with only numbers.
  If the string doesn't end with a number then "n" will be equal to the empty string.
  -}
  splitName :: Name -> Name -> Name
  splitName [] acc = acc ++ "0"
  splitName n@(x:xs) acc = case isDigit x of
    True -> acc ++ show ((read n :: Int) + 1) 
    False -> splitName xs (acc++[x])

  -- | The alpha function generates the alpha-equivalence of a lambda term.
  alpha :: Lambda -> Lambda
  alpha (V x) = V x
  alpha (App t s) = App (alpha t) (alpha s)
  alpha (L x t) = L x1 (alpha (substitution t (x,V x1))) where
    x1 = newId x

  -- | The substitution function applies the substitution given as a parameter to a lambda term.
  substitution :: Lambda -> Subst -> Lambda
  substitution (V x) (y,t) = if x == y then t else V x
  substitution (App t r) s = App (substitution t s) (substitution r s)
  substitution (L y t) s@(x,r) = case not (y `elem` ([x]`union`fv r)) of
    True -> L y (substitution t s)
    False -> let l' = alpha (L y t) in substitution l' s

  -- | The beta function is an implementation of the beta reduction.
  beta :: Lambda -> Lambda
  beta (App (L x t) r) = substitution t (x,r)
  beta (App t1 t2) = if normal t1 then App t1 (beta t2) else App (beta t1) t2
  beta (L x t) = L x t' where
    t' = beta t

  -- | The normal function is the predicate that is True iff a lambda term is in normal form.
  normal :: Lambda -> Bool
  normal (V x) = True
  normal (L x t) = normal t
  normal (App t1 t2) = case t1 of
    (L x _) -> False
    _ -> normal t1 && normal t2

  {-| 
  The betas function is a implementation of the reflexive-transitive closure of the beta
  reduction. Before the application of the beta reduction, this function test if the lambda
  term is in normal form.
  -}
  betas' :: Lambda -> Lambda
  betas' t = case normal t of 
    True -> t
    _ -> betas' $ beta t

  betas :: Lambda -> Lambda
  betas t = betas' t

  -- A list of examples.

  t1 = (App (L "n" (L "s" (L "z" (App (V "s") (App (App (V "n") (V "s")) (V "z")))))) (L "s" (L "z" (V "z"))))

  t2 = App (L "x" (L "y" (App (V "x") (L "z" (App (V "y") (V "z")))))) (L "s" (App (L "z" (V "z")) (V "y")))

  omega = L "x" (App (V "x") (V "x"))

  wow_example = betas (App omega omega) --Infinite applications! :3

  true = L "x" (L "y" (V "x"))
  false = L "x" (L "y" (V "y"))

  ift = L "v" (L "t" (L "f" (App (App (V "v") (V "t")) (V "f"))))

  if0 = betas (App (App (App ift true) zeroC) oneC)  
  if1 = betas (App (App (App ift false) zeroC) oneC)

  notL = L "z" (App (App (V "z") false) true)

  example1 = betas (App notL true) --Result: false

  andL = L "x" (L "y" (App (App (V "x") (V "y")) false))

  example2 = betas (App (App andL true) true) --Result: true
  example3 = betas (App (App andL true) false) --Result: false

  orL = L "x" (L "y" (App notL (App (App andL (App notL (V "x"))) (App notL (V "y")))))

  example4 = betas (App (App orL true) true) --Result: true
  example5 = betas (App (App orL false) false) --Result: false  

  zeroC = L "s" (L "z" (V "z"))

  oneC = L "s" (L "z" (App (V "s") (V "z")))

  sucC = L "n" (L "s" (L "z" (App (V "s") (App (App (V "n") (V "s")) (V "z")))))

  suc1 = betas (App sucC oneC)
  suc2 = betas (App sucC suc1)
  suc3 = betas (App sucC suc2)  

  suma = L "m" (L "n" (App (V "n") (App sucC (V "m"))))

  suma_01 = betas (App (App suma zeroC) oneC)

  suma_11 = betas (App (App suma oneC) oneC)

  suma_12 = betas (App (App suma oneC) suc3)
  suma_21 = betas (App (App suma suc3) oneC)

  prod = L "m" (L "n" (App (App (V "m") (App suma (V "n"))) zeroC) )

  prod_11 = betas (App (App prod oneC) suma_11)

  isZero = L "m" (App (App (V "m") (L "x" (false))) true)

  is0 = betas (App isZero zeroC)
  is1 = betas (App isZero oneC)  

  pair = L "f" (L "s" (L "b" (App (App (V "b") (V "f")) (V "s"))))

  fstC = L "p" (App (V "p") true)

  sncC = L "p" (App (V "p") false)

  zz = (App (App pair zeroC) zeroC)
  zz2 = (App (App pair suc3) oneC)
  zz3 = (App (App pair oneC) suc3)

  pair0 = betas (App fstC zz2)

  pair1 = betas (App sncC zz3) 

  ss = L "p" (App (App pair (App sncC (V "p"))) (App sucC (App sncC (V "p"))) )

  predC = L "m" (App fstC (App (App (V "m") ss) zz))

  pred1 = betas (App predC oneC)

  pred0 = betas (App predC oneC)

  pred2 = betas (App predC suma_11)

   -- Fixed point combinator Y
  curry_rosser_fix = L "f" (App 
                    (L "x" (App (V "f") (App (V "x") (V "x")))) 
                    (L "x" (App (V "f") (App (V "x") (V "x"))))
                    )

  -- Fixed point combinator V
  turingfix = App u u where
    u = L "f" (L "x" (App (V "x") (App (App (V "f") (V "f")) (V "x"))))

  gsum = L "f" (L "n" (L "m" (App (App (App ift (App isZero (V "n"))) (App (App suma (V "m")) zeroC)) (App (App suma oneC) (App (App (V "f") (App predC (V "n"))) (V "m"))) )))  

  -- g_fac = L "f" (L "n" (Ift (Equi (V "n") (N 0)) (N 1) (Prod (V "n") (App (V "f") (Pred (V "n"))))))

  --letf = betas (App (L "f" (App (V "f") (V "p"))) ())

  crsum = betas (App (L "suma" (App (App (V "suma") oneC) oneC)) (L "y" (L "x" (App (App (App curry_rosser_fix gsum) (V "x")) (V "y")) ) ))

  -- desugar (Let x t1 t2) = App (L x (desugar t2)) (desugar t1)
  -- desugar (LetFun f x t1 t2) = desugar (Let f (L x t1) t2)

  --fac_curry_rosser = LetFun "fac" "x" (App (App curry_rosser_fix g) (V "x")) (App (V "fac") (N 4))
  -- Let "fac" (L "x" (App (App curry_rosser_fix g) (V "x"))) (App (V "fac") (N 4))
  -- (App (L "fac" (App (V "fac") (N 4))) (L "x" (App (App curry_rosser_fix g) (V "x"))))


  --example0 = (Let "one" oneC (Let "suc" sucC (App (V "suc") (V "one")))) 

  example6 = betas (App sucC zeroC) --Result: one
  example7 = betas (App sucC oneC) --Result: two
  example8 = betas (App sucC example7) --Result: three

  plusC = L "m" (L "n" (App (App (V "n") sucC) (V "m")))

  example9 = betas (App (App plusC example8) example8) --Result: four

  example_01 = betas (App (App true (V "0")) (V "1"))
  example_10 = betas (App (App false (V "0")) (V "1"))
  



  id2 = betas (App (L "x" (V "x")) zeroC)