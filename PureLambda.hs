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

  id2 = betas (App (L "x" (V "x")) zeroC)
