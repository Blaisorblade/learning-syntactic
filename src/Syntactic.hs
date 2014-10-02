{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverlappingInstances #-}

module Syntactic where

-- Following Emil Axelsson, "A Generic Abstract Syntax Model for Embedded
-- Languages", ICFP 2012, http://doi.acm.org/10.1145/2364527.2364573.

-- Sec. 2.2

newtype Full a  = Full { result :: a }
newtype a :-> b = Partial (a -> b)
infixr :->

-- | dom is the type of allowed symbols (see the direct use in the Sym
-- constructor), so it describes the primitives available in an AST.

data AST dom sig where
  Sym  :: dom sig -> AST dom sig
  (:$) :: AST dom (a :-> sig) -> AST dom (Full a) -> AST dom sig

type ASTF dom res = AST dom (Full res)

infixl 1 :$

-- A valid dom. (Nominal subtyping would help here).
data NUM a where
  -- Num :: Int -> NUM Int -- NO! FAils at zeroPOne
  Num :: Int -> NUM (Full Int)
  Add :: NUM (Int :-> Int :-> Full Int)
  Mul :: NUM (Int :-> Int :-> Full Int)

type Expr3 a = ASTF NUM a

num3 :: Int -> Expr3 Int
num3 = Sym . Num

add3 :: Expr3 Int -> Expr3 Int -> Expr3 Int
add3 a b = Sym Add :$ a :$ b

-- Examples
zero3, zeroPOne3, zeroPZeroPOne3 :: Expr3 Int

zero3 = num3 0
zeroPOne3 = add3 zero3 $ num3 1
zeroPZeroPOne3 = add3 zero3 zeroPOne3

-- Sec. 2.3
evalNUM :: Expr3 a -> a
evalNUM (Sym (Num n)) = n
evalNUM (Sym Add :$ a :$ b) = evalNUM a + evalNUM b
evalNUM (Sym Mul :$ a :$ b) = evalNUM a * evalNUM b

renderNUM :: Expr3 a -> String
renderNUM (Sym (Num n)) = show n
renderNUM (Sym Add :$ a :$ b) = "(" ++ renderNUM a ++ " + " ++ renderNUM b ++ ")"
renderNUM (Sym Mul :$ a :$ b) = "(" ++ renderNUM a ++ " * " ++ renderNUM b ++ ")"

-- Sec. 3

--- Listing 1.

data (dom1 :+: dom2) a where
  InjL :: dom1 a -> (dom1 :+: dom2) a
  InjR :: dom2 a -> (dom1 :+: dom2) a

--- Listing 2, altered according to syntactic 2.0.
data Empty

-- | sup is a sum which can also contains sub.
class Project sub sup where
  prj :: sup a -> Maybe (sub a)

instance Project sub sup where
  prj _ = Nothing

instance Project sub sub where
  prj = Just

instance Project sym1 (sym1 :+: sym3) where
  prj (InjL c) = Just c
  prj (InjR _) = Nothing

instance Project sym1 sym3 => Project sym1 (sym2 :+: sym3) where
  prj (InjL _) = Nothing
  prj (InjR c) = prj c

instance Project sub sup => Project sub (AST sup) where
  prj (Sym a) = prj a
  prj (a :$ b) = Nothing

-- | sup is a sum which must contains sub.

class Project sub sup => (sub :<: sup) where
  inj :: sub a -> sup a

instance (sub :<: sub) where
  inj = id

instance sym1 :<: (sym1 :+: sym3) where
  inj = InjL

instance (sym1 :<: sym3) => sym1 :<: (sym2 :+: sym3) where
  inj = InjR . inj

instance (sub :<: sup) => sub :<: AST sup where
  inj = Sym . inj

--- End Listing 2

data Logic a where
  Not :: Logic (Bool :-> Full Bool)
  Eq  :: Eq a => Logic (a :-> a :-> Full Bool)

data If a where
  If :: If (Bool :-> a :-> a :-> Full a)

type Expr a = ASTF (NUM :+: Logic :+: If) a
