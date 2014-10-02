{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UnicodeSyntax #-}

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
  -- Num :: Int -> NUM Int -- NO! Fails at zeroPOne
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

infixr :+: -- We need this line because left-nested uses don't fully work --
           -- commenting this out makes exSize3 fail.

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

--- Listing 3
data Logic a where
  Not :: Logic (Bool :-> Full Bool)
  Eq  :: Eq a => Logic (a :-> a :-> Full Bool)

data If a where
  If :: If (Bool :-> a :-> a :-> Full a)

type Expr a = ASTF (NUM :+: Logic :+: If) a

num :: (NUM :<: dom) => Int -> ASTF dom Int
num = inj . Num

(⊕) :: (NUM :<: dom) =>
       ASTF dom Int -> ASTF dom Int -> ASTF dom Int
a ⊕ b = inj Add :$ a :$ b

(⊙) :: (NUM :<: dom) =>
       ASTF dom Int -> ASTF dom Int -> ASTF dom Int
a ⊙ b = inj Mul :$ a :$ b

(≣) :: (Logic :<: dom, Eq a) =>
       ASTF dom a -> ASTF dom a -> ASTF dom Bool
a ≣ b = inj Eq :$ a :$ b

cond :: (If :<: dom) =>
       ASTF dom Bool -> ASTF dom a -> ASTF dom a -> ASTF dom a
cond c t e = inj If :$ c :$ t :$ e

infixl 6 ⊕
infixl 7 ⊙

--- End Listing 3

nnot :: (Logic :<: dom) => ASTF dom Bool -> ASTF dom Bool
nnot a = inj Not :$ a

ex2 :: (NUM :<: dom) => ASTF dom Int
ex2 = (num 5 ⊕ num 0) ⊙ num 6

ex3 :: (NUM :<: dom, Logic :<: dom) => ASTF dom Bool
ex3 = ex2 ≣ ex2

ex2M :: Expr Int
ex2M = ex2
ex3M :: Expr Bool
ex3M = ex3

-- Sec. 3.1
size :: AST dom a -> Int
size (Sym _) = 1
size (a :$ b) = size a + size b

exSize2 = size ex2M
exSize3 = size ex3M

countAdds :: (NUM :<: dom) => AST dom a -> Int
countAdds (a :$ b)    = countAdds a + countAdds b
countAdds s -- `s` was `Sym s` in the paper.
  | Just Add <- prj s = 1
  | otherwise         = 0

-- Sec. 3.2
optAddTop :: (NUM :<: dom) => AST dom a -> AST dom a
optAddTop (add :$ a :$ zero)
  | Just Add <- prj add
  , Just (Num 0) <- prj zero = a
optAddTop a = a

-- My extension: using pattern synonyms together with view patterns.

-- XXX turn these into explicitly bidirectional patterns, after the code merged
-- in https://ghc.haskell.org/trac/ghc/ticket/8581 (when it was first fixed) is
-- released.
pattern ADD <- Sym (prj -> Just Add)
pattern NUM n <- Sym (prj -> Just (Num n))

-- countAdds, implemented using pattern synonyms.
countAdds2 :: (NUM :<: dom) => AST dom a -> Int

countAdds2 (a :$ b) = countAdds a + countAdds b
countAdds2 ADD      = 1
countAdds2 _        = 0

-- optAddTop, renamed and simplified through pattern synonyms.
optAddRule :: (NUM :<: dom) => AST dom a -> AST dom a

optAddRule (ADD :$ a :$ NUM 0) = a
optAddRule a = a

-- Sec. 4.1
type family Denotation sig
type instance Denotation (Full a) = a
type instance Denotation (a :-> sig) = a -> Denotation sig

evalG ∷ (∀ a.     dom a → Denotation a)
      → (∀ a. AST dom a → Denotation a)
evalG f (Sym s)  = f s
evalG f (s :$ a) = evalG f s (evalG f a)

evalSymNUM :: NUM a -> Denotation a
evalSymNUM (Num n) = n
evalSymNUM Add     = (+)
evalSymNUM Mul     = (*)

class Eval expr where
  eval ∷ expr a -> Denotation a

-- Boilerplate for generic functions
instance (Eval sub1, Eval sub2) => Eval (sub1 :+: sub2) where
  eval (InjL v) = eval v
  eval (InjR v) = eval v

instance Eval dom => Eval (AST dom) where
  eval (Sym s) = eval s
  eval (f :$ a) = eval f (eval a)

-- Interesting cases
instance Eval NUM where
  eval (Num n) = n
  eval Add     = (+)
  eval Mul     = (*)

instance Eval Logic where
  eval Eq = (==)
  eval Not = not
instance Eval If where
  eval If = \ c t e -> if c then t else e

-- Sec. 4.2

class Render expr where
  renderArgs :: expr a -> [String] -> String

render :: Render expr => expr a -> String
render a = renderArgs a []

instance (Render sub1, Render sub2) => Render (sub1 :+: sub2) where
  renderArgs (InjL v) = renderArgs v
  renderArgs (InjR v) = renderArgs v

-- Interesting cases
instance Render NUM where
  renderArgs (Num n) [] = show n
  renderArgs Add [a, b] = "(" ++ a ++ " + " ++ b ++ ")"
  renderArgs Mul [a, b] = "(" ++ a ++ " * " ++ b ++ ")"

instance Render Logic where
  renderArgs Eq [a, b] = "(" ++ a ++ " == " ++ b ++ ")"
  renderArgs Not [a] = "(not " ++ a ++ ")"

instance Render If where
  renderArgs If [c, t, e] = unwords ["if", c, "then", t, "else", e]

instance Render dom => Render (AST dom) where
  renderArgs (Sym s)  xs = renderArgs s xs
  renderArgs (f :$ a) xs = renderArgs f (render a : xs)

-- Sec. 4.3
