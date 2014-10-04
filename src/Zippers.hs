{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Zippers where

import Syntactic

-- | A location in an AST, where the hole has signature sigHole, and the whole tree
-- has signature sig. All ASTs involved share the same domain.
data ASTLocation dom sigHole sig = Loc (AST dom sigHole) (ASTZipper dom sigHole sig)
-- Generally speaking, to create a zipper for an inductive data type, we need to
-- similarly duplicate all indexes (since they might vary), creating for each
-- original index two indexes of both zipper type and location type, but we
-- needn't for parameters (since they are shared across subterms), creating for
-- each original parameter one parameter of both zipper type and location type.
-- In this case, since for the type constructor 'AST' 'dom' is a parameter but
-- 'sig' is an index, we get a zipper with one parameter and two indexes.

-- | A Zipper.
data ASTZipper dom sigHole sig where
  -- | The empty zipper. Since the hole is the whole tree, the signature of the
  -- hole and of the tree have to match.
  ZHole :: ASTZipper dom sig sig
  -- | A zipper for a hole on the left. This zipper provides the right sibling
  -- and a parent zipper. The hole signature of the resulting zipper is bigger,
  -- since it needs to accept as parameter the right sibling we provide.
  ZLeft :: ASTZipper dom sig sigTot → AST dom (Full a)
          → ASTZipper dom (a :-> sig) sigTot
  -- | A zipper for a hole on the right. This zipper provides the left sibling
  -- and a parent zipper. The hole signature of the resulting zipper is the
  -- argument type for the given left sibling.
  ZRight :: AST dom (a :-> sig) → ASTZipper dom sig sigTot -> ASTZipper dom (Full a) sigTot

{-
data Exists b where
  Ex :: ∀ a. b a → Exists b
-}

-- We need existentials here... that's so sad...
goLeft :: ASTLocation dom (Full a) sigTot → (∀ sig. ASTLocation dom (a :-> sig) sigTot → b) → b
goLeft (Loc arg (ZRight f parent)) k = k $ Loc f (ZLeft parent arg)

goRight :: ASTLocation dom (a :-> sig) sigTot → ASTLocation dom (Full a) sigTot
goRight (Loc f (ZLeft parent arg)) = Loc arg (ZRight f parent)

goLeftUp :: ASTLocation dom (a :-> sig) sigTot -> ASTLocation dom sig sigTot
goLeftUp (Loc f (ZLeft parent arg))  = Loc (f :$ arg) parent

goRightUp :: ASTLocation dom (Full a) sigTot → (∀ sig. ASTLocation dom sig sigTot → b) → b
goRightUp (Loc arg (ZRight f parent)) k = k $ Loc (f :$ arg) parent

goUp :: ASTLocation dom someSig sigTot → (∀ sig. ASTLocation dom sig sigTot → b) → b
goUp l@(Loc f   (ZLeft parent arg)) k = k $ goLeftUp l
goUp l@(Loc arg (ZRight f parent))  k =     goRightUp l k

-- In fact, we can probably avoid existentials by just storing all indexes in a
-- type-level list (as provided by HList).

mergeLoc :: ASTLocation dom sigHole sig → AST dom sig
mergeLoc (Loc ast zip) = merge ast zip

merge :: AST dom sigHole → ASTZipper dom sigHole sig → AST dom sig
merge ast ZHole = ast
merge ast (ZLeft parent right) = merge (ast :$ right) parent
merge ast (ZRight left parent) = merge (left :$ ast)  parent


ex1M :: Expr Int
ex1M = num 5 ⊕ num 0

-- When writing zippers explicitly, we can highlight the decomposition into the
-- various contexts, as in the examples below.

ex1Z1 =
  Loc (num 0)
        $ ZRight (inj Add :$ num 5)
        $ ZHole
ex1Z2Bis =
  Loc (num 5)
        $ ZRight (inj Add)
        $ ZHole

-- Unfortunately, ZLeft takes the parent zipper as first argument, so we use
-- '(??)' to be able to write the parent zipper afterwards.
ex1Z2 =
  Loc (num 5)
        $ ZRight (inj Add)
        $ ZLeft ?? (num 0)
        $ ZHole

(??) = flip

-- Note that each context (except ZHole) is represented as a function. If we
-- defunctionalize them, we get something isomorphic to ASTZipperF, and one
-- direction of the isomorphism is "essentially" LCons (only "essentially"
-- because we also need to use zipperIso{L,R}).

-- GHCi tests (to turn into proper ones):

-- > renderSafe ex1M == renderSafe (mergeLoc ex1Z1 :: Expr Int)
-- True

-- > renderSafe ex1M == renderSafe (mergeLoc ex1Z2Bis :$ num 0 :: Expr Int)
-- True

-- > renderSafe ex1M == renderSafe (mergeLoc ex1Z2 :: Expr Int)
-- True

exZ =
  Loc (inj Mul :$ num 1)
        $ ZLeft ?? (num 0)
        $ ZRight (inj Add)
        $ ZHole

ex2Z1 =
  Loc (num 0)
        $ ZRight (inj Add :$ num 5)
        $ ZRight (inj Mul)
        $ ZLeft ?? (num 6)
        $ ZHole

-- > renderSafe ex2M == renderSafe (mergeLoc ex2Z1 :: Expr Int)
-- True

ex2Z2 =
  Loc (num 5)
        $ ZRight (inj Add)
        $ ZLeft ?? (num 0)
        $ ZRight (inj Mul)
        $ ZLeft ?? (num 6)
        $ ZHole

-- > renderSafe ex2M == renderSafe (mergeLoc ex2Z2 :: Expr Int)
-- True
