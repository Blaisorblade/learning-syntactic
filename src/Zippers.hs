{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE DataKinds #-}

module Zippers where

import Syntactic


data HList where
  HNil :: HList
  (:::) :: a → HList → HList
infixr 5 :::

-- | A location in an AST, where the hole's signature is the head of sigHoles,
-- and the whole tree has signature sig. All ASTs involved share the same
-- domain.
data ASTLocation dom (sigHoles :: HList) sig where
  Loc :: AST dom sigHole → ASTZipper dom (sigHole ::: sigs) sig → ASTLocation dom (sigHole ::: sigs) sig
-- Generally speaking, to create a zipper for an inductive data type, we need to
-- similarly duplicate all indexes (since they might vary), creating for each
-- original index two indexes of both zipper type and location type, but we
-- needn't for parameters (since they are shared across subterms), creating for
-- each original parameter one parameter of both zipper type and location type.
-- In this case, since for the type constructor 'AST' 'dom' is a parameter but
-- 'sig' is an index, we get a zipper with one parameter and two indexes.
-- Apparently, to avoid existentials we seem to need a list of types, as below.
-- Now, this trick must be standard, but where is it described? I'd guess Conor
-- McBride must be aware of it, since he worked on zippers and he uses Agda.

-- | A Zipper.
data ASTZipper dom (sigHoles :: HList) sig where
  -- | The empty zipper. Since the hole is the whole tree, the signature of the
  -- hole and of the tree have to match.
  ZHole :: ASTZipper dom (sig ::: HNil) sig
  -- | A zipper for a hole on the left. This zipper provides the right sibling
  -- and a parent zipper. The hole signature of the resulting zipper is bigger,
  -- since it needs to accept as parameter the right sibling we provide.
  ZLeft :: ASTZipper dom (sig ::: sigs) sigTot → AST dom (Full a)
          → ASTZipper dom (a :-> sig ::: sig ::: sigs) sigTot
  -- | A zipper for a hole on the right. This zipper provides the left sibling
  -- and a parent zipper. The hole signature of the resulting zipper is the
  -- argument type for the given left sibling.
  ZRight :: AST dom (a :-> sig) → ASTZipper dom (sig ::: sigs) sigTot -> ASTZipper dom (Full a ::: sig ::: sigs) sigTot

-- Instead of having a type representing the complete zipper, we
-- can also have separate individual contexts. The only downside is that we
-- need a specialized list type for that.

data ASTZipperF dom sigTop sigNext sig where
  FZLeft  :: AST dom (Full a) → ASTZipperF dom (a :-> sig) sig sigTot
  FZRight :: AST dom (a :-> sig) → ASTZipperF dom (Full a) sig sigTot

-- The same structure essentially appears in Agda's standard library (it's a
-- reflexive transitive closure IIRC), except for the extra `sig` parameter.
data ASTZipperL dom (sigHoles :: HList) sig where
  LNil :: ASTZipperL dom (sig ::: HNil) sig
  LCons :: ASTZipperF dom sigTop sigNext sig → ASTZipperL dom (sigNext ::: sigs) sig → ASTZipperL dom (sigTop ::: sigNext ::: sigs) sig

data ASTLocationL dom (sigHoles :: HList) sig where
  LLoc :: AST dom sigHole → ASTZipperL dom (sigHole ::: sigs) sig → ASTLocationL dom (sigHole ::: sigs) sig

-- Let's "prove" (as far as possible in Haskell) that these structures are
-- essentially isomorphic.
zipperIsoL :: ASTZipperL dom sigHoles sig → ASTZipper dom sigHoles sig
zipperIsoR :: ASTZipper dom sigHoles sig → ASTZipperL dom sigHoles sig

zipperIsoL LNil = ZHole
zipperIsoL (LCons (FZLeft arg) zips) = ZLeft (zipperIsoL zips) arg
zipperIsoL (LCons (FZRight f) zips) = ZRight f (zipperIsoL zips)

zipperIsoR ZHole = LNil
zipperIsoR (ZLeft rest arg) = LCons (FZLeft arg) (zipperIsoR rest)
zipperIsoR (ZRight f rest) = LCons (FZRight f) (zipperIsoR rest)

locIsoL :: ASTLocationL dom sigHoles sig → ASTLocation dom sigHoles sig
locIsoR :: ASTLocation dom sigHoles sig → ASTLocationL dom sigHoles sig

locIsoL (LLoc ast z) = Loc ast (zipperIsoL z)
locIsoR (Loc ast z) = LLoc ast (zipperIsoR z)

-- Functions for "normal" zippers.
goLeft :: ASTLocation dom (Full a ::: sig ::: sigs) sigTot → ASTLocation dom (a :-> sig ::: sig ::: sigs) sigTot
goLeft (Loc arg (ZRight f parent)) = Loc f (ZLeft parent arg)

goRight :: ASTLocation dom (a :-> sig ::: sig ::: sigs) sigTot → ASTLocation dom (Full a ::: sig ::: sigs) sigTot
goRight (Loc f (ZLeft parent arg)) = Loc arg (ZRight f parent)

goUp :: ASTLocation dom (sig1 ::: sig ::: sigs) sigTot → ASTLocation dom (sig ::: sigs) sigTot
goUp (Loc f   (ZLeft parent arg)) = Loc (f :$ arg) parent
goUp (Loc arg (ZRight f parent))  = Loc (f :$ arg) parent

goFirst :: ASTLocation dom (sig ::: sigs) sigTot → (∀ a. ASTLocation dom (a :-> sig ::: sig ::: sigs) sigTot → b) → b
goFirst (Loc (f :$ s) zip) k = k $ Loc f (ZLeft zip s)

goSecond :: ASTLocation dom sigs sigTot → (∀ a. ASTLocation dom (Full a ::: sigs) sigTot → b) → b
goSecond (Loc (f :$ s) zip) k = k $ Loc s (ZRight f zip)

mergeLoc :: ASTLocation dom sigHoles sig → AST dom sig
mergeLoc (Loc ast zip) = merge ast zip

merge :: AST dom sigHole → ASTZipper dom (sigHole ::: sigs) sig → AST dom sig
merge ast ZHole = ast
merge ast (ZLeft parent right) = merge (ast :$ right) parent
merge ast (ZRight left parent) = merge (left :$ ast)  parent

-- Since ASTZipper and ASTZipperL are computably isomorphic, we wouldn't need to
-- write these functions explicitly (we could simply precompose and postcompose
-- the base functions with the two sides of the isomorphism, that is, apply the
-- category-theoretic (zipperIsoR ← zipperIsoL)). But it's comforting that we
-- can write them directly.

goLeftL :: ASTLocationL dom (Full a ::: sig ::: sigs) sigTot → ASTLocationL dom (a :-> sig ::: sig ::: sigs) sigTot
goLeftL (LLoc arg (LCons (FZRight f) parent)) = LLoc f (LCons (FZLeft arg) parent)

goRightL :: ASTLocationL dom (a :-> sig ::: sig ::: sigs) sigTot → ASTLocationL dom (Full a ::: sig ::: sigs) sigTot
goRightL (LLoc f (LCons (FZLeft arg) parent)) = LLoc arg (LCons (FZRight f) parent)

goUpL :: ASTLocationL dom (sig1 ::: sig ::: sigs) sigTot → ASTLocationL dom (sig ::: sigs) sigTot
goUpL (LLoc f   (LCons (FZLeft  arg) parent)) = LLoc (f :$ arg) parent
goUpL (LLoc arg (LCons (FZRight f)   parent)) = LLoc (f :$ arg) parent

goFirstL :: ASTLocationL dom (sig ::: sigs) sigTot → (∀ a. ASTLocationL dom (a :-> sig ::: sig ::: sigs) sigTot → b) → b
goFirstL (LLoc (f :$ s) zip) k = k $ LLoc f (LCons (FZLeft s) zip)

goSecondL :: ASTLocationL dom sigs sigTot → (∀ a. ASTLocationL dom (Full a ::: sigs) sigTot → b) → b
goSecondL (LLoc (f :$ s) zip) k = k $ LLoc s (LCons (FZRight f) zip)

mergeL :: AST dom sigHole → ASTZipperL dom (sigHole ::: sigs) sig → AST dom sig
mergeL ast LNil = ast
mergeL ast (LCons (FZLeft right) parent) = mergeL (ast :$ right) parent
mergeL ast (LCons (FZRight left) parent) = mergeL (left :$ ast)  parent


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
