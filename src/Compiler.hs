{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Compiler where
import Syntactic

import Control.Monad.Writer
import Control.Monad.State

--Sec 4.3

--- (Derived from) Listing 4, with extra newtypes
newtype VarId = V {unV ∷ Integer}
newtype ResultLoc = R {unR ∷ VarId}
newtype Program = P { unP ∷ [String] }
  deriving Monoid
type CodeMonad = WriterT Program (State VarId)
type CodeGen = ResultLoc → CodeMonad ()


freshVar ∷ CodeMonad VarId
freshVar = do v <- get; put $ V (unV v + 1); return v

var ∷ VarId → String
var = ("v" ++) . show . unV

(=:=) ∷ VarId → String → String
loc =:= expr = unwords [var loc, "=", expr]

indent = P . map ("  " ++) . unP
--- (Derived from) Listing 5

-- Core
class Render expr ⇒ Compile expr where
  compileArgs ∷ expr a → [CodeGen] → CodeGen
  compileArgs expr args loc = do
    argVars <- replicateM (length args) freshVar
    zipWithM ($) args (map R argVars)
    tell $ P [unR loc =:= renderArgs expr (map var argVars)]

-- called compile in Listing 5
compileTop expr =
  unlines $
  unP $
  flip evalState (V 1) $
  execWriterT $
  compile expr (R $ V 0)

-- With this, the instance for AST is unnecessary.
compileTop2 a =
  unlines $
  unP $
  flip evalState (V 1) $
  execWriterT $
  fold compileArgs a (R $ V 0)

-- Boilerplate
-- This is analogous to render.
compile ∷ Compile expr ⇒ expr a → CodeGen
compile s = compileArgs s []

instance (Compile sub1, Compile sub2) ⇒ Compile (sub1 :+: sub2) where
  compileArgs (InjL expr) = compileArgs expr
  compileArgs (InjR expr) = compileArgs expr

instance Compile dom ⇒ Compile (AST dom) where
  compileArgs (Sym s) xs = compileArgs s xs
  compileArgs (f :$ s) xs = compileArgs f (compile s : xs)

-- Listing 6
-- compilation for various cases
instance Compile NUM
instance Compile Logic
instance Compile If where
  compileArgs If [cGen, tGen, eGen] loc = do
    cVar <- freshVar
    cGen $ R cVar
    tRes <- lift $ execWriterT $ tGen loc
    eRes <- lift $ execWriterT $ eGen loc
    tell $ P [unwords ["if", var cVar, "then"]]
           <> indent tRes
           <> P [ "else" ]
           <> indent eRes
