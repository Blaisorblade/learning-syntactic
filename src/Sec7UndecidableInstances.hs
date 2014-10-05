{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Segregate code requiring UndecidableInstances.
module Sec7UndecidableInstances where

import Syntactic

-- Example from the paper
class OptAdd sym dom where
  optAddSym ∷ sym a → Args (AST dom) a → AST dom (Full (Result a))

optAdd ∷ OptAdd dom dom ⇒ ASTF dom a → AST dom (Full a)
optAdd = query optAddSym

instance (OptAdd sub1 dom, OptAdd sub2 dom) ⇒ OptAdd (sub1 :+: sub2) dom where
  optAddSym (InjL s) = optAddSym s
  optAddSym (InjR s) = optAddSym s

optAddDefault ∷ (OptAdd dom dom, sym :<: dom) ⇒
  sym a → Args (AST dom) a → AST dom (Full (Result a))
optAddDefault s = appArgs (Sym (inj s)) . mapArgs optAdd

instance (NUM :<: dom, OptAdd dom dom) ⇒ OptAdd NUM dom where
  optAddSym Add (a :* NUM 0 :* Nil) = optAdd a
  optAddSym s as = optAddDefault s as

instance (Logic :<: dom, OptAdd dom dom) ⇒ OptAdd Logic dom where
  optAddSym = optAddDefault

instance (If :<: dom, OptAdd dom dom) ⇒ OptAdd If dom where
  optAddSym If (c :* t :* e :* Nil) =
    appArgs (Sym (inj If)) (optAdd c :* t :* e :* Nil)
