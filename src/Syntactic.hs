{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Syntactic where

import Data.Monoid (mconcat)
-- Following Emil Axelsson, "A Generic Abstract Syntax Model for Embedded
-- Languages", ICFP 2012, http://doi.acm.org/10.1145/2364527.2364573.

-- Sec. 2.2

newtype Full a  = Full { result ∷ a }
newtype a :→ b = Partial (a → b)
infixr :→

-- | dom is the type of allowed symbols (see the direct use in the Sym
-- constructor), so it describes the primitives available in an AST.

data AST dom sig where
  Sym  ∷ dom sig → AST dom sig
  (:$) ∷ AST dom (a :→ sig) → AST dom (Full a) → AST dom sig

type ASTF dom res = AST dom (Full res)

infixl 1 :$

-- A valid dom. (Nominal subtyping would help here).
data NUM a where
  -- Num ∷ Int → NUM Int -- NO! Fails at zeroPOne
  Num ∷ Int → NUM (Full Int)
  Add ∷ NUM (Int :→ Int :→ Full Int)
  Mul ∷ NUM (Int :→ Int :→ Full Int)

type Expr3 a = ASTF NUM a

num3 ∷ Int → Expr3 Int
num3 = Sym . Num

add3 ∷ Expr3 Int → Expr3 Int → Expr3 Int
add3 a b = Sym Add :$ a :$ b

-- Examples
zero3, zeroPOne3, zeroPZeroPOne3 ∷ Expr3 Int

zero3 = num3 0
zeroPOne3 = add3 zero3 $ num3 1
zeroPZeroPOne3 = add3 zero3 zeroPOne3

-- Sec. 2.3
evalNUM ∷ Expr3 a → a
evalNUM (Sym (Num n)) = n
evalNUM (Sym Add :$ a :$ b) = evalNUM a + evalNUM b
evalNUM (Sym Mul :$ a :$ b) = evalNUM a * evalNUM b

renderNUM ∷ Expr3 a → String
renderNUM (Sym (Num n)) = show n
renderNUM (Sym Add :$ a :$ b) = "(" ++ renderNUM a ++ " + " ++ renderNUM b ++ ")"
renderNUM (Sym Mul :$ a :$ b) = "(" ++ renderNUM a ++ " * " ++ renderNUM b ++ ")"

-- Sec. 3

--- Listing 1.

data (dom1 :+: dom2) a where
  InjL ∷ dom1 a → (dom1 :+: dom2) a
  InjR ∷ dom2 a → (dom1 :+: dom2) a

infixr :+: -- We need this line because left-nested uses don't fully work --
           -- commenting this out makes exSize3 fail.

--- Listing 2, altered according to syntactic 2.0.
data Empty

-- | sup is a sum which can also contains sub.
class Project sub sup where
  prj ∷ sup a → Maybe (sub a)

instance Project sub sup where
  prj _ = Nothing

instance Project sub sub where
  prj = Just

instance Project sym1 (sym1 :+: sym3) where
  prj (InjL c) = Just c
  prj (InjR _) = Nothing

instance Project sym1 sym3 ⇒ Project sym1 (sym2 :+: sym3) where
  prj (InjL _) = Nothing
  prj (InjR c) = prj c

instance Project sub sup ⇒ Project sub (AST sup) where
  prj (Sym a) = prj a
  prj (a :$ b) = Nothing

-- | sup is a sum which must contains sub.

class Project sub sup ⇒ (sub :<: sup) where
  inj ∷ sub a → sup a

instance (sub :<: sub) where
  inj = id

instance sym1 :<: (sym1 :+: sym3) where
  inj = InjL

instance (sym1 :<: sym3) ⇒ sym1 :<: (sym2 :+: sym3) where
  inj = InjR . inj

instance (sub :<: sup) ⇒ sub :<: AST sup where
  inj = Sym . inj

--- End Listing 2

--- Listing 3
data Logic a where
  Not ∷ Logic (Bool :→ Full Bool)
  Eq  ∷ Eq a ⇒ Logic (a :→ a :→ Full Bool)

data If a where
  If ∷ If (Bool :→ a :→ a :→ Full a)

type Expr a = ASTF (NUM :+: Logic :+: If) a

num ∷ (NUM :<: dom) ⇒ Int → ASTF dom Int
num = inj . Num

(⊕) ∷ (NUM :<: dom) ⇒
       ASTF dom Int → ASTF dom Int → ASTF dom Int
a ⊕ b = inj Add :$ a :$ b

(⊙) ∷ (NUM :<: dom) ⇒
       ASTF dom Int → ASTF dom Int → ASTF dom Int
a ⊙ b = inj Mul :$ a :$ b

(≣) ∷ (Logic :<: dom, Eq a) ⇒
       ASTF dom a → ASTF dom a → ASTF dom Bool
a ≣ b = inj Eq :$ a :$ b

cond ∷ (If :<: dom) ⇒
       ASTF dom Bool → ASTF dom a → ASTF dom a → ASTF dom a
cond c t e = inj If :$ c :$ t :$ e

infixl 6 ⊕
infixl 7 ⊙

--- End Listing 3

nnot ∷ (Logic :<: dom) ⇒ ASTF dom Bool → ASTF dom Bool
nnot a = inj Not :$ a

ex2 ∷ (NUM :<: dom) ⇒ ASTF dom Int
ex2 = (num 5 ⊕ num 0) ⊙ num 6

ex3 ∷ (NUM :<: dom, Logic :<: dom) ⇒ ASTF dom Bool
ex3 = ex2 ≣ ex2

-- From Sec. 4.3
ex4 ∷ (NUM :<: dom, Logic :<: dom, If :<: dom) ⇒ ASTF dom Int
ex4 = cond (num 1 ≣ num 2) (num 3) ex2

ex2M ∷ Expr Int
ex2M = ex2
ex3M ∷ Expr Bool
ex3M = ex3
ex4M ∷ Expr Int
ex4M = ex4

-- Sec. 3.1
size ∷ AST dom a → Int
size (Sym _) = 1
size (a :$ b) = size a + size b

exSize2 = size ex2M
exSize3 = size ex3M

countAdds ∷ (NUM :<: dom) ⇒ AST dom a → Int
countAdds (a :$ b)    = countAdds a + countAdds b
countAdds s -- `s` was `Sym s` in the paper.
  | Just Add <- prj s = 1
  | otherwise         = 0

-- Sec. 3.2
optAddTop ∷ (NUM :<: dom) ⇒ AST dom a → AST dom a
optAddTop (add :$ a :$ zero)
  | Just Add <- prj add
  , Just (Num 0) <- prj zero = a
optAddTop a = a

-- My extension: using pattern synonyms together with view patterns.

-- XXX turn these into explicitly bidirectional patterns, after the code merged
-- in https://ghc.haskell.org/trac/ghc/ticket/8581 (when it was first fixed) is
-- released.
pattern ADD <- Sym (prj → Just Add)
pattern NUM n <- Sym (prj → Just (Num n))

-- countAdds, implemented using pattern synonyms.
countAdds2 ∷ (NUM :<: dom) ⇒ AST dom a → Int

countAdds2 (a :$ b) = countAdds a + countAdds b
countAdds2 ADD      = 1
countAdds2 _        = 0

-- optAddTop, renamed and simplified through pattern synonyms.
optAddRule ∷ (NUM :<: dom) ⇒ AST dom a → AST dom a

optAddRule (ADD :$ a :$ NUM 0) = a
optAddRule a = a

-- Sec. 4.1
type family Denotation sig
type instance Denotation (Full a) = a
type instance Denotation (a :→ sig) = a → Denotation sig

evalG ∷ (∀ a.     dom a → Denotation a)
      → (∀ a. AST dom a → Denotation a)
evalG f (Sym s)  = f s
evalG f (s :$ a) = evalG f s (evalG f a)

evalSymNUM ∷ NUM a → Denotation a
evalSymNUM (Num n) = n
evalSymNUM Add     = (+)
evalSymNUM Mul     = (*)

class Eval expr where
  eval ∷ expr a → Denotation a

-- Boilerplate for generic functions
instance (Eval sub1, Eval sub2) ⇒ Eval (sub1 :+: sub2) where
  eval (InjL v) = eval v
  eval (InjR v) = eval v

instance Eval dom ⇒ Eval (AST dom) where
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
  eval If = \ c t e → if c then t else e

-- Sec. 4.2

class Render expr where
  renderArgs ∷ expr a → [String] → String

-- Boilerplate
render ∷ Render expr ⇒ expr a → String
render a = renderArgs a []

instance (Render sub1, Render sub2) ⇒ Render (sub1 :+: sub2) where
  renderArgs (InjL v) = renderArgs v
  renderArgs (InjR v) = renderArgs v

instance Render dom ⇒ Render (AST dom) where
  renderArgs (Sym s)  xs = renderArgs s xs
  renderArgs (f :$ a) xs = renderArgs f (render a : xs)

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

-- Sec. 5

fold ∷ ∀ dom res. (∀ a. dom a → [res] → res)
                → (∀ a. AST dom a →     res)
fold f a = go a []
  where
    go ∷ AST dom a → [res] → res
    go (Sym s)  as = f s as
    go (s :$ a) as = go s (fold f a : as)

-- With this, the instance for AST is unnecessary.
render2 = fold renderArgs

-- Term equality
class Equality expr where
  -- equal ∷ expr a → expr a → Bool
  --
  -- The type above is too strict, so it cannot be used for application nodes,
  -- since corresponding subterms are not guaranteed to have the same type.
  equal ∷ expr a → expr b → Bool

-- Boilerplate-ish instances.
instance (Equality sub1, Equality sub2) ⇒ Equality (sub1 :+: sub2) where
  equal (InjL v1) (InjL v2) = equal v1 v2
  equal (InjR v1) (InjR v2) = equal v1 v2
  equal _         _         = False

instance Equality dom ⇒ Equality (AST dom) where
  equal (Sym s1)   (Sym s2)   = equal s1 s2
  equal (f1 :$ s1) (f2 :$ s2) = equal f1 f2 && equal s1 s2
  equal _          _          = False

-- Language-specific instances
instance Equality NUM where
  equal (Num n1) (Num n2) = n1 == n2
  equal Add      Add      = True
  equal Mul      Mul      = True
  equal _        _        = False

instance Equality Logic where
  equal Not      Not      = True
  equal Eq       Eq       = True
  equal _        _        = False

instance Equality If where
  equal If       If = True

-- Sec. 6: Regaining type-safety

{-

type family Result sig
type instance Result (Full a) = a
type instance Result (a :→ b) = Result b

-- The version I came up with. In this version, there are less
-- `Full` wrappers around stuff (compare argEx here and below).
-- However, Sec. 6.1 explains why that is not done, and this would be a problem
-- in Sec. 7

data Args c sig where
  Nil ∷ Args c (Full a)
  (:*) ∷ c (Result (Full a)) → Args c sig → Args c (a :→ sig)

infixr :*

argEx ∷ Args Maybe (Int :→ Bool :→ Full Char)
argEx = Just 1 :* Just False :* Nil

typedFold ∷ ∀ dom c.
     (∀ sig. dom sig → Args c sig → c (Result sig)) →
     (∀ a. ASTF dom a → c a)
typedFold f t = go t Nil
  where
    go ∷ ∀ sig.
         AST dom sig → Args c sig → c (Result sig)
    go (Sym s)  as = f s as
    -- Both do the same:
    --go (s :$ a) as = go s (go a Nil :* as)
    go (s :$ a) as = go s (typedFold f a :* as)
-}


-- The version in the paper

-- Sec 6.1: Typed argument lists
type family Result sig

-- Note that Result removes the Full type constructor...
type instance Result (Full a) = a
type instance Result (a :→ b) = Result b
-- But we often do use Full (Result sig)!

data Args c sig where
  Nil ∷ Args c (Full a)
  (:*) ∷ c (Full a) → Args c sig → Args c (a :→ sig)

infixr :*

argEx ∷ Args Maybe (Int :→ Bool :→ Full Char)
argEx = Just (Full 1) :* Just (Full False) :* Nil

-- Sec 6.2: Type-safe fold

typedFold ∷ ∀ dom c.
     (∀ sig. dom sig → Args c sig → c (Full (Result sig))) →
     (∀ a. ASTF dom a              → c (Full a))
typedFold f t = go t Nil
  where
    go ∷ ∀ sig.
         AST dom sig → Args c sig → c (Full (Result sig))
    go (Sym s)  as = f s as
    -- Both do the same:
    --go (s :$ a) as = go s (go a Nil :* as)
    go (s :$ a) as = go s (typedFold f a :* as)

everywhere ∷ (∀ a. ASTF dom a → ASTF dom a) →
             (∀ a. ASTF dom a → ASTF dom a)
everywhere f = typedFold (appArgs2 f)

appArgs2 ∷ (∀ a. ASTF dom a → ASTF dom a) → dom sig → Args (AST dom) sig → AST dom (Full (Result sig))
appArgs2 f = \s → f . appArgs (Sym s)

appArgs ∷ AST dom sig → Args (AST dom) sig → AST dom (Full (Result sig))
appArgs s Nil = s
appArgs s (a :* as) = appArgs (s :$ a) as

newtype Const a b = Const { unConst ∷ a }

typedFoldSimple ∷ ∀ dom c.
   (∀ sig. dom sig → Args (Const c) sig → c) →
   (∀ a.  ASTF dom a                     → c)
typedFoldSimple f = unConst . typedFold ((Const .) . f)

class RenderSafe sym where
  renderArgsSafe ∷ sym a → Args (Const String) a → String

renderSafe = typedFoldSimple renderArgsSafe

binOp op a b = mconcat ["(", a, " ", op, " ", b, ")"]

-- We still need the instance for :+:
instance (RenderSafe sub1, RenderSafe sub2) ⇒ RenderSafe (sub1 :+: sub2) where
  renderArgsSafe (InjL v) = renderArgsSafe v
  renderArgsSafe (InjR v) = renderArgsSafe v

instance RenderSafe NUM where
  renderArgsSafe (Num n) Nil = show n
  renderArgsSafe Add (Const a :* Const b :* Nil) = binOp "+" a b
  renderArgsSafe Mul (Const a :* Const b :* Nil) = binOp "*" a b

instance RenderSafe Logic where
  renderArgsSafe Not (Const b :* Nil) = mconcat ["(not ", b, ")"]
  renderArgsSafe Eq (Const a :* Const b :* Nil) = binOp "==" a b

instance RenderSafe If where
  renderArgsSafe If (Const c :* Const t :* Const e :* Nil) = unwords ["if", c, "then", t, "else", e]

-- Sec. 7: Controlling the recursion

-- We get the following by taking typedFold, removing the recursive call, and
-- adapting the arguments of Args in the type signature. The version in the
-- paper has a different type signature, and the paper claims this extra
-- generality makes it more applicable. I currently doubt it, so let's see where
-- this version fails.

query ∷ ∀ dom c.
     (∀ sig. dom sig → Args (AST dom) sig → c (Full (Result sig))) →
     (∀ a. ASTF dom a              → c (Full a))
query f t = go t Nil
  where
    go ∷ ∀ sig.
         AST dom sig → Args (AST dom) sig → c (Full (Result sig))
    go (Sym s)  as = f s as
    go (s :$ a) as = go s (a :* as)

-- Left out from the paper: defining typedFold in terms of query. Since query is
-- a one-level fold, to get a multi-level fold we follow the standard pattern.
-- That is, query's argument will first recurse onto all arguments, and then
-- apply the function to the symbol and the transformed arguments. The only
-- difference is that we have an extra child (representing the node
-- constructor), but we still do not need to recurse on it (we recurse on the
-- whole node).

-- We do the obvious thing: we construct an argument to query and do the recursive calls on the arguments

mapArgs ∷ (∀ a. f (Full a) → g (Full a)) → Args f sig → Args g sig
mapArgs f Nil = Nil
mapArgs f (a :* as) = f a :* mapArgs f as

typedFold2 ∷ ∀ dom c.
     (∀ sig. dom sig → Args c sig → c (Full (Result sig))) →
     (∀ a. ASTF dom a              → c (Full a))
typedFold2 f = query $ \sym → f sym . mapArgs (typedFold2 f)

-- For the examples from the paper, see Sec7UndecidableInstances.hs

-- Sec. 8: Mutually recursive types

data E a -- Expressions
data S   -- Statements

type Var = String

type ExprEnc a = ASTF (ExprDom :+: StmtDom) (E a)
type StmtEnc   = ASTF (ExprDom :+: StmtDom) S

data ExprDom a where
  NumSym  ∷ Int → ExprDom (Full (E Int))
  AddSym  ∷        ExprDom (E Int :→ E Int :→ Full (E Int))
  ExecSym ∷ Var → ExprDom (S :→ Full (E a))
data StmtDom a where
  AssignSym ∷ Var → StmtDom (E a :→ Full S)
  SeqSym    ∷        StmtDom (S :→ S :→ Full S)
