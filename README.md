Let's have a little fun with basic AB grammars in Haskell, see how
far we can get. First off, don't let this scare you off... we are
going to need a LOT of language extensions:

~~~ {.haskell}
{-# LANGUAGE TemplateHaskell, QuasiQuotes, FlexibleInstances, FlexibleContexts,
             TypeFamilies, GADTs, TypeOperators, DataKinds, PolyKinds, RankNTypes,
             KindSignatures, UndecidableInstances, StandaloneDeriving,
             RecordWildCards, DeriveFunctor, DeriveFoldable, DeriveTraversable  #-}
module README where
~~~

In addition, we're going to use the following packages:

  - singletons (see <https://hackage.haskell.org/package/singletons>);
  - extensible effects (see <http://okmij.org/ftp/Haskell/extensible/>);
  - parsec (see <https://hackage.haskell.org/package/parsec>).

For the extensible effects library, the code is included in this repository.

~~~ {.haskell}
import Prelude hiding (lookup,lex)
import Control.Applicative ((<|>),empty)
import Data.Maybe (maybeToList)
import Data.Singletons.Decide (Decision(..),(:~:)(..),(%~))
import Data.Singletons.Prelude
import Data.Singletons.TH (singletons)
import Eff1 (Eff,run,Reader,runReader,ask,Writer,tell,runWriter)
import Text.Parsec (char,letter,spaces,many1,chainr1,parse)
~~~

Before we start off, let's review some basic AB-grammar knowledge. In
general, a categorial grammar---of which AB-grammars are an
instance---consist of three things:

 1. a typed language `L₁`;
 2. a typed language `L₂`; and
 3. a translation `Tr` from `L₁` to `L₂`.

In the case of AB-grammars, the language `L₁` is the language of
syntactic types, and consists of:

    Types A, B ::= S | N | NP | A \ B | B / A

It also includes a set of typed words, and two typing rules for
function application:

    A   A \ B   B / A   A
    ---------   ---------
        B           B

The language `L₂` is the simply-typed lambda calculus, typed with only
the primitive types `e` and `t`, for entities and truth-values:

    Types σ, τ ::= e | t | σ → τ

It furthermore consists of a second set of typed constants, which
represent the interpretations of the words, and is usually taken to
include both the universal and the existential quantifier.

The translation function then maps the types for `L₁` to types for
`L₂`, and the words in `L₁` to constants in `L₂`:

    Tr S       = T
    Tr N       = E → T
    Tr NP      = E
    Tr (A \ B) = Tr A → Tr B
    Tr (B / A) = Tr A → Tr B

So, let's start off by creating some Haskell data types to represent
the syntactic and semantic types described above:

~~~ {.haskell}
singletons [d|

    data SynT = S | N | NP | SynT :\ SynT | SynT :/ SynT
              deriving (Show,Eq)

    data SemT = E | T | SemT :-> SemT
              deriving (Show,Eq)

  |]
~~~

The reason we're wrapping these declarations in the `singletons` macro
is---obviously---because later on we will want to use their singletons.
First off, a 'singleton' is a Haskell data type which has the same
structure on the value level and on the type level. For the type
`SynT` above, that means that the `singletons` function generates a
second data type:

    data SSynT (ty :: SynT) where
      SS    :: SSynT S
      SN    :: SSynT N
      SNP   :: SSynT NP
      (:%\) :: SSynT a -> SSynT b -> SSynT (a :\ b)
      (:%/) :: SSynT b -> SSynT a -> SSynT (b :/ a)

By providing a value of such a type, we can constrain the types, and
by pattern matching on it we can pattern match on types. For now, just
be aware that those data types are generated. They will become
relevant soon enough.

First off, though---we probably should've done this right away---let's
just set some fixities for our type-level operators:

~~~ {.haskell}
infixr 5 :\
infixl 5 :/
infixr 5 :->
~~~

And while we're at it, let's create some type-level aliases for common
parts of speech---though I cannot say that this treatment of appositive
modifiers is entirely common:

~~~ {.haskell}
type IV = NP :\ S  -- intransitive verbs
type TV = IV :/ NP -- transitive verbs
type AP = NP :/ NP -- appositive modifier

sIV = SNP :%\ SS
sTV = sIV :%/ SNP
sAP = SNP :%/ SNP
~~~

Now that we have this type structure, our translation function `Tr`
can almost be copied into a Haskell type function:

~~~ {.haskell}
type family Tr (ty :: SynT) :: SemT where
  Tr S        = T
  Tr N        = E :-> T
  Tr NP       = E
  Tr (a :\ b) = Tr a :-> Tr b
  Tr (b :/ a) = Tr a :-> Tr b
~~~

Let's assume for now that we have some sort of data type that we wish
to use to represent our semantic terms, for instance:

    data Expr (ty :: SemT) where
      John :: Expr E
      Mary :: Expr E
      Like :: Expr (E :-> E :-> T)

While we have a way of talking about terms of a certain type---e.g. by
saying `Expr E` we can talk about all entities---we cannot really
leave the type open and talk about all well-typed terms. For this we
need to introduce a new data type:

~~~ {.haskell}
data Typed (expr :: SemT -> *) = forall a. Typed (SSynT a, expr (Tr a))
~~~

The `Typed` data-type contains a tuple of a singleton for a semantic
type, and an expression. Notice that the type-level variable `a` is
shared between the singleton and the expression, which means that the
expression in the second position is forced to be of the type given in
the first.

~~~ {.haskell}
data Tree a = Leaf a | Node (Tree a) (Tree a)
            deriving (Show, Functor, Foldable, Traversable)
~~~


~~~ {.haskell}
data Lexicon (expr :: SemT -> *) = Lexicon
  { lookup :: String -> [Typed expr]
  , apply  :: forall a b. expr (a :-> b) -> expr a -> expr b
  }
~~~


~~~ {.haskell}
maybeApply :: Lexicon expr -> Typed expr -> Typed expr -> Maybe (Typed expr)
maybeApply Lexicon{..} ty1 ty2 =
  case (ty1, ty2) of

    (Typed (a1,x), Typed (a2 :%\ b,f)) ->
      case a1 %~ a2 of
        Proved Refl -> pure (Typed (b, apply f x))
        _           -> empty

    (Typed (b :%/ a1,f), Typed (a2,x)) ->
      case a1 %~ a2 of
        Proved Refl -> pure (Typed (b, apply f x))
        _           -> empty

    _ -> empty
~~~


~~~ {.haskell}
parseAs :: Lexicon expr -> String -> SSynT a -> [expr (Tr a)]
parseAs lex str a1 =
  case parse sent "" str of
    Left  _ -> empty
    Right t -> exec =<< (comp =<< traverse (lookup lex) t)
    where
      -- unpack expression only if it has the right type
      exec (Typed (a2,x)) =
        case a1 %~ a2 of
          Proved Refl -> pure x
          _           -> empty

      -- fold tree using function application
      comp (Leaf e)     = pure e
      comp (Node t1 t2) =
        do e1 <- comp t1; e2 <- comp t2; maybeToList (maybeApply lex e1 e2)

      -- simple grammar for phrases as "(the unicorn) found jack first"
      sent = chainr1 atom node
        where
          word = Leaf <$> many1 letter
          atom = word <|> (char '(' *> (sent <* char ')'))
          node = pure Node <* spaces
~~~

~~~ {.haskell}
data Entity = Tim | Bob
            deriving (Show)

data Pred = Like Entity Entity | Stupid Entity
          deriving (Show)
~~~

~~~ {.haskell}
type family ToEff r t :: * where
  ToEff r E        = Eff r Entity
  ToEff r T        = Eff r Pred
  ToEff r (a :-> b) = ToEff r a -> ToEff r b
~~~

~~~ {.haskell}
newtype Ext r a = Ext (ToEff r a)
~~~

~~~ {.haskell}
type RW = (Reader Entity ': Writer Pred ': '[])
~~~

~~~ {.haskell}
lex :: String -> [Typed (Ext RW)]
lex "tim"    = pure (Typed (SNP , Ext (pure Tim)))
lex "bob"    = pure (Typed (SNP , Ext (pure Bob)))
lex "likes"  = pure (Typed (sTV , Ext (\y x -> Like <$> x <*> y)))
lex "stupid" = pure (Typed (sAP , Ext (\x -> x >>= \x' -> tell (Stupid x') *> pure x')))
lex "him"    = pure (Typed (SNP , Ext ask))
~~~

~~~ {.haskell}
app :: (ToEff r t ~ (ToEff r a -> ToEff r b)) => Ext r t -> Ext r a -> Ext r b
app (Ext f) (Ext x) = Ext (f x)
~~~

~~~ {.haskell}
ext :: Lexicon (Ext RW)
ext = Lexicon { lookup = lex, apply = app }
~~~

~~~ {.haskell}
runExt :: Ext RW T -> Entity -> (Pred, [Pred])
runExt (Ext e) x = run (runWriter (runReader e x))
~~~

~~~ {.haskell}
s1 :: [(Pred, [Pred])]
s1 = runExt <$> parseAs ext "(stupid bob) likes him" SS <*> pure Tim
~~~

`[(Like Bob Tim,[Stupid Bob])]`
