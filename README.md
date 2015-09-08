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


~~~ {.haskell}
singletons [d|

    data SynT = S | N | NP | SynT :\ SynT | SynT :/ SynT
              deriving (Show,Eq)

    data SemT = E | T | SemT :-> SemT
              deriving (Show,Eq)

  |]
~~~


~~~ {.haskell}
infixr 5 :\
infixl 5 :/
infixr 5 :->

type IV = NP :\ S  -- intransitive verbs
type TV = IV :/ NP -- transitive verbs
type AP = NP :/ NP -- appositive modifier

sIV :: SSynT IV
sIV = SNP :%\ SS
sTV :: SSynT TV
sTV = sIV :%/ SNP
sAP :: SSynT (NP :/ NP)
sAP = SNP :%/ SNP
~~~


~~~ {.haskell}
type family Tr (ty :: SynT) :: SemT where
  Tr S        = T
  Tr N        = E :-> T
  Tr NP       = E
  Tr (a :\ b) = Tr a :-> Tr b
  Tr (b :/ a) = Tr a :-> Tr b
~~~

~~~ {.haskell}
data Typed (expr :: SemT -> *) = forall a. Typed (SSynT a, expr (Tr a))
~~~

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

    -- unpack `Typed' if its type is correct
    exec (Typed (a2,x)) =
      case a1 %~ a2 of
        Proved Refl -> pure x
        _           -> empty

    -- compose the function at the node using `maybeApply'
    comp (Leaf e)     = pure e
    comp (Node t1 t2) =
      do e1 <- comp t1; e2 <- comp t2; maybeToList (maybeApply lex e1 e2)

    -- simple Parsec grammar for trees such as "(the unicorn) found jack first"
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
