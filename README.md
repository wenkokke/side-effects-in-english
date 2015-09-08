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
import Control.Applicative ((<|>),empty)
import Data.Maybe (maybeToList)
import Data.Singletons.Decide (Decision(..),(:~:)(..),(%~))
import Data.Singletons.Prelude
import Data.Singletons.TH (singletons)
import Eff1 (Eff,run,Reader,runReader,ask,Writer,tell,runWriter)
import Text.Parsec (char,letter,spaces,many1,chainr1)
import qualified Text.Parsec (parse)
~~~


~~~ {.haskell}
singletons [d|

    data SynT = S | N | NP | SynT :\ SynT | SynT :/ SynT
              deriving (Show,Eq)

    data SemT = E | T | SemT :-> SemT
              deriving (Show,Eq)

  |]
~~~
