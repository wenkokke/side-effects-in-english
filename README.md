Let's have a little fun with basic AB grammars in Haskell, see how
far we can get. First off, don't let this scare you off... we are
going to need a LOT of language extensions:

``` haskell
{-# LANGUAGE TemplateHaskell, QuasiQuotes, FlexibleInstances, FlexibleContexts,
             TypeFamilies, GADTs, TypeOperators, DataKinds, PolyKinds, RankNTypes,
             KindSignatures, UndecidableInstances, StandaloneDeriving,
             RecordWildCards, DeriveFunctor, DeriveFoldable, DeriveTraversable  #-}
module README where
```

In addition, we're going to import some dependencies. We're going to
make some use of the 'singletons' package (see
<https://hackage.haskell.org/package/singletons>). The extensible
effects module was taken from <http://okmij.org/ftp/Haskell/extensible/>.
Lastly, for a very simple parser we're going to use 'parsec' (see
<https://hackage.haskell.org/package/parsec>).

``` haskell
import           Control.Applicative ((<|>),empty)
import           Data.Maybe (maybeToList)
import           Data.Singletons.Decide (Decision(..),(:~:)(..),(%~))
import           Data.Singletons.Prelude
import           Data.Singletons.TH (singletons)
import           Eff1 (Eff,Reader,Writer,ask,tell,run,runReader,runWriter)
import           Text.Parsec (char,letter,spaces,many1,chainr1)
import qualified Text.Parsec (parse)
```
