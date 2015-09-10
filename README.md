## AB grammars in Haskell

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
import Control.Applicative ((<|>),empty,liftA2)
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

    Tr S       = t
    Tr N       = e → t
    Tr NP      = e
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
      (:$) :: Expr (a :-> b) -> Expr a -> Expr b

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

We are abstracting over the expressions used, but we're going to need
them to support *at least* function application---as this is what AB
grammars are built around. Therefore, we're going to make a tiny type
class which encodes function application of functions using the
semantic types:

~~~ {.haskell}
class SemE (expr :: SemT -> *) where
    apply :: forall a b. expr (a :-> b) -> expr a -> expr b
~~~

Using this `apply` function, we can define application on `Typed`
expression as well. Since these expressions hide their type, we cannot
enforce on the type-level that this application necessarily
succeeds. What we're doing in the function is the following:

 1. we pattern match to check if either the left or the right type is
    an appropriate function type;
 2. we use the type-level equality function `%~` to check if the
    argument type is the same in both cases;
 3. and if so, we apply `apply`.

In all other cases, we're forced to return `Nothing`. As a side note,
this function corresponds to proof search in the AB grammars, and this
is the function that should be extended if you wish to extend this
grammar to use e.g. Lambek grammars.

~~~ {.haskell}
maybeApply :: SemE expr => Typed expr -> Typed expr -> Maybe (Typed expr)
maybeApply (Typed (a1,x)) (Typed (a2 :%\ b,f)) =
  case a1 %~ a2 of
    Proved Refl -> pure (Typed (b, apply f x))
    _           -> empty
maybeApply (Typed (b :%/ a1,f)) (Typed (a2,x)) =
  case a1 %~ a2 of
    Proved Refl -> pure (Typed (b, apply f x))
    _           -> empty
maybeApply _ _ = empty
~~~

Next, since AB-grammars don't do full parsing but work on parse trees,
we're going to need some sort of trees:

~~~ {.haskell}
data Tree a = Leaf a | Node (Tree a) (Tree a)
            deriving (Show, Functor, Foldable, Traversable)
~~~

However, since we don't actually want to write these horribly verbose
things, we implement a tiny parser which parses sentences of the form
"(the unicorn) (found jack) first":

~~~ {.haskell}
parseTree :: String -> Maybe (Tree String)
parseTree str = case parse sent "" str of
  Left  _ -> empty
  Right t -> pure t
  where
    sent = chainr1 atom node
      where
        word = Leaf <$> many1 letter
        atom = word <|> (char '(' *> (sent <* char ')'))
        node = pure Node <* spaces
~~~

Spaces form nodes in the tree, and
are taken to be right associative, so the example above represents the
following tree:

            -----------
           /           \
          /           ----
         /           /    \
       ----        ----    \
      /    \      /    \    \
    the unicorn found jack first

Last, before we can write out full implementation of parsing with AB
grammars, we're going to need the concept of a lexicon. In our case, a
lexicon will be a function from `String`s to a list of typed
expression---that is, a word can have multiple interpretations:

~~~ {.haskell}
type Lexicon expr = String -> [Typed expr]
~~~

Parsing consists of four stages:

  1. we parse the given string into a tree;
  2. we look up the words in the tree in the lexicon;
  3. we combine the words using `maybeApply` as defined above;
  4. we check if the resulting terms are of the correct type, and
     return those that are.

Note that the `checkType` function once again makes use of the
type-level equality function `%~`.

~~~ {.haskell}
parseWith :: SemE expr => Lexicon expr -> String -> SSynT a -> [expr (Tr a)]
parseWith lex str a1 = do
    wordTree <- maybeToList (parseTree str)
    exprTree <- traverse lex wordTree
    expr     <- combine exprTree
    checkType expr
    where
      -- Check if type a1 == a2, and if so return the
      -- expression. Otherwise return Nothing.
      checkType (Typed (a2,x)) =
        case a1 %~ a2 of
          Proved Refl -> pure x
          _           -> empty

      -- Combine the expressions in the tree using the maybeApply
      -- function, defined above.
      combine (Leaf e)     = pure e
      combine (Node t1 t2) =
        do e1 <- combine t1; e2 <- combine t2; maybeToList (maybeApply e1 e2)
~~~



## Interpretations in Haskell

Now comes the part where all this mucking about with singleton types
really pays off. Because our expressions are typed, and sound with
respect to Haskell's type system, we can choose Haskell to be our
semantic language. That means that we now have the ability to parse
strings to valid Haskell functions.

First, let's set up a small language to represent our world, which in
this case is mostly made up of Bob and Tim:

~~~ {.haskell}
data Entity = Tim -- ^ Tim is a carpenter and an introvert, likes
                  --   holding hands and long walks on the beach.
            | Bob -- ^ Bob is an aspiring actor, and a social media
                  --   junkie. Likes travelling, beer, and Tim.
            deriving (Show)

data Pred = Like Entity Entity -- ^ Is it 'like' or 'like like'?
          | Stupid Entity      -- ^ This is definitely not 'like like'.
          deriving (Show)
~~~

Secondly, we could turn our expressions into plain Haskell
expressions, but that would be dull. Language isn't side-effect
free---there's all kinds of stuff going on! So, we're going to use
a library for extensible effects written by Oleg Kiselyov, Amr Sabry,
Cameron Swords, and Hiromi Ishii. For more information, see
<http://okmij.org/ftp/Haskell/extensible/>. However, if you just want
to compile and run this code, I've included the necessary files in the
repository.

Let's translate our semantic types into effectful Haskell types! And,
most importantly, let's keep the set of effects `r` unspecified!

~~~ {.haskell}
type family ToEff r t :: * where
  ToEff r E         = Eff r Entity
  ToEff r T         = Eff r Pred
  ToEff r (a :-> b) = ToEff r a -> ToEff r b
~~~

Now, because Haskell is being a buzzkill about using un-saturated type
families, we have to wrap our translation in a newtype to be able to
use it with the `Typed` definition and the `SemE` type class. And
because of this, we also have to convince Haskell that these wrapped
Haskell functions can be applied:

~~~ {.haskell}
newtype Ext r a = Ext (ToEff r a)

instance SemE (Ext r) where
  apply (Ext f) (Ext x) = Ext (f x)
~~~

But now we're all ready to go! First, let's determine the effects we
want to use in our library. We could still leave this underspecified,
and only give membership constraints... but that would be much more
verbose.

~~~ {.haskell}
type RW = (Reader Entity ': Writer Pred ': '[])
~~~

Hooray! We can have a lexicon now! And it's reasonably simple, too!

~~~ {.haskell}
lex :: String -> [Typed (Ext RW)]
lex "tim"    = [ Typed (SNP , Ext (pure Tim))                            ]
lex "bob"    = [ Typed (SNP , Ext (pure Bob))                            ]
lex "likes"  = [ Typed (sTV , Ext (liftA2 (flip Like)))                  ]
lex "stupid" = [ Typed (sAP , Ext (>>= \x -> tell (Stupid x) *> pure x)) ]
lex "him"    = [ Typed (SNP , Ext ask)                                   ]
~~~

The first two definitions simply return Tim and Bob as effect-free
constants---hence the application of `pure`. Tim and Bob are both of
type `Entity`, and through our translation, `NP` gets translated to
`Eff r Entity`, so this works out.

Then, the predicate `Like` is simply lifted by `liftA2`, which is
similar to `pure`, but for binary functions. The `flip` is present
because according to the grammar, `Like` will take it's object first
and the subject second... but for readability, we'd like that to be
the other way around.

The definition for "stupid" acts as an identity function on entities,
but inserts a predicate into the 'appositive dimension'. This
corresponds to the linguistic analysis of expressives: they don't
contribute to the sentence meaning, but store their meanings in some
other meaning dimension---in this case, a `Writer` monad!

And last, the definition for "him" simply asks a `Reader` monad what
it's interpretation should be! A more complex example of anaphora
resolution would be to also include a `Writer` monad, and have
entities submit themselves as potential referents, then have this
`Writer` monad periodically empty itself into the `Reader` monad,
e.g. at sentence or clause boundaries, and have anaphora consume the
first appropriate referent. But we digress!

We're still stuck with these unresolved effects, which arise from our
lexicon. So we're going to define a function `runExt`, which handles
all effects in order, and then escapes the `Eff` monad:

~~~ {.haskell}
runExt :: Entity -> Ext RW T -> (Pred, [Pred])
runExt x (Ext e) = run (runWriter (runReader e x))
~~~

And with all this in place, we can handle an example sentence:

~~~ {.haskell}
s1 :: [(Pred, [Pred])]
s1 = runExt Tim <$> parseWith lex "(stupid bob) likes him" SS
~~~

Which evaluates to: `[(Like Bob Tim,[Stupid Bob])]`
