---
title      : "Side-effects in English"
date       : 2016-03-09 12:00:00
categories : [compsci, compling]
tags       : [haskell, catgram]
---

Back when I wrote this, I had just discovered
["Extensible Effects: an alternative to Monad Transformers"][eff]{:#eff}
by Oleg Kiselyov, Amr Sabry, Cameron Swords, and Hiromi Ishii, and
I've always had a penchant for mucking about with linguistics and
Haskell... so... let's have a little fun with this library and some
basic AB grammars in Haskell, see how far we can get within the
universally well-defined maximum length of a blog post!

Before we start, let's get a clear idea of what we're going to try and
accomplish. It's more or less a well known fact that natural language
has tons of side-effects---sometimes also referred to as
"non-compositional phenomena". Let's look at some examples:

  1. "I cooked up a delicious dinner!"
  2. "There! I walked the damn dog!"
  3. "As Mary left, she whistled a cheery tune."

In (1), the word "I" is non-compositional: it's a word which you can
always use, but which changes its meaning depending on the
context---on who uses it.
In (2) we have the word "damn", an expressive. There's pretty
extensive literature on expressives---see, for instance, Daniel
Gutzmann's ["Use-conditional meaning"][ucm]---but
the gist of it is as follows: "damn" doesn't affect the
*truth* of a sentence. If I come back from walking the dog, even
though I do not like dogs, and say "There! I walked the damn dog!",
you can't reply by saying "No, you didn't! The dog is nice!" Instead,
"damn" conveys it's meaning on some sort of side-channel.
Finally, in (3) we have "she", which again has a context-dependent
meaning. However, in this situation, "she" doesn't get its meaning
from the context in which the sentence is uttered. Instead, reading
this sentence in isolation, it seems pretty likely that "she" refers
to Mary.

"Non-compositional phenomena" is a bit of a misnomer for the phenomena
in (1-3). We can implement these phenomena as *side-effects*, and as
we know from functional programming, side-effects are often perfectly
compositional. In fact, the above phenomena correspond, in
Haskell-lingo, to a *Reader*, a *Writer* and a *State*
monad.[^esslli2015-monads] However, rolling together various different
monads can be a tedious chore. In addition, when we're writing what
a word means, we might not *want* to specify its meaning for *all
possible side-effects*. Since linguistics is continually changing, we
might not even want to commit to what all possible side-effects *are*.

So this is why I got excited when I saw the latest library for
extensible effects. If you don't know what extensible effects are, I'd
recommend [the paper linked above](#eff). But anyway, what I'm going
to do in this post is: develop a parser, which parses Haskell strings,
looks up the words in a dictionary of *effectful* Haskell functions,
and composes these to get some meaning for the sentence. Here's an
example that you'll see again at the end of the post, except then
it'll actually work!

~~~
lex :: String -> [SomeEffectfulFunction]
lex "tim"    = [ NP , Tim             ]
lex "bob"    = [ NP , Bob             ]
lex "likes"  = [ TV , Like            ]
lex "stupid" = [ AP , < id , Stupid > ]
-- ^ Has an identity (i.e. no) meaning, but
--   but conveys `Stupid` as a side-effect.
lex "him"    = [ NP , magic           ]
-- ^ Has some magic way of obtaining the
--   thing that's referenced.

example :: [(Pred, [Pred])]
example = parseWith Tim "(stupid bob) likes him"
     -- > [(Like Bob Tim,[Stupid Bob])]
~~~
{:.language-haskell}


## AB Grammars in Haskell

Well, first off, don't let this scare you off... but we are going to
do this in Haskell, and we're going to need a LOT of language
extensions. This is because we're basically going to parse strings to
Haskell functions:

``` haskell
{-# LANGUAGE
    TemplateHaskell, QuasiQuotes, FlexibleInstances, FlexibleContexts,
    TypeFamilies, GADTs, TypeOperators, DataKinds, PolyKinds, RankNTypes,
    KindSignatures, UndecidableInstances, StandaloneDeriving,
    RecordWildCards, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
```

<div style="display:none;">
``` haskell
import Prelude hiding (lookup,lex)
import Control.Applicative ((<|>),empty,liftA2)
import Data.Maybe (maybeToList)
import Data.Singletons.Decide (Decision(..),(:~:)(..),(%~))
import Data.Singletons.Prelude
import Data.Singletons.TH (singletons)
import Eff1 (Eff,run,Reader,runReader,ask,Writer,tell,runWriter)
import Text.Parsec (char,letter,spaces,many1,chainr1,parse)
```
</div>

In addition, we're going to use the following packages:
[singletons](https://hackage.haskell.org/package/singletons);
[extensible effects](http://okmij.org/ftp/Haskell/extensible/);
[parsec](https://hackage.haskell.org/package/parsec);
[markdown-unlit](https://hackage.haskell.org/package/markdown-unlit).
For the extensible effects library, I've included a copy of all the
required code in [the repository](https://github.com/pepijnkokke/side-effects-in-english/).

Before we start off, let's review some basic AB-grammar knowledge. In
general, a categorial grammar---of which AB-grammars are an
instance---consist of three things:

  1. a typed language $$\mathcal{L}_1$$;
  2. a typed language $$\mathcal{L}_2$$; and
  3. a translation $$Tr$$ from $$\mathcal{L}_1$$ to $$\mathcal{L}_2$$.

The language $$\mathcal{L}_1$$ describes the *grammar* of our
language, whereas $$\mathcal{L}_2$$ will describe its
*meaning*. And one more important requirement: if we have a type in
$$\mathcal{L}_1$$, then we should have some efficient way of
getting all the programs of that type---this will be our parsing
algorithm.

In the case of AB-grammars, $$\mathcal{L}_1$$ has the following types:

$$
    \text{Type }A, B ::= S \mid N \mid NP \mid A \backslash B \mid B / A
$$

The programs in this language consist of a bunch of constants, which
represent words. It also has two rules for building programs, of
them variants of function application:

$$
    \frac{x:A \quad f:A \backslash B}{(fx):B}{\small \backslash e}
    \quad
    \frac{f:B / A \quad x:A}{(fx):B}{\small / e}
$$

The language $$\mathcal{L}_2$$ is the simply-typed lambda calculus,
typed with only the primitive types $$e$$ and $$t$$, for entities
and truth-values:

$$
    \text{Types }\sigma, \tau ::= e \mid t \mid \sigma \to \tau
$$

It also has a set of typed constants, which we use to represent the
abstract meanings of words. This means it contains familiar logical
operators, like $${\wedge}:t\to t\to t$$ or $$\forall:(e\to
t)\to t$$, but also things like $$cat:e\to t$$, the predicate
which tests whether or not something is a cat.

The translation function then maps the types for $$\mathcal{L}_1$$
to types for $$\mathcal{L}_2$$, and the words in
$$\mathcal{L}_1$$ to expressions in $$\mathcal{L}_2$$. For the
types, the translation is as follows:

$$
  \begin{array}{lcl}
    Tr(S) &= &t\\
    Tr(N) &= &e\to t\\
    Tr(NP) &= &e\\
    Tr(A \backslash B) &= &Tr(A)\to Tr(B)\\
    Tr(B / A) &= &Tr(A)\to Tr(B)
  \end{array}
$$

The translation on the level of programs is simple: programs in
$$\mathcal{L}_1$$ consist *solely* of function applications and
some constants. As long as we don't make promises in the types of
those constants that we cannot keep, we should be fine!

So, let's start off by creating some Haskell data types to represent
the syntactic and semantic types described above:

``` haskell
singletons [d|

    data SynT = S | N | NP | SynT :\ SynT | SynT :/ SynT
              deriving (Show,Eq)

    data SemT = E | T | SemT :-> SemT
              deriving (Show,Eq)

  |]
```

The `singletons` function that we're using here is important. It's a
template Haskell function which, given some datatype, defines its
"singleton". A "singleton" is a Haskell data type which has the same
structure on the value level and on the type level. For the type
`SynT` above, that means that the `singletons` function generates a
second data type:

~~~
data SSynT (ty :: SynT) where
  SS    :: SSynT S
  SN    :: SSynT N
  SNP   :: SSynT NP
  (:%\) :: SSynT a -> SSynT b -> SSynT (a :\ b)
  (:%/) :: SSynT b -> SSynT a -> SSynT (b :/ a)
~~~
{:.language-haskell}

By using the singleton of some value, we can get that value *on the
type level*---and by pattern matching on a singleton, we can pattern
match on types! For now, just be aware that those data types are
generated. They will become relevant soon enough.

First off, though---we probably should've done this right away---let's
just set some fixities for our type-level operators:

``` haskell
infixr 5 :\
infixl 5 :/
infixr 5 :->
```

And while we're at it, let's create some type-level aliases for common
parts of speech---though I cannot say that this treatment of appositive
modifiers is entirely common:[^convention]

``` haskell
type IV = NP :\ S  -- intransitive verbs
type TV = IV :/ NP -- transitive verbs
type AP = NP :/ NP -- appositive modifier

sIV = SNP :%\ SS
sTV = sIV :%/ SNP
sAP = SNP :%/ SNP
```

So now that we've defined the types of the languages
$$\mathcal{L}_1$$ and $$\mathcal{L}_2$$, we can define our
translation *on types*. Note that our previous definition of our
translation function was already more-or-less valid Haskell:

``` haskell
type family Tr (ty :: SynT) :: SemT where
  Tr S        = T
  Tr N        = E :-> T
  Tr NP       = E
  Tr (a :\ b) = Tr a :-> Tr b
  Tr (b :/ a) = Tr a :-> Tr b
```

Let's assume for now that we have some sort of data type that we wish
to use to represent our semantic terms, for instance:

~~~
data Expr (ty :: SemT) where
  John :: Expr E
  Mary :: Expr E
  Like :: Expr (E :-> E :-> T)
  (:$) :: Expr (a :-> b) -> Expr a -> Expr b
~~~
{:.language-haskell}

While we have a way of talking about terms of a certain type---e.g. by
saying `Expr E` we can talk about all entities---we cannot really
leave the type open and talk about *all* well-typed terms, regardless
of type. For this we need to introduce a new data type:

``` haskell
data Typed (expr :: SemT -> *) = forall a. Typed (SSynT a, expr (Tr a))
```

The `Typed` data-type contains a tuple of a singleton for a semantic
type, and an expression. Notice that the type-level variable `a` is
shared between the singleton and the expression, which means that the
expression in the second position is forced to be of the type given in
the first.

Our definition of `Typed` has one type-level parameter, `expr`, which
represents the type of expressions. One possible value for this is the
`Expr` type we sketched earlier---for instance, some values of the
type `Typed Expr` would be `(SE, John)`, `(SE, Mary)`, `(ST, Like :$
John :$ Mary)` and `(SE %:-> ST, Like :$ Mary)`.

We are abstracting over the expressions used, but we're going to need
them to support *at least* function application---as this is what AB
grammars are built around. Therefore, we're going to make a tiny type
class which encodes function application of functions using the
semantic types:

``` haskell
class SemE (expr :: SemT -> *) where
    apply :: forall a b. expr (a :-> b) -> expr a -> expr b
```

Using this `apply` function, we can define application on `Typed`
expression as well.[^proofsearch] Since these expressions hide their
type, we cannot enforce on the type-level that this application
necessarily succeeds. What we're doing in the function is the
following:

 1. we pattern match to check if either the left or the right type is
    an appropriate function type;
 2. we use the type-level equality function `%~` to check if the
    argument type is the same in both cases; and
 3. if so, we apply `apply`.

In all other cases, we're forced to return `Nothing`:

``` haskell
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
```

What we've implemented above is just a *check* to see if some given
pair of expressions can be applied as function and argument. Applied
repeatedly, this corresponds to checking if some given syntax tree has
a well-typed function-argument structure. If we want to do this, we're
going to need some sort of trees:

``` haskell
data Tree a = Leaf a | Node (Tree a) (Tree a)
            deriving (Show, Functor, Foldable, Traversable)
```

However, since we don't actually want to write these horribly verbose
things, we're going to use parser combinators to implement a tiny
parser which parses sentences of the form "(the unicorn) (found jack)
first":

``` haskell
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
```

That is to say, for our parser, spaces form nodes in the tree, and are
taken to be right associative. So, the example above represents the
following tree:

            -----------
           /           \
          /           ----
         /           /    \
       ----        ----    \
      /    \      /    \    \
    the unicorn found jack first

Last, before we can write out full implementation of "parsing" with AB
grammars, we're going to need the concept of a lexicon. In our case, a
lexicon will be a function from string to lists of typed expressions
(because a word can have multiple interpretations):

``` haskell
type Lexicon expr = String -> [Typed expr]
```

Parsing consists of four stages:

  1. we parse the given string into a tree;
  2. we look up the words in the tree in the lexicon;
  3. we combine the words using `maybeApply` as defined above; and
  4. we return those resulting terms that are of the correct type.

Below, you see the function written out in full. Note that the
`checkType` function once again makes use of the type-level equality
function `%~`:

``` haskell
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
```



## Interpretations in Haskell

Now comes the part where all this mucking about with singleton types
really pays off. Because our expressions are typed, and sound with
respect to Haskell's type system, we can choose Haskell to be our
semantic language. That means that we now have the ability to parse
strings to valid Haskell functions.

First, let's set up a small language to represent our world, which in
this case is mostly made up of Bob and Tim:

``` haskell
data Entity = Tim -- ^ Tim is a carpenter and an introvert, likes
                  --   holding hands and long walks on the beach.
            | Bob -- ^ Bob is an aspiring actor, and a social media
                  --   junkie. Likes travelling, beer, and Tim.
            deriving (Show)

data Pred = Like Entity Entity -- ^ Is it 'like' or 'like like'?
          | Stupid Entity      -- ^ This is definitely not 'like like'.
          deriving (Show)
```

Secondly, we could turn our expressions into plain Haskell
expressions, but that would be dull. Language isn't side-effect
free---there's all kinds of stuff going on! So, we're going to use
a library for
[extensible effects](http://okmij.org/ftp/Haskell/extensible/) written
by Oleg Kiselyov, Amr Sabry, Cameron Swords, and Hiromi Ishii.

Let's translate our semantic types into effectful Haskell types! And,
most importantly, let's keep the set of effects `r` unspecified!

``` haskell
type family ToEff r t :: * where
  ToEff r E         = Eff r Entity
  ToEff r T         = Eff r Pred
  ToEff r (a :-> b) = ToEff r a -> ToEff r b
```

Now, because Haskell is being a buzzkill about using un-saturated type
families, we have to wrap our translation in a newtype to be able to
use it with the `Typed` definition and the `SemE` type class. And
because of this, we also have to convince Haskell that these wrapped
Haskell functions can be applied:

``` haskell
newtype Ext r a = Ext (ToEff r a)

instance SemE (Ext r) where
  apply (Ext f) (Ext x) = Ext (f x)
```

But now we're all ready to go! First, let's determine the effects we
want to use in our library. We could still leave this underspecified,
and only mention which effects we expect to be supported... but that
would be much more verbose:

``` haskell
type RW = (Reader Entity ': Writer Pred ': '[])
```

Hooray! We can have a lexicon now! And it's reasonably simple, too!

``` haskell
lex :: String -> [Typed (Ext RW)]
lex "tim"    = [ Typed (SNP , Ext (pure Tim))                            ]
lex "bob"    = [ Typed (SNP , Ext (pure Bob))                            ]
lex "likes"  = [ Typed (sTV , Ext (liftA2 (flip Like)))                  ]
lex "stupid" = [ Typed (sAP , Ext (>>= \x -> tell (Stupid x) *> pure x)) ]
lex "him"    = [ Typed (SNP , Ext ask)                                   ]
```

The first two definitions simply return Tim and Bob as effect-free
constants---hence the application of `pure`. Tim and Bob are both of
type `Entity`, and through our translation, `NP` gets translated to
`Eff r Entity`, so this works out.

Then, the predicate `Like` is simply lifted by `liftA2`, which is
similar to `pure`, but for binary functions. The `flip` is present
because according to... *egh*... *grammar*, `Like` will take its
object first and its subject second... but for readability, we'd like
that to be the other way around.

The definition for "stupid" acts as an identity function on entities,
but inserts a predicate into the "appositive dimension". This
corresponds to the linguistic analysis of expressives: they don't
contribute to the sentence meaning, but store their meanings in some
other meaning dimension---in this case, a `Writer` monad!

And last, the definition for "him" simply asks a `Reader` monad what
it's interpretation should be! A more complex example of anaphora
resolution would be to also include a `Writer` monad, and have
entities submit themselves as potential referents, then have this
`Writer` monad periodically empty itself into the `Reader` monad,
e.g. at sentence or clause boundaries, and have anaphora consume the
first appropriate referent... But we digress!

We're still stuck with these unresolved effects coming from our
lexicon. So we're going to define a function `runExt`, which handles
all effects in order, and then escapes the `Eff` monad:

``` haskell
runExt :: Entity -> Ext RW T -> (Pred, [Pred])
runExt x (Ext e) = run (runWriter (runReader e x))
```

And with all this in place, we can handle an example sentence:

``` haskell
example :: [(Pred, [Pred])]
example = runExt Tim <$> parseWith lex "(stupid bob) likes him" SS
```

Which evaluates to: `[(Like Bob Tim,[Stupid Bob])]`

---

[eff]: http://okmij.org/ftp/Haskell/extensible/
[ucm]: http://www.danielgutzmann.com/work/use-conditional-meaning

[^convention]: The convention in the singletons library is to define
    the singleton version of a constructor by prefixing it with an
    `S`. Obviously, since the above definitions aren't constructors,
    we can't do that. However, we stick as close to the convention as
    possible in naming these "derived" singletons `sIV`, `sTV` and `sAP`.

[^proofsearch]: It is the repeated application of this function which
    corresponds to backward-chaining proof search in the more general
    framework of categorial grammar. However, AB grammars *only*
    support function application, and therefore our "proof search" (1)
    can return at most one result, and (2) is more-or-less just a
    cursory check to see if the types match.

[^esslli2015-monads]: For a more hands-on implementation of
    side-effects in natural language using *monads*, see
    <https://github.com/dylnb/esslli2015-monads>.
