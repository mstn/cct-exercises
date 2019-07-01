
\subsection{List as a functor from $\mathit{Set}$ to $\mathit{Mon}$}

This section follows Pierce Chapter 2. In particular, we consider examples 2.1.2 and 2.1.3.

> module Functors.ListAsMonoidFunctor
>
> import Interfaces.Verified
>
> import Basic.Category
> import Basic.Functor
>
> import Idris.TypesAsCategoryExtensional
> import Idris.FunctorAsCFunctor
>
> import Monoid.MonoidsCategory
> import Monoid.Monoid
> import Monoid.MonoidMorphism

A list can be seen as a functor from $Set$ to $Mon$ that takes each set $S$ to the monoid of lists with elements from $S$.
Indeed, a list is a monoid where unit is the empty list and the monoidal operator is the classical list append operator.

The |mapMor| part of this new functor takes a function $f$ over sets to $\mathit{mapList}(f)$. It is easy to show on paper that this
$\mathit{mapList}(f)$ is actually a monoidal homomorphism. Let's see how to prove it in Idris.

First, we define the functor mapping where |mapToMonoidList| and |mapToMonoidListMorphism| are |mapObj| and |mapMor|, respectively.

Fortunately, Idris implements the concept of monoid. We can borrow this definition and wrap it in |idris-ct| monoids using some utilities from |idris-ct|.

> mapToMonoidList : (a : Type) -> Monoid
> mapToMonoidList a = buildMonoid @{the (VerifiedMonoid (List a)) %implementation}

The defintion of |mapToMonoidListMorphism| is not hard. As before, we can reuse Idris already proved theorems, in this case, |mapAppendDistributive| from |Prelude|.

> mapToMonoidListMorphism :
>     (a, b : Type)
>  -> (f : ExtensionalTypeMorphism a b)
>  -> MonoidMorphism (mapToMonoidList a) (mapToMonoidList b)
> mapToMonoidListMorphism a b (MkExtensionalTypeMorphism f) = MkMonoidMorphism
>   (map f)
>   (mapAppendDistributive f)
>   (Refl)

Finally, we have to prove the functor properties, that is, |preserveId| and |preserveCompose|. The first one is trivial.

> mapToMonoidListPreserveId :
>      (a : Type)
>   -> mapToMonoidListMorphism a a (extIdentity a) = monoidIdentity (mapToMonoidList a)
> mapToMonoidListPreserveId a = monoidMorphismEq
>   (mapToMonoidListMorphism a a (extIdentity a))
>   (monoidIdentity (mapToMonoidList a))
>   (\x => functorIdentity id (\_ => Refl) x)

The other one, |mapToMonoidListPreserveCompose|, is a bit trickier. Idris is not able to understand that |func| for monoids and extended functions are actually the same things.
We need to help the compiler with some auxiliary trivial lemmas. Please note that a better way might exist, but I do not know how to use Idris to prove |mapToMonoidListPreserveCompose|
without the two lemmas.

> unfoldExtCompose :
>      (f : ExtensionalTypeMorphism a b)
>   -> (g : ExtensionalTypeMorphism b c)
>   -> func (mapToMonoidListMorphism a c (extCompose a b c f g))
>      = func (mapToMonoidListMorphism a c (MkExtensionalTypeMorphism (func g . func f)))
> unfoldExtCompose (MkExtensionalTypeMorphism f)  (MkExtensionalTypeMorphism g) = Refl

> unpackMonMorphism :
>      (f : ExtensionalTypeMorphism a b)
>   -> func (mapToMonoidListMorphism a b f) = map (func f)
> unpackMonMorphism (MkExtensionalTypeMorphism f) = Refl

> packMonMorphism :
>      (f : ExtensionalTypeMorphism a b)
>   -> (g : ExtensionalTypeMorphism b c)
>   -> (map (func g) . map (func f)) = func (monoidMorphismsComposition (mapToMonoidListMorphism a b f) (mapToMonoidListMorphism b c g))
> packMonMorphism (MkExtensionalTypeMorphism f) (MkExtensionalTypeMorphism g) = Refl

> applyWith : (x : a) -> (a -> b) -> b
> applyWith x = \f => apply f x

This function is the actual property we want to prove.

> mapToMonoidListPreserveCompose :
>      (a, b, c : Type)
>   -> (f : ExtensionalTypeMorphism a b)
>   -> (g : ExtensionalTypeMorphism b c)
>   -> mapToMonoidListMorphism a c (extCompose a b c f g)
>      = monoidMorphismsComposition (mapToMonoidListMorphism a b f) (mapToMonoidListMorphism b c g)
> mapToMonoidListPreserveCompose a b c f g = monoidMorphismEq
>   (mapToMonoidListMorphism a c (extCompose a b c f g))
>   (monoidMorphismsComposition (mapToMonoidListMorphism a b f)  (mapToMonoidListMorphism b c g))
>   (\x =>
>       trans
>         (cong { f = (applyWith x) }  (unfoldExtCompose f g))
>         (trans
>             (trans
>               (cong { f = (applyWith x) } (unpackMonMorphism  (MkExtensionalTypeMorphism ((func g) . (func f)))))
>               (functorComposition x (func f) (func g))
>              )
>              (cong { f = (applyWith x) } (packMonMorphism f g))
>          )
>   )

Finally, we can prove that what we defined is a functor.

> mapToMonoidListFunctor : CFunctor TypesAsCategoryExtensional.typesAsCategoryExtensional Monoid.MonoidsCategory.monoidsCategory
> mapToMonoidListFunctor = MkCFunctor
>   (mapToMonoidList)
>   (mapToMonoidListMorphism)
>   (mapToMonoidListPreserveId)
>   (mapToMonoidListPreserveCompose)

Note that we used the theorems from |VerifiedFunctor| instead of |ListAsSetFunctor| properties,
Under the hood, |ListAsSetFunctor| uses |VerifiedFunctor|, too. So it could look like the dog chasing its own tail.
However, the categorical approach is more abstract since it does not depend on the concrete type |List|.
Next, we are going to generalize this piece of code in a more categorical way.
