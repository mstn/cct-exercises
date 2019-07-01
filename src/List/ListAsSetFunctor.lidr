\subsection{List as a functor from $\mathit{Set}$ to $\mathit{Set}$}

This section follows Pierce Chapter 2. In particular, we consider example 2.1.2.

Given a set $S$, we define the set $List(S)$ of finite lists with elements from $S$.
We can see $List$ as a |CFunctor| from $Set$ to $Set$ where

\begin{itemize}
  \item |mapObj| maps set $S$ to $List(S)$
  \item |mapMor| takes a function $f : S \to T$ to a function $List(f) : List(S) \to List(T)$
        where $f$ is applied to each element of the list, individually.
\end{itemize}

> module Functors.ListAsSetFunctor
>
> import Interfaces.Verified
>
> import Basic.Category
> import Basic.Functor
>
> import Idris.TypesAsCategoryExtensional
> import Idris.FunctorAsCFunctor

We can use |idris-ct| utility to map Idris functors to CT functors. Idris provides an implementation of |List| functor,
we just need to access it using |%implementation| keyword.

> ListAsSetFunctor : CFunctor TypesAsCategoryExtensional.typesAsCategoryExtensional TypesAsCategoryExtensional.typesAsCategoryExtensional
> ListAsSetFunctor = functorToCFunctor (the (VerifiedFunctor List) %implementation)
