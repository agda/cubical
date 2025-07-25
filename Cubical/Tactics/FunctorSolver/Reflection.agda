
module Cubical.Tactics.FunctorSolver.Reflection where

open import Cubical.Foundations.Prelude

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String

open import Cubical.Data.Bool
open import Cubical.Data.List
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Reflection.Base
open import Cubical.Tactics.FunctorSolver.Solver
open import Cubical.Tactics.Reflection

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Free.Category
open import Cubical.Categories.Constructions.Free.Functor
open import Cubical.Categories.Functor

private
  variable
    ℓ ℓ' : Level

module ReflectionSolver where
  module _ (domain : Term) (codomain : Term) (functor : Term) where
    -- the two implicit levels and the category
    pattern category-args xs =
      _ h∷ _ h∷ _ v∷ xs

    -- the four implicit levels, the two implicit categories and the functor
    pattern functor-args functor xs =
      _ h∷ _ h∷ _ h∷ _ h∷ _ h∷ _ h∷ functor v∷ xs

    pattern “id” =
      def (quote Category.id) (category-args (_ h∷ []))

    pattern “⋆” f g =
      def (quote Category._⋆_) (category-args (_ h∷ _ h∷ _ h∷ f v∷ g v∷ []))

    pattern “F” functor f =
      def (quote Functor.F-hom) (functor-args functor (_ h∷ _ h∷ f v∷ []))

    -- Parse the input into an exp
    buildDomExpression : Term → Term
    buildDomExpression “id” = con (quote FreeCategory.idₑ) []
    buildDomExpression (“⋆” f g) =
      con (quote FreeCategory._⋆ₑ_)
          (buildDomExpression f v∷ buildDomExpression g v∷ [])
    buildDomExpression f = con (quote FreeCategory.↑_) (f v∷ [])

    buildCodExpression : Term → TC Term
    buildCodExpression “id” = returnTC (con (quote FreeFunctor.idₑ) [])
    buildCodExpression (“⋆” f g) =
      ((λ fe ge → (con (quote FreeFunctor._⋆ₑ_) (fe v∷ ge v∷ [])))
        <$> buildCodExpression f)
        <*> buildCodExpression g
    buildCodExpression (“F” functor' f) = do
      unify functor functor'
      returnTC (con (quote FreeFunctor.F⟪_⟫) (buildDomExpression f v∷ []))
    buildCodExpression f = returnTC (con (quote FreeFunctor.↑_) (f v∷ []))

  solve-macro : Bool -- ^ whether to give the more detailed but messier error
                     --   message on failure
              → Term -- ^ The term denoting the domain category
              → Term -- ^ The term denoting the codomain category
              → Term -- ^ The term denoting the functor
              → Term -- ^ The hole whose goal should be an equality between
                     --   morphisms in the codomain category
              → TC Unit
  solve-macro b dom cod fctor =
    equation-solver
      (quote Category.id ∷ quote Category._⋆_ ∷ quote Functor.F-hom ∷ [])
      mk-call
      b
      where

      mk-call : Term → Term → TC Term
      mk-call lhs rhs = do
        l-e ← buildCodExpression dom cod fctor lhs
        r-e ← buildCodExpression dom cod fctor rhs
        -- unify l-e r-e
        returnTC (def (quote Eval.solve) (
          dom v∷ cod v∷ fctor v∷
          l-e v∷ r-e v∷ def (quote refl) [] v∷ []))
macro
  solveFunctor! : Term → Term → Term → Term → TC _
  solveFunctor! = ReflectionSolver.solve-macro false

  solveFunctorDebug! : Term → Term → Term → Term → TC _
  solveFunctorDebug! = ReflectionSolver.solve-macro true
