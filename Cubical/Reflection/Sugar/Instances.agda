{-

This module provides specific instances for various classes defined in `Sugar.Base`, integrating definitions from the Cubical library. The instances cover several widely-used types and structures within the Cubical library.

Key Features:

- **Applicative and Monad Instances**:
  - `Maybe`: Instance implementations for `RawApplicative` and `RawMonad`.
  - `List`: Instance implementations for `RawApplicative` and `RawMonad`.
  - `Sum`: Supports sum types (`⊎`), with instances for both `RawApplicative` and `RawMonad`.

- **Monad Transformer Instances**:
  - `State`: Provides a monad transformer instance for state computations.
  - `Plus`: Provides a monad transformer instance for sum types.

- **Utility Functions**:
  - Functions like `mapM`, `concatMapM`, `foldlM`, and `foldrM` facilitate common monadic operations on lists.
  - Functions `get` and `modify` support stateful computations.


Note how the use of type-level `ω` simplifies the writing of instances without dealing with universe polymorphism, wich is instead dealt with in de definition of functions relaying on those instances.

-}

{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Reflection.Sugar.Instances where


open import Cubical.Foundations.Function


open import Cubical.Reflection.Sugar.Base
open import Cubical.Data.List as L
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.Sigma


module _ {M : Functorω} {{_ : RawApplicative M}} {{_ : RawMonad M}} where

 mapM : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
            → (A → M B) → List A → M (List B)
 mapM f [] = ⦇ [] ⦈
 mapM f (x ∷ xs) = ⦇ f x ∷ mapM f xs ⦈

 mapM-snd : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {A' : Type ℓ'} {B : Type ℓ''}
            → (A → M B) → A' × A → M (A' × B)
 mapM-snd f (x , y) = ⦇ ⦇ x ⦈ , f y ⦈

 concatMapM : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
            → (A → M (List B)) → List A → M (List B)
 concatMapM f [] = ⦇ [] ⦈
 concatMapM f (x ∷ xs) = ⦇ f x ++ concatMapM f xs ⦈


 foldlM : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
            → (B → A → M B) → B → List A → M B
 foldlM f b [] = pure b
 foldlM f b (x ∷ xs) = f b x >>= (flip (foldlM f)) xs


 foldrM : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
            → (A → B → M B) → B → List A → M B
 foldrM f b [] = pure b
 foldrM f b (x ∷ xs) = foldrM f b xs >>= f x


State₀T : Type → Functorω → Functorω
State₀T S F T = S → F (T × S)


get : {F : Functorω} {{FA : RawApplicative F }} {{FM : RawMonad F }} {S : Type}  → [ State₀T S RMT F ] S
unwrap get s = pure (s , s)

modify : {F : Functorω} {{FA : RawApplicative F }} {{FM : RawMonad F }} {S : Type}  →
  (S → S) → [ State₀T S RMT F ] Unit
unwrap (modify f) s = pure (_ , f s)


Plus₀T : Type → Functorω → Functorω
Plus₀T E F T = F (E ⊎.⊎ T)

module _ where
 open RawMonadTransformer

 instance
  rawMonadTransformerState₀ : ∀ {S} → RawMonadTransformer (State₀T S)
  (applicativeLiftT rawMonadTransformerState₀ RawApplicative.<$> x) = (map-fst x <$>_) ∘S_
  RawApplicative.pure (applicativeLiftT rawMonadTransformerState₀) x = pure ∘S (x ,_)
  (applicativeLiftT rawMonadTransformerState₀ RawApplicative.<*> f) x s =
    f s >>= uncurry (_<$>_ ∘S map-fst) ∘S map-snd x

  (monadLiftT rawMonadTransformerState₀ RawMonad.>>= x) y s = x s >>= uncurry y

  (monadLiftT rawMonadTransformerState₀ RawMonad.>> x) y s = x s >>= y ∘S snd
  lifting rawMonadTransformerState₀ x s = (_, s) <$> x

  rawMonadTransformerPlus₀ : ∀ {S} → RawMonadTransformer (Plus₀T S)
  (applicativeLiftT rawMonadTransformerPlus₀ RawApplicative.<$> x) =
    (⊎.map (idfun _) x) <$>_
  RawApplicative.pure (applicativeLiftT rawMonadTransformerPlus₀) x = pure (⊎.inr x)
  (applicativeLiftT rawMonadTransformerPlus₀ RawApplicative.<*> f) x =
    f >>= ⊎.rec (pure ∘S ⊎.inl) λ f → ⊎.map (idfun _) f <$> x
  (monadLiftT rawMonadTransformerPlus₀ RawMonad.>>= x) y =
    x >>= ⊎.rec (pure ∘S ⊎.inl) y
  (monadLiftT rawMonadTransformerPlus₀ RawMonad.>> x) y =
    x >>= ⊎.rec (pure ∘S ⊎.inl) (const y)
  lifting rawMonadTransformerPlus₀ x = ⊎.inr <$> x


  ApplicativeSum : {E : Type} → RawApplicative (E ⊎.⊎_)
  ApplicativeSum = applicativeLiftT rawMonadTransformerPlus₀ {{_}} {{RawMonadIdentityM}}

  MonadSum : {E : Type} → RawMonad (E ⊎.⊎_)
  MonadSum = monadLiftT rawMonadTransformerPlus₀ {{_}} {{RawMonadIdentityM}}



instance
 ApplicativeMaybe : RawApplicative Maybe
 RawApplicative._<$>_ ApplicativeMaybe = map-Maybe
 RawApplicative.pure ApplicativeMaybe = just
 (ApplicativeMaybe RawApplicative.<*> nothing) x₁ = nothing
 (ApplicativeMaybe RawApplicative.<*> just x) nothing = nothing
 (ApplicativeMaybe RawApplicative.<*> just x) (just x₁) = just (x x₁)


 MonadMaybe : RawMonad Maybe
 RawMonad._>>=_ MonadMaybe = flip (Mb.rec nothing)
 RawMonad._>>_ MonadMaybe = flip (Mb.rec nothing ∘ const)

 ApplicativeList : RawApplicative List
 RawApplicative._<$>_ ApplicativeList = L.map
 RawApplicative.pure ApplicativeList = [_]
 (ApplicativeList RawApplicative.<*> fs) xs = L.map (uncurry _$_) (cart fs xs)


 MonadList : RawMonad List
 RawMonad._>>=_ MonadList xs f = L.join (map f xs)
 RawMonad._>>_ MonadList xs ys = L.join (map (λ _ → ys) xs)


when : ∀ {M : Functorω} {{_ : RawApplicative M}} → Bool → M Unit → M Unit
when {M} false x = pure _
when {M} true x = x



infixl 4 _<⊎>_


private
 variable
  ℓ : Level
  A B E : Type ℓ

_<⊎>_ : {M : Functorω} {{_ : RawApplicative M}} {{_ : RawMonad M}} {{_ : RawMonadFail M E}} →
  (M A) → (M B) → M (A ⊎.⊎ B)
a <⊎> b = (⊎.inl <$> a) <|> (⊎.inr <$> b)
