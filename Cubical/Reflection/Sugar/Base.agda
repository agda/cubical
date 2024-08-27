{-

This module introduces several key classes and concepts for syntactic sugar in Agda:

- **Raw Monad**: Defines a basic monadic structure.
- **Raw Monad Fail**: Extends `Raw Monad` to handle failure cases.
- **Raw Applicative**: Defines an applicative structure.
- **Raw Monad Transformer**: Facilitates monad transformers.
- **Identity Functor**: Provides an identity functor to use with the above structures.

Key characteristics:

- No dependencies on the Cubical library, ensuring broad usability.
- Designed to simplify macro writing, not for formal reasoning.
- Utilizes type-level `ω` for defining functors to ease instance writing without requiring universe polymorphism.

All definitions necessary for syntactic sugar are implemented, allowing the use of multiple monads and applicatives correctly within the same context through instance resolution.

-}

{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Reflection.Sugar.Base where

open import Agda.Primitive public
  using    ( Level )
  renaming (  Set   to Type
           ;  Setω  to Typeω
           )

private
 variable
  ℓ ℓ' : Level
  A B C E : Type ℓ

Functorω : Typeω
Functorω = ∀ {ℓ} → Type ℓ → Type ℓ

private
 variable
  M : Functorω

record IdentityF (A : Type ℓ) : Type ℓ where ; constructor identity ; field ; runIdentity : A

open IdentityF public


record RawApplicative (F : Functorω) : Typeω where
 field
  _<$>_ : (A → B) → F A → F B
  pure : A → F A
  _<*>_ : F (A → B) → F A → F B

 infixl 4 _<*>_ _<$>_




module _ (M : Functorω) {{RA : RawApplicative M}} where

 open RawApplicative RA public



 record RawMonad : Typeω where
  field
   _>>=_ : M A → (A → M B) → M B
   _>>_ : M A → M B → M B

  infixl 4 _>>=_ _>>_




 module _ {{RM : RawMonad}} where

  open RawMonad RM public

  record RawMonadFail (E : Type ℓ') : Typeω where
   field
    fail : E → M A
    _<|>_ : M A → M A → M A

   infixl 4 _<|>_


  module _  {{RME : RawMonadFail E}}  where
   open RawMonadFail RME public



_>=&_ : ∀ {M : Functorω} {{_ : RawApplicative M}} →
  (A → M B) → (B → C) → A → M C
(x >=& x₁) x₂ =  x₁ <$> x x₂

joinM : ∀ {M : Functorω} {{_ : RawApplicative M}} {{_ : RawMonad M}} →
   M (M A) → M A
joinM x = x >>= (λ x → x)

_>=>_ :  ∀ {M : Functorω} {{_ : RawApplicative M}} {{_ : RawMonad M}} →
  (A → M B) → (B → M C) → A → M C
(x >=> x₁) x₂ = x x₂ >>= x₁

instance
 RawApplicativeIdentityF : RawApplicative IdentityF
 runIdentity ((RawApplicativeIdentityF RawApplicative.<$> f) x) = f (runIdentity x)
 runIdentity (RawApplicative.pure RawApplicativeIdentityF x) = x
 runIdentity ((RawApplicativeIdentityF RawApplicative.<*> f) x) = runIdentity f (runIdentity x)


 RawMonadIdentityF : RawMonad IdentityF
 (RawMonadIdentityF RawMonad.>>= x) y = y (runIdentity x)
 (RawMonadIdentityF RawMonad.>> _) y = y


RawApplicativeIdentityM : RawApplicative (λ {_} X → X)
RawApplicative._<$>_ RawApplicativeIdentityM f = f
RawApplicative.pure RawApplicativeIdentityM x = x
RawApplicative._<*>_ RawApplicativeIdentityM f x = f x


RawMonadIdentityM : RawMonad (λ {_} X → X) {{RawApplicativeIdentityM}}
(RawMonadIdentityM RawMonad.>>= x) y = y x
(RawMonadIdentityM RawMonad.>> _) y = y


record RawMonadTransformer (T : Functorω → Functorω) : Typeω where
 field
  lifting : {F : Functorω} → {{RA : RawApplicative F}} → {{_ : RawMonad F}} →  F A → T F A

  applicativeLiftT : {F : Functorω} → {{RA : RawApplicative F}}
      → {{RM : RawMonad F}} → RawApplicative (T F)

  monadLiftT : {F : Functorω} → {{RA : RawApplicative F}} → {{_ : RawMonad F}}
     → RawMonad (T F) {{applicativeLiftT}}


open RawMonadTransformer public


record [_RMT_]_ (T : Functorω → Functorω) (F : Functorω) {ℓ} (A : Type ℓ) : Type ℓ where
 constructor wrap
 field
   unwrap : T F A

open [_RMT_]_  public




module _ {T} {{rmt : RawMonadTransformer T}} where


 private
  instance
   ApplicativeLiftT' : {F : Functorω} →
     {{_ : RawApplicative F}} → {{_ : RawMonad F}} → RawApplicative (T F)
   ApplicativeLiftT' = applicativeLiftT rmt

  instance
   MonadLiftT' : {F : Functorω} →
     {{_ : RawApplicative F}} → {{_ : RawMonad F}} → RawMonad (T F)
   MonadLiftT' = monadLiftT rmt

 liftM : {F : Functorω} → {{_ : RawApplicative F}} → {{_ : RawMonad F}} → F A → [ T RMT F ] A
 liftM x = wrap (lifting rmt x)

 instance
   ApplicativeLiftT : {{RA : RawApplicative M}}
      → {{RM : RawMonad M}} → RawApplicative ([ T RMT M ]_)
   unwrap ((ApplicativeLiftT RawApplicative.<$> x) x₁) = x <$> unwrap x₁
   unwrap (RawApplicative.pure ApplicativeLiftT x) = pure x
   unwrap ((ApplicativeLiftT RawApplicative.<*> x) x₁) = unwrap x <*> unwrap x₁

   MonadLiftT : {{_ : RawApplicative M}} → {{_ : RawMonad M}} → RawMonad ([ T RMT M ]_)
   unwrap ((MonadLiftT RawMonad.>>= x) x₁) = unwrap x >>= λ v → unwrap (x₁ v)
   unwrap ((MonadLiftT RawMonad.>> x) x₁) = unwrap x >> unwrap x₁
