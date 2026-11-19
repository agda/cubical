-- universe⁰ is closed under the codes for the basic sets and the type formers,
-- using that lift-V⁰ commutes with each of them

{-# OPTIONS --lossy-unification #-}

module Cubical.Data.IterativeSets.Universes.Closures where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sum.Properties using (⊎-equiv)
open import Cubical.Data.Unit using (Unit ; Unit*)
open import Cubical.Data.Bool using (Bool ; Bool* ; false ; true)
open import Cubical.Data.Empty as ⊥ using (⊥*)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; ℕ*)
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Data.IterativeMultisets.Base using (sup-∞ ; ≡V∞-≃-≡Equiv)
open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Universes
open import Cubical.Data.IterativeSets.Empty
open import Cubical.Data.IterativeSets.Unit
open import Cubical.Data.IterativeSets.Bool
open import Cubical.Data.IterativeSets.Singleton.Base
open import Cubical.Data.IterativeSets.Singleton.Properties
open import Cubical.Data.IterativeSets.UnorderedPair.Base
open import Cubical.Data.IterativeSets.UnorderedPair.Properties
open import Cubical.Data.IterativeSets.OrderedPair
open import Cubical.Data.IterativeSets.Sigma
open import Cubical.Data.IterativeSets.Pi
open import Cubical.Data.IterativeSets.Sum
open import Cubical.Data.IterativeSets.Identity
open import Cubical.Data.IterativeSets.Fiber
open import Cubical.Data.IterativeSets.Nat

private
  variable
    ℓ : Level

private
  V⁰-ext : (x y : V⁰ {ℓ}) (e : El⁰ x ≃ El⁰ y)
         → ((a : El⁰ x) → elements x a ≡ elements y (e .fst a))
         → x ≡ y
  V⁰-ext (sup-∞ _ _ , _) (sup-∞ _ _ , _) e h =
    invEq ≡V⁰-≃-≡V∞ (invEq ≡V∞-≃-≡Equiv (e , funExt (λ a → cong fst (h a))))

-- raising commutes with the basic sets

lift-V⁰-empty⁰ : (ℓ' : Level) → lift-V⁰ ℓ' (empty⁰ {ℓ}) ≡ empty⁰ {ℓ-max ℓ ℓ'}
lift-V⁰-empty⁰ {ℓ} ℓ' = V⁰-ext (lift-V⁰ ℓ' empty⁰) empty⁰ e (λ a → ⊥.rec (a .lower .lower))
  where
    e : Lift ℓ' (⊥* {ℓ}) ≃ ⊥* {ℓ-max ℓ ℓ'}
    e = ⊥.uninhabEquiv (λ a → a .lower .lower) lower

lift-V⁰-singleton⁰ : (ℓ' : Level) (x : V⁰ {ℓ})
                   → lift-V⁰ ℓ' (singleton⁰ x) ≡ singleton⁰ (lift-V⁰ ℓ' x)
lift-V⁰-singleton⁰ {ℓ} ℓ' x =
  V⁰-ext (lift-V⁰ ℓ' (singleton⁰ x)) (singleton⁰ (lift-V⁰ ℓ' x)) e (λ _ → refl)
  where
    e : Lift ℓ' (Unit* {ℓ}) ≃ Unit* {ℓ-max ℓ ℓ'}
    e = compEquiv (invEquiv LiftEquiv) (Lift≃Lift (idEquiv Unit))

lift-V⁰-unit⁰ : (ℓ' : Level) → lift-V⁰ ℓ' (unit⁰ {ℓ}) ≡ unit⁰ {ℓ-max ℓ ℓ'}
lift-V⁰-unit⁰ ℓ' = lift-V⁰-singleton⁰ ℓ' empty⁰ ∙ cong singleton⁰ (lift-V⁰-empty⁰ ℓ')

lift-V⁰-unorderedPair⁰ : (ℓ' : Level) {x y : V⁰ {ℓ}} (x≢y : ¬ (x ≡ y))
                       → lift-V⁰ ℓ' (unorderedPair⁰ x y x≢y)
                         ≡ unorderedPair⁰ (lift-V⁰ ℓ' x) (lift-V⁰ ℓ' y) (x≢y ∘ lift-V⁰-inj ℓ')
lift-V⁰-unorderedPair⁰ {ℓ} ℓ' {x} {y} x≢y =
  V⁰-ext (lift-V⁰ ℓ' (unorderedPair⁰ x y x≢y))
         (unorderedPair⁰ (lift-V⁰ ℓ' x) (lift-V⁰ ℓ' y) (x≢y ∘ lift-V⁰-inj ℓ')) e elts
  where
    e : Lift ℓ' (Bool* {ℓ}) ≃ Bool* {ℓ-max ℓ ℓ'}
    e = compEquiv (invEquiv LiftEquiv) (Lift≃Lift (idEquiv Bool))

    elts : (b : Lift ℓ' (Bool* {ℓ}))
         → elements (lift-V⁰ ℓ' (unorderedPair⁰ x y x≢y)) b
           ≡ elements (unorderedPair⁰ (lift-V⁰ ℓ' x) (lift-V⁰ ℓ' y) (x≢y ∘ lift-V⁰-inj ℓ'))
                      (e .fst b)
    elts (lift (lift false)) = refl
    elts (lift (lift true)) = refl

lift-V⁰-bool⁰ : (ℓ' : Level) → lift-V⁰ ℓ' (bool⁰ {ℓ}) ≡ bool⁰ {ℓ-max ℓ ℓ'}
lift-V⁰-bool⁰ ℓ' = lift-V⁰-unorderedPair⁰ ℓ' empty⁰≢unit⁰
                   ∙ unorderedPair⁰-cong (lift-V⁰-empty⁰ ℓ') (lift-V⁰-unit⁰ ℓ')

lift-V⁰-orderedPair⁰ : (ℓ' : Level) (x y : V⁰ {ℓ})
                     → lift-V⁰ ℓ' ⟨ x , y ⟩⁰ ≡ ⟨ lift-V⁰ ℓ' x , lift-V⁰ ℓ' y ⟩⁰
lift-V⁰-orderedPair⁰ ℓ' x y =
  lift-V⁰-unorderedPair⁰ ℓ' unorderedPair⁰≢singleton⁰ ∙ unorderedPair⁰-cong left right
  where
    left : lift-V⁰ ℓ' (unorderedPair⁰ (singleton⁰ x) empty⁰ singleton⁰≢empty⁰)
           ≡ unorderedPair⁰ (singleton⁰ (lift-V⁰ ℓ' x)) empty⁰ singleton⁰≢empty⁰
    left = lift-V⁰-unorderedPair⁰ ℓ' singleton⁰≢empty⁰
           ∙ unorderedPair⁰-cong (lift-V⁰-singleton⁰ ℓ' x) (lift-V⁰-empty⁰ ℓ')

    right : lift-V⁰ ℓ' (singleton⁰ (singleton⁰ y)) ≡ singleton⁰ (singleton⁰ (lift-V⁰ ℓ' y))
    right = lift-V⁰-singleton⁰ ℓ' (singleton⁰ y) ∙ cong singleton⁰ (lift-V⁰-singleton⁰ ℓ' y)

-- raising commutes with the type formers

lift-V⁰-Σ⁰ : (ℓ' : Level) (x : V⁰ {ℓ}) (y : El⁰ x → V⁰ {ℓ})
           → lift-V⁰ ℓ' (Σ⁰ x y) ≡ Σ⁰ (lift-V⁰ ℓ' x) (lift-V⁰ ℓ' ∘ y ∘ lowerEl⁰ ℓ' x)
lift-V⁰-Σ⁰ {ℓ} ℓ' x y = sym (V⁰-ext (Σ⁰ (lift-V⁰ ℓ' x) y') (lift-V⁰ ℓ' (Σ⁰ x y)) e elts)
  where
    y' : El⁰ (lift-V⁰ ℓ' x) → V⁰ {ℓ-max ℓ ℓ'}
    y' = lift-V⁰ ℓ' ∘ y ∘ lowerEl⁰ ℓ' x

    e : El⁰ (Σ⁰ (lift-V⁰ ℓ' x) y') ≃ El⁰ (lift-V⁰ ℓ' (Σ⁰ x y))
    e = compEquiv (Σ-cong-equiv (El⁰-lift-V⁰≃El⁰ ℓ' x)
                                (λ a → El⁰-lift-V⁰≃El⁰ ℓ' (y (lowerEl⁰ ℓ' x a))))
                  LiftEquiv

    elts : (c : El⁰ (Σ⁰ (lift-V⁰ ℓ' x) y'))
         → elements (Σ⁰ (lift-V⁰ ℓ' x) y') c ≡ elements (lift-V⁰ ℓ' (Σ⁰ x y)) (e .fst c)
    elts (a , b) =
      cong₂ ⟨_,_⟩⁰ (elements-lift-V⁰ ℓ' x a) (elements-lift-V⁰ ℓ' (y a') b)
      ∙ sym (lift-V⁰-orderedPair⁰ ℓ' (elements x a') (elements (y a') (lowerEl⁰ ℓ' (y a') b)))
      where
        a' : El⁰ x
        a' = lowerEl⁰ ℓ' x a

lift-V⁰-×⁰ : (ℓ' : Level) (x y : V⁰ {ℓ})
           → lift-V⁰ ℓ' (x ×⁰ y) ≡ (lift-V⁰ ℓ' x ×⁰ lift-V⁰ ℓ' y)
lift-V⁰-×⁰ ℓ' x y = lift-V⁰-Σ⁰ ℓ' x (λ _ → y)

lift-V⁰-Π⁰ : (ℓ' : Level) (x : V⁰ {ℓ}) (y : El⁰ x → V⁰ {ℓ})
           → lift-V⁰ ℓ' (Π⁰ x y) ≡ Π⁰ (lift-V⁰ ℓ' x) (lift-V⁰ ℓ' ∘ y ∘ lowerEl⁰ ℓ' x)
lift-V⁰-Π⁰ {ℓ} ℓ' x@(sup-∞ _ _ , _) y =
  sym (V⁰-ext (Π⁰ (lift-V⁰ ℓ' x) y') (lift-V⁰ ℓ' (Π⁰ x y)) e elts)
  where
    y' : El⁰ (lift-V⁰ ℓ' x) → V⁰ {ℓ-max ℓ ℓ'}
    y' = lift-V⁰ ℓ' ∘ y ∘ lowerEl⁰ ℓ' x

    isom : Iso ((a : El⁰ (lift-V⁰ ℓ' x)) → El⁰ (y' a)) ((a : El⁰ x) → El⁰ (y a))
    isom .Iso.fun Φ a = lowerEl⁰ ℓ' (y a) (Φ (lift a))
    isom .Iso.inv Ψ a = liftEl⁰ ℓ' (y (a .lower)) (Ψ (a .lower))
    isom .Iso.sec Ψ = funExt (λ a → secEq (El⁰-lift-V⁰≃El⁰ ℓ' (y a)) (Ψ a))
    isom .Iso.ret Φ = funExt (λ a → retEq (El⁰-lift-V⁰≃El⁰ ℓ' (y (a .lower))) (Φ a))

    e : El⁰ (Π⁰ (lift-V⁰ ℓ' x) y') ≃ El⁰ (lift-V⁰ ℓ' (Π⁰ x y))
    e = compEquiv (isoToEquiv isom) LiftEquiv

    elts : (Φ : El⁰ (Π⁰ (lift-V⁰ ℓ' x) y'))
         → elements (Π⁰ (lift-V⁰ ℓ' x) y') Φ ≡ elements (lift-V⁰ ℓ' (Π⁰ x y)) (e .fst Φ)
    elts Φ = V⁰-ext (elements (Π⁰ (lift-V⁰ ℓ' x) y') Φ)
                    (elements (lift-V⁰ ℓ' (Π⁰ x y)) (e .fst Φ))
                    (idEquiv (El⁰ (lift-V⁰ ℓ' x))) graphElts
      where
        graphElts : (a : El⁰ (lift-V⁰ ℓ' x))
                  → ⟨ elements (lift-V⁰ ℓ' x) a , elements (y' a) (Φ a) ⟩⁰
                    ≡ lift-V⁰ ℓ' ⟨ elements x (a .lower)
                                , elements (y (a .lower)) (lowerEl⁰ ℓ' (y (a .lower)) (Φ a)) ⟩⁰
        graphElts a =
          cong ⟨ elements (lift-V⁰ ℓ' x) a ,_⟩⁰ (elements-lift-V⁰ ℓ' (y (a .lower)) (Φ a))
          ∙ sym (lift-V⁰-orderedPair⁰ ℓ' (elements x (a .lower))
                   (elements (y (a .lower)) (lowerEl⁰ ℓ' (y (a .lower)) (Φ a))))

lift-V⁰-→⁰ : (ℓ' : Level) (x y : V⁰ {ℓ})
           → lift-V⁰ ℓ' (x →⁰ y) ≡ (lift-V⁰ ℓ' x →⁰ lift-V⁰ ℓ' y)
lift-V⁰-→⁰ ℓ' x y = lift-V⁰-Π⁰ ℓ' x (λ _ → y)

lift-V⁰-Id⁰ : (ℓ' : Level) (x : V⁰ {ℓ}) (a b : El⁰ x)
            → lift-V⁰ ℓ' (Id⁰ x a b) ≡ Id⁰ (lift-V⁰ ℓ' x) (liftEl⁰ ℓ' x a) (liftEl⁰ ℓ' x b)
lift-V⁰-Id⁰ ℓ' x a b =
  V⁰-ext (lift-V⁰ ℓ' (Id⁰ x a b)) (Id⁰ (lift-V⁰ ℓ' x) (liftEl⁰ ℓ' x a) (liftEl⁰ ℓ' x b))
         e (λ _ → lift-V⁰-empty⁰ ℓ')
  where
    e : Lift ℓ' (a ≡ b) ≃ (liftEl⁰ ℓ' x a ≡ liftEl⁰ ℓ' x b)
    e = compEquiv (invEquiv LiftEquiv) (congEquiv (invEquiv (El⁰-lift-V⁰≃El⁰ ℓ' x)))

lift-V⁰-+⁰ : (ℓ' : Level) (x y : V⁰ {ℓ})
           → lift-V⁰ ℓ' (x +⁰ y) ≡ (lift-V⁰ ℓ' x +⁰ lift-V⁰ ℓ' y)
lift-V⁰-+⁰ {ℓ} ℓ' x y =
  sym (V⁰-ext (lift-V⁰ ℓ' x +⁰ lift-V⁰ ℓ' y) (lift-V⁰ ℓ' (x +⁰ y)) e elts)
  where
    e : El⁰ (lift-V⁰ ℓ' x +⁰ lift-V⁰ ℓ' y) ≃ El⁰ (lift-V⁰ ℓ' (x +⁰ y))
    e = compEquiv (⊎-equiv (El⁰-lift-V⁰≃El⁰ ℓ' x) (El⁰-lift-V⁰≃El⁰ ℓ' y)) LiftEquiv

    elts : (c : El⁰ (lift-V⁰ ℓ' x +⁰ lift-V⁰ ℓ' y))
         → elements (lift-V⁰ ℓ' x +⁰ lift-V⁰ ℓ' y) c
           ≡ elements (lift-V⁰ ℓ' (x +⁰ y)) (e .fst c)
    elts (inl a) =
      cong₂ ⟨_,_⟩⁰ (sym (lift-V⁰-empty⁰ ℓ')) (elements-lift-V⁰ ℓ' x a)
      ∙ sym (lift-V⁰-orderedPair⁰ ℓ' empty⁰ (elements x (lowerEl⁰ ℓ' x a)))
    elts (inr b) =
      cong₂ ⟨_,_⟩⁰ (sym (lift-V⁰-unit⁰ ℓ')) (elements-lift-V⁰ ℓ' y b)
      ∙ sym (lift-V⁰-orderedPair⁰ ℓ' unit⁰ (elements y (lowerEl⁰ ℓ' y b)))

lift-V⁰-fiber⁰ : (ℓ' : Level) {x y : V⁰ {ℓ}} (f : El⁰ x → El⁰ y) (b : El⁰ y)
               → lift-V⁰ ℓ' (fiber⁰ {x = x} {y = y} f b)
                 ≡ fiber⁰ {x = lift-V⁰ ℓ' x} {y = lift-V⁰ ℓ' y}
                          (liftEl⁰ ℓ' y ∘ f ∘ lowerEl⁰ ℓ' x) (liftEl⁰ ℓ' y b)
lift-V⁰-fiber⁰ ℓ' {x} {y} f b =
  lift-V⁰-Σ⁰ ℓ' x (λ a → Id⁰ y (f a) b)
  ∙ cong (Σ⁰ (lift-V⁰ ℓ' x)) (funExt (λ a → lift-V⁰-Id⁰ ℓ' y (f (lowerEl⁰ ℓ' x a)) b))

-- raising commutes with the von Neumann natural numbers

lift-V⁰-suc⁰ : (ℓ' : Level) (x : V⁰ {ℓ}) → lift-V⁰ ℓ' (suc⁰ x) ≡ suc⁰ (lift-V⁰ ℓ' x)
lift-V⁰-suc⁰ {ℓ} ℓ' x@(sup-∞ A _ , _) =
  sym (V⁰-ext (suc⁰ (lift-V⁰ ℓ' x)) (lift-V⁰ ℓ' (suc⁰ x)) e elts)
  where
    e : (Lift ℓ' A ⊎ Unit* {ℓ-max ℓ ℓ'}) ≃ Lift ℓ' (A ⊎ Unit* {ℓ})
    e = compEquiv (⊎-equiv (invEquiv LiftEquiv) (Lift≃Lift (idEquiv Unit))) LiftEquiv

    elts : (c : Lift ℓ' A ⊎ Unit* {ℓ-max ℓ ℓ'})
         → elements (suc⁰ (lift-V⁰ ℓ' x)) c ≡ elements (lift-V⁰ ℓ' (suc⁰ x)) (e .fst c)
    elts (inl _) = refl
    elts (inr _) = refl

lift-V⁰-vonNeumannEncoding : (ℓ' : Level) (n : ℕ)
                           → lift-V⁰ ℓ' (vonNeumannEncoding {ℓ} (lift n))
                             ≡ vonNeumannEncoding {ℓ-max ℓ ℓ'} (lift n)
lift-V⁰-vonNeumannEncoding ℓ' zero = lift-V⁰-empty⁰ ℓ'
lift-V⁰-vonNeumannEncoding ℓ' (suc n) =
  lift-V⁰-suc⁰ ℓ' (vonNeumannEncoding (lift n)) ∙ cong suc⁰ (lift-V⁰-vonNeumannEncoding ℓ' n)

lift-V⁰-ℕ⁰ : (ℓ' : Level) → lift-V⁰ ℓ' (ℕ⁰ {ℓ}) ≡ ℕ⁰ {ℓ-max ℓ ℓ'}
lift-V⁰-ℕ⁰ {ℓ} ℓ' = sym (V⁰-ext ℕ⁰ (lift-V⁰ ℓ' ℕ⁰) e elts)
  where
    e : ℕ* {ℓ-max ℓ ℓ'} ≃ Lift ℓ' (ℕ* {ℓ})
    e = compEquiv (Lift≃Lift (idEquiv ℕ)) LiftEquiv

    elts : (n : ℕ* {ℓ-max ℓ ℓ'})
         → vonNeumannEncoding n ≡ lift-V⁰ ℓ' (vonNeumannEncoding {ℓ} (lift (n .lower)))
    elts (lift n) = sym (lift-V⁰-vonNeumannEncoding ℓ' n)

-- the universe is closed under the basic sets

empty⁰-∈⁰-universe⁰ : empty⁰ ∈⁰ universe⁰ {ℓ}
empty⁰-∈⁰-universe⁰ {ℓ} = empty⁰ , lift-V⁰-empty⁰ (ℓ-suc ℓ)

unit⁰-∈⁰-universe⁰ : unit⁰ ∈⁰ universe⁰ {ℓ}
unit⁰-∈⁰-universe⁰ {ℓ} = unit⁰ , lift-V⁰-unit⁰ (ℓ-suc ℓ)

bool⁰-∈⁰-universe⁰ : bool⁰ ∈⁰ universe⁰ {ℓ}
bool⁰-∈⁰-universe⁰ {ℓ} = bool⁰ , lift-V⁰-bool⁰ (ℓ-suc ℓ)

ℕ⁰-∈⁰-universe⁰ : ℕ⁰ ∈⁰ universe⁰ {ℓ}
ℕ⁰-∈⁰-universe⁰ {ℓ} = ℕ⁰ , lift-V⁰-ℕ⁰ (ℓ-suc ℓ)

singleton⁰-∈⁰-universe⁰ : {X : V⁰} → X ∈⁰ universe⁰ {ℓ} → singleton⁰ X ∈⁰ universe⁰
singleton⁰-∈⁰-universe⁰ {ℓ} (x , p) =
  singleton⁰ x , lift-V⁰-singleton⁰ (ℓ-suc ℓ) x ∙ cong singleton⁰ p

unorderedPair⁰-∈⁰-universe⁰ : {X Y : V⁰} (X≢Y : ¬ (X ≡ Y))
                            → X ∈⁰ universe⁰ {ℓ} → Y ∈⁰ universe⁰
                            → unorderedPair⁰ X Y X≢Y ∈⁰ universe⁰
unorderedPair⁰-∈⁰-universe⁰ {ℓ} X≢Y (x , p) (y , q) =
  unorderedPair⁰ x y x≢y , lift-V⁰-unorderedPair⁰ (ℓ-suc ℓ) x≢y ∙ unorderedPair⁰-cong p q
  where
    x≢y : ¬ (x ≡ y)
    x≢y r = X≢Y (sym p ∙ cong (lift-V⁰ (ℓ-suc ℓ)) r ∙ q)

orderedPair⁰-∈⁰-universe⁰ : {X Y : V⁰}
                          → X ∈⁰ universe⁰ {ℓ} → Y ∈⁰ universe⁰ → ⟨ X , Y ⟩⁰ ∈⁰ universe⁰
orderedPair⁰-∈⁰-universe⁰ {ℓ} (x , p) (y , q) =
  ⟨ x , y ⟩⁰ , lift-V⁰-orderedPair⁰ (ℓ-suc ℓ) x y ∙ cong₂ ⟨_,_⟩⁰ p q

-- the universe is closed under the type formers

+⁰-∈⁰-universe⁰ : {X Y : V⁰}
                → X ∈⁰ universe⁰ {ℓ} → Y ∈⁰ universe⁰ → (X +⁰ Y) ∈⁰ universe⁰
+⁰-∈⁰-universe⁰ {ℓ} (x , p) (y , q) = (x +⁰ y) , lift-V⁰-+⁰ (ℓ-suc ℓ) x y ∙ cong₂ _+⁰_ p q

Σ⁰-∈⁰-universe⁰ : {X : V⁰} {Y : El⁰ X → V⁰}
                → X ∈⁰ universe⁰ {ℓ} → ((a : El⁰ X) → Y a ∈⁰ universe⁰)
                → Σ⁰ X Y ∈⁰ universe⁰
Σ⁰-∈⁰-universe⁰ {ℓ} {Y = Y} (x , p) = subst P p (base x) Y
  where
    P : V⁰ {ℓ-suc ℓ} → Type (ℓ-suc (ℓ-suc ℓ))
    P Z = (Y : El⁰ Z → V⁰ {ℓ-suc ℓ}) → ((a : El⁰ Z) → Y a ∈⁰ universe⁰)
        → Σ⁰ Z Y ∈⁰ universe⁰

    base : (x : V⁰ {ℓ}) → P (lift-V⁰ (ℓ-suc ℓ) x)
    base x@(sup-∞ _ _ , _) Y hY =
      Σ⁰ x (λ a → hY (lift a) .fst) ,
      lift-V⁰-Σ⁰ (ℓ-suc ℓ) x (λ a → hY (lift a) .fst)
      ∙ cong (Σ⁰ (lift-V⁰ (ℓ-suc ℓ) x)) (funExt (λ a → hY a .snd))

Π⁰-∈⁰-universe⁰ : {X : V⁰} {Y : El⁰ X → V⁰}
                → X ∈⁰ universe⁰ {ℓ} → ((a : El⁰ X) → Y a ∈⁰ universe⁰)
                → Π⁰ X Y ∈⁰ universe⁰
Π⁰-∈⁰-universe⁰ {ℓ} {Y = Y} (x , p) = subst P p (base x) Y
  where
    P : V⁰ {ℓ-suc ℓ} → Type (ℓ-suc (ℓ-suc ℓ))
    P Z = (Y : El⁰ Z → V⁰ {ℓ-suc ℓ}) → ((a : El⁰ Z) → Y a ∈⁰ universe⁰)
        → Π⁰ Z Y ∈⁰ universe⁰

    base : (x : V⁰ {ℓ}) → P (lift-V⁰ (ℓ-suc ℓ) x)
    base x@(sup-∞ _ _ , _) Y hY =
      Π⁰ x (λ a → hY (lift a) .fst) ,
      lift-V⁰-Π⁰ (ℓ-suc ℓ) x (λ a → hY (lift a) .fst)
      ∙ cong (Π⁰ (lift-V⁰ (ℓ-suc ℓ) x)) (funExt (λ a → hY a .snd))

×⁰-∈⁰-universe⁰ : {X Y : V⁰}
                → X ∈⁰ universe⁰ {ℓ} → Y ∈⁰ universe⁰ → (X ×⁰ Y) ∈⁰ universe⁰
×⁰-∈⁰-universe⁰ hX hY = Σ⁰-∈⁰-universe⁰ hX (λ _ → hY)

→⁰-∈⁰-universe⁰ : {X Y : V⁰}
                → X ∈⁰ universe⁰ {ℓ} → Y ∈⁰ universe⁰ → (X →⁰ Y) ∈⁰ universe⁰
→⁰-∈⁰-universe⁰ hX hY = Π⁰-∈⁰-universe⁰ hX (λ _ → hY)

Id⁰-∈⁰-universe⁰ : {X : V⁰} (a b : El⁰ X)
                 → X ∈⁰ universe⁰ {ℓ} → Id⁰ X a b ∈⁰ universe⁰
Id⁰-∈⁰-universe⁰ {ℓ} a b (x , p) = subst P p (base x) a b
  where
    P : V⁰ {ℓ-suc ℓ} → Type (ℓ-suc (ℓ-suc ℓ))
    P Z = (a b : El⁰ Z) → Id⁰ Z a b ∈⁰ universe⁰

    base : (x : V⁰ {ℓ}) → P (lift-V⁰ (ℓ-suc ℓ) x)
    base x@(sup-∞ _ _ , _) a b =
      Id⁰ x (a .lower) (b .lower) , lift-V⁰-Id⁰ (ℓ-suc ℓ) x (a .lower) (b .lower)

fiber⁰-∈⁰-universe⁰ : {X Y : V⁰} (f : El⁰ X → El⁰ Y) (b : El⁰ Y)
                    → X ∈⁰ universe⁰ {ℓ} → Y ∈⁰ universe⁰ → fiber⁰ f b ∈⁰ universe⁰
fiber⁰-∈⁰-universe⁰ f b hX hY = Σ⁰-∈⁰-universe⁰ hX (λ a → Id⁰-∈⁰-universe⁰ (f a) b hY)
