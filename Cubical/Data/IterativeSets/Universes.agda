-- The code for the universe of ℓ-small iterative sets, i.e. the set of all raised ℓ-small sets
-- (Proposition 33 of https://doi.org/10.1017/S0960129524000288)
-- `opaque` is used in two places, as unfolding these proofs is very expensive

module Cubical.Data.IterativeSets.Universes where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Embedding

open import Cubical.Data.IterativeMultisets.Base using (V∞ ; sup-∞ ; lift-V∞)
open import Cubical.Data.IterativeMultisets.Properties using (lift-V∞-inj)
open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ ℓ' : Level

private
  opaque
    isEmbedding-lift-elements : (ℓ' : Level) {A : Type ℓ} (α : A → V∞ {ℓ}) → isEmbedding α
      → ((a : A) → isIterativeSet (lift-V∞ ℓ' (α a)))
      → isEmbedding (λ (a : Lift ℓ' A) → lift-V∞ ℓ' (α (a .lower)))
    isEmbedding-lift-elements {ℓ} ℓ' {A} α isEmbα its =
      isEmbedding-∘ (V⁰↪V∞ .snd) (injEmbedding isSetV⁰ inj)
      where
        α' : Lift ℓ' A → V⁰ {ℓ-max ℓ ℓ'}
        α' a .fst = lift-V∞ ℓ' (α (a .lower))
        α' a .snd = its (a .lower)

        inj : {a b : Lift ℓ' A} → α' a ≡ α' b → a ≡ b
        inj {a} {b} p = liftExt (isEmbedding→Inj isEmbα (a .lower) (b .lower)
          (lift-V∞-inj ℓ' (α (a .lower)) (α (b .lower)) (cong fst p)))

  isIterativeSet-lift-V∞ : (ℓ' : Level) (x : V∞ {ℓ})
                         → isIterativeSet x → isIterativeSet (lift-V∞ ℓ' x)
  isIterativeSet-lift-V∞ ℓ' (sup-∞ A α) (isEmbα , itsα) .fst =
    isEmbedding-lift-elements ℓ' α isEmbα (λ a → isIterativeSet-lift-V∞ ℓ' (α a) (itsα a))
  isIterativeSet-lift-V∞ ℓ' (sup-∞ A α) (_ , itsα) .snd a =
    isIterativeSet-lift-V∞ ℓ' (α (a .lower)) (itsα (a .lower))

lift-V⁰ : (ℓ' : Level) → V⁰ {ℓ} → V⁰ {ℓ-max ℓ ℓ'}
lift-V⁰ ℓ' x .fst = lift-V∞ ℓ' (x .fst)
lift-V⁰ ℓ' x .snd = isIterativeSet-lift-V∞ ℓ' (x .fst) (x .snd)

opaque
  lift-V⁰-inj : (ℓ' : Level) {x y : V⁰ {ℓ}} → lift-V⁰ ℓ' x ≡ lift-V⁰ ℓ' y → x ≡ y
  lift-V⁰-inj ℓ' {x} {y} p =
    invEq ≡V⁰-≃-≡V∞ (lift-V∞-inj ℓ' (x .fst) (y .fst) (cong fst p))

  isEmbedding-lift-V⁰ : (ℓ' : Level) → isEmbedding (lift-V⁰ {ℓ} ℓ')
  isEmbedding-lift-V⁰ ℓ' = injEmbedding isSetV⁰ (lift-V⁰-inj ℓ')

-- the elements of a raised set

El⁰lift-V⁰IsLift : (ℓ' : Level) (x : V⁰ {ℓ}) → El⁰ (lift-V⁰ ℓ' x) ≡ Lift ℓ' (El⁰ x)
El⁰lift-V⁰IsLift ℓ' (sup-∞ _ _ , _) = refl

El⁰-lift-V⁰≃El⁰ : (ℓ' : Level) (x : V⁰ {ℓ}) → El⁰ (lift-V⁰ ℓ' x) ≃ El⁰ x
El⁰-lift-V⁰≃El⁰ ℓ' (sup-∞ _ _ , _) = invEquiv LiftEquiv

lowerEl⁰ : (ℓ' : Level) (x : V⁰ {ℓ}) → El⁰ (lift-V⁰ ℓ' x) → El⁰ x
lowerEl⁰ ℓ' x = equivFun (El⁰-lift-V⁰≃El⁰ ℓ' x)

liftEl⁰ : (ℓ' : Level) (x : V⁰ {ℓ}) → El⁰ x → El⁰ (lift-V⁰ ℓ' x)
liftEl⁰ ℓ' x = invEq (El⁰-lift-V⁰≃El⁰ ℓ' x)

elements-lift-V⁰ : (ℓ' : Level) (x : V⁰ {ℓ}) (a : El⁰ (lift-V⁰ ℓ' x))
                 → elements (lift-V⁰ ℓ' x) a ≡ lift-V⁰ ℓ' (elements x (lowerEl⁰ ℓ' x a))
elements-lift-V⁰ ℓ' (sup-∞ _ _ , _) _ = refl

-- the code for the universe

universe⁰ : V⁰ {ℓ-suc ℓ}
universe⁰ {ℓ} = fromEmb (V⁰ {ℓ} , lift-V⁰ (ℓ-suc ℓ) , isEmbedding-lift-V⁰ (ℓ-suc ℓ))

El⁰universe⁰IsV⁰ : El⁰ (universe⁰ {ℓ}) ≡ V⁰ {ℓ}
El⁰universe⁰IsV⁰ = refl

∈universe⁰-≃ : {z : V⁰ {ℓ-suc ℓ}} → (z ∈⁰ universe⁰) ≃ fiber (lift-V⁰ {ℓ} (ℓ-suc ℓ)) z
∈universe⁰-≃ = idEquiv _
