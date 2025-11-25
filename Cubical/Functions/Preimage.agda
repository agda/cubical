module Cubical.Functions.Preimage where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Powerset

open import Cubical.Functions.Embedding
open import Cubical.Functions.Image
open import Cubical.Functions.Surjection

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as ∥₁

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ

module _ (f : A → B)
         ((S , (g , emb)) : Embedding B ℓ')
         where
           isInPreimage : A → Type _
           isInPreimage x = isInImage g (f x)

           isPropIsInPreimage : ∀ x → isProp (isInPreimage x)
           isPropIsInPreimage x = isPropIsInImage g (f x)

           Preimage : Type _
           Preimage = Σ[ x ∈ A ] isInPreimage x

           preimageInclusion : Preimage ↪ A
           preimageInclusion = EmbeddingΣProp isPropIsInPreimage

           restrictToPreimage : Preimage → S
           restrictToPreimage (x , im) = lemma (f x) im .fst
             where lemma : ∀ y → isInImage g y
                         → fiber g y
                   lemma y = ∥₁.rec (isEmbedding→hasPropFibers emb y) λ fib → fib

-- Some notation
_⃖_ : (A → B) → (Embedding B ℓ') → Embedding A _
f ⃖ S = Preimage f S , preimageInclusion f S

PreimageOfImage : {A B : Type ℓ}
                  (f : A → B)
                → Preimage f (Image f , imageInclusion f) ≡ A
PreimageOfImage {A = A} {B = B} f = isoToPath is
  where is : Iso (Preimage f (Image f , imageInclusion f)) A
        Iso.fun is = fst
        Iso.inv is a = a , ∣ ((f a) , ∣ a , refl ∣₁) , refl ∣₁
        Iso.rightInv is x = refl
        Iso.leftInv is  x = Σ≡Prop (isPropIsInPreimage f (Image f , imageInclusion f)) refl
