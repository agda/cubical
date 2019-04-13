{-# OPTIONS --cubical --safe #-}

module Cubical.Foundations.Embedding where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism

private
  variable
    ℓ : Level
    A B : Set ℓ
    f : A → B
    w x : A
    y z : B

isEmbedding : (A → B) → Set _
isEmbedding f = ∀ w x → isEquiv {A = w ≡ x} (cong f)

isEmbeddingIsProp : isProp (isEmbedding f)
isEmbeddingIsProp {f = f}
  = propPi λ w → propPi λ x → isPropIsEquiv (cong f)

injEmbedding
  : {f : A → B}
  → isSet A → isSet B
  → (∀{w x} → f w ≡ f x → w ≡ x)
  → isEmbedding f
injEmbedding {f = f} iSA iSB inj w x
  = isoToIsEquiv (iso (cong f) inj sect retr)
  where
  sect : section (cong f) inj
  sect p = iSB (f w) (f x) _ p

  retr : retract (cong f) inj
  retr p = iSA w x _ p

private
  lemma₀ : (p : y ≡ z) → fiber f y ≡ fiber f z
  lemma₀ {f = f} p = λ i → fiber f (p i)

  lemma₁ : isEmbedding f → ∀ x → isContr (fiber f (f x))
  lemma₁ {f = f} iE x = value , path
    where
    value : fiber f (f x)
    value = (x , refl)

    path : ∀(fi : fiber f (f x)) → value ≡ fi
    path (w , p) i
      = case equiv-proof (iE w x) p of λ
      { ((q , sq) , _)
      → hfill (λ j → λ { (i = i0) → (x , refl)
                      ; (i = i1) → (w , sq j)
                      })
          (inS (q (~ i) , λ j → f (q (~ i ∨ j))))
          i1
      }

isEmbedding→isPropFiber : isEmbedding f → ∀ y → isProp (fiber f y)
isEmbedding→isPropFiber iE y (x , p)
  = subst (λ f → isProp f) (lemma₀ p) (isContr→isProp (lemma₁ iE x)) (x , p)

private
  lemma₂
    : (p : f w ≡ f x)
    → (∀ f₁ f₂ → PathP (λ i → fiber f (p i)) f₁ f₂)
    → fiber (cong f) p
  lemma₂ {f = f} {w} {x} p aP = invert , inverse
    where
    fw : fiber f (f w)
    fw = (w , refl)

    fx : fiber f (f x)
    fx = (x , refl)

    fp = aP fw fx

    invert : w ≡ x
    invert i = fst (fp i)

    inverse : cong f invert ≡ p
    inverse j i = snd (fp i) j
