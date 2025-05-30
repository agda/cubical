{-# OPTIONS --safe #-}

module Cubical.Algebra.DistributiveLaw.Base where

open import Cubical.Foundations.Prelude

private
  variable
    ℓs ℓp ℓt ℓr ℓq : Level

-- ⟨_,_⟩ notation - extremely dependent function pairing
[_,_,_]⟨_,_⟩ : {S : Type ℓs} {T : Type ℓt} {R : Type ℓr}
               (P : S → Type ℓp) (Q : T → Type ℓq) (s : S) (f : P s → T)
               (g : (Σ[ p ∈ P s ] Q (f p)) → R) (x : P s) → Σ[ t ∈ T ] (Q t → R)
[ P , Q , s ]⟨ f , g ⟩ x = (f x , λ y → g (x , y))

-- A curried version of the above (i.e. where the second function can be curried)
[_,_,_]⟨_,_⟩' : {S : Type ℓs} {T : Type ℓt} {R : Type ℓr} (P : S → Type ℓp)
                (Q : T → Type ℓq) (s : S) (f : P s → T) (g : (p : P s) → Q (f p) → R) (x : P s) →
                Σ[ t ∈ T ] (Q t → R)
[ P , Q , s ]⟨ f , g ⟩' x = (f x , g x)
