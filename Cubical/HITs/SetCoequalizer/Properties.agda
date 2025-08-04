{-

This file contains:

- the coequalizer of sets as a HIT as performed in https://1lab.dev/Data.Set.Coequaliser.html

-}
module Cubical.HITs.SetCoequalizer.Properties where

open import Cubical.HITs.SetCoequalizer.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'

-- Some helpful lemmas, similar to those in Cubical/HITs/SetQuotients/Properties.agda
elimProp : {f g : A → B} {C : SetCoequalizer f g → Type ℓ}
         → (Cprop : (x : SetCoequalizer f g) → isProp (C x))
         → (Cinc : (b : B) → C (inc b))
         → (x : SetCoequalizer f g) → C x
elimProp Cprop Cinc (inc x) = Cinc x
elimProp {f = f} {g = g} Cprop Cinc (coeq a i) =
  isProp→PathP (λ i → Cprop (coeq a i)) (Cinc (f a)) (Cinc (g a)) i
elimProp Cprop Cinc (squash x y p q i j) =
  isOfHLevel→isOfHLevelDep
    2 (λ x → isProp→isSet (Cprop x)) (g x) (g y) (cong g p) (cong g q) (squash x y p q) i j
  where
  g = elimProp Cprop Cinc

elimProp2 : {A' : Type ℓ} {B' : Type ℓ'} {f g : A → B} {f' g' : A' → B'}
            {C : SetCoequalizer f g → SetCoequalizer f' g' → Type (ℓ-max ℓ ℓ')}
          → (Cprop : (x : SetCoequalizer f g) → (y : SetCoequalizer f' g') → isProp (C x y))
          → (Cinc : (b : B) → (b' : B') → C (inc b) (inc b'))
          → (x : SetCoequalizer f g) → (y : SetCoequalizer f' g') → C x y
elimProp2 Cprop Cinc = elimProp (λ x → isPropΠ (λ y → Cprop x y))
                                (λ x → elimProp (λ y → Cprop (inc x) y) (Cinc x))

elimProp3 : {A' A'' : Type ℓ} {B' B'' : Type ℓ'} {f g : A → B} {f' g' : A' → B'}
            {f'' g'' : A'' → B''}
            {C : SetCoequalizer f g → SetCoequalizer f' g' → SetCoequalizer f'' g''
               → Type (ℓ-max ℓ ℓ')}
          → (Cprop : (x : SetCoequalizer f g)
                   → (y : SetCoequalizer f' g')
                   → (z : SetCoequalizer f'' g'')
                   → isProp (C x y z))
          → (Cinc : (b : B) → (b' : B') → (b'' : B'') → C (inc b) (inc b') (inc b''))
          → (x : SetCoequalizer f g) → (y : SetCoequalizer f' g') → (z : SetCoequalizer f'' g'')
          → C x y z
elimProp3 Cprop Cinc = elimProp (λ x → isPropΠ2 (λ y z → Cprop x y z))
                                (λ x → elimProp2 (λ y z → Cprop (inc x) y z) (Cinc x))

rec : {C : Type ℓ''} {f g : A → B}
    → (Cset : (x y : C) → (p q : x ≡ y) → p ≡ q)
    → (h : B → C)
    → (hcoeqs : (a : A) → h (f a) ≡ h (g a))
    → SetCoequalizer f g → C
rec Cset h hcoeqs (inc x) = h x
rec Cset h hcoeqs (coeq a i) = hcoeqs a i
rec Cset h hcoeqs (squash x y p q i j) =
    Cset (g x) (g y) (λ i → g (p i)) (λ i → g (q i)) i j
  where g = rec Cset h hcoeqs

rec2 : {A' : Type ℓ} {B' : Type ℓ'} {C : Type ℓ''} {f g : A → B} {f' g' : A' → B'}
     → (Cset : (x y : C) → (p q : x ≡ y) → p ≡ q)
     → (h : B → B' → C)
     → (hcoeqsl : (a : A) (b' : B') → h (f a) b' ≡ h (g a) b')
     → (hcoeqsr : (a' : A') (b : B) → h b (f' a') ≡ h b (g' a'))
     → SetCoequalizer f g → SetCoequalizer f' g' → C
rec2 Cset h hcoeqsl hcoeqsr =
  rec
    (isSetΠ (λ _ → Cset))
    (λ b → rec Cset (λ b' → h b b') (λ a' → hcoeqsr a' b))
    (λ a → funExt (elimProp (λ _ → Cset _ _) (λ b' → hcoeqsl a b')))

module UniversalProperty where
  {- The proof of the universal property of the coequalizer of sets.

  A ==f=g==> B --inc--> SetCoequalizer f g
              \         .
                \       .
                  h   ∃! inducedHom
                    \   .
                      \ .
                        C
  commuting diagram
  -}
  inducedHom : {C : Type ℓ''} {f g : A → B}
             → (Cset : (x y : C) → (p q : x ≡ y) → p ≡ q)
             → (h : B → C)
             → (hcoeq : (a : A) → h (f a) ≡ h (g a))
             → SetCoequalizer f g → C
  inducedHom Cset h hcoeq = rec Cset h hcoeq

  commutativity : {C : Type ℓ''} {f g : A → B}
                → (Cset : (x y : C) → (p q : x ≡ y) → p ≡ q)
                → (h : B → C)
                → (hcoeq : (a : A) → h (f a) ≡ h (g a))
                → ((b : B) → h b ≡ inducedHom Cset h hcoeq (inc b))
  commutativity Cset h hcoeq = λ b → refl

  uniqueness : {C : Type ℓ''}
             → (f g : A → B)
             → (Cset : (x y : C) → (p q : x ≡ y) → p ≡ q)
             → (h : B → C)
             → (hcoeq : (a : A) → h (f a) ≡ h (g a))
             → (i : SetCoequalizer f g → C)
             → (icommutativity : (b : B) → h b ≡ i (inc b))
             → (i ≡ inducedHom Cset h hcoeq)
  uniqueness f g Cset h hcoeq i icommutativity = λ j x → q x j
    where q : (x : SetCoequalizer f g) → i x ≡ inducedHom Cset h hcoeq x
          q = elimProp
                (λ _ → Cset _ _)
                (λ b → i (inc b) ≡⟨ sym (icommutativity b) ⟩
                      h b       ≡⟨ refl ⟩
                      inducedHom Cset h hcoeq (inc b) ∎)
