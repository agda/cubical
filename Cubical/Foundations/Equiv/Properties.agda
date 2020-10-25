{-

A couple of general facts about equivalences:

- if f is an equivalence then (cong f) is an equivalence ([equivCong])
- if f is an equivalence then pre- and postcomposition with f are equivalences ([preCompEquiv], [postCompEquiv])
- if f is an equivalence then (Σ[ g ] section f g) and (Σ[ g ] retract f g) are contractible ([isContr-section], [isContr-retract])

- isHAEquiv is a proposition [isPropIsHAEquiv]
(these are not in 'Equiv.agda' because they need Univalence.agda (which imports Equiv.agda))
-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.Equiv.Properties where

open import Cubical.Core.Everything

open import Cubical.Data.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels

open import Cubical.Functions.FunExtEquiv

private
  variable
    ℓ ℓ′ : Level
    A B C : Type ℓ

isEquivInvEquiv : isEquiv (λ (e : A ≃ B) → invEquiv e)
isEquivInvEquiv = isoToIsEquiv goal where
  open Iso
  goal : Iso (A ≃ B) (B ≃ A)
  goal .fun = invEquiv
  goal .inv = invEquiv
  goal .rightInv g = equivEq refl
  goal .leftInv f = equivEq refl

invEquivEquiv : (A ≃ B) ≃ (B ≃ A)
invEquivEquiv = _ , isEquivInvEquiv

isEquivCong : {x y : A} (e : A ≃ B) → isEquiv (λ (p : x ≡ y) → cong (equivFun e) p)
isEquivCong e = isoToIsEquiv (congIso (equivToIso e))

congEquiv : {x y : A} (e : A ≃ B) → (x ≡ y) ≃ (equivFun e x ≡ equivFun e y)
congEquiv e = isoToEquiv (congIso (equivToIso e))

equivAdjointEquiv : (e : A ≃ B) → ∀ {a b} → (a ≡ invEq e b) ≃ (equivFun e a ≡ b)
equivAdjointEquiv e = compEquiv (congEquiv e) (compPathrEquiv (retEq e _))

invEq≡→equivFun≡ : (e : A ≃ B) → ∀ {a b} → invEq e b ≡ a → equivFun e a ≡ b
invEq≡→equivFun≡ e = equivFun (equivAdjointEquiv e) ∘ sym

isEquivPreComp : (e : A ≃ B) → isEquiv (λ (φ : B → C) → φ ∘ equivFun e)
isEquivPreComp e = snd (equiv→ (invEquiv e) (idEquiv _))

preCompEquiv : (e : A ≃ B) → (B → C) ≃ (A → C)
preCompEquiv e = (λ φ → φ ∘ fst e) , isEquivPreComp e

isEquivPostComp : (e : A ≃ B) → isEquiv (λ (φ : C → A) → e .fst ∘ φ)
isEquivPostComp e = snd (equivΠCod (λ _ → e))

postCompEquiv : (e : A ≃ B) → (C → A) ≃ (C → B)
postCompEquiv e = _ , isEquivPostComp e

-- see also: equivΠCod for a dependent version of postCompEquiv

hasSection : (A → B) → Type _
hasSection {A = A} {B = B} f = Σ[ g ∈ (B → A) ] section f g

hasRetract : (A → B) → Type _
hasRetract {A = A} {B = B} f = Σ[ g ∈ (B → A) ] retract f g

isEquiv→isContrHasSection : {f : A → B} → isEquiv f → isContr (hasSection f)
fst (isEquiv→isContrHasSection isEq) = invIsEq isEq , secIsEq isEq
snd (isEquiv→isContrHasSection isEq) (f , ε) i = (λ b → fst (p b i)) , (λ b → snd (p b i))
  where p : ∀ b → (invIsEq isEq b , secIsEq isEq b) ≡ (f b , ε b)
        p b = isEq .equiv-proof b .snd (f b , ε b)

isEquiv→hasSection : {f : A → B} → isEquiv f → hasSection f
isEquiv→hasSection = fst ∘ isEquiv→isContrHasSection

isContr-hasSection : (e : A ≃ B) → isContr (hasSection (fst e))
isContr-hasSection e = isEquiv→isContrHasSection (snd e)

isEquiv→isContrHasRetract : {f : A → B} → isEquiv f → isContr (hasRetract f)
fst (isEquiv→isContrHasRetract isEq) = invIsEq isEq , retIsEq isEq
snd (isEquiv→isContrHasRetract {f = f} isEq) (g , η) =
    λ i → (λ b → p b i) , (λ a →  q a i)
  where p : ∀ b → invIsEq isEq b ≡ g b
        p b = sym (η (invIsEq isEq b)) ∙' cong g (secIsEq isEq b)
        -- one square from the definition of invIsEq
        ieSq : ∀ a → Square (cong g (secIsEq isEq (f a)))
                            refl
                            (cong (g ∘ f) (retIsEq isEq a))
                            refl
        ieSq a k j = g (commSqIsEq isEq a k j)
        -- one square from η
        ηSq : ∀ a → Square (η (invIsEq isEq (f a)))
                           (η a)
                           (cong (g ∘ f) (retIsEq isEq a))
                           (retIsEq isEq a)
        ηSq a i j = η (retIsEq isEq a i) j
        -- and one last square from the definition of p
        pSq : ∀ b → Square (η (invIsEq isEq b))
                           refl
                           (cong g (secIsEq isEq b))
                           (p b)
        pSq b i j = compPath'-filler (sym (η (invIsEq isEq b))) (cong g (secIsEq isEq b)) j i
        q : ∀ a → Square (retIsEq isEq a) (η a) (p (f a)) refl
        q a i j = hcomp (λ k → λ { (i = i0) → ηSq a j k
                                 ; (i = i1) → η a (j ∧ k)
                                 ; (j = i0) → pSq (f a) i k
                                 ; (j = i1) → η a k
                                 })
                        (ieSq a j i)

isEquiv→hasRetract : {f : A → B} → isEquiv f → hasRetract f
isEquiv→hasRetract = fst ∘ isEquiv→isContrHasRetract

isContr-hasRetract : (e : A ≃ B) → isContr (hasRetract (fst e))
isContr-hasRetract e = isEquiv→isContrHasRetract (snd e)

cong≃ : (F : Type ℓ → Type ℓ′) → (A ≃ B) → F A ≃ F B
cong≃ F e = pathToEquiv (cong F (ua e))

cong≃-char : (F : Type ℓ → Type ℓ′) {A B : Type ℓ} (e : A ≃ B) → ua (cong≃ F e) ≡ cong F (ua e)
cong≃-char F e = ua-pathToEquiv (cong F (ua e))

cong≃-idEquiv : (F : Type ℓ → Type ℓ′) (A : Type ℓ) → cong≃ F (idEquiv A) ≡ idEquiv (F A)
cong≃-idEquiv F A = cong≃ F (idEquiv A) ≡⟨ cong (λ p → pathToEquiv (cong F p)) uaIdEquiv  ⟩
                    pathToEquiv refl    ≡⟨ pathToEquivRefl ⟩
                    idEquiv (F A)       ∎

isPropIsHAEquiv : {f : A → B} → isProp (isHAEquiv f)
isPropIsHAEquiv {f = f} ishaef = goal ishaef where
  equivF : isEquiv f
  equivF = isHAEquiv→isEquiv ishaef

  rCoh1 : (sec : hasSection f) → Type _
  rCoh1 (g , ε) = Σ[ η ∈ retract f g ] ∀ x → cong f (η x) ≡ ε (f x)

  rCoh2 : (sec : hasSection f) → Type _
  rCoh2 (g , ε) = Σ[ η ∈ retract f g ] ∀ x → Square (ε (f x)) refl (cong f (η x)) refl

  rCoh3 : (sec : hasSection f) → Type _
  rCoh3 (g , ε) = ∀ x → Σ[ ηx ∈ g (f x) ≡ x ] Square (ε (f x)) refl (cong f ηx) refl

  rCoh4 : (sec : hasSection f) → Type _
  rCoh4 (g , ε) = ∀ x → Path (fiber f (f x)) (g (f x) , ε (f x)) (x , refl)

  characterization : isHAEquiv f ≃ Σ _ rCoh4
  characterization =
    isHAEquiv f
      -- first convert between Σ and record
      ≃⟨ isoToEquiv (iso (λ e → (e .g , e .rinv) , (e .linv , e .com))
                         (λ e → record { g = e .fst .fst ; rinv = e .fst .snd
                                       ; linv = e .snd .fst ; com = e .snd .snd })
                         (λ _ → refl) λ _ → refl) ⟩
    Σ _ rCoh1
      -- secondly, convert the path into a dependent path for later convenience
      ≃⟨  Σ-cong-equiv-snd (λ s → Σ-cong-equiv-snd
                             λ η → equivΠCod
                               λ x → compEquiv (flipSquareEquiv {a₀₀ = f x}) (invEquiv slideSquareEquiv)) ⟩
    Σ _ rCoh2
      ≃⟨ Σ-cong-equiv-snd (λ s → invEquiv Σ-Π-≃) ⟩
    Σ _ rCoh3
      ≃⟨ Σ-cong-equiv-snd (λ s → equivΠCod λ x → ΣPath≃PathΣ) ⟩
    Σ _ rCoh4
      ■
    where open isHAEquiv

  goal : isProp (isHAEquiv f)
  goal = subst isProp (sym (ua characterization))
    (isPropΣ (isContr→isProp (isEquiv→isContrHasSection equivF))
             λ s → isPropΠ λ x → isProp→isSet (isContr→isProp (equivF .equiv-proof (f x))) _ _)

-- composition on the right induces an equivalence of path types
compr≡Equiv : {A : Type ℓ} {a b c : A} (p q : a ≡ b) (r : b ≡ c) → (p ≡ q) ≃ (p ∙ r ≡ q ∙ r)
compr≡Equiv p q r = congEquiv ((λ s → s ∙ r) , compPathr-isEquiv r)

-- composition on the left induces an equivalence of path types
compl≡Equiv : {A : Type ℓ} {a b c : A} (p : a ≡ b) (q r : b ≡ c) → (q ≡ r) ≃ (p ∙ q ≡ p ∙ r)
compl≡Equiv p q r = congEquiv ((λ s → p ∙ s) , (compPathl-isEquiv p))
