{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Sets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Limits

open Category

module _ ℓ where
  SET : Category (ℓ-suc ℓ) ℓ
  ob SET = hSet ℓ
  Hom[_,_] SET (A , _) (B , _) = A → B
  id SET x = x
  _⋆_ SET f g x = g (f x)
  ⋆IdL SET f = refl
  ⋆IdR SET f = refl
  ⋆Assoc SET f g h = refl
  isSetHom SET {A} {B} = isSetΠ (λ _ → snd B)

private
  variable
    ℓ ℓ' : Level

open Functor

-- Hom functors
_[-,_] : (C : Category ℓ ℓ') → (c : C .ob) → Functor (C ^op) (SET ℓ')
(C [-, c ]) .F-ob x    = (C [ x , c ]) , C .isSetHom
(C [-, c ]) .F-hom f k = f ⋆⟨ C ⟩ k
(C [-, c ]) .F-id      = funExt λ _ → C .⋆IdL _
(C [-, c ]) .F-seq _ _ = funExt λ _ → C .⋆Assoc _ _ _

_[_,-] : (C : Category ℓ ℓ') → (c : C .ob)→ Functor C (SET ℓ')
(C [ c ,-]) .F-ob x    = (C [ c , x ]) , C .isSetHom
(C [ c ,-]) .F-hom f k = k ⋆⟨ C ⟩ f
(C [ c ,-]) .F-id      = funExt λ _ → C .⋆IdR _
(C [ c ,-]) .F-seq _ _ = funExt λ _ → sym (C .⋆Assoc _ _ _)

module _ {C : Category ℓ ℓ'} {F : Functor C (SET ℓ')} where
  open NatTrans

  -- natural transformations by pre/post composition
  preComp : {x y : C .ob}
          → (f : C [ x , y ])
          → C [ x ,-] ⇒ F
          → C [ y ,-] ⇒ F
  preComp f α .N-ob c k = (α ⟦ c ⟧) (f ⋆⟨ C ⟩ k)
  preComp f α .N-hom {x = c} {d} k
    = (λ l → (α ⟦ d ⟧) (f ⋆⟨ C ⟩ (l ⋆⟨ C ⟩ k)))
    ≡[ i ]⟨ (λ l → (α ⟦ d ⟧) (⋆Assoc C f l k (~ i))) ⟩
      (λ l → (α ⟦ d ⟧) (f ⋆⟨ C ⟩ l ⋆⟨ C ⟩ k))
    ≡[ i ]⟨ (λ l → (α .N-hom k) i (f ⋆⟨ C ⟩ l)) ⟩
      (λ l → (F ⟪ k ⟫) ((α ⟦ c ⟧) (f ⋆⟨ C ⟩ l)))
    ∎

-- properties
-- TODO: move to own file
open CatIso renaming (inv to cInv)
open Iso

Iso→CatIso : ∀ {A B : (SET ℓ) .ob}
           → Iso (fst A) (fst B)
           → CatIso (SET ℓ) A B
Iso→CatIso is .mor = is .fun
Iso→CatIso is .cInv = is .inv
Iso→CatIso is .sec = funExt λ b → is .rightInv b -- is .rightInv
Iso→CatIso is .ret = funExt λ b → is .leftInv b -- is .rightInv



-- SET is complete

-- notes:
-- didn't need to restrict to *finite* diagrams , why is that required in Set theoretic?
-- didn't use coinduction here because Agda didn't like me referencing 'cone' frome 'up' (termination check)

open NatTrans

isCompleteSET : ∀ {ℓJ ℓJ'} → complete' {ℓJ = ℓJ} {ℓJ'} (SET (ℓ-max ℓJ ℓJ'))
isCompleteSET J K = record
                  { head = head'
                  ; islim = record { cone = cone' ; up = up' } }
  where
    -- the limit is defined as the Set of all cones with head Unit
    head' = Cone K (Unit* , isOfHLevelLift 2 isSetUnit) , isSetNatTrans

    -- the legs are defined by taking a cone to its component at j
    cone' : Cone K head'
    cone' .N-ob j μ = (μ ⟦ j ⟧) tt*
    -- Naturality follows from naturality of the Unit cone
    cone' .N-hom {x = i} {j} f
      = funExt λ μ → (μ ⟦ j ⟧) tt*
        ≡[ i ]⟨ (μ .N-hom f i) tt* ⟩
          (K ⟪ f ⟫) ((μ ⟦ i ⟧) tt*)
        ∎

    -- Given another cone α, we want a unique function f from α → cone' which factors it
    -- factorization property enforces that (cone' ⟦ j ⟧ ● f) ≡ α ⟦ j ⟧
    -- but cone' ⟦ j ⟧ simply takes the jth component the output Cone K Unit from f
    -- so this enforces that for all x ∈ A, (f x) ⟦ j ⟧ ≡ α ⟦ j ⟧ x
    -- this determines the *only* possible factoring morphism
    up' : ∀ {A} (α : Cone K A) → cone' uniquelyFactors α
    up' {A} α = (f , fact) , unique
      where
        f : fst A → Cone K (Unit* , isOfHLevelLift 2 isSetUnit)
        f x = natTrans (λ j _ → α .N-ob j x)
                       (λ {m} {n} f → funExt λ μ i → α .N-hom f i x)

        fact : α ≡ (f ◼ cone')
        fact = makeNatTransPath refl -- I LOVE DEFINITIONAL EQUALITY

        unique : (τ : cone' factors α) → (f , fact) ≡ τ
        unique (f' , fact') = ΣPathP (f≡f' , fact≡fact')
          where
            f≡f' : f ≡ f'
            f≡f' = funExt λ x → makeNatTransPath (funExt λ _ → sym eq2)
              where
                -- the factorization property enforces that f' must have the same behavior as f
                eq1 : ∀ {x j} → ((cone' ⟦ j ⟧) (f' x)) ≡ (α ⟦ j ⟧) x
                eq1 {x} {j} i = ((fact' (~ i)) ⟦ j ⟧) x

                eq2 : ∀ {x j} → (f' x) ⟦ j ⟧ ≡ λ _ → (α ⟦ j ⟧) x -- = (f x) ⟦ j ⟧
                eq2 {x} {j} = funExt λ _ → eq1

            -- follows from Set having homsets
            fact≡fact' : PathP (λ i → α ≡ ((f≡f' i) ◼ cone')) fact fact'
            fact≡fact' = isOfHLevel→isOfHLevelDep 1 (λ β → isSetNatTrans α β) fact fact' λ i → (f≡f' i) ◼ cone'
