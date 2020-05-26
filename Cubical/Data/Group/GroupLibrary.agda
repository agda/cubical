{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Group.GroupLibrary where

open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Data.Group.Base
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Cubical.HITs.PropositionalTruncation hiding (map)

import Cubical.Foundations.Isomorphism as I
import Cubical.Foundations.Equiv as E
import Cubical.Foundations.Equiv.HalfAdjoint as HAE

open import Cubical.HITs.SetQuotients as sq


-- imGroup : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → morph G H
--         → Group (ℓ-max ℓ ℓ')
-- Group.type (imGroup G H (ϕ , mf)) = Σ[ x ∈ Group.type H ] isInIm G H ϕ x
-- Group.setStruc (imGroup G H (ϕ , mf)) = isOfHLevelΣ 2 (Group.setStruc H) λ _ → isOfHLevelSuc 1 propTruncIsProp
-- isGroup.id (Group.groupStruc (imGroup G H (ϕ , mf))) =
--  let idH = isGroup.id (Group.groupStruc H)
--      idG = isGroup.id (Group.groupStruc G)
--      invG = isGroup.inv (Group.groupStruc G)
--      invH = isGroup.inv (Group.groupStruc H)
--      lUnit = isGroup.lUnit (Group.groupStruc H)
--      rCancel = isGroup.rCancel (Group.groupStruc H)
--  in idH , ∣ idG , morph0→0 G H ϕ mf ∣
-- isGroup.inv (Group.groupStruc (imGroup G H (ϕ , mf))) (h , hinim) =
--   let idH = isGroup.id (Group.groupStruc H)
--       idG = isGroup.id (Group.groupStruc G)
--       invG = isGroup.inv (Group.groupStruc G)
--       invH = isGroup.inv (Group.groupStruc H)
--       lUnit = isGroup.lUnit (Group.groupStruc H)
--       rCancel = isGroup.rCancel (Group.groupStruc H)
--   in invH h , rec propTruncIsProp
--                   (λ a → ∣ (invG (fst a))
--                           , morphMinus G H ϕ mf (fst a) ∙ cong (λ x → invH x) (snd a) ∣)
--                   hinim
-- isGroup.comp (Group.groupStruc (imGroup G H (ϕ , mf))) (h1 , h1inim) (h2 , h2inim) =
--  let idH = isGroup.id (Group.groupStruc H)
--      idG = isGroup.id (Group.groupStruc G)
--      invG = isGroup.inv (Group.groupStruc G)
--      invH = isGroup.inv (Group.groupStruc H)
--      compH = isGroup.comp (Group.groupStruc H)
--      compG = isGroup.comp (Group.groupStruc G)
--      lUnit = isGroup.lUnit (Group.groupStruc H)
--      rCancel = isGroup.rCancel (Group.groupStruc H)
--  in compH h1 h2 , rec propTruncIsProp
--                       (λ p1 → rec propTruncIsProp
--                                   (λ p2 → ∣ (compG (fst p1) (fst p2))
--                                           , mf (fst p1) (fst p2) ∙ cong₂ compH (snd p1) (snd p2) ∣)
--                                    h2inim)
--                       h1inim
-- isGroup.lUnit (Group.groupStruc (imGroup G H (ϕ , mf))) (h , _) =
--  let lUnit = isGroup.lUnit (Group.groupStruc H)
--  in ΣProp≡ (λ _ → propTruncIsProp)
--            (lUnit h)
-- isGroup.rUnit (Group.groupStruc (imGroup G H (ϕ , mf))) (h , _) =
--  let rUnit = isGroup.rUnit (Group.groupStruc H)
--  in ΣProp≡ (λ _ → propTruncIsProp)
--            (rUnit h)
-- isGroup.assoc (Group.groupStruc (imGroup G H (ϕ , mf))) (h1 , _) (h2 , _) (h3 , _) =
--  let assoc = isGroup.assoc (Group.groupStruc H)
--  in ΣProp≡ (λ _ → propTruncIsProp)
--            (assoc h1 h2 h3)
-- isGroup.lCancel (Group.groupStruc (imGroup G H (ϕ , mf))) (h , _) =
--  let lCancel = isGroup.lCancel (Group.groupStruc H)
--  in ΣProp≡ (λ _ → propTruncIsProp)
--            (lCancel h)
-- isGroup.rCancel (Group.groupStruc (imGroup G H (ϕ , mf))) (h , _) =
--  let rCancel = isGroup.rCancel (Group.groupStruc H)
--  in ΣProp≡ (λ _ → propTruncIsProp)
--            (rCancel h)


-- kerGroup : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → morph G H
--         → Group (ℓ-max ℓ ℓ')
-- Group.type (kerGroup G H (ϕ , pf)) = Σ[ x ∈ Group.type G ] isInKer G H ϕ x
-- Group.setStruc (kerGroup G H (ϕ , pf)) = isOfHLevelΣ 2 (Group.setStruc G) λ _ → isOfHLevelPath 2 (Group.setStruc H) _ _
-- isGroup.id (Group.groupStruc (kerGroup G H (ϕ , pf))) = isGroup.id (Group.groupStruc G) , morph0→0 G H ϕ pf
-- isGroup.inv (Group.groupStruc (kerGroup G H (ϕ , pf))) (g , inker) =
--   let
--   idH = isGroup.id (Group.groupStruc H)
--   invG = isGroup.inv (Group.groupStruc G)
--   invH = isGroup.inv (Group.groupStruc H)
--   lUnit = isGroup.lUnit (Group.groupStruc H)
--   rCancel = isGroup.rCancel (Group.groupStruc H)
--   in invG g , morphMinus G H ϕ pf g ∙ cong (λ f → invH f) inker ∙ sym (lUnit (invH idH))  ∙ rCancel idH
-- isGroup.comp (Group.groupStruc (kerGroup G H (ϕ , pf))) (g1 , inkerg1) (g2 , inkerg2) =
--   let
--   idH = isGroup.id (Group.groupStruc H)
--   compG = isGroup.comp (Group.groupStruc G)
--   compH = isGroup.comp (Group.groupStruc H)
--   lUnit = isGroup.lUnit (Group.groupStruc H)
--   in (compG g1 g2) , pf g1 g2 ∙ (λ i → compH (inkerg1 i) (inkerg2 i)) ∙ lUnit idH
-- isGroup.lUnit (Group.groupStruc (kerGroup G H (ϕ , pf))) (g , _) =
--   let lUnit = isGroup.lUnit (Group.groupStruc G)
--   in ΣProp≡ (λ _ → isOfHLevelPath' 1 (Group.setStruc H) _ _) (lUnit g)
-- isGroup.rUnit (Group.groupStruc (kerGroup G H (ϕ , pf))) (g , _) =
--   let rUnit = isGroup.rUnit (Group.groupStruc G)
--   in ΣProp≡ (λ _ → isOfHLevelPath' 1 (Group.setStruc H) _ _) (rUnit g)
-- isGroup.assoc (Group.groupStruc (kerGroup G H (ϕ , pf))) (g1 , _) (g2 , _) (g3 , _) =
--   let assoc = isGroup.assoc (Group.groupStruc G)
--   in ΣProp≡ (λ _ → isOfHLevelPath' 1 (Group.setStruc H) _ _) (assoc g1 g2 g3)
-- isGroup.lCancel (Group.groupStruc (kerGroup G H (ϕ , pf))) (g1 , _) =
--   let lCancel = isGroup.lCancel (Group.groupStruc G)
--   in ΣProp≡ (λ _ → isOfHLevelPath' 1 (Group.setStruc H) _ _) (lCancel g1)
-- isGroup.rCancel (Group.groupStruc (kerGroup G H (ϕ , pf))) (g1 , _) =
--   let rCancel = isGroup.rCancel (Group.groupStruc G)
--   in ΣProp≡ (λ _ → isOfHLevelPath' 1 (Group.setStruc H) _ _) (rCancel g1)

open import Cubical.Data.Unit

trivialGroup : Group ℓ-zero
Group.type trivialGroup = Unit
Group.setStruc trivialGroup = isOfHLevelSuc 1 isPropUnit
isGroup.id (Group.groupStruc trivialGroup) = tt
isGroup.inv (Group.groupStruc trivialGroup) = λ _ → tt
isGroup.comp (Group.groupStruc trivialGroup) = λ _ _ → tt
isGroup.lUnit (Group.groupStruc trivialGroup) = λ _ → refl
isGroup.rUnit (Group.groupStruc trivialGroup) = λ _ → refl
isGroup.assoc (Group.groupStruc trivialGroup) = λ _ _ _ → refl
isGroup.lCancel (Group.groupStruc trivialGroup) = λ _ → refl
isGroup.rCancel (Group.groupStruc trivialGroup) = λ _ → refl

open import Cubical.Data.Int 

intGroup : Group ℓ-zero
Group.type intGroup = Int
Group.setStruc intGroup = isSetInt
isGroup.id (Group.groupStruc intGroup) = pos 0
isGroup.inv (Group.groupStruc intGroup) = pos 0 -_
isGroup.comp (Group.groupStruc intGroup) = _+_
isGroup.lUnit (Group.groupStruc intGroup) = λ a → +-comm (pos 0) a
isGroup.rUnit (Group.groupStruc intGroup) = λ _ → refl
isGroup.assoc (Group.groupStruc intGroup) = λ a b c → sym (+-assoc a b c)
isGroup.lCancel (Group.groupStruc intGroup) = λ a → minusPlus a 0
isGroup.rCancel (Group.groupStruc intGroup) = λ a → +-comm a (pos 0 - a) ∙ minusPlus a 0



-- Short exact sequences without req for first group to be definitionally equal to the trivial group --
record SES {ℓ ℓ' ℓ'' ℓ'''} (A : Group ℓ) (B : Group ℓ') (leftGr : Group ℓ'') (rightGr : Group ℓ''') : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' ℓ''')))) where
  constructor ses
  field
    isTrivialLeft : Iso leftGr trivialGroup
    isTrivialRight : Iso rightGr trivialGroup

    left : morph leftGr A
    right : morph B rightGr
    ϕ : morph A B
    
    Ker-ϕ⊂Im-left : (x : Group.type A) --
                  → isInKer A B (fst ϕ) x
                  → isInIm leftGr A (fst left) x
    Ker-right⊂Im-ϕ : (x : Group.type B) --
                   → isInKer B rightGr (fst right) x
                   → isInIm A B (fst ϕ) x

SES→inj-surj-morph : ∀ {ℓ ℓ' ℓ'' ℓ'''} (A : Group ℓ) (B : Group ℓ') (leftGr : Group ℓ'') (rightGr : Group ℓ''')
                   → SES A B leftGr rightGr
                   → inj-surj-morph A B
inj-surj-morph.ϕ (SES→inj-surj-morph _ _ _ _ (ses _ _ _ _ ϕ _ _)) = ϕ
inj-surj-morph.inj
  (SES→inj-surj-morph A _ lGr _
    (ses (iso ψ ξ rinv linv) _ left _ ϕ Ker-ϕ⊂Im-left _)) x inKer =
  rec (isOfHLevelPath' 1 (Group.setStruc A) _ _)
      (λ (a , pf) → sym pf ∙∙ (λ i → fst left (helper a i)) ∙∙ morph0→0 lGr A (fst left) (snd left))
      (Ker-ϕ⊂Im-left x inKer)
  where
  helper : (a : Group.type lGr) → a ≡ isGroup.id (Group.groupStruc lGr)
  helper a =
    a                                      ≡⟨ sym (linv a) ⟩
    ξ .fst (ψ .fst a)                      ≡⟨ refl ⟩
    ξ .fst tt                              ≡⟨ morph0→0 trivialGroup lGr (fst ξ) (snd ξ) ⟩
    isGroup.id (Group.groupStruc lGr) ∎

inj-surj-morph.surj (SES→inj-surj-morph _ _ _ rGr
                            (ses _ (iso ψ ξ rinv linv) _ right ϕ _ Ker-right⊂Im-ϕ)) b =
  Ker-right⊂Im-ϕ b (helper (right .fst b))
  where
  helper : (a : Group.type rGr) → a ≡ isGroup.id (Group.groupStruc rGr)
  helper a =
    a                                      ≡⟨ sym (linv a) ⟩
    ξ .fst (ψ .fst a)                      ≡⟨ refl ⟩
    ξ .fst tt                              ≡⟨ morph0→0 trivialGroup rGr (fst ξ) (snd ξ) ⟩
    isGroup.id (Group.groupStruc rGr) ∎

SES→Iso : ∀ {ℓ ℓ' ℓ'' ℓ'''} (A : Group ℓ) (B : Group ℓ') (leftGr : Group ℓ'') (rightGr : Group ℓ''')
        → SES A B leftGr rightGr
        → Iso A B
SES→Iso A B lGr rGr seq = inj-surj-morph→Iso A B (SES→inj-surj-morph A B lGr rGr seq)


{- direct products of groups -}
dirProd : ∀ {ℓ ℓ'} (A : Group ℓ) (B : Group ℓ') → Group (ℓ-max ℓ ℓ')
Group.type (dirProd (group A _ _) (group B _ _)) = A × B
Group.setStruc (dirProd (group _ setA _) (group _ setB _)) = isOfHLevelProd 2 setA setB
isGroup.id (Group.groupStruc (dirProd (group _ _ strucA) (group _ _ strucB))) =
  (isGroup.id strucA) , (isGroup.id strucB)
isGroup.inv (Group.groupStruc (dirProd (group _ _ strucA) (group _ _ strucB))) =
  map (isGroup.inv strucA) (isGroup.inv strucB)
isGroup.comp (Group.groupStruc (dirProd (group _ _ strucA) (group _ _ strucB))) (a1 , b1) (a2 , b2) =
  (isGroup.comp strucA a1 a2) , isGroup.comp strucB b1 b2
isGroup.lUnit (Group.groupStruc (dirProd (group _ _ strucA) (group _ _ strucB))) (a , b) i =
  (isGroup.lUnit strucA a i) , (isGroup.lUnit strucB b i)
isGroup.rUnit (Group.groupStruc (dirProd (group _ _ strucA) (group _ _ strucB))) (a , b) i =
  (isGroup.rUnit strucA a i) , (isGroup.rUnit strucB b i)
isGroup.assoc (Group.groupStruc (dirProd (group _ _ strucA) (group _ _ strucB))) (a1 , b1) (a2 , b2) (a3 , b3) i =
  (isGroup.assoc strucA a1 a2 a3 i) , (isGroup.assoc strucB b1 b2 b3 i)
isGroup.lCancel (Group.groupStruc (dirProd (group _ _ strucA) (group _ _ strucB))) (a , b) i =
  (isGroup.lCancel strucA a i) , (isGroup.lCancel strucB b i)
isGroup.rCancel (Group.groupStruc (dirProd (group _ _ strucA) (group _ _ strucB))) (a , b) i =
  (isGroup.rCancel strucA a i) , (isGroup.rCancel strucB b i)
                      
