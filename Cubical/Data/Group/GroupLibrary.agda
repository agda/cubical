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

open import Cubical.Data.Sigma hiding (_×_ ; comp)

open import Cubical.HITs.SetQuotients as sq

-- The image of a morphism
{-
imGroup : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → morph G H

         → Group (ℓ-max ℓ ℓ')
Group.type (imGroup G H (ϕ , mf)) = Σ[ x ∈ Group.type H ] isInIm G H ϕ x
Group.setStruc (imGroup G H (ϕ , mf)) = isOfHLevelΣ 2 (Group.setStruc H) λ _ → isOfHLevelSuc 1 propTruncIsProp
isGroup.id (Group.groupStruc (imGroup G H (ϕ , mf))) =
 let idH = isGroup.id (Group.groupStruc H)
     idG = isGroup.id (Group.groupStruc G)
     invG = isGroup.inv (Group.groupStruc G)
     invH = isGroup.inv (Group.groupStruc H)
     lUnit = isGroup.lUnit (Group.groupStruc H)
     rCancel = isGroup.rCancel (Group.groupStruc H)
 in idH , ∣ idG , morph0→0 G H ϕ mf ∣
isGroup.inv (Group.groupStruc (imGroup G H (ϕ , mf))) (h , hinim) =
  let idH = isGroup.id (Group.groupStruc H)
      idG = isGroup.id (Group.groupStruc G)
      invG = isGroup.inv (Group.groupStruc G)
      invH = isGroup.inv (Group.groupStruc H)
      lUnit = isGroup.lUnit (Group.groupStruc H)
      rCancel = isGroup.rCancel (Group.groupStruc H)
  in invH h , rec propTruncIsProp
                  (λ a → ∣ (invG (fst a))
                          , morphMinus G H ϕ mf (fst a) ∙ cong (λ x → invH x) (snd a) ∣)
                  hinim
isGroup.comp (Group.groupStruc (imGroup G H (ϕ , mf))) (h1 , h1inim) (h2 , h2inim) =
 let idH = isGroup.id (Group.groupStruc H)
     idG = isGroup.id (Group.groupStruc G)
     invG = isGroup.inv (Group.groupStruc G)
     invH = isGroup.inv (Group.groupStruc H)
     compH = isGroup.comp (Group.groupStruc H)
     compG = isGroup.comp (Group.groupStruc G)
     lUnit = isGroup.lUnit (Group.groupStruc H)
     rCancel = isGroup.rCancel (Group.groupStruc H)
 in compH h1 h2 , rec propTruncIsProp
                      (λ p1 → rec propTruncIsProp
                                  (λ p2 → ∣ (compG (fst p1) (fst p2))
                                          , mf (fst p1) (fst p2) ∙ cong₂ compH (snd p1) (snd p2) ∣)
                                   h2inim)
                      h1inim
isGroup.lUnit (Group.groupStruc (imGroup G H (ϕ , mf))) (h , _) =
 let lUnit = isGroup.lUnit (Group.groupStruc H)
 in ΣProp≡ (λ _ → propTruncIsProp)
           (lUnit h)
isGroup.rUnit (Group.groupStruc (imGroup G H (ϕ , mf))) (h , _) =
  let rUnit = isGroup.rUnit (Group.groupStruc H)
  in ΣProp≡ (λ _ → propTruncIsProp)
           (rUnit h)
isGroup.assoc (Group.groupStruc (imGroup G H (ϕ , mf))) (h1 , _) (h2 , _) (h3 , _) =
 let assoc = isGroup.assoc (Group.groupStruc H)
 in ΣProp≡ (λ _ → propTruncIsProp)
           (assoc h1 h2 h3)
isGroup.lCancel (Group.groupStruc (imGroup G H (ϕ , mf))) (h , _) =
 let lCancel = isGroup.lCancel (Group.groupStruc H)
 in ΣProp≡ (λ _ → propTruncIsProp)
           (lCancel h)
isGroup.rCancel (Group.groupStruc (imGroup G H (ϕ , mf))) (h , _) =
 let rCancel = isGroup.rCancel (Group.groupStruc H)
 in ΣProp≡ (λ _ → propTruncIsProp)
           (rCancel h)

-}
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
    isTrivialLeft : isProp (Group.type leftGr)
    isTrivialRight : isProp (Group.type rightGr)

    left : morph leftGr A
    right : morph B rightGr
    ϕ : morph A B
    
    Ker-ϕ⊂Im-left : (x : Group.type A) --
                  → isInKer A B (morph.fun ϕ) x
                  → isInIm leftGr A (morph.fun left) x
    Ker-right⊂Im-ϕ : (x : Group.type B) --
                   → isInKer B rightGr (morph.fun right) x
                   → isInIm A B (morph.fun ϕ) x
SES→Iso : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Group ℓ} {B : Group ℓ'} (leftGr : Group ℓ'') (rightGr : Group ℓ''')
        → SES A B leftGr rightGr
        → Iso A B
SES→Iso {A = A} {B = B} lGr rGr sess =
  Iso''→Iso
    (iso'' (SES.ϕ sess)
           (λ a inker → rec (Group.setStruc A _ _)
                             (λ {(a , p) → sym p ∙ cong (morph.fun (SES.left sess)) (SES.isTrivialLeft sess a _)
                                          ∙ morph0→0 lGr A (morph.fun (SES.left sess)) (morph.ismorph (SES.left sess))})
                             (SES.Ker-ϕ⊂Im-left sess a inker))
           λ a → SES.Ker-right⊂Im-ϕ sess a (SES.isTrivialRight sess _ _))

{- direct products of groups -}
dirProd : ∀ {ℓ ℓ'} (A : Group ℓ) (B : Group ℓ') → Group (ℓ-max ℓ ℓ')
Group.type (dirProd A B) = Group.type A × Group.type B
Group.setStruc (dirProd A B) = isOfHLevelProd 2 (Group.setStruc A) (Group.setStruc B)
isGroup.id (Group.groupStruc (dirProd A B)) =
  isGroup.id (Group.groupStruc A) , isGroup.id (Group.groupStruc B)
isGroup.inv (Group.groupStruc (dirProd A B)) (a1 , b1) =
  (isGroup.inv (Group.groupStruc A) a1) , (isGroup.inv (Group.groupStruc B) b1)
isGroup.comp (Group.groupStruc (dirProd A B)) (a1 , b1) (a2 , b2) =
  (isGroup.comp (Group.groupStruc A) a1 a2) , (isGroup.comp (Group.groupStruc B) b1 b2)
isGroup.lUnit (Group.groupStruc (dirProd A B)) (a1 , b1) i =
  (isGroup.lUnit (Group.groupStruc A) a1 i) , (isGroup.lUnit (Group.groupStruc B) b1 i)
isGroup.rUnit (Group.groupStruc (dirProd A B)) (a1 , b1) i =
  (isGroup.rUnit (Group.groupStruc A) a1 i) , (isGroup.rUnit (Group.groupStruc B) b1 i)
isGroup.assoc (Group.groupStruc (dirProd A B)) (a1 , b1) (a2 , b2) (a3 , b3) i =
  (isGroup.assoc (Group.groupStruc A) a1 a2 a3 i) , (isGroup.assoc (Group.groupStruc B) b1 b2 b3 i)
isGroup.lCancel (Group.groupStruc (dirProd A B)) (a1 , b1) i =
  (isGroup.lCancel (Group.groupStruc A) a1 i) , (isGroup.lCancel (Group.groupStruc B) b1 i)
isGroup.rCancel (Group.groupStruc (dirProd A B)) (a1 , b1) i =
  (isGroup.rCancel (Group.groupStruc A) a1 i) , (isGroup.rCancel (Group.groupStruc B) b1 i)


dirProdIso : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Group ℓ} {B : Group ℓ'} {C : Group ℓ''} {D : Group ℓ'''}
           → Iso A C → Iso B D
           → Iso (dirProd A B) (dirProd C D)
dirProdIso {A = A'} {B = B'} {C = C'} {D = D'} isoAC isoBD =
  Iso'→Iso
    (iso'
      (I.iso
        (λ a → (morph.fun (Iso.fun isoAC) (proj₁ a)) , (morph.fun (Iso.fun isoBD) (proj₂ a)))
        (λ a → (morph.fun (Iso.inv isoAC) (proj₁ a)) , (morph.fun (Iso.inv isoBD) (proj₂ a)))
        (λ a → ×≡ (Iso.rightInv isoAC (proj₁ a)) (Iso.rightInv isoBD (proj₂ a)))
        λ a → ×≡ (Iso.leftInv isoAC (proj₁ a)) (Iso.leftInv isoBD (proj₂ a)))
      λ {(_ , _) (_ , _) → ×≡ (morph.ismorph (Iso.fun isoAC) _ _) (morph.ismorph (Iso.fun isoBD) _ _)})



{-
Given the following diagram
  a ↦ (a , 0)   ψ         ϕ
 A -->  A × A -------> B --->  C
If ψ is an isomorphism and ϕ is surjective with ker ϕ ≡ {ψ (a , a) ∣ a ∈ A}, then C ≃ B  
-}

diagonalIso1 : ∀ {ℓ ℓ' ℓ''} (A : Group ℓ) (B : Group ℓ') (C : Group ℓ'')
               (ψ : Iso (dirProd A A) B) (ϕ : morph B C)
             → isSurjective _ _ ϕ
             → ((x : Group.type B) → isInKer B C (morph.fun ϕ) x
                                    → ∃[ y ∈ Group.type A ] x ≡ morph.fun (Iso.fun ψ) (y , y))
             → ((x : Group.type B) → (∃[ y ∈ Group.type A ] x ≡ morph.fun (Iso.fun ψ) (y , y))
                                    → isInKer B C (morph.fun ϕ) x)
             → Iso A C
diagonalIso1 A' B' C' ψ' ϕ' issurj ker→diag diag→ker =
  Iso''→Iso
    (iso'' (compMorph fstProj (compMorph (Iso.fun ψ') ϕ'))
           (λ a inker
           → rec (Group.setStruc A' _ _)
                  (λ {(a' , id') → cong proj₁ (sym (Iso.leftInv ψ' (a , id A))
                                              ∙ (cong (morph.fun (Iso.inv ψ')) id')
                                              ∙ Iso.leftInv ψ' (a' , a'))
                                  ∙ cong proj₂ (sym ((sym (Iso.leftInv ψ' (a , id A))
                                                   ∙ (cong (morph.fun (Iso.inv ψ')) id')
                                                   ∙ Iso.leftInv ψ' (a' , a'))))})
                  (ker→diag (ψ (a , id A)) inker))
           λ c → rec propTruncIsProp
                     (λ { (b , id') → ∣ comp A (proj₁ (ψ⁻ b)) (inv A (proj₂ (ψ⁻ b)))
                                      , sym (rUnit C _)
                                      ∙ cong (comp C _) (sym (diag→ker (ψ (proj₂ (ψ⁻ b) , proj₂ (ψ⁻ b)))
                                                                        ∣ proj₂ (ψ⁻ b) , refl ∣))
                                      ∙ sym (ϕmf _ _)
                                      ∙ cong ϕ (sym (Iso.rightInv ψ' _))
                                      ∙ cong (λ x → ϕ (ψ x)) (morph.ismorph (Iso.inv ψ') _ _)
                                      ∙ cong (λ x → ϕ (ψ x)) (cong₂ (comp (groupStruc (dirProd A' A')))
                                                                     (Iso.leftInv ψ' _)
                                                                     (Iso.leftInv ψ' _))
                                      ∙ cong (λ x → ϕ (ψ x)) (×≡ {a = _ , _} {b = _ , _}
                                                                  (assoc A _ _ _)
                                                                  (lUnit A _))
                                      ∙ cong (λ x → ϕ (ψ x)) (×≡ {a = _ , _} {b = _ , _}
                                                                   (cong (comp A (proj₁ (ψ⁻ b))) (lCancel A _))
                                                                   refl)
                                      ∙ cong (λ x → ϕ (ψ x)) (×≡ {a = _ , _} {b = _ , _}
                                                                  (rUnit A _)
                                                                  refl)
                                      ∙ cong (λ x → ϕ (ψ x)) (sym (×-η (ψ⁻ b)))
                                      ∙ cong ϕ (Iso.rightInv ψ' b)
                                      ∙ id' ∣ })
                     (issurj c))
  where
  open Group
  open isGroup
  A = groupStruc A'
  B = groupStruc B'
  C = groupStruc C'
  ϕ = morph.fun ϕ'
  ϕmf = morph.ismorph ϕ'
  ψ = morph.fun (Iso.fun ψ')
  ψ⁻ = morph.fun (Iso.inv ψ')

  fstProj : morph A' (dirProd A' A')
  morph.fun fstProj = λ a → a , (id A)
  morph.ismorph fstProj = λ g0 g1 i → comp A g0 g1 , lUnit A (id A) (~ i)

{-
Given the following diagram

      ϕ
A × A ⇉ B 
  ^
  |
  | a ↦ (a , 0)
  |
  A ≃ C

If ϕ is surjective with ker ϕ ≡ {(a , a) ∣ a ∈ A}, then C ≃ B  
-}

diagonalIso : ∀ {ℓ ℓ' ℓ''} (A : Group ℓ) (B : Group ℓ') (C : Group ℓ'')
           → (ϕ : morph (dirProd A A) B)
           → ((x : Group.type (dirProd A A)) → isInKer (dirProd A A) B (morph.fun ϕ) x → ∃[ y ∈ Group.type A ] x ≡ (y , y))
           → ((x : Group.type (dirProd A A)) → ∃[ y ∈ Group.type A ] x ≡ (y , y) → isInKer (dirProd A A) B (morph.fun ϕ) x)
           → isSurjective (dirProd A A) B ϕ
           → Iso C A
           → Iso C B
diagonalIso A' B' C' ϕ' diagKer1 diagKer2 issurj I =
  Iso''→Iso
    (iso'' (compMorph (compMorph (Iso.fun I) fstProj) ϕ')
           inj
           surj)
  where
  open Group
  open isGroup
  A = groupStruc A'
  B = groupStruc B'
  C = groupStruc C'
  ϕ = morph.fun ϕ'
  ϕmf = morph.ismorph ϕ'
  C→A = morph.fun (Iso.fun I)
  C→A-mf = morph.ismorph (Iso.fun I)

  fstProj : morph A' (dirProd A' A')
  morph.fun fstProj = λ a → a , (id A)
  morph.ismorph fstProj = λ g0 g1 i → comp A g0 g1 , lUnit A (id A) (~ i)

  inj :  (a : Group.type C') → isInKer C' B' (λ x → ϕ (morph.fun fstProj (C→A x))) a
        → a ≡ id C
  inj a inker = rec (Group.setStruc C' _ _)
                    (λ {(b , id') → sym (Iso.leftInv I a)
                                   ∙ cong (morph.fun (Iso.inv I)) (cong proj₁ id')
                                   ∙ cong (morph.fun (Iso.inv I)) (cong proj₂ (sym id'))
                                   ∙ morph0→0 A' C' (morph.fun (Iso.inv I)) (morph.ismorph (Iso.inv I))})
                    (diagKer1 (C→A a , isGroup.id A) inker)

  surj : (b : Group.type B') → ∃[ c ∈ Group.type C' ] ϕ (morph.fun fstProj (C→A c)) ≡ b
  surj b = rec propTruncIsProp
               (λ {(a , id') → ∣ morph.fun (Iso.inv I) a , cong ϕ (×≡ {a = _ , _} {b = _ , _} (Iso.rightInv I a) refl) ∙ id' ∣})
               (idhelper b)
    where
    idhelper : (b : Group.type B') → ∃[ a ∈ Group.type A' ] ϕ (a , (id A)) ≡ b
    idhelper b = rec  propTruncIsProp
                     (λ {((a1 , a2) , id') → ∣ (comp A a1 (inv A a2))
                                            , sym (rUnit B (ϕ (comp A a1 (inv A a2) , id A)))
                                            ∙ cong (comp B _) (sym (diagKer2 (a2 , a2) ∣ a2 , refl ∣))
                                            ∙ sym (ϕmf _ _)
                                            ∙ cong ϕ (×≡ {a = _ , _} {b = _ , _}
                                                          (assoc A a1 (inv A a2) a2 ∙ cong (comp A a1) (lCancel A a2) ∙ rUnit A a1)
                                                          (lUnit A a2))
                                            ∙ id' ∣})
                     (issurj b)
