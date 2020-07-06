{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Data.Group.Properties where

open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.Data.Group.Base
open import Cubical.Data.Sigma.Base hiding (comp)


{-
Given the following diagram
  a ↦ (a , 0)   ψ         ϕ
 A -->  A × A -------> B --->  C
If ψ is an isomorphism and ϕ is surjective with ker ϕ ≡ {ψ (a , a) ∣ a ∈ A}, then C ≅ B
-}

diagonalIso1 : ∀ {ℓ ℓ' ℓ''} (A : Group ℓ) (B : Group ℓ') (C : Group ℓ'')
               (ψ : Iso (dirProd A A) B) (ϕ : morph B C)
             → isSurjective _ _ ϕ
             → ((x : Group.type B) → isInKer B C ϕ x
                                    → ∃[ y ∈ Group.type A ] x ≡ morph.fun (Iso.fun ψ) (y , y))
             → ((x : Group.type B) → (∃[ y ∈ Group.type A ] x ≡ morph.fun (Iso.fun ψ) (y , y))
                                    → isInKer B C ϕ x)
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
A × A ↠ B
  ^
  |
  | a ↦ (a , 0)
  |
  A ≃ C

If ϕ is surjective with ker ϕ ≡ {(a , a) ∣ a ∈ A}, then C ≅ B
-}

diagonalIso2 : ∀ {ℓ ℓ' ℓ''} (A : Group ℓ) (B : Group ℓ') (C : Group ℓ'')
           → (ϕ : morph (dirProd A A) B)
           → ((x : Group.type (dirProd A A)) → isInKer (dirProd A A) B ϕ x → ∃[ y ∈ Group.type A ] x ≡ (y , y))
           → ((x : Group.type (dirProd A A)) → ∃[ y ∈ Group.type A ] x ≡ (y , y) → isInKer (dirProd A A) B ϕ x)
           → isSurjective (dirProd A A) B ϕ
           → Iso C A
           → Iso C B
diagonalIso2 A' B' C' ϕ' diagKer1 diagKer2 issurj I =
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

  inj :  (a : Group.type C') → isInKer C' B' (compMorph (compMorph (Iso.fun I) fstProj) ϕ') a
        → a ≡ id C
  inj a inker = rec (Group.setStruc C' _ _)
                    (λ {(b , id') → sym (Iso.leftInv I a)
                                   ∙ cong (morph.fun (Iso.inv I)) (cong proj₁ id')
                                   ∙ cong (morph.fun (Iso.inv I)) (cong proj₂ (sym id'))
                                   ∙ morph0→0 A' C' (Iso.inv I)})
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
