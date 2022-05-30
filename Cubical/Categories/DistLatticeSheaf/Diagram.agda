{-

The sheaf property of a presheaf on a distributive lattice or a basis thereof
can be expressed as preservation of limits over diagrams defined in this file.

-}
{-# OPTIONS --safe #-}

module Cubical.Categories.DistLatticeSheaf.Diagram where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.FinData.Order
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Poset

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Instances.DistLattice

open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.DistLattice.BigOps

private
  variable
    ℓ ℓ' ℓ'' : Level

data DLShfDiagOb (n : ℕ) : Type where
  sing : Fin n → DLShfDiagOb n
  pair : (i j : Fin n) → i <'Fin j → DLShfDiagOb n

data DLShfDiagHom (n : ℕ) : DLShfDiagOb n → DLShfDiagOb n → Type where
  idAr : {x : DLShfDiagOb n} → DLShfDiagHom n x x
  singPairL : {i j : Fin n} {i<j : i <'Fin j}  → DLShfDiagHom n (sing i) (pair i j i<j)
  singPairR : {i j : Fin n} {i<j : i <'Fin j}→ DLShfDiagHom n (sing j) (pair i j i<j)


module DLShfDiagHomPath where
  variable
   n : ℕ

  -- DLShfDiagHom n x y is a retract of Code x y
  Code : (x y : DLShfDiagOb n) → Type
  Code (sing i) (sing j) = i ≡ j
  Code (sing i) (pair j k j<k) =
      (Σ[ p ∈ (i ≡ j) ] Σ[ i<k ∈ i <'Fin k ] PathP (λ ι → p ι <'Fin k) i<k j<k)
    ⊎ (Σ[ p ∈ (i ≡ k) ] Σ[ j<i ∈ j <'Fin i ] PathP (λ ι → j <'Fin p ι) j<i j<k)
  Code (pair i j i<j) (sing k) = ⊥
  Code (pair i j i<j) (pair k l k<l) =
    Σ[ p ∈ (i ≡ k) × (j ≡ l) ] PathP (λ ι → fst p ι <'Fin snd p ι) i<j k<l

  isSetCode : ∀ (x y : DLShfDiagOb n) → isSet (Code x y)
  isSetCode (sing _) (sing _) = isProp→isSet (isSetFin _ _)
  isSetCode (sing i) (pair j k j<k) =
    isSet⊎
      (isSetΣ (isProp→isSet (isSetFin _ _))
        λ _ → isSetΣ (isProp→isSet (≤'FinIsPropValued _ _))
        λ _ → isOfHLevelPathP 2 (isProp→isSet (≤'FinIsPropValued _ _)) _ _)
      (isSetΣ (isProp→isSet (isSetFin _ _))
        λ _ → isSetΣ (isProp→isSet (≤'FinIsPropValued _ _))
        λ _ → isOfHLevelPathP 2 (isProp→isSet (≤'FinIsPropValued _ _)) _ _)
  isSetCode (pair _ _ _) (sing _) = isProp→isSet isProp⊥
  isSetCode (pair _ _ _) (pair _ _ _) =
    isSetΣ
      (isSet× (isProp→isSet (isSetFin _ _)) (isProp→isSet (isSetFin _ _)))
        λ _ → isOfHLevelPathP 2 (isProp→isSet (≤'FinIsPropValued _ _)) _ _

  encode : (x y : DLShfDiagOb n) → DLShfDiagHom n x y → Code x y
  encode (sing i) (sing .i) idAr = refl
  encode (sing i) (pair .i j i<j) singPairL = inl (refl , i<j , refl)
  encode (sing j) (pair i .j i<j) singPairR = inr (refl , i<j , refl)
  encode (pair i j i<j) (pair .i .j .i<j) idAr = (refl , refl) , refl

  decode : (x y : DLShfDiagOb n) → Code x y → DLShfDiagHom n x y
  decode (sing i) (sing j) p = subst (λ k → DLShfDiagHom _ (sing i) (sing k)) p idAr
  decode (sing i) (pair j k j<k) (inl (p , i<k , q)) =
    transport (λ ι → DLShfDiagHom _ (sing i) (pair (p ι) k (q ι))) singPairL
  decode (sing i) (pair k j k<j) (inr (p , k<i , q)) =
    transport (λ ι → DLShfDiagHom _ (sing i) (pair k (p ι) (q ι))) singPairR
  decode (pair i j i<j) (pair k l k<l) (_ , p) =
    transport (λ ι → DLShfDiagHom _ (pair _ _ i<j) (pair _ _ (p ι))) idAr

  codeRetract : ∀ (x y : DLShfDiagOb n) (f : DLShfDiagHom n x y)
              → decode x y (encode x y f) ≡ f
  codeRetract (sing i) (sing .i) idAr = transportRefl idAr
  codeRetract (sing i) (pair .i k i<k) singPairL = transportRefl singPairL
  codeRetract (sing i) (pair j .i j<i) singPairR = transportRefl singPairR
  codeRetract (pair i j i<j) (pair .i .j .i<j) idAr = transportRefl idAr

  isSetDLShfDiagHom : ∀ (x y : DLShfDiagOb n) → isSet (DLShfDiagHom n x y)
  isSetDLShfDiagHom x y = isSetRetract (encode x y) (decode x y)
                                         (codeRetract x y) (isSetCode x y)



open Category
DLShfDiag : ℕ → Category ℓ-zero ℓ-zero
ob (DLShfDiag n) = DLShfDiagOb n
Hom[_,_] (DLShfDiag n) = DLShfDiagHom n
id (DLShfDiag n) = idAr
_⋆_ (DLShfDiag n) idAr f = f
_⋆_ (DLShfDiag n) singPairL idAr = singPairL
_⋆_ (DLShfDiag n) singPairR idAr = singPairR
⋆IdL (DLShfDiag n) _ = refl
⋆IdR (DLShfDiag n) idAr = refl
⋆IdR (DLShfDiag n) singPairL = refl
⋆IdR (DLShfDiag n) singPairR = refl
⋆Assoc (DLShfDiag n) idAr _ _ = refl
⋆Assoc (DLShfDiag n) singPairL idAr _ = refl
⋆Assoc (DLShfDiag n) singPairR idAr _ = refl
isSetHom (DLShfDiag n) = let open DLShfDiagHomPath in (isSetDLShfDiagHom _ _)


module _ (L' : DistLattice ℓ) where
 private
  L = fst L'
  LCat = (DistLatticeCategory L') ^op
  instance
   _ = snd L'

 open DistLatticeStr ⦃...⦄
 open Join L'
 open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L'))
 open PosetStr (IndPoset .snd) hiding (_≤_)
 open MeetSemilattice (Lattice→MeetSemilattice (DistLattice→Lattice L'))
      using (∧≤RCancel ; ∧≤LCancel)
 open Order (DistLattice→Lattice L')

 open Category LCat
 open Functor
 open Cone


 FinVec→Diag : {n : ℕ} → FinVec L n → Functor (DLShfDiag n) LCat
 F-ob (FinVec→Diag α) (sing i) = α i
 F-ob (FinVec→Diag α) (pair i j _) = α i ∧l α j
 F-hom (FinVec→Diag α) idAr = is-refl _
 F-hom (FinVec→Diag α) singPairL = ≤m→≤j _ _ (∧≤RCancel _ _)
 F-hom (FinVec→Diag α) singPairR = ≤m→≤j _ _ (∧≤LCancel _ _)
 F-id (FinVec→Diag α) = is-prop-valued _ _ _ _
 F-seq (FinVec→Diag α) _ _ = is-prop-valued _ _ _ _

 ⋁Cone : {n : ℕ} (α : FinVec L n) → Cone (FinVec→Diag α) (⋁ α)
 coneOut (⋁Cone α) (sing i) = ind≤⋁ α i
 coneOut (⋁Cone α) (pair i _ _) = is-trans _ (α i) _ (≤m→≤j _ _ (∧≤RCancel _ _)) (ind≤⋁ α i)
 coneOutCommutes (⋁Cone α) _ = is-prop-valued _ _ _ _

 isLimCone⋁Cone : {n : ℕ} (α : FinVec L n) → isLimCone (FinVec→Diag α) (⋁ α) (⋁Cone α)
 fst (fst (isLimCone⋁Cone α u uCone)) = ⋁IsMax α _ λ i → uCone .coneOut (sing i)
 snd (fst (isLimCone⋁Cone α u uCone)) _ = is-prop-valued _ _ _ _
 snd (isLimCone⋁Cone α _ uCone) _ = Σ≡Prop (λ _ → isPropIsConeMor uCone (⋁Cone α) _)
                                           (is-prop-valued _ _ _ _)


module PullbacksAsDLShfDiags (C : Category ℓ ℓ')
                             (cspan : Cospan C)
                             (pback : Pullback C cspan) where

 open Functor
 open Cone
 open Cospan ⦃...⦄
 open Pullback ⦃...⦄
 instance
  _ = cspan
  _ = pback

 cospanAsDiag : Functor (DLShfDiag 2) C
 F-ob cospanAsDiag (sing zero) = l
 F-ob cospanAsDiag (sing (suc zero)) = r
 F-ob cospanAsDiag (pair _ _ _) = m
 F-hom cospanAsDiag idAr = id C
 F-hom cospanAsDiag {x = sing zero} singPairL = s₁
 F-hom cospanAsDiag {x = sing (suc zero)} singPairL = s₂
 F-hom cospanAsDiag {x = sing zero} singPairR = s₁
 F-hom cospanAsDiag {x = sing (suc zero)} singPairR = s₂
 F-id cospanAsDiag = refl
 F-seq cospanAsDiag idAr idAr = sym (⋆IdL C _)
 F-seq cospanAsDiag idAr singPairL = sym (⋆IdL C _)
 F-seq cospanAsDiag idAr singPairR = sym (⋆IdL C _)
 F-seq cospanAsDiag singPairL idAr = sym (⋆IdR C _)
 F-seq cospanAsDiag singPairR idAr = sym (⋆IdR C _)

 pbPrAsCone : Cone cospanAsDiag pbOb
 coneOut pbPrAsCone (sing zero) = pbPr₁
 coneOut pbPrAsCone (sing (suc zero)) = pbPr₂
 coneOut pbPrAsCone (pair _ _ _) = pbPr₁ ⋆⟨ C ⟩ s₁
 coneOutCommutes pbPrAsCone idAr = ⋆IdR C _
 coneOutCommutes pbPrAsCone (singPairL {zero}) = refl
 coneOutCommutes pbPrAsCone (singPairL {suc zero}) = sym pbCommutes
 coneOutCommutes pbPrAsCone (singPairR {zero} {zero}) = refl
 coneOutCommutes pbPrAsCone (singPairR {zero} {suc zero}) = sym pbCommutes
 coneOutCommutes pbPrAsCone (singPairR {suc zero} {zero}) = refl
 coneOutCommutes pbPrAsCone (singPairR {suc zero} {suc zero}) = sym pbCommutes

 pbAsLimit : isLimCone cospanAsDiag pbOb pbPrAsCone
 pbAsLimit c cc = uniqueExists (fromPBUnivProp .fst .fst)
                               toConeMor
                               (λ _ → isPropIsConeMor cc pbPrAsCone _)
                               (λ f cf → cong fst (fromPBUnivProp .snd (f , fromConeMor cf)))
  where
  fromPBUnivProp : ∃![ hk ∈ C [ c , Pullback.pbOb pback ] ]
                      (coneOut cc (sing zero) ≡ hk ⋆⟨ C ⟩ pbPr₁) ×
                      (coneOut cc (sing (suc zero)) ≡ hk ⋆⟨ C ⟩ pbPr₂)
  fromPBUnivProp = univProp
     (cc .coneOut (sing zero)) (cc .coneOut (sing (suc zero)))
     (cc .coneOutCommutes (singPairL {i<j = s≤s z≤}) ∙ sym (cc .coneOutCommutes singPairR))

  toConeMor : isConeMor cc pbPrAsCone (fromPBUnivProp .fst .fst)
  toConeMor (sing zero) = sym (fromPBUnivProp .fst .snd .fst)
  toConeMor (sing (suc zero)) = sym (fromPBUnivProp .fst .snd .snd)
  toConeMor (pair zero j _) = path
   where
   path : fromPBUnivProp .fst .fst ⋆⟨ C ⟩ (pbPr₁ ⋆⟨ C ⟩ s₁) ≡ cc .coneOut (pair zero j _)
   path = fromPBUnivProp .fst .fst ⋆⟨ C ⟩ (pbPr₁ ⋆⟨ C ⟩ s₁)
        ≡⟨ sym (⋆Assoc C _ _ _) ⟩
          (fromPBUnivProp .fst .fst ⋆⟨ C ⟩ pbPr₁) ⋆⟨ C ⟩ s₁
        ≡⟨ cong (λ f → f ⋆⟨ C ⟩ s₁) (sym (fromPBUnivProp .fst .snd .fst)) ⟩
          cc .coneOut (sing zero) ⋆⟨ C ⟩ s₁
        ≡⟨ cc .coneOutCommutes singPairL ⟩
          cc .coneOut (pair zero j _) ∎
  toConeMor (pair (suc zero) j _) = path
   where
   path : fromPBUnivProp .fst .fst ⋆⟨ C ⟩ (pbPr₁ ⋆⟨ C ⟩ s₁)
        ≡ cc .coneOut (pair (suc zero) j _)
   path = fromPBUnivProp .fst .fst ⋆⟨ C ⟩ (pbPr₁ ⋆⟨ C ⟩ s₁)
        ≡⟨ cong (λ f → fromPBUnivProp .fst .fst ⋆⟨ C ⟩ f) pbCommutes ⟩
          fromPBUnivProp .fst .fst ⋆⟨ C ⟩ (pbPr₂ ⋆⟨ C ⟩ s₂)
        ≡⟨ sym (⋆Assoc C _ _ _) ⟩
          (fromPBUnivProp .fst .fst ⋆⟨ C ⟩ pbPr₂) ⋆⟨ C ⟩ s₂
        ≡⟨ cong (λ f → f ⋆⟨ C ⟩ s₂) (sym (fromPBUnivProp .fst .snd .snd)) ⟩
          cc .coneOut (sing (suc zero)) ⋆⟨ C ⟩ s₂
        ≡⟨ cc .coneOutCommutes singPairL ⟩
          cc .coneOut (pair (suc zero) j _) ∎

  fromConeMor : {f : C [ c , pbOb ]}
              → isConeMor cc pbPrAsCone f
              → (coneOut cc (sing zero) ≡ f ⋆⟨ C ⟩ pbPr₁) ×
                (coneOut cc (sing (suc zero)) ≡ f ⋆⟨ C ⟩ pbPr₂)
  fst (fromConeMor cf) = sym (cf (sing zero))
  snd (fromConeMor cf) = sym (cf (sing (suc zero)))



module DLShfDiagsAsPullbacks (C : Category ℓ ℓ')
                             (F : Functor (DLShfDiag 2) C)
                             (limF : LimCone F) where



 open Cospan
 open Pullback
 open Functor ⦃...⦄
 open Cone ⦃...⦄
 open LimCone ⦃...⦄
 instance
  _ = F
  _ = limF
  _ = limF .limCone


 DiagAsCospan : Cospan C
 l DiagAsCospan = F-ob (sing zero)
 m DiagAsCospan = F-ob (pair zero (suc zero) (s≤s z≤))
 r DiagAsCospan = F-ob (sing (suc zero))
 s₁ DiagAsCospan = F-hom singPairL
 s₂ DiagAsCospan = F-hom singPairR

 LimAsPullback : Pullback C DiagAsCospan
 pbOb LimAsPullback = lim
 pbPr₁ LimAsPullback = coneOut (sing zero)
 pbPr₂ LimAsPullback = coneOut (sing (suc zero))
 pbCommutes LimAsPullback = coneOutCommutes singPairL ∙ sym (coneOutCommutes singPairR)
 univProp LimAsPullback {d = d} f g cSq =
  uniqueExists
    (fromUnivProp .fst .fst)
      (sym (fromUnivProp .fst .snd (sing zero)) , sym (fromUnivProp .fst .snd (sing (suc zero))))
        (λ _ → isProp× (isSetHom C _ _) (isSetHom C _ _))
          λ h' trs → cong fst (fromUnivProp .snd (h' , toConeMor h' trs))
  where
  theCone : Cone F d
  Cone.coneOut theCone (sing zero) = f
  Cone.coneOut theCone (sing (suc zero)) = g
  Cone.coneOut theCone (pair zero zero ())
  Cone.coneOut theCone (pair zero (suc zero) (s≤s z≤)) = f ⋆⟨ C ⟩ DiagAsCospan .s₁
  Cone.coneOut theCone (pair (suc zero) zero ())
  Cone.coneOut theCone (pair (suc zero) (suc zero) (s≤s ()))
  Cone.coneOutCommutes theCone {u} idAr = cong (seq' C (Cone.coneOut theCone u)) F-id
                                        ∙ ⋆IdR C (Cone.coneOut theCone u)
  Cone.coneOutCommutes theCone {sing zero} {pair ._ (suc zero) (s≤s z≤)} singPairL = refl
  Cone.coneOutCommutes theCone {sing (suc zero)} {pair ._ (suc zero) (s≤s ())} singPairL
  Cone.coneOutCommutes theCone {sing (suc zero)} {pair zero ._ (s≤s z≤)} singPairR = sym cSq
  Cone.coneOutCommutes theCone {sing (suc zero)} {pair (suc zero) ._ (s≤s ())} singPairR

  fromUnivProp : ∃![ h ∈ C [ d , lim ] ] isConeMor theCone limCone h
  fromUnivProp = LimCone.univProp limF d theCone

  toConeMor : ∀ (h' : C [ d , lim ])
            → (f ≡ h' ⋆⟨ C ⟩ coneOut (sing zero)) × (g ≡ h' ⋆⟨ C ⟩ coneOut (sing (suc zero)))
            → isConeMor theCone limCone h'
  toConeMor h' (tr₁ , tr₂) (sing zero) = sym tr₁
  toConeMor h' (tr₁ , tr₂) (sing (suc zero)) = sym tr₂
  toConeMor h' (tr₁ , tr₂) (pair zero (suc zero) (s≤s z≤)) = path
    where
    path : h' ⋆⟨ C ⟩ coneOut (pair zero (suc zero) (s≤s z≤))
         ≡ f ⋆⟨ C ⟩ F-hom singPairL
    path = h' ⋆⟨ C ⟩ coneOut (pair zero (suc zero) (s≤s z≤))
         ≡⟨ cong (seq' C h') (sym (coneOutCommutes singPairL)) ⟩
           h' ⋆⟨ C ⟩ (coneOut (sing zero) ⋆⟨ C ⟩ F-hom singPairL)
         ≡⟨ sym (⋆Assoc C _ _ _) ⟩
           (h' ⋆⟨ C ⟩ coneOut (sing zero)) ⋆⟨ C ⟩ F-hom singPairL
         ≡⟨ cong (λ x → seq' C x (F-hom singPairL)) (sym tr₁) ⟩
           f ⋆⟨ C ⟩ F-hom singPairL ∎
  toConeMor h' (tr₁ , tr₂) (pair (suc zero) (suc zero) (s≤s ()))
