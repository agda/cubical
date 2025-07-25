{-

The sheaf property of a presheaf on a distributive lattice or a basis thereof
can be expressed as preservation of limits over diagrams defined in this file.

-}

module Cubical.Categories.DistLatticeSheaf.Diagram where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order hiding (_<_)
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.FinData.Order renaming (_<'Fin_ to _<_)
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Order.Poset

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

module _ {ℓ : Level} where
  data DLShfDiagOb (n : ℕ) : Type ℓ where
    sing : Fin n → DLShfDiagOb n
    pair : (i j : Fin n) → i < j → DLShfDiagOb n

  data DLShfDiagHom (n : ℕ) : DLShfDiagOb n → DLShfDiagOb n → Type ℓ where
    idAr : {x : DLShfDiagOb n} → DLShfDiagHom n x x
    singPairL : {i j : Fin n} {i<j : i < j}  → DLShfDiagHom n (sing i) (pair i j i<j)
    singPairR : {i j : Fin n} {i<j : i < j}→ DLShfDiagHom n (sing j) (pair i j i<j)


  module DLShfDiagHomPath where
    variable
     n : ℕ

    -- DLShfDiagHom n x y is a retract of Code x y
    Code : (x y : DLShfDiagOb n) → Type
    Code (sing i) (sing j) = i ≡ j
    Code (sing i) (pair j k j<k) =
        (Σ[ p ∈ (i ≡ j) ] Σ[ i<k ∈ i < k ] PathP (λ ι → p ι < k) i<k j<k)
      ⊎ (Σ[ p ∈ (i ≡ k) ] Σ[ j<i ∈ j < i ] PathP (λ ι → j < p ι) j<i j<k)
    Code (pair i j i<j) (sing k) = ⊥
    Code (pair i j i<j) (pair k l k<l) =
      Σ[ p ∈ (i ≡ k) × (j ≡ l) ] PathP (λ ι → fst p ι < snd p ι) i<j k<l

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
DLShfDiag : ℕ → (ℓ : Level) → Category ℓ ℓ
ob (DLShfDiag n ℓ) = DLShfDiagOb n
Hom[_,_] (DLShfDiag n ℓ) = DLShfDiagHom n
id (DLShfDiag n ℓ) = idAr
_⋆_ (DLShfDiag n ℓ) idAr f = f
_⋆_ (DLShfDiag n ℓ) singPairL idAr = singPairL
_⋆_ (DLShfDiag n ℓ) singPairR idAr = singPairR
⋆IdL (DLShfDiag n ℓ) _ = refl
⋆IdR (DLShfDiag n ℓ) idAr = refl
⋆IdR (DLShfDiag n ℓ) singPairL = refl
⋆IdR (DLShfDiag n ℓ) singPairR = refl
⋆Assoc (DLShfDiag n ℓ) idAr _ _ = refl
⋆Assoc (DLShfDiag n ℓ) singPairL idAr _ = refl
⋆Assoc (DLShfDiag n ℓ) singPairR idAr _ = refl
isSetHom (DLShfDiag n ℓ) = let open DLShfDiagHomPath in (isSetDLShfDiagHom _ _)


-- a lemma for eliminating pair cases
-- when checking that somthing is a cone morphism
module _ {C : Category ℓ ℓ'} {n : ℕ} {F : Functor (DLShfDiag n ℓ'') C} where
  open Category
  open Functor F
  open Cone

  isConeMorSingLemma : {c d : ob C} {f : C [ c , d ]}
                       (cc : Cone F c) (cd : Cone F d)
                     → (∀ i → f ⋆⟨ C ⟩ coneOut cd (sing i) ≡ coneOut cc (sing i))
                     → isConeMor cc cd f
  isConeMorSingLemma cc cd singHyp (sing i) = singHyp i
  isConeMorSingLemma {f = f} cc cd singHyp (pair i j i<j) =
                      f ⋆⟨ C ⟩ coneOut cd (pair i j i<j)
                    ≡⟨ cong (λ x → f ⋆⟨ C ⟩ x) (sym (cd .coneOutCommutes singPairL)) ⟩
                      f ⋆⟨ C ⟩ (coneOut cd (sing i) ⋆⟨ C ⟩ F-hom singPairL)
                    ≡⟨ sym (⋆Assoc C _ _ _) ⟩
                      (f ⋆⟨ C ⟩ coneOut cd (sing i)) ⋆⟨ C ⟩ F-hom singPairL
                    ≡⟨ cong (λ x → x ⋆⟨ C ⟩ F-hom singPairL) (singHyp i) ⟩
                      coneOut cc (sing i) ⋆⟨ C ⟩ F-hom singPairL
                    ≡⟨ cc .coneOutCommutes singPairL ⟩
                      coneOut cc (pair i j i<j) ∎


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


 FinVec→Diag : {n : ℕ} → FinVec L n → Functor (DLShfDiag n ℓ) LCat
 F-ob (FinVec→Diag α) (sing i) = α i
 F-ob (FinVec→Diag α) (pair i j _) = α j ∧l α i
 F-hom (FinVec→Diag α) idAr = is-refl _
 F-hom (FinVec→Diag α) singPairL = ≤m→≤j _ _ (∧≤LCancel _ _)
 F-hom (FinVec→Diag α) singPairR = ≤m→≤j _ _ (∧≤RCancel _ _)
 F-id (FinVec→Diag α) = is-prop-valued _ _ _ _
 F-seq (FinVec→Diag α) _ _ = is-prop-valued _ _ _ _

 ⋁Cone : {n : ℕ} (α : FinVec L n) → Cone (FinVec→Diag α) (⋁ α)
 coneOut (⋁Cone α) (sing i) = ind≤⋁ α i
 coneOut (⋁Cone α) (pair i _ _) = is-trans _ (α i) _ (≤m→≤j _ _ (∧≤LCancel _ _)) (ind≤⋁ α i)
 coneOutCommutes (⋁Cone α) _ = is-prop-valued _ _ _ _

 isLimCone⋁Cone : {n : ℕ} (α : FinVec L n) → isLimCone (FinVec→Diag α) (⋁ α) (⋁Cone α)
 fst (fst (isLimCone⋁Cone α u uCone)) = ⋁IsMax α _ λ i → uCone .coneOut (sing i)
 snd (fst (isLimCone⋁Cone α u uCone)) _ = is-prop-valued _ _ _ _
 snd (isLimCone⋁Cone α _ uCone) _ = Σ≡Prop (λ _ → isPropIsConeMor uCone (⋁Cone α) _)
                                           (is-prop-valued _ _ _ _)


module PullbacksAsDLShfDiags {ℓ'' : Level}
                             (C : Category ℓ ℓ')
                             (cspan : Cospan C)
                             (pback : Pullback C cspan) where

 open Functor
 open Cone
 open Cospan ⦃...⦄
 open Pullback ⦃...⦄
 instance
  _ = cspan
  _ = pback

 cospanAsDiag : Functor (DLShfDiag 2 ℓ'') C
 F-ob cospanAsDiag (sing zero) = l
 F-ob cospanAsDiag (sing one) = r
 F-ob cospanAsDiag (pair _ _ _) = m
 F-hom cospanAsDiag idAr = id C
 F-hom cospanAsDiag {x = sing zero} singPairL = s₁
 F-hom cospanAsDiag {x = sing one} singPairL = s₂
 F-hom cospanAsDiag {x = sing zero} singPairR = s₁
 F-hom cospanAsDiag {x = sing one} singPairR = s₂
 F-id cospanAsDiag = refl
 F-seq cospanAsDiag idAr idAr = sym (⋆IdL C _)
 F-seq cospanAsDiag idAr singPairL = sym (⋆IdL C _)
 F-seq cospanAsDiag idAr singPairR = sym (⋆IdL C _)
 F-seq cospanAsDiag singPairL idAr = sym (⋆IdR C _)
 F-seq cospanAsDiag singPairR idAr = sym (⋆IdR C _)

 pbPrAsCone : Cone cospanAsDiag pbOb
 coneOut pbPrAsCone (sing zero) = pbPr₁
 coneOut pbPrAsCone (sing one) = pbPr₂
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
                      (coneOut cc (sing one) ≡ hk ⋆⟨ C ⟩ pbPr₂)
  fromPBUnivProp = univProp
     (cc .coneOut (sing zero)) (cc .coneOut (sing one))
     (cc .coneOutCommutes (singPairL {i<j = s≤s z≤}) ∙ sym (cc .coneOutCommutes singPairR))

  toConeMor : isConeMor cc pbPrAsCone (fromPBUnivProp .fst .fst)
  toConeMor (sing zero) = sym (fromPBUnivProp .fst .snd .fst)
  toConeMor (sing one) = sym (fromPBUnivProp .fst .snd .snd)
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
  toConeMor (pair one j _) = path
   where
   path : fromPBUnivProp .fst .fst ⋆⟨ C ⟩ (pbPr₁ ⋆⟨ C ⟩ s₁)
        ≡ cc .coneOut (pair one j _)
   path = fromPBUnivProp .fst .fst ⋆⟨ C ⟩ (pbPr₁ ⋆⟨ C ⟩ s₁)
        ≡⟨ cong (λ f → fromPBUnivProp .fst .fst ⋆⟨ C ⟩ f) pbCommutes ⟩
          fromPBUnivProp .fst .fst ⋆⟨ C ⟩ (pbPr₂ ⋆⟨ C ⟩ s₂)
        ≡⟨ sym (⋆Assoc C _ _ _) ⟩
          (fromPBUnivProp .fst .fst ⋆⟨ C ⟩ pbPr₂) ⋆⟨ C ⟩ s₂
        ≡⟨ cong (λ f → f ⋆⟨ C ⟩ s₂) (sym (fromPBUnivProp .fst .snd .snd)) ⟩
          cc .coneOut (sing one) ⋆⟨ C ⟩ s₂
        ≡⟨ cc .coneOutCommutes singPairL ⟩
          cc .coneOut (pair one j _) ∎

  fromConeMor : {f : C [ c , pbOb ]}
              → isConeMor cc pbPrAsCone f
              → (coneOut cc (sing zero) ≡ f ⋆⟨ C ⟩ pbPr₁) ×
                (coneOut cc (sing one) ≡ f ⋆⟨ C ⟩ pbPr₂)
  fst (fromConeMor cf) = sym (cf (sing zero))
  snd (fromConeMor cf) = sym (cf (sing one))



module DLShfDiagsAsPullbacks (C : Category ℓ ℓ')
                             (F : Functor (DLShfDiag 2 ℓ'') C)
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
 m DiagAsCospan = F-ob (pair zero one (s≤s z≤))
 r DiagAsCospan = F-ob (sing one)
 s₁ DiagAsCospan = F-hom singPairL
 s₂ DiagAsCospan = F-hom singPairR

 LimAsPullback : Pullback C DiagAsCospan
 pbOb LimAsPullback = lim
 pbPr₁ LimAsPullback = coneOut (sing zero)
 pbPr₂ LimAsPullback = coneOut (sing one)
 pbCommutes LimAsPullback = coneOutCommutes singPairL ∙ sym (coneOutCommutes singPairR)
 univProp LimAsPullback {d = d} f g cSq =
  uniqueExists
    (fromUnivProp .fst .fst)
      (sym (fromUnivProp .fst .snd (sing zero)) , sym (fromUnivProp .fst .snd (sing one)))
        (λ _ → isProp× (isSetHom C _ _) (isSetHom C _ _))
          λ h' trs → cong fst (fromUnivProp .snd (h' , toConeMor h' trs))
  where
  theCone : Cone F d
  Cone.coneOut theCone (sing zero) = f
  Cone.coneOut theCone (sing one) = g
  Cone.coneOut theCone (pair zero zero ())
  Cone.coneOut theCone (pair zero one (s≤s z≤)) = f ⋆⟨ C ⟩ DiagAsCospan .s₁
  Cone.coneOut theCone (pair one zero ())
  Cone.coneOut theCone (pair one one (s≤s ()))
  Cone.coneOutCommutes theCone {u} idAr = cong (seq' C (Cone.coneOut theCone u)) F-id
                                        ∙ ⋆IdR C (Cone.coneOut theCone u)
  Cone.coneOutCommutes theCone {sing zero} {pair ._ one (s≤s z≤)} singPairL = refl
  Cone.coneOutCommutes theCone {sing one} {pair ._ one (s≤s ())} singPairL
  Cone.coneOutCommutes theCone {sing one} {pair zero ._ (s≤s z≤)} singPairR = sym cSq
  Cone.coneOutCommutes theCone {sing one} {pair one ._ (s≤s ())} singPairR

  fromUnivProp : ∃![ h ∈ C [ d , lim ] ] isConeMor theCone limCone h
  fromUnivProp = LimCone.univProp limF d theCone

  toConeMor : ∀ (h' : C [ d , lim ])
            → (f ≡ h' ⋆⟨ C ⟩ coneOut (sing zero)) × (g ≡ h' ⋆⟨ C ⟩ coneOut (sing one))
            → isConeMor theCone limCone h'
  toConeMor h' (tr₁ , tr₂) (sing zero) = sym tr₁
  toConeMor h' (tr₁ , tr₂) (sing one) = sym tr₂
  toConeMor h' (tr₁ , tr₂) (pair zero one (s≤s z≤)) = path
    where
    path : h' ⋆⟨ C ⟩ coneOut (pair zero one (s≤s z≤))
         ≡ f ⋆⟨ C ⟩ F-hom singPairL
    path = h' ⋆⟨ C ⟩ coneOut (pair zero one (s≤s z≤))
         ≡⟨ cong (seq' C h') (sym (coneOutCommutes singPairL)) ⟩
           h' ⋆⟨ C ⟩ (coneOut (sing zero) ⋆⟨ C ⟩ F-hom singPairL)
         ≡⟨ sym (⋆Assoc C _ _ _) ⟩
           (h' ⋆⟨ C ⟩ coneOut (sing zero)) ⋆⟨ C ⟩ F-hom singPairL
         ≡⟨ cong (λ x → seq' C x (F-hom singPairL)) (sym tr₁) ⟩
           f ⋆⟨ C ⟩ F-hom singPairL ∎
  toConeMor h' (tr₁ , tr₂) (pair one one (s≤s ()))
