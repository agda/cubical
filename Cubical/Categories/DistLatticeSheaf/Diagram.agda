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
  pair : {i j : Fin n} → i <Fin j → DLShfDiagOb n

-- Another idea: ob= Σ[ (i , j) ∈ Fin n × Fin n ] i≤j
-- Hom (i,j) (k,l) = (1) i≡k × j≡l
--                   (2) i≡j × k<l × (i≡k ⊎ i≡l)

data DLShfDiagHom (n : ℕ) : DLShfDiagOb n → DLShfDiagOb n → Type where
  idAr : {x : DLShfDiagOb n} → DLShfDiagHom n x x
  singPairL : {i j : Fin n} {i<j : i <Fin j}  → DLShfDiagHom n (sing i) (pair i<j)
  singPairR : {i j : Fin n} {i<j : i <Fin j}→ DLShfDiagHom n (sing j) (pair i<j)


module DLShfDiagHomPath where
  variable
   n : ℕ

  -- DLShfDiagHom n x y is a retract of Code x y
  Code : (x y : DLShfDiagOb n) → Type
  Code (sing i) (sing j) = i ≡ j
  Code (sing i) (pair {j} {k} _) = (i ≡ j) ⊎ (i ≡ k)
  Code (pair i<j) (sing k) = ⊥
  Code (pair {i} {j} _) (pair {k} {l} _) = (i ≡ k) × (j ≡ l)

  isSetCode : ∀ (x y : DLShfDiagOb n) → isSet (Code x y)
  isSetCode (sing i) (sing j) = isProp→isSet (isSetFin _ _)
  isSetCode (sing i) (pair j<k) =
    isSet⊎ (isProp→isSet (isSetFin _ _)) (isProp→isSet (isSetFin _ _))
  isSetCode (pair i<j) (sing k) = isProp→isSet isProp⊥
  isSetCode (pair i<j) (pair k<l) =
    isSet× (isProp→isSet (isSetFin _ _)) (isProp→isSet (isSetFin _ _))

  encode : (x y : DLShfDiagOb n) → DLShfDiagHom n x y → Code x y
  encode (sing _) .(sing _) idAr = refl
  encode (pair _) .(pair _) idAr = refl , refl
  encode .(sing _) .(pair _) singPairL = inl refl
  encode .(sing _) .(pair _) singPairR = inr refl

  decode : (x y : DLShfDiagOb n) → Code x y → DLShfDiagHom n x y
  decode (sing i) (sing j) p = subst (λ k → DLShfDiagHom _ (sing i) (sing k)) p idAr
  decode (sing i) (pair {j} {k} j<k) (inl p) =
    transp (λ ι → DLShfDiagHom _ (sing i) (pair (depPath ι))) i0 singPairL
      where
      i<k : i <Fin k
      i<k = subst (_<Fin k) (sym p) j<k
      depPath : PathP (λ ι → p ι <Fin k) i<k j<k
      depPath = isProp→PathP (λ _ → ≤FinIsPropValued _ _) _ _
  decode (sing i) (pair {k} {j} k<j) (inr p) =
    transp (λ ι → DLShfDiagHom _ (sing i) (pair (depPath ι))) i0 singPairR
      where
      k<i : k <Fin i
      k<i = subst (k <Fin_) (sym p) k<j
      depPath : PathP (λ ι → k <Fin p ι) k<i k<j
      depPath = isProp→PathP (λ _ → ≤FinIsPropValued _ _) _ _
  decode (pair {i} {j} i<j) (pair {k} {l} k<l) (p , q) =
    transp (λ ι → DLShfDiagHom _ (pair i<j) (pair (depPath ι))) i0 idAr
      where
      depPath : PathP (λ ι → p ι <Fin q ι) i<j k<l
      depPath = isProp→PathP (λ _ → ≤FinIsPropValued _ _) _ _

  codeRetract : ∀ (x y : DLShfDiagOb n) (f : DLShfDiagHom n x y)
              → decode x y (encode x y f) ≡ f
  codeRetract (sing i) (sing .i) idAr = transportRefl idAr
  codeRetract (sing i) (pair {.i} {k} i<k) singPairL ι₁ =
    transp (λ ι₂ → DLShfDiagHom _ (sing i) (pair (depPath (ι₁ ∨ ι₂)))) ι₁ singPairL
      where
      i<k' : i <Fin k
      i<k' = subst (_<Fin k) refl i<k
      depPath : PathP (λ _ → i <Fin k) i<k' i<k
      depPath = isProp→PathP (λ _ → ≤FinIsPropValued _ _) _ _

  codeRetract (sing i) (pair {j} {.i} j<i) singPairR ι₁ =
    transp (λ ι₂ → DLShfDiagHom _ (sing i) (pair (depPath (ι₁ ∨ ι₂)))) ι₁ singPairR
      where
      j<i' : j <Fin i
      j<i' = subst (j <Fin_) refl j<i
      depPath : PathP (λ ι → j <Fin i) j<i' j<i
      depPath = isProp→PathP (λ _ → ≤FinIsPropValued _ _) _ _

  codeRetract (pair {i} {j} i<j) (pair {.i} {.j} .i<j) idAr ι₁ = --hcomp {!!} {!!}
    transp (λ ι₂ → DLShfDiagHom _ (pair i<j) (pair (depPath (ι₁ ∨ ι₂)))) ι₁ {!!}
      where
      depPath : PathP (λ _ → i <Fin j) i<j i<j
      depPath = isProp→PathP (λ _ → ≤FinIsPropValued _ _) _ _

      partialInEq : i <Fin j
      partialInEq =
        (hcomp
        (λ { ι₂ (ι₁ = i0) → i<j
           ; ι₂ (ι₁ = i1)
               → ≤FinIsPropValued _ _ (transport (λ _ → i <Fin j) i<j) i<j ι₂
           })
        (transp (λ _ → i <Fin j) (~ ι₁) i<j))

  -- codeRetract (sing x) .(sing x) idAr = transportRefl idAr
  -- codeRetract (pair x) .(pair x) idAr = {!transportRefl idAr!}
  -- codeRetract .(sing _) .(pair _) singPairL ι = transp (λ ι2 → DLShfDiagHom _ (sing _)
  --        (pair (isProp→PathP (λ _ → ≤FinIsPropValued _ _) _ _ (ι ∨ ι2)))) ι singPairL
  -- codeRetract .(sing _) .(pair _) singPairR = {!!}
--   codeRetract (sing _) .(sing _) idAr = transportRefl idAr
--   codeRetract (pair _ _) .(pair _ _) idAr = transportRefl idAr
--   codeRetract .(sing _) .(pair _ _) singPairL = transportRefl singPairL
--   codeRetract .(sing _) .(pair _ _) singPairR = transportRefl singPairR

--   isSetDLShfDiagHom : ∀ (x y : DLShfDiagOb n) → isSet (DLShfDiagHom n x y)
--   isSetDLShfDiagHom x y = isSetRetract (encode x y) (decode x y)
--                                          (codeRetract x y) (isSetCode x y)



-- open Category
-- DLShfDiag : ℕ → Category ℓ-zero ℓ-zero
-- ob (DLShfDiag n) = DLShfDiagOb n
-- Hom[_,_] (DLShfDiag n) = DLShfDiagHom n
-- id (DLShfDiag n) = idAr
-- _⋆_ (DLShfDiag n) idAr f = f
-- _⋆_ (DLShfDiag n) singPairL idAr = singPairL
-- _⋆_ (DLShfDiag n) singPairR idAr = singPairR
-- ⋆IdL (DLShfDiag n) _ = refl
-- ⋆IdR (DLShfDiag n) idAr = refl
-- ⋆IdR (DLShfDiag n) singPairL = refl
-- ⋆IdR (DLShfDiag n) singPairR = refl
-- ⋆Assoc (DLShfDiag n) idAr _ _ = refl
-- ⋆Assoc (DLShfDiag n) singPairL idAr _ = refl
-- ⋆Assoc (DLShfDiag n) singPairR idAr _ = refl
-- isSetHom (DLShfDiag n) = let open DLShfDiagHomPath in (isSetDLShfDiagHom _ _)


-- module _ (L' : DistLattice ℓ) where
--  private
--   L = fst L'
--   LCat = (DistLatticeCategory L') ^op
--   instance
--    _ = snd L'

--  open DistLatticeStr ⦃...⦄
--  open Join L'
--  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L'))
--  open PosetStr (IndPoset .snd) hiding (_≤_)
--  open MeetSemilattice (Lattice→MeetSemilattice (DistLattice→Lattice L'))
--       using (∧≤RCancel ; ∧≤LCancel)
--  open Order (DistLattice→Lattice L')

--  open Category LCat
--  open Functor
--  open Cone


--  FinVec→Diag : {n : ℕ} → FinVec L n → Functor (DLShfDiag n) LCat
--  F-ob (FinVec→Diag α) (sing i) = α i
--  F-ob (FinVec→Diag α) (pair i j) = α i ∧l α j
--  F-hom (FinVec→Diag α) idAr = is-refl _
--  F-hom (FinVec→Diag α) singPairL = ≤m→≤j _ _ (∧≤RCancel _ _)
--  F-hom (FinVec→Diag α) singPairR = ≤m→≤j _ _ (∧≤LCancel _ _)
--  F-id (FinVec→Diag α) = is-prop-valued _ _ _ _
--  F-seq (FinVec→Diag α) _ _ = is-prop-valued _ _ _ _

--  ⋁Cone : {n : ℕ} (α : FinVec L n) → Cone (FinVec→Diag α) (⋁ α)
--  coneOut (⋁Cone α) (sing i) = ind≤⋁ α i
--  coneOut (⋁Cone α) (pair i j) = is-trans _ (α i) _ (≤m→≤j _ _ (∧≤RCancel _ _)) (ind≤⋁ α i)
--  coneOutCommutes (⋁Cone α) _ = is-prop-valued _ _ _ _

--  isLimCone⋁Cone : {n : ℕ} (α : FinVec L n) → isLimCone (FinVec→Diag α) (⋁ α) (⋁Cone α)
--  fst (fst (isLimCone⋁Cone α u uCone)) = ⋁IsMax α _ λ i → uCone .coneOut (sing i)
--  snd (fst (isLimCone⋁Cone α u uCone)) _ = is-prop-valued _ _ _ _
--  snd (isLimCone⋁Cone α _ uCone) _ = Σ≡Prop (λ _ → isPropIsConeMor uCone (⋁Cone α) _)
--                                            (is-prop-valued _ _ _ _)


-- module PullbacksAsDLShfDiags (C : Category ℓ ℓ')
--                              (cspan : Cospan C)
--                              (pback : Pullback C cspan) where

--  open Functor
--  open Cone
--  open Cospan ⦃...⦄
--  open Pullback ⦃...⦄
--  instance
--   _ = cspan
--   _ = pback

--  cospanAsDiag : Functor (DLShfDiag 2) C
--  F-ob cospanAsDiag (sing zero) = l
--  F-ob cospanAsDiag (sing (suc zero)) = r
--  F-ob cospanAsDiag (pair _ _) = m
--  F-hom cospanAsDiag idAr = id C
--  F-hom cospanAsDiag {x = sing zero} singPairL = s₁
--  F-hom cospanAsDiag {x = sing (suc zero)} singPairL = s₂
--  F-hom cospanAsDiag {x = sing zero} singPairR = s₁
--  F-hom cospanAsDiag {x = sing (suc zero)} singPairR = s₂
--  F-id cospanAsDiag = refl
--  F-seq cospanAsDiag idAr idAr = sym (⋆IdL C _)
--  F-seq cospanAsDiag idAr singPairL = sym (⋆IdL C _)
--  F-seq cospanAsDiag idAr singPairR = sym (⋆IdL C _)
--  F-seq cospanAsDiag singPairL idAr = sym (⋆IdR C _)
--  F-seq cospanAsDiag singPairR idAr = sym (⋆IdR C _)

--  pbPrAsCone : Cone cospanAsDiag pbOb
--  coneOut pbPrAsCone (sing zero) = pbPr₁
--  coneOut pbPrAsCone (sing (suc zero)) = pbPr₂
--  coneOut pbPrAsCone (pair _ _) = pbPr₁ ⋆⟨ C ⟩ s₁
--  coneOutCommutes pbPrAsCone idAr = ⋆IdR C _
--  coneOutCommutes pbPrAsCone (singPairL {zero}) = refl
--  coneOutCommutes pbPrAsCone (singPairL {suc zero}) = sym pbCommutes
--  coneOutCommutes pbPrAsCone (singPairR {zero}) = refl
--  coneOutCommutes pbPrAsCone (singPairR {suc zero}) = sym pbCommutes

--  pbAsLimit : isLimCone cospanAsDiag pbOb pbPrAsCone
--  pbAsLimit c cc = uniqueExists (fromPBUnivProp .fst .fst)
--                                toConeMor
--                                (λ _ → isPropIsConeMor cc pbPrAsCone _)
--                                (λ f cf → cong fst (fromPBUnivProp .snd (f , fromConeMor cf)))
--   where
--   fromPBUnivProp : ∃![ hk ∈ C [ c , Pullback.pbOb pback ] ]
--                       (coneOut cc (sing zero) ≡ hk ⋆⟨ C ⟩ pbPr₁) ×
--                       (coneOut cc (sing (suc zero)) ≡ hk ⋆⟨ C ⟩ pbPr₂)
--   fromPBUnivProp = univProp
--           (cc .coneOut (sing zero)) (cc .coneOut (sing (suc zero)))
--           (cc .coneOutCommutes singPairL ∙ sym (cc .coneOutCommutes singPairR))

--   toConeMor : isConeMor cc pbPrAsCone (fromPBUnivProp .fst .fst)
--   toConeMor (sing zero) = sym (fromPBUnivProp .fst .snd .fst)
--   toConeMor (sing (suc zero)) = sym (fromPBUnivProp .fst .snd .snd)
--   toConeMor (pair zero j) = path
--    where
--    path : fromPBUnivProp .fst .fst ⋆⟨ C ⟩ (pbPr₁ ⋆⟨ C ⟩ s₁) ≡ cc .coneOut (pair zero j)
--    path = fromPBUnivProp .fst .fst ⋆⟨ C ⟩ (pbPr₁ ⋆⟨ C ⟩ s₁)
--         ≡⟨ sym (⋆Assoc C _ _ _) ⟩
--           (fromPBUnivProp .fst .fst ⋆⟨ C ⟩ pbPr₁) ⋆⟨ C ⟩ s₁
--         ≡⟨ cong (λ f → f ⋆⟨ C ⟩ s₁) (sym (fromPBUnivProp .fst .snd .fst)) ⟩
--           cc .coneOut (sing zero) ⋆⟨ C ⟩ s₁
--         ≡⟨ cc .coneOutCommutes singPairL ⟩
--           cc .coneOut (pair zero j) ∎
--   toConeMor (pair (suc zero) j) = path
--    where
--    path : fromPBUnivProp .fst .fst ⋆⟨ C ⟩ (pbPr₁ ⋆⟨ C ⟩ s₁) ≡ cc .coneOut (pair (suc zero) j)
--    path = fromPBUnivProp .fst .fst ⋆⟨ C ⟩ (pbPr₁ ⋆⟨ C ⟩ s₁)
--         ≡⟨ cong (λ f → fromPBUnivProp .fst .fst ⋆⟨ C ⟩ f) pbCommutes ⟩
--           fromPBUnivProp .fst .fst ⋆⟨ C ⟩ (pbPr₂ ⋆⟨ C ⟩ s₂)
--         ≡⟨ sym (⋆Assoc C _ _ _) ⟩
--           (fromPBUnivProp .fst .fst ⋆⟨ C ⟩ pbPr₂) ⋆⟨ C ⟩ s₂
--         ≡⟨ cong (λ f → f ⋆⟨ C ⟩ s₂) (sym (fromPBUnivProp .fst .snd .snd)) ⟩
--           cc .coneOut (sing (suc zero)) ⋆⟨ C ⟩ s₂
--         ≡⟨ cc .coneOutCommutes singPairL ⟩
--           cc .coneOut (pair (suc zero) j) ∎

--   fromConeMor : {f : C [ c , pbOb ]}
--               → isConeMor cc pbPrAsCone f
--               → (coneOut cc (sing zero) ≡ f ⋆⟨ C ⟩ pbPr₁) ×
--                 (coneOut cc (sing (suc zero)) ≡ f ⋆⟨ C ⟩ pbPr₂)
--   fst (fromConeMor cf) = sym (cf (sing zero))
--   snd (fromConeMor cf) = sym (cf (sing (suc zero)))
