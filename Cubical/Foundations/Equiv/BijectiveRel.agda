{-

Bijective Relations ([BijectiveRel])

- Path to BijectiveRel ([pathToBijectiveRel])
- BijectiveRel is equivalent to Equiv ([BijectiveRel≃Equiv])

-}
module Cubical.Foundations.Equiv.BijectiveRel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Relation.Binary
open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'

open HeterogenousRelation

record isBijectiveRel {A : Type ℓ} {B : Type ℓ'} (R : Rel A B ℓ'') : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
  field
    rContr : isFunctionalRel R
    lContr : isFunctionalRel (flip R)

open isBijectiveRel

unquoteDecl isBijectiveRelIsoΣ = declareRecordIsoΣ isBijectiveRelIsoΣ (quote isBijectiveRel)

isPropIsBijectiveRel : {R : Rel A B ℓ''} → isProp (isBijectiveRel R)
isPropIsBijectiveRel x y i .rContr a = isPropIsContr (x .rContr a) (y .rContr a) i
isPropIsBijectiveRel x y i .lContr a = isPropIsContr (x .lContr a) (y .lContr a) i

BijectiveRel : ∀ (A : Type ℓ) (B : Type ℓ') ℓ'' → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ''))
BijectiveRel A B ℓ'' = Σ[ R ∈ Rel A B ℓ'' ] isBijectiveRel R

BijectiveRelPathP : {A : I → Type ℓ} {B : I → Type ℓ'} {R₀ : BijectiveRel (A i0) (B i0) ℓ''} {R₁ : BijectiveRel (A i1) (B i1) ℓ''}
                  → PathP (λ i → A i → B i → Type ℓ'') (R₀ .fst) (R₁ .fst) → PathP (λ i → BijectiveRel (A i) (B i) ℓ'') R₀ R₁
BijectiveRelPathP = ΣPathPProp λ _ → isPropIsBijectiveRel

BijectiveRelEq : {R₀ R₁ : BijectiveRel A B ℓ''} → R₀ .fst ≡ R₁ .fst → R₀ ≡ R₁
BijectiveRelEq = Σ≡Prop λ _ → isPropIsBijectiveRel

BijectiveRelIsoΣ : Iso (BijectiveRel A B ℓ'') (Σ[ R ∈ Rel A B ℓ'' ] isFunctionalRel R × isFunctionalRel (flip R))
BijectiveRelIsoΣ = Σ-cong-iso-snd λ _ → isBijectiveRelIsoΣ

EquivIsoBijectiveRel : (A B : Type ℓ) → Iso (A ≃ B) (BijectiveRel A B ℓ)
EquivIsoBijectiveRel A B = 
  (A ≃ B)                                                                 Iso⟨ Σ-cong-iso-snd isEquiv-isEquiv'-Iso ⟩
  (Σ[ f ∈ (A → B) ] (∀ a → isContr (fiber f a)))                          Iso⟨ Σ-cong-iso-fst (invIso (FunctionalRelIsoFunction A B)) ⟩
  (Σ[ (R , _) ∈ Σ (Rel A B _) isFunctionalRel ] isFunctionalRel (flip R)) Iso⟨ Σ-assoc-Iso ⟩
  (Σ[ R ∈ Rel A B _ ] isFunctionalRel R × isFunctionalRel (flip R))       Iso⟨ invIso BijectiveRelIsoΣ ⟩
  BijectiveRel A B _                                                     ∎Iso

Equiv≃BijectiveRel : (A B : Type ℓ) → (A ≃ B) ≃ (BijectiveRel A B ℓ)
Equiv≃BijectiveRel A B = isoToEquiv (EquivIsoBijectiveRel A B)

isBijectiveIdRel : isBijectiveRel (idRel A)
isBijectiveIdRel .rContr = isContrSingl
isBijectiveIdRel .lContr = isContrSingl'

idBijectiveRel : BijectiveRel A A _
idBijectiveRel = _ , isBijectiveIdRel

isBijectiveInvRel : {R : Rel A B ℓ'} → isBijectiveRel R → isBijectiveRel (invRel R)
isBijectiveInvRel Rbij .rContr = Rbij .lContr
isBijectiveInvRel Rbij .lContr = Rbij .rContr

invBijectiveRel : BijectiveRel A B ℓ' → BijectiveRel B A ℓ'
invBijectiveRel (_ , Rbij) = _ , isBijectiveInvRel Rbij

isBijectivePathP : (A : I → Type ℓ) → isBijectiveRel (PathP A)
isBijectivePathP A .rContr = isContrSinglP A
isBijectivePathP A .lContr = isContrSinglP' A

pathToBijectiveRel : A ≡ B → BijectiveRel A B _
pathToBijectiveRel P = _ , isBijectivePathP λ i → P i
