{-

Bijective Relations ([BijectiveRel])

- Path to BijectiveRel ([pathToBijectiveRel])
- BijectiveRel is equivalent to Equiv ([BijectiveRel≃Equiv])

-}
module Cubical.Foundations.Equiv.BijectiveRel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Univalence.Dependent
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv
open import Cubical.Relation.Binary
open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv
open import Cubical.Data.Sigma

private variable
  ℓ ℓ' ℓ'' : Level
  A B C : Type ℓ
  R S : Rel A B ℓ

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

BijectiveRelIsoΣ : Iso (BijectiveRel A B ℓ'') (Σ[ R ∈ Rel A B ℓ'' ] isFunctionalRel R × isFunctionalRel (flip R))
BijectiveRelIsoΣ = Σ-cong-iso-snd λ _ → isBijectiveRelIsoΣ

BijectiveRelPathP : {A : I → Type ℓ} {B : I → Type ℓ'} {R₀ : BijectiveRel (A i0) (B i0) ℓ''} {R₁ : BijectiveRel (A i1) (B i1) ℓ''}
                  → PathP (λ i → Rel (A i) (B i) ℓ'') (R₀ .fst) (R₁ .fst)
                  → PathP (λ i → BijectiveRel (A i) (B i) ℓ'') R₀ R₁
BijectiveRelPathP = ΣPathPProp λ _ → isPropIsBijectiveRel

BijectiveRelEq : {R₀ R₁ : BijectiveRel A B ℓ''} → (∀ a b → R₀ .fst a b ≃ R₁ .fst a b) → R₀ ≡ R₁
BijectiveRelEq h = BijectiveRelPathP (funExt₂ λ a b → ua (h a b))

BijectiveRel→Equiv : BijectiveRel A B ℓ → A ≃ B
BijectiveRel→Equiv R .fst a = R .snd .rContr a .fst .fst
BijectiveRel→Equiv (R , Rbij) .snd .equiv-proof b = flip (isOfHLevelRetractFromIso 0) (Rbij .lContr b) $
  Σ-cong-iso-snd $ invIso ∘ flip isIdentitySystem.isoPath b ∘ isContrTotal→isIdentitySystem ∘ Rbij .rContr

EquivIsoBijectiveRel : (A B : Type ℓ) → Iso (A ≃ B) (BijectiveRel A B ℓ)
EquivIsoBijectiveRel A B .Iso.fun e .fst = graphRel (e .fst)
EquivIsoBijectiveRel A B .Iso.fun e .snd .rContr a = isContrSingl (e .fst a)
EquivIsoBijectiveRel A B .Iso.fun e .snd .lContr = e .snd .equiv-proof
EquivIsoBijectiveRel A B .Iso.inv = BijectiveRel→Equiv
EquivIsoBijectiveRel A B .Iso.rightInv (R , Rbij) = sym $ BijectiveRelEq $
  isIdentitySystem.equivPath ∘ isContrTotal→isIdentitySystem ∘ Rbij .rContr
EquivIsoBijectiveRel A B .Iso.leftInv e = equivEq refl

Equiv≃BijectiveRel : (A B : Type ℓ) → (A ≃ B) ≃ (BijectiveRel A B ℓ)
Equiv≃BijectiveRel A B = isoToEquiv (EquivIsoBijectiveRel A B)

isBijectiveIdRel : isBijectiveRel (idRel A)
isBijectiveIdRel .rContr = isContrSingl
isBijectiveIdRel .lContr = isContrSingl'

idBijectiveRel : BijectiveRel A A _
idBijectiveRel = _ , isBijectiveIdRel

isBijectiveInvRel : isBijectiveRel R → isBijectiveRel (invRel R)
isBijectiveInvRel Rbij .rContr = Rbij .lContr
isBijectiveInvRel Rbij .lContr = Rbij .rContr

invBijectiveRel : BijectiveRel A B ℓ' → BijectiveRel B A ℓ'
invBijectiveRel (_ , Rbij) = _ , isBijectiveInvRel Rbij

isBijectiveCompRel : isBijectiveRel R → isBijectiveRel S → isBijectiveRel (compRel R S)
isBijectiveCompRel Rbij Sbij .rContr = isFunctionalCompRel   (Rbij .rContr) (Sbij .rContr)
isBijectiveCompRel Rbij Sbij .lContr = isCofunctionalCompRel (Rbij .lContr) (Sbij .lContr)

compBijectiveRel : BijectiveRel A B ℓ → BijectiveRel B C ℓ' → BijectiveRel A C _
compBijectiveRel (_ , Rbij) (_ , Sbij) = _ , isBijectiveCompRel Rbij Sbij

isBijectivePathP : (A : I → Type ℓ) → isBijectiveRel (PathP A)
isBijectivePathP A .rContr = isContrSinglP A
isBijectivePathP A .lContr = isContrSinglP' A

pathToBijectiveRel : A ≡ B → BijectiveRel A B _
pathToBijectiveRel P = _ , isBijectivePathP λ i → P i

BijectiveRelToPath : BijectiveRel A B ℓ → A ≡ B
BijectiveRelToPath R = ua (BijectiveRel→Equiv R)

path→BijectiveRel→Equiv : (P : A ≡ B) → BijectiveRel→Equiv (pathToBijectiveRel P) ≡ pathToEquiv P
path→BijectiveRel→Equiv P = equivEq refl

pathIsoBijectiveRel : Iso (A ≡ B) (BijectiveRel A B _)
pathIsoBijectiveRel .Iso.fun = pathToBijectiveRel
pathIsoBijectiveRel .Iso.inv = BijectiveRelToPath
pathIsoBijectiveRel .Iso.rightInv R = BijectiveRelEq λ a b → compEquiv (ua-ungluePath-Equiv _) $
  invEquiv $ isIdentitySystem.equivPath (isContrTotal→isIdentitySystem $ R .snd .rContr a) b
pathIsoBijectiveRel .Iso.leftInv P = cong ua (path→BijectiveRel→Equiv P) ∙ ua-pathToEquiv P

path≡BijectiveRel : (A ≡ B) ≡ BijectiveRel A B _
path≡BijectiveRel = isoToPath pathIsoBijectiveRel
