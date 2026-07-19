
{-

For an arbitrary type of generators:
 - `GroupIso-FG-L/↘↙` demonstrates that the free group defined as a HIT is equivalent to the definition based on quotienting lists by the appropriate relation (from `Cubical.Algebra.Group.Free`).

The following properties are defined with the assumption that the type of the generators is an hSet. Without this assumption, they can be adapted to be stated "modulo set truncation":

 - `isPropNF` ensures the uniqueness of the normal form.
 - `ηInj` establishes that the `η` constructor of FreeGroup is injective.
 - `NF⇔DiscreteA` indicates that computing the normal form is feasible if and only if the type of generators is discrete.
 - `discreteFreeGroup` asserts that if the generators are discrete, then the FreeGroup has decidable equality.

-}
module Cubical.HITs.FreeGroup.NormalForm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.HLevels

open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Free

open import Cubical.Data.List renaming (elim to elimList)
open import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.HITs.SetQuotients renaming
 (elimProp to elimProp/ ; _/_ to _/₂_ ; [_] to [_]/ ; rec to rec/)
open import Cubical.HITs.PropositionalTruncation renaming
 (rec to rec₁ ; map to map₁)


open import Cubical.HITs.FreeGroup.Base
open import Cubical.HITs.FreeGroup.Properties renaming (rec to recFreeGroup)

private
  variable
    ℓ : Level

module _ {A : Type ℓ} where

  open NormalForm A

  open NF (freeGroupGroup A) η renaming (inv to invFG)

  FG→L/↘↙ : GroupHom (freeGroupGroup A) (_ , List/↘↙GroupStr)
  FG→L/↘↙ = recFreeGroup ([_]/ ∘ [_] ∘ (true ,_))

  module gh/ = IsGroupHom (snd (FG→L/↘↙))
  open GroupTheory (freeGroupGroup A)

  open IsGroupHom

  ⇊1g→FG≡ : ∀ a → a ⇊1g → fromList a ≡ ε
  ⇊1g→FG≡ .[] [] = refl
  ⇊1g→FG≡ .(x ∷ (xs ∷ʳ not₁ x)) (cj x xs x₁) =
        cong (η* x ·fg_) (fromList· xs [ not₁ x ] ∙
          cong₂ _·fg_ (⇊1g→FG≡ xs x₁) (·IdR _) ∙ ·IdL _) ∙
           redex-ε-η* x (not₁ x) (symIsRedex _ _ refl)
  ⇊1g→FG≡ .(xs ++ ys) ((xs · ys) x x₁) = fromList· xs ys
      ∙∙ cong₂ _·fg_ (⇊1g→FG≡ _ x) (⇊1g→FG≡ _ x₁) ∙∙ ·IdL _

  fromListInv : (xs : List (Bool × A)) →
     fromList (invLi xs) ≡ invFG (fromList xs)
  fromListInv [] = sym (GroupTheory.inv1g (freeGroupGroup A))
  fromListInv (x ∷ xs) = (fromList· (invLi xs) _ ∙
           cong (fromList (invLi xs) ·fg_) (w' x))
        ∙∙ cong (_·fg invFG (η* x)) (fromListInv xs) ∙∙  sym (invDistr _ _)
   where
   w' : ∀ x → fromList [ not₁ x ] ≡ invFG (η* x)
   w' = λ { (false , a) → ·IdR _ ∙ sym (invInv _) ; (true , a) → ·IdR _ }

  fromL/ : List/↘↙ → _
  fromL/ = rec/ trunc fromList
    λ a b →
    _∙ (sym (fromListInv (invLi b))
            ∙ cong fromList (invol-invLi b)) ∘S invUniqueL
     ∘S sym (fromList· a (invLi b)) ∙_ ∘S ⇊1g→FG≡ _ ∘S ≡ε

  section-FG-L/↘↙ : ∀ a → fst (FG→L/↘↙) (fromList a) ≡ [ a ]/
  section-FG-L/↘↙ [] = refl
  section-FG-L/↘↙ (x ∷ xs) = gh/.pres· (η* x) (fromList xs) ∙
        cong (List/↘↙· (fst FG→L/↘↙ (η* x)))
          (section-FG-L/↘↙ xs) ∙ w x where
    w : ∀ x → List/↘↙· (fst FG→L/↘↙ (η* x)) [ xs ]/ ≡ [ x ∷ xs ]/
    w = λ { (false , a) → refl ; (true , a) → refl }

  isGroupHomFromL/ : IsGroupHom List/↘↙GroupStr fromL/ (snd (freeGroupGroup A))
  pres· isGroupHomFromL/ = elimProp2 (λ _ _ → trunc _ _) fromList·
  pres1 isGroupHomFromL/ = refl
  presinv isGroupHomFromL/ = elimProp/ (λ _ → trunc _ _) fromListInv

  GroupIso-FG-L/↘↙ : GroupIso (freeGroupGroup A) (List/↘↙group)
  Iso.fun (fst GroupIso-FG-L/↘↙) = fst FG→L/↘↙
  Iso.inv (fst GroupIso-FG-L/↘↙) = fromL/
  Iso.rightInv (fst GroupIso-FG-L/↘↙) =
     elimProp/ (λ _ → squash/ _ _) section-FG-L/↘↙
  Iso.leftInv (fst GroupIso-FG-L/↘↙) =
    funExt⁻ (congS fst (freeGroupHom≡
        {f = compGroupHom FG→L/↘↙ (fromL/ , isGroupHomFromL/)}
        {g = idGroupHom} (sym ∘ idr ∘ η )))
  snd GroupIso-FG-L/↘↙ = snd FG→L/↘↙

  module _ (isSetA : isSet A) where

   private
    isSet[𝟚×A] = isOfHLevelList 0 (isSet× isSetBool isSetA)

   isPropNF : ∀ g → isProp (NF g)
   isPropNF = λ g →
     λ (xs nf u , v) (xs' nf u' , v') →
      let zz = rec₁ (isSet[𝟚×A] xs xs')
                  (   sym
                   ∘S nf-uR _ _ (fst IsNormalisedInvLi v') v
                   ∘S ⇊1g++comm xs (invLi xs')
                   ∘S ≡ε )
                  (Iso.fun (≡→red xs xs') (
                    isoInvInjective (fst (GroupIso-FG-L/↘↙))
                    _ _ (u ∙ (sym u'))))
      in λ i → zz i
        nf isProp→PathP (λ i → trunc (fromList (zz i)) g) u u' i
         , isProp→PathP (λ i →  (isPropIsNormalised (zz i))) v v' i

   ηInj : ∀ a a' → Path (FreeGroup A) (η a) (η a') → a ≡ a'
   ηInj a a' =
         rec₁ (isSetA _ _)
           ((λ { (inl p) i → snd (p i)
               ; (inr (inl ())) ; (inr (inr ()))})
            ∘S ⇊1g⇒HasRedex _ _ ∘S ≡ε )
      ∘S Iso.fun (≡→red _ _)
      ∘S isoInvInjective (fst (GroupIso-FG-L/↘↙))
         [ [ true , _ ] ]/ [ [ true , _ ] ]/
      ∘S ·IdR _ ∙∙_∙∙ sym (·IdR _)

   NF-η : ∀ a → (nfa : NF (η a)) → [ true , a ] ≡ NF.word nfa
   NF-η a nfa = rec₁ (isSet[𝟚×A] _ _) (λ u →
    nf-uR _ _ (IsNormalised[x] (true , a))
     (NF.isNormalisedWord nfa) (⇊1g++comm _ [ false , a ] (≡ε u)))
      (Iso.fun (≡→red _ _) (isoInvInjective (fst (GroupIso-FG-L/↘↙))
             [ NF.word nfa ]/ [ [ (true , a) ] ]/
               (NF.fromListWord≡ nfa ∙ (sym (·IdR _)))))

   ΠNF⇒DiscreteA : (∀ g → NF g) → Discrete A
   ΠNF⇒DiscreteA nF a a' =
    let nff = nF (η a · invFG (η a'))
    in rec₁ (isPropDec (isSetA _ _))
       (λ r → ⊎.rec
         (yes ∘ sym ∘ cong snd)
         (no ∘ ⊎.rec (λ p pp → lower (subst (WillReduce false a)
         (isNormalised⇊1g _ (NF.isNormalisedWord nff)
          (pop⇊1gHead (cong (true ,_) (sym pp)) r)) p))
                      (const ∘ NF.isNormalisedWord nff))
           (⇊1g⇒HasRedex _ _ r))
        (map₁ (⇊1g++comm (NF.word nff) _ ∘ ≡ε)
        (Iso.fun (≡→red _ _) (isoInvInjective (fst (GroupIso-FG-L/↘↙))
             [ NF.word nff ]/ [ (true , a) ∷ [ false , a' ] ]/
               (NF.fromListWord≡ nff ∙ cong (η a ·_) (sym (·IdR _))))))

   NF⇔DiscreteA : (∀ g → NF g) ≃ Discrete A
   NF⇔DiscreteA = propBiimpl→Equiv (isPropΠ isPropNF) isPropDiscrete
     ΠNF⇒DiscreteA λ _≟_ g →
       let e = compIso (fst (GroupIso-FG-L/↘↙)) (invIso (Discrete.IsoNF _≟_))
           (g' , n) = Iso.fun e g
       in g' nf Iso.leftInv e g , n

  ≟→normalForm : Discrete A → (∀ g → NF g)
  ≟→normalForm _≟_ = invEq (NF⇔DiscreteA (Discrete→isSet _≟_)) _≟_

  discreteFreeGroup : Discrete A → Discrete (FreeGroup A)
  discreteFreeGroup _≟_ =
    isoPresDiscrete
      (compIso
         (Discrete.IsoNF _≟_)
         (invIso (fst (GroupIso-FG-L/↘↙))))
      (discreteΣProp
        (discreteList (discreteΣ 𝟚._≟_ λ _ → _≟_))
        isPropIsNormalised)
