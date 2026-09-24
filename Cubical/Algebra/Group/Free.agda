
{-

This module introduces a way to represent elements of free groups as lists of pairs ([𝟚× A]), where A identifies generators and Bool differentiates a generator from its inverse.


The definition of `_⇊1g` encodes the concept of a word being equivalent to the identity element in a free group. It includes three constructors:
 - The trivial case `[]` represents the identity itself.
 - The `cj` constructor signifies conjugation by a generator, indicating that a word extended by a generator and its inverse is still equivalent to the identity.
 - Lastly, the `_·_` constructor asserts that if two words are each equivalent to the identity, their concatenation will also be equivalent to the identity, preserving the identity property under the group operation.

Then, a `_·_⁻¹≡ε relation`, defined as `λ xs ys → (xs ++ invLi ys) ⇊1g`  captures the relationship where the concatenation of a word with the inverse of another equates to the group identity.

By quotienting by _·_⁻¹≡ε, resulting in the List/↘↙group, a group structure on equivalence classes of lists is established. Here, concatenation acts as the group operation, hence forming the foundation for the free group constructed over A.

Given that _·_⁻¹≡ε functions is equivalence relation, it permits the retrieval of this relationship from paths in the quotient. This feature facilitates the proof of the uniqueness of the normal form in `Cubical.HITs.FreeGroup.NormalForm`.

In the Discrete module, the presence of decidable equality on the type of generators (A) enables the definition of groups without requiring truncation. This utility is used in `Cubical.HITs.Bouquet.Discrete` to demonstrate that a bouquet over a discrete type is an hGroupoid without truncation.

-}

module Cubical.Algebra.Group.Free where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_)
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Data.List as Li

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Functions.Involution

open import Cubical.Algebra.Group

open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/₂_ ; [_] to [_]/)



private
  variable
    ℓ : Level

[𝟚×_] : (A : Type ℓ) → Type ℓ
[𝟚×_] = List ∘ (Bool ×_)

module NormalForm (A : Type ℓ) where

 -- Below we are defining predicate `HasRedex` over `List (Bool × A)`
 -- basing it on presence of sublist - REDucible EXpression of form [(b , x) , (not b , x)]

 not₁ : (Bool × A) → (Bool × A)
 not₁ = map-fst not

 not₁not₁ : ∀ x → not₁ (not₁ x) ≡ x
 not₁not₁ (x , y) = cong (_, y) (notnot x)

 IsRedex : Bool × A → Bool × A → Type ℓ
 IsRedex x x' = x ≡ not₁ x'

 symIsRedex : ∀ x y → IsRedex x y → IsRedex y x
 symIsRedex x y p = sym (not₁not₁ _) ∙ cong not₁ (sym p)

 WillReduce : Bool → A → (xs : [𝟚× A ]) → Type ℓ
 WillReduce _ _ [] = ⊥*
 WillReduce b x (h ∷ _) = IsRedex (b , x) h

 HeadIsRedex : [𝟚× A ] → Type ℓ
 HeadIsRedex [] = ⊥*
 HeadIsRedex ((b , a) ∷ xs) = WillReduce b a xs

 HasRedex : [𝟚× A ] → Type ℓ
 HasRedex [] = ⊥*
 HasRedex xs@(_ ∷ xs') = HeadIsRedex xs ⊎ HasRedex xs'

 HasRedex∷ʳ : ∀ {xs} {x} → HasRedex xs → HasRedex (xs ∷ʳ x)
 HasRedex∷ʳ {x₂ ∷ xs} (inr x₁) = inr (HasRedex∷ʳ x₁)
 HasRedex∷ʳ {x₂ ∷ x₃ ∷ xs} (inl x₁) = inl x₁

 HasRedex++ : ∀ xs ys → HasRedex xs → HasRedex (xs ++ ys)
 HasRedex++ (x₁ ∷ xs) ys (inr x) = inr (HasRedex++ xs ys x)
 HasRedex++ (x₁ ∷ x₂ ∷ xs) ys (inl x) = inl x

 ++HasRedex : ∀ xs ys → HasRedex ys → HasRedex (xs ++ ys)
 ++HasRedex [] ys x = x
 ++HasRedex (x₁ ∷ xs) ys x =
   inr (++HasRedex xs ys x)

 -- We use absence of redexes as property of representing normalised term

 IsNormalised : [𝟚× A ] → Type ℓ
 IsNormalised xs = (¬ HasRedex xs)

 isPropIsNormalised : ∀ xs → isProp (IsNormalised xs)
 isPropIsNormalised xs = isProp¬ _


 IsNormalised[] : IsNormalised []
 IsNormalised[] = lower

 IsNormalised[x] : ∀ x → IsNormalised [ x ]
 IsNormalised[x] _ = ⊎.rec lower lower

 IsNormalisedTail : ∀ xs → IsNormalised xs → IsNormalised (tail xs)
 IsNormalisedTail [] n = n
 IsNormalisedTail (x ∷ xs) = _∘ inr

 ¬IsRedex→IsNormalisedPair :
   ∀ {x x'} → ¬ IsRedex x x' → IsNormalised (x ∷ [ x' ])
 ¬IsRedex→IsNormalisedPair {x' = x'} ¬ir = ⊎.rec ¬ir (IsNormalised[x] x')

 invLi : [𝟚× A ] → [𝟚× A ]
 invLi = rev ∘ Li.map (map-fst not)

 invLi++ : ∀ xs ys → invLi (xs ++ ys) ≡
                 invLi ys ++ invLi xs
 invLi++ xs ys =
   sym (cong rev (map++ _ xs ys)) ∙
     rev-++ (Li.map _ xs) (Li.map _ ys)

 invol-invLi : isInvolution invLi
 invol-invLi xs =
  sym (rev-map-comm (map-fst not) (invLi xs)) ∙
    cong (Li.map (map-fst not))
      (rev-rev (Li.map (map-fst not) xs))
     ∙ map-∘ (map-fst not) (map-fst not) xs ∙
     (λ i → Li.map (map-fst (λ x → notnot x i) ) xs) ∙ map-id xs

 HasRedexInvLi : ∀ {xs} → HasRedex xs → HasRedex (invLi xs)
 HasRedexInvLi {_ ∷ []} x = x
 HasRedexInvLi {x₁ ∷ x₂ ∷ xs} = ⊎.rec
  (subst HasRedex (sym (++-assoc (invLi xs) _ _))
     ∘S ++HasRedex (invLi xs) (_ ∷ _)
     ∘S inl ∘S cong not₁  ∘S symIsRedex _ _ )
  (HasRedex∷ʳ ∘S HasRedexInvLi)


 IsNormalisedInvLi : ∀ {xs} → IsNormalised xs ≃ IsNormalised (invLi xs)
 IsNormalisedInvLi = propBiimpl→Equiv (isPropIsNormalised _) (isPropIsNormalised _)
  (_∘S subst HasRedex (invol-invLi _) ∘S HasRedexInvLi)
  (_∘S HasRedexInvLi)

 HasRedexSplit++ : ∀ {xs ys} → HasRedex (xs ++ ys) →
        HasRedex (take 1 (rev xs) ++ take 1 ys) ⊎
            (HasRedex xs ⊎ HasRedex ys)
 HasRedexSplit++ {[]} = inr ∘ inr
 HasRedexSplit++ {x ∷ []} {[]} r = ⊥.rec (IsNormalised[x] x r)
 HasRedexSplit++ {x ∷ []} {x₁ ∷ ys} = ⊎.rec (inl ∘ inl) (inr ∘ inr)
 HasRedexSplit++ {x ∷ x₁ ∷ xs} {ys} =
   ⊎.rec (inr ∘ inl ∘ inl)
    (⊎.rec (inl ∘ subst (λ zz → HasRedex (zz ++ take 1 ys))
     (w _ (subst (0 <ᵗ_) (+-comm 1 _ ∙ sym (length++ (rev xs) _)) _)))
      (⊎.rec (inr ∘ inl ∘ inr) (inr ∘ inr) ) ∘S HasRedexSplit++ {x₁ ∷ xs} {ys})
  where
  w : ∀ xs → 0 <ᵗ length xs → take 1 xs ≡ take 1 (xs ++ [ x ])
  w (x ∷ xs) _ = refl

 -- This predicate, is encoding fact that given list reduces to [],
 -- meaning that if interpreted as term of free group it would be equall to 1g

 infixl 10 _⇊1g

 data _⇊1g : [𝟚× A ] → Type ℓ where
  [] : [] ⇊1g
  cj : ∀ x → ∀ xs → xs ⇊1g →   (x ∷ (xs ∷ʳ not₁ x) ) ⇊1g
  _·_ : ∀ xs ys → xs ⇊1g → ys ⇊1g →  (xs ++ ys) ⇊1g

 _r·_ : ∀ {xs ys} → xs ⇊1g → ys ⇊1g → (xs ++ ys) ⇊1g
 _r·_ = _·_ _ _

 ¬⇊1g[len≡1] : ∀ xs → length xs ≡ 1 → ¬ xs ⇊1g
 ¬⇊1g[len≡1] .[] x [] = znots x
 ¬⇊1g[len≡1] .(_ ∷ (_ ∷ʳ _)) x (cj _ xs _) =
   snotz ((+-comm 1 _ ∙ sym (length++ xs _)) ∙ injSuc x)
 ¬⇊1g[len≡1] .(xs ++ ys) x ((xs · ys) x₁ x₂) =
  ⊎.rec (flip (¬⇊1g[len≡1] ys) x₂ ∘ snd)
        ((flip (¬⇊1g[len≡1] xs) x₁ ∘ fst))
    (m+n≡1→m≡0×n≡1⊎m≡1n≡0 {length xs} {length ys} (sym (length++ xs ys) ∙ x))

 ⇊1gWillReduceView : ∀ b a ys → ys ⇊1g → WillReduce b a ys →
      Σ ((Σ _ _⇊1g) × (Σ _ _⇊1g))
        λ ((rl , _) , (rr , _)) →
           rl ++ [ b , a ] ++ rr ≡ tail ys
 ⇊1gWillReduceView b a .(x ∷ (xs ∷ʳ _)) (cj x xs x₃) x₁ =
   ((_ , x₃) , (_ , [])) , cong (xs ∷ʳ_) x₁
 ⇊1gWillReduceView b a .([] ++ ys) (([] · ys) x x₂) x₁ =
   ⇊1gWillReduceView b a ys x₂ x₁
 ⇊1gWillReduceView b a .((_ ∷ _) ++ ys) ((xs@(_ ∷ _) · ys) x x₂) x₁ =
   let (((rl , rlR) , (rr , rrR)) , p) = ⇊1gWillReduceView b a xs x x₁
   in ((_ , rlR) , (_ , (_ · _) rrR x₂)) ,
     sym (++-assoc rl _ _) ∙ cong (_++ ys) p

 ⇊1g⇒HasRedex : ∀ xs → 0 <ᵗ length xs → xs ⇊1g → HasRedex xs
 ⇊1g⇒HasRedex .(x₁ ∷ ([] ∷ʳ not₁ x₁)) x (cj x₁ [] x₂) =
   inl (symIsRedex _ _ refl)
 ⇊1g⇒HasRedex .(x₁ ∷ ((x₃ ∷ xs) ∷ʳ not₁ x₁)) x (cj x₁ (x₃ ∷ xs) x₂) =
   inr (HasRedex∷ʳ (⇊1g⇒HasRedex _ _ x₂))
 ⇊1g⇒HasRedex .([] ++ ys) x (([] · ys) x₁ x₂) = ⇊1g⇒HasRedex _ x x₂
 ⇊1g⇒HasRedex .((x₃ ∷ xs) ++ ys) x (((x₃ ∷ xs) · ys) x₁ x₂) =
  HasRedex++ _ _ (⇊1g⇒HasRedex _ _ x₁)

 isNormalised⇊1g : ∀ xs → IsNormalised xs →  xs ⇊1g → xs ≡ []
 isNormalised⇊1g [] _ _ = refl
 isNormalised⇊1g (x₂ ∷ xs) x x₁ = ⊥.rec (x (⇊1g⇒HasRedex _ _ x₁))


 ⇊1g-invLi : ∀ {xs} → xs ⇊1g → (invLi xs) ⇊1g
 ⇊1g-invLi [] = []
 ⇊1g-invLi (cj x xs x₁) =
   subst _⇊1g (cong (_∷ invLi (x ∷ xs)) (sym (not₁not₁ _) )
    ∙ cong (_∷ʳ _) (sym (invLi++ xs [ not₁ x ]))) (cj x _ (⇊1g-invLi x₁))
 ⇊1g-invLi ((xs · ys) x x₁) =
   subst _⇊1g (sym (invLi++ xs ys)) (⇊1g-invLi x₁ r· ⇊1g-invLi x)

 ⇊1gRot : ∀ xs → xs ⇊1g → _⇊1g (rot xs)
 ⇊1gRot [] x = []
 ⇊1gRot xs@(x'@(b , a) ∷ xs') x =
  let (((rl , rlR) , (rr , rrR)) , p) = ⇊1gWillReduceView (not b) a xs x refl
  in subst _⇊1g ((λ i → (++-assoc rl ([ not b , a ] ++ rr)
               [ not₁not₁ x' i ]) (~ i)) ∙ cong (_∷ʳ x') p)
       (rlR r· cj (not b , a) _ rrR)

 ⇊1g++comm : ∀ xs ys → (xs ++ ys) ⇊1g → (ys ++ xs) ⇊1g
 ⇊1g++comm [] ys = subst _⇊1g (sym (++-unit-r ys))
 ⇊1g++comm (x₁ ∷ xs) ys x =
   subst _⇊1g (++-assoc ys _ _)
      (⇊1g++comm xs _ (subst _⇊1g (++-assoc xs _ _) (⇊1gRot _ x)))

 pop⇊1gHead : ∀ {xs} → HeadIsRedex xs → xs ⇊1g → _⇊1g (tail (tail xs))
 pop⇊1gHead x (cj x₁ [] r) = []
 pop⇊1gHead x (cj x₁ (x₂ ∷ xs) r) =
   subst (_⇊1g ∘ (xs ∷ʳ_)) (symIsRedex _ _ x) (⇊1gRot _ r)
 pop⇊1gHead x (([] · ys) r r₁) = pop⇊1gHead x r₁
 pop⇊1gHead x (((x₁ ∷ []) · ys) r r₁) = ⊥.rec (¬⇊1g[len≡1] [ x₁ ] refl r)
 pop⇊1gHead x (((_ ∷ _ ∷ _) · ys) r r₁) = pop⇊1gHead x r r· r₁

 ⇊1gCJ : ∀ xs ys → _⇊1g (ys ++ xs ++ invLi ys) → xs ⇊1g
 ⇊1gCJ xs [] = subst _⇊1g (++-unit-r xs)
 ⇊1gCJ xs (x₁ ∷ ys) x =
  ⇊1gCJ xs ys (pop⇊1gHead refl
   (⇊1g++comm (x₁ ∷ ys ++ xs ++ invLi ys) [ not₁ x₁ ]
    (subst _⇊1g (cong (x₁ ∷_) (cong (ys ++_) (sym (++-assoc xs _ _))
           ∙ sym (++-assoc ys _ _))) x)))

 nf-uR : ∀ xs ys
    → IsNormalised (invLi xs)
    → IsNormalised ys
    → (invLi xs ++ ys) ⇊1g → xs ≡ ys
 nf-uR xs [] nXs x₁ r = sym (invol-invLi xs) ∙ cong invLi
      (isNormalised⇊1g _ nXs (subst _⇊1g (++-unit-r _) r))
 nf-uR [] (x₃ ∷ ys) x x₁ x₂ = ⊥.rec (x₁ (⇊1g⇒HasRedex _ _ x₂))
 nf-uR xs@(_ ∷ _) (x₃ ∷ ys) nXs nYs r =
   let ww = subst _⇊1g (cong (x₃ ∷_) (sym (++-assoc ys _ _)))
              (⇊1g++comm (invLi xs) _ r)
       www = subst (0 <ᵗ_)
           (sym (+-suc _ _)
             ∙ sym (length++ (invLi xs) _)) _
   in (⊎.rec (⊎.rec (λ p → cong₂ _∷_
          (sym (not₁not₁ _) ∙ sym (symIsRedex _ _ p))
          (nf-uR (tail xs) _ (fst IsNormalisedInvLi
             (invEq (IsNormalisedInvLi {xs}) nXs ∘ inr) ) (nYs ∘ inr)
               (⇊1g++comm _ (invLi (tail xs))
                  (pop⇊1gHead p (⇊1g++comm _ [ _ ] ww)))))
        (⊥.rec ∘ IsNormalised[x] x₃) ∘S
       subst HasRedex (cong ((_++ _) ∘ take 1)
         (rev-rev (Li.map not₁ xs))))
        (⊥.rec ∘ ⊎.rec nXs nYs)
    ∘S HasRedexSplit++ {invLi xs}
    ∘S ⇊1g⇒HasRedex _ www) r

 infixr 5 _·_⁻¹≡ε

 -- We are defining this relation using record
 -- to help later definitions infer implicit arguments.
 -- With the help of earlier lemmas, we can prove that it is EquivRel,
 -- wich lets us recover witness of this relation from path in SetQuotent

 record _·_⁻¹≡ε (xs ys : _) : Type ℓ where
  constructor [_]≡ε
  field
   ≡ε :  (xs ++ invLi ys) ⇊1g

 open _·_⁻¹≡ε public

 open BinaryRelation
 open isEquivRel

 ·⁻¹≡ε-refl : isRefl _·_⁻¹≡ε
 ·⁻¹≡ε-refl [] = [ [] ]≡ε
 ≡ε (·⁻¹≡ε-refl (x ∷ xs)) =
   subst _⇊1g (sym (++-assoc [ x ] xs (invLi (x ∷ xs)) ∙
         cong (x ∷_) (sym (++-assoc xs (invLi xs) _))))
     (cj x _ (≡ε (·⁻¹≡ε-refl xs)))

 ·⁻¹≡ε-sym : isSym _·_⁻¹≡ε
 ≡ε (·⁻¹≡ε-sym a b [ p ]≡ε) =
    subst _⇊1g (invLi++ a (invLi b) ∙
       cong (_++ invLi a) (invol-invLi b)) (⇊1g-invLi p)

 ·⁻¹≡ε-trans : isTrans _·_⁻¹≡ε
 ≡ε (·⁻¹≡ε-trans xs ys zs [ p ]≡ε [ q ]≡ε) =
    ⇊1g++comm (invLi zs) xs
      (⇊1gCJ (invLi zs ++ xs) ys
        (subst _⇊1g (++-assoc ys _ _ ∙
         cong (ys ++_) (sym (++-assoc (invLi zs) _ _))) (q r· p)))

 ·⁻¹≡ε-isEquivRel : isEquivRel _·_⁻¹≡ε
 reflexive ·⁻¹≡ε-isEquivRel = ·⁻¹≡ε-refl
 symmetric ·⁻¹≡ε-isEquivRel = ·⁻¹≡ε-sym
 transitive ·⁻¹≡ε-isEquivRel = ·⁻¹≡ε-trans

 ≡→red : ∀ a b → Iso ([ a ]/ ≡ [ b ]/) ∥ a · b ⁻¹≡ε ∥₁
 ≡→red = isEquivRel→TruncIso ·⁻¹≡ε-isEquivRel


 open Iso


 _↘↙_ = _·_⁻¹≡ε

 List/↘↙ : Type ℓ
 List/↘↙ = _ /₂ _·_⁻¹≡ε


 -- concatenation of lists, respects `_·_⁻¹≡ε` on both sides,
 -- so we can give SetQuotiening by _·_⁻¹≡ε  structure of a group
 -- by taking concatenation as group operation

 _↘↙++↘↙_ : ∀ {xsL xsR ysL ysR} →
    xsL ↘↙ ysL → xsR ↘↙ ysR →
      (xsL ++ xsR) ↘↙ (ysL ++ ysR)
 ≡ε (_↘↙++↘↙_ {xsL} {xsR} {ysL} {ysR} [ p ]≡ε [ q ]≡ε) =
   subst _⇊1g (sym (++-assoc xsL _ _))
     (⇊1g++comm _ xsL
       (subst _⇊1g (++-assoc xsR _ _ ∙∙
           (λ i → xsR ++ ++-assoc (invLi ysR) (invLi ysL) xsL (~ i)) ∙∙
           ( λ i → ++-assoc xsR (invLi++ ysL ysR (~ i)) xsL (~ i)))
         (q r· ⇊1g++comm xsL _ p)))

 List/↘↙· : List/↘↙ → List/↘↙ → List/↘↙
 List/↘↙· =  SQ.rec2 squash/ (λ a b → [ a ++ b ]/)
    (λ _ _ c → eq/ _ _ ∘ _↘↙++↘↙ (·⁻¹≡ε-refl c))
    (λ a _ _ → eq/ _ _ ∘ (·⁻¹≡ε-refl a) ↘↙++↘↙_ )

 List/↘↙GroupStr : GroupStr List/↘↙
 GroupStr.1g List/↘↙GroupStr = [ [] ]/
 GroupStr._·_ List/↘↙GroupStr = List/↘↙·
 GroupStr.inv List/↘↙GroupStr =
  SQ.rec squash/ ([_]/ ∘ invLi)
     λ xs ys → sym ∘S eq/ _ _ ∘S [_]≡ε
     ∘S subst (_⇊1g ∘ (invLi ys ++_)) (sym (invol-invLi xs))
     ∘S ⇊1g++comm xs (invLi ys) ∘S ≡ε

 GroupStr.isGroup List/↘↙GroupStr = makeIsGroup squash/
  (SQ.elimProp3 (λ _ _ _ → squash/ _ _)
      λ xs _ _ → cong [_]/ (sym (++-assoc xs _ _)))
  (SQ.elimProp (λ _ → squash/ _ _) λ xs → cong [_]/ (++-unit-r xs))
  (SQ.elimProp (λ _ → squash/ _ _) λ _ → refl)
  (SQ.elimProp (λ _ → squash/ _ _) λ xs → sym (eq/ _ _
     ([ ⇊1g-invLi (≡ε (·⁻¹≡ε-refl xs)) ]≡ε)))
  (SQ.elimProp (λ _ → squash/ _ _) λ xs → eq/ _ _ [
     subst _⇊1g (cong (invLi xs ++_) (invol-invLi xs) ∙
       sym (++-unit-r _)) (≡ε (·⁻¹≡ε-refl (invLi xs))) ]≡ε)

 List/↘↙group : Group ℓ
 List/↘↙group = _ , List/↘↙GroupStr



 module Discrete (_≟_ : Discrete A) where

  -- For discrete set of generators, we can compute normal form,
  -- and proove `Iso (Σ _  IsNormalised) List/↘↙`

  isSetA = Discrete→isSet _≟_

  isSet[𝟚×] = isOfHLevelList 0 (isSet× isSetBool isSetA)

  IsRedex? : ∀ x x' → Dec (IsRedex x x')
  IsRedex? _ _ = discreteΣ 𝟚._≟_ (λ _ → _≟_) _ _

  HeadIsRedex? : ∀ xs → Dec (HeadIsRedex xs)
  HeadIsRedex? [] = no lower
  HeadIsRedex? (x ∷ []) = no lower
  HeadIsRedex? (x ∷ x' ∷ _) = IsRedex? x x'

  preη· : ∀ x xs → Dec (HeadIsRedex (x ∷ xs)) → [𝟚× A ]
  preη· _ xs (yes _) = tail xs
  preη· x xs (no _) = x ∷ xs

  preη·-N : ∀ {x xs} hir? → IsNormalised xs → IsNormalised (preη· x xs hir?)
  preη·-N (yes _) = IsNormalisedTail _
  preη·-N (no ¬p) = ⊎.rec ¬p

  sec-preη· : ∀ x xs p q → IsNormalised xs → preη· (not₁ x) (preη· x xs p) q ≡ xs
  sec-preη· x (x₂ ∷ xs) (yes p) (no ¬p) x₁ =
    cong (_∷ xs) (sym (symIsRedex _ _ p))
  sec-preη· x (x₂ ∷ x₃ ∷ xs) (yes p) (yes p₁) x₁ =
    ⊥.rec (x₁ (inl (symIsRedex _ _ p ∙ p₁)))
  sec-preη· x xs (no ¬p) (no ¬p₁) x₁ = ⊥.rec (¬p₁ refl)
  sec-preη· x xs (no ¬p) (yes p) _ = refl

  η· : (Bool × A) → [𝟚× A ] → [𝟚× A ]
  η· x xs = preη· _ _ (HeadIsRedex? (x ∷ xs))

  η·∷ : ∀ x xs → (HeadIsRedex (x ∷ xs) → ⊥) → η· x xs ≡ x ∷ xs
  η·∷ x xs x₁ = cong (λ u → preη· x xs u)
   (≡no (HeadIsRedex? (x ∷ xs)) x₁)

  nη· : (Bool × A) → Σ _ IsNormalised → Σ _ IsNormalised
  fst (nη· x x₁) = η· x (fst x₁)
  snd (nη· x x₁) = preη·-N (HeadIsRedex? _) (snd x₁)


  η·iso : (Bool × A) → Iso (Σ [𝟚× A ] IsNormalised) (Σ [𝟚× A ] IsNormalised)
  Iso.fun (η·iso x) = nη· x
  Iso.inv (η·iso x) = nη· (not₁ x)
  Iso.sec (η·iso x) b =
    Σ≡Prop isPropIsNormalised
     (funExt⁻ (cong η· (sym (not₁not₁ x)) ) (η· (not₁ x) (fst b))
      ∙ sec-preη· (not₁ x) _ (HeadIsRedex? _) (HeadIsRedex? _) (snd b))
  Iso.ret (η·iso x) a =
    Σ≡Prop isPropIsNormalised
     (sec-preη· x _ (HeadIsRedex? _) (HeadIsRedex? _) (snd a))

  η·≃ = isoToEquiv ∘ η·iso

  normalise : ∀ xs → Σ _ λ xs' →
    (xs' · xs ⁻¹≡ε) × IsNormalised xs'
  normalise = Li.elim ([] , [ [] ]≡ε , lower )
   λ {x} {xs} (xs' , [ u ]≡ε , v) →
    let zz : ∀ xs' uu u → (preη· x xs' uu ++ invLi (x ∷ xs)) ⇊1g
        zz =
          λ { xs' (no ¬p) → subst (_⇊1g ∘S (x ∷_)) (++-assoc xs' _ _) ∘ cj x _
             ; [] (yes ())
             ; (_ ∷ xs') (yes p) →
                  subst _⇊1g (λ i → ++-assoc xs' (invLi xs)
                       [ symIsRedex _ _ p i ] i) ∘ ⇊1gRot _ }
        h = HeadIsRedex? _
    in  _ , [ zz xs' h u ]≡ε , preη·-N h v

  IsoNF : Iso (Σ _  IsNormalised) List/↘↙
  fun IsoNF = [_]/ ∘ fst
  Iso.inv IsoNF =
   SQ.rec (isSetΣ isSet[𝟚×] (isProp→isSet ∘ isPropIsNormalised))
   ((λ (_ , _ , u) → _ , u) ∘ normalise)
   λ _ _ →
     let (a' , t  , u ) = normalise _ ; (b' , t' , u') = normalise _
     in  Σ≡Prop isPropIsNormalised ∘S sym
      ∘S nf-uR _ _ (fst (IsNormalisedInvLi {b'}) u') u
      ∘S ⇊1g++comm a' (invLi b') ∘S ≡ε
      ∘S flip (·⁻¹≡ε-trans _ _ _) (·⁻¹≡ε-sym _ _ t')
      ∘S ·⁻¹≡ε-trans _ _ _ t
  sec IsoNF = SQ.elimProp (λ _ → squash/ _ _)
    (eq/ _ _ ∘ fst ∘ snd ∘ normalise)
  ret IsoNF = Σ≡Prop isPropIsNormalised ∘ uncurry
   (Li.elim (λ _ → refl) λ f v →
   let lem : ∀ uu → preη· _ _ uu ≡ _ ∷ _
       lem =
        λ { (yes p) → ⊥.rec (v (inl (subst (WillReduce _ _) (f (v ∘ inr)) p)))
          ; (no ¬p) → refl }
   in lem (HeadIsRedex? _) ∙ cong (_ ∷_) (f (v ∘ inr)))

module NF {ℓ'} {A : Type ℓ} (G : Group ℓ') (η : A → ⟨ G ⟩) where
 open NormalForm A

 open GroupStr (snd G) renaming (_·_ to _·fg_) public

 η* : Bool × A → ⟨ G ⟩
 η* (b , a) = (if b then idfun _ else inv) (η a)

 fromList : [𝟚× A ] → ⟨ G ⟩
 fromList = foldr (_·fg_ ∘ η*) 1g

 record NF (g : _) : Type (ℓ-max ℓ ℓ') where
  constructor _nf_,_
  field
   word : [𝟚× A ]
   fromListWord≡ : fromList word ≡ g
   isNormalisedWord : IsNormalised word


 fromList· : ∀ xs ys → fromList (xs ++ ys) ≡
                           fromList xs ·fg fromList ys
 fromList· [] _ = sym (·IdL _)
 fromList· (_ ∷ xs) _ =
  cong (_ ·fg_) (fromList· xs _) ∙
   ·Assoc _ _ _

 redex-ε-η* : ∀ x x' → IsRedex x x' → η* x ·fg η* x' ≡ 1g
 redex-ε-η* (false , _) (false , _) = ⊥.rec ∘ false≢true ∘ cong fst
 redex-ε-η* (false , x) (true , _) q =
   cong (inv (η x) ·fg_) (cong (η) (sym (cong snd q))) ∙ ·InvL (η x)
 redex-ε-η* (true , x) (false , _) q =
   cong (η x ·fg_) (cong (inv ∘ η) (sym (cong snd q))) ∙ ·InvR (η x)
 redex-ε-η* (true , _) (true , _) = ⊥.rec ∘ true≢false ∘ cong fst
