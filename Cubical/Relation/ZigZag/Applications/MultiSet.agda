-- We apply the theory of quasi equivalence relations (QERs) to finite multisets and association lists.
module Cubical.Relation.ZigZag.Applications.MultiSet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.RelationalStructure
open import Cubical.Foundations.Structure
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients
open import Cubical.HITs.FiniteMultiset as FMS hiding ([_] ; _++_)
open import Cubical.HITs.FiniteMultiset.CountExtensionality
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Relation.Nullary
open import Cubical.Relation.ZigZag.Base

open import Cubical.Structures.MultiSet
open import Cubical.Structures.Relational.Auto
open import Cubical.Structures.Relational.Macro

-- we define simple association lists without any higher constructors
data AList {ℓ} (A : Type ℓ) : Type ℓ where
  ⟨⟩ : AList A
  ⟨_,_⟩∷_ : A → ℕ → AList A → AList A

infixr 5 ⟨_,_⟩∷_

private
  variable
    ℓ : Level

-- We have a CountStructure on List and AList and use these to get a QER between the two
module Lists&ALists {A : Type ℓ} (discA : Discrete A) where

  multisetShape : Type ℓ → Type ℓ
  multisetShape X = X × (A → X → X) × (X → X → X) × (A → X → Const[ ℕ , isSetℕ ])

  module S = RelMacro ℓ (autoRelDesc multisetShape)

  addIfEq : (a x : A) → ℕ → ℕ → ℕ
  addIfEq a x m n with discA a x
  ... | yes _ = m + n
  ... | no _ = n

  module _ {a x : A} {n : ℕ} where

    addIfEq≡ : {m : ℕ} → a ≡ x → addIfEq a x m n ≡ m + n
    addIfEq≡ a≡x with discA a x
    ... | yes _ = refl
    ... | no a≢x = ⊥.rec (a≢x a≡x)

    addIfEq≢ : {m : ℕ} → ¬ (a ≡ x) → addIfEq a x m n ≡ n
    addIfEq≢ a≢x with discA a x
    ... | yes a≡x = ⊥.rec (a≢x a≡x)
    ... | no _ = refl

    addIfEq0 : addIfEq a x 0 n ≡ n
    addIfEq0 with discA a x
    ... | yes _ = refl
    ... | no _ = refl

    addIfEq+ : {m : ℕ} (n' : ℕ) → addIfEq a x m (n + n') ≡ addIfEq a x m n + n'
    addIfEq+ n' with discA a x
    ... | yes _ = +-assoc _ n n'
    ... | no _ = refl

  module L where
    emp : List A
    emp = []

    insert : A → List A → List A
    insert x xs = x ∷ xs

    union : List A → List A → List A
    union xs ys = xs ++ ys

    count : A → List A → ℕ
    count a [] = zero
    count a (x ∷ xs) = addIfEq a x 1 (count a xs)

    structure : S.structure (List A)
    structure = emp , insert , union , count

    countUnion : ∀ a xs ys → count a (union xs ys) ≡ count a xs + count a ys
    countUnion a [] ys = refl
    countUnion a (x ∷ xs) ys =
      cong (addIfEq a x 1) (countUnion a xs ys)
      ∙ addIfEq+ (count a ys)

  module AL where
    emp : AList A
    emp = ⟨⟩

    insert* : ℕ → A → AList A → AList A
    insert* m a ⟨⟩ = ⟨ a , m ⟩∷ ⟨⟩
    insert* m a (⟨ y , n ⟩∷ ys) with (discA a y)
    ... | yes _ = ⟨ y , m + n ⟩∷ ys
    ... | no _ = ⟨ y , n ⟩∷ insert* m a ys

    insert : A → AList A → AList A
    insert = insert* 1

    union : AList A → AList A → AList A
    union ⟨⟩ ys = ys
    union (⟨ x , n ⟩∷ xs) ys = insert* n x (union xs ys)

    count : A → AList A → ℕ
    count a ⟨⟩ = zero
    count a (⟨ y , n ⟩∷ ys) = addIfEq a y n (count a ys)

    structure : S.structure (AList A)
    structure = emp , insert , union , count

    countInsert* : ∀ m a x ys → count a (insert* m x ys) ≡ addIfEq a x m (count a ys)
    countInsert* m a x ⟨⟩ = refl
    countInsert* m a x (⟨ y , n ⟩∷ ys) with discA a x | discA a y | discA x y
    ... | yes a≡x | yes a≡y | yes x≡y = addIfEq≡ a≡y ∙ sym (+-assoc m n _)
    ... | yes a≡x | yes a≡y | no x≢y = ⊥.rec (x≢y (sym a≡x ∙ a≡y))
    ... | yes a≡x | no a≢y | yes x≡y = ⊥.rec (a≢y (a≡x ∙ x≡y))
    ... | yes a≡x | no a≢y | no x≢y =  addIfEq≢ a≢y ∙ countInsert* m a x ys ∙ addIfEq≡ a≡x
    ... | no a≢x | yes a≡y | yes x≡y = ⊥.rec (a≢x (a≡y ∙ sym x≡y))
    ... | no a≢x | yes a≡y | no x≢y = addIfEq≡ a≡y ∙ cong (n +_) (countInsert* m a x ys ∙ addIfEq≢ a≢x)
    ... | no a≢x | no a≢y | yes x≡y = addIfEq≢ a≢y
    ... | no a≢x | no a≢y | no x≢y = addIfEq≢ a≢y ∙ countInsert* m a x ys ∙ addIfEq≢ a≢x

    countInsert = countInsert* 1

    countUnion : ∀ a xs ys → count a (union xs ys) ≡ count a xs + count a ys
    countUnion a ⟨⟩ ys = refl
    countUnion a (⟨ x , n ⟩∷ xs) ys =
      countInsert* n a x (union xs ys)
      ∙ cong (addIfEq a x n) (countUnion a xs ys)
      ∙ addIfEq+ (count a ys)

  -- now for the QER between List and Alist

  R : List A → AList A → Type ℓ
  R xs ys = ∀ a → L.count a xs ≡ AL.count a ys

  φ : List A → AList A
  φ [] = ⟨⟩
  φ (x ∷ xs) = AL.insert x (φ xs)

  ψ : AList A → List A
  ψ ⟨⟩ = []
  ψ (⟨ x , zero ⟩∷ xs) = ψ xs
  ψ (⟨ x , suc n ⟩∷ xs) = x ∷ ψ (⟨ x , n ⟩∷ xs)

  η : ∀ xs → R xs (φ xs)
  η [] a = refl
  η (x ∷ xs) a = cong (addIfEq a x 1) (η xs a) ∙ sym (AL.countInsert a x (φ xs))

  -- for the other direction we need a little helper function
  ε : ∀ y → R (ψ y) y
  ε' : (x : A) (n : ℕ) (xs : AList A) (a : A)
    → L.count a (ψ (⟨ x , n ⟩∷ xs)) ≡ AL.count a (⟨ x , n ⟩∷ xs)

  ε ⟨⟩ a = refl
  ε (⟨ x , n ⟩∷ xs) a = ε' x n xs a

  ε' x zero xs a = ε xs a ∙ sym addIfEq0
  ε' x (suc n) xs a with discA a x
  ... | yes a≡x = cong suc (ε' x n xs a ∙ addIfEq≡ a≡x)
  ... | no  a≢x = ε' x n xs a ∙ addIfEq≢ a≢x

  -- Induced quotients and equivalence

  open isQuasiEquivRel

  -- R is a QER
  QuasiR : QuasiEquivRel _ _ ℓ
  QuasiR .fst .fst = R
  QuasiR .fst .snd _ _ = isPropΠ λ _ → isSetℕ _ _
  QuasiR .snd .zigzag r r' r'' a = (r a) ∙∙ sym (r' a) ∙∙ (r'' a)
  QuasiR .snd .fwd a = ∣ φ a , η a ∣₁
  QuasiR .snd .bwd b = ∣ ψ b , ε b ∣₁

  isStructuredInsert : (x : A) {xs : List A} {ys : AList A}
    → R xs ys → R (L.insert x xs) (AL.insert x ys)
  isStructuredInsert x {xs} {ys} r a =
    cong (addIfEq a x 1) (r a) ∙ sym (AL.countInsert a x ys)

  isStructuredUnion :
    {xs : List A} {ys : AList A} (r : R xs ys)
    {xs' : List A} {ys' : AList A} (r' : R xs' ys')
    → R (L.union xs xs') (AL.union ys ys')
  isStructuredUnion {xs} {ys} r {xs'} {ys'} r' a =
    L.countUnion a xs xs' ∙ cong₂ _+_ (r a) (r' a) ∙ sym (AL.countUnion a ys ys')

  -- R is structured
  isStructuredR : S.relation R L.structure AL.structure
  isStructuredR .fst a = refl
  isStructuredR .snd .fst = isStructuredInsert
  isStructuredR .snd .snd .fst {xs} {ys} = isStructuredUnion {xs} {ys}
  isStructuredR .snd .snd .snd a r = r a

  module E = QER→Equiv QuasiR
  open E renaming (Rᴸ to Rᴸ; Rᴿ to Rᴬᴸ)

  List/Rᴸ = (List A) / Rᴸ
  AList/Rᴬᴸ = (AList A) / Rᴬᴸ

  List/Rᴸ≃AList/Rᴬᴸ : List/Rᴸ ≃ AList/Rᴬᴸ
  List/Rᴸ≃AList/Rᴬᴸ = E.Thm

  main : QERDescends _ S.relation (List A , L.structure) (AList A , AL.structure) QuasiR
  main = structuredQER→structuredEquiv S.suitable _ _ QuasiR isStructuredR

  open QERDescends

  LQstructure : S.structure List/Rᴸ
  LQstructure = main .quoᴸ .fst

  ALQstructure : S.structure AList/Rᴬᴸ
  ALQstructure = main .quoᴿ .fst

  -- We get a path between structure over the equivalence from the fact that the QER is structured
  List/Rᴸ≡AList/Rᴬᴸ :
    Path (TypeWithStr ℓ S.structure) (List/Rᴸ , LQstructure) (AList/Rᴬᴸ , ALQstructure)
  List/Rᴸ≡AList/Rᴬᴸ =
    sip S.univalent _ _
      (E.Thm , S.matches (List/Rᴸ , LQstructure) (AList/Rᴬᴸ , ALQstructure) E.Thm .fst (main .rel))

  -- Deriving associativity of union for association list multisets

  LQunion = LQstructure .snd .snd .fst
  ALQunion = ALQstructure .snd .snd .fst

  hasAssociativeUnion : TypeWithStr ℓ S.structure → Type ℓ
  hasAssociativeUnion (_ , _ , _ , _⊔_ , _) =
    ∀ xs ys zs → (xs ⊔ ys) ⊔ zs ≡ xs ⊔ (ys ⊔ zs)

  LQassoc : hasAssociativeUnion (List/Rᴸ , LQstructure)
  LQassoc = elimProp3 (λ _ _ _ → squash/ _ _) (λ xs ys zs i → [ ++-assoc xs ys zs i ])

  ALQassoc : hasAssociativeUnion (AList/Rᴬᴸ , ALQstructure)
  ALQassoc = subst hasAssociativeUnion List/Rᴸ≡AList/Rᴬᴸ LQassoc

  -- We now show that List/Rᴸ≃FMSet

  _∷/_ : A → List/Rᴸ → List/Rᴸ
  _∷/_ = LQstructure .snd .fst

  multisetShape' : Type ℓ → Type ℓ
  multisetShape' X = X × (A → X → X) × (A → X → Const[ ℕ , isSetℕ ])

  FMSstructure : S.structure (FMSet A)
  FMSstructure = [] , _∷_ , FMS._++_ , FMScount discA

  infixr 5 _∷/_

  FMSet→List/Rᴸ : FMSet A → List/Rᴸ
  FMSet→List/Rᴸ = FMS.Rec.f squash/ [ [] ] _∷/_ β
    where
    δ : ∀ c a b xs → L.count c (a ∷ b ∷ xs) ≡ L.count c (b ∷ a ∷ xs)
    δ c a b xs with discA c a | discA c b
    δ c a b xs | yes _        | yes _ = refl
    δ c a b xs | yes _        | no  _ = refl
    δ c a b xs | no  _        | yes _ = refl
    δ c a b xs | no  _        | no  _ = refl

    γ : ∀ a b xs → Rᴸ (a ∷ b ∷ xs) (b ∷ a ∷ xs)
    γ a b xs =
      ∣ φ (a ∷ b ∷ xs) , η (a ∷ b ∷ xs) , (λ c → δ c b a xs ∙ η (a ∷ b ∷ xs) c) ∣₁

    β : ∀ a b [xs] → a ∷/ b ∷/ [xs] ≡ b ∷/ a ∷/ [xs]
    β a b = elimProp (λ _ → squash/ _ _) (λ xs → eq/ _ _ (γ a b xs))

  -- The inverse is induced by the standard projection of lists into finite multisets,
  -- which is a morphism of CountStructures
  -- Moreover, we need 'count-extensionality' for finite multisets
  List→FMSet : List A → FMSet A
  List→FMSet [] = []
  List→FMSet (x ∷ xs) = x ∷ List→FMSet xs

  List→FMSet-count : ∀ a xs → L.count a xs ≡ FMScount discA a (List→FMSet xs)
  List→FMSet-count a [] = refl
  List→FMSet-count a (x ∷ xs) with discA a x
  ...                         | yes _ = cong suc (List→FMSet-count a xs)
  ...                         | no  _ = List→FMSet-count a xs

  List/Rᴸ→FMSet : List/Rᴸ → FMSet A
  List/Rᴸ→FMSet [ xs ] = List→FMSet xs
  List/Rᴸ→FMSet (eq/ xs ys r i) = path i
    where
    countsAgree : ∀ a → L.count a xs ≡ L.count a ys
    countsAgree a = cong (LQstructure .snd .snd .snd a) (eq/ xs ys r)

    θ : ∀ a → FMScount discA a (List→FMSet xs) ≡ FMScount discA a (List→FMSet ys)
    θ a = sym (List→FMSet-count a xs) ∙∙ countsAgree a ∙∙ List→FMSet-count a ys

    path : List→FMSet xs ≡ List→FMSet ys
    path = FMScountExt.Thm discA _ _ θ
  List/Rᴸ→FMSet (squash/ xs/ xs/' p q i j) =
    trunc (List/Rᴸ→FMSet xs/) (List/Rᴸ→FMSet xs/') (cong List/Rᴸ→FMSet p) (cong List/Rᴸ→FMSet q) i j

  List/Rᴸ→FMSet-insert : (x : A) (ys : List/Rᴸ) → List/Rᴸ→FMSet (x ∷/ ys) ≡ x ∷ List/Rᴸ→FMSet ys
  List/Rᴸ→FMSet-insert x = elimProp (λ _ → FMS.trunc _ _) λ xs → refl

  List→FMSet-union : (xs ys : List A)
    → List→FMSet (xs ++ ys) ≡ FMS._++_ (List→FMSet xs) (List→FMSet ys)
  List→FMSet-union [] ys = refl
  List→FMSet-union (x ∷ xs) ys = cong (x ∷_) (List→FMSet-union xs ys)

  List/Rᴸ≃FMSet : List/Rᴸ ≃ FMSet A
  List/Rᴸ≃FMSet = isoToEquiv (iso List/Rᴸ→FMSet FMSet→List/Rᴸ τ σ)
    where
    σ' : (xs : List A) → FMSet→List/Rᴸ (List/Rᴸ→FMSet [ xs ]) ≡ [ xs ]
    σ' [] = refl
    σ' (x ∷ xs) = cong (x ∷/_) (σ' xs)

    σ : section FMSet→List/Rᴸ List/Rᴸ→FMSet
    σ = elimProp (λ _ → squash/ _ _) σ'

    τ' : ∀ x {xs} → List/Rᴸ→FMSet (FMSet→List/Rᴸ xs) ≡ xs → List/Rᴸ→FMSet (FMSet→List/Rᴸ (x ∷ xs)) ≡ x ∷ xs
    τ' x {xs} p = List/Rᴸ→FMSet-insert x (FMSet→List/Rᴸ xs) ∙ cong (x ∷_) p

    τ : retract FMSet→List/Rᴸ List/Rᴸ→FMSet
    τ = FMS.ElimProp.f (FMS.trunc _ _) refl τ'

  List/Rᴸ≃FMSet-EquivStr : S.equiv (List/Rᴸ , LQstructure) (FMSet A , FMSstructure) List/Rᴸ≃FMSet
  List/Rᴸ≃FMSet-EquivStr .fst = refl
  List/Rᴸ≃FMSet-EquivStr .snd .fst a xs = List/Rᴸ→FMSet-insert a xs
  List/Rᴸ≃FMSet-EquivStr .snd .snd .fst = elimProp2 (λ _ _ → trunc _ _) List→FMSet-union
  List/Rᴸ≃FMSet-EquivStr .snd .snd .snd a =
    elimProp (λ _ → isSetℕ _ _) (List→FMSet-count a)

  {-
  Putting everything together we get:
                ≃
  List/Rᴸ ------------> AList/Rᴬᴸ
    |
    |≃
    |
    ∨
                ≃
  FMSet A ------------> AssocList A
  We thus get that AList/Rᴬᴸ≃AssocList.
  Constructing such an equivalence directly requires count extensionality for association lists,
  which should be even harder to prove than for finite multisets.
  This strategy should work for all implementations of multisets with HITs.
  We just have to show that:
   ∙ The HIT is equivalent to FMSet (like AssocList)
   ∙ There is a QER between lists and the basic data type of the HIT
     with the higher constructors removed (like AList)
  Then we get that this HIT is equivalent to the corresponding set quotient that identifies elements
  that give the same count on each a : A.
  TODO: Show that all the equivalences are indeed isomorphisms of multisets not only of CountStructures!
  -}
