{-# OPTIONS --cubical --no-import-sorts #-}

module SyntheticReals.MoreLogic.Properties where -- hProp logic

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Data.Sigma renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Function.Base using (_∋_)
open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)
open import Cubical.Foundations.Logic renaming (inl to inlᵖ; inr to inrᵖ)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) renaming (⊥ to ⊥⊥) -- `⊥` and `elim`
open import Cubical.HITs.PropositionalTruncation.Base -- ∣_∣

import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit.Base

open import SyntheticReals.Utils

-- lifted versions of ⊥ and ⊤

open import SyntheticReals.MoreLogic.Reasoning
open import SyntheticReals.MoreLogic.Definitions

isProp⊤ : isProp [ ⊤ ]
isProp⊤ tt tt = refl

symₚ : ∀{ℓ} → {A : Type ℓ} {x y : A} → [ x ≡ₚ y ] → [ y ≡ₚ x ]
symₚ {x = x} x≡y = substₚ (λ p → p ≡ₚ x) x≡y ∣ refl ∣

⊔-identityˡ-↑ : (P : hProp ℓ) → ⊥↑ {ℓ} ⊔ P ≡ P
⊔-identityˡ-↑ P =
  ⇒∶ (⊔-elim ⊥↑ P (λ _ → P) (λ ()) (λ x → x))
  ⇐∶ inrᵖ

⊔-identityʳ-↑ : (P : hProp ℓ) → P ⊔ ⊥↑ {ℓ} ≡ P
⊔-identityʳ-↑ P = ⇔toPath (⊔-elim P ⊥↑ (λ _ → P) (λ x → x) λ ()) inlᵖ

⊓-identityˡ-↑ : (P : hProp ℓ) → ⊤↑ {ℓ} ⊓ P ≡ P
⊓-identityˡ-↑ _ = ⇔toPath snd  λ x → lift tt , x

⊓-identityʳ-↑ : (P : hProp ℓ) → P ⊓ ⊤↑ {ℓ} ≡ P
⊓-identityʳ-↑ _ = ⇔toPath fst λ x → x , lift tt

¬↑≡¬ : ∀{ℓ} → {P : hProp ℓ} → (¬↑ P) ≡ (¬ P)
¬↑≡¬ =
 ⇒∶ (λ ¬↑P P → lower (¬↑P P))
 ⇐∶ (λ  ¬P P → lift  ( ¬P P))

¬¬-introᵗ : (P : Type ℓ) → P → ¬ᵗ ¬ᵗ P
¬¬-introᵗ _ p ¬p = ¬p p

¬¬-elimᵗ : (P : Type ℓ) → ¬ᵗ ¬ᵗ ¬ᵗ P → ¬ᵗ P
¬¬-elimᵗ _ ¬¬¬p p = ¬¬¬p (λ ¬p → ¬p p)

¬¬-intro : (P : hProp ℓ) → [ P ] → [ ¬ ¬ P ]
¬¬-intro _ p ¬p = ¬p p

¬¬-elim : (P : hProp ℓ) → [ ¬ ¬ ¬ P ] → [ ¬ P ]
¬¬-elim _ ¬¬¬p p = ¬¬¬p (λ ¬p → ¬p p)

¬¬-involutive : (P : hProp ℓ) → [ ¬ ¬ ¬ P ⇔ ¬ P ]
¬¬-involutive P .fst = ¬¬-elim     P
¬¬-involutive P .snd = ¬¬-intro (¬ P)

⇔toPath' : ∀{ℓ} {P Q : hProp ℓ} → [ P ⇔ Q ] → P ≡ Q
⇔toPath' = uncurry ⇔toPath

pathTo⇔ : ∀{ℓ} {P Q : hProp ℓ} → P ≡ Q → [ P ⇔ Q ]
pathTo⇔ p≡q = (pathTo⇒ p≡q , pathTo⇐ p≡q)

⊓⇔⊓ : ∀{ℓ ℓ' ℓ'' ℓ'''} {P : hProp ℓ} {Q : hProp ℓ'} {R : hProp ℓ''} {S : hProp ℓ'''}
   → [ (P ⇔ R) ⊓ (Q ⇔ S) ] → [ (P ⊓ Q) ⇔ (R ⊓ S) ]
⊓⇔⊓ (p⇔r , q⇔s) .fst (p , q) = p⇔r .fst p , q⇔s .fst q
⊓⇔⊓ (p⇔r , q⇔s) .snd (r , s) = p⇔r .snd r , q⇔s .snd s

⊓≡⊓ : ∀{ℓ} {P Q R S : hProp ℓ} → P ≡ R → Q ≡ S → (P ⊓ Q) ≡ (R ⊓ S)
⊓≡⊓ p≡r q≡s i = p≡r i ⊓ q≡s i

[path]To⇒ : (P Q : hProp ℓ) → [ P ] ≡ [ Q ] → [ P ⇒ Q ]
[path]To⇒ P Q [P]≡[Q] p = transport [P]≡[Q] p

[path]To⇐ : (P Q : hProp ℓ) → [ P ] ≡ [ Q ] → [ Q ⇒ P ]
[path]To⇐ P Q [P]≡[Q] q = transport (sym [P]≡[Q]) q

¬¬-involutiveᵗ : (A : Type ℓ) → (¬ᵗ ¬ᵗ ¬ᵗ A) ≡ (¬ᵗ A)
abstract
  ¬¬-involutiveᵗ A = isoToPath λ where
    .Iso.fun      ¬¬¬a a → ¬¬¬a (λ ¬a → ¬a a)
    .Iso.inv      ¬a ¬¬a → ¬¬a ¬a
    .Iso.rightInv ¬a     → refl
    -- the following proof is `... ≡ ¬¬¬a` and uses funext to reduce this to a proof `∀ x → ... x ≡ ¬¬¬a x`
    -- but this does not matter, since we have `¬¬¬a x` which is `⊥` and then we can use ⊥-elim to obtain whatever is necessary
    -- `⊥-elim` needed a detailed hint what to produce and this might not be the most elegant way to proof this
    .Iso.leftInv  ¬¬¬a   →
      funExt {A = (¬ᵗ ¬ᵗ A)} {B = λ _ i → ⊥⊥} {f = (λ ¬¬a → ¬¬a (λ a → ¬¬¬a (λ ¬a → ¬a a)))} {g = ¬¬¬a}
             (λ x → ⊥-elim {A = λ _ → (x (λ a → ¬¬¬a (λ ¬a → ¬a a)) ≡ ¬¬¬a x)} (¬¬¬a x))

-- taken from https://ncatlab.org/nlab/show/excluded+middle#DoubleNegatedPEM
-- Double-negated PEM
weak-LEM : ∀(P : hProp ℓ) → [ ¬ ¬ (P ⊔ ¬ P) ]
weak-LEM _ ¬[p⊔¬p] = ¬[p⊔¬p] (inrᵖ (λ p → ¬[p⊔¬p] (inlᵖ p)))

weak-LEMᵗ : ∀(P : Type ℓ) → ¬ᵗ ¬ᵗ (P ⊎ (¬ᵗ P))
weak-LEMᵗ _ ¬[p⊔¬p] = ¬[p⊔¬p] (inr (λ p → ¬[p⊔¬p] (inl p)))

⊤-introᵖ : {P : hProp ℓ} → [ P ] → P ≡ ⊤↑
⊤-introᵖ {ℓ = ℓ} {P = P} p = let
  P⇔⊤↑ : [ P ⇔ ⊤↑ {ℓ} ]
  P⇔⊤↑ = (λ _ → lift tt) , (λ _ → p)
  in ⇔toPath (fst P⇔⊤↑) (snd P⇔⊤↑)

⊤-elimᵖ : {P : hProp ℓ} → P ≡ ⊤↑ → [ P ]
⊤-elimᵖ {ℓ = ℓ} {P = P} p≡⊤ = (
  [ ⊤↑ {ℓ} ] ⇒⟨ transport ( λ i → [ p≡⊤ (~ i) ]) ⟩
  [ P      ] ◼) (lift tt)

contraposition : (P : hProp ℓ) (Q : hProp ℓ') → [ P ⇒ Q ] → [ ¬ Q ⇒ ¬ P ]
contraposition P Q f ¬q p = ⊥-elim (¬q (f p))

instance≡ : ∀{ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → ({{x : A}} → B x) ≡ ((x : A) → B x)
instance≡ = isoToPath (iso (λ f a → f {{a}}) (λ f {{a}} → f a) (λ f i → f) (λ f i → f))

implicit≡ : ∀{ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → ({x : A} → B x) ≡ ((x : A) → B x)
implicit≡ = isoToPath (iso (λ f a → f {a}) (λ f {a} → f a) (λ f i → f) (λ f i → f))

instanceFunExt : {A : Type ℓ} {B : A → I → Type ℓ'}
                 {f : {{x : A}} → B x i0} {g : {{x : A}} → B x i1}
               → ({{x : A}} → PathP (B x) (f {{x}}) (g {{x}}))
               → PathP (λ i → {{x : A}} → B x i) f g
instanceFunExt p i {{x}} = p {{x}} i

funExt-⊥ : {A : Type ℓ} (f g : A → Empty.⊥) → f ≡ g
funExt-⊥ f g = funExt (λ x → ⊥-elim {A = λ _ →  f x ≡ g x} (f x)) -- ⊥-elim needed a hint here

-- uncurry-preserves-≡
--   : {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''}
--   → (f : (a : A) → (b : B a) → C a b)
--   -------------------------------------------------------------
--   → ∀ a b → f a b ≡ (uncurry f) (a , b)
-- uncurry-preserves-≡ f a b = refl

Σ-preserves-≡ :
      {A : Type ℓ}
      {B : A → Type ℓ'}
      {C : (a : A) → (b : B a) → Type ℓ''}
      {f g : ((a , b) : Σ A B) → C a b}
    → ((a : A) (b : B a) → (f (a , b)) ≡ (g (a , b)))
    → ((ab : Σ A B)      → (f   ab   ) ≡ (g   (ab) ))
Σ-preserves-≡ p (a , b) = p a b

Σ-reflects-≡ :
      {A : Type ℓ}
      {B : A → Type ℓ'}
      {a b : Σ A B}
    → a ≡ b
    → Σ[ p ∈ (fst a ≡ fst b) ] transport (λ i → B (p i)) (snd a) ≡ snd b
    --  Σ[ q ∈ (fst a ≡ fst b) ] (PathP (λ i → B (q i)) (snd a) (snd b))
Σ-reflects-≡ a≡b with PathΣ→ΣPathTransport _ _ a≡b
... | fst≡fst , snd≡snd = fst≡fst , snd≡snd

uncurry-reflects-≡
  : {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''}
  → (f g : (a : A) → (b : B a) → C a b)
  -------------------------------------------------------------
  → (uncurry f ≡ uncurry g) → f ≡ g
uncurry-reflects-≡ f g p = funExt (λ x →
  f x                         ≡⟨ refl ⟩
  (λ y → (uncurry f) (x , y)) ≡⟨ ( λ i → λ y → (p i) (x , y)) ⟩
  (λ y → (uncurry g) (x , y)) ≡⟨ refl ⟩
  g x                         ∎)

-- "constant" version of funExt
funExt₂ᶜ :
      {A : Type ℓ}
      {B : A → Type ℓ'}
      {C : (a : A) → (b : B a) → Type ℓ''}
      {f g : (a : A) → (b : B a) → C a b}
      → ((a : A) → (b : B a) → (f a b) ≡ (g a b)) → f ≡ g
funExt₂ᶜ {A = A} {B = B} {C = C} {f = f} {g = g} = (
 ((a : A) (b : B a) → (         f   a   b)  ≡ (         g   a   b) ) ⇒⟨ (λ z → z) ⟩ -- holds definitionally
 ((a : A) (b : B a) → ((uncurry f) (a , b)) ≡ ((uncurry g) (a , b))) ⇒⟨ Σ-preserves-≡ ⟩
 ((ab : Σ A B)      → ((uncurry f)   ab   ) ≡ ((uncurry g) ( ab  ))) ⇒⟨ funExt ⟩
                       (uncurry f)          ≡  (uncurry g)           ⇒⟨ uncurry-reflects-≡ f g ⟩
                                f           ≡           g            ◼)

funExt-⊥₂ : {A B : Type ℓ} (f g : A → B → Empty.⊥) → f ≡ g
funExt-⊥₂ f g =  funExt₂ᶜ λ a b → ⊥-elim {A = λ _ → f a b ≡ g a b} (g a b)

-- weak deMorgan laws: only these three hold without further assumptions

deMorgan₂ : (P : hProp ℓ) (Q : hProp ℓ') → [ ¬ (P ⊔ Q) ] → [ ¬ P ⊓ ¬ Q ]
abstract deMorgan₂ P Q ¬[p⊔q] = (λ p →  ⊥-elim (¬[p⊔q] (inlᵖ p))) , λ q → ⊥-elim (¬[p⊔q] (inrᵖ q))

deMorgan₂-back : (P : hProp ℓ) (Q : hProp ℓ') → [ ¬ P ⊓ ¬ Q ] → [ ¬ (P ⊔ Q) ]
abstract deMorgan₂-back P Q (¬p , ¬q) p⊔q = ⊔-elim P Q (λ p⊔q → ⊥) ¬p ¬q p⊔q

deMorgan₁-back : (P : hProp ℓ) (Q : hProp ℓ') → [ ¬ P ⊔ ¬ Q ] → [ ¬ (P ⊓ Q) ]
abstract deMorgan₁-back {ℓ = ℓ} P Q [¬p⊔¬q] (p , q) = ⊔-elim (¬ P) (¬ Q) (λ [¬p⊔¬q] → ⊥) (λ ¬p → ¬p p) (λ ¬q → ¬q q) [¬p⊔¬q]

¬-⊓-distrib  : (P : hProp ℓ) (Q : hProp ℓ') → [ ¬ (P ⊓ Q) ] → [ (P ⇒ ¬ Q) ⊓ (Q ⇒ ¬ P) ]
¬-⊓-distrib P Q ¬p⊓q = (λ p q → ¬p⊓q (p , q)) , (λ q p → ¬p⊓q (p , q))

implication : (P : hProp ℓ) (Q : hProp ℓ') → [ ¬ (P ⊓ Q) ] → [ P ⇒ ¬ Q ]
implication {ℓ = ℓ} P Q ¬[p⊓q] p q = ⊥-elim (¬[p⊓q] (p , q))

uncurryₚ : ∀{ℓ ℓ' ℓ''} (P : hProp ℓ) (Q : hProp ℓ')(R : hProp ℓ'') → (f : [ P ] → [ Q ] → [ R ]) → [ P ⊓ Q ] → [ R ]
uncurryₚ P Q R f = uncurry f

⊓¬¬⇒¬¬⊓ : ∀{ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ') → [ ¬ ¬ P ] → [ ¬ ¬ Q ] → [ ¬ ¬ (P ⊓ Q) ]
⊓¬¬⇒¬¬⊓ P Q ¬¬p ¬¬q = contraposition (¬ (P ⊓ Q)) (P ⇒ ¬ Q) (implication P Q) λ p⇒¬q → ¬¬p (contraposition P (¬ Q) p⇒¬q ¬¬q)

-- Q and P are disjoint if P ⇒ ¬ Q or equivalently Q ⇒ ¬ P

abstract
  -- we have that  (P ⇒ ¬ Q)   ≡ (Q ⇒ ¬ P)
  -- normalizes to (P ⇒ Q ⇒ ⊥) ≡ (Q ⇒ P ⇒ ⊥)
  -- which is just flipping of the arguments
  [P⇒¬Q]≡[Q⇒¬P] : ∀{ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ') → (P ⇒ ¬ Q) ≡ (Q ⇒ ¬ P)
  [P⇒¬Q]≡[Q⇒¬P] P Q = ⇒∶ flip ⇐∶ flip
    -- ⇒∶ (λ p⇒¬q q p → p⇒¬q p q)
    -- ⇐∶ (λ q⇒¬p p q → q⇒¬p q p)

  [P⇒¬Q]⇒[Q⇒¬P] : ∀{ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ') → [ (P ⇒ ¬ Q) ] → [ (Q ⇒ ¬ P) ]
  [P⇒¬Q]⇒[Q⇒¬P] P Q = flip -- pathTo⇒ ([P⇒¬Q]≡[Q⇒¬P] P Q)

  [P⇒¬Q]≡¬[P⊓Q] : ∀{ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ') → (P ⇒ ¬ Q) ≡ ¬ (P ⊓ Q)
  [P⇒¬Q]≡¬[P⊓Q] P Q = ⇒∶ uncurry ⇐∶ curry
    -- ⇒∶ (λ{ p⇒¬q (p , q) →  p⇒¬q   p   q })
    -- ⇐∶ (λ ¬[p⊓q] p   q  → ¬[p⊓q] (p , q) )

-- [¬P⇒Q]⇒[¬Q⇒¬¬P]
-- [¬P⇒¬¬Q]≡[¬Q⇒¬¬P]
--         ≡¬[¬P⊓¬Q]
--         ≡¬¬[P⊔Q]
-- [¬P≡Q]⇒¬[P⊓Q]≡¬[P⊓¬P]

¬[P⊓¬P] : ∀{ℓ} (P : hProp ℓ) → [ ¬ (P ⊓ ¬ P) ]
¬[P⊓¬P] P (p , ¬p) = ¬p p

-- NOTE: I think that we do not have ¬ P ≡ ¬ Q → P ≡ Q
--       since this might be equivalent to some LEM ?

-- ¬-reflects-≡ : ∀{ℓ} (P Q : hProp ℓ) → ¬ P ≡ ¬ Q → P ≡ Q
-- ¬-reflects-≡ P Q ¬p≡¬q with Σ-reflects-≡ ¬p≡¬q
-- ... | fst≡fst , snd≡snd = ΣPathP ({!   !} , {!   !})
--
-- -- (∀ x → P x ≡ P y) → x ≡ y
--
-- postulate dne : ∀{ℓ} (P : hProp ℓ) → ¬ ¬ P ≡ P
--
-- ¬-isEquiv : ∀ ℓ → isEquiv (¬_ {ℓ = ℓ})
-- ¬-isEquiv ℓ = λ where
--   .equiv-proof P → ((¬ P) , dne P) , λ{ (Q , ¬Q≡P) →
--     let γ = {! isPropIsProp (isProp[] Q) (isProp[] Q)  !}
--     in {!   !} }

-- fst (fst (equiv-proof (¬-isEquiv ℓ) P)) = ¬ P
-- snd (fst (equiv-proof (¬-isEquiv ℓ) P)) = dne P
-- snd (equiv-proof (¬-isEquiv ℓ) P) (Q , ¬Q≡P) = {!   !}

-- ¬[P⊓¬P]≡¬[P⊓Q]⇒[¬P≡Q] : ∀{ℓ } (P Q : hProp ℓ) → [ ¬ (P ⊓ ¬ P) ] ≡ [ ¬ (P ⊓ Q) ] → [ P ] ≡ [ ¬ Q ]
-- ¬[P⊓¬P]≡¬[P⊓Q]⇒[¬P≡Q] P Q p = {! [P⇒¬Q]≡¬[P⊓Q] P Q  !}
--
-- ¬[P⊓¬P]≡¬[P⊓Q]≡[P⇒¬Q]≡[P⇒¬¬P]

-- foo : ∀{ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ') → [ (P ⇒ ¬ Q) ] → [ (¬ Q ⇒ P) ] → P ≡ ¬ Q

-- bar : ∀{ℓ} (P Q : hProp ℓ) → [ ¬ (P ⊓ Q) ] → P ≡ ¬ Q
-- -- ¬-⊓-distrib P Q ¬p⊓q
-- bar P Q ¬p⊓q = let r1 : [ (P ⇒ ¬ Q) ⊓ (Q ⇒ ¬ P) ]
--                    r1 =
--                    r2 : [ (Q ⇒ ¬ P) ⊓ (P ⇒ ¬ Q) ]
--                    r2 =
--                in {! ¬-⊓-distrib Q P (transport (λ i → [ ¬ ⊓-comm P Q i ]) ¬p⊓q)  !}

-- more logic

⊓-⊔-distribʳ : (P : hProp ℓ) (Q : hProp ℓ')(R : hProp ℓ'')
  → (Q ⊔ R) ⊓ P ≡ (Q ⊓ P) ⊔ (R ⊓ P)
⊓-⊔-distribʳ P Q R = (
  (Q ⊔ R) ⊓ P       ≡⟨ ⊓-comm _ _ ⟩
   P ⊓ (Q ⊔ R)      ≡⟨ ⊓-⊔-distribˡ P Q R ⟩
  (P ⊓ Q) ⊔ (P ⊓ R) ≡⟨ ( λ i → ⊓-comm P Q i ⊔ ⊓-comm P R i) ⟩
  (Q ⊓ P) ⊔ (R ⊓ P) ∎)

-- NOTE: this is in the standard library
-- ⊓-∀-distrib :  (P : A → hProp ℓ) (Q : A → hProp ℓ')
--   → (∀[ a ∶ A ] P a) ⊓ (∀[ a ∶ A ] Q a) ≡ (∀[ a ∶ A ] (P a ⊓ Q a))
-- ⊓-∀-distrib P Q =
--   ⇒∶ (λ {(p , q) a → p a , q a})
--   ⇐∶ λ pq → (fst ∘ pq ) , (snd ∘ pq)

-- well, we do not have `∀-⊔-distrib`
-- ∀-⊔-distrib : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} → (P : A → hProp ℓ') → (Q : A → hProp ℓ'')
--             → ((∀[ x ∶ A ] P x) ⊔ (∀[ x ∶ A ] Q x)) ≡ (∀[ x ∶ A ] (P x ⊔ Q x))
-- ∀-⊔-distrib {A = A} P Q =
--   ⇒∶ (λ [∀xPx]⊔[∀xQx] x → ⊔-elim (∀[ x ] P x) (∀[ x ] Q x) (λ _ → P x ⊔ Q x) (λ ∀xPx → inlᵖ (∀xPx x)) (λ ∀xQx → inrᵖ (∀xQx x)) [∀xPx]⊔[∀xQx])
--   ⇐∶ λ ∀x[Px⊔Qx] → {!   !}

-- ∀-⊔-distribʳ : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} → (P : hProp ℓ') → (Q : A → hProp ℓ'')
--             → (P ⊔ (∀[ x ∶ A ] Q x)) ≡ (∀[ x ∶ A ] (P ⊔ Q x))
-- ∀-⊔-distribʳ {A = A} P Q =
--   ⇒∶ (λ [P]⊔[∀xQx] x → ⊔-elim P (∀[ x ] Q x) (λ _ → P ⊔ Q x) (λ p → inlᵖ p) (λ ∀xQx → inrᵖ (∀xQx x)) [P]⊔[∀xQx])
--   ⇐∶ λ ∀x[P⊔Qx] → {!   !}

-- ∀-⊎-distribʳ : ∀{ℓ ℓ' ℓ''} (a : Type ℓ) {B : Type ℓ'} (f : B → Type ℓ'')
--              → (a → ∀ b → ¬ᵗ f b) -- a implies that fb is wrong
--              → (∀ b → f b → ¬ᵗ a) -- b implies that a is wrong
--              → (∀ b → a ⊎ f b)    -- for all b, either a holds or fb holds
--              → a ⊎ (∀ b → f b)    -- either a holds or fb holds forall b
-- ∀-⊎-distribʳ a f a→¬fb fb→¬a g = {!   !}

-- hProp-union and Σ-Type-union are equivalent when the two disjuncts are disjoint such that one disproves the other and vice versa

⊎-Level : ∀{A : Type ℓ}{B : Type ℓ'} → A ⊎ B → Level
⊎-Level {ℓ  = ℓ } (inl x) = ℓ
⊎-Level {ℓ' = ℓ'} (inr x) = ℓ'

⊎-Type : ∀{A : Type ℓ}{B : Type ℓ'}(x : A ⊎ B) → Type (⊎-Level x)
⊎-Type {A = A} (inl x) = A
⊎-Type {B = B} (inr x) = B

⊎-pred : ∀{A : Type ℓ}{B : Type ℓ'}(x : A ⊎ B) → ⊎-Type x
⊎-pred (inl x) = x
⊎-pred (inr x) = x

⊎-predˡ : ∀{A : Type ℓ}{B : Type ℓ'}(z : A ⊎ B) → {y : A} → z ≡ inl y → A
⊎-predˡ (inl x) {y} p = x
⊎-predˡ (inr x) {y} p = y

inl-reflects-≡ : ∀{A : Type ℓ}{B : Type ℓ'} {x y : A} → ((A ⊎ B) ∋ inl x) ≡ inl y → x ≡ y
inl-reflects-≡ {A = A} {B = B} {x = x} {y = y} p =  cong γ p where
  γ : (z : A ⊎ B) → A
  γ (inl y) = y
  γ (inr y) = x

inr-reflects-≡ : ∀{A : Type ℓ}{B : Type ℓ'} {x y : B} → ((A ⊎ B) ∋ inr x) ≡ inr y → x ≡ y
inr-reflects-≡ {A = A} {B = B} {x = x} {y = y} p = cong γ p where
  γ : (z : A ⊎ B) → B
  γ (inl y) = x
  γ (inr y) = y

isProp⊎ : ∀{ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → isProp A → isProp B → (A → ¬ᵗ B) ⊎ (B → ¬ᵗ A) → isProp (A ⊎ B)
isProp⊎ pA pB      X⇒¬Y  (inl x) (inl y) = cong inl (pA x y)
isProp⊎ pA pB      X⇒¬Y  (inr x) (inr y) = cong inr (pB x y)
isProp⊎ pA pB (inl A⇒¬B) (inl x) (inr y) = ⊥-elim (A⇒¬B x y)
isProp⊎ pA pB (inr B⇒¬A) (inl x) (inr y) = ⊥-elim (B⇒¬A y x)
isProp⊎ pA pB (inl A⇒¬B) (inr x) (inl y) = ⊥-elim (A⇒¬B y x)
isProp⊎ pA pB (inr B⇒¬A) (inr x) (inl y) = ⊥-elim (B⇒¬A x y)

module _ {ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ')
         (X⇒¬Y : [ P ⇒ ¬ Q ] ⊎ [ Q ⇒ ¬ P ]) where

  ⊎-isProp : isProp ([ P ] ⊎ [ Q ])
  ⊎-isProp = isProp⊎ (isProp[] P) (isProp[] Q) X⇒¬Y

  P⊎Qᵖ : hProp (ℓ-max ℓ ℓ')
  P⊎Qᵖ = ([ P ] ⊎ [ Q ]) , ⊎-isProp

  -- ⊎⇒⊔' : [ P⊎Qᵖ ] → [ P ⊔ Q ]
  -- ⊎⇒⊔' x = ∣ x ∣

  ⊔⇒⊎ : [ P ⊔ Q ] → [ P⊎Qᵖ ]
  abstract ⊔⇒⊎ x = ⊔-elim P Q (λ x → ([ P ] ⊎ [ Q ]) , ⊎-isProp) (λ p → inl p) (λ q → inr q) x

  ⊔⊎-equiv : [ P⊎Qᵖ ⇔ P ⊔ Q ]
  ⊔⊎-equiv = ⊎⇒⊔ P Q , ⊔⇒⊎

  ⊔⊎-≡ : P⊎Qᵖ ≡ P ⊔ Q
  abstract
    ⊔⊎-≡ with ⊔⊎-equiv
    ... | p , q = ⇔toPath p q
