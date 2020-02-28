{-

In this file we apply the cubical machinery to Martin Hötzel-Escardó's
structure identity principle:

https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sns

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.SIP where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence renaming (ua-pathToEquiv to ua-pathToEquiv')
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.FunExtEquiv
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HAEquiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Prod.Base hiding (_×_) renaming (_×Σ_ to _×_)

private
 variable
  ℓ ℓ' ℓ'' ℓ''' ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level

-- For technical reasons we reprove ua-pathToEquiv using the
-- particular proof constructed by iso→HAEquiv. The reason is that we
-- want to later be able to extract
--
--   eq : ua-au (ua e) ≡ cong ua (au-ua e)
--
uaHAEquiv : (A B : Type ℓ) → HAEquiv (A ≃ B) (A ≡ B)
uaHAEquiv A B = iso→HAEquiv (iso ua pathToEquiv ua-pathToEquiv' pathToEquiv-ua)
open isHAEquiv

-- We now extract the particular proof constructed from iso→HAEquiv
-- for reasons explained above.
ua-pathToEquiv : {A B : Type ℓ} (e : A ≡ B) → ua (pathToEquiv e) ≡ e
ua-pathToEquiv e = uaHAEquiv _ _ .snd .ret e


-- A structure is a type-family S : Type ℓ → Type ℓ', i.e. for X : Type ℓ and s : S X, the pair (X , s)
-- means that X is equipped with a S-structure, which is witnessed by s.
-- An S-structure should have a notion of S-homomorphism, or rather S-isomorphism.
-- This will be implemented by a function ι
-- that gives us for any two types with S-structure (X , s) and (Y , t) a family:
--    ι (X , s) (Y , t) : (X ≃ Y) → Type ℓ''
-- Note that for any equivalence (f , e) : X ≃ Y the type  ι (X , s) (Y , t) (f , e) need not to be
-- a proposition. Indeed this type should correspond to the ways s and t can be identified
-- as S-structures. This we call a standard notion of structure or SNS.
-- We will use a different definition, but the two definitions are interchangeable.
SNS : (S : Type ℓ → Type ℓ')
    → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → A .fst ≃ B .fst → Type ℓ'')
    → Type (ℓ-max (ℓ-max(ℓ-suc ℓ) ℓ') ℓ'')
SNS  {ℓ = ℓ} S ι = ∀ {X : (Type ℓ)} (s t : S X) → ((s ≡ t) ≃ ι (X , s) (X , t) (idEquiv X))


-- We introduce the notation for structure preserving equivalences a bit differently,
-- but this definition doesn't actually change from Escardó's notes.
_≃[_]_ : {S : Type ℓ → Type ℓ'}
       → (A : Σ[ X ∈ (Type ℓ) ] (S X))
       → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → A .fst ≃ B .fst → Type ℓ'')
       → (B : Σ[ X ∈ (Type ℓ) ] (S X))
       → Type (ℓ-max ℓ ℓ'')
A ≃[ ι ] B = Σ[ f ∈ ((A .fst) ≃ (B. fst)) ] (ι A B f)

-- Before we can formulate our version of an SNS we introduce a bit of
-- notation and prove a few basic results. First, we define the
-- "cong-≃":
_⋆_ : (S : Type ℓ → Type ℓ') → {X Y : Type ℓ} → (X ≃ Y) → S X ≃ S Y
S ⋆ f = pathToEquiv (cong S (ua f))


-- Next, we prove a couple of helpful results about this ⋆ operation:
⋆-idEquiv : (S : Type ℓ → Type ℓ') (X : Type ℓ) → S ⋆ (idEquiv X) ≡ idEquiv (S X)
⋆-idEquiv S X = S ⋆ (idEquiv X)  ≡⟨ cong (λ p → pathToEquiv (cong S p)) uaIdEquiv  ⟩
                pathToEquiv refl ≡⟨ pathToEquivRefl ⟩
                idEquiv (S X)    ∎

⋆-char : (S : Type ℓ → Type ℓ') {X Y : Type ℓ} (f : X ≃ Y) → ua (S ⋆ f) ≡ cong S (ua f)
⋆-char S f = ua-pathToEquiv (cong S (ua f))

PathP-⋆-lemma : (S : Type ℓ → Type ℓ') (A B : Σ[ X ∈ (Type ℓ) ] (S X)) (f : A .fst ≃ B .fst)
    → (PathP (λ i →  ua (S ⋆ f) i) (A .snd) (B .snd)) ≡ (PathP (λ i → S ((ua f) i)) (A .snd) (B .snd))
PathP-⋆-lemma S A B f i = PathP (λ j → (⋆-char S f) i j) (A .snd) (B .snd)



-- Our new definition of standard notion of structure SNS' using the ⋆ notation.
-- This is easier to work with than SNS wrt Glue-types
SNS' : (S : Type ℓ → Type ℓ')
     → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → A .fst ≃ B .fst → Type ℓ'')
     → Type (ℓ-max (ℓ-max(ℓ-suc ℓ) ℓ') ℓ'')
SNS' S ι = (A B : Σ[ X ∈ (Type _) ] (S X)) → (f : A .fst ≃ B .fst)
         → (equivFun (S ⋆ f) (A .snd) ≡ (B .snd)) ≃ (ι A B f)

-- We can unfold SNS' as follows:
SNS'' : (S : Type ℓ → Type ℓ')
     → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → A .fst ≃ B .fst → Type ℓ'')
     → Type (ℓ-max (ℓ-max(ℓ-suc ℓ) ℓ') ℓ'')
SNS''  S ι = (A B : Σ[ X ∈ (Type _) ] (S X)) → (f : A .fst ≃ B .fst)
          → (transport (λ i → S (ua f i)) (A .snd) ≡ (B .snd)) ≃ (ι A B f)

SNS'≡SNS'' : (S : Type ℓ → Type ℓ')
           → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → A .fst ≃ B .fst → Type ℓ'')
           → SNS' S ι ≡ SNS'' S ι
SNS'≡SNS'' S ι = refl



-- A quick sanity-check that our definition is interchangeable with
-- Escardó's. The direction SNS→SNS' corresponds more or less to an
-- EquivJ formulation of Escardó's homomorphism-lemma.
SNS'→SNS : (S : Type ℓ → Type ℓ')
         → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → A .fst ≃ B .fst → Type ℓ'')
         → SNS' S ι → SNS S ι
SNS'→SNS S ι θ {X = X} s t = subst (λ x → (equivFun x s ≡ t) ≃ ι (X , s) (X , t) (idEquiv X)) (⋆-idEquiv S X) θ-id
  where
   θ-id = θ (X , s) (X , t) (idEquiv X)

SNS→SNS' : (S : Type ℓ → Type ℓ')
         → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → A .fst ≃ B .fst → Type ℓ'')
         → SNS S ι → SNS' S ι
SNS→SNS' S ι θ A B f = EquivJ P C (B .fst) (A .fst) f (B .snd) (A .snd)
  where
   P : (X Y : Type _) → Y ≃ X → Type _
   P X Y g = (s : S X) (t : S Y) → (equivFun (S ⋆ g) t ≡ s) ≃ ι (Y , t) (X , s) g

   C : (X : Type _) → (s t : S X) → (equivFun (S ⋆ (idEquiv X)) t ≡ s) ≃ ι (X , t) (X , s) (idEquiv X)
   C X s t = subst (λ u →  (u ≡ s) ≃ (ι (X , t) (X , s) (idEquiv X)))
                   (sym ( cong (λ f → (equivFun f) t) (⋆-idEquiv S X))) (θ t s)



-- The following transport-free version of SNS'' is a bit easier to
-- work with for the proof of the SIP
SNS''' : (S : Type ℓ → Type ℓ')
       → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → A .fst ≃ B .fst → Type ℓ'')
       → Type (ℓ-max (ℓ-max(ℓ-suc ℓ) ℓ') ℓ'')
SNS''' S ι = (A B : Σ[ X ∈ (Type _) ] (S X)) → (e : A .fst ≃ B .fst)
          → (PathP (λ i → S (ua e i)) (A .snd) (B .snd)) ≃ ι A B e

-- We can easily go between SNS'' (which is def. equal to SNS') and SNS'''
-- We should be able to find are more direct version of PathP≃Path for the family (λ i → S (ua f i))
-- using glue and unglue terms.
SNS''→SNS''' : {S : Type ℓ → Type ℓ'}
             → {ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → A .fst ≃ B .fst → Type ℓ''}
             → SNS'' S ι → SNS''' S ι
SNS''→SNS''' {S = S} h A B f =  PathP (λ i → S (ua f i)) (A .snd) (B .snd)
                             ≃⟨ PathP≃Path (λ i → S (ua f i)) (A .snd) (B .snd) ⟩
                                h A B f

SNS'''→SNS'' : (S : Type ℓ → Type ℓ')
             → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → A .fst ≃ B .fst → Type ℓ'')
             → SNS''' S ι → SNS'' S ι
SNS'''→SNS'' S ι h A B f =  transport (λ i → S (ua f i)) (A .snd) ≡ (B .snd)
                         ≃⟨ invEquiv (PathP≃Path (λ i → S (ua f i)) (A .snd) (B .snd)) ⟩
                            h A B f


-- We can now directly define a function
--    sip : A ≃[ ι ] B → A ≡ B
-- together with is inverse.
-- Here, these functions use SNS''' and are expressed using a Σ-type instead as it is a bit
-- easier to work with
sip : (S : Type ℓ → Type ℓ')
    → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → A .fst ≃ B .fst → Type ℓ'')
    → (θ : SNS''' S ι)
    → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
    → A ≃[ ι ] B
    → Σ (A .fst ≡ B .fst) (λ p → PathP (λ i → S (p i)) (A .snd) (B .snd))
sip S ι θ A B (e , p) = ua e , invEq (θ A B e) p

-- The inverse to sip using the following little lemma
lem : (S : Type ℓ → Type ℓ')
      (A B : Σ[ X ∈ (Type ℓ) ] (S X))
      (e : A .fst ≡ B .fst)
    → PathP (λ i → S (ua (pathToEquiv e) i)) (A .snd) (B .snd) ≡
      PathP (λ i → S (e i)) (A .snd) (B .snd)
lem S A B e i = PathP (λ j → S (ua-pathToEquiv e i j)) (A .snd) (B .snd)

sip⁻ : (S : Type ℓ → Type ℓ')
     → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → A .fst ≃ B .fst → Type ℓ'')
     → (θ : SNS''' S ι)
     → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
     → Σ (A .fst ≡ B .fst) (λ p → PathP (λ i → S (p i)) (A .snd) (B .snd))
     → A ≃[ ι ] B
sip⁻ S ι θ A B (e , r) = pathToEquiv e , θ A B (pathToEquiv e) .fst q
  where
  q : PathP (λ i → S (ua (pathToEquiv e) i)) (A .snd) (B .snd)
  q = transport (λ i → lem S A B e (~ i)) r


-- we can rather directly show that sip and sip⁻ are mutually inverse:
sip-sip⁻ : (S : Type ℓ → Type ℓ')
         → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → A .fst ≃ B .fst → Type ℓ'')
         → (θ : SNS''' S ι)
         → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
         → (r : Σ (A .fst ≡ B .fst) (λ p → PathP (λ i → S (p i)) (A .snd) (B .snd)))
         → sip S ι θ A B (sip⁻ S ι θ A B r) ≡ r
sip-sip⁻ S ι θ A B (p , q) =
    sip S ι θ A B (sip⁻ S ι θ A B (p , q))
  ≡⟨ refl ⟩
    ua (pathToEquiv p) , invEq (θ A B (pathToEquiv p)) (θ A B (pathToEquiv p) .fst (transport (λ i → lem S A B p (~ i)) q))
  ≡⟨ (λ i → ua (pathToEquiv p) , secEq (θ A B (pathToEquiv p)) (transport (λ i → lem S A B p (~ i)) q) i) ⟩
    ua (pathToEquiv p) , transport (λ i → lem S A B p (~ i)) q
  ≡⟨ (λ i → ua-pathToEquiv p i ,
            transp (λ k → PathP (λ j → S (ua-pathToEquiv p (i ∧ k) j)) (A .snd) (B .snd))
                   (~ i)
                   (transport (λ i → lem S A B p (~ i)) q)) ⟩
    p , transport (λ i → lem S A B p i) (transport (λ i → lem S A B p (~ i)) q)
  ≡⟨ (λ i → p , transportTransport⁻ (lem S A B p) q i) ⟩
    p , q ∎


-- The trickier direction:
sip⁻-sip : (S : Type ℓ → Type ℓ')
         → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → A .fst ≃ B .fst → Type ℓ'')
         → (θ : SNS''' S ι)
         → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
         → (r : A ≃[ ι ] B)
         → sip⁻ S ι θ A B (sip S ι θ A B r) ≡ r
sip⁻-sip S ι θ A B (e , p) =
    sip⁻ S ι θ A B (sip S ι θ A B (e , p))
  ≡⟨ refl ⟩
    pathToEquiv (ua e) , θ A B (pathToEquiv (ua e)) .fst (f⁺ p')
  ≡⟨ (λ i → pathToEquiv-ua e i , θ A B (pathToEquiv-ua e i) .fst (pth' i)) ⟩
    e , θ A B e .fst (f⁻ (f⁺ p'))
  ≡⟨ (λ i → e , θ A B e .fst (transportTransport⁻ (lem S A B (ua e)) p' i)) ⟩
    e , θ A B e .fst (invEq (θ A B e) p)
  ≡⟨ (λ i → e , (retEq (θ A B e) p i)) ⟩
    e , p ∎
  where
  p' : PathP (λ i → S (ua e i)) (A .snd) (B .snd)
  p' = invEq (θ A B e) p

  f⁺ : PathP (λ i → S (ua e i)) (A .snd) (B .snd)
     → PathP (λ i → S (ua (pathToEquiv (ua e)) i)) (A .snd) (B .snd)
  f⁺ = transport (λ i → PathP (λ j → S (ua-pathToEquiv (ua e) (~ i) j)) (A .snd) (B .snd))

  f⁻ : PathP (λ i → S (ua (pathToEquiv (ua e)) i)) (A .snd) (B .snd)
     → PathP (λ i → S (ua e i)) (A .snd) (B .snd)
  f⁻ = transport (λ i → PathP (λ j → S (ua-pathToEquiv (ua e) i j)) (A .snd) (B .snd))

  -- We can prove the following as in sip∘pis-id, but the type is not
  -- what we want as it should be "cong ua (pathToEquiv-ua e)"
  pth : PathP (λ j → PathP (λ k → S (ua-pathToEquiv (ua e) j k)) (A .snd) (B .snd))
              (f⁺ p') (f⁻ (f⁺ p'))
  pth i = transp (λ k → PathP (λ j → S (ua-pathToEquiv (ua e) (i ∧ k) j)) (A .snd) (B .snd))
                 (~ i)
                 (f⁺ p')

  -- So we build an equality that we want to cast the types with
  casteq : PathP (λ j → PathP (λ k → S (ua-pathToEquiv (ua e) j k)) (A .snd) (B .snd))
                 (f⁺ p') (f⁻ (f⁺ p'))
         ≡ PathP (λ j → PathP (λ k → S (cong ua (pathToEquiv-ua e) j k)) (A .snd) (B .snd))
                 (f⁺ p') (f⁻ (f⁺ p'))
  casteq i = PathP (λ j → PathP (λ k → S (eq i j k)) (A .snd) (B .snd)) (f⁺ p') (f⁻ (f⁺ p'))
    where
    -- This is where we need the half-adjoint equivalence property
    eq : ua-pathToEquiv (ua e) ≡ cong ua (pathToEquiv-ua e)
    eq = sym (uaHAEquiv (A .fst) (B .fst) .snd .com e)

  -- We then get a term of the type we need
  pth' : PathP (λ j → PathP (λ k → S (cong ua (pathToEquiv-ua e) j k)) (A .snd) (B .snd))
               (f⁺ p') (f⁻ (f⁺ p'))
  pth' = transport (λ i → casteq i) pth


-- Finally package everything up to get the cubical SIP
SIP : (S : Type ℓ → Type ℓ')
    → (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → A .fst ≃ B .fst → Type ℓ'')
    → (θ : SNS''' S ι)
    → (A B : Σ[ X ∈ (Type ℓ) ] (S X))
    → A ≃[ ι ] B ≃ (A ≡ B)
SIP S ι θ A B = (A ≃[ ι ] B ) ≃⟨ eq ⟩ Σ≡
  where
  eq : A ≃[ ι ] B ≃ Σ (A .fst ≡ B .fst) (λ p → PathP (λ i → S (p i)) (A .snd) (B .snd))
  eq = isoToEquiv (iso (sip S ι θ A B) (sip⁻ S ι θ A B)
                       (sip-sip⁻ S ι θ A B) (sip⁻-sip S ι θ A B))


-- Now, we want to add axioms (i.e. propositions) to our Structure S that don't affect the ι.
-- For this and the remainder of this file we will work with SNS'
-- We use a lemma due to Zesen Qian, which can now be found in Foundations.Prelude:
-- https://github.com/riaqn/cubical/blob/hgroup/Cubical/Data/Group/Properties.agda#L83
add-to-structure : (S : Type ℓ → Type ℓ')
                   (axioms : (X : Type ℓ) → (S X) → Type ℓ''')
                 → Type ℓ → Type (ℓ-max ℓ' ℓ''')
add-to-structure S axioms X = Σ[ s ∈ S X ] (axioms X s)

add-to-iso : (S : Type ℓ → Type ℓ')
             (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → A .fst ≃ B .fst → Type ℓ'')
             (axioms : (X : Type ℓ) → (S X) → Type ℓ''')
           → (A B : Σ[ X ∈ (Type ℓ) ] (add-to-structure S axioms X)) → A .fst ≃ B .fst
           → Type ℓ''
add-to-iso S ι axioms (X , (s , a)) (Y , (t , b)) f = ι (X , s) (Y , t) f

add-⋆-lemma : (S : Type ℓ → Type ℓ')
              (axioms : (X : Type ℓ) → (S X) → Type ℓ''')
              (axioms-are-Props : (X : Type ℓ) (s : S X) → isProp (axioms X s))
              {X Y : Type ℓ} {s : S X} {t : S Y} {a : axioms X s} {b : axioms Y t}
              (f : X ≃ Y)
            → (equivFun (add-to-structure S axioms ⋆ f) (s , a) ≡ (t , b)) ≃ (equivFun (S ⋆ f) s ≡ t)
add-⋆-lemma S axioms axioms-are-Props {Y = Y} {s = s} {t = t} {a = a} {b = b} f = isoToEquiv (iso φ ψ η ε)
      where
       φ : equivFun ((add-to-structure S axioms) ⋆ f) (s , a) ≡ (t , b)
         → equivFun (S ⋆ f) s ≡ t
       φ r i = r i .fst

       ψ : equivFun (S ⋆ f) s ≡ t
         → equivFun ((add-to-structure S axioms) ⋆ f) (s , a) ≡ (t , b)
       ψ p i = p i , isProp→PathP (λ j → axioms-are-Props Y (p j)) (equivFun (add-to-structure S axioms ⋆ f) (s , a) .snd) b i

       η : section φ ψ
       η p = refl

       ε : retract φ ψ
       ε r i j = r j .fst
               , isProp→isSet-PathP (λ k → axioms-are-Props Y (r k .fst)) _ _
                                    (isProp→PathP (λ j → axioms-are-Props Y (r j .fst))
                                                  (equivFun (add-to-structure S axioms ⋆ f) (s , a) .snd) b)
                                    (λ k → r k .snd) i j


add-axioms-SNS' : (S : Type ℓ → Type ℓ')
                  (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → A .fst ≃ B .fst → Type ℓ'')
                  (axioms : (X : Type ℓ) → (S X) → Type ℓ''')
                  (axioms-are-Props : (X : Type ℓ) (s : S X) → isProp (axioms X s))
                  (θ : SNS' S ι)
                → SNS' (add-to-structure S axioms) (add-to-iso S ι axioms)
add-axioms-SNS' S ι axioms axioms-are-Props θ (X , (s , a)) (Y , (t , b)) f =
               equivFun (add-to-structure S axioms ⋆ f) (s , a) ≡ (t , b) ≃⟨ add-⋆-lemma S axioms axioms-are-Props f ⟩
               equivFun (S ⋆ f) s ≡ t                                     ≃⟨ θ (X , s) (Y , t) f ⟩
               add-to-iso S ι axioms (X , (s , a)) (Y , (t , b)) f ■


-- Now, we want to join two structures. Together with the adding of
-- axioms this will allow us to prove that a lot of mathematical
-- structures are a standard notion of structure
technical-×-lemma : {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
                  → A ≃ C → B ≃ D → A × B ≃ C × D
technical-×-lemma {A = A} {B = B} {C = C} {D = D} f g = isoToEquiv (iso φ ψ η ε)
 where
  φ : (A × B) → (C × D)
  φ (a , b) = equivFun f a , equivFun g b

  ψ : (C × D) → (A × B)
  ψ (c , d) = equivFun (invEquiv f) c , equivFun (invEquiv g) d

  η : section φ ψ
  η (c , d) i = retEq f c i , retEq g d i

  ε : retract φ ψ
  ε (a , b) i = secEq f a i , secEq g b i


join-structure : (S₁ : Type ℓ₁ → Type ℓ₂) (S₂ : Type ℓ₁ → Type ℓ₄)
                → Type ℓ₁ → Type (ℓ-max ℓ₂ ℓ₄)
join-structure S₁ S₂ X = S₁ X × S₂ X

join-iso : {S₁ : Type ℓ₁ → Type ℓ₂}
           (ι₁ : (A B : Σ[ X ∈ (Type ℓ₁) ] (S₁ X)) → A .fst ≃ B .fst → Type ℓ₃)
           {S₂ : Type ℓ₁ → Type ℓ₄}
           (ι₂ : (A B : Σ[ X ∈ (Type ℓ₁) ] (S₂ X)) → A .fst ≃ B .fst → Type ℓ₅)
           (A B : Σ[ X ∈ (Type ℓ₁) ] (join-structure S₁ S₂ X))
         → A .fst ≃ B .fst
         → Type (ℓ-max ℓ₃ ℓ₅)
join-iso ι₁ ι₂ (X , s₁ , s₂) (Y , t₁ , t₂) f = (ι₁ (X , s₁) (Y , t₁) f) × (ι₂ (X , s₂) (Y , t₂) f)

join-⋆-lemma : (S₁ : Type ℓ₁ → Type ℓ₂) (S₂ : Type ℓ₁ → Type ℓ₄)
               {X Y : Type ℓ₁} {s₁ : S₁ X} {s₂ : S₂ X} {t₁ : S₁ Y} {t₂ : S₂ Y} (f : X ≃ Y)
             → (equivFun (join-structure S₁ S₂ ⋆ f) (s₁ , s₂) ≡ (t₁ , t₂)) ≃
               (equivFun (S₁ ⋆ f) s₁ ≡ t₁) × (equivFun (S₂ ⋆ f) s₂ ≡ t₂)
join-⋆-lemma S₁ S₂ {Y = Y} {s₁ = s₁} {s₂ = s₂} {t₁ = t₁} {t₂ = t₂} f = isoToEquiv (iso φ ψ η ε)
   where
    φ : equivFun (join-structure S₁ S₂ ⋆ f) (s₁ , s₂) ≡ (t₁ , t₂)
      → (equivFun (S₁ ⋆ f) s₁ ≡ t₁) × (equivFun (S₂ ⋆ f) s₂ ≡ t₂)
    φ p = (λ i → p i .fst) , (λ i → p i .snd)

    ψ : (equivFun (S₁ ⋆ f) s₁ ≡ t₁) × (equivFun (S₂ ⋆ f) s₂ ≡ t₂)
      → equivFun (join-structure S₁ S₂ ⋆ f) (s₁ , s₂) ≡ (t₁ , t₂)
    ψ (p , q) i = (p i) , (q i)

    η : section φ ψ
    η (p , q) = refl

    ε : retract φ ψ
    ε p = refl

join-SNS' : (S₁ : Type ℓ₁ → Type ℓ₂)
            (ι₁ : (A B : Σ[ X ∈ (Type ℓ₁) ] (S₁ X)) → A .fst ≃ B .fst → Type ℓ₃)
            (θ₁ : SNS' S₁ ι₁)
            (S₂ : Type ℓ₁ → Type ℓ₄)
            (ι₂ : (A B : Σ[ X ∈ (Type ℓ₁) ] (S₂ X)) → A .fst ≃ B .fst → Type ℓ₅)
            (θ₂ : SNS' S₂ ι₂)
          → SNS' (join-structure S₁ S₂) (join-iso ι₁ ι₂)
join-SNS' S₁ ι₁ θ₁ S₂ ι₂ θ₂ (X , s₁ , s₂) (Y , t₁ , t₂) f =
    equivFun (join-structure S₁ S₂ ⋆ f) (s₁ , s₂) ≡ (t₁ , t₂)
  ≃⟨ join-⋆-lemma S₁ S₂ f ⟩
    (equivFun (S₁ ⋆ f) s₁ ≡ t₁) × (equivFun (S₂ ⋆ f) s₂ ≡ t₂)
  ≃⟨ technical-×-lemma (θ₁ (X , s₁) (Y , t₁) f) (θ₂ (X , s₂) (Y , t₂) f)  ⟩
    join-iso ι₁ ι₂ (X , s₁ , s₂) (Y , t₁ , t₂) f ■


-- Now, we want to do Monoids as an example. We begin by showing SNS' for simple structures, i.e. pointed types and ∞-magmas.
-- Pointed types with SNS'
pointed-structure : Type ℓ → Type ℓ
pointed-structure X = X

Pointed-Type : Type (ℓ-suc ℓ)
Pointed-Type {ℓ = ℓ} = Σ (Type ℓ) pointed-structure

pointed-iso : (A B : Pointed-Type) → A .fst ≃ B .fst → Type ℓ
pointed-iso A B f = equivFun f (A .snd) ≡ B .snd

pointed-is-SNS' : SNS' {ℓ = ℓ} pointed-structure pointed-iso
pointed-is-SNS' A B f = transportEquiv (λ i → transportRefl (equivFun f (A .snd)) i ≡ B .snd)


-- ∞-Magmas with SNS'
-- We need function extensionality for binary functions.
-- TODO: upstream
funExtBin : {A : Type ℓ} {B : A → Type ℓ'} {C : (x : A) → B x → Type ℓ''} {f g : (x : A) → (y : B x) → C x y}
           → ((x : A) (y : B x) → f x y ≡ g x y) → f ≡ g
funExtBin p i x y = p x y i
module _ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : (x : A) → B x → Type ℓ''} {f g : (x : A) → (y : B x) → C x y} where
  private
    appl₂ : f ≡ g → ∀ x y → f x y ≡ g x y
    appl₂ eq x y i = eq i x y

    fib : (p : f ≡ g) → fiber funExtBin p
    fib p = (appl₂ p , refl)

    funExtBin-fiber-isContr
      : (p : f ≡ g)
      → (fi : fiber funExtBin p)
      → fib p ≡ fi
    funExtBin-fiber-isContr p (h , eq) i = (appl₂ (eq (~ i)) , λ j → eq (~ i ∨ j))

  funExtBin-isEquiv : isEquiv funExtBin
  equiv-proof funExtBin-isEquiv p = (fib p , funExtBin-fiber-isContr p)

  funExtBinEquiv : (∀ x y → f x y ≡ g x y) ≃ (f ≡ g)
  funExtBinEquiv = (funExtBin , funExtBin-isEquiv)

-- ∞-Magmas
∞-magma-structure : Type ℓ → Type ℓ
∞-magma-structure X = X → X → X

∞-Magma : Type (ℓ-suc ℓ)
∞-Magma {ℓ = ℓ} = Σ (Type ℓ) ∞-magma-structure

∞-magma-iso : (A B : ∞-Magma) → A .fst ≃ B .fst → Type ℓ
∞-magma-iso (X , _·_) (Y , _∗_) f = (x x' : X) → equivFun f (x · x') ≡ (equivFun f x) ∗ (equivFun f x')

∞-magma-is-SNS' : SNS' {ℓ = ℓ} ∞-magma-structure ∞-magma-iso
∞-magma-is-SNS' (X , _·_) (Y , _∗_) f = SNS→SNS' ∞-magma-structure ∞-magma-iso C (X , _·_) (Y , _∗_) f
 where
  C : {X : Type ℓ} (_·_ _∗_ : X → X → X) → (_·_ ≡ _∗_) ≃ ((x x' : X) → (x · x') ≡ (x ∗ x'))
  C _·_ _∗_ = invEquiv funExtBinEquiv



-- Now we're getting serious: Monoids
raw-monoid-structure : Type ℓ → Type ℓ
raw-monoid-structure X = X × (X → X → X)


raw-monoid-iso : (M N : Σ (Type ℓ) raw-monoid-structure) → (M .fst) ≃ (N .fst) → Type ℓ
raw-monoid-iso (M , e , _·_) (N , d , _∗_) f = (equivFun f e ≡ d)
                        × ((x y : M) → equivFun f (x · y) ≡ (equivFun f x) ∗ (equivFun f y))

-- If we ignore the axioms we get something like a "raw" monoid, which essentially is the join of a pointed type and an ∞-magma
raw-monoid-is-SNS' : SNS' {ℓ = ℓ} raw-monoid-structure raw-monoid-iso
raw-monoid-is-SNS' = join-SNS' pointed-structure pointed-iso pointed-is-SNS'
                               ∞-magma-structure ∞-magma-iso ∞-magma-is-SNS'

-- Now define monoids
monoid-axioms : (X : Type ℓ) → raw-monoid-structure X → Type ℓ
monoid-axioms X (e , _·_ ) = isSet X
                           × ((x y z : X) → (x · (y · z)) ≡ ((x · y) · z))
                           × ((x : X) → (x · e) ≡ x)
                           × ((x : X) → (e · x) ≡ x)

monoid-structure : Type ℓ → Type ℓ
monoid-structure = add-to-structure (raw-monoid-structure) monoid-axioms

-- TODO: it might be nicer to formulate the SIP lemmas so that they're
-- easier to use for things that are not "completely packaged"
Monoids : Type (ℓ-suc ℓ)
Monoids = Σ (Type _) monoid-structure

monoid-iso : (M N : Monoids) → M .fst ≃ N .fst → Type ℓ
monoid-iso = add-to-iso raw-monoid-structure raw-monoid-iso monoid-axioms

-- We have to show that the monoid axioms are indeed Propositions
monoid-axioms-are-Props : (X : Type ℓ) (s : raw-monoid-structure X) → isProp (monoid-axioms X s)
monoid-axioms-are-Props X (e , _·_) s = β s
   where
   α = s .fst
   β =      isOfHLevelΣ 1 isPropIsSet
      λ _ → isOfHLevelΣ 1 (isOfHLevelPi 1 (λ x → isOfHLevelPi 1 λ y → isOfHLevelPi 1 λ z → α (x · (y · z)) ((x · y) · z)))
      λ _ → isOfHLevelΣ 1 (isOfHLevelPi 1 λ x → α (x · e) x)
      λ _ →                isOfHLevelPi 1 λ x → α (e · x) x

monoid-is-SNS' : SNS' {ℓ = ℓ} monoid-structure monoid-iso
monoid-is-SNS' = add-axioms-SNS' raw-monoid-structure raw-monoid-iso
                                 monoid-axioms monoid-axioms-are-Props raw-monoid-is-SNS'

MonoidPath : (M N : Monoids {ℓ}) → (M ≃[ monoid-iso ] N) ≃ (M ≡ N)
MonoidPath M N = SIP monoid-structure monoid-iso (SNS''→SNS''' monoid-is-SNS') M N
