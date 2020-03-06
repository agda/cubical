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
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties renaming (cong≃ to _⋆_)
open import Cubical.Foundations.HAEquiv
open import Cubical.Data.Sigma
open import Cubical.Data.Prod.Base hiding (_×_) renaming (_×Σ_ to _×_)

open import Cubical.Foundations.Structure public

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level
    S : Type ℓ → Type ℓ'

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


-- Note that for any equivalence (f , e) : X ≃ Y the type  ι (X , s) (Y , t) (f , e) need not to be
-- a proposition. Indeed this type should correspond to the ways s and t can be identified
-- as S-structures. This we call a standard notion of structure or SNS.
-- We will use a different definition, but the two definitions are interchangeable.
SNS₁ : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') → Type (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') ℓ'')
SNS₁ {ℓ} S ι = ∀ {X : Type ℓ} (s t : S X) → ((s ≡ t) ≃ ι (X , s) (X , t) (idEquiv X))


-- We introduce the notation for structure preserving equivalences a bit differently,
-- but this definition doesn't actually change from Escardó's notes.
_≃[_]_ : (A : TypeWithStr ℓ S) (ι : StrIso S ℓ') (B : TypeWithStr ℓ S) → Type (ℓ-max ℓ ℓ')
A ≃[ ι ] B = Σ[ f ∈ (typ A ≃ typ B) ] (ι A B f)



-- The following PathP version of SNS₁ is a bit easier to
-- work with for the proof of the SIP
SNS₂ : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') → Type (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') ℓ'')
SNS₂ {ℓ} S ι = (A B : TypeWithStr ℓ S) (e : typ A ≃ typ B)
             → (PathP (λ i → S (ua e i)) (str A) (str B)) ≃ (ι A B e)

-- A quick sanity-check that our definition is interchangeable with
-- Escardó's. The direction SNS₁→SNS₂ corresponds more or less to a
-- dependent EquivJ formulation of Escardó's homomorphism-lemma.
SNS₂→SNS₁ : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') → SNS₂ S ι → SNS₁ S ι
SNS₂→SNS₁ S ι θ {X = X} s t =  s ≡ t ≃⟨ φ ⟩ θ (X , s) (X , t) (idEquiv X)
  where
   φ = transportEquiv λ j → PathP (λ i → S (uaIdEquiv {A = X} (~ j) i)) s t


SNS₁→SNS₂ : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') → SNS₁ S ι → SNS₂ S ι
SNS₁→SNS₂ S ι θ A B e = EquivJ P C (typ B) (typ A) e (str B) (str A)
  where
   P : (X Y : Type _) → Y ≃ X → Type _
   P X Y e' = (s : S X) (t : S Y) → PathP (λ i → S (ua e' i)) t s ≃ ι (Y , t) (X , s) e'

   C : (X : Type _) → (s t : S X) → PathP (λ i → S (ua (idEquiv X) i)) t s ≃ ι (X , t) (X , s) (idEquiv X)
   C X s t = PathP (λ i → S (ua (idEquiv X) i)) t s ≃⟨ ψ ⟩ θ t s
    where
     ψ = transportEquiv λ j → PathP (λ i → S (uaIdEquiv {A = X} j i)) t s







-- We can now directly define a function
--    sip : A ≃[ ι ] B → A ≡ B
-- together with is inverse.
-- Here, these functions use SNS₂ and are expressed using a Σ-type instead as it is a bit
-- easier to work with
sip : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') (θ : SNS₂ S ι)
    → (A B : TypeWithStr ℓ S)
    → A ≃[ ι ] B
    → Σ (typ A ≡ typ B) (λ p → PathP (λ i → S (p i)) (str A) (str B))
sip S ι θ A B (e , p) = ua e , invEq (θ A B e) p

-- The inverse to sip using the following little lemma

private
  lem : (S : Type ℓ → Type ℓ') (A B : TypeWithStr ℓ S) (e : typ A ≡ typ B)
      → PathP (λ i → S (ua (pathToEquiv e) i)) (A .snd) (B .snd) ≡
        PathP (λ i → S (e i)) (A .snd) (B .snd)
  lem S A B e i = PathP (λ j → S (ua-pathToEquiv e i j)) (A .snd) (B .snd)

sip⁻ : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') (θ : SNS₂ S ι)
     → (A B : TypeWithStr ℓ S)
     → Σ (typ A ≡ typ B) (λ p → PathP (λ i → S (p i)) (str A) (str B))
     → A ≃[ ι ] B
sip⁻ S ι θ A B (e , r) = pathToEquiv e , θ A B (pathToEquiv e) .fst q
  where
  q : PathP (λ i → S (ua (pathToEquiv e) i)) (A .snd) (B .snd)
  q = transport (λ i → lem S A B e (~ i)) r


-- we can rather directly show that sip and sip⁻ are mutually inverse:
sip-sip⁻ : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') (θ : SNS₂ S ι)
         → (A B : TypeWithStr ℓ S)
         → (r : Σ (typ A ≡ typ B) (λ p → PathP (λ i → S (p i)) (str A) (str B)))
         → sip S ι θ A B (sip⁻ S ι θ A B r) ≡ r
sip-sip⁻ S ι θ A B (p , q) =
    sip S ι θ A B (sip⁻ S ι θ A B (p , q))
  ≡⟨ refl ⟩
    ua (pathToEquiv p) , invEq (θ A B (pathToEquiv p)) (θ A B (pathToEquiv p) .fst (transport (λ i → lem S A B p (~ i)) q))
  ≡⟨ (λ i → ua (pathToEquiv p) , secEq (θ A B (pathToEquiv p)) (transport (λ i → lem S A B p (~ i)) q) i) ⟩
    ua (pathToEquiv p) , transport (λ i → lem S A B p (~ i)) q
  ≡⟨ (λ i → ua-pathToEquiv p i ,
            transp (λ k → PathP (λ j → S (ua-pathToEquiv p (i ∧ k) j)) (str A) (str B))
                   (~ i)
                   (transport (λ i → lem S A B p (~ i)) q)) ⟩
    p , transport (λ i → lem S A B p i) (transport (λ i → lem S A B p (~ i)) q)
  ≡⟨ (λ i → p , transportTransport⁻ (lem S A B p) q i) ⟩
    p , q ∎


-- The trickier direction:
sip⁻-sip : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') (θ : SNS₂ S ι)
         → (A B : TypeWithStr ℓ S)
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
  p' : PathP (λ i → S (ua e i)) (str A) (str B)
  p' = invEq (θ A B e) p

  f⁺ : PathP (λ i → S (ua e i)) (str A) (str B)
     → PathP (λ i → S (ua (pathToEquiv (ua e)) i)) (str A) (str B)
  f⁺ = transport (λ i → PathP (λ j → S (ua-pathToEquiv (ua e) (~ i) j)) (str A) (str B))

  f⁻ : PathP (λ i → S (ua (pathToEquiv (ua e)) i)) (str A) (str B)
     → PathP (λ i → S (ua e i)) (str A) (str B)
  f⁻ = transport (λ i → PathP (λ j → S (ua-pathToEquiv (ua e) i j)) (str A) (str B))

  -- We can prove the following as in sip∘pis-id, but the type is not
  -- what we want as it should be "cong ua (pathToEquiv-ua e)"
  pth : PathP (λ j → PathP (λ k → S (ua-pathToEquiv (ua e) j k)) (str A) (str B))
              (f⁺ p') (f⁻ (f⁺ p'))
  pth i = transp (λ k → PathP (λ j → S (ua-pathToEquiv (ua e) (i ∧ k) j)) (str A) (str B))
                 (~ i)
                 (f⁺ p')

  -- So we build an equality that we want to cast the types with
  casteq : PathP (λ j → PathP (λ k → S (ua-pathToEquiv (ua e) j k)) (str A) (str B))
                 (f⁺ p') (f⁻ (f⁺ p'))
         ≡ PathP (λ j → PathP (λ k → S (cong ua (pathToEquiv-ua e) j k)) (str A) (str B))
                 (f⁺ p') (f⁻ (f⁺ p'))
  casteq i = PathP (λ j → PathP (λ k → S (eq i j k)) (str A) (str B)) (f⁺ p') (f⁻ (f⁺ p'))
    where
    -- This is where we need the half-adjoint equivalence property
    eq : ua-pathToEquiv (ua e) ≡ cong ua (pathToEquiv-ua e)
    eq = sym (uaHAEquiv (typ A) (typ B) .snd .com e)

  -- We then get a term of the type we need
  pth' : PathP (λ j → PathP (λ k → S (cong ua (pathToEquiv-ua e) j k)) (str A) (str B))
               (f⁺ p') (f⁻ (f⁺ p'))
  pth' = transport (λ i → casteq i) pth


-- Finally package everything up to get the cubical SIP
SIP : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') (θ : SNS₂ S ι)
    → (A B : TypeWithStr ℓ S)
    → A ≃[ ι ] B ≃ (A ≡ B)
SIP S ι θ A B = (A ≃[ ι ] B ) ≃⟨ eq ⟩ Σ≡
  where
  eq : A ≃[ ι ] B ≃ Σ (A .fst ≡ B .fst) (λ p → PathP (λ i → S (p i)) (A .snd) (B .snd))
  eq = isoToEquiv (iso (sip S ι θ A B) (sip⁻ S ι θ A B)
                       (sip-sip⁻ S ι θ A B) (sip⁻-sip S ι θ A B))


-- Now, we want to add axioms (i.e. propositions) to our Structure S that don't affect the ι.
-- For this and the remainder of this file we will work with SNS₂
-- We use a lemma due to Zesen Qian, which can now be found in Foundations.Prelude:
-- https://github.com/riaqn/cubical/blob/hgroup/Cubical/Data/Group/Properties.agda#L83

add-to-structure : (S : Type ℓ → Type ℓ')
                   (axioms : (X : Type ℓ) → (S X) → Type ℓ''')
                 → Type ℓ → Type (ℓ-max ℓ' ℓ''')
add-to-structure S axioms X = Σ[ s ∈ S X ] (axioms X s)

add-to-iso : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'')
             (axioms : (X : Type ℓ) → (S X) → Type ℓ''')
           → StrIso (add-to-structure S axioms) ℓ''
add-to-iso S ι axioms (X , (s , a)) (Y , (t , b)) f = ι (X , s) (Y , t) f


add-ax-lemma :  (S : Type ℓ → Type ℓ')
              (axioms : (X : Type ℓ) → (S X) → Type ℓ''')
              (axioms-are-Props : (X : Type ℓ) (s : S X) → isProp (axioms X s))
              {X Y : Type ℓ} {s : S X} {t : S Y} {a : axioms X s} {b : axioms Y t}
              (f : X ≃ Y)
            → PathP (λ i → (add-to-structure S axioms) (ua f i)) (s , a) (t , b) ≃ PathP (λ i → S (ua f i)) s t
add-ax-lemma S axioms axioms-are-Props {Y = Y} {s = s} {t = t} {a = a} {b = b} f = isoToEquiv (iso φ ψ η ε)
      where
       φ : PathP (λ i → (add-to-structure S axioms) (ua f i)) (s , a) (t , b) → PathP (λ i → S (ua f i)) s t
       φ r i = r i .fst

       ψ : PathP (λ i → S (ua f i)) s t → PathP (λ i → (add-to-structure S axioms) (ua f i)) (s , a) (t , b)
       ψ p i = p i , isProp→PathP (λ i → axioms-are-Props (ua f i) (p i)) a b i

       η : section φ ψ
       η p = refl

       ε : retract φ ψ
       ε r i j =  r j .fst , isProp→isSet-PathP (λ k → axioms-are-Props (ua f k) (r k .fst)) _ _
                                                (isProp→PathP (λ k → axioms-are-Props (ua f k) (r k .fst)) a b)
                                                (λ k → r k .snd) i j



add-axioms-SNS : (S : Type ℓ → Type ℓ')
                    (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → A .fst ≃ B .fst → Type ℓ'')
                    (axioms : (X : Type ℓ) → (S X) → Type ℓ''')
                    (axioms-are-Props : (X : Type ℓ) (s : S X) → isProp (axioms X s))
                    (θ : SNS₂ S ι)
                   → SNS₂ (add-to-structure S axioms) (add-to-iso S ι axioms)
add-axioms-SNS S ι axioms axioms-are-Props θ (X , (s , a)) (Y , (t , b)) f =

               PathP (λ i → (add-to-structure S axioms) (ua f i)) (s , a) (t , b) ≃⟨ add-ax-lemma S axioms axioms-are-Props f ⟩
               PathP (λ i → S (ua f i)) s t                                       ≃⟨ θ (X , s) (Y , t) f ⟩
               add-to-iso S ι axioms (X , (s , a)) (Y , (t , b)) f ■









-- Now, we want to join two structures. Together with the adding of
-- axioms this will allow us to prove that a lot of mathematical
-- structures are a standard notion of structure

private
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

join-iso : {S₁ : Type ℓ₁ → Type ℓ₂} (ι₁ : StrIso S₁ ℓ₃)
           {S₂ : Type ℓ₁ → Type ℓ₄} (ι₂ : StrIso S₂ ℓ₅)
         → StrIso (join-structure S₁ S₂) (ℓ-max ℓ₃ ℓ₅)
join-iso ι₁ ι₂ (X , s₁ , s₂) (Y , t₁ , t₂) f = (ι₁ (X , s₁) (Y , t₁) f) × (ι₂ (X , s₂) (Y , t₂) f)


-- We do the same with SNS₂
join-lemma :  (S₁ : Type ℓ₁ → Type ℓ₂) (S₂ : Type ℓ₁ → Type ℓ₄)
              {X Y : Type ℓ₁} {s₁ : S₁ X} {s₂ : S₂ X} {t₁ : S₁ Y} {t₂ : S₂ Y} (e : X ≃ Y)
            → PathP (λ i → (join-structure S₁ S₂) (ua e i)) (s₁ , s₂) (t₁ , t₂) ≃
             (PathP (λ i → S₁ (ua e i)) s₁ t₁) × (PathP (λ i → S₂ (ua e i)) s₂ t₂)
join-lemma S₁ S₂ {Y = Y} {s₁ = s₁} {s₂ = s₂} {t₁ = t₁} {t₂ = t₂} e =  isoToEquiv (iso φ ψ η ε)
   where
    φ :  PathP (λ i → (join-structure S₁ S₂) (ua e i)) (s₁ , s₂) (t₁ , t₂) →
        (PathP (λ i → S₁ (ua e i)) s₁ t₁) × (PathP (λ i → S₂ (ua e i)) s₂ t₂)
    φ p = (λ i → p i .fst) , (λ i → p i .snd)

    ψ : (PathP (λ i → S₁ (ua e i)) s₁ t₁) × (PathP (λ i → S₂ (ua e i)) s₂ t₂) →
         PathP (λ i → (join-structure S₁ S₂) (ua e i)) (s₁ , s₂) (t₁ , t₂)
    ψ (p , q) i = (p i) , (q i)

    η : section φ ψ
    η (p , q) = refl

    ε : retract φ ψ
    ε p = refl



-- join-lemma' :  (S₁ : Type ℓ₁ → Type ℓ₂) (S₂ : Type ℓ₁ → Type ℓ₄)
--               {X Y : Type ℓ₁} {s₁ : S₁ X} {s₂ : S₂ X} {t₁ : S₁ Y} {t₂ : S₂ Y} (e : X ≃ Y)
--             → PathP (λ i → (join-structure S₁ S₂) (ua e i)) (s₁ , s₂) (t₁ , t₂) ≃
--              (PathP (λ i → S₁ (ua e i)) s₁ t₁) × (PathP (λ i → S₂ (ua e i)) s₂ t₂)
-- join-lemma' S₁ S₂ {Y = Y} {s₁ = s₁} {s₂ = s₂} {t₁ = t₁} {t₂ = t₂} e = φ , isEquivφ
--  where
--   φ = (λ p → (λ i → p i .fst) , (λ i → p i .snd))

--   isEquivφ : isEquiv φ
--   isEquivφ .equiv-proof r .fst .fst = (λ i → r .fst i , r .snd i)
--   isEquivφ .equiv-proof r .fst .snd = refl
--   isEquivφ .equiv-proof r .snd y =  {!!} --subst (λ u → fst (isEquivφ .equiv-proof u) ≡ y) (y .snd) refl



join-SNS : (S₁ : Type ℓ₁ → Type ℓ₂) (ι₁ : StrIso S₁ ℓ₃) (θ₁ : SNS₂ S₁ ι₁)
           (S₂ : Type ℓ₁ → Type ℓ₄) (ι₂ : StrIso S₂ ℓ₅) (θ₂ : SNS₂ S₂ ι₂)
         → SNS₂ (join-structure S₁ S₂) (join-iso ι₁ ι₂)
join-SNS S₁ ι₁ θ₁ S₂ ι₂ θ₂ (X , s₁ , s₂) (Y , t₁ , t₂) e =

     PathP (λ i → (join-structure S₁ S₂) (ua e i)) (s₁ , s₂) (t₁ , t₂)
  ≃⟨ join-lemma S₁ S₂ e ⟩
    (PathP (λ i → S₁ (ua e i)) s₁ t₁) × (PathP (λ i → S₂ (ua e i)) s₂ t₂)
  ≃⟨ technical-×-lemma (θ₁ (X , s₁) (Y , t₁) e) (θ₂ (X , s₂) (Y , t₂) e)  ⟩
     join-iso ι₁ ι₂ (X , s₁ , s₂) (Y , t₁ , t₂) e ■
