{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.FunLoopSpace where



open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.FunExtEquiv
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Nat
open import Cubical.Data.HomotopyGroup

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'





{- Beware: Use of J -}
cancelReflMid : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) (q : b ≡ a) → p ∙ refl ∙ q ≡ p ∙ q
cancelReflMid {ℓ = ℓ}{A = A} {a = a} {b = b} p q = J {ℓ} {A} {a} {ℓ} (λ b p → ((q : b ≡ a) →  p ∙ refl ∙ q ≡ p ∙ q)) (λ r → sym (lUnit (refl  ∙ r ))) {b} p q

---


FunLR : (n : ℕ) {f : A → B} →
        ((typ ((Ω^ (suc n)) ((A → B) , f))) →
        (((x : A) → (typ ((Ω^ (suc n)) (B , f x))))))
LR-id : (n : ℕ) {f : A → B} → FunLR n {f} refl ≡ (λ x → refl)
FunLR zero {f} = funExt⁻
FunLR (suc n) {f} p x = cong (λ y → y x) (sym (LR-id n)) ∙ (funExt⁻ (cong  (FunLR n)  p ) x) ∙ cong (λ y → y x)  (LR-id n)
LR-id zero {f} = refl
LR-id (suc n) {f} = funExt λ y → (cancelReflMid (λ i → (LR-id n) (~ i) y)
                                                      (λ i → (LR-id n {f}) i y) ∙
                                                        rCancel (λ i → (LR-id  n {f}) (~ i) y))

{-
lemma2 : (n : ℕ) {f : A → B} {x : A} → PathP (λ i → LR-id n {f} i x ≡ λ _  → pt ((Ω^ n) (B , f x))) (cong (λ y → y x) ((LR-id n {f}))) refl
lemma2 zero = refl
lemma2 (suc n) {f} {x} j = hcomp {!!} {!(cong (λ y → y x) (funExt (λ y → cancelReflMid (λ i → LR-id n {f} (~ (i)) y) (λ i → LR-id n {f} (i ∨ j) y) ∙ rCancel (λ i → LR-id n ((~ i)) y)))) !}
-}


FunRL : (n : ℕ) {f : A → B} →
        ((x : A) → (typ ((Ω^ (suc n)) (B , f x)))) →
        ((typ ((Ω^ (suc n)) ((A → B) , f))))
RL-id : (n : ℕ) {f : A → B} →
        FunRL n (λ x → pt (((Ω^ (suc n)) (B , f x)))) ≡ pt  ((Ω^ (suc n)) ((A → B) , f))
FunRL zero = funExt
FunRL (suc n) {f} = λ g → (sym (RL-id n {f}) ∙ cong (FunRL n {f}) (funExt g) ∙ (RL-id n {f}))
RL-id zero = refl
RL-id (suc n) {f} = cancelReflMid (λ i → (RL-id n {f}) (~ i)) (RL-id n) ∙
                                          rCancel (λ i → (RL-id n) (~ i))



----



wantToShow : (n : ℕ) (f : A → B) →
             ((x : A) → (typ ((Ω^ n) (B , f x)))) ≡ (typ ((Ω^ n) ((A → B) , f)))
wantToShow zero f = refl
wantToShow (suc zero) f = ua funExtEquiv
wantToShow (suc (suc n)) f = isoToPath (iso (FunRL (suc n)) (FunLR (suc n)) (λ b → {!!}) {!!}) 
  where
  hauptLemma : (n : ℕ) (f : A → B) (b : typ (Ω ((Ω^ n) ((A → B) , f)))) → FunRL n (FunLR n b ) ≡ b
  hauptLemma zero f b = refl
  hauptLemma (suc n) f b = {!!}
    where

    oi : {!λ j → ((λ i → RL-id n {f} (~ i)) ∙
                          (λ i → (hauptLemma n f (b i) (i))) ∙
                          (λ i →  RL-id n {f} i))!}
    oi = {!!}


    firstTransp : PathP (λ j → RL-id n (~ j) ≡ RL-id n (~ j))
                        (FunRL (suc n) (FunLR (suc n) b ))
                        ((λ i → FunRL n {f} (funExt (λ x → (λ i₁ → LR-id n {f} (~ i₁) x) ∙ (λ i₁ → FunLR n {f} (b i₁) x) ∙ (λ i₁ → LR-id n {f} i₁ x)) i)))
    firstTransp j = hcomp (λ k → λ{(j = i0) → FunRL (suc n) (FunLR (suc n) b ) ;
                                   (j = i1) → (sym (lUnit ((λ i → FunRL n (funExt (λ x → (λ i₁ → LR-id n (~ i₁) x) ∙
                                                           (λ i₁ → FunLR n {f} (b i₁) x) ∙ (λ i₁ → LR-id n {f} i₁ x)) i)) ∙
                                                           (λ i →  RL-id n {f} (i0)))) ∙
                                               sym (rUnit (λ i → FunRL n (funExt (λ x → (λ i₁ → LR-id n (~ i₁) x) ∙
                                                           (λ i₁ → FunLR n {f} (b i₁) x) ∙
                                                           (λ i₁ → LR-id n {f} i₁ x)) i)))) k })
                          ((λ i → RL-id n {f} (~ i ∧ ( ~ j))) ∙
                          (λ i → FunRL n (funExt (λ x → (λ i₁ → LR-id n (~ i₁) x) ∙
                          (λ i₁ → FunLR n {f} (b i₁) x) ∙
                          (λ i₁ → LR-id n {f} i₁ x)) i)) ∙
                          (λ i →  RL-id n {f} (i ∧ (~ j))))

    SNDtransp : PathP (λ j → (FunRL n {f} (λ x → LR-id n {f} (~ j) x)) ≡ (FunRL n {f} (λ x → LR-id n {f} (~ j) x)))
                          ((λ i → FunRL n {f} (funExt (λ x → (λ i₁ → LR-id n (~ i₁) x) ∙
                          (λ i₁ → FunLR n {f} (b i₁) x) ∙
                          (λ i₁ → LR-id n {f} i₁ x)) i))) λ i → FunRL n {f} (FunLR n {f} (b i))
    SNDtransp j = hcomp (λ k → λ{ (j = i0) → 
                          ((λ i → FunRL n (funExt (λ x → (λ i₁ → LR-id n (~ i₁) x) ∙
                          (λ i₁ → FunLR n {f} (b i₁) x) ∙
                          (λ i₁ → LR-id n {f} i₁ x)) i)))
                                ; (j = i1) → {!(FunRL n {f} (λ x → LR-id n {f} (~ i1) x))!}})
                        (λ i → FunRL n {f} (funExt (λ x → (λ i₁ → LR-id n {f} (~ i₁ ∧ (~ j)) x) ∙
                          (λ i₁ → FunLR n {f} (b i₁) x) ∙
                          (λ i₁ → LR-id n {f} (i₁ ∧ (~ j)) x)) i))

    3transp : PathP (λ j → (hauptLemma n f refl j) ≡ (hauptLemma n f refl j)) (λ i → FunRL n {f} (FunLR n {f} (b i))) b
    3transp j =  (λ i → (hauptLemma n f (b i) j))

    test : (λ j₂ → RL-id  n {f} (~ j₂) ≡ RL-id  n {f} (~ j₂)) ∙ (λ i → FunRL n {f} (LR-id n {f} (~ i)) ≡ FunRL n {f} (LR-id n {f} (~ i))) ∙ (λ i → hauptLemma n f refl i ≡ hauptLemma n f refl i) ≡ refl
    test j = {!((λ j₂ → RL-id  n {f} ((~ j₂) ∨ j) ≡ RL-id  n {f} ((~ j₂) ∨ j)) ∙ (λ i → FunRL n {f} (LR-id n {f} (?)) ≡ FunRL n {f} (LR-id n {f} (?))))!}
      where



    postulate
          wowiecomp : (i : I) → FunRL (n) (funExt (λ x → (λ i₁ → LR-id (n) (~ i₁) x) ∙
                                                (λ i₁ → FunLR (n) (b i₁) x) ∙
                                                (λ i₁ → LR-id (n) {f} i₁ x)) i)  ≡ b i



    needToShow : ((λ j₁ → ((λ j₂ → RL-id n {f} (~ j₂) ≡ RL-id n {f} (~ j₂)) ∙ (λ i → FunRL n {f} (LR-id n (~ i)) ≡ FunRL n {f} (LR-id n {f} (~ i))))
             j₁) ∙ (λ i → hauptLemma n f refl i ≡ hauptLemma n f refl i)) ≡ refl
    needToShow j k = {!((λ j₁ → ((λ j₂ → RL-id n {f} (~ j₂) ≡ RL-id n {f} (~ j₂)) ∙ (λ i → FunRL n {f} (LR-id n (~ i)) ≡ FunRL n {f} (LR-id n {f} (~ i))))!}


{-
where

  linvLemma : (n : ℕ) {f : A → B} {b : typ ((Ω^ (suc (suc (suc n)))) ((A → B) , f))} →
              (λ i → RL-id (suc n) (~ i)) ∙
                (λ i → FunRL (suc n) (funExt (λ x → (λ i₁ → LR-id (suc n) (~ i₁) x) ∙
                                       (λ i₁ → FunLR (suc n) (b i₁) x) ∙
                                       (λ i₁ → LR-id (suc n) {f} i₁ x)) i)) ∙
                RL-id (suc n) {f}
                ≡ b
  linvLemma n {f} {b} j  = {!hcomp ? ( (λ i → RL-id (suc n) (~ i ∧ j)) ∙
                (λ i → FunRL (suc n) (funExt (λ x → (λ i₁ → LR-id (suc n) ((~ i₁)) x) ∙
                                       (λ i₁ → FunLR (suc n) (b i₁) x) ∙
                                       (λ i₁ → LR-id (suc n) {f} (i₁ ) x)) (i))) ∙
                (λ i → (RL-id (suc n) {f} (i ∧ j)))) !}
    where
    cunt : (i : I) → (funExt (λ x → (λ i₁ → LR-id (suc n) (~ i₁) x) ∙ (λ i₁ → FunLR (suc n) {f} (b i₁) x) ∙ (λ i₁ → LR-id (suc n) {f} i₁ x )) i )
                     ≡ (funExt (λ x → (λ i₁ → LR-id (suc n) (~ i₁) x)) ∙ funExt (λ x → (λ i₁ → FunLR (suc n) {f} (b i₁) x)) ∙ funExt (λ x → (λ i₁ → LR-id (suc n) {f} i₁ x ))) i
    cunt i = refl

    cunt2 : (i : I)  → (funExt (λ x → (λ i₁ → LR-id (suc n) (~ i₁) x) ∙ (λ i₁ → FunLR (suc n) {f} (b i₁) x) ∙ (λ i₁ → LR-id (suc n) {f} i₁ x )) i )
                       ≡ (funExt (λ x → (λ i₁ → LR-id (suc n) (~ i₁) x)) ∙ (λ j → FunLR (suc n) {f} (b j)) ∙ funExt (λ x → (λ i₁ → LR-id (suc n) {f} i₁ x ))) i
    cunt2 i = refl
{-
    cunt3 : (i : I) → FunRL n (funExt (λ x → (λ i₁ → LR-id n (~ i₁) x) ∙ (λ i₁ → FunLR n (b i₁) x) ∙ (λ i₁ → LR-id n {f} i₁ x)) i) ≡ FunRL n (((λ i₁ → LR-id n {f} (~ i₁)) ∙ (λ j → FunLR n {f} (b j)) ∙ (λ i₁ → LR-id n {f} i₁)) i)
    cunt3 i = refl

    cunt4 : (i : I) → FunRL (suc n) (((λ i₁ → LR-id (suc n) {f} (~ i₁)) ∙ (λ j → FunLR (suc n) {f} (b j)) ∙ (λ i₁ → LR-id (suc n) {f} i₁)) i) ≡  FunRL n {f} ( LR-id n {f} (~ i)) ∙ FunRL n (FunLR n {f} (b i)) ∙ FunRL n {f} ( LR-id n {f} i)
    cunt4 i = {!!}


{-
    main2 : (λ i → RL-id n (~ i)) ∙ (λ i → FunRL n (((λ i₁ → LR-id n {f} (~ i₁)) ∙ (λ j → FunLR n {f} (b j)) ∙ (λ i₁ → LR-id n {f} i₁)) i)) ∙ (λ i → RL-id n i) ≡ {!!}
    main2 j i = {!FunRL n (((λ i₁ → LR-id n {f} (~ i₁ ∧ i0)) ∙ (λ k → FunLR n {f} (b (k))) ∙ (λ i₁ → LR-id n {f} (i₁ ∧ i0))) i0)!}

    main3 : PathP (λ j → (RL-id  n {f} j ≡ RL-id n j)) (λ i → FunRL n (((λ i₁ → LR-id n {f} (~ i₁)) ∙ (λ j → FunLR n {f} (b j)) ∙ (λ i₁ → LR-id n {f} i₁)) i)) ((λ i → RL-id n (~ i)) ∙ (λ i → FunRL n (((λ i₁ → LR-id n {f} (~ i₁)) ∙ (λ j → FunLR n {f} (b j)) ∙ (λ i₁ → LR-id n {f} i₁)) i)) ∙ (λ i → RL-id n {f} i))  
    main3 j = hcomp (λ k → λ{(j = i0) → {!((λ i → RL-id n ((~ i) ∧ j))!} ; (j = i1) → {!!}}) ((λ i → RL-id n ((~ i) ∧ j)) ∙ (λ i → FunRL n (((λ i₁ → LR-id n {f} (~ i₁)) ∙ (λ j → FunLR n {f} (b j)) ∙ (λ i₁ → LR-id n {f} i₁)) i)) ∙ (λ i → RL-id n (i ∧ j)))

    main4 : PathP (λ j → FunRL n (LR-id n j) ≡ FunRL n (LR-id n j)) {!LR-id n {f} i0!} (λ i → FunRL n (((λ i₁ → LR-id n {f} (~ i₁)) ∙ (λ j → FunLR n {f} (b j)) ∙ (λ i₁ → LR-id n {f} i₁)) i))
    main4 j = hcomp (λ k → {! LR-id n {f} (i0)!}) (λ i → FunRL n {f} (((λ i₁ → LR-id n {f} (~ i₁ ∧ j)) ∙ (λ k → FunLR n {f} (b (k))) ∙ (λ i₁ → LR-id n {f} (i₁ ∧ j))) i))
-}

    wowie : (i : I) → ( FunRL (suc n) (((λ i₁ → LR-id (suc n) {f} (~ i₁)) ∙ (λ j → FunLR (suc n) {f} (b j)) ∙ (λ i₁ → LR-id (suc n) {f} i₁)) i)) ≡ (FunRL (suc n) (((λ i₁ → (FunLR (suc n) refl)) ∙ (λ j → FunLR (suc n) {f} (b j)) ∙ (λ i₁ → (FunLR (suc n) refl))) i))
    wowie i = sym (λ j → FunRL (suc n) (((λ i₁ → LR-id (suc n) {f} (~ i₁ ∧ j)) ∙ (λ k → FunLR (suc n) {f} (b (k))) ∙ (λ i₁ → LR-id (suc n) {f} (i₁ ∧ j))) i))

    wowie2 : (i : I) → (FunRL (suc n) (((λ i₁ → (FunLR (suc n) refl)) ∙ (λ j → FunLR (suc n) {f} (b j)) ∙ (λ i₁ → (FunLR (suc n) refl))) i)) ≡ (FunRL (suc n) ((( FunLR (suc n) {f} (b i))) ))
    wowie2 i = (λ j → FunRL (suc n) {f} ((sym (lUnit ((λ j → FunLR (suc n) {f} (b j)) ∙ refl)) j) i)  ) ∙ ((λ j → FunRL (suc n) {f} ((sym (rUnit ((λ j → FunLR (suc n) {f} (b j)))) j) i)))

    main4 : PathP (λ j → FunRL n (LR-id n j) ≡ FunRL n (LR-id n j)) {!LR-id n {f} i0!} (λ i → FunRL n (((λ i₁ → LR-id n {f} (~ i₁)) ∙ (λ j → FunLR n {f} (b j)) ∙ (λ i₁ → LR-id n {f} i₁)) i))
    main4 j = hcomp (λ k → {! LR-id n {f} (i0)!}) (λ i → FunRL n {f} (((λ i₁ → LR-id n {f} (~ i₁ ∧ j)) ∙ (λ k → FunLR n {f} (b (k))) ∙ (λ i₁ → LR-id n {f} (i₁ ∧ j))) i))

    postulate
      fixLater : (i : I) → (FunRL (suc n) ((( FunLR (suc n) {f} (b i))) )) ≡ b i
    
    wowie3 : 
                (λ i → FunRL (suc n) (funExt (λ x → (λ i₁ → LR-id (suc n) (~ i₁) x) ∙
                                       (λ i₁ → FunLR (suc n) (b i₁) x) ∙
                                       (λ i₁ → LR-id (suc n) {f} i₁ x)) i)) 
                ≡
                {!b!}
    wowie3 j = {!FunRL!}

    wowiecomp : (i : I) → FunRL (suc n) (funExt (λ x → (λ i₁ → LR-id (suc n) (~ i₁) x) ∙
                                       (λ i₁ → FunLR (suc n) (b i₁) x) ∙
                                       (λ i₁ → LR-id (suc n) {f} i₁ x)) i)  ≡ b i
    wowiecomp i = wowie i ∙ wowie2 i ∙ fixLater {!wowiecomp i0!}


-}

-}
