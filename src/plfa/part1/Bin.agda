module plfa.part1.Bin where
-- Solutions to all exercises involving Bin

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; trans; refl; cong; sym; _≢_)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Relation.Nullary using (¬_)

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Data.Nat.Properties using (+-suc; +-assoc; *-comm; +-identityʳ; +-mono-≤; +-monoˡ-≤)
open _≤_

open import Function.Base using (_∘_)


data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin


-- Bin (Naturals)
inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = 2 * from b
from (b I) = suc (2 * from b)


-- Bin-laws (Induction)
bin-from-inc-suc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
bin-from-inc-suc ⟨⟩ = refl
bin-from-inc-suc (b O) =
  begin
    from (inc (b O))
  ≡⟨⟩
    from (b I)
  ≡⟨⟩
    suc (2 * from b)
  ≡⟨⟩
    suc (from (b O))
  ∎
bin-from-inc-suc (b I) = 
  begin
    from (inc (b I))
  ≡⟨⟩
    from ((inc b) O)
  ≡⟨⟩
    2 * from (inc b)
  ≡⟨ cong (2 *_) (bin-from-inc-suc b) ⟩
    2 * suc (from b)
  ≡⟨⟩
    2 * (1 + from b)
  ≡⟨ *-comm 2 (1 + from b) ⟩
    (1 + from b) * 2
  ≡⟨⟩
    suc (suc (from b * 2))
  ≡⟨ cong (λ t → suc (suc t)) (*-comm (from b) 2) ⟩
    suc (from (b I))
  ∎


-- This law is false - hence a counterexample
not-bin-to-from : ¬(∀ (b : Bin) → (to (from b) ≡ b))
not-bin-to-from x =  f (x (⟨⟩ O I))
  where
  f : (⟨⟩ I) ≡ ((⟨⟩ O) I) → ⊥
  f ()


bin-from-to : ∀ (n : ℕ) → from (to n) ≡ n
bin-from-to zero = refl
bin-from-to (suc n) = 
  begin
    from (inc (to n))
  ≡⟨ bin-from-inc-suc (to n) ⟩
    suc (from (to n))
  ≡⟨ cong suc (bin-from-to n) ⟩
    suc n
  ∎
  

-- Bin-predicates (Relations)
data One : Bin → Set where
  one : One (⟨⟩ I)

  cons-zero : ∀ {b : Bin}
    → One b
      ---------
    → One (b O)

  cons-one : ∀ {b : Bin}
    → One b
      ---------
    → One (b I)


data Can : Bin → Set where
  zero : Can (⟨⟩ O)
  
  leading-one : ∀ {b : Bin}
    → One b
    → Can b

one-inc : ∀ {b : Bin}
  → One b
  -------------
  → One (inc b)
one-inc one = cons-zero one
one-inc (cons-zero ob) = cons-one ob
one-inc (cons-one ob) = cons-zero (one-inc ob)


can-inc : ∀ {b : Bin}
  → Can b
  -------------
  → Can (inc b)
can-inc zero = leading-one one
can-inc (leading-one ob) = leading-one (one-inc ob)


to-can : ∀ (n : ℕ)
  ------------
  → Can (to n)
to-can zero = zero
to-can (suc n) = can-inc (to-can n)


gte-one : ∀ {b : Bin}
  → One b
  ------------
  → 1 ≤ from b
gte-one one = s≤s z≤n
gte-one (cons-zero ob) = +-mono-≤ (gte-one ob) z≤n 
gte-one (cons-one ob) = +-mono-≤ {0} {1} z≤n (+-mono-≤ (gte-one ob) z≤n)


to-double : ∀ {n : ℕ}
  → 1 ≤ n
  -----------------------
  → to (2 * n) ≡ (to n) O
to-double {suc zero} (s≤s z≤n) = refl
to-double {suc (suc n)} (s≤s z≤n) =
  begin
    to (2 * suc (suc n))
  ≡⟨ cong to (2-suc-n≡2n+2 (suc n)) ⟩
    to (suc (suc (2 * suc n)))
  ≡⟨⟩
    inc (inc (to (2 * suc n)))
  ≡⟨ cong (inc ∘ inc) (to-double {suc n} (s≤s z≤n)) ⟩
    inc (inc ((to (suc n)) O))
  ≡⟨⟩
    inc ((to (suc n)) I)
  ≡⟨⟩
    inc (to (suc n)) O
  ≡⟨⟩
    (to (suc (suc n))) O
  ∎
  where
  2n≡n+n : ∀ (n : ℕ) → 2 * n ≡ n + n
  2n≡n+n n rewrite +-identityʳ n = refl
  
  2-suc-n≡2n+2 : ∀ (n : ℕ) → 2 * suc n ≡ suc (suc (2 * n))
  2-suc-n≡2n+2 n =
    begin
      2 * suc n
    ≡⟨ 2n≡n+n (suc n)⟩
      suc n + suc n
    ≡⟨ +-suc (suc n) n ⟩
      suc (suc n + n)
    ≡⟨⟩
      suc (suc (n + n))
    ≡⟨ cong (λ x → suc (suc x)) (sym (2n≡n+n n))⟩
      suc (suc (2 * n))
    ∎


to-from-one : ∀ {b : Bin}
  → One b
  -----------------
  → to (from b) ≡ b
to-from-one one = refl
to-from-one (cons-zero ob) = trans (to-double (gte-one ob)) (cong (_O) (to-from-one ob))
to-from-one (cons-one ob) = cong inc (trans (to-double (gte-one ob)) (cong (_O) (to-from-one ob)))
--- ugly duplication, but oh well...

to-from-can : ∀ {b : Bin}
  → Can b
  -----------------
  → to (from b) ≡ b
to-from-can zero = refl
to-from-can (leading-one ob) = to-from-one ob


-- Bin-embedding (Isomorphism)
open import plfa.part1.Isomorphism using (_≃_; _≲_)

Bin-embedding : ℕ ≲ Bin
Bin-embedding =
  record
    { to = to
    ; from = from
    ; from∘to = bin-from-to
    }


-- Bin-isomorphism (Quantifiers)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; proj₁)
open import Agda.Primitive using (lzero; lsuc)


≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′
≡One one one = refl
≡One (cons-zero x) (cons-zero y) = cong cons-zero (≡One x y)
≡One (cons-one x) (cons-one y) = cong cons-one (≡One x y)


≡Can : ∀ {b : Bin} (c c′ : Can b) → c ≡ c′
≡Can zero zero = refl
≡Can zero (leading-one (cons-zero ()))
≡Can (leading-one (cons-zero ())) zero
≡Can (leading-one x) (leading-one y) = cong leading-one (≡One x y)


proj₁≡→Can≡ : {c c′ : ∃[ b ] Can b} → proj₁ c ≡ proj₁ c′ → c ≡ c′
proj₁≡→Can≡ {a , ca} {.a , cb} refl = cong (λ c → a , c) (≡Can ca cb)


Bin-isomorphism : ∀{b : Bin} → ℕ ≃ ∃[ b ] Can b
Bin-isomorphism =
  record
    { to = λ x → to x , to-can x
    ; from = from'
    ; from∘to = λ x → 
              begin
                from' (to x , to-can x)
              ≡⟨⟩
                from (to x)
              ≡⟨ bin-from-to x ⟩
                x
              ∎
    ; to∘from = λ{ (fst , snd) → 
                    begin
                      (to (from' (fst , snd)) , to-can (from' (fst , snd)))
                    ≡⟨⟩
                      (to (from fst) , to-can (from fst))
                    ≡⟨ proj₁≡→Can≡ (to-from-can snd) ⟩
                      (fst , snd)
                    ∎ }
    }
    where
    --- TODO: can I get rid of this?
    from' : ∃[ b ] Can b → ℕ
    from' (fst , snd) = from fst



-- Bin-decidable (Decidable)
open import plfa.part1.Decidable using (Dec; toWitness; T)
open Dec


One? : ∀ (b : Bin) → Dec (One b)
One? ⟨⟩ = no λ()
One? (b O) with (One? b)
...           | yes ob  =  yes (cons-zero ob)
...           | no ¬ob  =  no (λ { (cons-zero x) → ¬ob x })
One? (b I) with (One? b)
...           | yes ob  =  yes (cons-one ob)
...           | no  ¬ob  =  helper b ¬ob
  where 
  helper : ∀ (b : Bin) → (¬ One b) → Dec (One (b I))
  helper ⟨⟩ _ = yes one
  helper (b O) ¬ob = no (λ{ (cons-one x) → ¬ob x})
  helper (b I) ¬ob = no (λ{ (cons-one x) → ¬ob x})


¬One⟨⟩ : ¬ One ⟨⟩
¬One⟨⟩ ()

Can? : ∀ (b : Bin) → Dec (Can b)
Can? ⟨⟩ = no λ{ (leading-one x) → ¬One⟨⟩ x }
Can? (b I) with One? (b I)
...           | yes ob  =  yes (leading-one ob)
...           | no ¬ob  =  no (λ{ (leading-one x) → ¬ob x })
Can? (b O) with One? (b O)
...           | yes ob  =  yes (leading-one ob)
...           | no ¬ob  =  helper b ¬ob
  where
  helper : ∀ (b : Bin) → (¬ One (b O)) → Dec (Can (b O))
  helper ⟨⟩ _ = yes zero
  helper (b O) ¬ob = no (λ{ (leading-one x) → ¬ob x})
  helper (b I) ¬ob = no (λ{ (leading-one x) → ¬ob x})
