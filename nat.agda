-- Funcs
_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
        (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

Fun₁ : ∀ {A} → Set A → Set A
Fun₁ A = A → A

Fun₂ : ∀ {A} → Set A → Set A
Fun₂ X = X → X → X

infixr 0 _$_
_$_ : ∀ {a b} {A : Set a} {B : Set b} →
        (A → B) → A → B
f $ v = f v


-- BOOL
data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool 
not true = false
not false = true

_and_ : Fun₂ Bool
true and true = true
_ and _       = false

_or_ : Fun₂ Bool 
true or _  = true
false or x = x

infixr 0 if_then_else_
if_then_else_ : {A : Set} -> Bool -> Fun₂ A
if true then val else _  = val
if false then _ else val = val

-- LIST
data List (A : Set) : Set where
  _∷_ : A -> List A -> List A
  []  : List A

map : {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

_++_ : {A : Set} → List A → List A → List A
[] ++ ys       = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- NAT
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

_+_ : Fun₂ ℕ
zero + y    = y
(suc x) + y = suc $ x + y

_*_ : Fun₂ ℕ
zero * n  = n
suc m * n = m + (n * m)

_==_ : ℕ → ℕ → Bool
zero == zero       = true
(suc n) == (suc m) = n == m
_ == _             = false

-- BOOL: RECORDS
record True : Set where
record False : Set where

isTrue : Bool → Set
isTrue true = True
isTrue false = False

-- LIST: VECT
data Vect (A : Set) : ℕ -> Set where
  ♯[]  : Vect A zero
  _♯∷_ : {n : ℕ} -> A → Vect A n → Vect A (suc n)

n₀ : {A : Set}{n : ℕ} → Vect A (suc n) → A
n₀ (x ♯∷ xs) = x

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc  : {n : ℕ} → Fin n → Fin (suc n)

d : (n : ℕ) -> Fin n -> Bool
d a b = true

f : Bool
f = d 1 fzero

_!_ : {n : ℕ}{A : Set} → Vect A n → Fin n → A
(x ♯∷ xs) ! fzero    = x
(x ♯∷ xs) ! (fsuc n) = xs ! n
