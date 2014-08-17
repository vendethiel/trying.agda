-- BOOL
data Bool : Set where
  true : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

if_then_else_ : ∀ {a} {A : Set a} -> Bool -> A -> A -> A
if true then val else _ = val
if false then _ else val = val


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

-- NAT
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ


_+_ : ℕ -> ℕ → ℕ
zero + y = y
(suc x) + y = suc $ x + y

even : ℕ → Bool
even zero = true
even (suc zero) = false
even (suc (suc n)) = even n

odd : ℕ → Bool
odd = not ∘ even