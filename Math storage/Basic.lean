-- Peano's 5 axioms
inductive NaturalNumber: Type where
|Zero : NaturalNumber
|Successor : NaturalNumber → NaturalNumber
notation "N" => NaturalNumber
instance : Zero NaturalNumber where
  zero := NaturalNumber.Zero
def s := NaturalNumber.Successor
theorem SuccessorNotEqualZero ( n : N ) : s n ≠ 0 := by
intro h
contradiction
theorem Injective (a b : N)  : s a = s b → a = b := by
intro h
injection h
-- define Adition
def NaturalNumber.Add (n m : NaturalNumber) : NaturalNumber :=
match n with
|0 => m
|Successor (n') => Successor (  n'.Add m)
instance : Add NaturalNumber where
  add := NaturalNumber.Add
-- define Number
def NaturalNumber.ofNat : Nat → NaturalNumber
| 0 => 0
| n + 1 => s (NaturalNumber.ofNat n)
instance : OfNat NaturalNumber n where
  ofNat := NaturalNumber.ofNat n
-- Adition property
theorem AdditionZero (a : N): a + 0 = a := by
induction a with
| Zero => rfl
| Successor n ih =>
calc
  s n + 0 = s (n+0) := by rfl
  s (n+0) = s (n) := by rw [ih]
theorem AdditionSuccessor (a b : N): a + s b = s (a+b) := by
induction a with
| Zero => rfl
| Successor n ih =>
change s n + s b = s (s (n) + b)
calc
  s n + s b = s (n + s b) := by rfl
  s (n + s b) = s (s (n+b)) := by rw [ih]
theorem AdditionCommutative (a b : N): a + b = b + a := by
induction a with
| Zero =>
change 0+b = b+0
rw [AdditionZero]
rfl
| Successor n ih =>
change s n + b = b + s n
rw [AdditionSuccessor, ← ih]
rfl
theorem AssociativeAddition (a b c : N): (a + b) + c = a + (b + c) := by
induction a with
| Zero =>
change (0+b)+c = 0 + (b+c)
rfl
| Successor n ih =>
change (s n + b) + c = s n + (b + c)
calc
  (s n + b) + c = s (n+b+c) := by rfl
  s (n+b+c) = s (n+(b+c)) := by rw [ih]
