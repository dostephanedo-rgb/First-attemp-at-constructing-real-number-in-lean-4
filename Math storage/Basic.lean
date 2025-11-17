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
