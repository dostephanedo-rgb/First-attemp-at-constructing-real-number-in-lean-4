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
theorem SuccessorInjective (a b : N)  : s a = s b ↔ a = b := by
constructor
intro h
injection h
intro h
rw [h]
-- define Addition
def NaturalNumber.Addition (n m : NaturalNumber) : NaturalNumber :=
match n with
|0 => m
|Successor (n') => Successor (  n'.Addition m)
instance : Add NaturalNumber where
  add := NaturalNumber.Addition
-- define NautralNumber to readable number (example: 1,2,3,...)
def NaturalNumber.ofNat : Nat → NaturalNumber
| 0 => 0
| n + 1 => s (NaturalNumber.ofNat n)
instance : OfNat NaturalNumber n where
  ofNat := NaturalNumber.ofNat n
-- s n = n + 1
theorem SuccessorImplication (a : N): s a = a + 1 := by
induction a with
|Zero => rfl
|Successor n ih=>
change s (s n ) = s (n) + 1
conv =>
  left
  rw [ih]
calc
  s n + 1 = s (n+1) := by rfl
-- Natural Number Addition property
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
theorem AdditionAssociative (a b c : N): (a + b) + c = a + (b + c) := by
induction a with
| Zero =>
  change (0+b)+c = 0 + (b+c)
  rfl
| Successor n ih =>
  change (s n + b) + c = s n + (b + c)
  calc
    (s n + b) + c = s (n+b+c) := by rfl
    s (n+b+c) = s (n+(b+c)) := by rw [ih]
theorem AdditionEquality (a b c : N): a + c = b + c ↔ a = b:= by
constructor
{
  induction c with
  |Zero =>
    change a + 0 = b + 0 → a = b
    simp [AdditionZero]
  |Successor n ih =>
    change a + s n = b + s n → a = b
    simp [AdditionSuccessor]
    rw [SuccessorInjective]
    exact ih
}
{
  intro h
  rw [h]
}
-- Convinient Natural Number Addition theorem
theorem AdditionSwap (a b c : N): a+b+c = a+c+b := by
  rw [AdditionAssociative]
  rw [AdditionCommutative b c]
  rw [← AdditionAssociative]
-- define NaturalNumberMultiplication
def NaturalNumber.Multiplication (n m : NaturalNumber): NaturalNumber :=
match n with
|0 => 0
| Successor (n') => (n'.Multiplication m) + m
instance : Mul NaturalNumber where
  mul:= NaturalNumber.Multiplication
-- Multiplication properties:
theorem MultiplicationZero (a : NaturalNumber): a * 0 = 0 := by
induction a with
  | Zero =>
    change 0*0 = 0
    rfl
  |Successor n ih =>
  change s n * 0 = 0
  calc
    s n * 0 = n * 0 + 0 := by rfl
    n * 0 + 0 = 0 := by
      rw [ih]
      rfl
theorem MultiplicationIndentity (a : N): a * 1 = a := by
  induction a with
  |Zero =>
    change 0 * 1 = 0
    rfl
  |Successor n ih=>
    change s (n) * 1 = s (n)
    calc
      s (n) * 1 = (n*1) + 1 := by rfl
      (n*1) + 1 = s (n) := by
        rw [ih]
        rw [SuccessorImplication]
theorem MultiplicationLeftDistributive (a b c : NaturalNumber): a * (b + c) = (a*b) + (a*c) := by
induction a with
|Zero =>
rfl
|Successor n ih=>
change s n * (b+c) = (s n*b) + (s n*c)
calc
  s n * (b+c) = n*(b+c)+(b+c) := by rfl
  n * (b + c) + (b + c) = n*b+n*c + (b+c) := by rw[ih]
  n * b + n * c + (b + c) =  (s n * b) + (s n * c) := by
    rw [← AdditionAssociative]
    rw [AdditionSwap (n*b)]
    rw [AdditionAssociative ((n * b) + b)]
    rfl
theorem MultiplicationCommutative (a b: N): a * b = b * a := by
  induction b with
    | Zero =>
    change a*0=0*a
    rw [MultiplicationZero]
    rfl
    |Successor n ih =>
    change a* (s n) = s n * a
    conv =>
      left
      rw [SuccessorImplication]
      rw [MultiplicationLeftDistributive]
      rw [MultiplicationIndentity]
    symm
    calc
      s n * a = n * a + a := by rfl
      n * a + a = a * n + a := by rw [ih]
theorem MultiplicationRightDistributive (a b c : NaturalNumber): (a + b) * c = (a*c) + (b*c) := by
  rw [MultiplicationCommutative]
  rw [MultiplicationLeftDistributive]
  simp [MultiplicationCommutative]
theorem MultiplicationAssociative (a b c : NaturalNumber): a * b * c = a * (b*c) := by
  induction a with
  | Zero =>
    rfl
  | Successor n ih =>
    change s n * b * c = s n * (b * c)
    rw [SuccessorImplication]
    rw [MultiplicationRightDistributive n 1 (b*c)]
    rw [MultiplicationCommutative 1]
    rw [MultiplicationIndentity]
    rw [MultiplicationRightDistributive]
    rw [MultiplicationCommutative 1]
    rw [MultiplicationIndentity]
    rw [MultiplicationRightDistributive]
    rw [ih]
-- define Interger
def NaturalPair : Type := NaturalNumber × NaturalNumber
def EquivalenceDifference (p₁ p₂ : NaturalPair) : Prop :=
  let (a, b) := p₁
  let (c, d) := p₂
  a + d = c + b
instance : Setoid NaturalPair where
  r := EquivalenceDifference
  iseqv := by
    constructor
    {
      intro ⟨a, b⟩
      trivial
    }
    {
      intro ⟨a, b⟩
      intro ⟨c, d⟩
      simp [EquivalenceDifference]
      intro h
      rw [h]
    }
    {
      intro ⟨a, b⟩
      intro ⟨c, d⟩
      intro ⟨e, f⟩
      simp [EquivalenceDifference]
      intro h₁
      intro h₂
      rw [← AdditionEquality (c+f) (e+d) (c+b)] at h₂
      conv at h₂ =>
        left
        rw [← h₁]
        repeat rw [← AdditionAssociative]
        rw [AdditionAssociative c f a]
        rw [AdditionCommutative c]
      conv at h₂ =>
        right
        repeat rw [← AdditionAssociative]
        rw [AdditionCommutative (e + d + c)]
        rw [AdditionAssociative]
        rw [AdditionCommutative d]
        repeat rw [← AdditionAssociative]
      conv at h₂ =>
        repeat rw [AdditionEquality]
      rw [AdditionCommutative a]
      rw [AdditionCommutative e]
      exact h₂
    }
    done
def Interger : Type := Quot EquivalenceDifference
def NaturalPairToInterger (a :NaturalPair):
Interger := Quot.mk EquivalenceDifference a
instance : OfNat Interger n where
  ofNat := Quot.mk EquivalenceDifference (NaturalNumber.ofNat n, 0)
-- define IntergerAddition nad IntergerSubtraction
def PairAddition (a b : NaturalPair):
NaturalPair := (a.1+b.1, a.2+b.2)
theorem PairAdditionWellDefine (p1 p2 q1 q2 : NaturalPair): EquivalenceDifference p1 p2 → EquivalenceDifference q1 q2 → EquivalenceDifference (PairAddition p1 q1) (PairAddition p2 q2) := by
  cases p1 with
  | mk a b =>
  cases p2 with
  | mk a' b' =>
  cases q1 with
  | mk c d =>
  cases q2 with
  | mk c' d' =>
  simp [PairAddition, EquivalenceDifference]
  intro h1 h2
  conv at h2 =>
    rw [← AdditionEquality (c+d') (c'+d) (a+b')]
    right
    rw [h1]
  simp [← AdditionAssociative] at *
  conv at h2 =>
    left
    rw [AdditionSwap c]
    rw [AdditionCommutative c]
    rw [AdditionSwap (a+c)]
  conv at h2 =>
    right
    rw [AdditionSwap c']
    rw [AdditionCommutative c']
    rw [AdditionSwap (a'+c')]
  exact h2
def IntergerAddition : Interger → Interger → Interger :=
  Quot.lift
    (fun p₁ =>
      Quot.lift
        (fun p₂ => Quot.mk _ (PairAddition p₁ p₂))
        ( by
          intro q1 q2 h
          apply Quot.sound
          cases p₁ with
          | mk a b =>
          cases q1 with
          | mk c d
          cases q2 with
          | mk c' d'
          simp [PairAddition, EquivalenceDifference, ← AdditionAssociative] at *
          rw [AdditionSwap a c b]
          rw [AdditionSwap a c' b]
          repeat rw [AdditionCommutative (a+b)]
          rw [AdditionCommutative (c+(a+b))]
          rw [AdditionCommutative (c'+(a+b))]
          simp [← AdditionAssociative, AdditionEquality]
          rw [AdditionCommutative]
          rw [h]
          rw [AdditionCommutative]
        )
    )
    ( by
      intro p1 p2 hp
      funext x
      induction x using Quot.ind with
      | _ q =>
        apply Quot.sound
        apply PairAdditionWellDefine
        exact hp
        rfl
    )
instance : Add Interger where
  add := IntergerAddition
def PairNegation (p :NaturalPair) : NaturalPair :=
(p.2,p.1)
def IntergerNegation : Interger → Interger :=
Quot.lift
  (fun p => Quot.mk _ (PairNegation p))
  ( by
    intro a b h
    apply Quot.sound
    cases a with
    | mk a1 a2 =>
    cases b with
    | mk b1 b2 =>
    simp [EquivalenceDifference, PairNegation] at *
    rw [AdditionCommutative]
    rw [← h]
    rw [AdditionCommutative]
  )
def IntergerSubtraction (x y : Interger) : Interger := x + (IntergerNegation y)
instance : Sub Interger where
  sub := IntergerSubtraction
-- define IntergerMultiplication
def PairMultiplication (p q : NaturalPair): NaturalPair :=
  ((p.1 * q.1 + p.2 * q.2), (p.1*q.2+p.2*q.1))
def IntergerMultiplication : Interger → Interger → Interger :=
  Quot.lift
  (
    fun p1 =>
    Quot.lift
      (
        fun p2 => Quot.mk EquivalenceDifference (PairMultiplication p1 p2)
      )
      (
        by
        intro q1 q2 h
        apply Quot.sound
        cases p1 with
        | mk a b =>
        cases q1 with
        | mk c d =>
        cases q2 with
        | mk e f =>
        simp [EquivalenceDifference,PairMultiplication, ← AdditionAssociative] at *
        rw [AdditionSwap (a*c)]
        rw [AdditionSwap (a*e)]
        simp [← MultiplicationLeftDistributive,AdditionAssociative]
        rw [AdditionCommutative d e, AdditionCommutative f c]
        simp [h]
      )
  )
  (
    by
    intro p1 p2 h
    funext x
    induction x using Quot.ind with
    | _ q =>
      apply Quot.sound
      cases p1 with
      | mk a b =>
      cases p2 with
      | mk c d =>
      cases q with
      | mk e f =>
      simp [EquivalenceDifference,PairMultiplication,← AdditionAssociative] at *
      rw [AdditionSwap, AdditionSwap (a*e)]
      rw [AdditionSwap (c * e + d * f), AdditionSwap (c*e)]
      rw [MultiplicationCommutative,MultiplicationCommutative d]
      rw [MultiplicationCommutative c e,MultiplicationCommutative b e]
      simp [← MultiplicationLeftDistributive]
      rw [AdditionAssociative, AdditionAssociative]
      rw [MultiplicationCommutative b f, MultiplicationCommutative c f]
      rw [MultiplicationCommutative d f, MultiplicationCommutative a f]
      simp [← MultiplicationLeftDistributive]
      rw [h]
      rw [AdditionCommutative a d] at h
      rw [h]
      simp [AdditionCommutative]
  )
