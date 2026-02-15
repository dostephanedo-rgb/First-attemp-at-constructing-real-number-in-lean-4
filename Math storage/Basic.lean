open Classical
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
theorem AdditionEqualZeroImplication (a b : N): a + b = 0 ↔ a = 0 ∧ b = 0 := by
constructor
{
  intro h
  cases a with
  | Zero =>
  conv at h =>
    change b = 0
  change 0 = 0 ∧ b = 0
  rw [h]
  trivial
  | Successor n =>
  contradiction
}
{
  intro ⟨h1, h2 ⟩
  rw [h1,h2]
  rfl
}
-- Convinient Natural Number Addition theorem
theorem AdditionCancelation (a b: N): a + b = b ↔ a = 0 := by
constructor
{
  intro h
  conv at h =>
    right
    rw [← AdditionZero b]
  conv at h =>
    rw [AdditionCommutative b,AdditionEquality]
  exact h
}
{
  intro h
  simp [h]
  rfl
}
theorem AdditionSwap (a b c : N): a+b+c = a+c+b := by
  rw [AdditionAssociative]
  rw [AdditionCommutative b c]
  rw [← AdditionAssociative]
-- Equality deffinition
def NaturalNumber.StrictLess (a b : N) : Prop :=
  ∃ n : N, a + (s n) = b
instance : LT N where
  lt := NaturalNumber.StrictLess
def NaturalNumber.LessEqual (a b : N) : Prop :=
  a < b ∨ a = b
instance : LE N where
  le := NaturalNumber.LessEqual
-- Equality Property
theorem EqualitySymetry (a b : N): a > b ↔ b < a := by
constructor
{
  intro h
  exact h
}
{
  intro h
  exact h
}
theorem NaturalNumberNotEqualImplication (a b: N): a < b ∨ b < a ↔ a ≠ b := by
  constructor
  {
    intro h
    cases h with
    | inl h=>
      intro h1
      rw [h1] at h
      let ⟨k, hk ⟩ := h
      rw [AdditionCommutative b (s k)] at hk
      conv at hk =>
        right
        rw [← AdditionZero b]
      rw [AdditionCommutative b 0] at hk
      conv at hk =>
        rw [AdditionEquality]
      contradiction
    | inr h=>
      intro h1
      rw [h1] at h
      let ⟨k, hk ⟩ := h
      rw [AdditionCommutative b (s k)] at hk
      conv at hk =>
        right
        rw [← AdditionZero b, AdditionCommutative]
      rw [AdditionEquality] at hk
      contradiction
  }
  {
    intro h
    revert b
    induction a with
    | Zero =>
      intro b
      intro h
      cases b with
      | Zero =>
        contradiction
      | Successor n =>
        left
        exists n
    | Successor n ih=>
      intro b h1
      cases b with
      | Zero =>
        right
        exists n
        | Successor m =>
        have h2: n ≠ m := by
          intro h
          apply h1
          change s n = s m
          rw [SuccessorInjective]
          exact h
        have h3 := ih m h2
        cases h3 with
        | inl h3 =>
          let ⟨k, hk⟩:= h3
          left
          exists k
          change s n + s k = s m
          rw [AdditionCommutative,AdditionSuccessor,SuccessorInjective, AdditionCommutative]
          exact hk
        | inr h3 =>
          let ⟨k, hk⟩:= h3
          right
          exists k
          change s m + s k = s n
          rw [AdditionCommutative,AdditionSuccessor,SuccessorInjective, AdditionCommutative]
          exact hk
  }
theorem AdditionSelfWithSuccessorIsNotLessThan (a b: N): a + s b < a → False := by
intro ⟨k, hk⟩
change a + s b + s k = 0 + a at hk
rw [AdditionAssociative,AdditionCommutative,AdditionEquality,AdditionSuccessor] at hk
contradiction
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
theorem MultiplicationEqualZeroImplication (a b : N): a * b = 0 ↔ a = 0 ∨ b = 0 := by
constructor
{
  cases a with
  |Zero =>
  intro h1
  left
  trivial
  |Successor n =>
  intro h
  cases b with
  |Zero =>
  right
  trivial
  |Successor m =>
  conv at h =>
    change s n * s m = 0
    change (n*s m) + s m = 0
    rw [AdditionEqualZeroImplication]
  exfalso
  have HRight := h.right
  contradiction
}
{
  intro h
  cases h with
  | inl h =>
  rw [h]
  trivial
  | inr h =>
  rw [h,MultiplicationCommutative]
  trivial
}
theorem MultiplicationEquality (a b c : N): c ≠ 0 → (a * c = b * c ↔ a = b) := by
intro h
constructor
{
  revert b
  induction a with
  |Zero =>
    intro b h1
    symm at h1
    change b * c = 0 at h1
    change 0 = b
    rw [MultiplicationEqualZeroImplication] at h1
    cases h1 with
    | inl h1 =>
      rw [h1]
    | inr h1 =>
      exfalso
      apply h
      exact h1
  |Successor n ih =>
    intro b
    intro h1
    cases b with
    | Zero =>
      change s n * c = 0 at h1
      rw [MultiplicationEqualZeroImplication] at h1
      cases h1 with
      | inl h1 =>
        contradiction
      | inr h1 =>
        exfalso
        apply h
        exact h1
    | Successor m =>
      change n * c + c = m * c + c at h1
      rw [AdditionEquality] at h1
      change s n = s m
      rw [SuccessorInjective]
      rw [ih m h1]
}
{
  intro k
  rw [k]
}
-- define Interger
def NaturalPair : Type := NaturalNumber × NaturalNumber
def EquivalenceDifference (p₁ p₂ : NaturalPair) : Prop :=
  let (a, b) := p₁
  let (c, d) := p₂
  a + d = c + b
@[simp]
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
def Interger : Type := Quotient (inferInstance: Setoid NaturalPair)
def NaturalPairToInterger (a :NaturalPair):
Interger := Quot.mk EquivalenceDifference a
def Interger.ofNat : Nat → Interger
| 0 => Quotient.mk (inferInstance: Setoid NaturalPair) (0,0)
| n + 1 => Quotient.mk (inferInstance: Setoid NaturalPair) (NaturalNumber.ofNat (n + 1), NaturalNumber.ofNat (0) )
instance : OfNat Interger n where
  ofNat := Interger.ofNat (n)
attribute [simp] HasEquiv.Equiv Setoid.r EquivalenceDifference  NaturalNumber.ofNat Interger.ofNat
-- define IntergerAddition and IntergerSubtraction
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
          dsimp [Setoid.r]
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
    dsimp [Setoid.r]
    simp [EquivalenceDifference, PairNegation] at *
    rw [AdditionCommutative]
    rw [← h]
    rw [AdditionCommutative]
  )
def IntergerSubtraction (x y : Interger) : Interger := x + (IntergerNegation y)
instance : Sub Interger where
  sub := IntergerSubtraction
-- define absoluteValue
noncomputable def PairAbsoluteValue (p: NaturalPair) : NaturalPair :=
if p.1 > p.2 then p else (p.2,p.1)
@[simp]
theorem PairAbsoluteValueOrdered (a b : N ) (h : a > b): PairAbsoluteValue (a, b) = (a, b) := by
unfold PairAbsoluteValue
simp [h]
@[simp]
theorem PairAbsoluteValueUnordred (a b : N) (h : b > a): PairAbsoluteValue (a, b) = (b, a) := by
unfold PairAbsoluteValue
simp
intro ⟨k, hk ⟩
cases h with
| intro j hj =>
  rw [← hk,AdditionAssociative,AdditionCommutative,AdditionCancelation,AdditionSuccessor] at hj
  contradiction
noncomputable def IntergerAbsoluteValue: Interger → Interger :=
Quotient.lift
(
  fun p => Quotient.mk _ (PairAbsoluteValue p)
)
(
  by
  intro a b h
  apply Quotient.sound
  cases a with
  | mk a1 a2 =>
  cases b with
  | mk b1 b2 =>
    dsimp [HasEquiv.Equiv,Setoid.r,EquivalenceDifference] at h
    have h1 : a1 = a2 ∨ a1 ≠ a2 := Classical.em (a1 = a2)
    cases h1 with
    | inl h1 =>
      rw [h1,AdditionCommutative,AdditionEquality] at h
      simp [h,h1,PairAbsoluteValue]
      rw [AdditionCommutative]
    | inr h1 =>
      rw [← NaturalNumberNotEqualImplication] at h1
      cases h1 with
      | inl h1 =>
        change a2 > a1 at h1
        cases h1 with
        | intro k hk
        rw [← hk,← AdditionAssociative,AdditionSwap,AdditionCommutative,AdditionEquality] at h
        have h1 : a2 > a1 := by{exists k}
        have h2 : b2 > b1 := by
        {
          exists k
          symm
          exact h
        }
        simp [h1, h2]
        simp [h,← hk,AdditionSwap,AdditionEquality]
        rw [AdditionCommutative]
      | inr h1 =>
        have h2 := h
        have h3 := h1
        cases h3 with
        | intro k hk
        rw [← hk,AdditionAssociative,AdditionCommutative,AdditionEquality,AdditionCommutative] at h2
        have h2 : b1>b2 := by exists k
        change a1 > a2 at h1
        simp [h2,h1]
        exact h
)
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
instance: Mul Interger where
  mul:= IntergerMultiplication
-- Addition property For interger
@[simp]
theorem IntergerAdditionZero (a : Interger): a + 0 = a := by
  induction a using Quot.ind with
  | _ x =>
    apply Quot.sound
    induction x with
    | mk a b =>
      simp [PairAddition]
      change a + 0 + b = a + (b + 0)
      simp [AdditionZero]
theorem IntergerAdditionCommutative (a b : Interger): a + b = b + a := by
induction a using Quot.ind with
  | _ x =>
induction b using Quot.ind with
  | _ y =>
    apply Quot.sound
    induction x with
    | mk a b =>
    induction y with
    | mk c d =>
      simp[Setoid.r, PairAddition, EquivalenceDifference]
      simp [AdditionCommutative]
theorem IntergerAdditionAssociative (a b c : Interger): a + b + c = a + ( b + c ) := by
  induction a using Quot.ind with
  | _ A =>
  induction b using Quot.ind with
  | _ B =>
  induction c using Quot.ind with
  | _ C =>
    apply Quot.sound
    induction A with
    | mk a1 a2 =>
    induction B with
    | mk b1 b2 =>
    induction C with
    | mk c1 c2 =>
      simp [Setoid.r,EquivalenceDifference, PairAddition]
      simp [AdditionAssociative]
theorem IntergerNegationExpand (a b: Interger): IntergerNegation (a + b) = IntergerNegation a + IntergerNegation b := by
induction a,b using Quotient.ind₂ with
| _ a b =>
cases a with
| mk a1 a2
cases b with
| mk b1 b2
apply Quotient.sound
simp[PairNegation,PairAddition]
theorem IntergerNegationSimplification (a: Interger): IntergerNegation (IntergerNegation a) = a := by
induction a using Quotient.ind with
| _ a =>
cases a with
| mk a1 a2 =>
apply Quotient.sound
simp [PairNegation]
-- Algebraic Manipulation For interger part 1 (Addition and Subtraction)
theorem IntergerEqualitySubtraction (a b : Interger): a = b ↔ a - b = 0 := by
  induction a using Quot.ind with
  | _ A =>
  induction b using Quot.ind with
  | _ B =>
    constructor
    {
      intro h
      apply Quot.sound
      have mh : EquivalenceDifference A B := Quotient.exact h
      cases A with
      | mk a1 a2 =>
      cases B with
      | mk b1 b2 =>
        simp [EquivalenceDifference, PairAddition, PairNegation] at *
        change a1 + b2 + 0 = 0 + a2 + b1
        rw [AdditionZero]
        rw [mh]
        simp [AdditionCommutative, AdditionZero]
    }
    {
      intro h
      apply Quot.sound
      have mh : EquivalenceDifference (PairAddition A (PairNegation B)) (0,0) := Quotient.exact h
      cases A with
      | mk a1 a2 =>
      cases B with
      | mk b1 b2 =>
        simp [Setoid.r,PairAddition, PairNegation, EquivalenceDifference, AdditionZero, AdditionCommutative] at *
        exact mh
    }
@[simp]
theorem IntergerSubtractionSimplication (a : Interger): a - a = 0 := by
  change a + IntergerNegation a = 0
  induction a using Quot.ind with
  | _ A =>
    apply Quot.sound
    simp[Setoid.r,EquivalenceDifference,PairAddition,PairNegation,AdditionZero]
    rw [AdditionCommutative]
    rfl
theorem IntergerAdditionSwap (a b c : Interger): a + b + c = a + c  + b := by
rw [IntergerAdditionAssociative,IntergerAdditionCommutative b,← IntergerAdditionAssociative]
theorem IntergerEqualitySwapSubtraction (a b c: Interger): a - b = c ↔ a = c + b := by
constructor
{
  intro h
  rw [← h]
  change a = a + IntergerNegation b + b
  rw [IntergerAdditionSwap,IntergerAdditionAssociative]
  change a = a + (b - b)
  rw [IntergerSubtractionSimplication,IntergerAdditionZero]
}
{
  intro h
  rw [h]
  change c + b + IntergerNegation b = c
  rw [IntergerAdditionAssociative]
  change c + (b - b) = c
  rw [IntergerSubtractionSimplication,IntergerAdditionZero]
}
-- Multiplication Property
@[simp]
theorem IntergerMultiplicationZero (a: Interger): a*0 = 0 := by
  induction a using Quot.ind with
  | _ A =>
    induction A with
    | mk a1 a2 =>
      apply Quot.sound
      simp [EquivalenceDifference,PairMultiplication, MultiplicationZero, AdditionZero]
@[simp]
theorem IntergerMultiplicationIdentity (a: Interger): a * 1 = a := by
  induction a using Quot.ind with
    | _ A =>
      induction A with
        | mk a1 a2 =>
          apply Quot.sound
          simp [EquivalenceDifference,PairMultiplication,MultiplicationZero,AdditionCommutative]
          change a2 + a1 * 1 = a1 + a2 * 1
          simp [AdditionCommutative,MultiplicationIndentity]
theorem IntergerMultiplicationLeftDistributiveAddition (a b c : Interger): a * ( b + c ) = (a * b) + (a * c) := by
  induction a using Quot.ind with
  | _ A =>
  induction b using Quot.ind with
  | _ B =>
  induction c using Quot.ind with
  | _ C =>
    induction A with
    | mk a1 a2 =>
    induction B with
    | mk b1 b2 =>
    induction C with
    | mk c1 c2 =>
      apply Quot.sound
      simp [EquivalenceDifference,PairMultiplication,PairAddition,MultiplicationLeftDistributive,← AdditionAssociative, AdditionSwap]
theorem IntergerMultiplicationCommutative (a b: Interger): a * b = b * a := by
  induction a using Quot.ind with
  | _ A =>
  induction b using Quot.ind with
  | _ B =>
    induction A with
    | mk a1 a2 =>
    induction B with
    | mk b1 b2 =>
      apply Quot.sound
      simp [EquivalenceDifference,PairMultiplication,← AdditionAssociative, AdditionSwap,MultiplicationCommutative]
theorem IntergerMultiplicationRightDistributiveAddtion (a b c : Interger): (b + c) * a = (a * b) + (a * c) := by
rw [IntergerMultiplicationCommutative,IntergerMultiplicationLeftDistributiveAddition]
theorem IntergerMultiplicationAssociative (a b c : Interger): a * b * c = a * ( b * c ) := by
  induction a using Quot.ind with
  | _ A =>
  induction b using Quot.ind with
  | _ B =>
  induction c using Quot.ind with
  | _ C =>
    induction A with
    | mk a1 a2 =>
    induction B with
    | mk b1 b2 =>
    induction C with
    | mk c1 c2 =>
      apply Quot.sound
      simp [EquivalenceDifference,PairMultiplication,MultiplicationLeftDistributive,MultiplicationRightDistributive,← AdditionAssociative,← MultiplicationAssociative,AdditionSwap]
theorem IntergerMultiplicationEqualZeroImplication (a b: Interger): a * b = 0 ↔ a = 0 ∨ b = 0 := by
constructor
{
  induction a using Quot.ind with | _ A =>
  induction b using Quot.ind with | _ B =>
    intro H
    have h_rel : EquivalenceDifference (PairMultiplication A B) (0, 0) := Quotient.exact H
    induction A with
    | mk a1 a2 =>
    induction B with
    | mk b1 b2 =>
      simp [PairMultiplication,EquivalenceDifference,AdditionZero,AdditionCommutative] at *
      have equality: a1 = a2 ∨ a1 ≠ a2 := Classical.em (a1 = a2)
      cases equality with
      | inl equality =>
        left
        apply Quot.sound
        simp [AdditionZero]
        change a1 = a2
        exact equality
      | inr inequality =>
        rw [← NaturalNumberNotEqualImplication] at inequality
        cases inequality with
        | inl inequality =>
          let ⟨k, hk ⟩ := inequality
          conv at h_rel =>
            simp [← hk,MultiplicationRightDistributive,← AdditionAssociative]
            rw [AdditionSwap,AdditionCommutative (a1 * b2),AdditionSwap (a1*b1) (a1 * b2),AdditionEquality]
            rw [AdditionCommutative,AdditionCommutative (a1 * b1),AdditionEquality,MultiplicationCommutative,MultiplicationCommutative (s k),MultiplicationEquality _ _ _ (SuccessorNotEqualZero k)]
          right
          apply Quot.sound
          dsimp [Setoid.r]
          rw [AdditionZero]
          rw [h_rel]
          rfl
        | inr inequality =>
          let ⟨k, hk ⟩ := inequality
          conv at h_rel =>
            simp [← hk,MultiplicationRightDistributive,← AdditionAssociative]
            rw [AdditionAssociative (a2 * b2),AdditionCommutative (a2 * b2), AdditionEquality, AdditionCommutative, AdditionEquality, MultiplicationCommutative, MultiplicationCommutative (s k), MultiplicationEquality _ _ _ (SuccessorNotEqualZero k)]
          right
          apply Quot.sound
          simp
          rw [h_rel,AdditionZero]
          rfl
}
{
  intro h
  cases h with
  | inl h =>
    rw [h,IntergerMultiplicationCommutative,IntergerMultiplicationZero]
  | inr h =>
    rw [h,IntergerMultiplicationZero]
}
theorem IntergerMultiplicationIntergerNegation (a b: Interger): a * IntergerNegation b = IntergerNegation (a * b) := by
induction a using Quot.ind with
| _ A =>
induction b using Quot.ind with
| _ B =>
  induction A with
  | mk a1 a2 =>
  induction B with
  | mk b1 b2 =>
    apply Quot.sound
    simp [EquivalenceDifference,PairMultiplication,PairNegation]
theorem IntergerMutliplicationLeftDistrivutiveSubtraction (a b c : Interger): a * (b - c) = (a*b)-(a*c) := by
change a * (b + IntergerNegation c) = a * b + IntergerNegation (a*c)
rw [IntergerMultiplicationLeftDistributiveAddition,IntergerMultiplicationIntergerNegation]
theorem IntergerMultiplicationEquality (a b c : Interger): c ≠ 0 → (a*c=b*c↔a=b) := by
intro h
constructor
{
  intro h1
  conv at h1 =>
    rw [IntergerEqualitySubtraction, IntergerMultiplicationCommutative,IntergerMultiplicationCommutative b, ← IntergerMutliplicationLeftDistrivutiveSubtraction, IntergerMultiplicationEqualZeroImplication]
  cases h1 with
  | inl h1 =>
    rw [h1] at h
    contradiction
  | inr h1 =>
    rw [← IntergerEqualitySubtraction] at h1
    exact h1
}
{
  intro h1
  rw [h1]
}
-- Algebraic Manipulation for Interger part 2 (Multiplication)
theorem IntergerMultiplicationSwap (a b c: Interger): a * b * c = a * c * b := by
rw [IntergerMultiplicationAssociative,IntergerMultiplicationCommutative b,← IntergerMultiplicationAssociative]
-- Rational Number Contruction
structure Fraction where
  Numerator : Interger
  Denominator : Interger
  DenominatorNotEqualZero : Denominator ≠ 0
def EquivalenceFraction (a b: Fraction):=
  a.Numerator * b.Denominator = b.Numerator * a.Denominator
instance : Setoid Fraction where
r := EquivalenceFraction
iseqv := by
  constructor
  {
    intro x
    rw [EquivalenceFraction]
  }
  {
    intro x y
    simp [EquivalenceFraction]
    intro h
    rw [h]
  }
  {
    intro x y z
    simp [EquivalenceFraction]
    intro h₁ h₂
    have equality1: x.Numerator = 0 ∨ x.Numerator ≠ 0 := Classical.em (x.Numerator = 0)
    cases equality1 with
    | inl equality1 =>
      rw [equality1] at h₁
      rw [equality1]
      simp [IntergerMultiplicationCommutative,IntergerMultiplicationZero] at *
      rw [h₁,IntergerMultiplicationEquality]
      symm at h₁
      have h1 := (IntergerMultiplicationEqualZeroImplication y.Numerator x.Denominator)
      rw [h1] at h₁
      cases h₁ with
      | inl h₁ =>
        rw [h₁] at h₂
        rw [h₁]
        simp [IntergerMultiplicationCommutative,IntergerMultiplicationZero] at *
        have h2 := IntergerMultiplicationEqualZeroImplication z.Numerator y.Denominator
        symm at h₂
        rw [h2] at h₂
        cases h₂ with
        | inl h₂ =>
          rw [h₂]
        | inr h₂ =>
          have h3 := Fraction.DenominatorNotEqualZero y
          exfalso
          apply h3
          exact h₂
      | inr h₁ =>
        have h3 := Fraction.DenominatorNotEqualZero x
        exfalso
        apply h3
        exact h₁
      have k := Fraction.DenominatorNotEqualZero x
      exact k
    | inr equality1 =>
      rw [← IntergerMultiplicationEquality _ _ x.Numerator equality1,← IntergerMultiplicationEquality _ _ y.Denominator ] at h₂
      rw [IntergerMultiplicationSwap z.Numerator y.Denominator x.Numerator, IntergerMultiplicationAssociative z.Numerator,h₁,← IntergerMultiplicationAssociative] at h₂
      rw [IntergerMultiplicationEquality ] at h₂
      have equality2 : y.Numerator = 0 ∨ y.Numerator ≠ 0 := Classical.em (y.Numerator = 0)
      cases equality2 with
      | inl equality2 =>
        rw [equality2] at h₁
        simp [IntergerMultiplicationCommutative,IntergerMultiplicationZero] at h₁
        have h1 := IntergerMultiplicationEqualZeroImplication x.Numerator y.Denominator
        rw [h1] at h₁
        cases h₁ with
        | inl h₁ =>
          exfalso
          apply equality1
          exact h₁
        | inr h₁ =>
          have k := Fraction.DenominatorNotEqualZero y
          exfalso
          apply k
          exact h₁
      | inr equality2 =>
        rw [IntergerMultiplicationAssociative,IntergerMultiplicationCommutative,IntergerMultiplicationSwap z.Numerator, IntergerMultiplicationEquality _ _ _ _, IntergerMultiplicationCommutative] at h₂
        exact h₂
        exact equality2
      have k := Fraction.DenominatorNotEqualZero y
      exact k
      have k := Fraction.DenominatorNotEqualZero y
      exact k
  }
def RationalNumber : Type := Quotient (inferInstance: Setoid Fraction)
attribute [simp] EquivalenceFraction
-- Define Rational Number Addition and subtraction
def FractionAddition (a b : Fraction): Fraction :=
{
  Numerator:= a.Numerator*b.Denominator+b.Numerator*a.Denominator
  Denominator := a.Denominator * b.Denominator
  DenominatorNotEqualZero := by
  {
    intro h
    rw [IntergerMultiplicationEqualZeroImplication] at h
    cases h with
    | inl h =>
      apply Fraction.DenominatorNotEqualZero a
      exact h
    | inr h =>
      apply Fraction.DenominatorNotEqualZero b
      exact h
  }
}
def FractionNegation (f : Fraction): Fraction :=
{
  Numerator := IntergerNegation (f.Numerator)
  Denominator := f.Denominator
  DenominatorNotEqualZero := by exact Fraction.DenominatorNotEqualZero f
}
def RationalNumber.ofNat: Nat → RationalNumber
| 0 =>
Quotient.mk (inferInstance : Setoid Fraction) {
    Numerator := Interger.ofNat (0),
    Denominator := 1,
    DenominatorNotEqualZero := by
    {
      intro h
      have h1 := Quotient.exact h
      simp at *
      contradiction
    }
  }
| n + 1 =>
Quotient.mk (inferInstance : Setoid Fraction) {
    Numerator := Interger.ofNat (n+1),
    Denominator := 1,
    DenominatorNotEqualZero := by
    {
      intro h
      have h1 := Quotient.exact h
      simp at *
      contradiction
    }
  }
instance (n : Nat) : OfNat RationalNumber n where
  ofNat := RationalNumber.ofNat n
attribute [simp] FractionAddition RationalNumber.ofNat FractionNegation
def RationalNumberAddition (a b: RationalNumber): RationalNumber :=
Quotient.lift₂
(fun f1 f2 => Quotient.mk (inferInstance: Setoid Fraction) (FractionAddition f1 f2))
(
  by
  intro a1 b1 a2 b2 h1 h2
  apply Quotient.sound
  simp [IntergerMultiplicationRightDistributiveAddtion,← IntergerMultiplicationAssociative] at *
  rw [IntergerMultiplicationAssociative b2.Denominator,IntergerMultiplicationCommutative a2.Denominator,h1,IntergerMultiplicationCommutative b2.Denominator (a2.Numerator * a1.Denominator)]
  rw [IntergerMultiplicationSwap b2.Denominator,IntergerMultiplicationCommutative b2.Denominator,h2]
  rw [IntergerMultiplicationCommutative (b1.Denominator * a1.Denominator)]
  rw [IntergerMultiplicationCommutative (b1.Denominator * a1.Denominator)]
  simp [IntergerMultiplicationSwap, ← IntergerMultiplicationAssociative]
) a b
def RationalNumberNegation (a: RationalNumber): RationalNumber :=
Quotient.lift
(fun f => Quotient.mk (inferInstance: Setoid Fraction) (FractionNegation f))
(
  by
  intro f1 f2 h1
  apply Quotient.sound
  simp at *
  rw [IntergerMultiplicationCommutative (IntergerNegation f1.Numerator) ]
  rw [IntergerMultiplicationCommutative (IntergerNegation f2.Numerator)]
  simp [IntergerMultiplicationIntergerNegation,h1, IntergerMultiplicationCommutative]
) a
@[simp]
def RationalNumberSubtraction (a b: RationalNumber): RationalNumber := RationalNumberAddition a  (RationalNumberNegation b)
instance: Add RationalNumber where
  add := RationalNumberAddition
instance: Sub RationalNumber where
  sub := RationalNumberSubtraction
-- Rational Number Addition and Subtraction property
theorem RationalNumberSubtractionSimplification (a : RationalNumber): a +  RationalNumberNegation a = 0 := by
induction a using Quotient.ind with
| _ f =>
  apply Quotient.sound
  simp
  change f.Numerator * f.Denominator + IntergerNegation f.Numerator * f.Denominator = 0 * (f.Denominator * f.Denominator)
  rw [IntergerMultiplicationCommutative,IntergerMultiplicationCommutative (IntergerNegation f.Numerator),← IntergerMultiplicationLeftDistributiveAddition,IntergerMultiplicationCommutative 0]
  change f.Denominator * (f.Numerator - f.Numerator) = f.Denominator * f.Denominator * 0
  simp
theorem RationalNumberAdditionZeroLeft (a : RationalNumber): a + 0 = a := by
induction a using Quotient.ind with
| _ f =>
apply Quotient.sound
simp
change (f.Numerator + 0 * f.Denominator) * f.Denominator = f.Numerator * f.Denominator
simp [IntergerMultiplicationCommutative]
theorem RationalNumberAdditionCommutative (a b : RationalNumber): a + b = b + a := by
induction a using Quotient.ind with
| _ a =>
induction b using Quotient.ind with
| _ b =>
  apply Quotient.sound
  simp
  rw [IntergerMultiplicationCommutative b.Denominator, IntergerMultiplicationEquality]
  simp [IntergerAdditionCommutative]
  intro h
  rw [IntergerMultiplicationEqualZeroImplication] at h
  cases h with
  | inl h =>
    apply Fraction.DenominatorNotEqualZero a
    exact h
  | inr h =>
    apply Fraction.DenominatorNotEqualZero b
    exact h
theorem RationalNumberAdditionAssociative (a b c : RationalNumber): a + b + c = a + (b + c) := by
induction a, b using Quotient.ind₂ with
| _ a b =>
induction c using Quotient.ind with
| _ c =>
  apply Quotient.sound
  simp [IntergerMultiplicationRightDistributiveAddtion,IntergerMultiplicationLeftDistributiveAddition,← IntergerMultiplicationAssociative,IntergerMultiplicationSwap,← IntergerAdditionAssociative]
-- Rational Number Addition and Subtraction property (for simplifying the equation)
theorem RationalNumberAdditionZeroRight (a : RationalNumber): 0 + a = a := by
simp [RationalNumberAdditionCommutative,RationalNumberAdditionZeroLeft]
theorem RationalNumberAdditionSwap (a b c : RationalNumber): a + b + c = a + c + b := by
simp [RationalNumberAdditionAssociative]
rw [RationalNumberAdditionCommutative c]
theorem RationalNumberAdditionReverseAssociative (a b c: RationalNumber): a + (b + c) = a + b + c := by
rw [RationalNumberAdditionAssociative]
theorem RationalNumberAdditionSimplification (a b: RationalNumber): a = b ↔ a + RationalNumberNegation b = 0 := by
induction a,b using Quotient.ind₂ with
| _ a b =>
constructor
{
  intro h
  apply Quotient.sound
  simp
  have h1 := Quotient.exact h
  change a.Numerator*b.Denominator = b.Numerator * a.Denominator at h1
  change a.Numerator * b.Denominator + IntergerNegation b.Numerator * a.Denominator = 0 * (a.Denominator * b.Denominator)
  rw [h1,IntergerMultiplicationCommutative,IntergerMultiplicationCommutative (IntergerNegation b.Numerator),← IntergerMultiplicationLeftDistributiveAddition]
  change a.Denominator * (b.Numerator - b.Numerator) = 0 * (a.Denominator * b.Denominator)
  simp [IntergerMultiplicationCommutative]
}
{
  intro h
  apply Quotient.sound
  have h1 := Quotient.exact h
  simp at *
  change a.Numerator * b.Denominator + IntergerNegation b.Numerator * a.Denominator = 0 * (a.Denominator * b.Denominator) at h1
  simp [IntergerMultiplicationCommutative] at h1
  rw [IntergerMultiplicationIntergerNegation] at h1
  change a.Numerator * b.Denominator - (a.Denominator * b.Numerator) = 0 at h1
  rw [← IntergerEqualitySubtraction] at h1
  simp [h1,IntergerMultiplicationCommutative]
}
theorem RationalNumberAdditionNegationDistributive(a b: RationalNumber): RationalNumberNegation (a + b) = RationalNumberNegation a + RationalNumberNegation b := by
induction a,b using Quotient.ind₂ with
| _ a b
apply Quotient.sound
simp
rw [IntergerMultiplicationEquality]
simp [IntergerMultiplicationIntergerNegation,IntergerMultiplicationCommutative,IntergerNegationExpand]
intro h
rw [IntergerMultiplicationEqualZeroImplication] at h
cases h with
| inl h=>
  apply Fraction.DenominatorNotEqualZero a
  exact h
| inr h=>
  apply Fraction.DenominatorNotEqualZero b
  exact h
theorem rationalNumberNegationSimplification (a:RationalNumber): RationalNumberNegation (RationalNumberNegation a) = a  := by
induction a using Quotient.ind with
| _ a =>
apply Quotient.sound
simp
rw [IntergerNegationSimplification]
attribute [simp] RationalNumberSubtractionSimplification RationalNumberAdditionZeroLeft RationalNumberAdditionZeroRight RationalNumberAdditionSwap RationalNumberAdditionReverseAssociative RationalNumberAdditionSimplification RationalNumberAdditionNegationDistributive rationalNumberNegationSimplification
-- Define Rational Number Multiplication and Division
def FractionMultiplication (a b : Fraction): Fraction :=
{
  Numerator := a.Numerator * b.Numerator
  Denominator := a.Denominator * b.Denominator
  DenominatorNotEqualZero := by
  {
    intro h
    rw [IntergerMultiplicationEqualZeroImplication] at h
    cases h with
    | inl h =>
      apply Fraction.DenominatorNotEqualZero a
      exact h
    | inr h =>
      apply Fraction.DenominatorNotEqualZero b
      exact h
  }
}
def FractionReciprocal (a: Fraction) (h:a.Numerator ≠ 0): Fraction :=
{
  Numerator := a.Denominator
  Denominator := a.Numerator
  DenominatorNotEqualZero := h
}
attribute [simp] FractionMultiplication FractionReciprocal
def RationalNumberMultiplication (a b: RationalNumber): RationalNumber :=
Quotient.lift₂
(fun a b => Quotient.mk (inferInstance: Setoid Fraction) (FractionMultiplication a b))
(
  by
  intro a1 b1 a2 b2 h1 h2
  apply Quotient.sound
  simp at *
  simp [← IntergerMultiplicationAssociative]
  rw [IntergerMultiplicationSwap a1.Numerator,h1,IntergerMultiplicationAssociative (a2.Numerator * a1.Denominator),h2]
  simp [← IntergerMultiplicationAssociative,IntergerMultiplicationSwap]
) a b
set_option linter.unusedVariables false
noncomputable def RationalNumberReciprocal (a: RationalNumber) (h: a ≠ 0): RationalNumber :=
Quotient.lift (fun f:Fraction => Quotient.mk _ (if hf: f.Numerator = 0 then f else FractionReciprocal f hf))
(
  by
  intro a1 a2 h1
  apply Quotient.sound
  simp at h1
  have h2 := Classical.em (a1.Numerator = 0)
  cases h2 with
  | inl h2 =>
    rw [h2] at h1
    symm at h1
    simp [IntergerMultiplicationCommutative,IntergerMultiplicationEqualZeroImplication]at h1
    cases h1 with
    | inl h1 =>
      simp [h1,h2,IntergerMultiplicationCommutative]
    | inr h1 =>
      exfalso
      apply Fraction.DenominatorNotEqualZero a1
      exact h1
  | inr h2 =>
    {
      have h3 : ¬ a2.Numerator = 0 := by
      {
        intro h
        simp[h,IntergerMultiplicationCommutative,IntergerMultiplicationEqualZeroImplication] at h1
        cases h1 with
        | inl h1 =>
        {
          apply h2
          exact h1
        }
        | inr h1 =>
        {
          apply Fraction.DenominatorNotEqualZero a2
          exact h1
        }
      }
      simp [h2,h3]
      symm
      rw [IntergerMultiplicationCommutative,h1,IntergerMultiplicationCommutative]
    }
)
a
noncomputable def RationalNumberDivision (a b : RationalNumber) (h:b ≠ 0):= RationalNumberMultiplication a (RationalNumberReciprocal b h)
instance: Mul RationalNumber where
  mul := RationalNumberMultiplication
-- Rational Number Multiplication and Division property
theorem RationalNumberDivisionSimplification (a:RationalNumber) (h:a≠0) : a * RationalNumberReciprocal a h = 1 := by
induction a using Quotient.ind with
| _ a =>
  have h1 : a.Numerator ≠ 0 := by
  {
    intro h1
    apply h
    apply Quotient.sound
    simp
    show a.Numerator = 0 * a.Denominator
    simp [IntergerMultiplicationCommutative]
    exact h1
  }
  apply Quotient.sound
  simp [h1]
  change a.Numerator * a.Denominator = 1 * (a.Denominator * a.Numerator)
  simp [IntergerMultiplicationCommutative]
theorem RationalNumberMultiplicationZeroLeft (a:RationalNumber) : a * 0 = 0 := by
induction a using Quotient.ind with
| _ a =>
apply Quotient.sound
simp
change a.Numerator * 0 = 0 * a.Denominator
simp [IntergerMultiplicationCommutative]
theorem RationalNumberMultiplicationIdentity (a:RationalNumber) : a * 1 = a := by
induction a using Quotient.ind with
| _ a =>
apply Quotient.sound
simp
change a.Numerator * 1 * a.Denominator = _
simp
theorem RationalNumberMultiplicationCommutative (a b : RationalNumber): a * b = b * a := by
induction a,b using Quotient.inductionOn₂ with
| _ a b
apply Quotient.sound
simp [IntergerMultiplicationCommutative]
theorem RationalNumberMultiplicationAssociative (a b c : RationalNumber): a * (b * c) = a * b * c := by
induction a,b,c using Quotient.inductionOn₃ with
| _ a b c
apply Quotient.sound
simp [IntergerMultiplicationAssociative]
theorem RationalNumberMultiplicationLeftDistributiveAddition (a b c : RationalNumber): a * (b + c) = a * b + a * c := by
induction a, b, c using Quotient.inductionOn₃ with
| _ a b c
apply Quotient.sound
simp [IntergerMultiplicationLeftDistributiveAddition,← IntergerMultiplicationAssociative,IntergerMultiplicationRightDistributiveAddtion,IntergerMultiplicationSwap]
theorem RationalNumberMultiplicationRightDistributiveAddition (a b c : RationalNumber): (a + b) * c = a * c + b * c := by
simp [RationalNumberMultiplicationCommutative,RationalNumberMultiplicationLeftDistributiveAddition]
theorem RationalNumberMultiplicationEqualZeroImplication (a b : RationalNumber) : a * b = 0 ↔ a = 0 ∨ b = 0 := by
constructor
{
  intro h
  induction a, b using Quotient.inductionOn₂ with
  | _ a b =>
  have equality := Quotient.exact h
  conv at equality =>
  {
    simp
    change _ = 0 * _
    simp [IntergerMultiplicationCommutative,IntergerMultiplicationEqualZeroImplication]
  }
  cases equality with
  | inl equality =>
    left
    apply Quotient.sound
    simp
    change _ = 0 * _
    simp [IntergerMultiplicationCommutative]
    exact equality
  | inr equality =>
    right
    apply Quotient.sound
    simp
    change _ = 0 * _
    simp [IntergerMultiplicationCommutative]
    exact equality
}
{
  intro h
  cases h with
  | inl h =>
    simp [RationalNumberMultiplicationCommutative,RationalNumberMultiplicationZeroLeft,h]
  | inr h =>
    simp [RationalNumberMultiplicationZeroLeft,h]
}
theorem RationalNumberMultiplicationNotEqualZeroImplication (a b : RationalNumber) : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
constructor
{
  intro h
  constructor
  {
    intro h1
    apply h
    rw [RationalNumberMultiplicationEqualZeroImplication]
    left
    exact h1
  }
  {
    intro h1
    apply h
    rw [RationalNumberMultiplicationEqualZeroImplication]
    right
    exact h1
  }
}
{
  intro ⟨h2, h3⟩
  intro h1
  rw [RationalNumberMultiplicationEqualZeroImplication] at h1
  cases h1 with
  | inl h1 =>
    apply h2
    exact h1
  | inr h1 =>
    apply h3
    exact h1
}
