variable (p q r s : Prop)
namespace mysettheory
#check And.intro
#check And.left
#check And.right
#check Or.intro_left --or  {a : Prop} (b : Prop) (h : a) : a ∨ b =
#check Or.intro_right -- (b : Prop) → a → a ∨ b
#check Or.inl --or {a b : Prop} (h : a) : a ∨ b =  a → a ∨ b
#check Or.inr --
#check Or.elim -- a ∨ b → (a → c) → (b → c) → c
#check ¬p -- p → False
#check False.elim -- False : False → ()
--{C : Sort u} → False → C
-- {C : Sort u}
#check absurd --  a → ¬a → b
#check True.intro --
#check Iff.intro --(a → b) → (b → a) → (a ↔ b)
#check Iff.mp -- a ↔ b → a → b
#check Iff.mpr -- a ↔ b → b → a

-- #check em p
-- byContradiction


--Theorem 1
-- (a) Law of addition (Add.)
#check Or.intro_left
-- (b) Laws of simplification (Simp.)
#check And.left
#check And.right
-- (c) Disjunctive Syllogism (D.S.)
theorem DS : (p ∨ q) ∧ ¬p  → q :=
  fun h : (p ∨ q) ∧ ¬p =>
  Or.elim h.left (fun hp : p => False.elim (h.right hp)) (fun hq : q => hq)

open Classical

--Theorem 2
-- (a) Law of Double Negation (D.N.)
theorem DN : ¬¬p ↔ p := --
  Iff.intro
    (fun hnnp : ¬¬p =>  -- (p → False) → False
      byContradiction fun hnp : ¬p => show False from hnnp hnp
    )
    (fun (hp : p) (h : p → False) =>
      False.elim (h hp)
    )

-- (b) Commutative Laws (Com.)
theorem ComAnd : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))
theorem ComOr : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q =>
     show q ∨ p from
     Or.elim h
     (fun hp : p => Or.intro_right q hp)
     (fun hq : q => Or.intro_left p hq))
     (fun h : q ∨ p =>
     show p ∨ q from
     Or.elim h
     (fun hq : q => Or.intro_right p hq)
     (fun hp : p => Or.intro_left q hp))

-- (c) Laws of Idempotency (Idemp.)
theorem IdempAnd : p ∧ p ↔ p :=
  Iff.intro
    (fun h : p ∧ p => h.left)
    (fun h : p => And.intro h h)
theorem IdempOr : p ∨ p ↔ p :=
  Iff.intro
    (fun h : p ∨ p =>
    h.elim (fun hp : p => hp) (fun hp : p => hp))
    (fun h : p => Or.inl h)

-- (d) Contrapositive Law (Contrap.)
theorem Contrap : (¬q → ¬p) ↔ (p → q) :=
  Iff.intro
  (fun (h : ¬q → ¬p) (hp : p) =>
    byContradiction (fun nq : ¬q =>
    absurd hp (h nq))
  )

  (fun (h : p → q) (nq : ¬q) =>
   fun (hp : p) => nq (h hp)
  )

-- Theorem 3 De Morgan's Law (De M.)
theorem DeM : ¬(p ∧ q) ↔ ¬p ∨ ¬q :=
  Iff.intro
  (fun h : ¬(p ∧ q) =>
     Or.elim (em p)
      (fun hp : p => -- ¬p ∨ ¬q
        Or.elim (em q)
        (fun hq : q  => False.elim (h (And.intro hp hq)))
        (fun nq : ¬q => Or.intro_right (¬p) nq)
      )
      (fun hnp : ¬p => -- ¬p ∨ ¬q
        Or.intro_left (¬q) hnp
      ))
  (fun h : ¬p ∨ ¬q =>
    show ¬(p ∧ q) from
    fun h₂ : p ∧ q =>
    h.elim (fun np : ¬p => (absurd h₂.left np)) (fun nq : ¬q => nq (h₂.right)))

-- Theorem 4

-- (a) Associative Laws (Assoc.)
theorem Assoc : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
  (fun h : (p ∧ q) ∧ r =>
    show p ∧ (q ∧ r) from
    And.intro (And.left (And.left h)) (And.intro (And.right (And.left h)) (And.right h)))
   (fun h : p ∧ (q ∧ r) =>-- 축약 X
    show (p ∧ q) ∧ r from
    And.intro (And.intro h.left h.right.left) (h.right.right))


-- (b) Distributive Laws (dist.)

theorem distAndOr: p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
  (fun h : p ∧ (q ∨ r) => -- (q ∨ r) → (p ∧ q) ∨ (p ∧ r)
    Or.elim h.right
    (fun hq : q => -- q → (p ∧ q) ∨ (p ∧ r)
      Or.inl (And.intro h.left hq))
    (fun hr : r=> -- r → (p ∧ q) ∨ (p ∧ r)
      Or.inr (And.intro h.left hr)
    )
  )
  (fun h : (p ∧ q) ∨ (p ∧ r) =>
    show p ∧ (q ∨ r) from
    Or.elim h
    (fun hpq : p ∧ q => -- p ∧ q → p ∧ (q ∨ r)
      show p ∧ (q ∨ r) from
      And.intro (hpq.left) (Or.inl hpq.right)
    )
    (fun hpr : p ∧ r =>  -- p ∧ r →  p ∧ (q ∨ r)
      show p ∧ (q ∨ r) from
      And.intro (hpr.left) (Or.inr hpr.right)
    )

  )
theorem distOrAnd : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
  (fun h : p ∨ (q ∧ r) => -- p ∨ (q ∧ r) →  (p ∨ q) ∧ (p ∨ r)
    h.elim
    (fun hp : p => -- p → (p ∨ q) ∧ (p ∨ r)
      And.intro (Or.intro_left q hp) (Or.intro_left r hp)
    )
    (fun hqr : q ∧ r => -- q ∧ r → (p ∨ q) ∧ (p ∨ r)
     And.intro (Or.intro_right p hqr.left) (Or.intro_right p hqr.right)
    )
  )
  (fun h : (p ∨ q) ∧ (p ∨ r) =>  -- (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r)
    have hpq : p ∨ q := h.left
    have hpr : p ∨ r := h.right
    hpq.elim (fun hp : p => Or.inl hp)
    (fun hq : q =>
      hpr.elim (fun hp : p => Or.inl hp) (fun hr : r => Or.inr (And.intro hq hr))
    )
  )

  -- (c) Transitive Law (Trans.)
theorem Trans : (p → q) ∧ (q → r) → (p → r) :=
  fun (h : (p → q) ∧ (q → r)) (hp : p) =>
    have hq :q := h.left hp
    h.right hq

--Theorem 5
-- (a) Constructive Dilemmas (C.D.)
theorem CDOr : (p → q) ∧ (r → s) → (p ∨ r → q ∨ s) :=
  fun (h₁ : (p → q) ∧ (r → s))  (h₂ : p ∨ r) =>
    h₂.elim
    (fun hp : p =>
    have hq : q := h₁.left hp
    Or.intro_left s hq )
    (fun hr : r =>
    have hs : s := h₁.right hr
    Or.intro_right q hs)

theorem CDAnd : (p → q) ∧ (r → s) → (p ∧ r → q ∧ s) :=
  fun (h₁ : (p → q) ∧ (r → s) ) (h₂ : p ∧ r) =>
    have hq : q := h₁.left h₂.left
    have hs : s := h₁.right h₂.right
    And.intro hq hs

-- (b) Destructive Dilemmas (D.D.)
theorem DDOr : (p → q) ∧ (r → s) → (¬q ∨ ¬ s → ¬p ∨ ¬r) :=
  fun (h₁ : (p → q) ∧ (r → s)) (h₂ : ¬q ∨ ¬s) =>
  Or.elim (em p)
  (fun hp : p =>
    Or.elim (em r)
    (fun hr : r =>
    have hq : q := h₁.left hp
    have hs : s := h₁.right hr
    have hnqs : ¬(q ∧ s) := (Iff.mpr (DeM q s)) h₂
    False.elim (hnqs (And.intro hq hs))
    )
    (fun hnr : ¬r => Or.intro_right (¬p) hnr)
  )
  (fun hnp : ¬p => Or.intro_left (¬r) hnp )


theorem DDAnd : (p → q) ∧ (r → s) → (¬q ∧ ¬ s → ¬p ∧ ¬r) :=
  fun (h₁ :(p → q) ∧ (r → s) ) (h₂ : ¬q ∧ ¬ s ) =>
    Or.elim (em p)
    (fun hp : p =>
    have hq : q := h₁.left hp
    False.elim (h₂.left hq))
    (fun hnp : ¬p =>
      Or.elim (em r)
      (fun hr :r =>
      have hs : s := h₁.right hr
      False.elim (h₂.right hs)
      )
      (fun hnr : ¬r =>
      And.intro hnp hnr)
    )


-- Theorem 6
-- (a) Modus Ponens (M.P.)
theorem MP : (p → q) ∧ p → q :=
  fun h₁ : (p → q) ∧ p =>
  have hp := h₁.right
  show q from h₁.left hp

-- (b) Modus Tollens (M.T.)
theorem MT : (p → q) ∧ ¬q → ¬p :=
  fun h : (p → q) ∧ ¬q =>
    Or.elim (em p)
      (fun hp : p   => False.elim (h.right (h.left hp)))
      (fun hnp : ¬p => hnp)

-- (c) Reductio ad Absurdum (R.A )
theorem R.A : (p → q) ↔ (p ∧ ¬q → q ∧ ¬q) :=
  Iff.intro
  (fun (h₁ : p → q) (h₂ : p ∧ ¬q) =>
  have hq : q := h₁ h₂.left
  And.intro hq h₂.right
  )
  (fun (h₁ : p ∧ ¬q → q ∧ ¬q) (hp : p) => -- q
  byContradiction (fun hnq : ¬q =>
  have hn : q ∧ ¬q := h₁ (And.intro hp hnq)
  absurd hn.left hn.right)
  )
