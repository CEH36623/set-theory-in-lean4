variable (p q r s : Prop)
--1. 양화사 하기.
--2. tactic 정리하면서 증명 다시
--Conjuction
#check And.intro
#check And.left
#check And.right

--Disjuction
#check Or.intro_left -- 명제 ∨ 참값 명제 타입
#check Or.intro_right  -- 참값 명제 타입 ∨ 명제
#check Or.inl -- 명제 자동완성 ver
#check Or.inr  -- 명제 자동완성 ver
#check Or.elim
-- a or b -> ~b -> a 이거 어디갔어.


-- neg and contradiction

-- ¬p
#check ¬p -- p → False
-- 모순으로부터 무엇이든 증명
#check False.elim -- False -> C
-- False.elim (h : False) 아무 명제 다 나옴, 자동완성
#check absurd
#check True.intro


-- Iff
#check Iff.intro --(a → b) → (b → a) → (a ↔ b)
#check Iff.mp -- a ↔ b → a → b
#check Iff.mpr -- a ↔ b → b → a

open Classical
#check em p -- 배중률
-- byContradiction : 귀류법
-- input(부정할 명제 : ¬p) => false → p 명제가 튀어나옴, 보통 have로 잡지


---------------------------------------------------
-- Conjunction(∧) Introduction
example (hp : p)(hq : q) : p ∧ q :=
  And.intro hp hq
  -- ⟨hp, hq⟩

-- Conjunction(∧) Elimination(2)
example (h : p ∧ q) : p :=
  And.left h
-- h.left
example (h :p ∧ q) : q :=
  And.right h
-- h.right

-- ano notation
--1. And.intro hp hq
--      ⟨hp, hq⟩
--2. And.left
--      h.left
---------------------------------------------------

-- Disjuction(∨) Introduction
example (hp : p) : p ∨ q :=
  Or.intro_left q hp
  --명제 타입(new), p타입 (있던 거)
  --왼쪽 걸 이용해서 도입한다.
  --Or.inl hp
example (hq : q) : p ∨ q :=
  Or.intro_right p hq

--Disjuction(∨) Elimination
example (h : p ∨ q) : q ∨ p :=
Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)
-- hp : p라고 해도 됨. (자동완성)

--ano notation
-- 1. Or.intro_left q hp
  --      Or.inl hp (명제 생략)
example (hp : p) : p ∨ q :=
  Or.inl hp -- 명제를 안 써도 자동완성 됨.

---------------------------------------------------

-- Implication Introduction
example  : p → q :=
  fun (hp : p) => sorry

-- Inmlication Elimination
example (hp : p) (h : p → q): q :=
  h hp

---------------------------------------------------

-- ~p
#check ¬p -- same as p → False


-- False.elim
-- False 넣으면 자동완성
theorem DS : (p ∨ q) ∧ ¬p  → q :=
  fun h : (p ∨ q) ∧ ¬p =>
  Or.elim h.left
  (fun hp : p => False.elim (h.right hp)) -- 여기에서 False를 넣었더니 q(자동완성)가 나옴.
  (fun hq : q => hq)

-- 앞에것 가독성 높게
-- absurd
-- hp hnp 넣으면 자동완성
theorem DS2 : (p ∨ q) ∧ ¬p  → q :=
  fun h : (p ∨ q) ∧ ¬p =>
  Or.elim h.left
  (fun hp : p => absurd hp h.right)
  (fun hq : q => hq)

-- False.elim (hnp hp)
--  absurd hp hnp 같은 말

---------------------------------------------------

-- Iff Introduction
example (h₁ : p → q) (h₂ : q → p) : p ↔ q :=
  Iff.intro h₁ h₂

-- Iff Elimination
example (h : p ↔ q) (hp : p) : q :=
  Iff.mp h hp     -- 제거 (→ 방향)

example (h : p ↔ q) (hq : q) : p :=
  Iff.mpr h hq     -- 제거 (← 방향)

---------------------------------------------------

-- em 배중률 사용 예
-- em : p → p ∨ ¬p
theorem dne {p : Prop} (h : ¬¬p) : p :=
Or.elim (em p)
(fun hp : p => hp)
(fun hnp : ¬p => absurd hnp h)

-- byContradicion 사용 예

-- Using False.elim
theorem dne2 (h : ¬¬p) : p :=
byContradiction
  (fun h₁ : ¬p =>
   False.elim (h h₁) )

--Using absurd
theorem dne3 (h : ¬¬p) : p :=
byContradiction
  (fun h₁ : ¬p =>
   absurd h₁ h)
