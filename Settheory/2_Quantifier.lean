open Classical

variable (α : Type) (p q : α → Prop)
variable (b : Prop) (w : α)

---------------------------------------------------

#check (∀ x :  α, p x ∧ q x) -- 명제
#check fun x : α => p x ∧ q x -- 명제를 구성하는 함수
--위 명제는 아래와 같은 함수로 대응 될 수 있다.

#check(∃ x : α, p x ∧ q x)
#check Exists (fun x : α => p x ∧ q x)
#check Exists
--전자는 후자로 desugar됨
-- ∀은 핵심 논리문법 -> ∃는 inductive type으로 만든 것.

#check Exists.intro
#check Exists.elim

---------------------------------------------------
-- ∀ Introduction
example : ∀ x : ℕ, x = x :=
  fun x => rfl
-- 함수를 만들면 됨

-- ∀ Elimination
example (h : ∀ x : α, p x) (a : α) : p a :=
  h a
-- h : (x : α) -> p x이므로
-- p a 나옴

---------------------------------------------------

-- ∃ Introduction
-- (∃에 종속될 항) (그 항을 포함한 명제)
-- 종속변수 x도 들어갈 수 있다.
example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h
-- h에서 0을 y로 intro
example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

-- ∃ Elimination
-- exists.elim의 형식
-- ∃ x, p x
-- ∀ x, p x → (b : prop)
-----------------------
-- b
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
  (fun w : α  =>
  fun hw : p w ∧ q w =>
    have hw₂ : q w ∧ p w :=
      ⟨hw.right, hw.left⟩
    Exists.intro w hw₂
  )

-- ∃ intro 축약형 notation
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
  (fun w =>
  fun hw : p w ∧ q w =>
  show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)

-- match를 사용해서 축약 ()
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with -- exists 없앨 명제
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩



-- notations
-- 1. Exists.intro 0 h
--   same as ⟨0,h⟩
-- 2. match h with
-- fun w => fun hw : p w ∧ q w
-- same as ⟨w, hw⟩
-- 나머지는 그대로.
-- for all 부분 간단하게 작성하기

---------------------------------------------------

example : (∃ x : α, b) → b :=
  fun h : (∃ x : α, b) =>
  Exists.elim h (fun (w : α)  => fun hw : b => hw)

--ver2
example : (∃ x : α, b) → b :=
  fun h =>
  match h with
  | ⟨_, hw⟩ => hw

example (a : α) : b → (∃ x : α, b) :=
  fun hb : b =>
  Exists.intro a hb

example : (∃ x, p x ∧ b) ↔ (∃ x, p x) ∧ b :=
  Iff.intro
  (fun h : (∃ x, p x ∧ b) =>
    Exists.elim h (fun w =>
    fun hw : p w ∧ b =>
    have hr : p w := hw.left
    And.intro (Exists.intro w (hr)) hw.right
     ))

  (fun h : (∃ x, p x) ∧ b =>  -- (∃ x, p x ∧ b)
   Exists.elim h.left (fun w =>
   fun hw : p w
    => Exists.intro w ⟨hw, h.right⟩
  )
  )

example : (∃ x, p x ∧ b) ↔ (∃ x, p x) ∧ b :=
  Iff.intro
    (fun h =>
      match h with
      | ⟨w, hpw, hb⟩ => ⟨⟨w, hpw⟩, hb⟩
    )
    (fun ⟨⟨w, hpw⟩, hb⟩ =>
      ⟨w, ⟨hpw, hb⟩⟩
  )

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := -- 13
  Iff.intro
    (fun  h : (∃ x, p x ∨ q x) =>
     Exists.elim h
     (fun w => fun h1 : p w ∨ q w =>
     Or.elim h1
     (fun hpw : p w => Or.intro_left (∃ x, q x) (Exists.intro w hpw))
     (fun hqw : q w => Or.intro_right (∃ x, p x) (Exists.intro  w hqw))
     )
    )
    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
        (fun hl =>
        Exists.elim hl (fun w => fun hlpw : p w => Exists.intro w (Or.intro_left (q w) hlpw))
        )
        (fun hr =>
        Exists.elim hr (fun w => fun hrqw : q w => Exists.intro w (Or.intro_right (p w) hrqw))
        )
    )



example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨a, (h1 : p a ∨ q a)⟩ =>
      Or.elim h1
        (fun hpa : p a => Or.inl ⟨a, hpa⟩)
        (fun hqa : q a => Or.inr ⟨a, hqa⟩))

    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
        (fun ⟨a, hpa⟩ => ⟨a, (Or.inl hpa)⟩)
        (fun ⟨a, hqa⟩ => ⟨a, (Or.inr hqa)⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h₁ : (∀ x, p x) =>-- (∃ x, (p x) → False)) → False
       fun h₂ : (∃ x, ¬ p x) =>
        match h₂ with
        | ⟨w, hw⟩ => hw (h₁ w)
     )
     (fun h : ¬ (∃ x, ¬ p x) =>
      fun x : α  => -- p x
        byContradiction (fun hnp : ¬p x => -- (p x → False)
        have hex : ∃ x, ¬ p x := ⟨x, hnp⟩
        False.elim (h hex))

     )

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
  (fun h₁ : ∃ x, p x =>  -- (∀ x, ¬ p x) → False, False증명
    fun h₂ : ∀ x, ¬ p x =>  -- False
    match h₁ with
    | ⟨w, hw⟩ => (h₂ w) hw
  )

  (fun h : ¬ (∀ x, ¬ p x) => -- (∃ x, p x)  -- p w
    byContradiction (fun h₁ : ¬ (∃ x, p x) =>
    have h₂ :  (∀ x, ¬ p x) := fun x => fun hp : p x => h₁ ⟨x, hp⟩
    h h₂
    )
  )


example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
  (fun h : (¬ ∃ x, p x) => -- Exists p → False

    fun w : α =>
    fun hpw : p w =>
    have he : ∃ x, p x := Exists.intro w hpw
    h he -- False
    )
  (fun h : (∀ x, ¬ p x) =>  -- Exists p → False
    fun hep : ∃ x, p x =>
      Exists.elim hep (fun w => fun hw : p w => (h w) hw)
   )

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
  (fun h₁ : (¬ ∀ x, p x) => -- ¬ p w - (x → p x) → False
    byContradiction (
      fun hnp : ¬(∃ x, ¬ p x) =>
       have  h₂ : ∀ x, p x :=
       fun x =>
        byContradiction (fun hpx : ¬ p x =>
          have h₃ : ∃ x, ¬ p x := ⟨x, hpx⟩
          hnp h₃
          )
      h₁ h₂
    )
  )
  (fun h₁ : ∃ x, ¬ p x => fun h₂ : ∀ x, p x=>
  match h₁ with
  | ⟨w, hw⟩ => hw (h₂ w)
  )

example : (∀ x, p x → b) ↔ (∃ x, p x) → b :=
  Iff.intro
    (fun (h₁ :  (∀ x, p x → b)) (h₂ : ∃ x, p x )  =>   -- b
    match  h₂ with
    | ⟨w, hw⟩ => (h₁ w) hw
    )
    (fun (h₁ : (∃ x, p x) → b)  => -- (∀ x, p x → b)
     fun x => fun hp : p x => h₁ ⟨x, hp⟩
    )

-- α의 어떤 임의의 원소
example (a : α) : (∃ x, p x → b) ↔ (∀ x, p x) → b :=
  Iff.intro
    (fun (h₁ : (∃ x, p x → b)) (h₂ : (∀ x, p x)) =>
      match h₁ with
      | ⟨w, hw⟩ =>  hw (h₂ w)
     )

    (fun h₁: ((x : α) → p x) → b  =>
      --have h₁ : (x : α) → p x → b :=
      Or.elim (em b)
      (fun hb : b =>
        ⟨a, fun _ => hb⟩ -- 임의의 참값 a를 넣음면 됨.
      --fun hpa : p a 과 동일, 안 쓰면 세모 뜨니까.
      )

      (fun hnb : ¬b =>
      -- 2. 도입 안에 식 전개하기.


        -- have hnpa : ¬ (∀ x, p x) :=
        --   byContradiction ( fun (ha : ¬¬ ∀ x, p x) =>
        --   have h₄ : ∀ x, p x :=
        --       byContradiction (fun hna : ¬ (∀ x, p x) => False.elim (ha hna) )
        --   False.elim (hnb (h₁ h₄)))
          have henp : (∃ x, ¬ p x) :=
            byContradiction (fun hnp : ¬(∃ x, ¬ p x) =>
              have  hax : ∀ x, p x :=
                fun x =>
                  byContradiction (fun hnpx : ¬ p x =>
                    have henp₂ : ∃ x, ¬ p x := ⟨x, hnpx⟩
                    hnp henp₂
                    )
              False.elim (hnb (h₁ hax))
            )
          have hd : (∃x, ¬b → ¬ p x) :=
            match henp with
            | ⟨w, henpw⟩ => ⟨w,(fun hnb₁ : ¬ b => henpw)⟩
          match hd with
          | ⟨x, hdx⟩ => ⟨x, fun hpx : p x => have hnpx : ¬p x := hdx hnb; absurd hpx hnpx⟩
      )
    )
      -- have h₂ : ((x : α) → p x) := fun _ => hpx
      -- 잘못된 이유 : p a가 성립한다고 해서 ∀ x, p x가 성립되는 건 아니다.
      -- 논리가 잘못됨.




example (a : α) : (∃ x, b → p x) ↔ (b → ∃ x, p x) :=
  Iff.intro
    (fun (h₁ : (∃ x, b → p x)) (hb : b)  =>
      match h₁ with
      | ⟨w, hw⟩ => ⟨w, (hw hb)⟩
    )
      (fun(h₂ : (b → ∃ x, p x)) =>
        Or.elim (em b)
          (fun hb : b =>
            let hx := h₂ hb
            match hx with
            | ⟨x, hxx⟩ => ⟨x,(fun (hbb : b) => hxx)⟩
            -- b 타입 값 하나 받아야 하는데 이미 hb 있으니까 hbb로 안 받고
            -- fun _로 가도 됨.
          )
          (fun hnb : ¬b =>
            ⟨a, fun h => (hnb h).elim⟩
          )

      )

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun ( h : ∀ x, p x ∧ q x) =>
      ⟨fun w => (h w).left, fun w => (h w).right⟩)
    (fun ( h : (∀ x, p x) ∧ (∀ x, q x)) =>
      fun w => ⟨ (h.left) w, (h.right) w ⟩
    )

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h₁ : (∀ x, p x → q x) => fun h₂ : (∀ x, p x) =>
    fun w => h₁ w (h₂ w)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h : (∀ x, p x) ∨ (∀ x, q x) =>
      Or.elim h
        (fun hp :∀ x, p x => fun w => Or.inl (hp w))
        (fun hq :∀ x, q x => fun w => Or.inr (hq w))

example : α → ((∀ x : α, b) ↔ b) :=
  fun a : α  =>
    Iff.intro (fun h₁  : (∀ x : α, b) => (h₁ a)) (fun hb : b => fun x : α => hb)

example : (∀ x, p x ∨ b) ↔ (∀ x, p x) ∨ b :=
  Iff.intro
  (fun h : (∀ x, p x ∨ b) =>
    Or.elim (em b)
    (fun hb : b => Or.inr hb)
    (fun hnb : ¬b =>
      have h1 : ∀x, p x :=
        fun x => (h x).elim
          (fun hpx : p x  => hpx)
          (fun hb : b => False.elim (hnb hb))
      Or.inl h1
    )
  )
  (fun h : (∀ x, p x) ∨ b => fun x =>
    Or.elim h (fun h₁ : (∀ x, p x) =>  Or.inl (h₁ x)) (fun h₂ : b => Or.inr h₂)
  )
example : (∀ x, b → p x) ↔ (b → ∀ x, p x) :=
  Iff.intro
    (fun (h : (∀ x, b → p x)) (hb : b) => fun y : α => (h y) hb )
    (fun (h : (b → ∀ x, p x)) => fun (y : α) (hb : b)=> h hb y)

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have h₁ :shaves barber barber →  ¬ shaves barber barber := Iff.mp (h barber)
  have h₂ :¬ shaves barber barber → shaves barber barber := Iff.mpr (h barber)
  False.elim (
    Or.elim (em (shaves barber barber))
    (fun hs : shaves barber barber =>
      False.elim ((h₁ hs) hs))
    (fun hns : ¬ shaves barber barber =>
      False.elim (hns (h₂ hns)))
      )
