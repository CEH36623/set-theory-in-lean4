open Classical

variable (α : Type) (p q : α → Prop)
variable (b : Prop) (w : α)

#check Eq.refl
#check Eq.refl _
#check rfl
#check Eq.symm
#check Eq.trans
#check Eq.subst
#check congrArg
#check congrFun
#check congr
#check Exists.intro
#check Exists.elim



example : (∃ x : α, b) → b :=
  fun h : (∃ x : α, b) =>
  Exists.elim h (fun (w : α)  => fun hw : b => hw)

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


example (a : α) : (∃ x, p x → b) ↔ (∀ x, p x) → b :=
  Iff.intro
    (fun (h₁ : (∃ x, p x → b)) (h₂ : (∀ x, p x)) =>
      match h₁ with
      | ⟨w, hw⟩ =>  hw (h₂ w)
     )

    (fun h : ((x : α) → p x) → b  =>
      --have h₁ : (x : α) → p x → b :=

      sorry
      )

example (a : α) : (∃ x, b → p x) ↔ (b → ∃ x, p x) :=
  Iff.intro
    (fun (h₁ : (∃ x, b → p x)) (hb : b)  =>
      match h₁ with
      | ⟨w, hw⟩ => ⟨w, (hw hb)⟩
    )
    ( sorry
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
  sorry
