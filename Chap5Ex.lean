import HTPILib.Chap5
namespace HTPI.Exercises

/- Section 5.1 -/
-- 1.
theorem func_from_graph_ltr {A B : Type} (F : Set (A × B)) :
    (∃ (f : A → B), graph f = F) → is_func_graph F := by
  assume h : ∃ (f : A → B), graph f = F
  obtain (f : A → B) (h2 : graph f = F) from h
  define; fix a : A
  exists_unique
  · apply Exists.intro (f a)
    rw [← h2]; rfl
  · fix b₁; fix b₂; assume hb₁ : (a, b₁) ∈ F; assume hb₂ : (a, b₂) ∈ F
    rw [← h2] at hb₁; rw [← h2] at hb₂
    define at hb₁; define at hb₂
    rw [← hb₁, ← hb₂]
  done

-- 2.
theorem Exercise_5_1_13a
    {A B C : Type} (R : Set (A × B)) (S : Set (B × C)) (f : A → C)
    (h1 : ∀ (b : B), b ∈ Ran R ∧ b ∈ Dom S) (h2 : graph f = comp S R) :
    is_func_graph S := by
  define; fix b : B
  have hran : b ∈ Ran R := (h1 b).left; define at hran
  have hdom : b ∈ Dom S := (h1 b).right; define at hdom
  obtain (a : A) (ha : (a, b) ∈ R) from hran
  obtain (c : C) (hc : (b, c) ∈ S) from hdom
  exists_unique
  · apply Exists.intro c; exact hc
  · fix c₁; fix c₂; assume hc₁ : (b, c₁) ∈ S; assume hc₂ : (b, c₂) ∈ S
    have hac₁ : (a, c₁) ∈ comp S R := by
      define; apply Exists.intro b; apply And.intro ha hc₁
    have hac₂ : (a, c₂) ∈ comp S R := by
      define; apply Exists.intro b; apply And.intro ha hc₂
    rw [← h2] at hac₁; define at hac₁
    rw [← h2] at hac₂; define at hac₂
    rw [← hac₁, ← hac₂]
  done

-- 3.
theorem Exercise_5_1_14a
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h : ∀ (x y : A), R x y ↔ S (f x) (f y)) :
    reflexive S → reflexive R := by
  assume hs : reflexive S
  define at hs; define; fix a : A
  have hb : S (f a) (f a) := hs (f a)
  exact (h a a).mpr hb
  done

-- 4.
--You might not be able to complete this proof
theorem Exercise_5_1_15a
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v) :
    reflexive R → reflexive S := sorry
/-
The result is false. It may be the case that elements in `B` are not in the
range of `f`, and those elements are not related to any other, including
themselves.
-/

-- 5.
--You might not be able to complete this proof
theorem Exercise_5_1_15c
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v) :
    transitive R → transitive S := by
  assume hRtrans : transitive R
  define; fix x; fix y; fix z
  assume hSxy : S x y; assume hSyz : S y z
  /-
  The error in the proof is assuming that `v` is the same element for both.
  It may be the case that `f(v₁) = f(v₂) = y`, with `uRv₁` and `v₂Rw`. If
  `v₁ ≠ v₂`, we cannot use transitivity. The result is false.
  -/
  sorry

-- 6.
theorem Exercise_5_1_16b
    {A B : Type} (R : BinRel B) (S : BinRel (A → B))
    (h : ∀ (f g : A → B), S f g ↔ ∀ (x : A), R (f x) (g x)) :
    symmetric R → symmetric S := by
  assume symR : symmetric R
  define; fix f; fix g
  assume Sfg : S f g
  have Sfgequiv : ∀ (x : A), R (f x) (g x) := (h f g).mp Sfg
  have Sgfequiv : ∀ (x : A), R (g x) (f x) := by
    fix a; have h : R (f a) (g a) := Sfgequiv a
    define at symR; exact symR (f a) (g a) h
  exact (h g f).mpr Sgfequiv
  done

-- 7.
theorem Exercise_5_1_17a {A : Type} (f : A → A) (a : A)
    (h : ∀ (x : A), f x = a) : ∀ (g : A → A), f ∘ g = f := by
  fix g : A → A
  funext x
  have h₁ : f x = a := h x
  have h₂ : (f ∘ g) x = a := h (g x)
  rw [h₁, h₂]
  done

-- 8.
theorem Exercise_5_1_17b {A : Type} (f : A → A) (a : A)
    (h : ∀ (g : A → A), f ∘ g = f) :
    ∃ (y : A), ∀ (x : A), f x = y := by
  apply Exists.intro (f a); fix x
  set g : A → A := fun (x : A) => (f a)
  have hg : f ∘ g = f := h g
  have hfx : f x = (f ∘ g) x := by
    rw [hg]
  rw [← hg]; rfl
  done

/- Section 5.2 -/
-- 1.
theorem Exercise_5_2_10a {A B C : Type} (f: A → B) (g : B → C) :
    onto (g ∘ f) → onto g := by
  assume gfonto : onto (g ∘ f)
  define at gfonto; define
  fix c : C
  obtain (a : A) (ha : (g ∘ f) a = c) from gfonto c
  apply Exists.intro (f a)
  exact ha
  done

-- 2.
theorem Exercise_5_2_10b {A B C : Type} (f: A → B) (g : B → C) :
    one_to_one (g ∘ f) → one_to_one f := by
  assume gf11 : one_to_one (g ∘ f)
  define at gf11; define
  fix a₁; fix a₂; assume hf : f a₁ = f a₂
  have hgf : (g ∘ f) a₁ = (g ∘ f) a₂ := by
    repeat rw [comp_def]
    rw [hf]
  exact gf11 a₁ a₂ hgf
  done

-- 3.
theorem Exercise_5_2_11a {A B C : Type} (f: A → B) (g : B → C) :
    onto f → ¬(one_to_one g) → ¬(one_to_one (g ∘ f)) := by
  assume fonto : onto f
  assume gnot11 : ¬one_to_one g
  define at gnot11; define at fonto; define
  quant_neg at gnot11
  obtain (b : B) (hb : ¬∀ (b' : B), g b = g b' → b = b') from gnot11
  quant_neg at hb
  obtain (b' : B) (hb' : ¬(g b = g b' → b = b')) from hb
  conditional at hb'
  obtain (a : A) (ha : f a = b) from fonto b
  obtain (a' : A) (ha' : f a' = b') from fonto b'
  quant_neg; apply Exists.intro a; quant_neg; apply Exists.intro a'
  conditional
  apply And.intro
  · repeat rw [comp_def]
    rw [ha', ha]; exact hb'.left
  · by_contra h
    have h' : b = b' := by
      rw [← ha, ← ha', h]
    show False from hb'.right h'
  done

-- 4.
theorem Exercise_5_2_11b {A B C : Type} (f: A → B) (g : B → C) :
    ¬(onto f) → one_to_one g → ¬(onto (g ∘ f)) := by
  assume nontof : ¬(onto f)
  assume g11 : one_to_one g
  define at nontof; define at g11
  quant_neg at nontof
  obtain (b : B) (hb : ¬∃ (x : A), f x = b) from nontof
  quant_neg at hb
  define; quant_neg
  apply Exists.intro (g b)
  quant_neg; fix a
  by_contra h
  have hfab : f a = b := g11 (f a) b h
  have neghfab : ¬f a = b := hb a
  show False from neghfab hfab
  done

-- 5.
theorem Exercise_5_2_12 {A B : Type} (f : A → B) (g : B → Set A)
    (h : ∀ (b : B), g b = { a : A | f a = b }) :
    onto f → one_to_one g := by
  assume fonto : onto f
  define at fonto; define
  fix b₁; fix b₂
  assume gb : g b₁ = g b₂
  rw [h b₁, h b₂] at gb
  obtain (a : A) (ha : f a = b₁) from fonto b₁
  have haset : a ∈ {a : A | f a = b₁} := by
    define; exact ha
  rw [gb] at haset; define at haset
  rw [← ha, ← haset]
  done

-- 6.
theorem Exercise_5_2_16 {A B C : Type}
    (R : Set (A × B)) (S : Set (B × C)) (f : A → C) (g : B → C)
    (h1 : graph f = comp S R) (h2 : graph g = S) (h3 : one_to_one g) :
    is_func_graph R := by
  define at h3
  define; fix a
  have haga : (a, f a) ∈ graph f := by rfl
  rw [h1] at haga
  define at haga
  obtain (b : B) (hb : (a, b) ∈ R ∧ (b, f a) ∈ S) from haga
  exists_unique
  · apply Exists.intro b; exact hb.left
  · fix b₁; fix b₂; assume hb₁ : (a, b₁) ∈ R; assume hb₂ : (a, b₂) ∈ R
    have hgb₁ : (b₁, g b₁) ∈ S := by
      rw [← h2]; rfl
    have hagb₁ : (a, g b₁) ∈ graph f := by
      rw [h1]; define; apply Exists.intro b₁; exact And.intro hb₁ hgb₁
    have hgb₂ : (b₂, g b₂) ∈ S := by
      rw [← h2]; rfl
    have hagb₂ : (a, g b₂) ∈ graph f := by
      rw [h1]; define; apply Exists.intro b₂; exact And.intro hb₂ hgb₂
    define at hagb₁; define at hagb₂
    have gb₁b₂ : g b₁ = g b₂ := by
      rw [← hagb₁, ← hagb₂]
    exact h3 b₁ b₂ gb₁b₂
  done

-- 7.
theorem Exercise_5_2_17a
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h1 : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v)
    (h2 : onto f) : reflexive R → reflexive S := by
  assume reflR : reflexive R
  define at h2; define at reflR; define
  fix b : B
  obtain (a : A) (ha : f a = b) from h2 b
  have haR : R a a := reflR a
  rw [h1 b]; apply Exists.intro a; apply Exists.intro a
  exact And.intro ha (And.intro ha haR)
  done

-- 8.
theorem Exercise_5_2_17b
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h1 : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v)
    (h2 : one_to_one f) : transitive R → transitive S := by
  assume transR : transitive R
  define at h2; define at transR; define
  fix x; fix y; fix z; assume Sxy : S x y; assume Syz : S y z
  rw [h1 x y] at Sxy
  rw [h1 y z] at Syz
  obtain (u : A) (hu : ∃ (v : A), f u = x ∧ f v = y ∧ R u v) from Sxy
  obtain (v₁ : A) (hv₁ : f u = x ∧ f v₁ = y ∧ R u v₁) from hu
  obtain (v₂ : A) (hv₂ : ∃ (w : A), f v₂ = y ∧ f w = z ∧ R v₂ w) from Syz
  obtain (w : A) (hw : f v₂ = y ∧ f w = z ∧ R v₂ w) from hv₂
  have fv₁v₂ : f v₁ = f v₂ := by
    rw [hv₁.right.left, hw.left]
  have hv₁v₂ : v₁ = v₂ := h2 v₁ v₂ fv₁v₂
  rw [h1 x z]
  have hv₁w : R v₁ w := by
    have h : R v₂ w := hw.right.right
    rw [hv₁v₂]; exact h
  apply Exists.intro u; apply Exists.intro w
  have hRuw : R u w := transR u v₁ w hv₁.right.right hv₁w
  exact And.intro hv₁.left (And.intro hw.right.left hRuw)
  done

-- 9.
theorem Exercise_5_2_21a {A B C : Type} (f : B → C) (g h : A → B)
    (h1 : one_to_one f) (h2 : f ∘ g = f ∘ h) : g = h := by
  define at h1
  funext a
  have ghfa : (f ∘ g) a = (f ∘ h) a := by
    rw [h2]
  repeat rw [comp_def] at ghfa
  exact h1 (g a) (h a) ghfa
  done

-- 10.
theorem Exercise_5_2_21b {A B C : Type} (f : B → C) (a : A)
    (h1 : ∀ (g h : A → B), f ∘ g = f ∘ h → g = h) :
    one_to_one f := by
  define; fix b₁; fix b₂; assume hb : f b₁ = f b₂
  set g₁ : A → B := fun (a : A) => b₁
  set g₂ : A → B := fun (a : A) => b₂
  have hfg₁g₂ : f ∘ g₁ = f ∘ g₂ := by
    funext x; repeat rw [comp_def]
    exact hb
  have hg₁g₂ : g₁ = g₂ := h1 g₁ g₂ hfg₁g₂
  have hga : g₁ a = g₂ a := by
    rw [hg₁g₂]
  exact hga
  done

/- Section 5.3 -/
-- 1.
theorem Theorem_5_3_2_2 {A B : Type} (f : A → B) (g : B → A)
    (h1 : graph g = inv (graph f)) : f ∘ g = id := sorry

-- 2.
theorem Theorem_5_3_3_2 {A B : Type} (f : A → B) (g : B → A)
    (h1 : f ∘ g = id) : onto f := sorry

-- 3.
theorem Exercise_5_3_11a {A B : Type} (f : A → B) (g : B → A) :
    one_to_one f → f ∘ g = id → graph g = inv (graph f) := sorry

-- 4.
theorem Exercise_5_3_11b {A B : Type} (f : A → B) (g : B → A) :
    onto f → g ∘ f = id → graph g = inv (graph f) := sorry

-- 5.
theorem Exercise_5_3_14a {A B : Type} (f : A → B) (g : B → A)
    (h : f ∘ g = id) : ∀ x ∈ Ran (graph g), g (f x) = x := sorry

-- 6.
theorem Exercise_5_3_18 {A B C : Type} (f : A → C) (g : B → C)
    (h1 : one_to_one g) (h2 : onto g) :
    ∃ (h : A → B), g ∘ h = f := sorry

-- Definition for next two exercises:
def conjugate (A : Type) (f1 f2 : A → A) : Prop :=
    ∃ (g g' : A → A), (f1 = g' ∘ f2 ∘ g) ∧ (g ∘ g' = id) ∧ (g' ∘ g = id)

-- 7.
theorem Exercise_5_3_17a {A : Type} : symmetric (conjugate A) := sorry

-- 8.
theorem Exercise_5_3_17b {A : Type} (f1 f2 : A → A)
    (h1 : conjugate A f1 f2) (h2 : ∃ (a : A), f1 a = a) :
    ∃ (a : A), f2 a = a := sorry

/- Section 5.4 -/
-- 1.
example {A : Type} (F : Set (Set A)) (B : Set A) :
    smallestElt (sub A) B F → B = ⋂₀ F := sorry

-- 2.
def complement {A : Type} (B : Set A) : Set A := { a : A | a ∉ B }

theorem Exercise_5_4_7 {A : Type} (f g : A → A) (C : Set A)
    (h1 : f ∘ g = id) (h2 : closed f C) : closed g (complement C) := sorry

-- 3.
theorem Exercise_5_4_9a {A : Type} (f : A → A) (C1 C2 : Set A)
    (h1 : closed f C1) (h2 : closed f C2) : closed f (C1 ∪ C2) := sorry

-- 4.
theorem Exercise_5_4_10a {A : Type} (f : A → A) (B1 B2 C1 C2 : Set A)
    (h1 : closure f B1 C1) (h2 : closure f B2 C2) :
    B1 ⊆ B2 → C1 ⊆ C2 := sorry

-- 5.
theorem Exercise_5_4_10b {A : Type} (f : A → A) (B1 B2 C1 C2 : Set A)
    (h1 : closure f B1 C1) (h2 : closure f B2 C2) :
    closure f (B1 ∪ B2) (C1 ∪ C2) := sorry

-- 6.
theorem Theorem_5_4_9 {A : Type} (f : A → A → A) (B : Set A) :
    ∃ (C : Set A), closure2 f B C := sorry

-- 7.
theorem Exercise_5_4_13a {A : Type} (F : Set (A → A)) (B : Set A) :
    ∃ (C : Set A), closure_family F B C := sorry

/- Section 5.5 -/

--Warning!  Not all of these examples are correct!
example {A B : Type} (f : A → B) (W X : Set A) :
    image f (W ∪ X) = image f W ∪ image f X := sorry

example {A B : Type} (f : A → B) (W X : Set A) :
    image f (W \ X) = image f W \ image f X := sorry

example {A B : Type} (f : A → B) (W X : Set A) :
    W ⊆ X ↔ image f W ⊆ image f X := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f  (Y ∩ Z) =
        inverse_image f Y ∩ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f  (Y ∪ Z) =
        inverse_image f Y ∪ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f  (Y \ Z) =
        inverse_image f Y \ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    Y ⊆ Z ↔ inverse_image f Y ⊆ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (X : Set A) :
    inverse_image f (image f X) = X := sorry

example {A B : Type} (f : A → B) (Y : Set B) :
    image f (inverse_image f Y) = Y := sorry

example {A : Type} (f : A → A) (C : Set A) :
    closed f C → image f C ⊆ C := sorry

example {A : Type} (f : A → A) (C : Set A) :
    image f C ⊆ C → C ⊆ inverse_image f C := sorry

example {A : Type} (f : A → A) (C : Set A) :
    C ⊆ inverse_image f C → closed f C := sorry

example {A B : Type} (f : A → B) (g : B → A) (Y : Set B)
    (h1 : f ∘ g = id) (h2 : g ∘ f = id) :
    inverse_image f Y = image g Y := sorry
