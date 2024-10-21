-- Definizione app
def app : List α → List α → List α
  | [], l2 => l2
  | a::l1, l2 => a :: app l1 l2

-- Definizione rev
def rev : List α → List α
  | [] => []
  | a::l => app (rev l) (a::[])

-- Definizione rev1
def rev1 : List α → List α → List α
  | [], l2 => l2
  | a::l1, l2 => rev1 l1 (a::l2)

-- Propoposizione 7.1.15.1
theorem app_nil (l : List α) : app l [] = l := by
  induction l with
  | nil => rw [app]
  | cons a l' ih => rw [app, ih]

-- Proposizione 7.1.15.2
theorem app_assoc (l1 l2 l3 : List α) : app (app l1 l2) l3 = app l1 (app l2 l3) := by
  induction l1 with
  | nil => repeat rw [app]
  | cons a l' ih => rw [app, app, ih, ←app]

-- Proposizione 7.1.15.3
theorem rev_app_eq_app_rev_rev (l1 l2 : List α) : rev (app l1 l2) = app (rev l2) (rev l1) := by
  induction l1 with
  | nil => rw [rev, app, app_nil]
  | cons a l' ih => rw [app, rev, ih, app_assoc, rev]

-- Proprietà (1)
theorem rev_rev_eq_norev (l : List α) : rev (rev l) = l := by
  induction l with
  | nil => repeat rw [rev]
  | cons a l' ih => rw [rev, rev_app_eq_app_rev_rev, ih] ; repeat rw [rev] ; repeat rw [app]


-- Dimostrazione che l'invariante implica rev1(l, []) = rev(l)
theorem inv_impl_rev1_nil_eq_rev (h : forall l1 l2 : List α, rev1 l1 l2 = app (rev l1) l2) (l : List α) : rev1 l [] = rev l := by
  induction l with
  | nil => rw [h, rev, app]
  | cons a l' => rw [h, app_nil]

-- Dimostrazione invariante
theorem inv (l1 : List α) : forall (l2 : List α), rev1 l1 l2 = app (rev l1) l2 := by
  induction l1 with
  | nil => intro l ; rw [rev1, rev, app]
  | cons a l' ih => intro l ; rw [rev1, ih (a::l), ←rev_rev_eq_norev (a::l), ←rev_app_eq_app_rev_rev, rev, app_assoc, app, app, rev_app_eq_app_rev_rev, rev_rev_eq_norev]


-- Applichiamo la dimostrazione dell'invariante all'implicazione inv_impl_rev1_nil_eq_rev per completare la dimostrazione della proprietà (2)
theorem rev1_nil_eq_rev (l : List α) : rev1 l [] = rev l := by
  exact inv_impl_rev1_nil_eq_rev inv l



-- Dim di Clorinda
def intt : List α → List α → List α
  | [], l2 => l2
  | a::l1, l2 => app (rev (a::l1)) l2

def intt_def (l1 : List α) (l2 : List α) : intt l1 l2 = app (rev l1) l2 := by
  induction l1 with
  | nil => simp [intt, rev, app]
  | cons a l' ih => simp [intt]
  
theorem int_eq_rev1 (l1 : List α) : forall (l2 : List α), intt l1 l2 = rev1 l1 l2 := by
  induction l1 with
  | nil => intro l ; simp [intt, rev1]
  | cons a l' ih => intro l ; simp [intt] ; rw [rev, app_assoc, app, app] ; rw [←intt_def l' (a::l), ih, rev1] 

theorem rev1_nil_eq_rev_bog (l : List α) : rev1 l [] = rev l := by
  have h (l1 : List α) : forall (l2 : List α), intt l1 l2 = rev1 l1 l2 := int_eq_rev1 l1
  have lol := h l []
  rw [intt_def] at lol
  exact inv_impl_rev1_nil_eq_rev h l
