import tactic

inductive llist (V : Type) : Type | P : V -> llist | L : V -> llist -> llist

namespace llist section
    parameters {V : Type} (adj : V -> V -> Prop)

    def mem : V -> llist V -> Prop | x (P v) := x = v | x (L v l) := x = v ∨ mem x l
    instance has_mem_llist : has_mem V (llist V) := ⟨mem⟩

    def to_list :            llist V -> list V  |   (P v)    := [v]       |   (L v l)    := v :: to_list l
    def size    :            llist V -> nat     |   (P _)    := 0         |   (L v l)    := (size l) + 1
    def head    :            llist V -> V       |   (P v)    := v         |   (L v l)    := v
    def tail    :            llist V -> list V  |   (P v)    := []        |   (L v l)    := l.head :: tail l
    def init    :            llist V -> list V  |   (P v)    := []        |   (L v l)    := v :: init l
    def last    :            llist V -> V       |   (P v)    := v         |   (L v l)    := last l
    def inside  :            llist V -> list V  |   (P v)    := []        |   (L v l)    := init l
    def is_path :            llist V -> Prop    |   (P v)    := true      |   (L v l)    := adj v l.head ∧ is_path l
    def append  :       V -> llist V -> llist V | x (P v)    := L v (P x) | x (L v l)    := L v (append x l)
    def rev     :            llist V -> llist V |   (P v)    := (P v)     |   (L v l)    := append v (rev l)
    def nodup   :            llist V -> Prop    |   (P v)    := true      |   (L v l)    := v ∉ l ∧ nodup l
    def concat  : llist V -> llist V -> llist V |   (P _) l' := l'        |   (L v l) l' := L v (concat l l')

    @[simp] def compat (l₁ l₂ : llist V) := last l₁ = head l₂
    def qnodup (l : llist V) := head l ∉ inside l ∧ last l ∉ inside l ∧ list.nodup (inside l)

    variables {x y v w : V} {l l' l'' : llist V}

    @[simp] lemma head_P                           : head (P x)               = x
        := rfl

    @[simp] lemma head_cons                        : head (L v l)             = v
        := rfl

    @[simp] lemma last_P                           : last (P x)               = x
        := rfl

    @[simp] lemma concat_head    (h : compat l l') : head (concat l l')       = head l
        := by { cases l, { convert h.symm }, { refl } }

    @[simp] lemma concat_last                      : last (concat l l')       = last  l'
        := by { induction l, { rw concat }, { rwa [concat,last] } }

    @[simp] lemma append_head                      : head (append v l)        = head l
        := by { cases l; refl }

    @[simp] lemma append_last                      : last (append v l)        = v
        := by { induction l; simp!, assumption }

    @[simp] lemma rev_append                       : rev  (append v l)        = L v (rev l)
        := by { induction l; simp!, rw l_ih, simp! }

    @[simp] lemma append_rev                       : rev (L v l)              = append v (rev l)
        := by { induction l; simp! }

    @[simp] lemma rev_head                         : head (rev l)             = last l
        := by { induction l; simp!, assumption}

    @[simp] lemma rev_last                         : last (rev l)             = head l
        := by { induction l; simp! }

    @[simp] lemma rev_rev                          : rev  (rev l)             = l
        := by { induction l; simp!, assumption }

    @[simp] lemma mem_singleton                    : x ∈ P y                <-> x = y
        := iff.rfl

    @[simp] lemma mem_cons                         : x ∈ L v l              <-> x = v ∨ x ∈ l
        := iff.rfl

    @[simp] lemma concat_path    (h : compat l l') : is_path (concat l l')  <-> is_path l ∧ is_path l'
        := by { induction l with v v l hr; simp!, simp! at h, rw [concat_head h, hr h], tauto }

    @[simp] lemma mem_append                       : w ∈ append v l         <-> w = v ∨ w ∈ l
        := by { induction l; simp!; cc }

    @[simp] lemma mem_rev                          : v ∈ rev l              <-> v ∈ l
        := by { induction l; simp!, cc }

    @[simp] lemma mem_head                         : head l ∈ l
        := by { cases l; simp! }

    @[simp] lemma mem_last                         : last l ∈ l
        := by { induction l; simp!, right, assumption }

    @[simp] lemma mem_list                         : x ∈ to_list l          <-> x ∈ l
        := by { induction l with v v l hr; simp!, rw hr }

    @[simp] lemma append_nodup                     : nodup (append x l)     <-> x ∉ l ∧ nodup l
        := by { induction l; simp [append, nodup], tauto, push_neg, rw l_ih, tauto }

    @[simp] lemma append_is_path                   : is_path (append v l)   <-> adj (last l) v ∧ is_path l
        := by { induction l; finish [is_path, append] }

    @[simp] lemma rev_nodup                        : nodup (rev l)          <-> nodup l
        := by { induction l; finish [rev, nodup] }

    @[simp] lemma init_append                      : init (append x l)        = to_list l
        := by { induction l with v v l hr; simp [append,init,to_list], assumption }

    @[simp] lemma list_head_tail                   : head l :: tail l         = to_list l
        := by { induction l; simp [to_list,tail], assumption }

    @[simp] lemma list_init_last                   : init l ++ [last l]       = to_list l
        := by { induction l; simp [to_list,init], assumption }

    @[simp] lemma list_head_init  (h : 0 < size l) : head l :: inside l       = init l
        := by { cases l with v v l, cases h, simp [head,inside,init] }

    @[simp] lemma list_tail_last  (h : 0 < size l) : inside l ++ [last l]     = tail l
        := by { cases l with v v l, cases h, simp [inside,last,tail],  }

    @[simp] lemma inside_append                    : inside (append x l)      = tail l
        := by { induction l with v v l hr; simp [append,inside,init,tail,to_list], }

    @[simp] lemma tail_append                      : tail (append x l)        = tail l ++ [x]
        := by { induction l with v v l hr; simp [append,tail], rw [hr,<-list_head_tail], refl }

    @[simp] lemma tail_rev                         : tail (rev l)             = list.reverse (init l)
        := by { induction l with v v l hr; simp [rev,tail,init], rw hr }

    @[simp] lemma rev_inside                       : inside (rev l)           = list.reverse (inside l)
        := by { induction l with v v l hr; simp [rev,inside] }

    @[simp] lemma rev_qnodup                       : qnodup (rev l)         <-> qnodup l
        := by { simp [qnodup], finish }

    @[simp] lemma rev_is_path  (h : symmetric adj) : is_path (rev l)        <-> is_path l
        := by { induction l; simp [rev, is_path], tidy }

    @[simp] lemma mem_concat     (h : compat l l') : x ∈ concat l l'        <-> x ∈ l ∨ x ∈ l'
        := by { induction l with v v l hr, refine ⟨or.inr, _⟩, simp, finish [compat, concat, last], finish [concat] }

    @[simp] lemma concat_nil      (h : last l = w) : concat l (P w)           = l
        := by { induction l; rw concat, { simp, exact h.symm }, finish }

    @[simp] lemma concat_nil2                      : concat (P w) l           = l
        := rfl

    @[simp] lemma concat_size                      : size (concat l l')       = size l + size l'
        := by {induction l; rw concat; rw size, simp, rw size, rw l_ih, simp }

    lemma         concat_assoc                     : concat (concat l l') l'' = concat l (concat l' l'')
        := by { induction l with v v l hr; simp [concat], exact hr }

    lemma         concat_nodup   (h : compat l l') : nodup (concat l l')    <-> nodup l ∧ nodup l' ∧ (∀ x, x ∈ l ∧ x ∈ l' -> x = head l')
        := by { induction l with v v l hr,
            { finish [nodup, last] },
            { rw [concat,nodup,nodup], simp [nodup, concat], simp [last] at h, rw [hr h], split,
                { rintros ⟨h1,h2,h3,h4⟩, rw mem_concat h at h1, push_neg at h1, refine ⟨⟨h1.1,h2⟩,h3,_⟩,
                    rintros x h6 h7, cases h6,
                    { subst h6, cases h1.2 h7 },
                    { exact h4 x ⟨h6,h7⟩ } },
                { rintros ⟨⟨h1,h2⟩,h3,h4⟩, rw mem_concat h, push_neg, refine ⟨⟨h1,_⟩,h2,h3,_⟩,
                    { intro h5, have h6 := h4 v (or.inl rfl) h5, subst h6, rw <-h at h1, exact (h1 mem_last) },
                    { rintros x ⟨h5,h6⟩, exact h4 x (or.inr h5) h6, } } } }

    lemma         mem_iff             (h : l = l') : x ∈ l                  <-> x ∈ l'
        := by { rw h }

    lemma         mem_init        (h : x ∈ init l) : x ∈ l
        := by { induction l; finish [init] }

    lemma         mem_head_init   (h : 0 < size l) : head l ∈ init l
        := by { cases l, cases h, simp! }

    lemma         mem_last_tail   (h : 0 < size l) : last l ∈ tail l
        := by { cases l with v v l, cases h, clear h, induction l with w w l hr, 
            { simp! }, { exact or.inr hr } }

    lemma         mem_tail        (h : x ∈ tail l) : x ∈ l
        := by { cases l, cases h, simp [tail] at h, right, assumption }

    lemma         mem_init_last                    : x ∈ l                  <-> x ∈ init l ∨ x = last l
        := by { split,
            { induction l with v v l hr; simp [init,last], intro h, cases h,
                { left, left, assumption },
                { cases (hr h), left, right, exact h_1, right, exact h_1 } },
            { intro h, cases h, exact mem_init h, convert mem_last } }

    lemma         mem_head_tail                    : x ∈ l                  <-> x = head l ∨ x ∈ tail l
        := by { cases l; simp [tail] }

    lemma         mem_init_inside (h : 0 < size l) : x ∈ init l             <-> x = head l ∨ x ∈ inside l
        := by { rw <-(list_head_init h), simp }

    lemma         mem_tail_inside (h : 0 < size l) : x ∈ tail l             <-> x ∈ inside l ∨ x = last l
        := by { rw <-(list_tail_last h), simp }

    lemma         nodup_mem_head     (h : nodup l) : head l ∉ tail l
        := by { cases l; simp [head,tail], exact h.1 }

    lemma         nodup_mem_last     (h : nodup l) : last l ∉ init l
        := by { induction l with v v l hr; simp [init,last], push_neg, split,
            { intro h1, apply h.1, convert mem_last, rw h1 },
            { exact hr h.2 } }

    lemma         rev_compat                       : compat l l' <-> compat l'.rev l.rev
        := by { finish }

    lemma         concat_append                    : append v (concat l l')  = concat l (append v l')
        := by { induction l with w w l hr, refl, { rw concat, rw append, rw hr, refl } }

    lemma         rev_concat     (h : compat l l') : rev (concat l l')       = concat (rev l') (rev l)
        := by { induction l with v v l hr,
            { simp [rev], rw concat_nil, rw rev_last, exact h.symm },
            { simp [compat,last] at h, simp [hr h,rev,concat,concat_append] } }

    lemma         nodup_init         (h : nodup l) : list.nodup (init l)
        := by { induction l with v v l hr; simp [init,nodup],
            refine ⟨_,hr h.2⟩, intro h1, exact h.1 (mem_init h1) }

    lemma         nodup_qnodup       (h : nodup l) : qnodup l
        := by { induction l with v v l hr; simp [nodup,qnodup,inside,last],
            refine ⟨_,nodup_mem_last h.2, nodup_init h.2⟩, intro h1, exact h.1 (mem_init h1) }

    lemma         nodup_of_init : list.nodup (init l) -> last l ∉ init l -> nodup l
        := by { induction l with v v l hr; simp [init,last,nodup], push_neg, simp, intros h1 h2 h3 h4, split,
            { intro h, replace h := mem_init_last.mp h, cases h, contradiction, exact h3 h.symm },
            { exact hr h2 h4 } }

    lemma         qnodup_ne_nodup : qnodup l -> head l ≠ last l -> nodup l
        := by { cases l with v v l; simp [nodup,qnodup,last,inside],
            intros h1 h2 h3 h4, split, { intro h, cases mem_init_last.mp h; contradiction },
            { apply nodup_of_init h3 h2 } }
end end llist

structure llist' (V : Type) (x y : V) := (l : llist V) (hx : x = l.head) (hy : l.last = y)
instance llist'_to_llist {V : Type} {x y : V} : has_coe (llist' V x y) (llist V) := ⟨llist'.l⟩

namespace llist' section open llist
    parameters {V : Type} (adj : V -> V -> Prop)
    variables {x y z : V}

    def mem (v : V) (l : llist' V x y) := v ∈ l.l
    instance has_mem : has_mem V (llist' V x y) := ⟨mem⟩

    @[simp] lemma mem_simp {v l hx hy} : v ∈ (⟨l,hx,hy⟩ : llist' V x y) <-> v ∈ l
        := by { simp [(∈),mem] }

    def P    (v : V)                    : llist' V v v := ⟨P v,     rfl, rfl⟩
    def cons (v : V) (l : llist' V x y) : llist' V v y := ⟨L v l.l, rfl, l.hy⟩

    @[simp] lemma head   {l : llist' V x y}                     : l.l.head = x          := l.hx.symm
    @[simp] lemma last   {l : llist' V x y}                     : l.l.last = y          := l.hy

    lemma compat {l : llist' V x y} {l' : llist' V y z} : llist.compat l.l l'.l := by simp [compat]

    def concat {x y z : V} (l : llist' V x y) (l' : llist' V y z) : llist' V x z
        := ⟨llist.concat l.l l'.l, eq.trans l.hx (concat_head compat).symm, eq.trans concat_last l'.hy⟩

    @[simp] lemma concat_P {l : llist' V x y} {hx' hy'} : concat l ⟨llist.P y, hx', hy'⟩ = l
        := by { rcases l with ⟨l,hx,hy⟩, subst hx, subst hy, rw concat, simp }


    @[extensionality] lemma eq {l l' : llist' V x y} : l.l = l'.l -> l = l'
        := by { cases l, cases l', simp }
end end llist'
