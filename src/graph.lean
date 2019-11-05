import tactic
import llist
open function

structure graph := (V : Type) (adj : V -> V -> Prop) (sym : symmetric adj)
instance graph_to_V : has_coe_to_sort graph := {S := _, coe := λ G, G.V}

namespace graph section
    structure hom  (G G' : graph) := (f : G -> G') (hom : ∀ x y, G.adj x y -> G'.adj (f x) (f y))

    structure iso (G G' : graph) extends hom G G' := (bij : bijective f) (iso : ∀ x y, G.adj x y <-> G'.adj (f x) (f y))

    structure subgraph (G' : graph) := (G : graph) (f : hom G G') (inj : injective f.f)
end end graph

def edge (G : graph) := { e : G×G // G.adj e.1 e.2 }

namespace edge section
    def flip  {G} (e : edge G)    : edge G := ⟨⟨_,_⟩, G.sym e.2⟩
    def same  {G} (e e' : edge G) : Prop   := e' = e ∨ e' = flip e
    def nsame {G} (e e' : edge G) : Prop   := ¬ same e e'
end end edge

structure path  (G : graph) (x y) extends llist' G x y := (adj : llist.is_path G.adj l)

namespace path section
    parameters {G : graph}
    variables {x y z : G}

    instance : has_coe (path G x y) (llist' G x y) := ⟨path.to_llist'⟩

    @[extensionality] lemma eq {p p' : path G x y} : p.to_llist' = p'.to_llist' -> p = p'
        := by { cases p, cases p', simp }

    def mem (v : G) (p : path G x y) := llist.mem v p.l
    instance has_mem : has_mem G (path G x y) := ⟨mem⟩

    def P (v : G) : path G v v := ⟨llist'.P v, trivial⟩

    def cons (v : G) (p : path G x y) (h : G.adj v x) : path G v y
        := ⟨llist'.cons v p.1, by { simp [llist'.cons,llist.is_path], exact ⟨h,p.2⟩ }⟩

    def linked     (x y : G)        : Prop := nonempty (path G x y)
    def connected                   : Prop := ∀ x y, linked x y
    def simple     (p : path G x y) : Prop := llist.nodup p.l

    def rev (p : path G x y) : path G y x
        := { l := llist.rev p.l, hx := by simp, hy := by simp, adj := (llist.rev_is_path G.adj G.sym).mpr p.adj }

    def concat (p : path G x y) (p' : path G y z) : path G x z
        := { to_llist' := llist'.concat p.to_llist' p'.to_llist',
            adj := by { apply (llist.concat_path G.adj llist'.compat).mpr, exact ⟨p.adj,p'.adj⟩ } }

    def edges_aux : Π (l : llist G) (h : llist.is_path G.adj l), list (edge G)
        | (llist.P v)   _ := []
        | (llist.L v l) h := ⟨⟨_,_⟩,h.1⟩ :: edges_aux l h.2

    def edges (p : path G x y) : list (edge G) := edges_aux p.l p.adj

    lemma mem_edges_aux {l h} {e : edge G} : e ∈ edges_aux l h -> e.1.1 ∈ l ∧ e.1.2 ∈ l
        := by { induction l with v v l hr; intro e; cases e with he he,
            { subst he, simp },
            { replace hr := hr he, exact ⟨or.inr hr.1, or.inr hr.2⟩ } }

    lemma mem_edges {p : path G x y} {e : edge G} : e ∈ p.edges -> e.1.1 ∈ p.l ∧ e.1.2 ∈ p.l
        := mem_edges_aux

    lemma edges_simple {l h} {hs : llist.nodup l} : list.pairwise edge.nsame (edges_aux l h)
        := by { induction l with v v l hr; rw edges_aux, exact list.pairwise.nil,
            simp, cases hs with h1 h2, cases h with h3 h4, refine ⟨_, @hr h4 h2⟩,
            intros e he, have h5 := @mem_edges_aux G l h4 e he,
            rw [edge.nsame, edge.same], push_neg, split; intro h6; subst h6,
            exact h1 h5.1, exact h1 h5.2 }
end end path

structure spath (G : graph) (x y) extends path   G x y := (simple : path.simple to_path)

namespace spath section
    parameters {G : graph}
    variables {x y z : G}

    instance : has_coe (spath G x y) (path G x y) := ⟨spath.to_path⟩

    lemma eq {p p' : spath G x y} : p.to_path = p'.to_path -> p = p'
        := by { cases p, cases p', simp }

    def rev (p : spath G x y) : spath G y x
        := { to_path := path.rev p.to_path, simple := llist.rev_nodup.mpr p.simple }

    lemma edges_simple {p : spath G x y} : list.pairwise edge.nsame p.to_path.edges
        := by { rw path.edges, apply path.edges_simple, exact p.simple }
end end spath

section embedding
    structure graph_embedding (G G' : graph) :=
        (f        : G -> G')
        (df       : Π (e : edge G), spath G' (f e.1.1) (f e.1.2))
        --
        (inj      : injective f)
        (sym      : ∀ e : edge G, df e.flip = (df e).rev)
        --
        (endpoint : ∀ e x, f x ∈ (df e).l -> x = e.1.1 ∨ x = e.1.2)
        (disjoint : ∀ e e' z, z ∈ (df e).l ∧ z ∈ (df e').l -> edge.same e e' ∨ ∃ x, z = f x)
        (inside   : ∀ e x, f x ∉ (df e).l.inside)

    def embeds_into (G G' : graph) := nonempty (graph_embedding G G')

    variables {G G' G'' : graph} {x y z : G} (F : graph_embedding G G')

    def follow_llist : Π (l : llist G) (h : llist.is_path G.adj l), llist G'
        | (llist.P v)   _ := llist.P (F.f v)
        | (llist.L v l) h := llist.concat (F.df ⟨(_,_),h.1⟩) (follow_llist l h.2)

    @[simp] lemma follow_head {l h} : llist.head (follow_llist F l h) = F.f l.head
        := by { induction l with v v l hr; rw follow_llist,
            { refl },
            { let e : edge G := ⟨(_,_),h.1⟩, replace hr := @hr h.2,
                rw llist.concat_head, simp, exact (F.df e).hx.symm,
                simp [llist.compat], rw hr, exact (F.df e).hy } }

    @[simp] lemma follow_last {l h} : llist.last (follow_llist F l h) = F.f l.last
        := by { induction l with v v l hr; rw follow_llist,
            { refl },
            { rw llist.concat_last, exact @hr h.2 } }

    lemma follow_path {l h} : llist.is_path G'.adj (follow_llist F l h)
        := by { induction l with v v l hr; rw [follow_llist],
            { simp [llist.is_path] },
            { apply (llist.concat_path G'.adj _).mpr, split,
                refine (F.df _).adj, exact @hr h.2,
                simp, let e : edge G := ⟨(_,_),h.1⟩, exact (F.df e).hy } }

    def follow (p : path G x y) : path G' (F.f x) (F.f y)
        := { l := follow_llist F p.l p.adj,
            hx := by simp,
            hy := by simp,
            adj := follow_path F }

    @[simp] lemma follow_nil : follow F (path.P x) = path.P (F.f x)
        := by { simp [follow,path.P,llist'.P,follow_llist] }

    lemma follow_edges {z : G'} {l : llist G} {h} {hz : l ≠ llist.P l.head} :
            z ∈ follow_llist F l h <-> ∃ e ∈ path.edges_aux l h, z ∈ (F.df e).l
        := by { induction l with v v l hr,
            { simp at hz, contradiction },
            { simp [llist.is_path] at h, replace hr := @hr h.2, clear hz,
                have compat : (F.df ⟨(_,_),h.1⟩).l.last = F.f l.head, by simp,
                simp [follow_llist,path.edges_aux],
                rw llist.mem_concat, swap, rw llist.compat, convert compat, rw follow_head, split,
                { intro h1, cases h1 with h1 h1,
                    { use ⟨(_,_),h.1⟩, simpa },
                    { cases l with w w l,
                        { simp [follow_llist] at h1, use ⟨(_,_),h.1⟩, simp, convert llist.mem_last, simpa },
                        { rcases hr.mp h1 with ⟨e,⟨he1,he2⟩⟩, use e, finish, simp } } },
                { rintros ⟨e,he1,he2⟩, cases he1 with he1 he1,
                    { subst he1, left, assumption },
                    { cases l with w w l,
                        { cases he1 },
                        { right, apply hr.mpr, use e, use he1, exact he2, simp } } } } }

    example {l h} {hs : llist.nodup l} : llist.nodup (follow_llist F l h)
        := by {
            induction l with v v l hr, simp [follow_llist],
            let es : list (edge G) := path.edges_aux (llist.L v l) h,
            have h0 : list.pairwise edge.nsame es, by { apply path.edges_simple, exact hs },
            rw [llist.is_path] at h, cases h with h1 h2,
            rw [llist.nodup] at hs, cases hs with h3 h4,
            replace hr := @hr h2 h4,
            let e : edge G := ⟨(_,_),h1⟩,
            have h5 : llist.compat (F.df e).l (follow_llist F l h2), by { simp },
            have h55 := classical.em (l = llist.P l.head), cases h55 with h55 h55,
            {
                conv { congr, congr, skip, congr, skip, rw h55 }, simp [follow_llist],
                rw llist.concat_nil, exact (F.df _).simple, convert h5, rw follow_head
            },
            rw follow_llist, apply (llist.concat_nodup h5).mpr,
            refine ⟨(F.df _).simple, hr, _⟩, rintros x ⟨h6,h7⟩,
            obtain ⟨e',h8,h9⟩ : ∃ e' ∈ path.edges_aux l h2, x ∈ (F.df e').l,
                by { apply (follow_edges F).mp h7, exact h55 },
            have h10 : edge.nsame e e', by { cases h0, exact h0_a_1 e' h8 },
            obtain ⟨u, h11⟩ : ∃ u : G, x = F.f u, by { cases F.disjoint e e' x ⟨h6,h9⟩ with h h, cases h10 h, exact h },
            subst h11, rw follow_head, apply congr_arg,
            have h12 := F.endpoint e u h6, simp at h12, cases h12, swap, exact h12,
            suffices : u ∈ l, by { rw h12 at this, contradiction },
            cases path.mem_edges_aux h8 with h13 h14,
            have h15 := F.endpoint e' u h9, cases h15 with h15 h15; rw h15; assumption
        }

    lemma follow_simple {p : spath G x y} : path.simple (follow F p.to_path)
        := by {
            let sp0 := p,
            rcases p with ⟨⟨⟨l,hx,hy⟩,h⟩,hs⟩, revert x y h hs, induction l with v v l hr; intros; simp at *,

            let p0  : path G x y      := sp0.to_path,
            let es  : list (edge G)   := path.edges p0,
            let e   : edge G          := ⟨(v,l.head), h.1⟩,
            let p   : path G l.head y := ⟨⟨l,rfl,hy⟩,h.2⟩,
            let p₁  : spath G' _ _    := F.df e,

            rw llist.head at hx, subst hx, rw llist.last at hy, subst hy,
            cases l with w w l, { rw follow, rw path.simple, simp [follow_llist], rw llist.concat_nil,
                                    exact (F.df _).simple, exact (F.df _).hy },
            replace hr := hr rfl hy h.2 hs.2, simp at hr,

            have step2 : list.pairwise edge.nsame es,                   by { exact spath.edges_simple },
            suffices   : llist.nodup (path.concat p₁.1 (follow F p)).l, by { convert this },
            apply (llist.concat_nodup llist'.compat).mpr, simp,
            refine ⟨p₁.simple, hr, _⟩, rintros z h1 h2,
            obtain ⟨e',h3,h4⟩ : ∃ e' ∈ p.edges, z ∈ (F.df e').l,        by { apply (follow_edges F).mp h2, simp },
            have step4 : ¬ edge.same e e',                              by { cases step2, exact step2_a_1 e' h3 },
            obtain ⟨x₀, zfx⟩ : ∃ x₀ : G, z = F.f x₀,                    by { cases F.disjoint e e' z ⟨h1,h4⟩ with h h,
                                                                            exact absurd h step4, exact h },
            subst zfx, apply congr_arg,
            have h5 := F.endpoint e x₀ h1, simp at h5,
            cases h5, swap, exact h5,
            suffices : x₀ ∈ llist.L w l,                                by { cases hs, subst h5, contradiction },
            have h6 := F.endpoint e' x₀ h4,
            have h7 := path.mem_edges h3,
            cases h6 with h6 h6, { rw h6, exact h7.1 }, { rw h6, exact h7.2 }
        }

    -- lemma follow_cons {v : G} {p : path G x y} {h : G.adj v x} :
    --         follow F (path.cons v p h) = path.concat (F.df ⟨(v,x),h⟩).1 (follow F p)
    --     := by { simp [path.cons,llist'.cons,follow], congr; simp }

    -- @[simp] lemma follow_concat {p : path G x y} {p' : path G y z} :
    --         follow F (path.concat p p') = path.concat (follow F p) (follow F p')
    --     := by { rcases p with ⟨⟨l,hx,hy⟩,hp⟩, revert x y, induction l with v v l hr; intros,
    --         { simp [path.concat,llist'.concat,llist.concat,follow,follow_aux],
                    -- ext, simp, convert rfl; subst hx; subst hy; simp },
    --         {
    --             simp [llist.is_path] at hp,
    --             have h1 := @path.concat_cons G l.head y z v ⟨⟨l,rfl,hy⟩,hp.2⟩ p' hp.1,
    --             simp [path.cons,llist'.cons] at h1, replace h1 := congr_arg (follow F) h1,
    --         }
    --     }

    @[simp] def sfollow (p : spath G x y) : spath G' (F.f x) (F.f y) := ⟨follow F p.to_path, follow_simple F⟩

    @[simp] lemma sfollow_rev (p : spath G x y) : sfollow F p.rev = (sfollow F p).rev
        := by { sorry }

    def comp (F : graph_embedding G G') (F' : graph_embedding G' G'') : (graph_embedding G G'') := {
        f := F'.f ∘ F.f,
        df := λ e, sfollow F' (F.df e),
        --
        inj := injective_comp F'.inj F.inj,
        sym := sorry,
        --
        endpoint := sorry,
        disjoint := sorry,
        inside := sorry
    }

    theorem embed_trans : transitive embeds_into := sorry
end embedding
