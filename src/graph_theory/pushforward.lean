import combinatorics.simple_graph.basic combinatorics.simple_graph.connectivity data.set.basic
import graph_theory.to_mathlib
open function set classical

variables {V V' V'' : Type} {x y z : V} {x' y' z' : V'} {f : V → V'} {g : V' → V''}
variables {G G₁ G₂ : simple_graph V} {G' G'₁ G'₂ : simple_graph V'} {G'' : simple_graph V''}

namespace simple_graph
    def pull (f : V → V') (G' : simple_graph V') : simple_graph V :=
    {
        adj := G'.adj on f,
        symm := λ _ _ h, G'.symm h,
        loopless := λ _, G'.loopless _
    }

    namespace pull
        lemma comp : pull (g ∘ f) G'' = pull f (pull g G'') :=
        by { ext x y, exact iff.rfl }

        def to_iso (f : V ≃ V') (G' : simple_graph V') : pull f G' ≃g G' :=
        ⟨f,λ x y, iff.rfl⟩

        lemma from_iso (φ : G ≃g G') : pull φ G' = G :=
        by { ext x y, have := φ.map_rel_iff', exact this }

        lemma mono : monotone (pull f) :=
        by { intros G'₁ G'₂ h x' y', apply h }
    end pull

    -- TODO: this is an alternative definition for pull
    def pull' (f : V → V') (G' : simple_graph V') : simple_graph V :=
    {
        adj := λ x y, x ≠ y ∧ (f x = f y ∨ G'.adj (f x) (f y)),
        symm := λ x y ⟨h₁,h₂⟩, by { refine ⟨h₁.symm,_⟩, cases h₂, left, exact h₂.symm, right, exact h₂.symm },
        loopless := λ x, by { push_neg, intro, contradiction }
    }

    namespace pull'
        lemma comp : pull' (g ∘ f) G'' = pull' f (pull' g G'') :=
        begin
            ext x y, split,
            { rintros ⟨h₁,h₂⟩, refine ⟨h₁,_⟩, by_cases f x = f y,
                { left, exact h },
                { right, exact ⟨h,h₂⟩ } },
            { rintros ⟨h₁,h₂⟩, refine ⟨h₁,_⟩, cases h₂,
                { left, convert congr_arg g h₂ },
                { rcases h₂ with ⟨h₃,h₄⟩, cases h₄, left, exact h₄, right, exact h₄ } }
        end

        lemma iff_pull_of_inj (hf : injective f) : pull f G' = pull' f G' :=
        begin
            ext x y, split,
            { intro h₁, refine ⟨simple_graph.ne_of_adj _ h₁,_⟩, right, exact h₁ },
            { rintros ⟨h₁,h₂⟩, cases h₂, have := hf h₂, contradiction, exact h₂ }
        end

        def to_iso (f : V ≃ V') (G' : simple_graph V') : pull' f G' ≃g G' :=
        by { rewrite ← iff_pull_of_inj f.injective, apply pull.to_iso }

        lemma from_iso (φ : G ≃g G') : pull' φ G' = G :=
        by { rewrite ← iff_pull_of_inj φ.injective, apply pull.from_iso }

        lemma mono : monotone (pull' f) :=
        by { rintros G H h x y ⟨h₁,h₂⟩, refine ⟨h₁,_⟩, cases h₂, left, exact h₂, right, exact h h₂ }
    end pull'

    def push (f : V → V') (G : simple_graph V) : simple_graph V' :=
    {
        adj := λ x' y', x' ≠ y' ∧ ∃ x y : V, f x = x' ∧ f y = y' ∧ G.adj x y,
        symm := λ x' y' ⟨h₀,x,y,h₁,h₂,h₃⟩, ⟨h₀.symm,y,x,h₂,h₁,h₃.symm⟩,
        loopless := λ _ ⟨h₀,_⟩, h₀ rfl
    }

    namespace push
        @[simp] lemma push_id : push id G = G :=
        begin
            ext x y, split,
            { rintros ⟨-,x',y',rfl,rfl,h₂⟩, exact h₂ },
            { intro h, exact ⟨G.ne_of_adj h,x,y,rfl,rfl,h⟩ }
        end

        lemma adj (f : V → V') : G.adj x y → f x = f y ∨ (push f G).adj (f x) (f y) :=
        by { intro h₁, by_cases f x = f y, left, exact h, right, exact ⟨h,x,y,rfl,rfl,h₁⟩ }

        lemma comp : push (g ∘ f) G = push g (push f G) :=
        begin
            ext x'' y'', split,
            { rintro ⟨h₁,x,y,rfl,rfl,h₄⟩, exact ⟨h₁,f x,f y,rfl,rfl,ne_of_apply_ne g h₁,x,y,rfl,rfl,h₄⟩ },
            { rintro ⟨h₁,-,-,rfl,rfl,-,x,y,rfl,rfl,h₇⟩, exact ⟨h₁,x,y,rfl,rfl,h₇⟩ }
        end

        lemma left_inv (h : injective f) : left_inverse (pull f) (push f) :=
        begin
            intro G, ext x y, split,
            { rintro ⟨-,xx,yy,h₂,h₃,h₄⟩, rw [←h h₂,←h h₃], exact h₄ },
            { intro h₁, exact ⟨h.ne (G.ne_of_adj h₁),x,y,rfl,rfl,h₁⟩ }
        end

        lemma left_inv' (h : injective f) : left_inverse (pull' f) (push f) :=
        begin
            intro G, ext x y, split,
            { rintro ⟨h₁,h₂⟩, cases h₂, have := h h₂, contradiction, rcases h₂ with ⟨h₂,x',y',h₃,h₄,h₅⟩, rwa [←h h₃, ←h h₄] },
            { intro h₁, refine ⟨G.ne_of_adj h₁, _⟩, by_cases h₂ : f x = f y, left, exact h₂, right, refine ⟨h₂,x,y,rfl,rfl,h₁⟩ }
        end

        lemma right_inv (h : surjective f) : right_inverse (pull f) (push f) :=
        begin
            intro G', ext x' y', split,
            { rintro ⟨h₁,x,y,rfl,rfl,h₂⟩, exact h₂ },
            { intro h₁, cases h x' with x, cases h y' with y, substs x' y', exact ⟨G'.ne_of_adj h₁,x,y,rfl,rfl,h₁⟩ }
        end

        lemma right_inv' (h : surjective f) : right_inverse (pull' f) (push f) :=
        begin
            intro G', ext x' y', split,
            { rintro ⟨h₁,x,y,rfl,rfl,h₂,h₃⟩, cases h₃, contradiction, exact h₃ },
            { intro h₁, cases h x' with x, cases h y' with y, substs x' y', refine ⟨G'.ne_of_adj h₁,x,y,rfl,rfl, _⟩,
                refine ⟨_,_⟩, intro h₂, exact G'.ne_of_adj h₁ (congr_arg f h₂), right, exact h₁ }
        end

        def to_iso (f : V ≃ V') (G : simple_graph V) : G ≃g push f G :=
        begin
            convert ← pull.to_iso f _, apply left_inv f.left_inv.injective
        end

        lemma from_iso (φ : G ≃g G') : G' = push φ G :=
        begin
            convert ← congr_arg _ (pull.from_iso φ), apply right_inv φ.right_inv.surjective
        end

        lemma mono : monotone (push f) :=
        by { rintros G₁ G₂ h₁ x' y' ⟨h₂,x,y,rfl,rfl,h₃⟩, exact ⟨h₂,x,y,rfl,rfl,h₁ h₃⟩ }

        lemma le {φ : G →g G'} : push φ G ≤ G' :=
        by { rintros x' y' ⟨-,x,y,rfl,rfl,h₂⟩, exact φ.map_rel h₂ }
    end push

    def select (P : V → Prop) (G : simple_graph V) : simple_graph (subtype P) :=
    pull subtype.val G

    def level (f : V → V') (z : V') (G : simple_graph V) : simple_graph {x // f x = z}
    := select (λ x, f x = z) G

    namespace select
        variables {P : V → Prop} {P' : V' → Prop}

        lemma mono {P : V → Prop} : monotone (select P)
        := by { apply pull.mono }

        def map (f : V → V') (P' : V' → Prop) : {x // P' (f x)} → {x' // P' x'} :=
        subtype.map f (λ _, id)

        lemma level_comp (g_inj : injective g) {z : V'} : level (g ∘ f) (g z) G ≃g level f z G :=
        {
            to_fun := λ x, ⟨x.val, g_inj x.prop⟩,
            inv_fun := λ x, ⟨x.val, congr_arg g x.prop⟩,
            left_inv := λ x, by { simp only [subtype.val_eq_coe, subtype.coe_eta] },
            right_inv := λ x, by { simp only [subtype.val_eq_coe, subtype.coe_eta] },
            map_rel_iff' := λ x y, iff.rfl
        }

        lemma level_map {hz' : P' z'} : level (map f P') ⟨z',hz'⟩ (select (P' ∘ f) G) ≃g level f z' G :=
        begin
            refine ⟨⟨_,_,_,_⟩,_⟩,
            { rintro ⟨⟨x,p₁x⟩,p₂x⟩, simp [map,subtype.map] at p₂x, exact ⟨x,p₂x⟩ },
            { rintro ⟨x,px⟩, use x, rw px, exact hz', simp [map,subtype.map], exact px },
            { rintro ⟨⟨x,p₁x⟩,p₂x⟩, refl },
            { rintro ⟨x,px⟩, refl },
            { rintros ⟨⟨a,h₁a⟩,h₂a⟩ ⟨⟨b,h₁b⟩,h₂b⟩, simp [level,select,pull] }
        end

        lemma of_push : select P' (push f G) = push (map f P') (select (P' ∘ f) G) :=
        begin
            ext x' y', cases x' with x' hx', cases y' with y' hy',
            simp [select,pull,push,on_fun,map,subtype.ext_iff], intro h₁, split,
            { rintros ⟨x,rfl,y,rfl,h⟩, exact ⟨x,hx',y,hy',rfl,rfl,h⟩ },
            { rintros ⟨x,hx,y,hy,rfl,rfl,h⟩, refine ⟨x,rfl,y,rfl,h⟩ }
        end

        def push_walk (p : walk G x y) (hp : ∀ z ∈ p.support, P z) :
            walk (select P G) ⟨x, hp x (walk.start_mem_support p)⟩ ⟨y, hp y (walk.end_mem_support p)⟩ :=
        begin
            induction p with a a b c h₁ p ih, refl,
            have hp' : ∀ z ∈ p.support, P z := by { intros z hz, apply hp, right, exact hz },
            refine walk.cons _ (ih hp'), exact h₁
        end

        def pull_walk {x y} (p : walk (select P G) x y) : walk G x.val y.val :=
        by { induction p with a a b c h₁ p ih, refl, refine walk.cons h₁ ih }

        lemma pull_walk_spec {x y} (p : walk (select P G) x y) : ∀ z ∈ (pull_walk p).support, P z :=
        by { induction p with a a b c h₁ p ih,
            { intros z hz, cases hz, rw hz, exact a.prop, cases hz },
            { intros z hz, cases hz, rw hz, exact a.prop, exact ih z hz }}
    end select

    def embed (f : V → V') : simple_graph V → simple_graph (range f) :=
    select (range f) ∘ push f

    namespace embed
        -- TODO : computable version of this taking a left inverse of f?
        noncomputable def iso (f_inj : injective f) : G ≃g embed f G :=
        let φ : V → range f := λ x, ⟨f x, x, rfl⟩,
            ψ : range f → V := λ y, some y.prop in
        {
            to_fun := φ,
            inv_fun := ψ,
            left_inv := λ x, f_inj (some_spec (subtype.prop (φ x))),
            right_inv := λ y, subtype.ext (some_spec y.prop),
            map_rel_iff' := by {
                simp [φ,embed,push,select,pull,on_fun],
                simp_rw [subtype.coe_mk], intros a b, split,
                { rintro ⟨h₁,x,h₂,y,h₃,h₄⟩, rwa [←f_inj h₂,←f_inj h₃] },
                { intro h₁, exact ⟨f_inj.ne (G.ne_of_adj h₁),a,rfl,b,rfl,h₁⟩ }
            }
        }

        lemma le_select {f : G →g G'} (f_inj : injective f) : embed f G ≤ select (range f) G' :=
        select.mono push.le
    end embed
end simple_graph
