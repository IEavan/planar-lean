import tactic group_theory.subgroup
import graph_theory.path graph_theory.metric topology.metric_space.lipschitz

namespace simple_graph
    namespace cayley
        structure genset (G : Type) [group G] :=
            (els : finset G)
            (sym : ∀ {s : G}, s ∈ els -> s⁻¹ ∈ els)
            (gen : subgroup.closure (coe els) = (⊤ : subgroup G))
            (nem : els.nonempty)
            (irr : (1:G) ∉ els)

        variables {G : Type} [group G] (S : genset G) (a : G) {x y z : G}

        instance : has_coe (genset G) (finset G) := ⟨λ S, S.els⟩
        instance : has_mem G (genset G) := ⟨λ a s, a ∈ s.els⟩

        def adj (x y : G) := x ≠ y ∧ x⁻¹ * y ∈ S

        @[simp] lemma cancel {x y a : G} : (a * x)⁻¹ * (a * y) = x⁻¹ * y
            := by { simp [mul_assoc] }

        lemma inv_prod {x y : G} : (x⁻¹ * y)⁻¹ = y⁻¹ * x
            := by { simp }

        lemma shift_adj {a x y : G} : adj S x y -> adj S (a*x) (a*y)
        := begin
            rintro ⟨h1,h2⟩, split,
            { exact (mul_ne_mul_right a).mpr h1 },
            { rw cancel, assumption }
        end

        @[symm] lemma adj_symm {x y} : adj S x y -> adj S y x
        := begin
            rintro ⟨h1,h2⟩, refine ⟨h1.symm,_⟩,
            rw <-inv_prod, exact S.sym h2
        end

        def Cay (S : genset G) : simple_graph G := ⟨
            adj S,
            by { apply adj_symm },
            by { intro x, unfold adj, tauto }
        ⟩

        -- instance : group (Cay S) := by { exact _inst_1 }
        -- instance : simple_graph (Cay S) := { adj := adj S, sym := @adj_symm _ _ S }

        def shift_llist : llist G -> llist G := llist.map (λ v, a * v)

        lemma shift_is_path {l : llist G} (h : llist.is_path (adj S) l) : llist.is_path (adj S) (shift_llist a l)
            := by { induction l with v v l hr, trivial,
                refine ⟨_, hr h.2⟩, rw [llist.head_map], exact shift_adj S h.1 }

        def shift_path (p : path (Cay S) x y) : path (Cay S) (a*x : G) (a*y : G)
            := { l := @shift_llist _ _ a p.l,
                hx := by { rw [shift_llist,llist.head_map,p.hx] },
                hy := by { rw [shift_llist,llist.last_map,p.hy] },
                adj := shift_is_path _ _ p.adj }

        lemma shift : linked (Cay S) x y -> linked (Cay S) (a*x : G) (a*y : G)
            := by { intro h, induction h with b c hxb hbc hr, refl,
                exact linked.tail hr (shift_adj S hbc) }

        lemma inv : linked (Cay S) (1:G) x -> linked (Cay S) (1:G) (x⁻¹:G)
            := by { intro h, symmetry, convert shift S x⁻¹ h; simp }

        lemma linked_mp : linked (Cay S) (1:G) x
        := begin
            have h : x ∈ subgroup.closure (coe S.els) := by { rw S.gen, trivial },
            apply subgroup.closure_induction,
            { exact h, },
            { intros, apply linked.edge,
                split, { intro h, rw <-h at H, exact S.irr H },
                change 1⁻¹ * x_1 ∈ S, rwa [one_inv,one_mul] },
            { refl },
            { intros u v h1 h2, refine linked.trans h1 _, convert shift _ u h2, rw mul_one, },
            { intros, apply inv, assumption },
        end

        theorem connected : connected (Cay S)
            := by { suffices : ∀ x, linked (Cay S) (1:G) x,
                    { intros x y, transitivity (1:G), symmetry, apply this, apply this },
                intro, apply linked_mp }

        instance : connected_graph (Cay S) := ⟨connected S⟩

        noncomputable def word_dist : G -> G -> ℕ := simple_graph.dist (Cay S)

        lemma covariant : word_dist S (a*x) (a*y) = word_dist S x y
            := by { unfold word_dist simple_graph.dist, congr' 1, funext ℓ, rw [eq_iff_iff],
                let dists : G -> G -> set ℕ := dists (Cay S),
                have h2 : ∀ x y a ℓ, dists x y ℓ -> dists (a*x) (a*y) ℓ
                    := by { intros x y a ℓ h, cases h with p, use ⟨shift_path S a p, h_h ▸ llist.size_map⟩ },
                exact ⟨λ h, inv_mul_cancel_left a x ▸ inv_mul_cancel_left a y ▸ h2 (a*x) (a*y) a⁻¹ ℓ h,
                    h2 x y a ℓ⟩ }
    end cayley

    namespace cayley
        variables {G : Type} [group G] (S1 S2 : genset G)
        open finset

        lemma lipschitz : ∃ K : ℕ, ∀ x y : G, word_dist S2 x y <= K * word_dist S1 x y
            := by { obtain K := max_of_nonempty (nonempty.image S1.nem _), cases K, use K_w,
                intros x y, obtain ⟨⟨⟨l,rfl,rfl⟩,hp⟩,h⟩ := simple_graph.shortest_path (Cay S1) x y,
                unfold word_dist, rw <-h, clear h, induction l; intros, simp,
                { let z : G := llist.head l_ᾰ_1,
                    transitivity word_dist S2 l_ᾰ z + word_dist S2 z l_ᾰ_1.last, { exact simple_graph.dist_triangle _ },
                    rw [path.size,llist.size,mul_add,add_comm,mul_one],
                    apply add_le_add (l_ih hp.2), rw [<-(covariant S2 l_ᾰ⁻¹),inv_mul_self],
                    refine le_max_of_mem (mem_image_of_mem _ _) K_h, exact hp.1.2 } }

        -- theorem bilipschitz : don't know how to state it
    end cayley
end simple_graph
