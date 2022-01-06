import tactic data.finset.lattice data.set.basic
import graph_theory.path graph_theory.metric topology.metric_space.lipschitz

namespace simple_graph
    namespace cayley
        open mypath walk

        structure genset (G : Type) [group G] :=
            (els : finset G)
            (sym : ∀ {s : G}, s ∈ els -> s⁻¹ ∈ els)
            (gen : subgroup.closure (coe els) = (⊤ : subgroup G))
            (nem : els.nonempty)
            (irr : (1:G) ∉ els)

        variables {G : Type} [group G] (S : genset G) (a : G) {x y z : G}

        instance : has_mem G (genset G) := ⟨λ a s, a ∈ s.els⟩

        def adj (x y : G) := x ≠ y ∧ x⁻¹ * y ∈ S

        @[simp] lemma cancel : (a * x)⁻¹ * (a * y) = x⁻¹ * y := by group

        lemma shift_adj : adj S x y -> adj S (a*x) (a*y)
            := by { rintro ⟨h1,h2⟩, refine ⟨(mul_ne_mul_right a).mpr h1,_⟩, rw cancel, exact h2 }

        @[symm] lemma adj_symm (x y) : adj S x y -> adj S y x
            := by { rintro ⟨h1,h2⟩, refine ⟨h1.symm,_⟩, convert S.sym h2, group }

        def Cay (S : genset G) : simple_graph G := ⟨adj S, adj_symm S, (λ x, not_and.mpr (λ h1 h2, h1 rfl ))⟩

        @[simp] def shift_path : Π {x y : G}, walk (Cay S) x y -> walk (Cay S) (a*x : G) (a*y : G)
            | _ _ nil        := nil
            | _ _ (cons h p) := walk.cons (shift_adj S a h) (shift_path p)

        @[simp] lemma size_shift_path (p : walk (Cay S) x y) : length (shift_path S a p) = length p
            := by { induction p, refl, simpa }

        lemma shift : linked (Cay S) x y -> linked (Cay S) (a*x : G) (a*y : G)
            := by { intro h, cases h with p, use shift_path S _ p }

        lemma inv : linked (Cay S) (1:G) x -> linked (Cay S) (1:G) (x⁻¹:G)
            := by { intro h, symmetry, convert shift S x⁻¹ h; group }

        lemma linked_mp : linked (Cay S) (1:G) x
            := by { apply subgroup.closure_induction,
                { rw S.gen, trivial },
                { intros, have := linked.step, apply this, split,
                    { intro h, rw <-h at H, exact S.irr H },
                    { convert H, group } },
                { refl },
                { intros u v h1 h2, refine linked.trans h1 _, convert shift _ u h2, group },
                { intros y h, apply inv, exact h },
            }

        theorem connected : connected (Cay S)
            := by { intros x y, transitivity (1:G), symmetry, apply linked_mp, apply linked_mp }

        instance : connected_graph (Cay S) := ⟨connected S⟩

        noncomputable def word_dist : G -> G -> ℕ := (Cay S).dist

        lemma covariant : (Cay S).dist (a*x) (a*y) = (Cay S).dist x y
            := by { unfold simple_graph.dist, congr' 1, funext ℓ, rw [eq_iff_iff],
                let dists := dists (Cay S),
                have h2 : ∀ x y a ℓ, ℓ ∈ dists x y -> ℓ ∈ dists (a*x) (a*y)
                    := by { intros x y a ℓ h, cases h with p, use shift_path S a p, simpa },
                exact ⟨λ h, inv_mul_cancel_left a x ▸ inv_mul_cancel_left a y ▸ h2 (a*x) (a*y) a⁻¹ ℓ h,
                    h2 x y a ℓ⟩ }
    end cayley

    namespace cayley
        variables {G : Type} [group G] (S1 S2 : genset G)
        open finset

        lemma lipschitz : ∃ K : ℕ, ∀ x y : G, (Cay S2).dist x y <= K * (Cay S1).dist x y
            := begin
                set Δ := finset.image ((Cay S2).dist 1) S1.els,
                have : Δ.nonempty := finset.nonempty.image S1.nem ((Cay S2).dist 1),
                obtain K := finset.max_of_nonempty this, cases K, use K_w,
                intros x y, obtain ⟨p,hp⟩ := simple_graph.shortest_path (Cay S1) x y,
                rw <-hp, clear hp, induction p with u u v w h p ih, simp,
                transitivity (Cay S2).dist u v + (Cay S2).dist v w, apply simple_graph.dist_triangle,
                dsimp, rw [mul_add,mul_one,add_comm], apply add_le_add ih,
                suffices : (Cay S2).dist u v ∈ Δ, by exact finset.le_max_of_mem this K_h,
                simp, use u⁻¹ * v, split, exact h.2, convert covariant S2 u⁻¹, group
            end
    end cayley
end simple_graph
