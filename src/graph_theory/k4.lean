import tactic
import combinatorics.simple_graph.basic
import graph_theory.planar

namespace simple_graph

def K4 := complete_graph (finset.range 4)

def K4_to_plane (v : finset.range 4) : (ℤ × ℤ) :=
begin
  cases v with v' hv',
  exact if v'=0 then (0,0) else
        if v'=1 then (0,1) else
        if v'=2 then (0,2) else (1,1),
end

lemma out_of_range (x : ℕ) : x.succ.succ.succ.succ ∉ finset.range 4 :=
begin
  intro h,
  rw finset.mem_range at h,
  change x.succ.succ.succ.succ with x + 4 at h, 
  linarith,
end

def K4_dart_to_path (e : K4.dart) : plane.walk (K4_to_plane e.fst) (K4_to_plane e.snd) :=
begin
  cases e.fst with x hx,
  cases e.snd with y hy,

  iterate 4 { any_goals { cases x, norm_num, }, },
  iterate 4 { any_goals { cases y, norm_num, }, },

  any_goals {
    exfalso, 
    { apply out_of_range x, assumption, } <|> { apply out_of_range y, assumption, }
  },

  all_goals { 
    rw [K4_to_plane, K4_to_plane],
    simp only [nat.one_ne_zero,
     zero_eq_bit0,
     bit0_eq_zero,
     nat.bit1_ne_bit0,
     nat.bit1_eq_one,
     if_true,
     eq_self_iff_true,
     nat.zero_ne_one,
     if_false,
     nat.succ_succ_ne_one,
     nat.bit1_ne_zero],
  },

  any_goals { exact walk.cons (by rw [plane, cartesian_product, Z]; norm_num) walk.nil, },
  
  have step1 : plane.adj (0,0) (-1,0) := by rw [plane, cartesian_product, Z]; norm_num,
  have step2 : plane.adj (-1,0) (-1,1) := by rw [plane, cartesian_product, Z]; norm_num,
  have step3 : plane.adj (-1,1) (-1,2) := by rw [plane, cartesian_product, Z]; norm_num,
  have step4 : plane.adj (-1,2) (0,2) := by rw [plane, cartesian_product, Z]; norm_num,
  exact walk.cons step1 (walk.cons step2 (walk.cons step3 (walk.cons step4 walk.nil))),

  have step1 : plane.adj (0,0) (1,0) := by rw [plane, cartesian_product, Z]; norm_num,
  have step2 : plane.adj (1,0) (1,1) := by rw [plane, cartesian_product, Z]; norm_num,
  exact walk.cons step1 (walk.cons step2 walk.nil),

  have step1 : plane.adj (0,2) (-1,2) := by rw [plane, cartesian_product, Z]; norm_num,
  have step2 : plane.adj (-1,2) (-1,1) := by rw [plane, cartesian_product, Z]; norm_num,
  have step3 : plane.adj (-1,1) (-1,0) := by rw [plane, cartesian_product, Z]; norm_num,
  have step4 : plane.adj (-1,0) (0,0) := by rw [plane, cartesian_product, Z]; norm_num,
  exact walk.cons step1 (walk.cons step2 (walk.cons step3 (walk.cons step4 walk.nil))),
  
  have step1 : plane.adj (0,2) (1,2) := by rw [plane, cartesian_product, Z]; norm_num,
  have step2 : plane.adj (1,2) (1,1) := by rw [plane, cartesian_product, Z]; norm_num,
  exact walk.cons step1 (walk.cons step2 walk.nil),
  
  have step1 : plane.adj (1,1) (1,0) := by rw [plane, cartesian_product, Z]; norm_num,
  have step2 : plane.adj (1,0) (0,0) := by rw [plane, cartesian_product, Z]; norm_num,
  exact walk.cons step1 (walk.cons step2 walk.nil),
  
  have step1 : plane.adj (1,1) (1,2) := by rw [plane, cartesian_product, Z]; norm_num,
  have step2 : plane.adj (1,2) (0,2) := by rw [plane, cartesian_product, Z]; norm_num,
  exact walk.cons step1 (walk.cons step2 walk.nil),
end

lemma paths_support_nodup : ∀ e : K4.dart, (K4_dart_to_path e).support.nodup :=
begin
  rintro ⟨⟨e1, e2⟩, adj⟩,
  fin_cases e1; fin_cases e2,
  all_goals { dec_trivial, },
end

lemma no_overlap (e e' : K4.dart)
                 (z : ℤ × ℤ)
                 (hz1 : z ∈ (K4_dart_to_path e).support)
                 (hz2 : z ∈ (K4_dart_to_path e').support) : (e.edge = e'.edge ∨ ∃ (x : ↥(finset.range 4)), z = K4_to_plane x) :=
begin
  rcases e with ⟨⟨ a1, a2 ⟩, adj_a⟩,
  rcases e' with ⟨⟨ b1, b2 ⟩, adj_b⟩,

  fin_cases a1; fin_cases a2,

  all_goals {
    fin_cases b1; fin_cases b2,

    any_goals {
      apply or.inl,
      trivial <|> exact sym2.eq_swap,
    },

    all_goals { apply or.inr, },

    all_goals {
      iterate {erw [list.mem_cons_iff] at hz1},
      iterate {erw [list.mem_cons_iff] at hz2},
      rw list.mem_nil_iff at hz1 hz2,
      cases_matching* [_ ∨ _],
      any_goals {
        exfalso,
        assumption,
      },
      try { any_goals {
          exfalso,
          let p := prod.mk.inj (eq.trans (eq.symm hz1) hz2),
          linarith [p.left, p.right],
      }, },
      try { any_goals {
        use ⟨ 0, dec_trivial ⟩,
        assumption,
      }, },
      try { any_goals {
        use ⟨ 1, dec_trivial ⟩,
        assumption,
      }, },
      try { any_goals {
        use ⟨ 2, dec_trivial ⟩,
        assumption,
      }, },
      try { any_goals {
        use ⟨ 3, dec_trivial ⟩,
        assumption,
      }, },
      done,
    },
  },
end

example : K4.is_planar :=
begin
  split,
  {
    refine nonempty.intro (path_embedding.mk _ _ _ _ _ _),
    exact ⟨ K4_to_plane, (by dec_trivial!) ⟩,
    exact K4_dart_to_path,
    focus {
      exact paths_support_nodup,
    },
    focus {
      rintro ⟨⟨e1, e2⟩, adj⟩,
      fin_cases e1; fin_cases e2,
      all_goals { dec_trivial, },
    },
    focus {
      rintro ⟨⟨e1, e2⟩, adj⟩,
      fin_cases e1; fin_cases e2,
      all_goals { dec_trivial, },
    },
    exact no_overlap,
  },
  split,
  {
    intros x y,
    by_cases h : (x=y),
    rwa h,
    exact nonempty.intro (walk.cons (h) walk.nil),
  },
  {
    apply (finset.nonempty_coe_sort (finset.range 4)).mpr,
    apply (@finset.nonempty_range_iff 4).mpr,
    norm_num,
  }
end

end simple_graph
