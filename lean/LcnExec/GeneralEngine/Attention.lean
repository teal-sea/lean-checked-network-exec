import LcnExec.GeneralEngine.Softmax

/-!
# Total correctness of `general_engine.head_scores_at`

The causal attention scores of head `h` of layer `l` at position `p` are exactly the
model's `GeneralModel.headScoresAt`, within the frozen score envelope, for every
causal stream bounded by the embedding envelope.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace LcnExec.GeneralEngine

/-- The model reads layer `l` of the runtime weights as the mapped layer. -/
theorem model_layer_eq (W : general_engine.Weights) (l : Usize) (hl : l.val < 2) :
    GeneralModel.layer (toGeneralModel W) l.val =
      toLayerModel (W.layers.val[l.val]'(by simp; omega)) := by
  simp only [GeneralModel.layer, toGeneralModel]
  rw [project_nth_eq _ _ _ (by simp; omega)]
  simp

/-- Reading head `h` of a translated head tensor gives the mapped matrix. -/
theorem model_nth_map (xs : List (Array (Array I8 32#usize) 128#usize)) (h : Usize)
    (hh : h.val < xs.length) :
    GeneralModel.nth []
      (xs.map (fun mat => mat.val.map (fun row => row.val.map (·.val)))) h.val =
      (xs[h.val]'hh).val.map (fun row => row.val.map (·.val)) := by
  rw [project_nth_eq _ _ _ (by simp; omega)]
  simp

theorem head_scores_at_spec (W : general_engine.Weights) (hW : LoadBounds W)
    (l h : Usize) (hl : l.val < 2) (hh : h.val < 4)
    (x : Array (Array I64 128#usize) 32#usize) (p : Usize) (hp : p.val < 32)
    (hxb : streams x) :
    general_engine.head_scores_at W l h x p ⦃ r =>
      (ints r).take (p.val + 1) =
        GeneralModel.headScoresAt (toGeneralModel W) l.val h.val p.val (ints2 x) ∧
      Bounded Envelope.score r ⦄ := by
  have hbe : 0 ≤ Envelope.embedding := by simp only [Envelope.embedding]; norm_num
  have hqenv : 128 * Envelope.embedding * 5 ≤ 1000000 := by
    simp only [Envelope.embedding]; norm_num
  have hkenv : 128 * Envelope.embedding * 22 ≤ 1000000 := by
    simp only [Envelope.embedding]; norm_num
  have hscenv : (32 : Int) * ((128 * Envelope.embedding * 5) *
      (128 * Envelope.embedding * 22)) ≤ Envelope.score := by
    simp only [Envelope.embedding, Envelope.score]; norm_num
  have hqenv2 : 128 * Envelope.embedding * 5 ≤ Envelope.value := by
    simp only [Envelope.embedding, Envelope.value]; norm_num
  have hkenv2 : 128 * Envelope.embedding * 22 ≤ Envelope.value := by
    simp only [Envelope.embedding, Envelope.value]; norm_num
  have hrowp : Bounded Envelope.embedding (x.val[p.val]'(by simpa using hp)) :=
    hxb _ (List.getElem_mem _)
  have hL := layerBounds hW l hl
  unfold general_engine.head_scores_at
  step with row_at_spec x p hp Envelope.embedding hbe hrowp as ⟨rowp, hrowpe, hrowpb⟩
  step as ⟨lw, hlw⟩
  subst hlw
  step as ⟨wqh, hwqh⟩
  have hwqmat : MatrixBound 5 wqh := by
    have hmem : wqh ∈ (W.layers.val[l.val]'(by simp; omega)).wq.val := by
      rw [hwqh]
      exact List.getElem_mem (by simp; omega)
    exact hL.wq _ hmem
  step with project_spec rowp wqh Envelope.embedding 5 hbe (by norm_num) hrowpb hwqmat
    hqenv2 as ⟨q, hqe, hqb⟩
  have hqsmall : Small q := by
    intro v hv
    have hbb := hqb v hv
    constructor <;> omega
  apply loop.spec_decr_nat
    (measure := fun (st : Array I64 32#usize × Usize) => p.val + 1 - st.2.val)
    (inv := fun (st : Array I64 32#usize × Usize) =>
      st.2.val ≤ p.val + 1 ∧ Bounded Envelope.score st.1 ∧
      ∀ (j : Nat) (hj : j < st.2.val) (hj32 : j < 32),
        (ints st.1)[j]'(by rw [ints_length32]; exact hj32) =
          GeneralModel.keyScore (toGeneralModel W) l.val h.val
            (GeneralModel.rowAt (ints2 x) p.val) (GeneralModel.rowAt (ints2 x) j))
  · rintro ⟨s, j⟩ ⟨hj1, hsc, heq⟩
    unfold general_engine.head_scores_at_loop.body
    dsimp only at hj1 hsc heq ⊢
    split
    · have hjp : j.val ≤ p.val := by scalar_tac
      have hj32 : j.val < 32 := by omega
      have hrowj : Bounded Envelope.embedding (x.val[j.val]'(by simpa using hj32)) :=
        hxb _ (List.getElem_mem _)
      step with row_at_spec x j hj32 Envelope.embedding hbe hrowj as
        ⟨rowj, hrowje, hrowjb⟩
      step as ⟨lw2, hlw2⟩
      subst hlw2
      step as ⟨wkh, hwkh⟩
      have hwkmat : MatrixBound 22 wkh := by
        have hmem : wkh ∈ (W.layers.val[l.val]'(by simp; omega)).wk.val := by
          rw [hwkh]
          exact List.getElem_mem (by simp; omega)
        exact hL.wk _ hmem
      step with project_spec rowj wkh Envelope.embedding 22 hbe (by norm_num) hrowjb hwkmat
        hkenv2 as ⟨key, hkeye, hkeyb⟩
      have hkeysmall : Small key := by
        intro v hv
        have hbb := hkeyb v hv
        constructor <;> omega
      step with dot_spec q key hqsmall hkeysmall as ⟨d, hdv⟩
      step as ⟨s1, hs1⟩
      step as ⟨j1, hj1'⟩
      have hwqlen : h.val < (W.layers.val[l.val]'(by simp; omega)).wq.val.length := by
        simp; omega
      have hwklen : h.val < (W.layers.val[l.val]'(by simp; omega)).wk.val.length := by
        simp; omega
      have hwqmodel : GeneralModel.nth [] (GeneralModel.layer (toGeneralModel W) l.val).wq h.val =
          wqh.val.map (fun row => row.val.map (·.val)) := by
        rw [model_layer_eq W l hl]
        simp only [toLayerModel]
        rw [model_nth_map _ h hwqlen, hwqh]
      have hwkmodel : GeneralModel.nth [] (GeneralModel.layer (toGeneralModel W) l.val).wk h.val =
          wkh.val.map (fun row => row.val.map (·.val)) := by
        rw [model_layer_eq W l hl]
        simp only [toLayerModel]
        rw [model_nth_map _ h hwklen, hwkh]
      have hscore : d.val = GeneralModel.keyScore (toGeneralModel W) l.val h.val
          (GeneralModel.rowAt (ints2 x) p.val) (GeneralModel.rowAt (ints2 x) j.val) := by
        simp only [GeneralModel.keyScore]
        rw [hwqmodel, hwkmodel, hdv]
        simp only [hqe, hkeye, hrowpe, hrowje]
      have hqmem : ∀ (xv : Int), xv ∈ (ints q) → ∃ (v : I64), v ∈ q.val ∧ v.val = xv := by
        intro xv hxv
        simpa [ints] using hxv
      have hkmem : ∀ (yv : Int), yv ∈ (ints key) → ∃ (v : I64), v ∈ key.val ∧ v.val = yv := by
        intro yv hyv
        simpa [ints] using hyv
      have hdbound : -Envelope.score ≤ d.val ∧ d.val ≤ Envelope.score := by
        have hd := project_dot_bound (ints q) (ints key)
          (128 * Envelope.embedding * 5) (128 * Envelope.embedding * 22)
          (by positivity) (by positivity)
          (fun xv hxv => by obtain ⟨v, hv, rfl⟩ := hqmem xv hxv; exact hqb v hv)
          (fun yv hyv => by obtain ⟨v, hv, rfl⟩ := hkmem yv hyv; exact hkeyb v hv)
        rw [ints_length32] at hd
        omega
      simp only [hj1']
      refine ⟨by omega, ?_, ?_, by omega⟩
      · intro v hv
        by_cases hvj : v = d
        · subst v
          exact hdbound
        · have hmem : v ∈ s.val := by
            rw [hs1, Array.set_val_eq s j d] at hv
            rcases List.mem_or_eq_of_mem_set hv with hmem' | heq'
            · exact hmem'
            · exact absurd heq' (by simpa using hvj)
          exact hsc v hmem
      · intro j' hj' hj32
        by_cases hjj : j' < j.val
        · have hval : (ints s1)[j']'(by rw [ints_length32]; omega) =
              (ints s)[j']'(by rw [ints_length32]; omega) := by
            simp only [hs1, ints, Array.set_val_eq, List.getElem_map]
            rw [List.getElem_set_ne (by omega)]
          exact hval.trans (heq j' (by omega) hj32)
        · have hje : j' = j.val := by omega
          subst j'
          have hval : (ints s1)[j.val]'(by rw [ints_length32]; omega) = d.val := by
            simp [hs1, Array.set_val_eq, List.getElem_set_self, ints, List.getElem_map]
          exact hval.trans hscore
    · have hjp : j.val = p.val + 1 := by scalar_tac
      simp only [WP.spec_ok]
      have hsklen : (GeneralModel.headScoresAt (toGeneralModel W) l.val h.val p.val
          (ints2 x)).length = p.val + 1 := by
        simp [GeneralModel.headScoresAt]
      have htklen : ((ints s).take (p.val + 1)).length = p.val + 1 := by
        rw [List.length_take, ints_length32]
        omega
      have hsl : (ints s).length = 32 := ints_length32 s
      refine ⟨?_, hsc⟩
      apply List.ext_getElem
      · simp only [List.length_take, List.length_map]
        omega
      · intro j' hj' hj''
        have htake : ((ints s).take (p.val + 1))[j']'(by omega) =
            (ints s)[j']'(by rw [ints_length32]; omega) :=
          (List.getElem_take' (by rw [ints_length32]; omega) (by omega)).symm
        rw [htake]
        simp only [GeneralModel.headScoresAt, List.getElem_map, List.getElem_range]
        exact heq j' (by omega) (by omega)
  · simp only
    refine ⟨by scalar_tac, ?_, ?_⟩
    · intro v hv
      have hvz : v = 0#i64 := by simpa using hv
      subst v
      constructor <;> (simp only [Envelope.score]; norm_num)
    · intro j' hj'
      exact absurd hj' (by show ¬(j' < 0); omega)

end LcnExec.GeneralEngine
