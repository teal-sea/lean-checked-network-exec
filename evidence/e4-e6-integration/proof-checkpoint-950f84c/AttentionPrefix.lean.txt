import LcnExec.GeneralEngine.AttentionAdd
import LcnExec.GeneralEngine.Softmax

open Aeneas Aeneas.Std Result ControlFlow
namespace LcnExec.GeneralEngine

private theorem foldl_congr_probe {α γ : Type} (f g : γ → α → γ)
    (l : List α) (init : γ) (h : ∀ a acc, a ∈ l → f acc a = g acc a) :
    l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons a rest ih =>
    rw [List.foldl_cons, List.foldl_cons, h a init (by simp)]
    exact ih (g init a) (fun a' acc ha' => h a' acc (by simp [ha']))

theorem nth_prefix_probe (xs ys : List Int) (p : Nat) (hlen : p + 1 ≤ xs.length)
    (htake : xs.take (p + 1) = ys) (j : Nat) (hj : j ≤ p) :
    GeneralModel.nth 0 xs j = GeneralModel.nth 0 ys j := by
  have htk : j < (xs.take (p + 1)).length := by rw [List.length_take]; omega
  rw [← htake, project_nth_eq _ _ _ (by omega), project_nth_eq _ _ _ htk]
  exact List.getElem_take' (xs := xs) (i := j) (j := p + 1) (by omega) (by omega)

theorem softmax_prefix_probe (W : GeneralModel.Weights) (s s' : List Int) (p : Nat)
    (h : ∀ j, j ≤ p → GeneralModel.nth 0 s j = GeneralModel.nth 0 s' j) :
    GeneralModel.softmaxAt W s p = GeneralModel.softmaxAt W s' p := by
  have hm : GeneralModel.softmaxMax s p = GeneralModel.softmaxMax s' p := by
    unfold GeneralModel.softmaxMax
    rw [h 0 (Nat.zero_le p)]
    apply foldl_congr_probe
    intro j m hj
    rw [h j (by simpa using hj)]
  have he : (List.range (p + 1)).map (fun j =>
        GeneralModel.expFix W (Int.sub (GeneralModel.softmaxMax s p) (GeneralModel.nth 0 s j))) =
      (List.range (p + 1)).map (fun j =>
        GeneralModel.expFix W (Int.sub (GeneralModel.softmaxMax s' p) (GeneralModel.nth 0 s' j))) := by
    rw [hm]
    apply List.map_congr_left
    intro j hj
    rw [h j (by simpa using hj)]
  unfold GeneralModel.softmaxAt
  exact congrArg (fun es : List Int => es.map (fun e =>
    Int.tdiv (Int.mul e GeneralModel.ALPHA_ONE) (es.foldl Int.add (.ofNat 0)))) he

theorem head_alpha_prefix_probe (W : GeneralModel.Weights) (l hd p : Nat)
    (rows : List (List Int)) (a a' : List Int)
    (h : ∀ j, j ≤ p → GeneralModel.nth 0 a j = GeneralModel.nth 0 a' j) :
    GeneralModel.headOutAt W l hd p rows a = GeneralModel.headOutAt W l hd p rows a' := by
  have hm (vs : List (List Int)) : GeneralModel.mixAt a vs p = GeneralModel.mixAt a' vs p := by
    unfold GeneralModel.mixAt
    congr 1
    funext i
    congr 1
    apply foldl_congr_probe
    intro j acc hj
    rw [h j (by simpa using hj)]
  unfold GeneralModel.headOutAt
  rw [hm]

end LcnExec.GeneralEngine
