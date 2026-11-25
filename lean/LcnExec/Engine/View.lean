import LcnExec.Engine.Dot

open Aeneas Aeneas.Std Result
namespace LcnExec.Engine

/-- Read runtime weights as exact integers. No shape, range or semantic assumptions. -/
def toModel (w : engine.Weights) : TransformerInt.Weights where
  tok := w.tok.val.map (fun row => row.val.map (·.val))
  pos := w.pos.val.map (fun row => row.val.map (·.val))
  wq := w.wq.val.map (fun mat => mat.val.map (fun row => row.val.map (·.val)))
  wk := w.wk.val.map (fun mat => mat.val.map (fun row => row.val.map (·.val)))
  wv := w.wv.val.map (fun mat => mat.val.map (fun row => row.val.map (·.val)))
  wo := w.wo.val.map (fun mat => mat.val.map (fun row => row.val.map (·.val)))
  win := w.win.val.map (fun row => row.val.map (·.val))
  bin := w.bin.val.map (·.val)
  wout := w.wout.val.map (fun row => row.val.map (·.val))
  bout := w.bout.val.map (·.val)
  u := w.u.val.map (fun row => row.val.map (·.val))
  expN := w.exp_n.val.map (·.val)
  exp2 := w.exp_2.val.map (·.val)
  exp1 := w.exp_1.val.map (·.val)
  exp0 := w.exp_0.val.map (·.val)

/-- Build a fixed array from a total index function. -/
def arrayOfFn {α : Type} (n : Usize) (f : Nat → α) : Array α n :=
  Array.from (List.ofFn (fun i : Fin n.val => f i.val)) (by simp)

/-- This encoding wraps outside the scalar range. Only the pinned trained instance is used
in the target theorem. Its exact decoding and successful load are separate proof obligations. -/
def encode8 (z : Int) : I8 := ⟨BitVec.ofInt 8 z⟩
def encode64 (z : Int) : I64 := ⟨BitVec.ofInt 64 z⟩

def ofModel (w : TransformerInt.Weights) : engine.Weights where
  tok := arrayOfFn 114#usize (fun i => arrayOfFn 128#usize (fun j => encode8 (TransformerInt.nth 0 (TransformerInt.nth [] w.tok i) j)))
  pos := arrayOfFn 3#usize (fun i => arrayOfFn 128#usize (fun j => encode8 (TransformerInt.nth 0 (TransformerInt.nth [] w.pos i) j)))
  wq := arrayOfFn 4#usize (fun i => arrayOfFn 128#usize (fun j => arrayOfFn 32#usize (fun k => encode8 (TransformerInt.nth 0 (TransformerInt.nth [] (TransformerInt.nth [] w.wq i) j) k))))
  wk := arrayOfFn 4#usize (fun i => arrayOfFn 128#usize (fun j => arrayOfFn 32#usize (fun k => encode8 (TransformerInt.nth 0 (TransformerInt.nth [] (TransformerInt.nth [] w.wk i) j) k))))
  wv := arrayOfFn 4#usize (fun i => arrayOfFn 128#usize (fun j => arrayOfFn 32#usize (fun k => encode8 (TransformerInt.nth 0 (TransformerInt.nth [] (TransformerInt.nth [] w.wv i) j) k))))
  wo := arrayOfFn 4#usize (fun i => arrayOfFn 32#usize (fun j => arrayOfFn 128#usize (fun k => encode8 (TransformerInt.nth 0 (TransformerInt.nth [] (TransformerInt.nth [] w.wo i) j) k))))
  win := arrayOfFn 128#usize (fun i => arrayOfFn 512#usize (fun j => encode8 (TransformerInt.nth 0 (TransformerInt.nth [] w.win i) j)))
  wout := arrayOfFn 512#usize (fun i => arrayOfFn 128#usize (fun j => encode8 (TransformerInt.nth 0 (TransformerInt.nth [] w.wout i) j)))
  u := arrayOfFn 128#usize (fun i => arrayOfFn 113#usize (fun j => encode8 (TransformerInt.nth 0 (TransformerInt.nth [] w.u i) j)))
  bin := arrayOfFn 512#usize (fun i => encode64 (TransformerInt.nth 0 w.bin i))
  bout := arrayOfFn 128#usize (fun i => encode64 (TransformerInt.nth 0 w.bout i))
  exp_n := arrayOfFn 32#usize (fun i => encode64 (TransformerInt.nth 0 w.expN i))
  exp_2 := arrayOfFn 256#usize (fun i => encode64 (TransformerInt.nth 0 w.exp2 i))
  exp_1 := arrayOfFn 256#usize (fun i => encode64 (TransformerInt.nth 0 w.exp1 i))
  exp_0 := arrayOfFn 256#usize (fun i => encode64 (TransformerInt.nth 0 w.exp0 i))

end LcnExec.Engine
