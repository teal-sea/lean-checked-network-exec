module

public import SepLogic.Public

@[expose] public section

namespace Mir

open Rust2Lean.Public

-- Use these names with `Vocab` to state reusable properties.
-- Named handles make no correctness claim about their functions.
def Fn.«transformer::logits» : RustFn := { name := "transformer::logits", id := (49739299031083307186578040091645295328 : Int) }
def Fn.«transformer::unembed» : RustFn := { name := "transformer::unembed", id := (46168347513122081955746207889220996848 : Int) }
def Fn.«transformer::softmax_weights» : RustFn := { name := "transformer::softmax_weights", id := (159762759809334429166513159273949594024 : Int) }
def Fn.«transformer::mlp_hidden» : RustFn := { name := "transformer::mlp_hidden", id := (17429726526314642554676156852803705188 : Int) }
def Fn.«transformer::head_scores» : RustFn := { name := "transformer::head_scores", id := (92685237858209229869110401364278963132 : Int) }
def Fn.«transformer::attention» : RustFn := { name := "transformer::attention", id := (137321542771320453294014206410151710538 : Int) }
def Fn.«transformer::argmax» : RustFn := { name := "transformer::argmax", id := (142191240991724325571759982786600717398 : Int) }
def Fn.«<roots>» : RustFn := { name := "<roots>", id := (111346825598767891485696918120015726990 : Int) }
def Fn.«transformer::head_output» : RustFn := { name := "transformer::head_output", id := (33519979933561480779030302237961914814 : Int) }
def Fn.«transformer::predict» : RustFn := { name := "transformer::predict", id := (3126137629058132514947727526165518017 : Int) }
def Fn.«transformer::embed» : RustFn := { name := "transformer::embed", id := (78251105609679199858211579641967590625 : Int) }
def Fn.«transformer::forward» : RustFn := { name := "transformer::forward", id := (43820631992906711689781999161945009841 : Int) }
def Fn.«transformer::final_stream» : RustFn := { name := "transformer::final_stream", id := (4969635184303153910492718214870104361 : Int) }
def Fn.«transformer::project» : RustFn := { name := "transformer::project", id := (18819061706704887955832556805021056233 : Int) }
def Fn.«transformer::mlp_output» : RustFn := { name := "transformer::mlp_output", id := (76083678893886261968005692869882822957 : Int) }
def Fn.«transformer::residual» : RustFn := { name := "transformer::residual", id := (53222379657583034237687909536112323771 : Int) }
def Fn.«transformer::exp_fix» : RustFn := { name := "transformer::exp_fix", id := (57282904872362196957873770489052042055 : Int) }
def Global.«static transformer::weights::EXP_1» : RustGlobal := { name := "static transformer::weights::EXP_1", id := (23360874521468957692580420383299364240 : Int) }
def Global.«static transformer::weights::U» : RustGlobal := { name := "static transformer::weights::U", id := (85385257087209664840038087180804464852 : Int) }
def Global.«static transformer::weights::WV» : RustGlobal := { name := "static transformer::weights::WV", id := (20749505671399803134190771747135992692 : Int) }
def Global.«static transformer::weights::BIN» : RustGlobal := { name := "static transformer::weights::BIN", id := (139693932042913781846677357917351318810 : Int) }
def Global.«static transformer::weights::WOUT» : RustGlobal := { name := "static transformer::weights::WOUT", id := (54050118084076007162154477415598627110 : Int) }
def Global.«static transformer::weights::EXP_2» : RustGlobal := { name := "static transformer::weights::EXP_2", id := (23360874522397412722044455589473708353 : Int) }
def Global.«static transformer::weights::TOK» : RustGlobal := { name := "static transformer::weights::TOK", id := (139695614096108555925875292584038856457 : Int) }
def Global.«static transformer::weights::WQ» : RustGlobal := { name := "static transformer::weights::WQ", id := (20749505671090318124369426678411211321 : Int) }
def Global.«static transformer::weights::WIN» : RustGlobal := { name := "static transformer::weights::WIN", id := (139695682865534648287677633642757576133 : Int) }
def Global.«static transformer::weights::EXP_N» : RustGlobal := { name := "static transformer::weights::EXP_N", id := (23360874531062992997042117513767586741 : Int) }
def Global.«static transformer::weights::POS» : RustGlobal := { name := "static transformer::weights::POS", id := (139695250274196590227610161655600652845 : Int) }
def Global.«static transformer::weights::BOUT» : RustGlobal := { name := "static transformer::weights::BOUT", id := (53315114245478394412354192904019500995 : Int) }
def Global.«static transformer::weights::EXP_0» : RustGlobal := { name := "static transformer::weights::EXP_0", id := (23360874521778442702401765452024145611 : Int) }
def Global.«static transformer::weights::WK» : RustGlobal := { name := "static transformer::weights::WK", id := (20749505663043707869014454891566895675 : Int) }
def Global.«static transformer::weights::WO» : RustGlobal := { name := "static transformer::weights::WO", id := (20749505664281647908299835166466021159 : Int) }

end Mir
