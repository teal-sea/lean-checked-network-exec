module

public import SepLogic.Public

@[expose] public section

namespace Mir

open Rust2Lean.Public

-- Use these names with `Vocab` to state reusable properties.
-- Named handles make no correctness claim about their functions.
def Fn.«<usize as core::slice::index::SliceIndex<[T]>>::get_unchecked::precondition_check» : RustFn := { name := "<usize as core::slice::index::SliceIndex<[T]>>::get_unchecked::precondition_check", id := (55170973502587100625289970512202772736 : Int) }
def Fn.«core::slice::<impl [i32]>::as_mut_ptr» : RustFn := { name := "core::slice::<impl [i32]>::as_mut_ptr", id := (79469727797017434500324838237553484176 : Int) }
def Fn.«core::slice::<impl [[i8; 128]]>::get_unchecked::<usize>» : RustFn := { name := "core::slice::<impl [[i8; 128]]>::get_unchecked::<usize>", id := (142554284190113065070272202272424422448 : Int) }
def Fn.«core::str::<impl str>::as_bytes» : RustFn := { name := "core::str::<impl str>::as_bytes", id := (135862955628691765269839677187441824200 : Int) }
def Fn.«mlp::hidden» : RustFn := { name := "mlp::hidden", id := (68457326687298013774613952765598965684 : Int) }
def Fn.«core::slice::<impl [i8]>::as_ptr» : RustFn := { name := "core::slice::<impl [i8]>::as_ptr", id := (124699742419678723910695828173473086324 : Int) }
def Fn.«core::slice::<impl [u8]>::len» : RustFn := { name := "core::slice::<impl [u8]>::len", id := (160574279778018090677650161301335860124 : Int) }
def Fn.«mlp::score» : RustFn := { name := "mlp::score", id := (144957863182100726987357598253928302050 : Int) }
def Fn.«core::ptr::mut_ptr::<impl *mut i32>::add» : RustFn := { name := "core::ptr::mut_ptr::<impl *mut i32>::add", id := (3590993626580003628271153990774901266 : Int) }
def Fn.«core::ptr::const_ptr::<impl *const i32>::add» : RustFn := { name := "core::ptr::const_ptr::<impl *const i32>::add", id := (61892574377708794331522020095994001746 : Int) }
def Fn.«mlp::fast::predict_fast» : RustFn := { name := "mlp::fast::predict_fast", id := (89926771542270930521073156096244100914 : Int) }
def Fn.«<usize as core::slice::index::SliceIndex<[[i8; 128]]>>::get_unchecked» : RustFn := { name := "<usize as core::slice::index::SliceIndex<[[i8; 128]]>>::get_unchecked", id := (22073387688874796801060818689235812266 : Int) }
def Fn.«core::ub_checks::check_language_ub::runtime» : RustFn := { name := "core::ub_checks::check_language_ub::runtime", id := (8293199113496313564823340542723244570 : Int) }
def Fn.«<roots>» : RustFn := { name := "<roots>", id := (111346825598767891485696918120015726990 : Int) }
def Fn.«core::ub_checks::check_language_ub» : RustFn := { name := "core::ub_checks::check_language_ub", id := (125971959633468490860113802020913031886 : Int) }
def Fn.«core::slice::<impl [i32]>::as_ptr» : RustFn := { name := "core::slice::<impl [i32]>::as_ptr", id := (6884473163503590771050697414455329029 : Int) }
def Fn.«mlp::predict» : RustFn := { name := "mlp::predict", id := (119770211079577644314193167366899439797 : Int) }
def Fn.«core::str::<impl str>::as_ptr» : RustFn := { name := "core::str::<impl str>::as_ptr", id := (51146926204421869741299086106099015037 : Int) }
def Fn.«core::ptr::const_ptr::<impl *const [[i8; 128]]>::len» : RustFn := { name := "core::ptr::const_ptr::<impl *const [[i8; 128]]>::len", id := (148394530395642474913012271374945133155 : Int) }
def Fn.«core::ptr::metadata::metadata::<[[i8; 128]]>» : RustFn := { name := "core::ptr::metadata::metadata::<[[i8; 128]]>", id := (50223504215062680922765490743766372051 : Int) }
def Fn.«core::str::<impl str>::len» : RustFn := { name := "core::str::<impl str>::len", id := (158487094977812692205751313987658244731 : Int) }
def Fn.«core::ptr::const_ptr::<impl *const i8>::add» : RustFn := { name := "core::ptr::const_ptr::<impl *const i8>::add", id := (101022720636411580070245269635373828503 : Int) }
def Fn.«core::fmt::Arguments::<'_>::from_str» : RustFn := { name := "core::fmt::Arguments::<'_>::from_str", id := (72213781763269989042978836912174212503 : Int) }
def Fn.«mlp::fast::score_fast» : RustFn := { name := "mlp::fast::score_fast", id := (82065635256544624319658922791769483703 : Int) }
def Fn.«core::ptr::metadata::metadata::<[u8]>» : RustFn := { name := "core::ptr::metadata::metadata::<[u8]>", id := (8586619058249235659138233691742537583 : Int) }
def Global.«static mlp::weights::W2» : RustGlobal := { name := "static mlp::weights::W2", id := (29006646745925339882453093569438704988 : Int) }
def Global.«static mlp::weights::E2» : RustGlobal := { name := "static mlp::weights::E2", id := (29006643257410309176251478903704877126 : Int) }
def Global.«static mlp::weights::E1» : RustGlobal := { name := "static mlp::weights::E1", id := (29006643257100824166430133834980095755 : Int) }
def Global.«"unsafe precondition(s) violated:"… [214 bytes] 6abba2084ac2f39b» : RustGlobal := { name := "\"unsafe precondition(s) violated:\"… [214 bytes] 6abba2084ac2f39b", id := (165695451485547367485226376508239184567 : Int) }

end Mir
