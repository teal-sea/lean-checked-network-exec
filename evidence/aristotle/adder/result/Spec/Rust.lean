module

public import SepLogic.Public

@[expose] public section

namespace Mir

open Rust2Lean.Public

-- Use these names with `Vocab` to state reusable properties.
-- Named handles make no correctness claim about their functions.
def Fn.«adder::add_u64» : RustFn := { name := "adder::add_u64", id := (51424674016978038240159012862990477168 : Int) }
def Fn.«<roots>» : RustFn := { name := "<roots>", id := (111346825598767891485696918120015726990 : Int) }
def Fn.«core::ptr::metadata::metadata::<[bool]>» : RustFn := { name := "core::ptr::metadata::metadata::<[bool]>", id := (121248722744445315741766754558464684846 : Int) }
def Fn.«adder::carry» : RustFn := { name := "adder::carry", id := (168911270184200412556081643805026289902 : Int) }
def Fn.«core::slice::<impl [(bool, bool)]>::len» : RustFn := { name := "core::slice::<impl [(bool, bool)]>::len", id := (121511511438012184600379160063347998558 : Int) }
def Fn.«adder::step» : RustFn := { name := "adder::step", id := (121566250866006592966578797993230802697 : Int) }
def Fn.«core::ptr::metadata::metadata::<[(bool, bool)]>» : RustFn := { name := "core::ptr::metadata::metadata::<[(bool, bool)]>", id := (158683930953575145635135695769546962009 : Int) }
def Fn.«adder::out» : RustFn := { name := "adder::out", id := (26279961555494421073650479249106297949 : Int) }
def Fn.«adder::dot_b» : RustFn := { name := "adder::dot_b", id := (103104504824019270445305664983573585859 : Int) }
def Fn.«core::slice::<impl [bool]>::len» : RustFn := { name := "core::slice::<impl [bool]>::len", id := (162883744360454046358308937209664554851 : Int) }
def Fn.«adder::thr» : RustFn := { name := "adder::thr", id := (26279468762822767555718893848782966895 : Int) }
def Fn.«adder::add_bits» : RustFn := { name := "adder::add_bits", id := (125211745499682152118754106708181499743 : Int) }
def Global.«const [16 bytes] 4f51ea92c411eebc» : RustGlobal := { name := "const [16 bytes] 4f51ea92c411eebc", id := (14223265638340095204025862882154187549 : Int) }
def Global.«const [16 bytes] 13cda269b0321f68» : RustGlobal := { name := "const [16 bytes] 13cda269b0321f68", id := (25882489958577252619782510696639101763 : Int) }
def Global.«const [64 bytes] 802a34efed5a47d7» : RustGlobal := { name := "const [64 bytes] 802a34efed5a47d7", id := (44225955321668461227474817154519591959 : Int) }

end Mir
