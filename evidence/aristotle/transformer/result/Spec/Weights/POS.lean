module

public import Spec.Weights.Decode

/-! The `static` table `POS` of `src/weights.rs`, entry for entry. -/

@[expose] public section
namespace Spec.Weights

/-- The rows of `POS` (innermost arrays, `128` entries each, in order), each written as one
natural number whose base-256 digits, least significant first, are the entries' bytes in
two's complement. -/
def POS_rows : List Nat := [
  0x06fdfffefffbfeff020005fd000201fc0202ff0102f9020907fdfd03fdfefa0002fefe03ff02fd020401ff02fefefe02fffafd0302fffeff00000304fffe01fefd040106fc01fdfa00020002fdfeff000102020000030301020003ff0004fb000404fef9fefc01000201fbfc0003000107fcfc0004faff0003fd030000fe0303,
  0x04fefffb01fafd0000ff01fcffff00fb02ff00fe02f8020505fefe04fbfcfa010200fd02ff02fa0004010001ff01fc01fffbfd06010100fe0000050300fe02fe00030006f902fcfbfe02ff00fefeffff0102020001ff02ff02ff0300ff02fbff0404fefcfbfc00000302fbfbff00ff0307fcfcfe04fafe0002fd0200fffd0001,
  0xeb131ee6112428ecdb0b143024e7df24173024e7e0181c1418e7cfe2101325e0ee1fe5e2210930f0db22d8de25212517dd1ce1d5da2d26f0e927dc08ebda2edee417ebe6dcd938f1101bdbc5d91ef4202015262d28d3e225ece2df1c1ce1e0e2f6dd2614e32d21e6e0e4fc2d0dd932e70e2d13de1b2122d6e3eeea25181d1d12
]

/-- Position embedding `POS: [[i8; 128]; 3]`. -/
def POS : List (List Int) := POS_rows.map (i8Row 128)

end Spec.Weights
