import LcnExec.Adder.Proofs
import LcnExec.Smoke.Proofs
import RnnAdder.Trained
open Aeneas Aeneas.Std Result
#check @LcnExec.Smoke.sum_zeros
#check @RnnAdder.Trained.sums_correct
#check @RnnAdder.Trained.carry_correct
#check @RnnAdder.Trained.adds
#check @LcnExec.Adder.rustNet_eq
#check @LcnExec.Adder.step_eq
#check @LcnExec.Adder.out_eq
#check @LcnExec.Adder.carry_eq
#check @LcnExec.Adder.add_bits_eq
#check @LcnExec.Adder.add_bits_len_ne
#check @LcnExec.Adder.add_bits_ripple
#check @LcnExec.Adder.add_bits_adds
#check @LcnExec.Adder.add_u64_net_eq
#check @LcnExec.Adder.add_u64_eq
