/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Key
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsCroPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6Placed
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

/-!
# Relocatable Key Decode and Jump-Table Dispatch

Relocatable (`[LibsignalPlacement]`) verification of key decoding (`+0x216c → +0x2174` via
`decode_varint [local#4]` at Block `515`) and `.rodata` jump-table dispatch
(`+0x2174 → overDecArmOff fl`) on Block `518` (`lsProg_518 ext`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection CryptoVerification.CodeLayout SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Record (A0)
open CryptoVerification.E2E.Record.DeserializeGeneral (GenField)
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.VarintBridge
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt)
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.CliHandshake.Placed

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private theorem allowPanic_oom_of_trace_eq_key_pl {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    PanicOomProp s0 sf ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) := by
  intro R hm
  have himp : allocFailedIn s sf ∧ s.trace <+: sf.trace →
      allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
    rintro ⟨ha, hp⟩
    unfold allocFailedIn at ha ⊢
    rw [← htr]
    exact ⟨ha, hp⟩
  exact allowPanic_frame himp hm

private theorem SepWPp_bind_sepWP_frame_key_pl {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      prog.CodeLoaded sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpc hrun hLm hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem stackAt_sub_eq_key_pl (sp : BitVec 64) (M N : Nat) (hMN : N ≤ M := by decide)
    (hbound : M < 2 ^ 64 := by decide) :
    stackAt sp M = stackAt sp N ∗ memRegion (sp - BitVec.ofNat 64 M) (M - N) := by
  have h1 : M = N + (M - N) := (Nat.add_sub_of_le hMN).symm
  have h2 := ProofLib.stackAt_split_bottom sp N (M - N) (by omega)
  rw [← h1] at h2
  rw [h2, sepConj_comm]

private theorem overDecWt_toNat_eq_pl (fl : GenFieldQ) :
    (overDecWt fl).toNat = fl.wt.toNat := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> rfl

private theorem decodeVarint_fl_enc_pl (fl : GenFieldQ) (rest : List (BitVec 8)) :
    decodeVarint (fl.enc ++ rest) = some (overDecKeyVal fl, fl.payload ++ rest) := by
  rw [GenFieldQ.enc, List.append_assoc, encodeKey, overDecKeyVal, overDecWt_toNat_eq_pl fl]
  exact decodeVarint_encodeVarint _ _

private theorem fl_payload_rest_len_le_pl (fl : GenFieldQ) (rest : List (BitVec 8)) :
    (fl.payload ++ rest).length ≤ (fl.enc ++ rest).length := by
  simp only [GenFieldQ.enc, List.length_append]
  omega

private theorem sliceCursorAfter_split_of_append_pl (slot ptr : BitVec 64)
    (bs1 bs2 : List (BitVec 8)) :
    Prost.sliceCursorAfter slot ptr (bs1 ++ bs2) bs2 =
      Prost.sliceCursorAt slot (ptr + BitVec.ofNat 64 bs1.length) bs2 ∗ (ptr ↦ₛ bs1) := by
  unfold Prost.sliceCursorAfter Prost.sliceCursorAt
  have hsub : (bs1 ++ bs2).length - bs2.length = bs1.length := by
    rw [List.length_append]; omega
  rw [hsub, pointsToBytes_append ptr bs1 bs2]
  ac_rfl

private theorem sliceCursorAfter_unsplit_of_append_pl (slot ptr : BitVec 64)
    (bs1 bs2 bs3 : List (BitVec 8)) (hle : bs3.length ≤ bs2.length) :
    Prost.sliceCursorAfter slot (ptr + BitVec.ofNat 64 bs1.length) bs2 bs3 ∗ (ptr ↦ₛ bs1) =
      Prost.sliceCursorAfter slot ptr (bs1 ++ bs2) bs3 := by
  unfold Prost.sliceCursorAfter
  have hadd : (ptr + BitVec.ofNat 64 bs1.length) + BitVec.ofNat 64 (bs2.length - bs3.length) =
      ptr + BitVec.ofNat 64 ((bs1 ++ bs2).length - bs3.length) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    rw [List.length_append]
    omega
  rw [hadd, pointsToBytes_append ptr bs1 bs2]
  ac_rfl

/-! ## Stage 1 (`+0x216c → lsmpl.base 515 → +0x2174`): `decode_varint [local#4]` Call -/

set_option maxHeartbeats 400000 in
private theorem overDecKey_precall_sepWP_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s0 s : State) (g : OverDecG)
    (hregs : OverDecRegsPlaced ext s0 g 0x216c#64 s) :
    SepWP (lsProg_518 ext) (lsmpl.base 515) s emp
      (fun sm P' => (P' ⊢ emp) ∧
        sm.sp = g.q ∧ (sm.sp &&& 15#64 == 0#64) = true ∧ sm.trace = s0.trace ∧
        sm.readReg64 .x0 = g.q + 0xbe8#64 ∧
        sm.readReg64 .lr = (blkPl_518).base + 0x2174#64 ∧
        sm.readReg64 .x19 = g.r19 ∧ sm.readReg64 .x20 = g.r20 ∧ sm.readReg64 .x26 = g.r26 ∧
        sm.readReg64 .x21 = g.q + 0x930#64 ∧ sm.readReg64 .x24 = 1#64 ∧
        sm.readReg64 .x25 = 0xffffffffffffffff#64 ∧ sm.readReg64 .x27 = g.prevPtr ∧
        sm.readReg64 .x28 = g.q + 0xa90#64 ∧ sm.readReg64 .x29 = g.q + 0xc70#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs g.sv) := by
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, _hcl,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  have h19 : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have h26 : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have h21 : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have h24 : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have h27 : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have h28 : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have h29 : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine ⟨Entails.refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hsp, arm64_norm]
  · simp only [hal, arm64_norm]
  · simp only [htr, arm64_norm]
  · simp only [arm64_norm]
  · simp only [arm64_norm]
  · simp only [h19, arm64_norm]
  · simp only [h20, arm64_norm]
  · simp only [h26, arm64_norm]
  · simp only [h21, arm64_norm]
  · simp only [h24, arm64_norm]
  · simp only [h25, arm64_norm]
  · simp only [h27, arm64_norm]
  · simp only [h28, arm64_norm]
  · simp only [h29, arm64_norm]
  · simp only [hvregs, arm64_norm]

private theorem overDec_call_decodeVarint5_plain_pl [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {s0 sm : State} {g : OverDecG} {fl : GenFieldQ}
    {pfx rest : List (BitVec 8)} {F : SepProp} {Q : State → SepProp → Prop}
    (hV : subroutine_ok (lsProg_518 ext) (lsmpl.base 515) (SpqrH.decodeVarint2SpecX A))
    (htrm : sm.trace = s0.trace)
    (hpcm : sm.pc = lsmpl.base 515)
    (hrunm : sm.status = .Running) (hspm : sm.sp = g.q)
    (halm : (sm.sp &&& 15#64 == 0#64) = true)
    (hx0m : sm.readReg64 .x0 = g.q + 0xbe8#64)
    (hlrm : sm.readReg64 .lr = (blkPl_518).base + 0x2174#64)
    (hlen63 : (fl.enc ++ rest).length < 2 ^ 63)
    (hnext : ∀ s2 : State,
      s2.pc = (blkPl_518).base + 0x2174#64 →
      s2.status = .Running → s2.sp = g.q →
      (lsProg_518 ext).CodeLoaded s2.mem → s2.trace = s0.trace →
      CalleeSavedPreserved sm s2 →
      s2.readReg64 .x0 = 0#64 → s2.readReg64 .x1 = overDecKeyVal fl →
      SepWPp (lsProg_518 ext) ret s2
        (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
          Prost.sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
            (fl.enc ++ rest) (fl.payload ++ rest) ∗
          A.pool ∗
          stackAt g.q SpqrH.decodeVarint2StackX) ∗ F)
        Q (PanicOomProp s0)) :
    SepWPp (lsProg_518 ext) ret sm
      (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
        Prost.sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length) (fl.enc ++ rest) ∗
        A.pool ∗
        stackAt g.q SpqrH.decodeVarint2StackX) ∗ F)
      Q (PanicOomProp s0) := by
  intro R hm hL
  let x : DecodeVarintSlowGhost :=
    ⟨g.q + 0xbe8#64, g.q + 0x920#64, g.encPtr + BitVec.ofNat 64 pfx.length, fl.enc ++ rest⟩
  have hpre : sm.mem ⊨ (SpqrH.decodeVarint2SpecX A).pre x sm ∗ (F ∗ R) := by
    dsimp only [SpqrH.decodeVarint2SpecX, x]
    rw [hspm, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0m, hlen63⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  obtain ⟨s2, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hV x (F ∗ R) hpcm hrunm hpre halm hL
  rcases hout with ⟨⟨hpc2, _, hrun2⟩, ⟨hsp2, hcs2⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom⟩
  rotate_right
  · dsimp only [SpqrH.decodeVarint2SpecX] at hoom
    exact (not_satisfies_false_sepConj hoom).elim
  · rw [hlrm] at hpc2; rw [hspm] at hsp2
    dsimp only [SpqrH.decodeVarint2SpecX, x] at hpost
    rw [decodeVarint_fl_enc_pl fl rest, hspm] at hpost
    dsimp only at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0_2, hx1_2⟩, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htr2, hpost⟩
    have hpost' : s2.mem ⊨ (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
        Prost.sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
          (fl.enc ++ rest) (fl.payload ++ rest) ∗
        A.pool ∗
        stackAt g.q SpqrH.decodeVarint2StackX) ∗ F) ∗ R := by
      have heq :
          (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
            Prost.sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
              (fl.enc ++ rest) (fl.payload ++ rest) ∗
            A.pool ∗
            stackAt g.q SpqrH.decodeVarint2StackX) ∗ F) ∗ R =
          ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
            A.pool ∗
            stackAt g.q SpqrH.decodeVarint2StackX ∗
            Prost.sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
              (fl.enc ++ rest) (fl.payload ++ rest)) ∗ F ∗ R := by ac_rfl
      rw [heq]; exact hpost
    have hL2 : (lsProg_518 ext).CodeLoaded s2.mem := hsteps.codeLoaded hL
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext s2 hpc2 hrun2 hsp2 hL2 (htr2.trans htrm) hcs2 hx0_2 hx1_2 R hpost' hL2
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [SpqrH.decodeVarint2SpecX] at hpost
    rw [← sepConj_assoc] at hpost
    exact ⟨s2, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, allowPanic_oom_of_trace_eq_key_pl htrm⟩)⟩
  · dsimp only [SpqrH.decodeVarint2SpecX] at hpost
    exact (allowPanic_not_exited hpost).elim

/-! ## Stage 2 (`+0x2174 → overDecArmOff fl`): Jump-Table Dispatch -/

@[local simp, local arm64_norm]
private theorem overDecKeyVal_lsr32_pl (fl : GenFieldQ) :
    overDecKeyVal fl >>> 32#64 = 0#64 := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_lsr32_nat_pl (fl : GenFieldQ) :
    overDecKeyVal fl >>> 32 = 0#64 := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_and7_pl (fl : GenFieldQ) :
    overDecKeyVal fl &&& 7#64 = overDecWt fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecWt_ule6_pl (fl : GenFieldQ) :
    (6#64).ule (overDecWt fl) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecWt, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_trunc32_zext64_pl (fl : GenFieldQ) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (overDecKeyVal fl)) = overDecKeyVal fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_lsr3_pl (fl : GenFieldQ) :
    overDecKeyVal fl >>> 3 = BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_wlsr3_pl (fl : GenFieldQ) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (overDecKeyVal fl) >>> 3#32) =
      BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_wlsr3_nat_pl (fl : GenFieldQ) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (overDecKeyVal fl) >>> 3) =
      BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecTag_trunc32_zext64_pl (fl : GenFieldQ) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 fl.tag)) =
      BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_beq_zero_pl (fl : GenFieldQ) :
    (BitVec.ofNat 64 fl.tag == 0#64) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_w32_beq_zero_pl (fl : GenFieldQ) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 fl.tag) == 0#32) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_sub1_64_pl (fl : GenFieldQ) :
    BitVec.ofNat 64 fl.tag - 1#64 = BitVec.ofNat 64 (fl.tag - 1) := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_add_neg1_64_pl (fl : GenFieldQ) :
    BitVec.ofNat 64 fl.tag + 0xffffffffffffffff#64 = BitVec.ofNat 64 (fl.tag - 1) := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_w32_sub1_pl (fl : GenFieldQ) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 fl.tag) - 1#32) =
      BitVec.ofNat 64 (fl.tag - 1) := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_w32_add_neg1_pl (fl : GenFieldQ) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 fl.tag) + 4294967295#32) =
      BitVec.ofNat 64 (fl.tag - 1) := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_sub1_trunc32_zext64_pl (fl : GenFieldQ) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 (fl.tag - 1))) =
      BitVec.ofNat 64 (fl.tag - 1) := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_sub1_ult14_pl (fl : GenFieldQ) :
    (14#32).ult (BitVec.setWidth 32 (BitVec.ofNat 64 (fl.tag - 1))) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_sub1_ult14_64_pl (fl : GenFieldQ) :
    (14#64).ult (BitVec.ofNat 64 (fl.tag - 1)) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecJtabByte_add_armOff_pl (fl : GenFieldQ) :
    8636#64 + (BitVec.setWidth 64 (overDecJtabByte fl) <<< 2#64) = overDecArmOff fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecJtabByte, overDecArmOff]

@[local simp, local arm64_norm]
private theorem overDecJtabByte_add_armOff_nat_pl (fl : GenFieldQ) :
    8636#64 + (BitVec.setWidth 64 (overDecJtabByte fl) <<< 2) = overDecArmOff fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecJtabByte, overDecArmOff]

@[local simp, local arm64_norm]
private theorem overDecJtabByte_zext_add_armOff_pl (fl : GenFieldQ) :
    8636#64 + (BitVec.zeroExtend 64 (overDecJtabByte fl) <<< 2) = overDecArmOff fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecJtabByte, overDecArmOff]

/-- Relocatable `.rodata` symbol for the 15-byte jump table of `decryptPrekeyClosure`. -/
abbrev overDecJtabSym : String :=
  "libsignal_cli_handshake:.rodata.libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"

/-- Conjures `(lsρ overDecJtabSym ↦ᵣ overDecJtabBytes)` from `LibsignalRoLoaded lsmpl s.mem`. -/
theorem rodata_overDecJtab_placed_intro [LibsignalPlacement]
    {s : State} (hro : CryptoVerification.LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((lsρ overDecJtabSym) ↦ᵣ overDecJtabBytes) ∗ P :=
  lsro_intro_chk hro (by rfl_kernel) hP

private theorem overDecJtab_split_eq (fl : GenFieldQ) :
    overDecJtabBytes = overDecJtabBytes.take (fl.tag - 1) ++
      (overDecJtabByte fl :: overDecJtabBytes.drop fl.tag) ∧
    (overDecJtabBytes.take (fl.tag - 1)).length = fl.tag - 1 := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    (simp only [GenFieldQ.tag, GenField.tag, overDecJtabByte]; decide)

theorem rodata_overDecJtabByte_of_table [LibsignalPlacement]
    {m : Memory} {R : SepProp} (fl : GenFieldQ)
    (htab : m ⊨ ((lsρ overDecJtabSym) ↦ᵣ overDecJtabBytes) ∗ R) :
    m ⊨ ((lsρ overDecJtabSym + BitVec.ofNat 64 (fl.tag - 1)) ↦₈ᵣ overDecJtabByte fl) ∗ R := by
  obtain ⟨hsplit, hlen⟩ := overDecJtab_split_eq fl
  have heq : ((lsρ overDecJtabSym) ↦ᵣ overDecJtabBytes) =
      ((lsρ overDecJtabSym) ↦ᵣ overDecJtabBytes.take (fl.tag - 1)) ∗
        (((lsρ overDecJtabSym + BitVec.ofNat 64 (fl.tag - 1)) ↦₈ᵣ overDecJtabByte fl) ∗
         ((lsρ overDecJtabSym + BitVec.ofNat 64 (fl.tag - 1) + 1#64) ↦ᵣ
           overDecJtabBytes.drop fl.tag)) := by
    conv_lhs => rw [hsplit]
    rw [pointsToBytesRO_append, pointsToBytesRO_cons, hlen]
  rw [heq] at htab
  have h1 : m ⊨ (((lsρ overDecJtabSym + BitVec.ofNat 64 (fl.tag - 1)) ↦₈ᵣ overDecJtabByte fl) ∗
      ((lsρ overDecJtabSym + BitVec.ofNat 64 (fl.tag - 1) + 1#64) ↦ᵣ
        overDecJtabBytes.drop fl.tag)) ∗ R := by
    rw [sepConj_assoc] at htab
    exact Satisfies.of_sep_right htab
  rw [sepConj_assoc] at h1
  have h2 : (((lsρ overDecJtabSym + BitVec.ofNat 64 (fl.tag - 1) + 1#64) ↦ᵣ
      overDecJtabBytes.drop fl.tag) ∗ R) =
      (R ∗ ((lsρ overDecJtabSym + BitVec.ofNat 64 (fl.tag - 1) + 1#64) ↦ᵣ
        overDecJtabBytes.drop fl.tag)) := sepConj_comm _ _
  rw [h2, ← sepConj_assoc] at h1
  exact Satisfies.of_sep_left h1

private theorem sepWPp_intro_overDecJtabByte_pl [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hro : ∀ (R : SepProp), s.mem ⊨ R →
      s.mem ⊨ ((lsρ overDecJtabSym) ↦ᵣ overDecJtabBytes) ∗ R)
    (fl : GenFieldQ)
    (h : SepWPp prog ret s
      (((lsρ overDecJtabSym + BitVec.ofNat 64 (fl.tag - 1)) ↦₈ᵣ overDecJtabByte fl) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  refine h R ?_ hL
  rw [sepConj_assoc]
  exact rodata_overDecJtabByte_of_table fl (hro (P ∗ R) hm)

set_option maxHeartbeats 600000 in
private theorem overDecKey_jtab_sepWP_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s0 s2 : State) (g : OverDecG) (fl : GenFieldQ)
    (hregs : OverDecRegsPlaced ext s0 g 0x2174#64 s2)
    (hx0 : s2.readReg64 .x0 = 0#64)
    (hx1 : s2.readReg64 .x1 = overDecKeyVal fl) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + overDecArmOff fl) s2
      ((lsρ overDecJtabSym + BitVec.ofNat 64 (fl.tag - 1)) ↦₈ᵣ overDecJtabByte fl)
      (fun sf P' =>
        (P' ⊢ ((lsρ overDecJtabSym + BitVec.ofNat 64 (fl.tag - 1)) ↦₈ᵣ overDecJtabByte fl)) ∧
        sf.sp = g.q ∧ (sf.sp &&& 15#64 == 0#64) = true ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x0 = overDecWt fl ∧
        sf.readReg64 .x22 = overDecKeyVal fl ∧
        sf.readReg64 .x19 = g.r19 ∧ sf.readReg64 .x20 = g.r20 ∧ sf.readReg64 .x26 = g.r26 ∧
        sf.readReg64 .x21 = g.q + 0x930#64 ∧ sf.readReg64 .x24 = 1#64 ∧
        sf.readReg64 .x25 = 0xffffffffffffffff#64 ∧ sf.readReg64 .x27 = g.prevPtr ∧
        sf.readReg64 .x28 = g.q + 0xa90#64 ∧ sf.readReg64 .x29 = g.q + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs g.sv) := by
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, _hcl,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  have h0 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s2.readReg64 (Reg.gpr 1#5) = overDecKeyVal fl := hx1
  have h19 : s2.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have h20 : s2.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have h26 : s2.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have h21 : s2.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have h24 : s2.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have h25 : s2.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have h27 : s2.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have h28 : s2.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have h29 : s2.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  iterate 17 wp_step
  refine SepWP.done (by simp only [arm64_norm, BitVec.add_assoc])
    (by simp only [hrun, arm64_norm]) ?_
  refine ⟨Entails.refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hsp, arm64_norm]
  · simp only [hal, arm64_norm]
  · simp only [htr, arm64_norm]
  · simp only [arm64_norm]
  · simp only [arm64_norm]
  · simp only [h19, arm64_norm]
  · simp only [h20, arm64_norm]
  · simp only [h26, arm64_norm]
  · simp only [h21, arm64_norm]
  · simp only [h24, arm64_norm]
  · simp only [h25, arm64_norm]
  · simp only [h27, arm64_norm]
  · simp only [h28, arm64_norm]
  · simp only [h29, arm64_norm]
  · simp only [hvregs, arm64_norm]

private theorem drop_left_sepWPp_pl {prog : Program} {ret : BitVec 64}
    {s : State} {Drop P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (Drop ∗ P) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

set_option maxHeartbeats 600000 in
/-- Relocatable `[LibsignalPlacement]` key dispatch (`+0x216c → overDecArmOff fl`, `OverDecKeyPlacedStmt`), parameterized by `decode_varint [local#4]` (Block `515`) and `.rodata` jump-table loadedness. -/
theorem overDecKey_placed_of_callees [LibsignalPlacement]
    (hDv5 : ∀ ext, subroutine_ok (lsProg_518 ext) (lsmpl.base 515)
      (SpqrH.decodeVarint2SpecX A0))
    (hro_jtab : ∀ ext (s : State) (R : SepProp),
      (lsProg_518 ext).CodeLoaded s.mem → s.mem ⊨ R →
      s.mem ⊨ ((lsρ overDecJtabSym) ↦ᵣ overDecJtabBytes) ∗ R) :
    OverDecKeyPlacedStmt := by
  intro ext s0 s g v fl rest _hAny _hok hsuf hlen hregs
  rcases hsuf with ⟨pfx, hpfx⟩
  have hlen63 : (fl.enc ++ rest).length < 2 ^ 63 := by
    have hle : (fl.enc ++ rest).length ≤ g.enc.length := by
      have hlen_eq := congrArg List.length hpfx
      rw [List.length_append] at hlen_eq
      omega
    omega
  refine SepWPp_bind_sepWP_frame_key_pl (overDecKey_precall_sepWP_placed ext s0 s g hregs)
    (F := overDecHeap g (fl.enc ++ rest) v)
    (by simp only [emp_sepConj])
    fun sm hpcm hrunm _hLm hregsm => ?_
  rcases hregsm with ⟨hspm, halm, htrm, hx0m, hlrm,
    hx19m, hx20m, hx26m, hx21m, hx24m, hx25m, hx27m, hx28m, hx29m, hvregsm⟩
  have hheap_split :
      emp ∗ overDecHeap g (fl.enc ++ rest) v =
        (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
          Prost.sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length) (fl.enc ++ rest) ∗
          A0.pool ∗
          stackAt g.q SpqrH.decodeVarint2StackX) ∗
         (overPrevElemRestExt A0 g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
          (g.encPtr ↦ₛ pfx) ∗
          prostSSGQAt A0 (g.q + 0x930#64) v ∗
          memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
          memRegion (g.q + 0xbf0#64) 128 ∗
          memRegion (g.q - BitVec.ofNat 64 overDecStackX)
            (overDecStackX - SpqrH.decodeVarint2StackX))) := by
    have hcur :
        Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc (fl.enc ++ rest) =
          Prost.sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length) (fl.enc ++ rest) ∗
            (g.encPtr ↦ₛ pfx) := by
      rw [← hpfx]
      exact sliceCursorAfter_split_of_append_pl (g.q + 0x920#64) g.encPtr pfx (fl.enc ++ rest)
    unfold overDecHeap overDecHeapExt
    rw [hcur, stackAt_sub_eq_key_pl g.q overDecStackX SpqrH.decodeVarint2StackX (by decide) (by decide),
      emp_sepConj]
    ac_rfl
  rw [hheap_split]
  refine overDec_call_decodeVarint5_plain_pl (hDv5 ext) htrm hpcm hrunm hspm halm hx0m hlrm hlen63
    fun s2 hpc2 hrun2 hsp2 hL2 htr2 hcs2 hx0_2 hx1_2 => ?_
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, _, _, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs, hx29_cs, hvregs_cs⟩
  have hal2 : (s2.sp &&& 15#64 == 0#64) = true := by simpa only [hsp2, hspm] using halm
  have hregs2 : OverDecRegsPlaced ext s0 g 0x2174#64 s2 :=
    ⟨hpc2, hrun2, hsp2, hal2, htr2, hL2,
     hx19_cs.trans hx19m, hx20_cs.trans hx20m, hx26_cs.trans hx26m,
     hx21_cs.trans hx21m, hx24_cs.trans hx24m, hx25_cs.trans hx25m,
     hx27_cs.trans hx27m, hx28_cs.trans hx28m, hx29_cs.trans hx29m,
     hvregs_cs.trans hvregsm⟩
  have hheap_unsplit :
      (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
        Prost.sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
          (fl.enc ++ rest) (fl.payload ++ rest) ∗
        A0.pool ∗
        stackAt g.q SpqrH.decodeVarint2StackX) ∗
       (overPrevElemRestExt A0 g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
        (g.encPtr ↦ₛ pfx) ∗
        prostSSGQAt A0 (g.q + 0x930#64) v ∗
        memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
        memRegion (g.q + 0xbf0#64) 128 ∗
        memRegion (g.q - BitVec.ofNat 64 overDecStackX)
          (overDecStackX - SpqrH.decodeVarint2StackX))) =
      overDecHeap g (fl.payload ++ rest) v := by
    have hunsplit :=
      sliceCursorAfter_unsplit_of_append_pl (g.q + 0x920#64) g.encPtr pfx (fl.enc ++ rest)
        (fl.payload ++ rest) (fl_payload_rest_len_le_pl fl rest)
    rw [hpfx] at hunsplit
    unfold overDecHeap overDecHeapExt
    rw [← hunsplit, stackAt_sub_eq_key_pl g.q overDecStackX SpqrH.decodeVarint2StackX (by decide) (by decide)]
    ac_rfl
  rw [hheap_unsplit]
  refine sepWPp_intro_overDecJtabByte_pl (fun R hR => hro_jtab ext s2 R hL2 hR) fl ?_
  refine SepWPp_bind_sepWP_frame_key_pl
    (overDecKey_jtab_sepWP_placed ext s0 s2 g fl hregs2 hx0_2 hx1_2)
    rfl
    fun sf hpcf hrunf hLf hregsf => ?_
  apply drop_left_sepWPp_pl
  rcases hregsf with ⟨hspf, half, htrf, hx0f, hx22f,
    hx19f, hx20f, hx26f, hx21f, hx24f, hx25f, hx27f, hx28f, hx29f, hvregsf⟩
  refine SepWPp.done hpcf hrunf
    ⟨⟨hpcf, hrunf, hspf, half, htrf, hLf,
      hx19f, hx20f, hx26f, hx21f, hx24f, hx25f, hx27f, hx28f, hx29f, hvregsf⟩,
     hx0f, hx22f, Entails.refl _⟩

section Cro

open CryptoVerification.LibsignalPublicApi

private theorem SepWPp_bind_sepWP_frame_cro_key_pl [LibsignalPlacement]
    {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      prog.CodeLoaded sm.mem → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpc hrun hLm (hcro.of_keepsFrozen hsteps.keepsFrozen) hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem overDec_call_decodeVarint5_lscl_pl [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {s0 sm : State} {g : OverDecG} {fl : GenFieldQ}
    {pfx rest : List (BitVec 8)} {F : SepProp} {Q : State → SepProp → Prop}
    (hV : subroutine_ok (lsProg_518 ext) (lsmpl.base 515)
      (withLsCodeLoaded lsmpl (SpqrH.decodeVarint2SpecX A)))
    (hcrom : StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem)
    (htrm : sm.trace = s0.trace)
    (hpcm : sm.pc = lsmpl.base 515)
    (hrunm : sm.status = .Running) (hspm : sm.sp = g.q)
    (halm : (sm.sp &&& 15#64 == 0#64) = true)
    (hx0m : sm.readReg64 .x0 = g.q + 0xbe8#64)
    (hlrm : sm.readReg64 .lr = (blkPl_518).base + 8564#64)
    (hlen63 : (fl.enc ++ rest).length < 2 ^ 63)
    (hnext : ∀ s2 : State,
      s2.pc = (blkPl_518).base + 8564#64 →
      s2.status = .Running → s2.sp = g.q →
      (lsProg_518 ext).CodeLoaded s2.mem →
      StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem → s2.trace = s0.trace →
      CalleeSavedPreserved sm s2 →
      s2.readReg64 .x0 = 0#64 → s2.readReg64 .x1 = overDecKeyVal fl →
      SepWPp (lsProg_518 ext) ret s2
        (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
          Prost.sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
            (fl.enc ++ rest) (fl.payload ++ rest) ∗
          A.pool ∗
          stackAt g.q SpqrH.decodeVarint2StackX) ∗ F)
        Q (PanicOomProp s0)) :
    SepWPp (lsProg_518 ext) ret sm
      (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
        Prost.sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length) (fl.enc ++ rest) ∗
        A.pool ∗
        stackAt g.q SpqrH.decodeVarint2StackX) ∗ F)
      Q (PanicOomProp s0) := by
  intro R hm hL
  let x : DecodeVarintSlowGhost :=
    ⟨g.q + 0xbe8#64, g.q + 0x920#64, g.encPtr + BitVec.ofNat 64 pfx.length, fl.enc ++ rest⟩
  have hpre : sm.mem ⊨ (withLsCodeLoaded lsmpl (SpqrH.decodeVarint2SpecX A)).pre x sm ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded, SpqrH.decodeVarint2SpecX, x]
    rw [sepConj_assoc, sepConj_left_comm _ (⌜LibsignalCodeLoaded _ _⌝), satisfies_pure_sepConj]
    refine ⟨hcrom.1, ?_⟩
    rw [hspm, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0m, hlen63⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  obtain ⟨s2, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hV x (F ∗ R) hpcm hrunm hpre halm hL
  rcases hout with ⟨⟨hpc2, _, hrun2⟩, ⟨hsp2, hcs2⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom⟩
  rotate_right
  · dsimp only [withLsCodeLoaded, SpqrH.decodeVarint2SpecX] at hoom
    exact (not_satisfies_false_sepConj hoom).elim
  · rw [hlrm] at hpc2; rw [hspm] at hsp2
    dsimp only [withLsCodeLoaded, SpqrH.decodeVarint2SpecX, x] at hpost
    rw [decodeVarint_fl_enc_pl fl rest, hspm] at hpost
    dsimp only at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0_2, hx1_2⟩, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htr2, hpost⟩
    have hpost' : s2.mem ⊨ (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
        Prost.sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
          (fl.enc ++ rest) (fl.payload ++ rest) ∗
        A.pool ∗
        stackAt g.q SpqrH.decodeVarint2StackX) ∗ F) ∗ R := by
      have heq :
          (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
            Prost.sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
              (fl.enc ++ rest) (fl.payload ++ rest) ∗
            A.pool ∗
            stackAt g.q SpqrH.decodeVarint2StackX) ∗ F) ∗ R =
          ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
            A.pool ∗
            stackAt g.q SpqrH.decodeVarint2StackX ∗
            Prost.sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
              (fl.enc ++ rest) (fl.payload ++ rest)) ∗ F ∗ R := by ac_rfl
      rw [heq]; exact hpost
    have hL2 : (lsProg_518 ext).CodeLoaded s2.mem := hsteps.codeLoaded hL
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext s2 hpc2 hrun2 hsp2 hL2 (hcrom.of_keepsFrozen hsteps.keepsFrozen) (htr2.trans htrm)
        hcs2 hx0_2 hx1_2 R hpost' hL2
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded, SpqrH.decodeVarint2SpecX] at hpost
    rw [← sepConj_assoc] at hpost
    exact ⟨s2, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, allowPanic_oom_of_trace_eq_key_pl htrm⟩)⟩
  · dsimp only [withLsCodeLoaded, SpqrH.decodeVarint2SpecX] at hpost
    exact (allowPanic_not_exited hpost).elim

set_option maxHeartbeats 600000 in
/-- Fixed-`ext` `LibsignalCodeRoLoaded` key dispatch (`OverDecKeyCroPlacedAt ext`), discharged from `HookSat` on `ext` and `LibsignalCodeRoLoaded`. -/
theorem overDecKey_cro_placed_of_hooks [LibsignalPlacement]
    {ext : LibsignalHooks}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat ext lsRustAllocSym (rustAllocSpec A0))
    (hpanic_alloc : ext lsHandleAllocErrorSym = some Rust.panicked) :
    OverDecKeyCroPlacedAt ext := by
  have hDv5 : subroutine_ok (lsProg_518 ext) (lsmpl.base 515)
      (withLsCodeLoaded lsmpl (SpqrH.decodeVarint2SpecX A0)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_518 ext)
      (SpqrH.bm6_decodeVarint5_placed_of_hooks hshim halloc hpanic_alloc)
  intro s0 s g v fl rest _hAny _hok hsuf hlen ⟨hcro, hregs⟩
  rcases hsuf with ⟨pfx, hpfx⟩
  have hlen63 : (fl.enc ++ rest).length < 2 ^ 63 := by
    have hle : (fl.enc ++ rest).length ≤ g.enc.length := by
      have hlen_eq := congrArg List.length hpfx
      rw [List.length_append] at hlen_eq
      omega
    omega
  refine SepWPp_bind_sepWP_frame_cro_key_pl hcro (overDecKey_precall_sepWP_placed ext s0 s g hregs)
    (F := overDecHeap g (fl.enc ++ rest) v)
    (by simp only [emp_sepConj])
    fun sm hpcm hrunm _hLm hcrom hregsm => ?_
  rcases hregsm with ⟨hspm, halm, htrm, hx0m, hlrm,
    hx19m, hx20m, hx26m, hx21m, hx24m, hx25m, hx27m, hx28m, hx29m, hvregsm⟩
  have hheap_split :
      emp ∗ overDecHeap g (fl.enc ++ rest) v =
        (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
          Prost.sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length) (fl.enc ++ rest) ∗
          A0.pool ∗
          stackAt g.q SpqrH.decodeVarint2StackX) ∗
         (overPrevElemRestExt A0 g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
          (g.encPtr ↦ₛ pfx) ∗
          prostSSGQAt A0 (g.q + 0x930#64) v ∗
          memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
          memRegion (g.q + 0xbf0#64) 128 ∗
          memRegion (g.q - BitVec.ofNat 64 overDecStackX)
            (overDecStackX - SpqrH.decodeVarint2StackX))) := by
    have hcur :
        Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc (fl.enc ++ rest) =
          Prost.sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length) (fl.enc ++ rest) ∗
            (g.encPtr ↦ₛ pfx) := by
      rw [← hpfx]
      exact sliceCursorAfter_split_of_append_pl (g.q + 0x920#64) g.encPtr pfx (fl.enc ++ rest)
    unfold overDecHeap overDecHeapExt
    rw [hcur, stackAt_sub_eq_key_pl g.q overDecStackX SpqrH.decodeVarint2StackX (by decide) (by decide),
      emp_sepConj]
    ac_rfl
  rw [hheap_split]
  refine overDec_call_decodeVarint5_lscl_pl hDv5 hcrom htrm hpcm hrunm hspm halm hx0m hlrm hlen63
    fun s2 hpc2 hrun2 hsp2 hL2 hcro2 htr2 hcs2 hx0_2 hx1_2 => ?_
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, _, _, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs, hx29_cs, hvregs_cs⟩
  have hal2 : (s2.sp &&& 15#64 == 0#64) = true := by simpa only [hsp2, hspm] using halm
  have hregs2 : OverDecRegsPlaced ext s0 g 0x2174#64 s2 :=
    ⟨hpc2, hrun2, hsp2, hal2, htr2, hL2,
     hx19_cs.trans hx19m, hx20_cs.trans hx20m, hx26_cs.trans hx26m,
     hx21_cs.trans hx21m, hx24_cs.trans hx24m, hx25_cs.trans hx25m,
     hx27_cs.trans hx27m, hx28_cs.trans hx28m, hx29_cs.trans hx29m,
     hvregs_cs.trans hvregsm⟩
  have hheap_unsplit :
      (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
        Prost.sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
          (fl.enc ++ rest) (fl.payload ++ rest) ∗
        A0.pool ∗
        stackAt g.q SpqrH.decodeVarint2StackX) ∗
       (overPrevElemRestExt A0 g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
        (g.encPtr ↦ₛ pfx) ∗
        prostSSGQAt A0 (g.q + 0x930#64) v ∗
        memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
        memRegion (g.q + 0xbf0#64) 128 ∗
        memRegion (g.q - BitVec.ofNat 64 overDecStackX)
          (overDecStackX - SpqrH.decodeVarint2StackX))) =
      overDecHeap g (fl.payload ++ rest) v := by
    have hunsplit :=
      sliceCursorAfter_unsplit_of_append_pl (g.q + 0x920#64) g.encPtr pfx (fl.enc ++ rest)
        (fl.payload ++ rest) (fl_payload_rest_len_le_pl fl rest)
    rw [hpfx] at hunsplit
    unfold overDecHeap overDecHeapExt
    rw [← hunsplit, stackAt_sub_eq_key_pl g.q overDecStackX SpqrH.decodeVarint2StackX (by decide) (by decide)]
    ac_rfl
  rw [hheap_unsplit]
  refine sepWPp_intro_overDecJtabByte_pl (fun R hR => rodata_overDecJtab_placed_intro hcro2.2 hR) fl ?_
  refine SepWPp_bind_sepWP_frame_cro_key_pl hcro2
    (overDecKey_jtab_sepWP_placed ext s0 s2 g fl hregs2 hx0_2 hx1_2)
    rfl
    fun sf hpcf hrunf hLf hcrof hregsf => ?_
  apply drop_left_sepWPp_pl
  rcases hregsf with ⟨hspf, half, htrf, hx0f, hx22f,
    hx19f, hx20f, hx26f, hx21f, hx24f, hx25f, hx27f, hx28f, hx29f, hvregsf⟩
  refine SepWPp.done hpcf hrunf
    ⟨⟨hcrof, hpcf, hrunf, hspf, half, htrf, hLf,
      hx19f, hx20f, hx26f, hx21f, hx24f, hx25f, hx27f, hx28f, hx29f, hvregsf⟩,
     hx0f, hx22f, Entails.refl _⟩

end Cro

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
