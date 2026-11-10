/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IkpTryFrom.LoopError
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Decode
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

/-!
# `IdentityKeyPair::try_from` Loop Key Varint Decode

Verifies the protobuf key varint decode header inside `<IdentityKeyPair as TryFrom<&[u8]>>::try_from`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IkpTryFrom

open CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section LoopVarintStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_lv (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_lv (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPState_lv (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_advancePC_lv (s : State) : s.advancePC.sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg64_gpr_lv (s : State) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg64 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg32_gpr_lv (s : State) (idx : BitVec 5) (val : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg_gpr_lv (s : State) (w : Width) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg w (Reg.gpr idx) val).sp = s.sp := by cases w <;> cases s <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_lv (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_lv (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPState_lv (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_lv (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_lv (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPState_lv (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_lv (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_lv (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPState_lv (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

end LoopVarintStateSimp

theorem decodeVarintSlow_304_cps {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext)
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 304#64)
    (hrun : s.status = .Running)
    (hregs : IkpLoopRegs img s0 sp' x.ret s)
    (hx23 : s.readReg64 .x23 = sp' + 32#64)
    (hx22 : s.readReg64 .x22 = sp' + 40#64)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 220#64 →
      s1.status = .Running →
      IkpLoopRegs img s0 sp' x.ret s1 →
      s1.readReg64 .x23 = sp' + 32#64 →
      s1.readReg64 .x22 = sp' + 40#64 →
      s1.readReg64 .x20 = key →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
          ikpLoopCommon img A sp' x.ret bs.length m)
        (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
        (tryFromQp s0))
    (hnone : decodeVarint bs = none →
      IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr bs ∗
        ikpLoopCommon img A sp' x.ret bs.length m)
      (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have hcall := ikp_varintSlow_ok hC
  have herr := @decodeErr_616_wp img C A S ext hC d x s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    304 20
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
  examples_hide_fetches
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have hsp_subst := hregs.base.sp
  subst hsp_subst
  have _hsp_align := hregs.base.spAligned
  have _hx29 := hregs.x29
  have hstack := stackAt_sub_split s.sp (64 + 2 * extHookStack) (skipFieldStackX 100)
  unfold sliceCursorAt ikpLoopCommon
  simp only [hstack, sepConj_assoc]
  refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
    (mid := entry + bv% (
      (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>") -
      (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_tryFrom (s.sp + 168#64, s.sp + 32#64, ptr, bs) hcall
    (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (by tryFromPost_sp_align hregs.base.spAligned) hF1 hsym1
    (ret_pc := entry + bv% (312)) (by simp [*, arm64_norm])
    (by simp [*, hregs.base.trace, arm64_norm])
    (T := ((s.sp + 168#64) ↦₆₄ (s.sp + 32#64)) ∗ ((s.sp + 32#64) ↦₆₄ ptr) ∗
      ((s.sp + 32#64 + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs) ∗
      A.pool ∗ stackAt s.sp (64 + 2 * extHookStack))
    (φ := bs.length < 18446744073709551616)
    (by simp [*, decodeVarintSlowSpecWithStack, arm64_norm])
    (by omega)
    (by sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs1 := hregs.of_steps hF1 hsym1 rfl
    (by simp [*, hregs.base.trace, arm64_norm])
    (by simp [*, hregs.base.x26, arm64_norm])
    (by simp [*, hregs.base.x27, arm64_norm])
    (by simp [*, hregs.base.x28, arm64_norm])
    (by simp [*, arm64_norm]) (by simp [*, hregs.x19, arm64_norm])
    (by simp [*, hregs.x21, arm64_norm]) (by simp [*, hregs.x24, arm64_norm])
  have hx23_2 : s2.readReg64 .x23 = s.sp + 32#64 :=
    hcs2.2.2.2.2.1.trans (by simp [*, arm64_norm])
  have hx22_2 : s2.readReg64 .x22 = s.sp + 40#64 :=
    hcs2.2.2.2.1.trans (by simp [*, arm64_norm])
  dsimp only [decodeVarintSlowSpecWithStack]
  rw [VarintBridge.decodeVarint_eq_varintSlow bs]
  cases hd : decodeVarint bs with
  | some p =>
    rcases p with ⟨key, rest⟩
    dsimp only [Option.map]
    obtain ⟨k, _, _hkl, hrest⟩ := decodeVarint_suffix hd
    have hlen_sub : bs.length - (bs.length - rest.length) = rest.length := by
      rw [hrest, List.length_drop]; omega
    rw [hlen_sub, sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun ⟨hx0_2, hx1_2⟩ => ?_
    have _hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    have _hx1_2' : s2.readReg64 (Reg.gpr 1#5) = key := hx1_2
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hF2 hsym2
      (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (220)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
    intro hF3 hsym3
    refine Wire.SepWPp.mono_pre
      (P' := sliceCursorAfter (s.sp + 32#64) ptr bs rest ∗
        ikpLoopCommon img A s.sp x.ret bs.length m)
      (by
        apply entails_of_eq
        unfold sliceCursorAfter ikpLoopCommon
        rw [hstack]
        simp only [arm64_norm]
        ac_rfl) ?_
    exact hcont key rest _ hd
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (hregs2.of_steps hF3 hsym3
        (by simp [*, hregs2.base.sp, arm64_norm])
        (by simp [*, hregs2.base.trace, arm64_norm])
        (by simp [*, hregs2.base.x26, arm64_norm])
        (by simp [*, hregs2.base.x27, arm64_norm])
        (by simp [*, hregs2.base.x28, arm64_norm])
        (by simp [*, hregs2.x29, arm64_norm])
        (by simp [*, hregs2.x19, arm64_norm])
        (by simp [*, hregs2.x21, arm64_norm])
        (by simp [*, hregs2.x24, arm64_norm]))
      (by simp [*, arm64_norm])
      (by simp [*, arm64_norm])
      (by simp [*, arm64_norm])
  | none =>
    dsimp only [Option.map]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun ⟨hx0_1, _hx1_ne⟩ => ?_
    have _hx0_1' : s2.readReg64 (Reg.gpr 0#5) = 1#64 := hx0_1
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hF2 hsym2
      (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (616)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
    intro hF3 hsym3
    have hpair := pointsTo64_pair_entails_memRegion16 (s.sp + 32#64)
      (ptr + BitVec.ofNat 64 (min 10 bs.length))
      (BitVec.ofNat 64 (bs.length - min 10 bs.length))
    refine Wire.SepWPp.mono_pre
      (P' := memRegion s.sp 32 ∗
        memRegion (s.sp + 32#64) 16 ∗
        ikpStructOf A (s.sp + 48#64) m ∗
        memRegion (s.sp + 96#64) 48 ∗
        ((s.sp + 168#64) ↦₆₄ (s.sp + 32#64)) ∗
        memRegion x.ret 72 ∗
        (ptr ↦ₛ bs) ∗
        logOff img ∗
        A.pool ∗
        stackAt s.sp (skipFieldStackX 100) ∗
        decodeErrorAt A (s2.readReg64 (Reg.gpr 1#5)))
      (by
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono hpair
            (sepConj_mono (ikpStructLoopOf_entails_of A (s.sp + 48#64) bs.length m)
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (decodeErrorWith_entails_at A (s2.readReg64 (Reg.gpr 1#5)) 0)))))))))))
        rw [hstack]
        apply entails_of_eq
        simp only [arm64_norm]
        ac_rfl) ?_
    exact herr (hnone hd)
      (hregs2.base.of_steps hF3 hsym3
        (by simp [*, hregs2.base.sp, arm64_norm])
        (by simp [*, hregs2.base.trace, arm64_norm])
        (by simp [*, hregs2.base.x26, arm64_norm])
        (by simp [*, hregs2.base.x27, arm64_norm])
        (by simp [*, hregs2.base.x28, arm64_norm]))
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, hregs2.x19, arm64_norm])
      (by simp [*, hregs2.x24, arm64_norm])
      (by simp [*, arm64_norm])

theorem decodeVarintSlice_168_cps {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext)
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 168#64)
    (hrun : s.status = .Running)
    (hregs : IkpLoopRegs img s0 sp' x.ret s)
    (hx23 : s.readReg64 .x23 = sp' + 32#64)
    (hx22 : s.readReg64 .x22 = sp' + 40#64)
    (hx1 : s.readReg64 .x1 = ptr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hlen : bs.length < 2 ^ 63)
    (hpre_slice : VarintSlicePre bs)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 220#64 →
      s1.status = .Running →
      IkpLoopRegs img s0 sp' x.ret s1 →
      s1.readReg64 .x23 = sp' + 32#64 →
      s1.readReg64 .x22 = sp' + 40#64 →
      s1.readReg64 .x20 = key →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
          ikpLoopCommon img A sp' x.ret bs.length m)
        (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
        (tryFromQp s0))
    (hnone : decodeVarint bs = none →
      IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr bs ∗
        ikpLoopCommon img A sp' x.ret bs.length m)
      (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have hcall := ikp_varintSlice_ok d
  have herr := @decodeErr_616_wp img C A S ext hC d x s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    168 52
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    840 8
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
  examples_hide_fetches
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have hsp_subst := hregs.base.sp
  subst hsp_subst
  have _hsp_align := hregs.base.spAligned
  have _hx29 := hregs.x29
  have _hx1' : s.readReg64 (Reg.gpr 1#5) = ptr := hx1
  have _hx2' : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := hx2
  have hx2_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hstack := stackAt_sub_split s.sp decodeVarintSliceStackX (skipFieldStackX 100)
  unfold sliceCursorAt ikpLoopCommon
  simp only [hstack, ikpMem48_split24 s.sp, sepConj_assoc]
  refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
    (mid := entry + bv% (2 ^ 64 +
      (ls_off% "prost::encoding::varint::decode_varint_slice") -
      (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_tryFrom ⟨s.sp + 96#64, ptr, bs⟩ hcall
    (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (by tryFromPost_sp_align hregs.base.spAligned) hF1 hsym1
    (ret_pc := entry + bv% (176)) (by simp [*, arm64_norm])
    (by simp [*, hregs.base.trace, arm64_norm])
    (T := memRegion (s.sp + 96#64) 24 ∗ (ptr ↦ₛ bs) ∗
      A.pool ∗ stackAt s.sp decodeVarintSliceStackX)
    (φ := bs.length < 9223372036854775808 ∧ VarintSlicePre bs)
    (by simp [*, decodeVarintSliceSpecX, arm64_norm])
    ⟨hlen, hpre_slice⟩
    (by sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs1 := hregs.of_steps hF1 hsym1 rfl
    (by simp [*, hregs.base.trace, arm64_norm])
    (by simp [*, hregs.base.x26, arm64_norm])
    (by simp [*, hregs.base.x27, arm64_norm])
    (by simp [*, hregs.base.x28, arm64_norm])
    (by simp [*, arm64_norm]) (by simp [*, hregs.x19, arm64_norm])
    (by simp [*, hregs.x21, arm64_norm]) (by simp [*, hregs.x24, arm64_norm])
  have hx23_2 : s2.readReg64 (Reg.gpr 23#5) = s.sp + 32#64 :=
    hcs2.2.2.2.2.1.trans (by simp [*, arm64_norm])
  have hx22_2 : s2.readReg64 (Reg.gpr 22#5) = s.sp + 40#64 :=
    hcs2.2.2.2.1.trans (by simp [*, arm64_norm])
  dsimp only [decodeVarintSliceSpecX]
  cases hd : decodeVarint bs with
  | some p =>
    rcases p with ⟨key, rest⟩
    dsimp only [varintSliceResultAt]
    obtain ⟨k, _, _hkl, hrest⟩ := decodeVarint_suffix hd
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    have hlen64 : bs.length < 2 ^ 64 := by omega
    have hrest64 : rest.length < 2 ^ 64 := by omega
    have hsub64 : bs.length - rest.length < 2 ^ 64 := by omega
    have hsub_bv :
        BitVec.ofNat 64 bs.length - BitVec.ofNat 64 (bs.length - rest.length) =
          BitVec.ofNat 64 rest.length := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64, Nat.mod_eq_of_lt hrest64]
      omega
    have hult_false :
        (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 (bs.length - rest.length)) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64,
        decide_eq_false_iff_not]
      omega
    rw [pointsTo64_zero_split32 (s.sp + 96#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hF2 hsym2
      (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp
    have _hx29_2 : s2.readReg64 (Reg.gpr 29#5) = s.sp + 144#64 := hregs2.x29
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (220)) ?_
    wp_steps
    wp_if hcc
    · exfalso
      rw [← hrest] at hcc
      exact Bool.false_ne_true (hult_false.symm.trans hcc)
    · wp_steps
      refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
      intro hF3 hsym3
      have hscr := ikpScratch24_ok_entails_mem48 s.sp key
        (BitVec.ofNat 64 (bs.length - rest.length))
      refine Wire.SepWPp.mono_pre
        (P' := sliceCursorAfter (s.sp + 32#64) ptr bs rest ∗
          ikpLoopCommon img A s.sp x.ret bs.length m)
        (by
          unfold sliceCursorAfter ikpLoopCommon
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left hscr))))
          rw [hstack]
          apply entails_of_eq
          simp only [← hrest, hsub_bv, arm64_norm]
          ac_rfl) ?_
      exact hcont key rest _ hd
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (hregs2.of_steps hF3 hsym3
          (by simp [*, hregs2.base.sp, arm64_norm])
          (by simp [*, hregs2.base.trace, arm64_norm])
          (by simp [*, hregs2.base.x26, arm64_norm])
          (by simp [*, hregs2.base.x27, arm64_norm])
          (by simp [*, hregs2.base.x28, arm64_norm])
          (by simp [*, hregs2.x29, arm64_norm])
          (by simp [*, hregs2.x19, arm64_norm])
          (by simp [*, hregs2.x21, arm64_norm])
          (by simp [*, hregs2.x24, arm64_norm]))
        (by simp [*, arm64_norm])
        (by simp [*, arm64_norm])
        (by simp [*, arm64_norm])
  | none =>
    dsimp only [varintSliceResultAt]
    rw [pointsTo64_one_split32 (s.sp + 96#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm]
    refine Wire.SepWPp.exists_pre fun e => Wire.SepWPp.pure_pre fun _he_ne => ?_
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hF2 hsym2
      (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp
    have _hx29_2 : s2.readReg64 (Reg.gpr 29#5) = s.sp + 144#64 := hregs2.x29
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (616)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
    intro hF3 hsym3
    have hpair := pointsTo64_pair_entails_memRegion16 (s.sp + 32#64) ptr
      (BitVec.ofNat 64 bs.length)
    have hscr := ikpScratch24_err_entails_mem48 s.sp e
    refine Wire.SepWPp.mono_pre
      (P' := memRegion s.sp 32 ∗
        memRegion (s.sp + 32#64) 16 ∗
        ikpStructOf A (s.sp + 48#64) m ∗
        memRegion (s.sp + 96#64) 48 ∗
        ((s.sp + 168#64) ↦₆₄ (s.sp + 32#64)) ∗
        memRegion x.ret 72 ∗
        (ptr ↦ₛ bs) ∗
        logOff img ∗
        A.pool ∗
        stackAt s.sp (skipFieldStackX 100) ∗
        decodeErrorAt A e)
      (by
        refine Entails.trans ?_
          (sepConj_mono_right
            (sepConj_mono hpair
              (sepConj_mono (ikpStructLoopOf_entails_of A (s.sp + 48#64) bs.length m)
                (sepConj_mono hscr
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                      (decodeErrorWith_entails_at A e 0)))))))))))
        rw [hstack]
        apply entails_of_eq
        simp only [arm64_norm]
        ac_rfl) ?_
    exact herr (hnone hd)
      (hregs2.base.of_steps hF3 hsym3
        (by simp [*, hregs2.base.sp, arm64_norm])
        (by simp [*, hregs2.base.trace, arm64_norm])
        (by simp [*, hregs2.base.x26, arm64_norm])
        (by simp [*, hregs2.base.x27, arm64_norm])
        (by simp [*, hregs2.base.x28, arm64_norm]))
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, hregs2.x19, arm64_norm])
      (by simp [*, hregs2.x24, arm64_norm])
      (by simp [*, arm64_norm])

theorem decodeVarintMulti_148_cps {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext)
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 148#64)
    (hrun : s.status = .Running)
    (hregs : IkpLoopRegs img s0 sp' x.ret s)
    (hx23 : s.readReg64 .x23 = sp' + 32#64)
    (hx22 : s.readReg64 .x22 = sp' + 40#64)
    (hx1 : s.readReg64 .x1 = ptr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hne : bs ≠ [])
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 220#64 →
      s1.status = .Running →
      IkpLoopRegs img s0 sp' x.ret s1 →
      s1.readReg64 .x23 = sp' + 32#64 →
      s1.readReg64 .x22 = sp' + 40#64 →
      s1.readReg64 .x20 = key →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
          ikpLoopCommon img A sp' x.ret bs.length m)
        (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
        (tryFromQp s0))
    (hnone : decodeVarint bs = none →
      IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr bs ∗
        ikpLoopCommon img A sp' x.ret bs.length m)
      (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have hslice := @decodeVarintSlice_168_cps img C A S ext hC d x s0
  have hslow := @decodeVarintSlow_304_cps img C A S ext hC d x s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    148 20
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
  examples_hide_fetches
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have _hsp_eq := hregs.base.sp
  have _hsp_align := hregs.base.spAligned
  have _hx1' : s.readReg64 (Reg.gpr 1#5) = ptr := hx1
  have _hx2' : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := hx2
  have _hlen_pos : 1 ≤ bs.length := List.length_pos_of_ne_nil hne
  have hlen64 : bs.length < 2 ^ 64 := by omega
  by_cases hlen11 : 11 ≤ bs.length
  · have _hhi : (10#64).ult (BitVec.ofNat 64 bs.length) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, decide_eq_true_eq]
      omega
    refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
      (mid := entry + bv% (168)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
    intro hF1 hsym1
    exact hslice
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (hregs.of_steps hF1 hsym1
        (by simp [*, hregs.base.sp, arm64_norm])
        (by simp [*, hregs.base.trace, arm64_norm])
        (by simp [*, hregs.base.x26, arm64_norm])
        (by simp [*, hregs.base.x27, arm64_norm])
        (by simp [*, hregs.base.x28, arm64_norm])
        (by simp [*, hregs.x29, arm64_norm])
        (by simp [*, hregs.x19, arm64_norm])
        (by simp [*, hregs.x21, arm64_norm])
        (by simp [*, hregs.x24, arm64_norm]))
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      hlen (Or.inl hlen11) hcont hnone
  · have _hhi : (10#64).ult (BitVec.ofNat 64 bs.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, decide_eq_false_iff_not]
      omega
    have hlast_addr :
        ptr + BitVec.ofNat 64 bs.length + bv% (2 ^ 64 - 1) =
          ptr + BitVec.ofNat 64 (bs.length - 1) := by
      have heq : bs.length = (bs.length - 1) + 1 := by omega
      have h1_eq : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 (bs.length - 1) + 1#64 := by
        conv_lhs => rw [heq]
        exact BitVec.ofNat_add (bs.length - 1) 1
      rw [h1_eq]; bv_omega
    by_cases hlast : (bs.getLast hne).toNat ≤ 0x7F
    · have _hbit31 := (signExtend32_bit31_eq_false_iff (bs.getLast hne)).mpr hlast
      unfold sliceCursorAt
      rw [Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]
      simp only [sepConj_assoc]
      refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
        (mid := entry + bv% (168)) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
      intro hF1 hsym1
      refine Wire.SepWPp.mono_pre
        (P' := sliceCursorAt (sp' + 32#64) ptr bs ∗ ikpLoopCommon img A sp' x.ret bs.length m)
        (by
          apply entails_of_eq
          unfold sliceCursorAt
          rw [Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]
          simp only [arm64_norm]) ?_
      exact hslice
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (hregs.of_steps hF1 hsym1
          (by simp [*, hregs.base.sp, arm64_norm])
          (by simp [*, hregs.base.trace, arm64_norm])
          (by simp [*, hregs.base.x26, arm64_norm])
          (by simp [*, hregs.base.x27, arm64_norm])
          (by simp [*, hregs.base.x28, arm64_norm])
          (by simp [*, hregs.x29, arm64_norm])
          (by simp [*, hregs.x19, arm64_norm])
          (by simp [*, hregs.x21, arm64_norm])
          (by simp [*, hregs.x24, arm64_norm]))
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        hlen (Or.inr ⟨hne, hlast⟩) hcont hnone
    · have _hbit31 := (signExtend32_bit31_eq_true_iff (bs.getLast hne)).mpr (by omega)
      unfold sliceCursorAt
      rw [Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]
      simp only [sepConj_assoc]
      refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
        (mid := entry + bv% (304)) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
      intro hF1 hsym1
      refine Wire.SepWPp.mono_pre
        (P' := sliceCursorAt (sp' + 32#64) ptr bs ∗ ikpLoopCommon img A sp' x.ret bs.length m)
        (by
          apply entails_of_eq
          unfold sliceCursorAt
          rw [Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]
          simp only [arm64_norm]) ?_
      exact hslow
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (hregs.of_steps hF1 hsym1
          (by simp [*, hregs.base.sp, arm64_norm])
          (by simp [*, hregs.base.trace, arm64_norm])
          (by simp [*, hregs.base.x26, arm64_norm])
          (by simp [*, hregs.base.x27, arm64_norm])
          (by simp [*, hregs.base.x28, arm64_norm])
          (by simp [*, hregs.x29, arm64_norm])
          (by simp [*, hregs.x19, arm64_norm])
          (by simp [*, hregs.x21, arm64_norm])
          (by simp [*, hregs.x24, arm64_norm]))
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        hlen hcont hnone

theorem decodeVarint_124_cps {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext)
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 124#64)
    (hrun : s.status = .Running)
    (hregs : IkpLoopRegs img s0 sp' x.ret s)
    (hx23 : s.readReg64 .x23 = sp' + 32#64)
    (hx22 : s.readReg64 .x22 = sp' + 40#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint (b0 :: bs1) = some (key, rest) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 220#64 →
      s1.status = .Running →
      IkpLoopRegs img s0 sp' x.ret s1 →
      s1.readReg64 .x23 = sp' + 32#64 →
      s1.readReg64 .x22 = sp' + 40#64 →
      s1.readReg64 .x20 = key →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr (b0 :: bs1) rest ∗
          ikpLoopCommon img A sp' x.ret (b0 :: bs1).length m)
        (ikpExitPost img A s0 sp' x.ret ptr (b0 :: bs1) (IdentityKeyPair.tryFrom x.bytes))
        (tryFromQp s0))
    (hnone : decodeVarint (b0 :: bs1) = none →
      IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr (b0 :: bs1) ∗
        ikpLoopCommon img A sp' x.ret (b0 :: bs1).length m)
      (ikpExitPost img A s0 sp' x.ret ptr (b0 :: bs1) (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have hmulti := @decodeVarintMulti_148_cps img C A S ext hC d x s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    124 24
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    212 8
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
  examples_hide_fetches
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have _hsp_eq := hregs.base.sp
  have _hsp_align := hregs.base.spAligned
  have _hx23' : s.readReg64 (Reg.gpr 23#5) = sp' + 32#64 := hx23
  have _hx22' : s.readReg64 (Reg.gpr 22#5) = sp' + 40#64 := hx22
  have _hx2' : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (b0 :: bs1).length := hx2
  by_cases hb0 : b0.toNat ≤ 0x7F
  · have _hbit63 := (signExtend64_bit63_eq_false_iff b0).mpr hb0
    have hd := decodeVarint_cons_of_le b0 bs1 hb0
    have hsub1 :
        BitVec.ofNat 64 (bs1.length + 1) - 1#64 = BitVec.ofNat 64 bs1.length := by
      have h1_eq : BitVec.ofNat 64 (bs1.length + 1) = BitVec.ofNat 64 bs1.length + 1#64 :=
        BitVec.ofNat_add bs1.length 1
      rw [h1_eq]; bv_omega
    unfold sliceCursorAt
    rw [pointsToBytes_cons ptr b0 bs1]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
      (mid := entry + bv% (220)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
    intro hF1 hsym1
    have hse := signExtend64_eq_zeroExtend64_of_le b0 hb0
    refine Wire.SepWPp.mono_pre
      (P' := sliceCursorAfter (sp' + 32#64) ptr (b0 :: bs1) bs1 ∗
        ikpLoopCommon img A sp' x.ret (b0 :: bs1).length m)
      (by
        apply entails_of_eq
        unfold sliceCursorAfter
        rw [pointsToBytes_cons ptr b0 bs1]
        simp only [List.length_cons, Nat.add_sub_cancel_left, hsub1, arm64_norm]) ?_
    exact hcont (b0.zeroExtend 64) bs1 _ hd
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (hregs.of_steps hF1 hsym1
        (by simp [*, hregs.base.sp, arm64_norm])
        (by simp [*, hregs.base.trace, arm64_norm])
        (by simp [*, hregs.base.x26, arm64_norm])
        (by simp [*, hregs.base.x27, arm64_norm])
        (by simp [*, hregs.base.x28, arm64_norm])
        (by simp [*, hregs.x29, arm64_norm])
        (by simp [*, hregs.x19, arm64_norm])
        (by simp [*, hregs.x21, arm64_norm])
        (by simp [*, hregs.x24, arm64_norm]))
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, arm64_norm])
  · have _hbit63 := (signExtend64_bit63_eq_true_iff b0).mpr (by omega)
    unfold sliceCursorAt
    rw [pointsToBytes_cons ptr b0 bs1]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
      (mid := entry + bv% (148)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.mono_pre
      (P' := sliceCursorAt (sp' + 32#64) ptr (b0 :: bs1) ∗
        ikpLoopCommon img A sp' x.ret (b0 :: bs1).length m)
      (by
        apply entails_of_eq
        unfold sliceCursorAt
        rw [pointsToBytes_cons ptr b0 bs1]
        simp only [arm64_norm]) ?_
    exact hmulti
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (hregs.of_steps hF1 hsym1
        (by simp [*, hregs.base.sp, arm64_norm])
        (by simp [*, hregs.base.trace, arm64_norm])
        (by simp [*, hregs.base.x26, arm64_norm])
        (by simp [*, hregs.base.x27, arm64_norm])
        (by simp [*, hregs.base.x28, arm64_norm])
        (by simp [*, hregs.x29, arm64_norm])
        (by simp [*, hregs.x19, arm64_norm])
        (by simp [*, hregs.x21, arm64_norm])
        (by simp [*, hregs.x24, arm64_norm]))
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (List.cons_ne_nil b0 bs1) hlen hcont hnone

theorem decodeKey_220_cps {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext)
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {key : BitVec 64} {bs rest : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hdv : decodeVarint bs = some (key, rest))
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 220#64)
    (hrun : s.status = .Running)
    (hregs : IkpLoopRegs img s0 sp' x.ret s)
    (hx20 : s.readReg64 .x20 = key)
    (hcont : ∀ (tag : Nat) (wt : WireType) (s1 : State),
      decodeKey bs = some ((tag, wt), rest) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 248#64 →
      s1.status = .Running →
      IkpLoopRegs img s0 sp' x.ret s1 →
      s1.readReg64 .x0 = BitVec.ofNat 64 wt.toNat →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
          ikpLoopCommon img A sp' x.ret bs.length m)
        (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
        (tryFromQp s0))
    (hnone : decodeKey bs = none →
      IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
        ikpLoopCommon img A sp' x.ret bs.length m)
      (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have herr := @decodeErrorFrom_600_wp img C A S ext hC d x s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    220 28
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    572 28
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
  examples_hide_fetches
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have _hsp_eq := hregs.base.sp
  have _hsp_align := hregs.base.spAligned
  have _hx20' : s.readReg64 (Reg.gpr 20#5) = key := hx20
  have _hx29' : s.readReg64 (Reg.gpr 29#5) = sp' + 144#64 := hregs.x29
  have _hx24' : s.readReg64 (Reg.gpr 24#5) = speWord 9 := hregs.x24
  by_cases hkey32 : 2 ^ 32 ≤ key.toNat
  · have hdk : decodeKey bs = none := by
      unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte]
    have _hcbnz := key_lsr32_ne_zero_of_ge key hkey32
    unfold ikpLoopCommon
    rw [ikpMem48_split_96_104_112 sp']
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun w1 => Wire.SepWPp.exists_pre fun w0 => ?_
    refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
      (mid := entry + bv% (600)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
    intro hF1 hsym1
    have hcur := sliceCursorAfter_entails_memRegion (sp' + 32#64) ptr bs rest
    have hm40 := ikpPointsTo64_104_mem32_entails_mem40 sp' key
    refine Wire.SepWPp.mono_pre
      (P' := memRegion sp' 32 ∗
        memRegion (sp' + 32#64) 16 ∗
        ikpStructOf A (sp' + 48#64) m ∗
        ((sp' + 96#64) ↦₆₄ w0) ∗ memRegion (sp' + 104#64) 40 ∗
        ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
        memRegion x.ret 72 ∗
        (ptr ↦ₛ bs) ∗
        logOff img ∗
        A.pool ∗
        stackAt sp' (skipFieldStackX 100))
      (by
        refine Entails.trans ?_
          (show memRegion sp' 32 ∗ (memRegion (sp' + 32#64) 16 ∗ (ptr ↦ₛ bs)) ∗
              ikpStructOf A (sp' + 48#64) m ∗ ((sp' + 96#64) ↦₆₄ w0) ∗
              memRegion (sp' + 104#64) 40 ∗ ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
              memRegion x.ret 72 ∗ logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100) ⊢ _
            by apply entails_of_eq; ac_rfl)
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono hcur
            (sepConj_mono (ikpStructLoopOf_entails_of A (sp' + 48#64) bs.length m)
              (sepConj_mono_right (sepConj_mono_left hm40)))))
        apply entails_of_eq
        simp only [arm64_norm]
        ac_rfl) ?_
    exact herr (hnone hdk)
      (hregs.of_steps hF1 hsym1
        (by simp [*, hregs.base.sp, arm64_norm])
        (by simp [*, hregs.base.trace, arm64_norm])
        (by simp [*, hregs.base.x26, arm64_norm])
        (by simp [*, hregs.base.x27, arm64_norm])
        (by simp [*, hregs.base.x28, arm64_norm])
        (by simp [*, hregs.x29, arm64_norm])
        (by simp [*, hregs.x19, arm64_norm])
        (by simp [*, hregs.x21, arm64_norm])
        (by simp [*, hregs.x24, arm64_norm]))
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, KindNoHeap, speWord, arm64_norm])
  · have hkey_lt : key.toNat < 2 ^ 32 := by omega
    have _hcbnz := key_lsr32_eq_zero_of_lt key hkey_lt
    cases hwt : WireType.ofNat? (key.toNat % 8) with
    | none =>
      have hdk : decodeKey bs = none := by
        unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt]
      have hge6 : 6 ≤ key.toNat % 8 :=
        (WireType.ofNat?_eq_none_iff (key.toNat % 8) (by omega)).mp hwt
      have _hbcs := key_and7_ule6_of_ge key hge6
      unfold ikpLoopCommon
      rw [ikpMem48_split_96_104_112 sp']
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine Wire.SepWPp.exists_pre fun w1 => Wire.SepWPp.exists_pre fun w0 => ?_
      refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
        (mid := entry + bv% (600)) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
      intro hF1 hsym1
      have hcur := sliceCursorAfter_entails_memRegion (sp' + 32#64) ptr bs rest
      have hm40 := ikpPointsTo64_104_mem32_entails_mem40 sp' (key &&& 7#64)
      refine Wire.SepWPp.mono_pre
        (P' := memRegion sp' 32 ∗
          memRegion (sp' + 32#64) 16 ∗
          ikpStructOf A (sp' + 48#64) m ∗
          ((sp' + 96#64) ↦₆₄ w0) ∗ memRegion (sp' + 104#64) 40 ∗
          ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
          memRegion x.ret 72 ∗
          (ptr ↦ₛ bs) ∗
          logOff img ∗
          A.pool ∗
          stackAt sp' (skipFieldStackX 100))
        (by
          refine Entails.trans ?_
            (show memRegion sp' 32 ∗ (memRegion (sp' + 32#64) 16 ∗ (ptr ↦ₛ bs)) ∗
                ikpStructOf A (sp' + 48#64) m ∗ ((sp' + 96#64) ↦₆₄ w0) ∗
                memRegion (sp' + 104#64) 40 ∗ ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
                memRegion x.ret 72 ∗ logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100) ⊢ _
              by apply entails_of_eq; ac_rfl)
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono hcur
              (sepConj_mono (ikpStructLoopOf_entails_of A (sp' + 48#64) bs.length m)
                (sepConj_mono_right (sepConj_mono_left hm40)))))
          apply entails_of_eq
          simp only [arm64_norm]
          ac_rfl) ?_
      exact herr (hnone hdk)
        (hregs.of_steps hF1 hsym1
          (by simp [*, hregs.base.sp, arm64_norm])
          (by simp [*, hregs.base.trace, arm64_norm])
          (by simp [*, hregs.base.x26, arm64_norm])
          (by simp [*, hregs.base.x27, arm64_norm])
          (by simp [*, hregs.base.x28, arm64_norm])
          (by simp [*, hregs.x29, arm64_norm])
          (by simp [*, hregs.x19, arm64_norm])
          (by simp [*, hregs.x21, arm64_norm])
          (by simp [*, hregs.x24, arm64_norm]))
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, KindNoHeap, arm64_norm])
    | some wt =>
      have hlt6 : key.toNat % 8 < 6 := WireType.lt_six_of_ofNat?_eq_some hwt
      have _hbcs := key_and7_ule6_of_lt key hlt6
      by_cases htag0 : key.toNat / 8 < 1
      · have hdk : decodeKey bs = none := by
          unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt, htag0]
        have _hcbz := key_tag32_eq_zero_of_lt1 key hkey_lt htag0
        unfold ikpLoopCommon
        rw [ikpMem48_split8 sp', ProofLib.memRegion_eight (sp' + 96#64)]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine Wire.SepWPp.exists_pre fun w0 => ?_
        refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
          (mid := entry + bv% (600)) ?_
        wp_steps
        refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
        intro hF1 hsym1
        have hcur := sliceCursorAfter_entails_memRegion (sp' + 32#64) ptr bs rest
        refine Wire.SepWPp.mono_pre
          (P' := memRegion sp' 32 ∗
            memRegion (sp' + 32#64) 16 ∗
            ikpStructOf A (sp' + 48#64) m ∗
            ((sp' + 96#64) ↦₆₄ w0) ∗ memRegion (sp' + 104#64) 40 ∗
            ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
            memRegion x.ret 72 ∗
            (ptr ↦ₛ bs) ∗
            logOff img ∗
            A.pool ∗
            stackAt sp' (skipFieldStackX 100))
          (by
            refine Entails.trans ?_
              (show memRegion sp' 32 ∗ (memRegion (sp' + 32#64) 16 ∗ (ptr ↦ₛ bs)) ∗
                  ikpStructOf A (sp' + 48#64) m ∗ ((sp' + 96#64) ↦₆₄ w0) ∗
                  memRegion (sp' + 104#64) 40 ∗ ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
                  memRegion x.ret 72 ∗ logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100) ⊢ _
                by apply entails_of_eq; ac_rfl)
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono hcur
                (sepConj_mono_left
                  (ikpStructLoopOf_entails_of A (sp' + 48#64) bs.length m))))
            apply entails_of_eq
            ac_rfl) ?_
        exact herr (hnone hdk)
          (hregs.of_steps hF1 hsym1
            (by simp [*, hregs.base.sp, arm64_norm])
            (by simp [*, hregs.base.trace, arm64_norm])
            (by simp [*, hregs.base.x26, arm64_norm])
            (by simp [*, hregs.base.x27, arm64_norm])
            (by simp [*, hregs.base.x28, arm64_norm])
            (by simp [*, hregs.x29, arm64_norm])
            (by simp [*, hregs.x19, arm64_norm])
            (by simp [*, hregs.x21, arm64_norm])
            (by simp [*, hregs.x24, arm64_norm]))
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, KindNoHeap, speWord, arm64_norm])
      · have hdk : decodeKey bs = some ((key.toNat / 8, wt), rest) := by
          unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt, htag0]
        have _hcbz := key_tag32_ne_zero_of_ge1 key hkey_lt htag0
        refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
          (mid := entry + bv% (248)) ?_
        wp_steps
        refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
        intro hF1 hsym1
        have htag_eq := key_tag32_zeroExtend64_eq key hkey_lt
        have hand7_eq := key_and7_eq_wt key hwt
        exact hcont (key.toNat / 8) wt _ hdk
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (hregs.of_steps hF1 hsym1
            (by simp [*, hregs.base.sp, arm64_norm])
            (by simp [*, hregs.base.trace, arm64_norm])
            (by simp [*, hregs.base.x26, arm64_norm])
            (by simp [*, hregs.base.x27, arm64_norm])
            (by simp [*, hregs.base.x28, arm64_norm])
            (by simp [*, hregs.x29, arm64_norm])
            (by simp [*, hregs.x19, arm64_norm])
            (by simp [*, hregs.x21, arm64_norm])
            (by simp [*, hregs.x24, arm64_norm]))
          (by simp [*, arm64_norm])
          (by simp [*, arm64_norm])

theorem decodeKey_124_cps {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext)
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 124#64)
    (hrun : s.status = .Running)
    (hregs : IkpLoopRegs img s0 sp' x.ret s)
    (hx23 : s.readReg64 .x23 = sp' + 32#64)
    (hx22 : s.readReg64 .x22 = sp' + 40#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hcont : ∀ (tag : Nat) (wt : WireType) (rest : List (BitVec 8)) (s1 : State),
      decodeKey (b0 :: bs1) = some ((tag, wt), rest) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 248#64 →
      s1.status = .Running →
      IkpLoopRegs img s0 sp' x.ret s1 →
      s1.readReg64 .x0 = BitVec.ofNat 64 wt.toNat →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr (b0 :: bs1) rest ∗
          ikpLoopCommon img A sp' x.ret (b0 :: bs1).length m)
        (ikpExitPost img A s0 sp' x.ret ptr (b0 :: bs1) (IdentityKeyPair.tryFrom x.bytes))
        (tryFromQp s0))
    (hnone : decodeKey (b0 :: bs1) = none →
      IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr (b0 :: bs1) ∗
        ikpLoopCommon img A sp' x.ret (b0 :: bs1).length m)
      (ikpExitPost img A s0 sp' x.ret ptr (b0 :: bs1) (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) :=
  decodeVarint_124_cps hC d hpc hrun hregs hx23 hx22 hx2 hlen
    (fun _key rest s1 hdv hpc1 hrun1 hregs1 _hx23_1 _hx22_1 hx20_1 =>
      decodeKey_220_cps hC d hdv hpc1 hrun1 hregs1 hx20_1
        (fun tag wt s2 hdk => hcont tag wt rest s2 hdk)
        hnone)
    (fun hdv_none => hnone (by simp [decodeKey, hdv_none]))

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IkpTryFrom
