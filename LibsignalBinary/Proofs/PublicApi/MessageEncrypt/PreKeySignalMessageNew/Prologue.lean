/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueFetch
public import LibsignalBinary.Specifications.LibsignalPublicApi
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueClones
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# `PreKeySignalMessage::new` Prologue and `serialized` Buffer Allocation

Packs the 128-byte `wire::PreKeySignalMessage` on the stack (`+0x1ac..+0x1f0`), invokes `encoded_len`
and allocates the `serialized: Vec<u8>` output buffer initialized with `[versionByte x.ver]`
(`+0x1f0..+0x25c`), and composes the full prologue (`+0x000..+0x25c`) reaching `SeamA` or an OOM panic.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Prologue

set_option maxHeartbeats 400000

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split

variable {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel}
  {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {abs : String → Option (State → State)}

/-! ## Wire Struct Stack Packing (`+0x1ac..+0x1f0`) -/

theorem preKeyMsg_store_wire_wp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (x : PreKeyMsgNewCall) (sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr w352 : BitVec 64)
    (w344_32 pkId32 kyberId32 : BitVec 32)
    (hkyCap : kyberCap = match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hpk : ∀ v, x.preKeyId = some v → pkId32 = v)
    (hkyId : ∀ k, x.kp = some k → kyberId32 = k.preKeyId)
    (hmsg_len : x.msg.serialized.length < 2 ^ 63)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 428#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = ikSerPtr)
    (hx8 : s.readReg64 .x8 = 1#64)
    (hx19 : s.readReg64 .x19 = kyberCap)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = 33#64)
    (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = msgCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = bkSerPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 496#64)
      s
      (((sp0 - 352#64) ↦₆₄ w352) ∗
       ((sp0 - 344#64) ↦₃₂ w344_32) ∗
       ((sp0 - 328#64) ↦₃₂ x.spk) ∗
       ((sp0 - 324#64) ↦₃₂ kyberId32) ∗
       ((sp0 - 320#64) ↦₆₄ kyberCopyPtr) ∗
       ((sp0 - 296#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
       ((sp0 - 292#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
       memRegion (sp0 - 272#64) 128 ∗
       optKyberCopyBuf A kyberCopyPtr x.kp ∗
       boxU8Buf A bkSerPtr x.baseKey.serialize ∗
       boxU8Buf A ikSerPtr x.ik.serialize ∗
       boxU8Buf A msgCopyPtr x.msg.serialized)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x0 = sp0 - 272#64 ∧
         sm.readReg64 .x19 = kyberCap ∧
         sm.readReg64 .x20 = (if x.preKeyId.isSome then 1#32 else 0#32).zeroExtend 64 ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧
         sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧
         sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x26 = msgCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = bkSerPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢
          ((sp0 - 352#64) ↦₆₄ ikSerPtr) ∗
          ((sp0 - 344#64) ↦₃₂ x.regId) ∗
          ((sp0 - 328#64) ↦₃₂ x.spk) ∗
          ((sp0 - 324#64) ↦₃₂ kyberId32) ∗
          ((sp0 - 320#64) ↦₆₄ kyberCopyPtr) ∗
          ((sp0 - 296#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
          ((sp0 - 292#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
          wirePreKeySignalMessageAt A
            (x.mkWirePins kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr)
            (sp0 - 272#64) x.protoMsg)) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx0 hx8 hx19 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
  rw [memRegion_wire_128 sp0]
  cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => ?_
  preKeyMsg_fetches_range b (Rust.withPanics ext) 0x1ac 0x1ec
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
  · simp only [State.spAligned, wp_norm, arm64_norm, *]
  · have hpack := pack_wirePreKeySignalMessageAt A x sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr
      msgCopyPtr pkId32 kyberId32 hkyCap hpk hkyId hmsg_len
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hpack)))))))
    simp only [← hkyCap, Option.isSome, arm64_norm]
    exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_store_wire_wp_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (x : PreKeyMsgNewCall) (sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr w352 : BitVec 64)
    (w344_32 pkId32 kyberId32 : BitVec 32)
    (hkyCap : kyberCap = match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hpk : ∀ v, x.preKeyId = some v → pkId32 = v) (hkyId : ∀ k, x.kp = some k → kyberId32 = k.preKeyId)
    (hmsg_len : x.msg.serialized.length < 2 ^ 63) (s : State)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 428#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = ikSerPtr) (hx8 : s.readReg64 .x8 = 1#64)
    (hx19 : s.readReg64 .x19 = kyberCap) (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64) (hx24 : s.readReg64 .x24 = 33#64)
    (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64) (hx26 : s.readReg64 .x26 = msgCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = bkSerPtr) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWP (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 496#64) s
      (((sp0 - 352#64) ↦₆₄ w352) ∗ ((sp0 - 344#64) ↦₃₂ w344_32) ∗ ((sp0 - 328#64) ↦₃₂ x.spk) ∗
       ((sp0 - 324#64) ↦₃₂ kyberId32) ∗ ((sp0 - 320#64) ↦₆₄ kyberCopyPtr) ∗
       ((sp0 - 296#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
       ((sp0 - 292#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
       memRegion (sp0 - 272#64) 128 ∗ optKyberCopyBuf A kyberCopyPtr x.kp ∗
       boxU8Buf A bkSerPtr x.baseKey.serialize ∗ boxU8Buf A ikSerPtr x.ik.serialize ∗
       boxU8Buf A msgCopyPtr x.msg.serialized)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x0 = sp0 - 272#64 ∧
         sm.readReg64 .x19 = kyberCap ∧
         sm.readReg64 .x20 = (if x.preKeyId.isSome then 1#32 else 0#32).zeroExtend 64 ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧ sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧ sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧ sm.readReg64 .x26 = msgCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = bkSerPtr ∧ sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ ((sp0 - 352#64) ↦₆₄ ikSerPtr) ∗ ((sp0 - 344#64) ↦₃₂ x.regId) ∗
          ((sp0 - 328#64) ↦₃₂ x.spk) ∗ ((sp0 - 324#64) ↦₃₂ kyberId32) ∗
          ((sp0 - 320#64) ↦₆₄ kyberCopyPtr) ∗
          ((sp0 - 296#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
          ((sp0 - 292#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
          wirePreKeySignalMessageAt A
            (x.mkWirePins kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr)
            (sp0 - 272#64) x.protoMsg)) :=
  preKeyMsg_store_wire_wp_ext x sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr w352
    w344_32 pkId32 kyberId32 hkyCap hpk hkyId hmsg_len s hpc hrun hsp hsp_align
    hx0 hx8 hx19 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29

theorem preKeyMsg_store_wire_wp {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (x : PreKeyMsgNewCall) (sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr w352 : BitVec 64)
    (w344_32 pkId32 kyberId32 : BitVec 32)
    (hkyCap : kyberCap = match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hpk : ∀ v, x.preKeyId = some v → pkId32 = v)
    (hkyId : ∀ k, x.kp = some k → kyberId32 = k.preKeyId)
    (hmsg_len : x.msg.serialized.length < 2 ^ 63)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 428#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = ikSerPtr)
    (hx8 : s.readReg64 .x8 = 1#64)
    (hx19 : s.readReg64 .x19 = kyberCap)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = 33#64)
    (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = msgCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = bkSerPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 496#64)
      s
      (((sp0 - 352#64) ↦₆₄ w352) ∗
       ((sp0 - 344#64) ↦₃₂ w344_32) ∗
       ((sp0 - 328#64) ↦₃₂ x.spk) ∗
       ((sp0 - 324#64) ↦₃₂ kyberId32) ∗
       ((sp0 - 320#64) ↦₆₄ kyberCopyPtr) ∗
       ((sp0 - 296#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
       ((sp0 - 292#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
       memRegion (sp0 - 272#64) 128 ∗
       optKyberCopyBuf A kyberCopyPtr x.kp ∗
       boxU8Buf A bkSerPtr x.baseKey.serialize ∗
       boxU8Buf A ikSerPtr x.ik.serialize ∗
       boxU8Buf A msgCopyPtr x.msg.serialized)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x0 = sp0 - 272#64 ∧
         sm.readReg64 .x19 = kyberCap ∧
         sm.readReg64 .x20 = (if x.preKeyId.isSome then 1#32 else 0#32).zeroExtend 64 ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧
         sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧
         sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x26 = msgCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = bkSerPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢
          ((sp0 - 352#64) ↦₆₄ ikSerPtr) ∗
          ((sp0 - 344#64) ↦₃₂ x.regId) ∗
          ((sp0 - 328#64) ↦₃₂ x.spk) ∗
          ((sp0 - 324#64) ↦₃₂ kyberId32) ∗
          ((sp0 - 320#64) ↦₆₄ kyberCopyPtr) ∗
          ((sp0 - 296#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
          ((sp0 - 292#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
          wirePreKeySignalMessageAt A
            (x.mkWirePins kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr)
            (sp0 - 272#64) x.protoMsg)) := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs preKeyMsgNewName] at hpc ⊢
  exact SepWP_kit_of_trTrap (preKeyMsg_store_wire_wp_trap x sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr w352 w344_32 pkId32 kyberId32 hkyCap hpk hkyId hmsg_len s hpc hrun hsp hsp_align hx0 hx8 hx19 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29)

/-! ## `encoded_len` Calls and `serialized` Allocation (`+0x1f0..+0x25c`) -/

theorem SepWPp.exists_elim {prog : Program} {ret : BitVec 64} {s : State}
    {α : Type _} {P : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a, SepWPp prog ret s (P a) Q Qp) :
    SepWPp prog ret s (∃∗ a, P a) Q Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨a, hm⟩
  exact h a R hm hL

theorem stackAt_allocHook_split_encodedLen (sp : BitVec 64) :
    stackAt sp allocHookStack =
      stackAt sp preKeyMsgEncodedLenStack ∗ memRegion (sp - 4096#64) 4080 := by
  unfold stackAt allocHookStack preKeyMsgEncodedLenStack
  rw [memRegion_split' (b := sp - 4096#64) (b' := sp - 16#64) (n := 4080) (k := 16)
    (by decide) (bv_sub_add_lit sp 4096 4080).symm (by decide), sepConj_comm]

theorem versionByte_word_eq' (w : BitVec 32) :
    BitVec.zeroExtend 8 (4#64 ||| BitVec.zeroExtend 64 (w <<< 4)) = versionByte (w.setWidth 8) := by
  unfold versionByte currentVersion
  bv_bits

theorem preKeyMsg_alloc_ser_wpp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (hEncLen : PreKeyMsgEncodedLenOk img C A ctl abs)
    (x : PreKeyMsgNewCall) (sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr
      w368 w144 w136 w128 : BitVec 64)
    (ver32 pkId32 : BitVec 32)
    (hkyCap : kyberCap = match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hky_len : ∀ k, x.kp = some k → k.ciphertext.length < 2 ^ 63)
    (hmsg_len : x.msg.serialized.length < 2 ^ 63)
    (hver : ver32.setWidth 8 = x.ver)
    (hfit : x.model.serialized.length < 2 ^ 42)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyMsgNewName + 496#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp0 - 272#64)
    (hx19 : s.readReg64 .x19 = kyberCap)
    (hx20 : s.readReg64 .x20 = (if x.preKeyId.isSome then 1#32 else 0#32).zeroExtend 64)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx24 : s.readReg64 .x24 = 33#64)
    (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = msgCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = bkSerPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyMsgNewName + 604#64)
      s
      (((sp0 - 368#64) ↦₆₄ w368) ∗
       ((sp0 - 332#64) ↦₃₂ ver32) ∗
       wirePreKeySignalMessageAt A
         (x.mkWirePins kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr)
         (sp0 - 272#64) x.protoMsg ∗
       ((sp0 - 144#64) ↦₆₄ w144) ∗
       ((sp0 - 136#64) ↦₆₄ w136) ∗
       ((sp0 - 128#64) ↦₆₄ w128) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = kyberCap ∧
         sm.readReg64 .x20 = (if x.preKeyId.isSome then 1#32 else 0#32).zeroExtend 64 ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧
         sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = bkSerPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢
          ∃∗ serPtr : BitVec 64,
            ((sp0 - 368#64) ↦₆₄ msgCopyPtr) ∗
            ((sp0 - 332#64) ↦₃₂ ver32) ∗
            memRegion (sp0 - 272#64) 128 ∗
            vecU8At A (sp0 - 144#64) (BitVec.ofNat 64 x.model.serialized.length)
              serPtr [versionByte x.ver] ∗
            optKyberCopyBuf A kyberCopyPtr x.kp ∗
            boxU8Buf A bkSerPtr x.baseKey.serialize ∗
            boxU8Buf A ikSerPtr x.ik.serialize ∗
            boxU8Buf A msgCopyPtr x.msg.serialized ∗
            A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) := by
  have hunpack := unpack_wirePreKeySignalMessageAt A x sp0 kyberCap kyberCopyPtr
    bkSerPtr ikSerPtr msgCopyPtr hkyCap hky_len hmsg_len
  have hver_byte :
      BitVec.zeroExtend 8 (4#64 ||| BitVec.zeroExtend 64 (ver32 <<< 4)) = versionByte x.ver := by
    rw [versionByte_word_eq' ver32, hver]
  clear hkyCap hky_len hmsg_len hver
  have henc := preKeyMsg_encodedLen_ok hEncLen
  have hshim := preKeyMsg_shim_ok (b := img.base) (C := C) (ctl := ctl) (abs := abs)
  have halloc := preKeyMsg_alloc_ok (A := A) (b := img.base) (C := C) (ctl := ctl)
    (abs := abs) hA
  have ho204 := @preKeyMsg_oom_at_204 img.base C ctl abs
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have hmod_len : x.model.serialized.length = x.protoMsg.encode.length + 1 :=
    model_serialized_length x
  have hfit62 : x.protoMsg.encode.length + 1 < 2 ^ 62 := by omega
  have hwire_fit : PreKeyMsgWireLengthsFit x.protoMsg :=
    preKeyMsgWireLengthsFit_protoMsg x (by omega)
  clear hfit
  obtain ⟨hovf_ult, hovf_msb, hovf_hi, hovf_add, hovf_toNat⟩ :=
    preKeyMsg_encLen_overflow_checks hfit62
  rw [hovf_add] at hovf_ult hovf_msb
  simp only [arm64_norm] at hx0 hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx27 hx28 hx29
  preKeyMsg_fetches_range img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x1f0 0x200
  preKeyMsg_fetches_range img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x210 0x258
  generalize_entry (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyMsgNewName = entry
  examples_hide_fetches
  let wg := x.mkWirePins kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr
  apply SepWPp.of_sepWP (mid := entry + 100920#64)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.call (x := ⟨sp0 - 272#64, wg, x.protoMsg⟩)
    (F := ((sp0 - 368#64) ↦₆₄ w368) ∗
          ((sp0 - 332#64) ↦₃₂ ver32) ∗
          ((sp0 - 144#64) ↦₆₄ w144) ∗
          ((sp0 - 136#64) ↦₆₄ w136) ∗
          ((sp0 - 128#64) ↦₆₄ w128) ∗
          A.pool ∗ memRegion (sp0 - 368#64 - 4096#64) 4080 ∗
          memRegion (sp0 - 368#64 - 7824#64) 3728)
    henc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    rw [stackAt_preKeyMsgSubStack_to_allocHook (sp0 - 368#64),
        stackAt_allocHook_split_encodedLen (sp0 - 368#64)] at hm
    simp only [preKeyMsgEncodedLenSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  simp only [preKeyMsgEncodedLenSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0_1, htr1⟩ => ?_
  simp only [wp_norm, arm64_norm] at hx0_1 htr1
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x15130))
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.call (x := ())
    (F := ((sp0 - 368#64) ↦₆₄ msgCopyPtr) ∗
          ((sp0 - 332#64) ↦₃₂ ver32) ∗
          wirePreKeySignalMessageAt A wg (sp0 - 272#64) x.protoMsg ∗
          ((sp0 - 144#64) ↦₆₄ w144) ∗
          ((sp0 - 136#64) ↦₆₄ w136) ∗
          ((sp0 - 128#64) ↦₆₄ w128) ∗
          A.pool ∗ stackAt s.sp preKeyMsgEncodedLenStack ∗
          memRegion (sp0 - 368#64 - 4096#64) 4080 ∗
          memRegion (sp0 - 368#64 - 7824#64) 3728)
    hshim (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    simp only [noAllocShimSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf2 hpc2 hrun2 hsp2 hcs2
  rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [noAllocShimSpec]
  refine SepWPp.pure_elim fun htr2 => ?_
  simp only [wp_norm, arm64_norm, htr1] at htr2
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - 0x15130))
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.call (x := (x.protoMsg.encode.length + 1, 1))
    (F := ((sp0 - 368#64) ↦₆₄ msgCopyPtr) ∗
          ((sp0 - 332#64) ↦₃₂ ver32) ∗
          wirePreKeySignalMessageAt A wg (sp0 - 272#64) x.protoMsg ∗
          ((sp0 - 144#64) ↦₆₄ w144) ∗
          ((sp0 - 136#64) ↦₆₄ w136) ∗
          ((sp0 - 128#64) ↦₆₄ w128) ∗
          memRegion (sp0 - 368#64 - 7824#64) 3728)
    halloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    simp only [rustAllocSpec, LayoutOk, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
    rw [stackAt_allocHook_split_encodedLen (sp0 - 368#64)]
    simp only [sepConj_assoc, arm64_norm]
    refine ⟨⟨by omega, ⟨0, rfl⟩, by omega⟩, ?_⟩
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf3 hpc3 hrun3 hsp3 hcs3
  rcases hcs3 with ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
  simp only [wp_norm, arm64_norm, *] at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
  by_cases hoom : sf3.readReg64 .x0 = 0#64
  · have hoom0 : (sf3.readReg64 .x0 = 0) = True := eq_true hoom
    simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_oom]
    refine SepWPp.pure_elim fun htr3 => ?_
    simp only [wp_norm, arm64_norm, htr2] at htr3 hoom
    apply SepWPp.of_sepWP (mid := entry + 516#64)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    exact ho204 (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
  · have hoom0 : (sf3.readReg64 .x0 = 0) = False := eq_false hoom
    simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_ok]
    refine SepWPp.pure_elim fun ⟨halign_ptr, htr3⟩ => ?_
    have hoom_beq : (sf3.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    simp only [wp_norm, arm64_norm, htr2] at htr3 hoom hoom_beq
    rw [memRegion_split' (b := sf3.readReg64 (Reg.gpr 0#5))
          (b' := sf3.readReg64 (Reg.gpr 0#5) + 1#64)
          (n := 1) (k := x.protoMsg.encode.length) (by omega) rfl (by omega),
        ProofLib.memRegion_one (sf3.readReg64 (Reg.gpr 0#5))]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    apply SepWPp.of_sepWP (mid := entry + 100920#64)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call (x := ⟨sp0 - 272#64, wg, x.protoMsg⟩)
      (F := (sf3.readReg64 (Reg.gpr 0#5) ↦₈ versionByte x.ver) ∗
            ((sp0 - 128#64) ↦₆₄ 1#64) ∗
            ((sp0 - 144#64) ↦₆₄ BitVec.ofNat 64 (x.protoMsg.encode.length + 1)) ∗
            ((sp0 - 136#64) ↦₆₄ sf3.readReg64 (Reg.gpr 0#5)) ∗
            ((sp0 - 332#64) ↦₃₂ ver32) ∗
            A.live (sf3.readReg64 (Reg.gpr 0#5)) (x.protoMsg.encode.length + 1) 1 ∗
            memRegion (sf3.readReg64 (Reg.gpr 0#5) + 1#64) x.protoMsg.encode.length ∗
            A.pool ∗
            ((sp0 - 368#64) ↦₆₄ msgCopyPtr) ∗
            memRegion (sp0 - 368#64 - 4096#64) 4080 ∗
            memRegion (sp0 - 368#64 - 7824#64) 3728)
      henc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp3, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      simp only [preKeyMsgEncodedLenSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      rw [stackAt_allocHook_split_encodedLen (sp0 - 368#64)] at hm
      simp only [sepConj_assoc, arm64_norm] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus)
    intro sf4 hpc4 hrun4 hsp4 hcs4
    rcases hcs4 with ⟨h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, hfp_4⟩
    simp only [wp_norm, arm64_norm, *] at hsp4 h19_4 h20_4 h21_4 h22_4 h23_4 h24_4 h25_4 h26_4 h27_4 h28_4 hfp_4
    simp only [preKeyMsgEncodedLenSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0_4, htr4⟩ => ?_
    simp only [wp_norm, arm64_norm, htr3] at hx0_4 htr4
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · simp only [State.spAligned, wp_norm, arm64_norm, *]
    · refine Entails.sepExists_right (sf3.readReg64 (Reg.gpr 0#5)) ?_
      have hser := (pack_serPrefix0 A sp0 (sf3.readReg64 (Reg.gpr 0#5)) x.ver
        x.protoMsg.encode.length hfit62 hoom).symm
      rw [hmod_len, hser,
          stackAt_preKeyMsgSubStack_to_allocHook (sp0 - 368#64),
          stackAt_allocHook_split_encodedLen (sp0 - 368#64)]
      refine Entails.trans (sepConj_mono_left hunpack) ?_
      simp only [hsp3, arm64_norm]
      exact entails_of_sep_focus (by sep_focus)

/-! ## Prologue Composition (`+0x000..+0x25c`) -/

theorem setWidth8_setWidth32 (w : BitVec 64) :
    (w.setWidth 32).setWidth 8 = w.setWidth 8 := by bv_bits

theorem setWidth32_zeroExtend64 (w : BitVec 32) :
    (w.zeroExtend 64).setWidth 32 = w := by bv_bits

theorem preKeyMsg_alloc_ser_wpp_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocHooks A ext) (hSh : HookSat ext shimName sessionShimSpec)
    (hEncLen : PreKeyMsgEncodedLenOk_ext img A ext)
    (x : PreKeyMsgNewCall) (sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr
      w368 w144 w136 w128 : BitVec 64) (ver32 pkId32 : BitVec 32)
    (hkyCap : kyberCap = match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hky_len : ∀ k, x.kp = some k → k.ciphertext.length < 2 ^ 63)
    (hmsg_len : x.msg.serialized.length < 2 ^ 63)
    (hver : ver32.setWidth 8 = x.ver) (hfit : x.model.serialized.length < 2 ^ 42) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyMsgNewName + 496#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp0 - 272#64) (hx19 : s.readReg64 .x19 = kyberCap)
    (hx20 : s.readReg64 .x20 = (if x.preKeyId.isSome then 1#32 else 0#32).zeroExtend 64)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64) (hx22 : s.readReg64 .x22 = 33#64)
    (hx24 : s.readReg64 .x24 = 33#64) (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = msgCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = bkSerPtr) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyMsgNewName + 604#64) s
      (((sp0 - 368#64) ↦₆₄ w368) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
       wirePreKeySignalMessageAt A
         (x.mkWirePins kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr)
         (sp0 - 272#64) x.protoMsg ∗
       ((sp0 - 144#64) ↦₆₄ w144) ∗ ((sp0 - 136#64) ↦₆₄ w136) ∗ ((sp0 - 128#64) ↦₆₄ w128) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x19 = kyberCap ∧
         sm.readReg64 .x20 = (if x.preKeyId.isSome then 1#32 else 0#32).zeroExtend 64 ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧ sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x24 = 33#64 ∧ sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = bkSerPtr ∧ sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ ∃∗ serPtr : BitVec 64,
          ((sp0 - 368#64) ↦₆₄ msgCopyPtr) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
          memRegion (sp0 - 272#64) 128 ∗
          vecU8At A (sp0 - 144#64) (BitVec.ofNat 64 x.model.serialized.length)
            serPtr [versionByte x.ver] ∗
          optKyberCopyBuf A kyberCopyPtr x.kp ∗ boxU8Buf A bkSerPtr x.baseKey.serialize ∗
          boxU8Buf A ikSerPtr x.ik.serialize ∗ boxU8Buf A msgCopyPtr x.msg.serialized ∗
          A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) := by
  have hunpack := unpack_wirePreKeySignalMessageAt A x sp0 kyberCap kyberCopyPtr
    bkSerPtr ikSerPtr msgCopyPtr hkyCap hky_len hmsg_len
  have hver_byte :
      BitVec.zeroExtend 8 (4#64 ||| BitVec.zeroExtend 64 (ver32 <<< 4)) = versionByte x.ver := by
    rw [versionByte_word_eq' ver32, hver]
  clear hkyCap hky_len hmsg_len hver
  have henc := preKeyMsg_encodedLen_ok_ext hEncLen
  have hshim := preKeyMsg_shim_ok_ext (b := img.base) hSh
  have halloc := preKeyMsg_alloc_ok_ext (b := img.base) hA
  have ho204 := @preKeyMsg_oom_at_204_ext img.base ext
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have hmod_len : x.model.serialized.length = x.protoMsg.encode.length + 1 :=
    model_serialized_length x
  have hfit62 : x.protoMsg.encode.length + 1 < 2 ^ 62 := by omega
  have hwire_fit : PreKeyMsgWireLengthsFit x.protoMsg :=
    preKeyMsgWireLengthsFit_protoMsg x (by omega)
  clear hfit
  obtain ⟨hovf_ult, hovf_msb, hovf_hi, hovf_add, hovf_toNat⟩ :=
    preKeyMsg_encLen_overflow_checks hfit62
  rw [hovf_add] at hovf_ult hovf_msb
  simp only [arm64_norm] at hx0 hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx27 hx28 hx29
  preKeyMsg_fetches_range img.base (Rust.withPanics ext) 0x1f0 0x200
  preKeyMsg_fetches_range img.base (Rust.withPanics ext) 0x210 0x258
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr preKeyMsgNewName = entry
  examples_hide_fetches
  let wg := x.mkWirePins kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr
  apply SepWPp.of_sepWP (mid := entry + 100920#64)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.call (x := ⟨sp0 - 272#64, wg, x.protoMsg⟩)
    (F := ((sp0 - 368#64) ↦₆₄ w368) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
          ((sp0 - 144#64) ↦₆₄ w144) ∗ ((sp0 - 136#64) ↦₆₄ w136) ∗ ((sp0 - 128#64) ↦₆₄ w128) ∗
          A.pool ∗ memRegion (sp0 - 368#64 - 4096#64) 4080 ∗
          memRegion (sp0 - 368#64 - 7824#64) 3728)
    henc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    rw [stackAt_preKeyMsgSubStack_to_allocHook (sp0 - 368#64),
        stackAt_allocHook_split_encodedLen (sp0 - 368#64)] at hm
    simp only [preKeyMsgEncodedLenSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  simp only [preKeyMsgEncodedLenSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0_1, htr1⟩ => ?_
  simp only [wp_norm, arm64_norm] at hx0_1 htr1
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x15130))
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.call (x := ())
    (F := ((sp0 - 368#64) ↦₆₄ msgCopyPtr) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
          wirePreKeySignalMessageAt A wg (sp0 - 272#64) x.protoMsg ∗
          ((sp0 - 144#64) ↦₆₄ w144) ∗ ((sp0 - 136#64) ↦₆₄ w136) ∗ ((sp0 - 128#64) ↦₆₄ w128) ∗
          A.pool ∗ stackAt s.sp preKeyMsgEncodedLenStack ∗
          memRegion (sp0 - 368#64 - 4096#64) 4080 ∗
          memRegion (sp0 - 368#64 - 7824#64) 3728)
    hshim (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    simp only [noAllocShimSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf2 hpc2 hrun2 hsp2 hcs2
  rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [noAllocShimSpec]
  refine SepWPp.pure_elim fun htr2 => ?_
  simp only [wp_norm, arm64_norm, htr1] at htr2
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - 0x15130))
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.call (x := (x.protoMsg.encode.length + 1, 1))
    (F := ((sp0 - 368#64) ↦₆₄ msgCopyPtr) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
          wirePreKeySignalMessageAt A wg (sp0 - 272#64) x.protoMsg ∗
          ((sp0 - 144#64) ↦₆₄ w144) ∗ ((sp0 - 136#64) ↦₆₄ w136) ∗ ((sp0 - 128#64) ↦₆₄ w128) ∗
          memRegion (sp0 - 368#64 - 7824#64) 3728)
    halloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    simp only [rustAllocSpec, LayoutOk, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
    rw [stackAt_allocHook_split_encodedLen (sp0 - 368#64)]
    simp only [sepConj_assoc, arm64_norm]
    refine ⟨⟨by omega, ⟨0, rfl⟩, by omega⟩, ?_⟩
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf3 hpc3 hrun3 hsp3 hcs3
  rcases hcs3 with ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
  simp only [wp_norm, arm64_norm, *] at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
  by_cases hoom : sf3.readReg64 .x0 = 0#64
  · have hoom0 : (sf3.readReg64 .x0 = 0) = True := eq_true hoom
    simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_oom]
    refine SepWPp.pure_elim fun htr3 => ?_
    simp only [wp_norm, arm64_norm, htr2] at htr3 hoom
    apply SepWPp.of_sepWP (mid := entry + 516#64)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    exact ho204 (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
  · have hoom0 : (sf3.readReg64 .x0 = 0) = False := eq_false hoom
    simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_ok]
    refine SepWPp.pure_elim fun ⟨halign_ptr, htr3⟩ => ?_
    have hoom_beq : (sf3.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    simp only [wp_norm, arm64_norm, htr2] at htr3 hoom hoom_beq
    rw [memRegion_split' (b := sf3.readReg64 (Reg.gpr 0#5))
          (b' := sf3.readReg64 (Reg.gpr 0#5) + 1#64)
          (n := 1) (k := x.protoMsg.encode.length) (by omega) rfl (by omega),
        ProofLib.memRegion_one (sf3.readReg64 (Reg.gpr 0#5))]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    apply SepWPp.of_sepWP (mid := entry + 100920#64)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call (x := ⟨sp0 - 272#64, wg, x.protoMsg⟩)
      (F := (sf3.readReg64 (Reg.gpr 0#5) ↦₈ versionByte x.ver) ∗
            ((sp0 - 128#64) ↦₆₄ 1#64) ∗
            ((sp0 - 144#64) ↦₆₄ BitVec.ofNat 64 (x.protoMsg.encode.length + 1)) ∗
            ((sp0 - 136#64) ↦₆₄ sf3.readReg64 (Reg.gpr 0#5)) ∗
            ((sp0 - 332#64) ↦₃₂ ver32) ∗
            A.live (sf3.readReg64 (Reg.gpr 0#5)) (x.protoMsg.encode.length + 1) 1 ∗
            memRegion (sf3.readReg64 (Reg.gpr 0#5) + 1#64) x.protoMsg.encode.length ∗
            A.pool ∗ ((sp0 - 368#64) ↦₆₄ msgCopyPtr) ∗
            memRegion (sp0 - 368#64 - 4096#64) 4080 ∗
            memRegion (sp0 - 368#64 - 7824#64) 3728)
      henc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp3, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      simp only [preKeyMsgEncodedLenSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      rw [stackAt_allocHook_split_encodedLen (sp0 - 368#64)] at hm
      simp only [sepConj_assoc, arm64_norm] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus)
    intro sf4 hpc4 hrun4 hsp4 hcs4
    rcases hcs4 with ⟨h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, hfp_4⟩
    simp only [wp_norm, arm64_norm, *] at hsp4 h19_4 h20_4 h21_4 h22_4 h23_4 h24_4 h25_4 h26_4 h27_4 h28_4 hfp_4
    simp only [preKeyMsgEncodedLenSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0_4, htr4⟩ => ?_
    simp only [wp_norm, arm64_norm, htr3] at hx0_4 htr4
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · simp only [State.spAligned, wp_norm, arm64_norm, *]
    · refine Entails.sepExists_right (sf3.readReg64 (Reg.gpr 0#5)) ?_
      have hser := (pack_serPrefix0 A sp0 (sf3.readReg64 (Reg.gpr 0#5)) x.ver
        x.protoMsg.encode.length hfit62 hoom).symm
      rw [hmod_len, hser,
          stackAt_preKeyMsgSubStack_to_allocHook (sp0 - 368#64),
          stackAt_allocHook_split_encodedLen (sp0 - 368#64)]
      refine Entails.trans (sepConj_mono_left hunpack) ?_
      simp only [hsp3, arm64_norm]
      exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_alloc_ser_wpp_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs)
    (hEncLen : PreKeyMsgEncodedLenOk_trap img C A abs)
    (x : PreKeyMsgNewCall) (sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr
      w368 w144 w136 w128 : BitVec 64) (ver32 pkId32 : BitVec 32)
    (hkyCap : kyberCap = match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hky_len : ∀ k, x.kp = some k → k.ciphertext.length < 2 ^ 63)
    (hmsg_len : x.msg.serialized.length < 2 ^ 63)
    (hver : ver32.setWidth 8 = x.ver) (hfit : x.model.serialized.length < 2 ^ 42) (s : State)
    (hpc : s.pc = (trTrapProgAt img.base C abs).fnAddr preKeyMsgNewName + 496#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp0 - 272#64) (hx19 : s.readReg64 .x19 = kyberCap)
    (hx20 : s.readReg64 .x20 = (if x.preKeyId.isSome then 1#32 else 0#32).zeroExtend 64)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64) (hx22 : s.readReg64 .x22 = 33#64)
    (hx24 : s.readReg64 .x24 = 33#64) (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = msgCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = bkSerPtr) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr preKeyMsgNewName + 604#64) s
      (((sp0 - 368#64) ↦₆₄ w368) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
       wirePreKeySignalMessageAt A
         (x.mkWirePins kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr)
         (sp0 - 272#64) x.protoMsg ∗
       ((sp0 - 144#64) ↦₆₄ w144) ∗ ((sp0 - 136#64) ↦₆₄ w136) ∗ ((sp0 - 128#64) ↦₆₄ w128) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x19 = kyberCap ∧
         sm.readReg64 .x20 = (if x.preKeyId.isSome then 1#32 else 0#32).zeroExtend 64 ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧ sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x24 = 33#64 ∧ sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = bkSerPtr ∧ sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ ∃∗ serPtr : BitVec 64,
          ((sp0 - 368#64) ↦₆₄ msgCopyPtr) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
          memRegion (sp0 - 272#64) 128 ∗
          vecU8At A (sp0 - 144#64) (BitVec.ofNat 64 x.model.serialized.length)
            serPtr [versionByte x.ver] ∗
          optKyberCopyBuf A kyberCopyPtr x.kp ∗ boxU8Buf A bkSerPtr x.baseKey.serialize ∗
          boxU8Buf A ikSerPtr x.ik.serialize ∗ boxU8Buf A msgCopyPtr x.msg.serialized ∗
          A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) :=
  preKeyMsg_alloc_ser_wpp_ext (trTrap_allocHooks hA) trTrap_shim_hookSat hEncLen x sp0 kyberCap
    kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr w368 w144 w136 w128 ver32 pkId32 hkyCap hky_len
    hmsg_len hver hfit s hpc hrun hsp hsp_align hx0 hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx27 hx28 hx29

theorem preKeyMsg_convert_344 (sp0 w344 : BitVec 64) {prog : Program} {ret : BitVec 64} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hfocus : P = (((sp0 - 344#64) ↦₆₄ w344) ∗ memRegion (sp0 - 336#64) 4) ∗ F)
    (h : ∀ w344_32 : BitVec 32,
      SepWPp prog ret s
        (((sp0 - 344#64) ↦₃₂ w344_32) ∗ memRegion (sp0 - 340#64) 8 ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus] at hm
  have h1 :
      (((sp0 - 344#64) ↦₆₄ w344) ∗ memRegion (sp0 - 336#64) 4) ∗ F ⊢
      ((∃∗ w : BitVec 32, (sp0 - 344#64) ↦₃₂ w) ∗ memRegion (sp0 - 340#64) 8) ∗ F :=
    sepConj_mono_left (word64_and_4_to_word32_and_8 sp0 w344)
  have hm' := Satisfies.mono (sepConj_mono_left h1) hm
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc] at hm'
  rcases hm' with ⟨w344_32, hm'⟩
  exact h w344_32 R (by simpa only [sepConj_assoc] using hm') hL

theorem PreKeyMsgSegExit.of_sepWPp_seamA {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {x : PreKeyMsgNewCall} {R P : SepProp} {s0 : State}
    (hm : s0.mem ⊨ P ∗ R)
    (hwpp : SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyMsgNewName + 604#64) s0 P
      (fun sf P_f => ∀ R', sf.mem ⊨ P_f ∗ R' → ∃ g, SeamA img A x g R' s0 sf)
      (PanicAllocPost s0)) :
    PreKeyMsgSegExit img C A ctl abs x R s0 s0
      (fun s => ∃ g, SeamA img A x g R s0 s) := by
  intro hL
  obtain ⟨sf, hsteps, ⟨_hpc, _hrun, P_f, hmf, hq⟩ | ⟨hpan, P_f, hmf, hp⟩ | ⟨_, _hoom⟩⟩ := hwpp R hm hL
  · exact ⟨sf, hsteps, Or.inl (hq R hmf)⟩
  · have hpan' : sf.status = .Panicked := by simpa [Rust.panicked] using hpan
    exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan', hp R hmf⟩))⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem PreKeyMsgSegExit_ext_of_sepWPp_seamA {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {x : PreKeyMsgNewCall} {R P : SepProp} {s0 : State}
    (hm : s0.mem ⊨ P ∗ R)
    (hwpp : SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyMsgNewName + 604#64) s0 P
      (fun sf P_f => ∀ R', sf.mem ⊨ P_f ∗ R' → ∃ g, SeamA img A x g R' s0 sf)
      (PanicAllocPost s0)) :
    PreKeyMsgSegExit_ext img A ext x R s0 s0 (fun s => ∃ g, SeamA img A x g R s0 s) := by
  intro hL
  obtain ⟨sf, hsteps, ⟨_hpc, _hrun, P_f, hmf, hq⟩ | ⟨hpan, P_f, hmf, hp⟩ | ⟨_, _hoom⟩⟩ := hwpp R hm hL
  · exact ⟨sf, hsteps, Or.inl (hq R hmf)⟩
  · have hpan' : sf.status = .Panicked := by simpa [Rust.panicked] using hpan
    exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan', hp R hmf⟩))⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem PreKeyMsgSegExit_trap_of_sepWPp_seamA {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)} {x : PreKeyMsgNewCall} {R P : SepProp} {s0 : State}
    (hm : s0.mem ⊨ P ∗ R)
    (hwpp : SepWPp (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr preKeyMsgNewName + 604#64) s0 P
      (fun sf P_f => ∀ R', sf.mem ⊨ P_f ∗ R' → ∃ g, SeamA img A x g R' s0 sf)
      (PanicAllocPost s0)) :
    PreKeyMsgSegExit_trap img C A abs x R s0 s0 (fun s => ∃ g, SeamA img A x g R s0 s) :=
  PreKeyMsgSegExit_ext_of_sepWPp_seamA hm hwpp

theorem preKeyMsg_seq_wpp' {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (htr : s.trace = s0.trace)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)) (PanicAllocPost s))
    (hfocus : P = P1 ∗ F)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | ⟨_, _hoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem optKyberAt_length_lt {A : RustAlloc} {a ptr : BitVec 64} {kp : Option KyberPayload}
    {m : Memory} {P1 F : SepProp}
    (hm : m ⊨ P1 ∗ optKyberAt A a ptr kp ∗ F) :
    ∀ k, kp = some k → k.ciphertext.length < 2 ^ 63 := by
  intro k hk
  subst hk
  rw [optKyberAt_eq_word0_and_rest, optKyberRestAt_some_eq] at hm
  simp only [sepConj_assoc] at hm
  rw [pull_pure_second, pull_pure_second, satisfies_pure_sepConj] at hm
  exact hm.1.2

/-- Prologue segment (`+0x000..+0x25c`): from entry `0x15130` under `(preKeyMsgNewSpec A).pre`,
execution reaches either `SeamA` or an OOM panic outcome of `preKeyMsgNewSpec A`. -/
theorem prologue_ok (h3 : PublicApiHooks C A S encRecord abs)
    (_himg : Obj.Loads libsignalSessionImage img)
    (hEncLen : PreKeyMsgEncodedLenOk img C A ctl abs)
    (x : PreKeyMsgNewCall) (R : SepProp) (s0 : State)
    (hs : s0.status = .Running)
    (hpc : s0.pc = preKeyMsgNewEntry img)
    (hsp : s0.spAligned = true)
    (hpre : s0.mem ⊨ (preKeyMsgNewSpec A).pre x s0 ∗ R) :
    PreKeyMsgSegExit img C A ctl abs x R s0 s0
      (fun s => ∃ g, SeamA img A x g R s0 s) := by
  have hA : AllocHooks A abs := h3.alloc
  have hpc_entry : s0.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyMsgNewName := by
    rw [fnAddr_preKeyMsgNew_eq, hpc]
  simp only [preKeyMsgNewSpec, sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hfit⟩, hpre⟩
  have hky_len := optKyberAt_length_lt hpre
  rw [optKyberAt_eq_word0_and_rest A x.kyA x.kyPtr x.kp,
      stackAt_preKeyMsgNewStack_ready s0.sp] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨w368, w360, w352, w344, w332, w328, w324, w320, w312, w304,
    w296, w292, w288, w280, w144, w136, w128, hpre⟩
  simp only [← sepConj_assoc] at hpre
  let ver32 : BitVec 32 := (s0.readReg64 .x0).setWidth 32
  let pkId32 : BitVec 32 := (s0.readReg64 .x3).setWidth 32
  have hver : ver32.setWidth 8 = x.ver := by
    dsimp [ver32]
    rw [setWidth8_setWidth32, hx0]
  have hpk : ∀ v, x.preKeyId = some v → pkId32 = v := hx3
  refine PreKeyMsgSegExit.of_sepWPp_seamA hpre ?_
  refine preKeyMsg_seq_wp
    (preKeyMsg_entry_to_04c_wp x s0.sp w304 w288 w280 w292 s0 hpc_entry hs rfl hsp
      hx1 hx2 hx4 hx5 hx6 hx7 hx8)
    (by sep_focus) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hsp1_align, s1_x6, s1_x20, s1_x21, s1_x22, s1_x23,
    s1_x25, s1_x26, s1_x29, htr1, hvregs1⟩
  refine preKeyMsg_seq_wpp htr1
    (preKeyMsg_kyber_clone_wpp hA x s0.sp w320 w312 w324 w296 ver32 pkId32 s1
      hpc1 hrun1 hsp1 hsp1_align s1_x6 s1_x20 s1_x21 s1_x22 s1_x23 s1_x25 s1_x26 s1_x29)
    (by sep_focus)
    (fun _ _ h => panicAllocPost_of_eq h) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hsp2_align, s2_x6, s2_x19, s2_x21, s2_x22, s2_x23,
    s2_x25, s2_x26, s2_x29, htr2, hvregs2⟩
  have htr20 : s2.trace = s0.trace := htr2.trans htr1
  have hvregs20 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2.trans hvregs1
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun kyberCopyPtr => ?_
  refine SepWPp.exists_elim fun w312' => ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hky_ptr_ne => ?_
  refine preKeyMsg_seq_wpp' htr20
    (preKeyMsg_pk_serialize_wpp hA x s0.sp (s2.readReg64 .x19) ver32 pkId32 s2
      hpc2 hrun2 hsp2 hsp2_align s2_x6 rfl s2_x21 s2_x22 s2_x23 s2_x25 s2_x26 s2_x29)
    (by sep_focus)
    (fun _ _ h => panicAllocPost_of_eq h) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, hsp3_align, s3_x1, s3_x19, s3_x20, s3_x21, s3_x22,
    s3_x23, s3_x24, s3_x25, s3_x26, s3_x29, htr3, hvregs3⟩
  have htr30 : s3.trace = s0.trace := htr3.trans htr20
  have hvregs30 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := hvregs3.trans hvregs20
  have s3_x19' : s3.readReg64 .x19 =
      match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length :=
    s3_x19.trans s2_x19
  refine preKeyMsg_seq_wpp' htr30
    (preKeyMsg_msg_clone_wpp hA x s0.sp (s3.readReg64 .x19) (s3.readReg64 .x28) (s3.readReg64 .x0)
      w360 w344 w312' w332 w328 ver32 pkId32 s3
      hpc3 hrun3 hsp3 hsp3_align rfl s3_x1 rfl s3_x20 s3_x21 s3_x22 s3_x23 s3_x24 s3_x25
      s3_x26 rfl s3_x29)
    (by sep_focus)
    (fun _ _ h => panicAllocPost_of_eq h) ?_
  intro s4 hpc4 hrun4 ⟨hsp4, hsp4_align, s4_x0, s4_x8, s4_x19, s4_x22, s4_x23,
    s4_x24, s4_x25, s4_x27, s4_x28, s4_x29, htr4, hvregs4, _hmsg9, hmsg_lt40, _hmsg_ptr_ne⟩
  have htr40 : s4.trace = s0.trace := htr4.trans htr30
  have hvregs40 : calleeSavedVRegs s4 = calleeSavedVRegs s0 := hvregs4.trans hvregs30
  have s4_x19' : s4.readReg64 .x19 =
      match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length :=
    s4_x19.trans s3_x19'
  have hmsg_len63 : x.msg.serialized.length < 2 ^ 63 := by omega
  have hkyId : ∀ k, x.kp = some k → kyberIdOf x.kp w324 = k.preKeyId := by
    intro k hk
    simp [kyberIdOf, hk]
  refine preKeyMsg_convert_344 s0.sp 33#64 (by sep_focus) fun w344_32 => ?_
  refine preKeyMsg_seq_wp
    (preKeyMsg_store_wire_wp x s0.sp (s4.readReg64 .x19) kyberCopyPtr
      (s3.readReg64 .x28) (s3.readReg64 .x0) (s4.readReg64 .x26) w352
      w344_32 pkId32 (kyberIdOf x.kp w324) s4_x19' hpk hkyId hmsg_len63 s4
      hpc4 hrun4 hsp4 hsp4_align s4_x0 s4_x8 rfl s4_x22 s4_x23 s4_x24 s4_x25 rfl s4_x27
      s4_x28 s4_x29)
    (by sep_focus) ?_
  intro s5 hpc5 hrun5 ⟨hsp5, hsp5_align, s5_x0, s5_x19, s5_x20, s5_x21, s5_x22,
    _s5_x23, s5_x24, s5_x25, s5_x26, s5_x27, s5_x28, s5_x29, htr5, hvregs5⟩
  have htr50 : s5.trace = s0.trace := htr5.trans htr40
  have hvregs50 : calleeSavedVRegs s5 = calleeSavedVRegs s0 := hvregs5.trans hvregs40
  have s5_x19' : s5.readReg64 .x19 =
      match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length :=
    s5_x19.trans s4_x19'
  refine preKeyMsg_seq_wpp htr50
    (preKeyMsg_alloc_ser_wpp hA hEncLen x s0.sp (s4.readReg64 .x19) kyberCopyPtr
      (s3.readReg64 .x28) (s3.readReg64 .x0) (s4.readReg64 .x26)
      w368 w144 w136 w128 ver32 pkId32 s4_x19' hky_len hmsg_len63 hver hfit s5
      hpc5 hrun5 hsp5 hsp5_align s5_x0 s5_x19 s5_x20 s5_x21 s5_x22 s5_x24 s5_x25
      s5_x26 s5_x27 s5_x28 s5_x29)
    (by sep_focus)
    (fun _ _ h => panicAllocPost_of_eq h) ?_
  intro sf hpcf hrunf ⟨hspf, hspf_align, sf_x19, sf_x20, sf_x21, sf_x22, sf_x24,
    sf_x25, sf_x27, sf_x28, sf_x29, htrf, hvregsf⟩
  have htrf0 : sf.trace = s0.trace := htrf.trans htr50
  have hvregsf0 : calleeSavedVRegs sf = calleeSavedVRegs s0 := hvregsf.trans hvregs50
  have sf_x19' : sf.readReg64 .x19 =
      match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length :=
    sf_x19.trans s4_x19'
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun serPtr => ?_
  apply SepWPp.done hpcf hrunf
  intro R' hmf
  let g : PreKeyMsgFrameGhost :=
    { serPtr := serPtr
      kyberCopyPtr := kyberCopyPtr
      bkSerPtr := s3.readReg64 .x28
      ikSerPtr := s3.readReg64 .x0
      msgCopyPtr := s4.readReg64 .x26
      ver32 := ver32
      preKeyVal32 := pkId32
      kyberId32 := kyberIdOf x.kp w324 }
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · rw [hpcf, fnAddr_preKeyMsgNew_eq (img := img) (C := C) (ctl := ctl) (abs := abs), preKeyMsgSeamAPC]
  · refine ⟨hfit, hver, hpk, fun k hk => ?_⟩
    simp [g, kyberIdOf, hk]
  · refine ⟨hrunf, hspf, hsp, hspf_align, htrf0, sf_x29, sf_x19', ?_, ?_, sf_x22, sf_x24, ?_, sf_x27, sf_x28, hvregsf0⟩
    · rw [sf_x20, setWidth32_zeroExtend64]
    · rw [sf_x21, setWidth32_zeroExtend64]
    · rw [sf_x25, setWidth32_zeroExtend64]
  · rw [preKeyMsgFrameSlotsAt_one_eq_vec]
    simp (disch := decide) only [preKeyMsgFrameSlotsAt, preKeyMsgHeapAt, g, bv_sub_add_lit, Nat.reduceSub,
      sepConj_assoc] at hmf ⊢
    exact satisfies_of_sep_focus hmf (by sep_focus)

theorem prologue_ok_ext {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocHooks A ext) (hSh : HookSat ext shimName sessionShimSpec)
    (hMc : HookSat ext memcpyName (sessionMemcpySpec allocHookStack))
    (_himg : Obj.Loads libsignalSessionImage img)
    (hEncLen : PreKeyMsgEncodedLenOk_ext img A ext)
    (x : PreKeyMsgNewCall) (R : SepProp) (s0 : State)
    (hs : s0.status = .Running) (hpc : s0.pc = preKeyMsgNewEntry img) (hsp : s0.spAligned = true)
    (hpre : s0.mem ⊨ (preKeyMsgNewSpec A).pre x s0 ∗ R) :
    PreKeyMsgSegExit_ext img A ext x R s0 s0 (fun s => ∃ g, SeamA img A x g R s0 s) := by
  have hpc_entry : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyMsgNewName := by
    rw [fnAddr_preKeyMsgNew_eq_ext, hpc]
  simp only [preKeyMsgNewSpec, sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hfit⟩, hpre⟩
  have hky_len := optKyberAt_length_lt hpre
  rw [optKyberAt_eq_word0_and_rest A x.kyA x.kyPtr x.kp,
      stackAt_preKeyMsgNewStack_ready s0.sp] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨w368, w360, w352, w344, w332, w328, w324, w320, w312, w304,
    w296, w292, w288, w280, w144, w136, w128, hpre⟩
  simp only [← sepConj_assoc] at hpre
  let ver32 : BitVec 32 := (s0.readReg64 .x0).setWidth 32
  let pkId32 : BitVec 32 := (s0.readReg64 .x3).setWidth 32
  have hver : ver32.setWidth 8 = x.ver := by
    dsimp [ver32]; rw [setWidth8_setWidth32, hx0]
  have hpk : ∀ v, x.preKeyId = some v → pkId32 = v := hx3
  refine PreKeyMsgSegExit_ext_of_sepWPp_seamA hpre ?_
  refine preKeyMsg_seq_wp
    (preKeyMsg_entry_to_04c_wp_ext x s0.sp w304 w288 w280 w292 s0 hpc_entry hs rfl hsp
      hx1 hx2 hx4 hx5 hx6 hx7 hx8)
    (by sep_focus) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hsp1_align, s1_x6, s1_x20, s1_x21, s1_x22, s1_x23,
    s1_x25, s1_x26, s1_x29, htr1, hvregs1⟩
  refine preKeyMsg_seq_wpp htr1
    (preKeyMsg_kyber_clone_wpp_ext hA hSh hMc x s0.sp w320 w312 w324 w296 ver32 pkId32 s1
      hpc1 hrun1 hsp1 hsp1_align s1_x6 s1_x20 s1_x21 s1_x22 s1_x23 s1_x25 s1_x26 s1_x29)
    (by sep_focus) (fun _ _ h => panicAllocPost_of_eq h) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hsp2_align, s2_x6, s2_x19, s2_x21, s2_x22, s2_x23,
    s2_x25, s2_x26, s2_x29, htr2, hvregs2⟩
  have htr20 : s2.trace = s0.trace := htr2.trans htr1
  have hvregs20 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2.trans hvregs1
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun kyberCopyPtr => ?_
  refine SepWPp.exists_elim fun w312' => ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hky_ptr_ne => ?_
  refine preKeyMsg_seq_wpp' htr20
    (preKeyMsg_pk_serialize_wpp_ext hA hSh x s0.sp (s2.readReg64 .x19) ver32 pkId32 s2
      hpc2 hrun2 hsp2 hsp2_align s2_x6 rfl s2_x21 s2_x22 s2_x23 s2_x25 s2_x26 s2_x29)
    (by sep_focus) (fun _ _ h => panicAllocPost_of_eq h) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, hsp3_align, s3_x1, s3_x19, s3_x20, s3_x21, s3_x22,
    s3_x23, s3_x24, s3_x25, s3_x26, s3_x29, htr3, hvregs3⟩
  have htr30 : s3.trace = s0.trace := htr3.trans htr20
  have hvregs30 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := hvregs3.trans hvregs20
  have s3_x19' : s3.readReg64 .x19 =
      match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length :=
    s3_x19.trans s2_x19
  refine preKeyMsg_seq_wpp' htr30
    (preKeyMsg_msg_clone_wpp_ext hA hSh hMc x s0.sp (s3.readReg64 .x19) (s3.readReg64 .x28)
      (s3.readReg64 .x0) w360 w344 w312' w332 w328 ver32 pkId32 s3
      hpc3 hrun3 hsp3 hsp3_align rfl s3_x1 rfl s3_x20 s3_x21 s3_x22 s3_x23 s3_x24 s3_x25
      s3_x26 rfl s3_x29)
    (by sep_focus) (fun _ _ h => panicAllocPost_of_eq h) ?_
  intro s4 hpc4 hrun4 ⟨hsp4, hsp4_align, s4_x0, s4_x8, s4_x19, s4_x22, s4_x23,
    s4_x24, s4_x25, s4_x27, s4_x28, s4_x29, htr4, hvregs4, _hmsg9, hmsg_lt40, _hmsg_ptr_ne⟩
  have htr40 : s4.trace = s0.trace := htr4.trans htr30
  have hvregs40 : calleeSavedVRegs s4 = calleeSavedVRegs s0 := hvregs4.trans hvregs30
  have s4_x19' : s4.readReg64 .x19 =
      match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length :=
    s4_x19.trans s3_x19'
  have hmsg_len63 : x.msg.serialized.length < 2 ^ 63 := by omega
  have hkyId : ∀ k, x.kp = some k → kyberIdOf x.kp w324 = k.preKeyId := fun k hk => by
    simp [kyberIdOf, hk]
  refine preKeyMsg_convert_344 s0.sp 33#64 (by sep_focus) fun w344_32 => ?_
  refine preKeyMsg_seq_wp
    (preKeyMsg_store_wire_wp_ext x s0.sp (s4.readReg64 .x19) kyberCopyPtr
      (s3.readReg64 .x28) (s3.readReg64 .x0) (s4.readReg64 .x26) w352
      w344_32 pkId32 (kyberIdOf x.kp w324) s4_x19' hpk hkyId hmsg_len63 s4
      hpc4 hrun4 hsp4 hsp4_align s4_x0 s4_x8 rfl s4_x22 s4_x23 s4_x24 s4_x25 rfl s4_x27
      s4_x28 s4_x29)
    (by sep_focus) ?_
  intro s5 hpc5 hrun5 ⟨hsp5, hsp5_align, s5_x0, s5_x19, s5_x20, s5_x21, s5_x22,
    _s5_x23, s5_x24, s5_x25, s5_x26, s5_x27, s5_x28, s5_x29, htr5, hvregs5⟩
  have htr50 : s5.trace = s0.trace := htr5.trans htr40
  have hvregs50 : calleeSavedVRegs s5 = calleeSavedVRegs s0 := hvregs5.trans hvregs40
  have s5_x19' : s5.readReg64 .x19 =
      match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length :=
    s5_x19.trans s4_x19'
  refine preKeyMsg_seq_wpp htr50
    (preKeyMsg_alloc_ser_wpp_ext hA hSh hEncLen x s0.sp (s4.readReg64 .x19) kyberCopyPtr
      (s3.readReg64 .x28) (s3.readReg64 .x0) (s4.readReg64 .x26)
      w368 w144 w136 w128 ver32 pkId32 s4_x19' hky_len hmsg_len63 hver hfit s5
      hpc5 hrun5 hsp5 hsp5_align s5_x0 s5_x19 s5_x20 s5_x21 s5_x22 s5_x24 s5_x25
      s5_x26 s5_x27 s5_x28 s5_x29)
    (by sep_focus) (fun _ _ h => panicAllocPost_of_eq h) ?_
  intro sf hpcf hrunf ⟨hspf, hspf_align, sf_x19, sf_x20, sf_x21, sf_x22, sf_x24,
    sf_x25, sf_x27, sf_x28, sf_x29, htrf, hvregsf⟩
  have htrf0 : sf.trace = s0.trace := htrf.trans htr50
  have hvregsf0 : calleeSavedVRegs sf = calleeSavedVRegs s0 := hvregsf.trans hvregs50
  have sf_x19' : sf.readReg64 .x19 =
      match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length :=
    sf_x19.trans s4_x19'
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun serPtr => ?_
  apply SepWPp.done hpcf hrunf
  intro R' hmf
  let g : PreKeyMsgFrameGhost :=
    { serPtr := serPtr, kyberCopyPtr := kyberCopyPtr, bkSerPtr := s3.readReg64 .x28,
      ikSerPtr := s3.readReg64 .x0, msgCopyPtr := s4.readReg64 .x26, ver32 := ver32,
      preKeyVal32 := pkId32, kyberId32 := kyberIdOf x.kp w324 }
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · rw [hpcf, fnAddr_preKeyMsgNew_eq_ext (img := img) (ext := ext), preKeyMsgSeamAPC]
  · refine ⟨hfit, hver, hpk, fun k hk => ?_⟩
    simp [g, kyberIdOf, hk]
  · refine ⟨hrunf, hspf, hsp, hspf_align, htrf0, sf_x29, sf_x19', ?_, ?_, sf_x22, sf_x24, ?_, sf_x27, sf_x28, hvregsf0⟩
    · rw [sf_x20, setWidth32_zeroExtend64]
    · rw [sf_x21, setWidth32_zeroExtend64]
    · rw [sf_x25, setWidth32_zeroExtend64]
  · rw [preKeyMsgFrameSlotsAt_one_eq_vec]
    simp (disch := decide) only [preKeyMsgFrameSlotsAt, preKeyMsgHeapAt, g, bv_sub_add_lit, Nat.reduceSub,
      sepConj_assoc] at hmf ⊢
    exact satisfies_of_sep_focus hmf (by sep_focus)

theorem prologue_ok_trap (h3 : TripleRatchetHooks C A S (trTrapExterns C abs))
    (_himg : Obj.Loads libsignalSessionImage img)
    (hEncLen : PreKeyMsgEncodedLenOk_trap img C A abs)
    (x : PreKeyMsgNewCall) (R : SepProp) (s0 : State)
    (hs : s0.status = .Running) (hpc : s0.pc = preKeyMsgNewEntry img) (hsp : s0.spAligned = true)
    (hpre : s0.mem ⊨ (preKeyMsgNewSpec A).pre x s0 ∗ R) :
    PreKeyMsgSegExit_trap img C A abs x R s0 s0 (fun s => ∃ g, SeamA img A x g R s0 s) :=
  prologue_ok_ext h3.alloc trTrap_shim_hookSat trTrap_memcpy_hookSat _himg hEncLen
    x R s0 hs hpc hsp hpre

/-! ## Relocatable Placement Proofs -/

open CryptoVerification.LibsignalPublicApi.Placed

private theorem subroutine_ok_withLsCl_of_plain [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCl lsmpl spec) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  dsimp only [withLsCl] at hpre
  rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre'⟩ := hpre
  obtain ⟨sf, hsteps, hout, _⟩ := h.no_fault_before_outcome x R s0 hpc hrun hpre' hsp hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcl0.of_keepsFrozen hsteps.keepsFrozen, hpost⟩
  · exact Or.inr hrest

theorem preKeyMsg_store_wire_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (x : PreKeyMsgNewCall) (sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr w352 : BitVec 64)
    (w344_32 pkId32 kyberId32 : BitVec 32)
    (hkyCap : kyberCap = match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hpk : ∀ v, x.preKeyId = some v → pkId32 = v)
    (hkyId : ∀ k, x.kp = some k → kyberId32 = k.preKeyId)
    (hmsg_len : x.msg.serialized.length < 2 ^ 63) (s : State)
    (hpc : s.pc = (blkPl_41).base + 428#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = ikSerPtr) (hx8 : s.readReg64 .x8 = 1#64)
    (hx19 : s.readReg64 .x19 = kyberCap) (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64) (hx24 : s.readReg64 .x24 = 33#64)
    (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64) (hx26 : s.readReg64 .x26 = msgCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = bkSerPtr) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWP (lsProg_41 H) ((blkPl_41).base + 496#64) s
      (((sp0 - 352#64) ↦₆₄ w352) ∗ ((sp0 - 344#64) ↦₃₂ w344_32) ∗ ((sp0 - 328#64) ↦₃₂ x.spk) ∗
       ((sp0 - 324#64) ↦₃₂ kyberId32) ∗ ((sp0 - 320#64) ↦₆₄ kyberCopyPtr) ∗
       ((sp0 - 296#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
       ((sp0 - 292#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
       memRegion (sp0 - 272#64) 128 ∗ optKyberCopyBuf A kyberCopyPtr x.kp ∗
       boxU8Buf A bkSerPtr x.baseKey.serialize ∗ boxU8Buf A ikSerPtr x.ik.serialize ∗
       boxU8Buf A msgCopyPtr x.msg.serialized)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x0 = sp0 - 272#64 ∧
         sm.readReg64 .x19 = kyberCap ∧ sm.readReg64 .x20 = (if x.preKeyId.isSome then 1#32 else 0#32).zeroExtend 64 ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧ sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧ sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧ sm.readReg64 .x26 = msgCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = bkSerPtr ∧ sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ ((sp0 - 352#64) ↦₆₄ ikSerPtr) ∗ ((sp0 - 344#64) ↦₃₂ x.regId) ∗ ((sp0 - 328#64) ↦₃₂ x.spk) ∗
          ((sp0 - 324#64) ↦₃₂ kyberId32) ∗ ((sp0 - 320#64) ↦₆₄ kyberCopyPtr) ∗
          ((sp0 - 296#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
          ((sp0 - 292#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
          wirePreKeySignalMessageAt A (x.mkWirePins kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr)
            (sp0 - 272#64) x.protoMsg)) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx0 hx8 hx19 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
  rw [memRegion_wire_128 sp0]; cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => ?_
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
  · simp only [State.spAligned, wp_norm, arm64_norm, *]
  · have hpack := pack_wirePreKeySignalMessageAt A x sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr
      msgCopyPtr pkId32 kyberId32 hkyCap hpk hkyId hmsg_len
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hpack)))))))
    simp only [← hkyCap, Option.isSome, arm64_norm]; exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_alloc_ser_wpp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hEncLen : PreKeyMsgEncodedLenPlacedOk A H)
    (x : PreKeyMsgNewCall) (sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr
      w368 w144 w136 w128 : BitVec 64) (ver32 pkId32 : BitVec 32)
    (hkyCap : kyberCap = match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hky_len : ∀ k, x.kp = some k → k.ciphertext.length < 2 ^ 63)
    (hmsg_len : x.msg.serialized.length < 2 ^ 63)
    (hver : ver32.setWidth 8 = x.ver) (hfit : x.model.serialized.length < 2 ^ 42)
    (s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 496#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp0 - 272#64) (hx19 : s.readReg64 .x19 = kyberCap)
    (hx20 : s.readReg64 .x20 = (if x.preKeyId.isSome then 1#32 else 0#32).zeroExtend 64)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64) (hx22 : s.readReg64 .x22 = 33#64)
    (hx24 : s.readReg64 .x24 = 33#64) (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = msgCopyPtr) (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = bkSerPtr) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (lsProg_41 H) ((blkPl_41).base + 604#64) s
      (((sp0 - 368#64) ↦₆₄ w368) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
       wirePreKeySignalMessageAt A (x.mkWirePins kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr)
         (sp0 - 272#64) x.protoMsg ∗
       ((sp0 - 144#64) ↦₆₄ w144) ∗ ((sp0 - 136#64) ↦₆₄ w136) ∗ ((sp0 - 128#64) ↦₆₄ w128) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x19 = kyberCap ∧
         sm.readReg64 .x20 = (if x.preKeyId.isSome then 1#32 else 0#32).zeroExtend 64 ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧ sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x24 = 33#64 ∧ sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = bkSerPtr ∧ sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ ∃∗ serPtr : BitVec 64,
          ((sp0 - 368#64) ↦₆₄ msgCopyPtr) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗ memRegion (sp0 - 272#64) 128 ∗
          vecU8At A (sp0 - 144#64) (BitVec.ofNat 64 x.model.serialized.length) serPtr [versionByte x.ver] ∗
          optKyberCopyBuf A kyberCopyPtr x.kp ∗ boxU8Buf A bkSerPtr x.baseKey.serialize ∗
          boxU8Buf A ikSerPtr x.ik.serialize ∗ boxU8Buf A msgCopyPtr x.msg.serialized ∗
          A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) := by
  have hunpack := unpack_wirePreKeySignalMessageAt A x sp0 kyberCap kyberCopyPtr
    bkSerPtr ikSerPtr msgCopyPtr hkyCap hky_len hmsg_len
  have hver_byte : BitVec.zeroExtend 8 (4#64 ||| BitVec.zeroExtend 64 (ver32 <<< 4)) = versionByte x.ver := by
    rw [versionByte_word_eq' ver32, hver]
  clear hkyCap hky_len hmsg_len hver
  have henc := preKeyMsg_encodedLen_placed_ok hEncLen
  have h_shim := subroutine_ok_withLsCl_of_plain (preKeyMsg_shim_placed_ok hshim)
  have h_alloc := subroutine_ok_withLsCl_of_plain (preKeyMsg_alloc_placed_ok halloc)
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have hmod_len : x.model.serialized.length = x.protoMsg.encode.length + 1 := model_serialized_length x
  have hfit62 : x.protoMsg.encode.length + 1 < 2 ^ 62 := by omega
  have hwire_fit : PreKeyMsgWireLengthsFit x.protoMsg := preKeyMsgWireLengthsFit_protoMsg x (by omega)
  clear hfit
  obtain ⟨hovf_ult, hovf_msb, hovf_hi, hovf_add, hovf_toNat⟩ := preKeyMsg_encLen_overflow_checks hfit62
  rw [hovf_add] at hovf_ult hovf_msb
  simp only [arm64_norm] at hx0 hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx27 hx28 hx29
  let wg := x.mkWirePins kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr
  apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_119).base); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
  intro hcl0
  refine SepWPp.call (x := ⟨sp0 - 272#64, wg, x.protoMsg⟩)
    (F := ((sp0 - 368#64) ↦₆₄ w368) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗ ((sp0 - 144#64) ↦₆₄ w144) ∗
          ((sp0 - 136#64) ↦₆₄ w136) ∗ ((sp0 - 128#64) ↦₆₄ w128) ∗ A.pool ∗
          memRegion (sp0 - 368#64 - 4096#64) 4080 ∗ memRegion (sp0 - 368#64 - 7824#64) 3728)
    henc (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align]) (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    rw [stackAt_preKeyMsgSubStack_to_allocHook (sp0 - 368#64), stackAt_allocHook_split_encodedLen (sp0 - 368#64)] at hm
    dsimp only [withLsCl]
    rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl _⌝, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    simp only [preKeyMsgEncodedLenSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  dsimp only [withLsCl]; simp only [preKeyMsgEncodedLenSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun hcl1 => ?_
  refine SepWPp.pure_elim fun ⟨hx0_1, htr1⟩ => ?_
  simp only [wp_norm, arm64_norm] at hx0_1 htr1
  apply SepWPp.of_sepWP_lscl hcl1 (mid := lsρ lsRustNoAllocShimSym); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl1'
  refine SepWPp.call (x := ())
    (F := ((sp0 - 368#64) ↦₆₄ msgCopyPtr) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
          wirePreKeySignalMessageAt A wg (sp0 - 272#64) x.protoMsg ∗ ((sp0 - 144#64) ↦₆₄ w144) ∗
          ((sp0 - 136#64) ↦₆₄ w136) ∗ ((sp0 - 128#64) ↦₆₄ w128) ∗ A.pool ∗ stackAt s.sp preKeyMsgEncodedLenStack ∗
          memRegion (sp0 - 368#64 - 4096#64) 4080 ∗ memRegion (sp0 - 368#64 - 7824#64) 3728)
    h_shim (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align]) (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    dsimp only [withLsCl]
    rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl _⌝, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl1', ?_⟩
    simp only [noAllocShimSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf2 hpc2 hrun2 hsp2 ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  dsimp only [withLsCl]; simp only [noAllocShimSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun hcl2 => ?_
  refine SepWPp.pure_elim fun htr2 => ?_
  simp only [wp_norm, arm64_norm, htr1] at htr2
  apply SepWPp.of_sepWP_lscl hcl2 (mid := lsρ lsRustAllocSym); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl2'
  refine SepWPp.call (x := (x.protoMsg.encode.length + 1, 1))
    (F := ((sp0 - 368#64) ↦₆₄ msgCopyPtr) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
          wirePreKeySignalMessageAt A wg (sp0 - 272#64) x.protoMsg ∗ ((sp0 - 144#64) ↦₆₄ w144) ∗
          ((sp0 - 136#64) ↦₆₄ w136) ∗ ((sp0 - 128#64) ↦₆₄ w128) ∗ memRegion (sp0 - 368#64 - 7824#64) 3728)
    h_alloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align]) (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    dsimp only [withLsCl]
    rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl _⌝, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl2', ?_⟩
    simp only [rustAllocSpec, LayoutOk, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
    rw [stackAt_allocHook_split_encodedLen (sp0 - 368#64)]
    simp only [sepConj_assoc, arm64_norm]
    exact ⟨⟨by omega, ⟨0, rfl⟩, by omega⟩, satisfies_of_sep_focus hm (by sep_focus)⟩
  intro sf3 hpc3 hrun3 hsp3 ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
  simp only [wp_norm, arm64_norm, *] at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
  dsimp only [withLsCl]
  rw [sepConj_assoc ⌜LibsignalCodeLoaded lsmpl sf3.mem⌝]
  refine SepWPp.pure_elim fun hcl3 => ?_
  by_cases hoom : sf3.readReg64 .x0 = 0#64
  · have hoom0 : (sf3.readReg64 .x0 = 0) = True := eq_true hoom
    simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_oom]
    refine SepWPp.pure_elim fun htr3 => ?_; simp only [wp_norm, arm64_norm, htr2] at htr3 hoom
    apply SepWPp.of_sepWP (mid := (blkPl_41).base + 516#64); wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    exact preKeyMsg_oom_at_204_placed hpanic (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  · have hoom0 : (sf3.readReg64 .x0 = 0) = False := eq_false hoom
    simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_ok]
    refine SepWPp.pure_elim fun ⟨halign_ptr, htr3⟩ => ?_
    have hoom_beq : (sf3.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    simp only [wp_norm, arm64_norm, htr2] at htr3 hoom hoom_beq
    rw [memRegion_split' (b := sf3.readReg64 (Reg.gpr 0#5)) (b' := sf3.readReg64 (Reg.gpr 0#5) + 1#64)
          (n := 1) (k := x.protoMsg.encode.length) (by omega) rfl (by omega),
        ProofLib.memRegion_one (sf3.readReg64 (Reg.gpr 0#5))]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    apply SepWPp.of_sepWP_lscl hcl3 (mid := (blkPl_119).base); wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
    intro hcl3'
    refine SepWPp.call (x := ⟨sp0 - 272#64, wg, x.protoMsg⟩)
      (F := (sf3.readReg64 (Reg.gpr 0#5) ↦₈ versionByte x.ver) ∗ ((sp0 - 128#64) ↦₆₄ 1#64) ∗
            ((sp0 - 144#64) ↦₆₄ BitVec.ofNat 64 (x.protoMsg.encode.length + 1)) ∗
            ((sp0 - 136#64) ↦₆₄ sf3.readReg64 (Reg.gpr 0#5)) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
            A.live (sf3.readReg64 (Reg.gpr 0#5)) (x.protoMsg.encode.length + 1) 1 ∗
            memRegion (sf3.readReg64 (Reg.gpr 0#5) + 1#64) x.protoMsg.encode.length ∗ A.pool ∗
            ((sp0 - 368#64) ↦₆₄ msgCopyPtr) ∗ memRegion (sp0 - 368#64 - 4096#64) 4080 ∗
            memRegion (sp0 - 368#64 - 7824#64) 3728)
      henc (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp3, hsp0_align]) (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      dsimp only [withLsCl]
      rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl _⌝, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hcl3', ?_⟩
      simp only [preKeyMsgEncodedLenSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      rw [stackAt_allocHook_split_encodedLen (sp0 - 368#64)] at hm
      simp only [sepConj_assoc, arm64_norm] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus)
    intro sf4 hpc4 hrun4 hsp4 ⟨h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, hfp_4⟩
    simp only [wp_norm, arm64_norm, *] at hsp4 h19_4 h20_4 h21_4 h22_4 h23_4 h24_4 h25_4 h26_4 h27_4 h28_4 hfp_4
    dsimp only [withLsCl]; simp only [preKeyMsgEncodedLenSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun _hcl4 => ?_
    refine SepWPp.pure_elim fun ⟨hx0_4, htr4⟩ => ?_
    simp only [wp_norm, arm64_norm, htr3] at hx0_4 htr4
    apply SepWPp.of_sepWP_ret; wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · simp only [State.spAligned, wp_norm, arm64_norm, *]
    · refine Entails.sepExists_right (sf3.readReg64 (Reg.gpr 0#5)) ?_
      have hser := (pack_serPrefix0 A sp0 (sf3.readReg64 (Reg.gpr 0#5)) x.ver
        x.protoMsg.encode.length hfit62 hoom).symm
      rw [hmod_len, hser, stackAt_preKeyMsgSubStack_to_allocHook (sp0 - 368#64),
          stackAt_allocHook_split_encodedLen (sp0 - 368#64)]
      refine Entails.trans (sepConj_mono_left hunpack) ?_
      simp only [hsp3, arm64_norm]; exact entails_of_sep_focus (by sep_focus)

theorem PreKeyMsgSegExit_placed.of_sepWPp_seamA [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : PreKeyMsgNewCall} {R P : SepProp} {s0 : State}
    (hm : s0.mem ⊨ P ∗ R)
    (hwpp : SepWPp (lsProg_41 H) ((blkPl_41).base + 604#64) s0 P
      (fun sf P_f => ∀ R', sf.mem ⊨ P_f ∗ R' → ∃ g, SeamA_placed A x g R' s0 sf)
      (PanicAllocPost s0)) :
    PreKeyMsgSegExit_placed A H x R s0 s0 (fun s => ∃ g, SeamA_placed A x g R s0 s) := by
  intro hL
  obtain ⟨sf, hsteps, ⟨_hpc, _hrun, P_f, hmf, hq⟩ | ⟨hpan, P_f, hmf, hp⟩ | ⟨_, _hoom⟩⟩ := hwpp R hm hL
  · exact ⟨sf, hsteps, Or.inl (hq R hmf)⟩
  · have hpan' : sf.status = .Panicked := by simpa [Rust.panicked] using hpan
    exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan', hp R hmf⟩))⟩
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim

theorem preKeyMsg_seq_wpp'_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)) (PanicAllocPost s))
    (hfocus : P = P1 ∗ F)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → LibsignalCodeLoaded lsmpl sm.mem → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | ⟨_, _hoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      h2 sm hpcm hrunm (hcl.of_keepsFrozen hsteps.keepsFrozen) hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by simpa [allocFailedIn, htr] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim

theorem prologue_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H "memcpy" framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hEncLen : PreKeyMsgEncodedLenPlacedOk A H)
    (x : PreKeyMsgNewCall) (R : SepProp) (s0 : State)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hs : s0.status = .Running)
    (hpc : s0.pc = preKeyMsgNewEntry_placed)
    (hsp : s0.spAligned = true)
    (hpre : s0.mem ⊨ (preKeyMsgNewSpec A).pre x s0 ∗ R) :
    PreKeyMsgSegExit_placed A H x R s0 s0 (fun s => ∃ g, SeamA_placed A x g R s0 s) := by
  simp only [preKeyMsgNewSpec, sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hfit⟩, hpre⟩
  have hky_len := optKyberAt_length_lt hpre
  rw [optKyberAt_eq_word0_and_rest A x.kyA x.kyPtr x.kp, stackAt_preKeyMsgNewStack_ready s0.sp] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨w368, w360, w352, w344, w332, w328, w324, w320, w312, w304,
    w296, w292, w288, w280, w144, w136, w128, hpre⟩
  simp only [← sepConj_assoc] at hpre
  let ver32 : BitVec 32 := (s0.readReg64 .x0).setWidth 32
  let pkId32 : BitVec 32 := (s0.readReg64 .x3).setWidth 32
  have hver : ver32.setWidth 8 = x.ver := by dsimp [ver32]; rw [setWidth8_setWidth32, hx0]
  have hpk : ∀ v, x.preKeyId = some v → pkId32 = v := hx3
  refine PreKeyMsgSegExit_placed.of_sepWPp_seamA hpre ?_
  refine preKeyMsg_seq_wp_lscl hcl
    (preKeyMsg_entry_to_04c_wp_placed x s0.sp w304 w288 w280 w292 s0 hpc hs rfl hsp
      hx1 hx2 hx4 hx5 hx6 hx7 hx8) (by sep_focus) ?_
  intro s1 hpc1 hrun1 hcl1 ⟨hsp1, hsp1_align, s1_x6, s1_x20, s1_x21, s1_x22, s1_x23,
    s1_x25, s1_x26, s1_x29, htr1, hvregs1⟩
  refine preKeyMsg_seq_wpp_lscl hcl1 htr1
    (preKeyMsg_kyber_clone_wpp_placed hshim halloc hmemcpy hpanic x s0.sp w320 w312 w324 w296 ver32 pkId32 s1
      hpc1 hrun1 hsp1 hsp1_align s1_x6 s1_x20 s1_x21 s1_x22 s1_x23 s1_x25 s1_x26 s1_x29)
    (by sep_focus) (fun _ _ h => panicAllocPost_of_eq h) ?_
  intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hsp2_align, s2_x6, s2_x19, s2_x21, s2_x22, s2_x23,
    s2_x25, s2_x26, s2_x29, htr2, hvregs2⟩
  have htr20 : s2.trace = s0.trace := htr2.trans htr1
  have hvregs20 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2.trans hvregs1
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun kyberCopyPtr => SepWPp.exists_elim fun w312' => ?_
  simp only [sepConj_assoc]; refine SepWPp.pure_elim fun hky_ptr_ne => ?_
  refine preKeyMsg_seq_wpp'_lscl hcl2 htr20
    (preKeyMsg_pk_serialize_wpp_placed hshim halloc hpanic x s0.sp (s2.readReg64 .x19) ver32 pkId32 s2
      hcl2 hpc2 hrun2 hsp2 hsp2_align s2_x6 rfl s2_x21 s2_x22 s2_x23 s2_x25 s2_x26 s2_x29)
    (by sep_focus) (fun _ _ h => panicAllocPost_of_eq h) ?_
  intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hsp3_align, s3_x1, s3_x19, s3_x20, s3_x21, s3_x22,
    s3_x23, s3_x24, s3_x25, s3_x26, s3_x29, htr3, hvregs3⟩
  have htr30 : s3.trace = s0.trace := htr3.trans htr20
  have hvregs30 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := hvregs3.trans hvregs20
  have s3_x19' : s3.readReg64 .x19 =
      match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length :=
    s3_x19.trans s2_x19
  refine preKeyMsg_seq_wpp'_lscl hcl3 htr30
    (preKeyMsg_msg_clone_wpp_placed hshim halloc hmemcpy hpanic x s0.sp (s3.readReg64 .x19)
      (s3.readReg64 .x28) (s3.readReg64 .x0) w360 w344 w312' w332 w328 ver32 pkId32 s3
      hpc3 hrun3 hsp3 hsp3_align rfl s3_x1 rfl s3_x20 s3_x21 s3_x22 s3_x23 s3_x24 s3_x25
      s3_x26 rfl s3_x29)
    (by sep_focus) (fun _ _ h => panicAllocPost_of_eq h) ?_
  intro s4 hpc4 hrun4 hcl4 ⟨hsp4, hsp4_align, s4_x0, s4_x8, s4_x19, s4_x22, s4_x23,
    s4_x24, s4_x25, s4_x27, s4_x28, s4_x29, htr4, hvregs4, _hmsg9, hmsg_lt40, _hmsg_ptr_ne⟩
  have htr40 : s4.trace = s0.trace := htr4.trans htr30
  have hvregs40 : calleeSavedVRegs s4 = calleeSavedVRegs s0 := hvregs4.trans hvregs30
  have s4_x19' : s4.readReg64 .x19 =
      match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length :=
    s4_x19.trans s3_x19'
  have hmsg_len63 : x.msg.serialized.length < 2 ^ 63 := by omega
  have hkyId : ∀ k, x.kp = some k → kyberIdOf x.kp w324 = k.preKeyId := fun k hk => by simp [kyberIdOf, hk]
  refine preKeyMsg_convert_344 s0.sp 33#64 (by sep_focus) fun w344_32 => ?_
  refine preKeyMsg_seq_wp_lscl hcl4
    (preKeyMsg_store_wire_wp_placed x s0.sp (s4.readReg64 .x19) kyberCopyPtr
      (s3.readReg64 .x28) (s3.readReg64 .x0) (s4.readReg64 .x26) w352
      w344_32 pkId32 (kyberIdOf x.kp w324) s4_x19' hpk hkyId hmsg_len63 s4
      hpc4 hrun4 hsp4 hsp4_align s4_x0 s4_x8 rfl s4_x22 s4_x23 s4_x24 s4_x25 rfl s4_x27
      s4_x28 s4_x29) (by sep_focus) ?_
  intro s5 hpc5 hrun5 hcl5 ⟨hsp5, hsp5_align, s5_x0, s5_x19, s5_x20, s5_x21, s5_x22,
    _s5_x23, s5_x24, s5_x25, s5_x26, s5_x27, s5_x28, s5_x29, htr5, hvregs5⟩
  have htr50 : s5.trace = s0.trace := htr5.trans htr40
  have hvregs50 : calleeSavedVRegs s5 = calleeSavedVRegs s0 := hvregs5.trans hvregs40
  have s5_x19' : s5.readReg64 .x19 =
      match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length :=
    s5_x19.trans s4_x19'
  refine preKeyMsg_seq_wpp_lscl hcl5 htr50
    (preKeyMsg_alloc_ser_wpp_placed hshim halloc hpanic hEncLen x s0.sp (s4.readReg64 .x19) kyberCopyPtr
      (s3.readReg64 .x28) (s3.readReg64 .x0) (s4.readReg64 .x26)
      w368 w144 w136 w128 ver32 pkId32 s4_x19' hky_len hmsg_len63 hver hfit s5 hcl5
      hpc5 hrun5 hsp5 hsp5_align s5_x0 s5_x19 s5_x20 s5_x21 s5_x22 s5_x24 s5_x25
      s5_x26 s5_x27 s5_x28 s5_x29)
    (by sep_focus) (fun _ _ h => panicAllocPost_of_eq h) ?_
  intro sf hpcf hrunf hclf ⟨hspf, hspf_align, sf_x19, sf_x20, sf_x21, sf_x22, sf_x24,
    sf_x25, sf_x27, sf_x28, sf_x29, htrf, hvregsf⟩
  have htrf0 : sf.trace = s0.trace := htrf.trans htr50
  have hvregsf0 : calleeSavedVRegs sf = calleeSavedVRegs s0 := hvregsf.trans hvregs50
  have sf_x19' : sf.readReg64 .x19 =
      match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length :=
    sf_x19.trans s4_x19'
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun serPtr => ?_
  apply SepWPp.done hpcf hrunf
  intro R' hmf
  let g : PreKeyMsgFrameGhost :=
    { serPtr := serPtr, kyberCopyPtr := kyberCopyPtr, bkSerPtr := s3.readReg64 .x28,
      ikSerPtr := s3.readReg64 .x0, msgCopyPtr := s4.readReg64 .x26, ver32 := ver32,
      preKeyVal32 := pkId32, kyberId32 := kyberIdOf x.kp w324 }
  refine ⟨g, hpcf, hclf, ⟨hfit, hver, hpk, fun k hk => by simp [g, kyberIdOf, hk]⟩, ?_, ?_⟩
  · refine ⟨hrunf, hspf, hsp, hspf_align, htrf0, sf_x29, sf_x19', ?_, ?_, sf_x22, sf_x24, ?_, sf_x27, sf_x28, hvregsf0⟩
    · rw [sf_x20, setWidth32_zeroExtend64]
    · rw [sf_x21, setWidth32_zeroExtend64]
    · rw [sf_x25, setWidth32_zeroExtend64]
  · rw [preKeyMsgFrameSlotsAt_one_eq_vec]
    simp (disch := decide) only [preKeyMsgFrameSlotsAt, preKeyMsgHeapAt, g, bv_sub_add_lit, Nat.reduceSub,
      sepConj_assoc] at hmf ⊢
    exact satisfies_of_sep_focus hmf (by sep_focus)

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Prologue
