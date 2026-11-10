/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.ProtocolErrCommon
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply

/-!
# `CiphertextMessage` Drop Tail (`+0xd40..+0xd4c` → `+0x46c`)

Proves `cmDrop_run` and `tailCmDrop` (along with trap-mode counterparts), invoking
`drop_glue::<CiphertextMessage>` at `sp + 0x370` and continuing into the T1 `tailDropRecord` tail.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?

/-- The CM drop packet `+0xd40 → bl (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]") → +0x46c`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.cmDrop_run_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hdrop : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmDropOk_trap img C A abs)
    (w0 w1 w2 : BitVec 64) (m : CiphertextMessage) (s : State)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0xd40#64) (hrun : s.status = .Running)
    (hal : s.spAligned = true) (hregs : tailRegs w0 w1 w2 s.sp s) :
    SepWP (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x46c#64) s
      (apiEncResultAt A (s.sp + 0x370#64) (.ok m) ∗ A.pool ∗ stackAt s.sp (allocHookStack + 0x40))
      (fun s' P => s'.sp = s.sp ∧ s'.trace = s.trace ∧ s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s' = calleeSavedVRegs s ∧ tailRegs w0 w1 w2 s.sp s' ∧
        ∀ m F, (m ⊨ P ∗ F) →
          (m ⊨ (memRegion (s.sp + 0x370#64) 248 ∗ A.pool ∗
            stackAt s.sp (allocHookStack + 0x40)) ∗ F)) := by
  obtain ⟨hx26, hx28, hx27, hx21, hx23⟩ := hregs
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry] at hpc ⊢
  rw [entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs) himg] at hpc ⊢
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = num% (ls_off% "libsignal_cli_ratchet::encrypt") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")
  have hcall : subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName +
        BitVec.ofNat 64 (((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))) (cmDropSpec A) := by
    have h : (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName +
        BitVec.ofNat 64 (((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64)) = img.base + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]") := by
      simp only [trTrapProgAt, Program.fnAddr_rebase, hfn]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      rfl
    rw [h]
    exact hdrop
  code_fetches_range CryptoVerification.libsignalSessionCode protocolErrBinCli img.base
    (Rust.withPanics (trTrapExterns C abs)) hfn (num% (ls_off% "libsignal_cli_ratchet::encrypt")) 3392 16
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at *
  clear himg hfn hdrop
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  wp_apply
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *], ?_,
      fun _ _ hm => hm⟩
  unfold tailRegs
  simp only [wp_norm, arm64_norm, *]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.cmDrop_run {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hdrop : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmDropOk img C A ctl abs)
    (w0 w1 w2 : BitVec 64) (m : CiphertextMessage) (s : State)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0xd40#64) (hrun : s.status = .Running)
    (hal : s.spAligned = true) (hregs : tailRegs w0 w1 w2 s.sp s) :
    SepWP (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x46c#64) s
      (apiEncResultAt A (s.sp + 0x370#64) (.ok m) ∗ A.pool ∗ stackAt s.sp (allocHookStack + 0x40))
      (fun s' P => s'.sp = s.sp ∧ s'.trace = s.trace ∧ s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s' = calleeSavedVRegs s ∧ tailRegs w0 w1 w2 s.sp s' ∧
        ∀ m F, (m ⊨ P ∗ F) →
          (m ⊨ (memRegion (s.sp + 0x370#64) 248 ∗ A.pool ∗
            stackAt s.sp (allocHookStack + 0x40)) ∗ F)) := by
  obtain ⟨hx26, hx28, hx27, hx21, hx23⟩ := hregs
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry] at hpc ⊢
  rw [entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) himg] at hpc ⊢
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = num% (ls_off% "libsignal_cli_ratchet::encrypt") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")
  have hcall : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName +
        BitVec.ofNat 64 (((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))) (cmDropSpec A) := by
    have h : (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName +
        BitVec.ofNat 64 (((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64)) = img.base + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]") := by
      simp only [tripleRatchetProgAt, Program.fnAddr_rebase, hfn]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      rfl
    rw [h]
    exact hdrop
  code_fetches_range CryptoVerification.libsignalSessionCode protocolErrBinCli img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (num% (ls_off% "libsignal_cli_ratchet::encrypt")) 3392 16
  dsimp only [tripleRatchetProgAt] at *
  clear himg hfn hdrop
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  wp_apply
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *], ?_,
      fun _ _ hm => hm⟩
  unfold tailRegs
  simp only [wp_norm, arm64_norm, *]

open CryptoVerification.LibsignalPublicApi.StoreKit

/-- **The CM drop**: `tailCmDrop_ok` with the T1 tail theorem (`tailDropRecord_ok`, specialized to this
call's frame, the CM slot emptied) as the hypothesis `hT1`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.tailCmDrop_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage img)
    (hdrop : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmDropOk_trap img C A abs)
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State}
    {answers : StoreAnswers (List (BitVec 8)) Unit} {e : ApiError AddrVal Unit}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {H : SepProp} {scratch : BitVec 64 → SepProp}
    {g : RecordGhost} {rec : SessionRecord (List (BitVec 8))}
    {ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8)))}
    {m : CiphertextMessage}
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0xd40#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A sp scratch g rec ot (some m) (pollWith sp 0x9d0 [w3, w4, w5]) ∗ H)
      R s0 s)
    (hT1 : ∀ s', TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s' →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x46c#64) (tailRegs w0 w1 w2)
        (fun sp => dropRecordSlots A sp scratch g rec ot none (pollWith sp 0x9d0 [w3, w4, w5]) ∗ H)
        R s0 s' →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s' (fun _ => False)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  have hn : allocHookStack + 0x40 ≤ encSubStack := by decide
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.segExit_of_run_trap hm (fun hL => ?_) hT1
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encTail_run_withEncCommon_trap (C := C) (abs := abs)
    (Act := apiEncResultAt A (s0.sp - 0xbe0#64 + 0x370#64) (.ok m) ∗ A.pool ∗
      stackAt (s0.sp - 0xbe0#64) (allocHookStack + 0x40))
    (Act' := memRegion (s0.sp - 0xbe0#64 + 0x370#64) 248 ∗ A.pool ∗
      stackAt (s0.sp - 0xbe0#64) (allocHookStack + 0x40))
    (Fr := (memRegion (s0.sp - 0xbe0#64 + 0x350#64) 0x20 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x468#64) 1) ∗
      dropRecordBase A (s0.sp - 0xbe0#64) scratch g rec ot ∗ pollWith (s0.sp - 0xbe0#64) 0x9d0 [w3, w4, w5] ∗
      H ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encCommonFr A ctl img x (x.draws S answers) s0 (allocHookStack + 0x40))
    hs ?_ ?_ ?_ hL
  · refine Entails.of_eq ?_
    rw [dropRecordSlots_eq, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encCommon_eq A ctl img x (x.draws S answers) s0 _ hn]
    simp only [cmSlotAt]
    ac_rfl
  · refine Entails.of_eq ?_
    rw [dropRecordSlots_eq, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encCommon_eq A ctl img x (x.draws S answers) s0 _ hn, cmSlot_none_eq]
    ac_rfl
  · intro hpc hmeta hregs
    obtain ⟨hrun, hssp, _, hspal, -⟩ := hmeta
    rw [← hssp] at hregs ⊢
    exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.cmDrop_run_trap himg hdrop w0 w1 w2 m s hpc hrun hspal hregs

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.tailCmDrop {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage img)
    (hdrop : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmDropOk img C A ctl abs)
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State}
    {answers : StoreAnswers (List (BitVec 8)) Unit} {e : ApiError AddrVal Unit}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {H : SepProp} {scratch : BitVec 64 → SepProp}
    {g : RecordGhost} {rec : SessionRecord (List (BitVec 8))}
    {ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8)))}
    {m : CiphertextMessage}
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0xd40#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A sp scratch g rec ot (some m) (pollWith sp 0x9d0 [w3, w4, w5]) ∗ H)
      R s0 s)
    (hT1 : ∀ s', TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s' →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x46c#64) (tailRegs w0 w1 w2)
        (fun sp => dropRecordSlots A sp scratch g rec ot none (pollWith sp 0x9d0 [w3, w4, w5]) ∗ H)
        R s0 s' →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s' (fun _ => False)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  have hn : allocHookStack + 0x40 ≤ encSubStack := by decide
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.segExit_of_run hm (fun hL => ?_) hT1
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encTail_run_withEncCommon (C := C) (abs := abs)
    (Act := apiEncResultAt A (s0.sp - 0xbe0#64 + 0x370#64) (.ok m) ∗ A.pool ∗
      stackAt (s0.sp - 0xbe0#64) (allocHookStack + 0x40))
    (Act' := memRegion (s0.sp - 0xbe0#64 + 0x370#64) 248 ∗ A.pool ∗
      stackAt (s0.sp - 0xbe0#64) (allocHookStack + 0x40))
    (Fr := (memRegion (s0.sp - 0xbe0#64 + 0x350#64) 0x20 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x468#64) 1) ∗
      dropRecordBase A (s0.sp - 0xbe0#64) scratch g rec ot ∗ pollWith (s0.sp - 0xbe0#64) 0x9d0 [w3, w4, w5] ∗
      H ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encCommonFr A ctl img x (x.draws S answers) s0 (allocHookStack + 0x40))
    hs ?_ ?_ ?_ hL
  · refine Entails.of_eq ?_
    rw [dropRecordSlots_eq, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encCommon_eq A ctl img x (x.draws S answers) s0 _ hn]
    simp only [cmSlotAt]
    ac_rfl
  · refine Entails.of_eq ?_
    rw [dropRecordSlots_eq, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encCommon_eq A ctl img x (x.draws S answers) s0 _ hn, cmSlot_none_eq]
    ac_rfl
  · intro hpc hmeta hregs
    obtain ⟨hrun, hssp, _, hspal, -⟩ := hmeta
    rw [← hssp] at hregs ⊢
    exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.cmDrop_run himg hdrop w0 w1 w2 m s hpc hrun hspal hregs

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr
