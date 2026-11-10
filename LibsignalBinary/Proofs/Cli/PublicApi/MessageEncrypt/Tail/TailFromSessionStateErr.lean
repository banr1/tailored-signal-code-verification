/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Segs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.Common
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.Common
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailDropRecordSteps
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailDropRecordStepsTrap
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailFetch
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailWriteErr
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFromSessionStateErr
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# T1 `from_session_state` Error Tail (`+0x49c..+0x564`)

Proves `tailFromSessionStateErr_ok` (and `tailFromSessionStateErr_ok_trap`), staging the
`from_session_state` protocol error from `sp + 0x588` to `sp + 0x9d0`, dropping the current session
if present, and continuing into `tailFreePrevSessions_ok` at `+0x564`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalPublicApi.MessageEncrypt

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

variable {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
  {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {abs : String → Option (State → State)}

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.logAddrAtEntry (entry : BitVec 64) : BitVec 64 :=
  ((entry + bv% (1188) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "libsignal_cli_ratchet::encrypt" + 1188))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.tripleRatchetProgAt_fnAddr_encryptWithStores_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = b + bv% (ls_off% "libsignal_cli_ratchet::encrypt") := by
  unfold trTrapProgAt
  rw [Program.fnAddr_rebase, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.tripleRatchetProgAt_fnAddr_encryptWithStores (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = b + bv% (ls_off% "libsignal_cli_ratchet::encrypt") := by
  unfold tripleRatchetProgAt
  rw [Program.fnAddr_rebase, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.logAddrAtEntry_eq_logFilterAddr_trap {img : Obj.Image}
    (hloads : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.logAddrAtEntry ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName) =
      logFilterAddr img := by
  have hbal := ProofLib.base_aligned_of_loads hloads
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.logAddrAtEntry
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.tripleRatchetProgAt_fnAddr_encryptWithStores_trap, BitVec.add_assoc img.base, adrp_page_of_aligned hbal, logFilterAddr]
  have hmask : (((bv% (ls_off% "libsignal_cli_ratchet::encrypt")) + 1188#64 : BitVec 64) &&& bv% (2 ^ 64 - 4096)) = (bv% (page% (ls_off% "libsignal_cli_ratchet::encrypt" + 1188))) := rfl
  rw [hmask]
  bv_omega

/-! ## 1. `SepWP` stepping lemma for `+0x49c..+0x54c` (`1180..1356`) -/

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.logAddrAtEntry_eq_logFilterAddr {img : Obj.Image}
    (hloads : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.logAddrAtEntry ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName) =
      logFilterAddr img := by
  have hbal := ProofLib.base_aligned_of_loads hloads
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.logAddrAtEntry
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.tripleRatchetProgAt_fnAddr_encryptWithStores, BitVec.add_assoc img.base, adrp_page_of_aligned hbal, logFilterAddr]
  have hmask : (((bv% (ls_off% "libsignal_cli_ratchet::encrypt")) + 1188#64 : BitVec 64) &&& bv% (2 ^ 64 - 4096)) = (bv% (page% (ls_off% "libsignal_cli_ratchet::encrypt" + 1188))) := rfl
  rw [hmask]
  bv_omega

set_option maxHeartbeats 800000 in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.fromSessionStateErr_sepWP_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State} {sp logA : BitVec 64}
    {w0 w1 w2 w3 w4 w5 : BitVec 64}
    {u850 u858 u860 u9d0 u9d8 u9e0 uab0 uab8 uac0 uac8 uad0 uad8 : BitVec 64}
    (hlog : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.logAddrAtEntry ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName) = logA)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x49c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp)
    (hx21 : s.readReg64 .x21 = sp + 0x580#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x54c#64) s
      (((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
        ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
        ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5) ∗
        ((sp + 0x850#64) ↦₆₄ u850) ∗ ((sp + 0x858#64) ↦₆₄ u858) ∗
        ((sp + 0x860#64) ↦₆₄ u860) ∗
        ((sp + 0x9d0#64) ↦₆₄ u9d0) ∗ ((sp + 0x9d8#64) ↦₆₄ u9d8) ∗
        ((sp + 0x9e0#64) ↦₆₄ u9e0) ∗
        ((sp + 0xab0#64) ↦₆₄ uab0) ∗ ((sp + 0xab8#64) ↦₆₄ uab8) ∗
        ((sp + 0xac0#64) ↦₆₄ uac0) ∗ ((sp + 0xac8#64) ↦₆₄ uac8) ∗
        ((sp + 0xad0#64) ↦₆₄ uad0) ∗ ((sp + 0xad8#64) ↦₆₄ uad8) ∗
        (logA ↦₆₄ 0#64))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = w1 ∧
        sf.readReg64 .x23 = w2 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = w0 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
          ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
          ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5) ∗
          ((sp + 0x850#64) ↦₆₄ w3) ∗ ((sp + 0x858#64) ↦₆₄ w4) ∗
          ((sp + 0x860#64) ↦₆₄ w5) ∗
          ((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗
          ((sp + 0x9e0#64) ↦₆₄ w5) ∗
          ((sp + 0xab0#64) ↦₆₄ w0) ∗ ((sp + 0xab8#64) ↦₆₄ w1) ∗
          ((sp + 0xac0#64) ↦₆₄ w2) ∗ ((sp + 0xac8#64) ↦₆₄ w3) ∗
          ((sp + 0xad0#64) ↦₆₄ w4) ∗ ((sp + 0xad8#64) ↦₆₄ w5) ∗
          (logA ↦₆₄ 0#64))) := by
  subst hsp
  subst hlog
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.logAddrAtEntry
  have hfn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4
  messageEncryptTail_fetches_cli b (Rust.withPanics (trTrapExterns C abs)) hfn 1180 32
  messageEncryptTail_fetches_cli b (Rust.withPanics (trTrapExterns C abs)) hfn 1324 32
  generalize_entry (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  exact ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by ac_rfl⟩

/-! ## 2. Frame splitting and weakening lemmas for `pollWith` and `memRegion` -/

set_option maxHeartbeats 800000 in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.fromSessionStateErr_sepWP {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp logA : BitVec 64}
    {w0 w1 w2 w3 w4 w5 : BitVec 64}
    {u850 u858 u860 u9d0 u9d8 u9e0 uab0 uab8 uac0 uac8 uad0 uad8 : BitVec 64}
    (hlog : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.logAddrAtEntry ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName) = logA)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x49c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp)
    (hx21 : s.readReg64 .x21 = sp + 0x580#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x54c#64) s
      (((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
        ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
        ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5) ∗
        ((sp + 0x850#64) ↦₆₄ u850) ∗ ((sp + 0x858#64) ↦₆₄ u858) ∗
        ((sp + 0x860#64) ↦₆₄ u860) ∗
        ((sp + 0x9d0#64) ↦₆₄ u9d0) ∗ ((sp + 0x9d8#64) ↦₆₄ u9d8) ∗
        ((sp + 0x9e0#64) ↦₆₄ u9e0) ∗
        ((sp + 0xab0#64) ↦₆₄ uab0) ∗ ((sp + 0xab8#64) ↦₆₄ uab8) ∗
        ((sp + 0xac0#64) ↦₆₄ uac0) ∗ ((sp + 0xac8#64) ↦₆₄ uac8) ∗
        ((sp + 0xad0#64) ↦₆₄ uad0) ∗ ((sp + 0xad8#64) ↦₆₄ uad8) ∗
        (logA ↦₆₄ 0#64))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = w1 ∧
        sf.readReg64 .x23 = w2 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = w0 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
          ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
          ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5) ∗
          ((sp + 0x850#64) ↦₆₄ w3) ∗ ((sp + 0x858#64) ↦₆₄ w4) ∗
          ((sp + 0x860#64) ↦₆₄ w5) ∗
          ((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗
          ((sp + 0x9e0#64) ↦₆₄ w5) ∗
          ((sp + 0xab0#64) ↦₆₄ w0) ∗ ((sp + 0xab8#64) ↦₆₄ w1) ∗
          ((sp + 0xac0#64) ↦₆₄ w2) ∗ ((sp + 0xac8#64) ↦₆₄ w3) ∗
          ((sp + 0xad0#64) ↦₆₄ w4) ∗ ((sp + 0xad8#64) ↦₆₄ w5) ∗
          (logA ↦₆₄ 0#64))) := by
  subst hsp
  subst hlog
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.logAddrAtEntry
  have hfn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4
  messageEncryptTail_fetches_cli b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 1180 32
  messageEncryptTail_fetches_cli b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 1324 32
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  exact ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by ac_rfl⟩

def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.encCommonRest (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (draws : Nat) (s0 : State) : SepProp :=
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ nowAt s0.sp x.now ∗
    CryptoVerification.SignalSession.Coins.coinsAfter ctl x.cur x.rest draws ∗
    stackAt (s0.sp - 0xbe0#64) encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.encCommon_eq_logOff_rest (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (draws : Nat) (s0 : State) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 =
      (logFilterAddr img ↦₆₄ 0#64) ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.encCommonRest A img.base x draws s0 := by
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon logOff CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.encCommonRest
  ac_rfl

/-! ## 3. `tailFromSessionStateErr_ok` (`+0x49c..+0x564`) -/

open CryptoVerification.LibsignalPublicApi.StoreKit

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.tailFromSessionStateErr_ok_trap {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x49c#64)
      (fun sp s => s.readReg64 .x21 = sp + 0x580#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
        s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
      (fun sp => curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H)
      R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let R := encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    ⟨hx21, hx25, hx26, hx28⟩, hstack_le, hmem⟩
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry_trap (C := C) (abs := abs) env.loads] at hpc
  let sp := s0.sp - 0xbe0#64
  change s.mem ⊨
    (curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R at hmem
  have h1ea : memRegion (sp + 0x280#64) 0x1ea =
      memRegion (sp + 0x280#64) 0x1e9 ∗ memRegion (sp + 0x469#64) 1 := by
    rw [memRegion_split' (b := sp + 0x280#64) (b' := sp + 0x469#64) (N := 0x1ea) (n := 0x1e9) (k := 1)
          (by decide) (by bv_omega) (by decide)]
  rw [h1ea, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.encCommon_eq_logOff_rest A ctl img x (x.draws S answers) s0] at hmem
  let F_inv := curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
    memRegion (sp + 0x280#64) 0x1e9 ∗ H ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.encCommonRest A img.base x (x.draws S answers) s0 ∗ R
  have hmem_469 : s.mem ⊨
      memRegion (sp + 0x469#64) 1 ∗
      (pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗ F_inv) := by
    have heq :
        ((curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
          (memRegion (sp + 0x280#64) 0x1e9 ∗ memRegion (sp + 0x469#64) 1) ∗
          pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         ((logFilterAddr img ↦₆₄ 0#64) ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.encCommonRest A img.base x (x.draws S answers) s0) ∗ R) =
        (memRegion (sp + 0x469#64) 1 ∗
         (pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
           (logFilterAddr img ↦₆₄ 0#64) ∗ F_inv)) := by
      dsimp only [F_inv]; ac_rfl
    rwa [← heq]
  obtain ⟨b469, hmem_b469⟩ := satisfies_memRegion_1 hmem_469
  have hmem_poll : s.mem ⊨
      pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
      (logFilterAddr img ↦₆₄ 0#64) ∗ (((sp + 0x469#64) ↦₈ b469) ∗ F_inv) := by
    have heq :
        (((sp + 0x469#64) ↦₈ b469) ∗
         (pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
           (logFilterAddr img ↦₆₄ 0#64) ∗ F_inv)) =
        (pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
         (logFilterAddr img ↦₆₄ 0#64) ∗ (((sp + 0x469#64) ↦₈ b469) ∗ F_inv)) := by ac_rfl
    rwa [← heq]
  obtain ⟨u850, u858, u860, u9d0, u9d8, u9e0, uab0, uab8, uac0, uac8, uad0, uad8, hmem_wp⟩ :=
    pollWith_588_mem_elim hmem_poll
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29]; dsimp only [sp]; bv_omega
  have hlog := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.logAddrAtEntry_eq_logFilterAddr_trap (C := C) (abs := abs)
    env.loads
  have hwp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.fromSessionStateErr_sepWP_trap (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5)
    (u850 := u850) (u858 := u858) (u860 := u860) (u9d0 := u9d0) (u9d8 := u9d8) (u9e0 := u9e0)
    (uab0 := uab0) (uab8 := uab8) (uac0 := uac0) (uac8 := uac8) (uad0 := uad0) (uad8 := uad8)
    hlog hpc hrun hsp_al hsp hx21 hx25 hx26 hx28 hx29'
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.segExit_of_sepWP_trap hmem_wp hwp ?_
  intro s1 P_f hsteps1 hpc1 hrun1 hmf1
    ⟨hsp1, hsp1_al, htr1, hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
  subst hPf
  have hpc1' : s1.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x54c#64 := by
    rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry_trap (C := C) (abs := abs) env.loads, hpc1]
  have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
    ⟨hm.1, htr1.trans hm.2⟩
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.tailDropRecordCur_ok_trap env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H curScratch (Or.inl rfl) g rec b469 hm1 hst ?_
  refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
    hsteps1.frozenLoaded hfl, hsym1.trans hsym, hvregs1.trans hvregs⟩,
    ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1, hx21_1, hx23_1⟩,
    hstack_le, ?_⟩
  have hmf2 := pollFrom_post_mem_weaken hmf1
  change s1.mem ⊨
    (curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
      memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
      pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.encCommon_eq_logOff_rest A ctl img x (x.draws S answers) s0]
  have heq :
      (pollWith sp 0x9d0 [w3, w4, w5] ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
        (((sp + 0x469#64) ↦₈ b469) ∗ F_inv)) =
      ((curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       ((logFilterAddr img ↦₆₄ 0#64) ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.encCommonRest A img.base x (x.draws S answers) s0) ∗ R) := by
    dsimp only [F_inv]; ac_rfl
  rwa [← heq]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.tailFromSessionStateErr_ok {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x49c#64)
      (fun sp s => s.readReg64 .x21 = sp + 0x580#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
        s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
      (fun sp => curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H)
      R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let R := encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    ⟨hx21, hx25, hx26, hx28⟩, hstack_le, hmem⟩
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads] at hpc
  let sp := s0.sp - 0xbe0#64
  change s.mem ⊨
    (curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R at hmem
  have h1ea : memRegion (sp + 0x280#64) 0x1ea =
      memRegion (sp + 0x280#64) 0x1e9 ∗ memRegion (sp + 0x469#64) 1 := by
    rw [memRegion_split' (b := sp + 0x280#64) (b' := sp + 0x469#64) (N := 0x1ea) (n := 0x1e9) (k := 1)
          (by decide) (by bv_omega) (by decide)]
  rw [h1ea, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.encCommon_eq_logOff_rest A ctl img x (x.draws S answers) s0] at hmem
  let F_inv := curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
    memRegion (sp + 0x280#64) 0x1e9 ∗ H ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.encCommonRest A img.base x (x.draws S answers) s0 ∗ R
  have hmem_469 : s.mem ⊨
      memRegion (sp + 0x469#64) 1 ∗
      (pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗ F_inv) := by
    have heq :
        ((curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
          (memRegion (sp + 0x280#64) 0x1e9 ∗ memRegion (sp + 0x469#64) 1) ∗
          pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         ((logFilterAddr img ↦₆₄ 0#64) ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.encCommonRest A img.base x (x.draws S answers) s0) ∗ R) =
        (memRegion (sp + 0x469#64) 1 ∗
         (pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
           (logFilterAddr img ↦₆₄ 0#64) ∗ F_inv)) := by
      dsimp only [F_inv]; ac_rfl
    rwa [← heq]
  obtain ⟨b469, hmem_b469⟩ := satisfies_memRegion_1 hmem_469
  have hmem_poll : s.mem ⊨
      pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
      (logFilterAddr img ↦₆₄ 0#64) ∗ (((sp + 0x469#64) ↦₈ b469) ∗ F_inv) := by
    have heq :
        (((sp + 0x469#64) ↦₈ b469) ∗
         (pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
           (logFilterAddr img ↦₆₄ 0#64) ∗ F_inv)) =
        (pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
         (logFilterAddr img ↦₆₄ 0#64) ∗ (((sp + 0x469#64) ↦₈ b469) ∗ F_inv)) := by ac_rfl
    rwa [← heq]
  obtain ⟨u850, u858, u860, u9d0, u9d8, u9e0, uab0, uab8, uac0, uac8, uad0, uad8, hmem_wp⟩ :=
    pollWith_588_mem_elim hmem_poll
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29]; dsimp only [sp]; bv_omega
  have hlog := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.logAddrAtEntry_eq_logFilterAddr (C := C) (ctl := ctl) (abs := abs)
    env.loads
  have hwp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.fromSessionStateErr_sepWP (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5)
    (u850 := u850) (u858 := u858) (u860 := u860) (u9d0 := u9d0) (u9d8 := u9d8) (u9e0 := u9e0)
    (uab0 := uab0) (uab8 := uab8) (uac0 := uac0) (uac8 := uac8) (uad0 := uad0) (uad8 := uad8)
    hlog hpc hrun hsp_al hsp hx21 hx25 hx26 hx28 hx29'
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.segExit_of_sepWP hmem_wp hwp ?_
  intro s1 P_f hsteps1 hpc1 hrun1 hmf1
    ⟨hsp1, hsp1_al, htr1, hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
  subst hPf
  have hpc1' : s1.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x54c#64 := by
    rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
  have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
    ⟨hm.1, htr1.trans hm.2⟩
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.tailDropRecordCur_ok env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H curScratch (Or.inl rfl) g rec b469 hm1 hst ?_
  refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
    hsteps1.frozenLoaded hfl, hsym1.trans hsym, hvregs1.trans hvregs⟩,
    ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1, hx21_1, hx23_1⟩,
    hstack_le, ?_⟩
  have hmf2 := pollFrom_post_mem_weaken hmf1
  change s1.mem ⊨
    (curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
      memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
      pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.encCommon_eq_logOff_rest A ctl img x (x.draws S answers) s0]
  have heq :
      (pollWith sp 0x9d0 [w3, w4, w5] ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
        (((sp + 0x469#64) ↦₈ b469) ∗ F_inv)) =
      ((curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       ((logFilterAddr img ↦₆₄ 0#64) ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr.encCommonRest A img.base x (x.draws S answers) s0) ∗ R) := by
    dsimp only [F_inv]; ac_rfl
  rwa [← heq]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr
