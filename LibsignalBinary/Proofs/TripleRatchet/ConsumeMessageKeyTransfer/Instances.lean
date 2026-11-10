/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
public import LibsignalBinary.Proofs.ConsumeMessageKey.Hmac
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Assembly
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndex
import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOne
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer

/-!
# Base-Program Subroutine Contracts on `tripleRatchetProgAt` and `[LibsignalPlacement]`

Transfers `LibsignalSession` subroutine contracts (`consume_message_key`,
`find_receiver_chain_index`, `hmac_sha256`, and `RawVec<Chain>::grow_one`) to
`tripleRatchetProgAt{,Ext}` via `session_subroutine_ok_mono`, proves hook-parametric contracts for
`PublicKey::deserialize`, `ct_eq`, and `PublicKey::eq`, and provides relocatable
`[LibsignalPlacement]` counterparts.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchetRepr

/-! ## Symbol names -/

/-- `RatchetState::consume_message_key` (image offset `0xded8`). -/
abbrev cmkName : String :=
  "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"

/-- `RatchetState::find_receiver_chain_index` (image offset `0xea88`). -/
abbrev findIndexName : String :=
  "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index"

/-- `crypto::hmac_sha256` (image offset `0x20b88`). -/
abbrev hmacName : String := "libsignal_protocol::crypto::hmac_sha256"

/-- `RawVec<Chain>::grow_one` (image offset `0x15cac`), sharing machine code with
`RawVec<MessageKey>::grow_one` (element size `104`, alignment `8`). -/
abbrev growOneChainName : String :=
  "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one"

/-- `PublicKey::deserialize` (image offset `0x3db50`). -/
abbrev deserializeName : String := "<libsignal_core::curve::PublicKey>::deserialize"

/-- `<PublicKey as PartialEq>::eq` (image offset `0x3ebf0`). -/
abbrev publicKeyEqName : String :=
  "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq"

/-- `<[u8] as ConstantTimeEq>::ct_eq` from `libsignal_core` (image offset `0x3ecc4`). -/
abbrev ctEqName : String := "<[u8] as subtle::ConstantTimeEq>::ct_eq"

/-! ## Transferred from the base program -/

theorem cmk_ok_ext {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {F : ShaCompress} {A : RustAlloc}
    {abs ext : String → Option (State → State)} (hA : AllocHooks A abs)
    (hle : ∀ n f, Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns F abs) n = some f →
      Rust.withPanics ext n = some f) :
    subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr cmkName)
      (CryptoVerification.LibsignalSession.consumeMessageKeySpec F A img) := by
  have h := session_subroutine_ok_mono_ext himg hle
    (CryptoVerification.LibsignalSession.consume_message_key_run F A abs img hA himg)
  have e : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr cmkName =
      CryptoVerification.LibsignalSession.cmkEntry img := by
    unfold CryptoVerification.LibsignalSession.cmkEntry
    rw [libsignalSessionCode_ofImage himg, Program.fnAddr_rebase, Program.fnAddr_rebase]
  rw [e]; exact h


theorem findIndex_ok_ext {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {F : ShaCompress} {A : RustAlloc}
    {abs ext : String → Option (State → State)}
    (hle : ∀ n f, Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns F abs) n = some f →
      Rust.withPanics ext n = some f) :
    subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr findIndexName)
      ((CryptoVerification.LibsignalSession.findIndexSpec img A).inImage img) := by
  have h := session_subroutine_ok_mono_ext himg hle
    (CryptoVerification.LibsignalSession.find_receiver_chain_index_ok img F abs A himg)
  have e : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr findIndexName =
      img.base + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index") := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index")]
  rw [e]; exact h

theorem hmac_ok_ext {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {F : ShaCompress} {abs ext : String → Option (State → State)}
    (hle : ∀ n f, Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns F abs) n = some f →
      Rust.withPanics ext n = some f) :
    subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr hmacName)
      ((CryptoVerification.LibsignalSession.hmacSpec F).inImage img) := by
  have h := session_subroutine_ok_mono_ext himg hle
    (CryptoVerification.LibsignalSession.hmac_sha256_ok img F abs himg)
  have e : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr hmacName =
      img.base + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256") := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::crypto::hmac_sha256")]
  rw [e]; exact h

theorem growOneChain_ok_ext {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {F : ShaCompress} {A : RustAlloc}
    {abs ext : String → Option (State → State)} (hA : AllocHooks A abs)
    (hle : ∀ n f, Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns F abs) n = some f →
      Rust.withPanics ext n = some f) :
    subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr growOneChainName)
      ((CryptoVerification.LibsignalSession.growOneSpec A).inImage img) := by
  have h := session_subroutine_ok_mono_ext himg hle
    (CryptoVerification.LibsignalSession.grow_one_ok img F abs himg A hA)
  have e : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr growOneChainName =
      img.base + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one") := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")]
  rw [e]; exact h

theorem cmk_ok_trap {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img) {C : Crypto}
    {A : RustAlloc}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt img.base C abs) ((trTrapProgAt img.base C abs).fnAddr cmkName)
      (CryptoVerification.LibsignalSession.consumeMessageKeySpec C.F A img) :=
  cmk_ok_ext himg hA (sessionExterns_le_trap C abs)

/-- `RatchetState::consume_message_key` meets `consumeMessageKeySpec` on `tripleRatchetProgAt`. -/
theorem cmk_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img) {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) ((tripleRatchetProgAt img.base C ctl abs).fnAddr cmkName)
      (CryptoVerification.LibsignalSession.consumeMessageKeySpec C.F A img) := by
  rw [← (trapsOnly_trTrap_kit img.base C ctl abs).fnAddr cmkName]
  exact subroutine_ok_kit_of_trTrap (cmk_ok_trap himg hA)

theorem findIndex_ok_trap {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img) {C : Crypto}
    {A : RustAlloc}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr findIndexName)
      ((CryptoVerification.LibsignalSession.findIndexSpec img A).inImage img) :=
  findIndex_ok_ext (A := A) himg (sessionExterns_le_trap C abs)

/-- `RatchetState::find_receiver_chain_index` meets `findIndexSpec` on `tripleRatchetProgAt`. -/
theorem findIndex_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img) {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr findIndexName)
      ((CryptoVerification.LibsignalSession.findIndexSpec img A).inImage img) := by
  rw [← (trapsOnly_trTrap_kit img.base C ctl abs).fnAddr findIndexName]
  exact subroutine_ok_kit_of_trTrap (findIndex_ok_trap (A := A) himg)

theorem hmac_ok_trap {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img) {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt img.base C abs) ((trTrapProgAt img.base C abs).fnAddr hmacName)
      ((CryptoVerification.LibsignalSession.hmacSpec C.F).inImage img) :=
  hmac_ok_ext himg (sessionExterns_le_trap C abs)

/-- `crypto::hmac_sha256` meets `hmacSpec` on `tripleRatchetProgAt`. -/
theorem hmac_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img) {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) ((tripleRatchetProgAt img.base C ctl abs).fnAddr hmacName)
      ((CryptoVerification.LibsignalSession.hmacSpec C.F).inImage img) := by
  rw [← (trapsOnly_trTrap_kit img.base C ctl abs).fnAddr hmacName]
  exact subroutine_ok_kit_of_trTrap (hmac_ok_trap himg)

theorem growOneChain_ok_trap {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr growOneChainName)
      ((CryptoVerification.LibsignalSession.growOneSpec A).inImage img) :=
  growOneChain_ok_ext himg hA (sessionExterns_le_trap C abs)

/-- `RawVec<Chain>::grow_one` meets `growOneSpec` on `tripleRatchetProgAt`. -/
theorem growOneChain_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr growOneChainName)
      ((CryptoVerification.LibsignalSession.growOneSpec A).inImage img) := by
  rw [← (trapsOnly_trTrap_kit img.base C ctl abs).fnAddr growOneChainName]
  exact subroutine_ok_kit_of_trTrap (growOneChain_ok_trap himg hA)


/-! ## Proved for any hook map -/


section AnyHooks
open ProofLib.ProgramReflection

theorem tripleRatchetProgAt_blackBox_trap (C : Crypto)
    (abs : String → Option (State → State)) :
    Rust.withPanics (trTrapExterns C abs) "subtle::black_box::<u8>" =
      some CryptoVerification.LibsignalSession.blackBoxHook := by
  rw [withPanics_trTrap_ne C abs (by decide)]
  rfl_kernel

/-- `Rust.withPanics (tripleRatchetExterns C ctl abs)` maps `"subtle::black_box::<u8>"` to
`blackBoxHook`. -/
theorem tripleRatchetProgAt_blackBox (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    Rust.withPanics (tripleRatchetExterns C ctl abs) "subtle::black_box::<u8>" =
      some CryptoVerification.LibsignalSession.blackBoxHook := by
  rfl_kernel

theorem deserialize_ok_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr deserializeName)
      (CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializeSpec b) :=
  CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserialize_ok b _

theorem ctEq_ok_ext (b : BitVec 64) {ext : String → Option (State → State)}
    (h_bb : Rust.withPanics ext "subtle::black_box::<u8>" =
      some CryptoVerification.LibsignalSession.blackBoxHook) :
    subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr ctEqName)
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.ctEqSliceSpec :=
  CryptoVerification.LibsignalSession.FindReceiverChainIndex.ct_eq_ok b h_bb

theorem publicKeyEq_ok_ext (b : BitVec 64) {ext : String → Option (State → State)}
    (h_bb : Rust.withPanics ext "subtle::black_box::<u8>" =
      some CryptoVerification.LibsignalSession.blackBoxHook) :
    subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr publicKeyEqName)
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqSpec :=
  CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKey_eq_ok b h_bb

theorem deserialize_ok_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr deserializeName)
      (CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializeSpec b) :=
  deserialize_ok_ext b (trTrapExterns C abs)

/-- `PublicKey::deserialize` meets `deserializeSpec` on `tripleRatchetProgAt`. -/
theorem deserialize_ok (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr deserializeName)
      (CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializeSpec b) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr deserializeName]
  exact subroutine_ok_kit_of_trTrap (deserialize_ok_trap b C abs)

theorem ctEq_ok_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr ctEqName)
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.ctEqSliceSpec :=
  ctEq_ok_ext b (tripleRatchetProgAt_blackBox_trap C abs)

/-- `<[u8] as subtle::ConstantTimeEq>::ct_eq` meets `ctEqSliceSpec` on `tripleRatchetProgAt`. -/
theorem ctEq_ok (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ctEqName)
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.ctEqSliceSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr ctEqName]
  exact subroutine_ok_kit_of_trTrap (ctEq_ok_trap b C abs)

theorem publicKeyEq_ok_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr publicKeyEqName)
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqSpec :=
  publicKeyEq_ok_ext b (tripleRatchetProgAt_blackBox_trap C abs)

/-- `<PublicKey as PartialEq>::eq` meets `publicKeyEqSpec` on `tripleRatchetProgAt`. -/
theorem publicKeyEq_ok (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr publicKeyEqName)
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr publicKeyEqName]
  exact subroutine_ok_kit_of_trTrap (publicKeyEq_ok_trap b C abs)

/-! ### Stacked 32-bit `black_box` (`CliExt.blackBoxSpec`, `extHookStack = 16384`) -/

/-- `"subtle::black_box::<u8>"` is not a Rust panic symbol, so `HookSat` lifts across `Rust.withPanics`. -/
theorem hookSat_withPanics_blackBox {α : Type} {ext : String → Option (State → State)}
    {spec : Spec α} (h : HookSat ext "subtle::black_box::<u8>" spec) :
    HookSat (Rust.withPanics ext) "subtle::black_box::<u8>" spec := by
  have hp : Rust.isPanicSymbol "subtle::black_box::<u8>" = false := by rfl_kernel
  obtain ⟨f, hf, hok⟩ := h
  exact ⟨f, by simp [Rust.withPanics, hp, hf], hok⟩

theorem ctEq_ok_ext32 (b : BitVec 64) {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>"
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.blackBoxSpec32) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ctEqName)
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.ctEqSliceSpecExt :=
  CryptoVerification.LibsignalSession.FindReceiverChainIndex.ct_eq_ok_ext32 b
    (hookSat_withPanics_blackBox h_bb)

theorem publicKeyEq_frame_ok_ext32 (b : BitVec 64) {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>"
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.blackBoxSpec32) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr publicKeyEqName)
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqSpecExt :=
  CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKey_eq_ok_ext32 b
    (hookSat_withPanics_blackBox h_bb)

theorem publicKeyEq_ok_ext32 (b : BitVec 64) {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>"
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.blackBoxSpec32) :
    CryptoVerification.LibsignalTripleRatchet.Getters.PublicKeyEqOkExt32 b ext :=
  CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKey_eq_stack_ok_ext32 b
    (hookSat_withPanics_blackBox h_bb)

/-- `RatchetState::find_receiver_chain_index` meets `Stage1X.FindIndexOkX` on
`tripleRatchetProgAtExt` under `HookSat ext "subtle::black_box::<u8>" blackBoxSpec32`. -/
theorem findIndex_ok_ext32 {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>"
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.blackBoxSpec32) :
    Proofs.libsignal.Stage1X.FindIndexOkX img A ext := by
  have hcode :=
    CryptoVerification.LibsignalSession.FindReceiverChainIndex.find_receiver_chain_index_code_ok_ext32
      (H := Rust.withPanics ext) img.base A (hookSat_withPanics_blackBox h_bb)
  refine subroutine_ok_outcome_intro fun ⟨p, cs, theirA, their⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, Proofs.libsignal.Stage1X.findIndexSpecX,
    CryptoVerification.LibsignalSession.logFilterAddr, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_, ⟨h1, h2, h3, h4⟩, hm⟩
  refine hcode.mono_outcome (p, cs, theirA, their) R s0 hpc hrun ?_ hsp fun _ hout => hout
  simp only [CryptoVerification.LibsignalSession.FindReceiverChainIndex.findCodeSpecExt,
    sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨h1, h2, h3, h4, hsp, ProofLib.ObjectLoad.base_aligned_of_loads himg⟩, hm⟩

end AnyHooks

/-! ## Relocatable `[LibsignalPlacement]` Contracts -/

section Placed

variable [LibsignalPlacement]

/-- Relocatable `[LibsignalPlacement]` contract for `find_receiver_chain_index` (Block `26`). -/
theorem findIndex_placed_ok {H : String → Option (State → State)} (A : RustAlloc)
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook) :
    subroutine_ok ((blkPC_26).rebase (blkPl_26).base H) (blkPl_26).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.LibsignalSession.FindReceiverChainIndex.findPlacedSpec A)) :=
  CryptoVerification.LibsignalSession.find_receiver_chain_index_placed_ok A h_bb

theorem findIndex_placed_ok_at_block {callerProg : Program} {i : Nat}
    {H : String → Option (State → State)} [IsLsBlockProg callerProg i H] (A : RustAlloc)
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 26)
      (withLsCodeLoaded lsmpl
        (CryptoVerification.LibsignalSession.FindReceiverChainIndex.findPlacedSpec A)) :=
  ls_subroutine_ok_transfer (findIndex_placed_ok A h_bb) hi

/-- Relocatable `[LibsignalPlacement]` contract for `crypto::hmac_sha256` (Block `73`)
with `hmacPlacedSpec F`. -/
theorem hmac_placed_ok (F : ShaCompress)
    {H : String → Option (State → State)}
    (h_mc : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym = some hookMemcpy)
    (h_ms : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym = some hookMemset)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F)) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.LibsignalSession.CryptoHmacSha256.hmacPlacedSpec F)) :=
  CryptoVerification.LibsignalSession.hmac_sha256_placed_ok F h_mc h_ms h_c256

/-- Relocatable `[LibsignalPlacement]` contract for `crypto::hmac_sha256` (Block `73`)
with `hmacSpec F` augmented with `LibsignalRoLoaded lsmpl`. -/
theorem hmac_placed_ro_ok (F : ShaCompress)
    {H : String → Option (State → State)}
    (h_mc : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym = some hookMemcpy)
    (h_ms : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym = some hookMemset)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F)) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl
        { CryptoVerification.LibsignalSession.hmacSpec F with
          pre := fun g s => (CryptoVerification.LibsignalSession.hmacSpec F).pre g s ∗
            ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) :=
  CryptoVerification.LibsignalSession.hmac_sha256_placed_ro_ok F h_mc h_ms h_c256

theorem hmac_placed_ro_ok_at_block {callerProg : Program} {i : Nat}
    (F : ShaCompress) {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (h_mc : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym = some hookMemcpy)
    (h_ms : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym = some hookMemset)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 73)
      (withLsCodeLoaded lsmpl
        { CryptoVerification.LibsignalSession.hmacSpec F with
          pre := fun g s => (CryptoVerification.LibsignalSession.hmacSpec F).pre g s ∗
            ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) :=
  ls_subroutine_ok_transfer (hmac_placed_ro_ok F h_mc h_ms h_c256) hi

/-- Relocatable `[LibsignalPlacement]` contract for `RawVec<Chain>::grow_one` (Block `43`). -/
theorem growOneChain_placed_ok {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_realloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (h_panic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (CryptoVerification.LibsignalSession.growOneSpec A)) :=
  CryptoVerification.LibsignalSession.grow_one_placed_ok h_shim h_alloc h_realloc h_panic

theorem growOneChain_placed_ok_at_block {callerProg : Program} {i : Nat} {A : RustAlloc}
    {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_realloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 43)
      (withLsCodeLoaded lsmpl (CryptoVerification.LibsignalSession.growOneSpec A)) :=
  ls_subroutine_ok_transfer (growOneChain_placed_ok h_shim h_alloc h_realloc h_panic) hi

/-- Relocatable `[LibsignalPlacement]` contract for `PublicKey::deserialize` (Block `201`). -/
theorem deserialize_placed_ok (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H) (blkPl_201).base
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializePlacedSpec :=
  CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserialize_placed_ok H

theorem deserialize_placed_ok_withLsCodeLoaded (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H) (blkPl_201).base
      (withLsCodeLoaded lsmpl
        CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializePlacedSpec) :=
  subroutine_ok_withLsCodeLoaded_of_plain (deserialize_placed_ok H)

/-- Relocatable `[LibsignalPlacement]` contract for `<[u8] as ConstantTimeEq>::ct_eq` (Block `213`). -/
theorem ctEq_placed_ok {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.ctEqSliceSpec :=
  CryptoVerification.LibsignalSession.FindReceiverChainIndex.ct_eq_placed_ok h_bb

theorem ctEq_placed_ok_withLsCodeLoaded {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      (withLsCodeLoaded lsmpl
        CryptoVerification.LibsignalSession.FindReceiverChainIndex.ctEqSliceSpec) :=
  subroutine_ok_withLsCodeLoaded_of_plain (ctEq_placed_ok h_bb)

/-- Relocatable `[LibsignalPlacement]` contract for `<PublicKey as PartialEq>::eq` (Block `212`). -/
theorem publicKeyEq_placed_ok {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl
        CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqSpec) :=
  CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKey_eq_placed_ok h_bb

end Placed

end CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer

