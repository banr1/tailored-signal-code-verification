/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.PublicApiDecryptCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.Defs
import LibsignalBinary.Proofs.Placed.PublicApiCodeSym -- shake: keep

/-!
# `MessageDecrypt` Seam States and Segment Specifications

Intermediate seam PCs, stack/frame invariants, model bridges, and segment specifications for
`session_message_decrypt_signal_with_stores` (`msgDecryptName`, image offset `0x3a4a8`, 2451
instructions) and its relocatable `[LibsignalPlacement]` counterpart on block `197`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt

open Arm64 ProofLib CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit

/-! ## 1. Seam PCs (`+0x…` from `entryOf img msgDecryptName`) -/

/-- `_with_stores` entry `+0x0` (`0x3a4a8`). -/
abbrev wsEntryPC (img : Obj.Image) : BitVec 64 := entryOf img msgDecryptName

/-- LoadPolled `+0x8c` (`0x3a534`): the load poll (`+0x88 blr`) returned; next `ldr x20, [sp, #0x5f0]`. -/
abbrev loadPolledPC (img : Obj.Image) : BitVec 64 := entryOf img msgDecryptName + 0x8c#64

/-- KeyReady `+0x1fcc` (`0x3c474`): `+0x1fc8 tbz` (remote identity key `None`) not taken; next the
key copy to `sp + 0x2a8` and the trust shim call. -/
abbrev keyReadyPC (img : Obj.Image) : BitVec 64 := entryOf img msgDecryptName + 0x1fcc#64

/-- `Ok(true)` of the trust poll, after its drop / dealloc: the save shim call `+0x2150`
(`0x3c5f8`). -/
abbrev saveCallPC (img : Obj.Image) : BitVec 64 := entryOf img msgDecryptName + 0x2150#64

/-- `Ok(false)` of the trust poll (`+0x214c tbz` taken): D7, `+0x21b0` (`0x3c658`). -/
abbrev untrustedPC (img : Obj.Image) : BitVec 64 := entryOf img msgDecryptName + 0x21b0#64

abbrev trustedPC (img : Obj.Image) (t : Bool) : BitVec 64 :=
  if t then saveCallPC img else untrustedPC img

/-- Seam `StoreCall` (`+0x2388`, `0x3c830`): entry to the `store_session` call segment. -/
abbrev storeCallPC (img : Obj.Image) : BitVec 64 := entryOf img msgDecryptName + 0x2388#64

/-- Seam `ErrJoin`: `+0x2294` (`0x3c73c`, plaintext `Vec` owned) or `+0x22a8` (`0x3c750`, no plaintext). -/
abbrev errJoinPC (img : Obj.Image) (pt : Bool) : BitVec 64 :=
  if pt then entryOf img msgDecryptName + 0x2294#64 else entryOf img msgDecryptName + 0x22a8#64

/-- Seam `ResultFinal` (`+0x24d4`, `0x3c97c`): 48-byte result copy to `[x27]`. -/
abbrev resultFinalPC (img : Obj.Image) : BitVec 64 := entryOf img msgDecryptName + 0x24d4#64

/-! ## 2. Frame, Stack, Saved Registers, and Machine Invariants -/

/-- `_with_stores`' frame: `stp x29, x30, [sp, #-0x60]!; sub sp, sp, #0xe80`. -/
abbrev wsFrame : Nat := 0xee0

/-- Stack `withStoresDecSpec` asks for: the public entry's `entryStack` minus the entry's
`0x20`-byte frame. -/
abbrev wsStack : Nat := entryStack - 0x20

/-- Stack left below `_with_stores`' frame for its callees (`rootStack`, the store kit, `alloc`). -/
abbrev wsCalleeStack : Nat := wsStack - wsFrame

/-- Callee stack budget below `_with_stores`'s `0xee0`-byte frame for `kit` and `ikit`. -/
def wsCalleeStackV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) : Nat :=
  max wsCalleeStack
    (max (max (max kit.loadShimStack kit.loadPollStack)
              (max kit.storeShimStack kit.storePollStack))
         (max (max ikit.trustShimStack ikit.trustPollStack)
              (max ikit.saveShimStack ikit.savePollStack)))

/-- Total stack budget at `_with_stores` entry (`s0.sp`) for `kit` and `ikit`. -/
def wsStackV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) : Nat :=
  wsCalleeStackV kit ikit + wsFrame

theorem wsCalleeStack_le_V {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    wsCalleeStack ≤ wsCalleeStackV kit ikit := Nat.le_max_left _ _

theorem loadShimStack_le_V {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    kit.loadShimStack ≤ wsCalleeStackV kit ikit :=
  Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    (Nat.le_max_left _ _)) (Nat.le_max_right _ _)

theorem loadPollStack_le_V {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    kit.loadPollStack ≤ wsCalleeStackV kit ikit :=
  Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
    (Nat.le_max_left _ _)) (Nat.le_max_right _ _)

theorem storeShimStack_le_V {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    kit.storeShimStack ≤ wsCalleeStackV kit ikit :=
  Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
    (Nat.le_max_left _ _)) (Nat.le_max_right _ _)

theorem storePollStack_le_V {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    kit.storePollStack ≤ wsCalleeStackV kit ikit :=
  Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
    (Nat.le_max_left _ _)) (Nat.le_max_right _ _)

theorem trustShimStack_le_V {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    ikit.trustShimStack ≤ wsCalleeStackV kit ikit :=
  Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    (Nat.le_max_right _ _)) (Nat.le_max_right _ _)

theorem trustPollStack_le_V {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    ikit.trustPollStack ≤ wsCalleeStackV kit ikit :=
  Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
    (Nat.le_max_right _ _)) (Nat.le_max_right _ _)

theorem saveShimStack_le_V {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    ikit.saveShimStack ≤ wsCalleeStackV kit ikit :=
  Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
    (Nat.le_max_right _ _)) (Nat.le_max_right _ _)

theorem savePollStack_le_V {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    ikit.savePollStack ≤ wsCalleeStackV kit ikit :=
  Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
    (Nat.le_max_right _ _)) (Nat.le_max_right _ _)

theorem allocHookStack_le_V {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    allocHookStack ≤ wsCalleeStackV kit ikit :=
  Nat.le_trans (by decide : allocHookStack ≤ wsCalleeStack) (wsCalleeStack_le_V kit ikit)

theorem wsStack_le_V {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    wsStack ≤ wsStackV kit ikit :=
  Nat.add_le_add_right (wsCalleeStack_le_V kit ikit) wsFrame

/-- The extra store & stack resources threaded through `R` in the middle seams. -/
def decStoreExtra {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st : kit.StoreState) (ist : ikit.IdState) (s0 : State) : SepProp :=
  ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
    kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
    memRegion (s0.sp - BitVec.ofNat 64 (wsStackV kit ikit)) (wsCalleeStackV kit ikit - wsCalleeStack)

theorem wsStack_split_extra {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st : kit.StoreState) (ist : ikit.IdState) (s0 : State)
    (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
      stackAt s0.sp (wsStackV kit ikit) ⊢
      stackAt s0.sp wsStack ∗ decStoreExtra kit ikit st ist s0 := by
  have hle := wsCalleeStack_le_V kit ikit
  have hlt := s0.sp.isLt
  have hsum : wsStack + (wsCalleeStackV kit ikit - wsCalleeStack) = wsStackV kit ikit := by
    have : wsStack = wsCalleeStack + wsFrame := rfl
    have : wsStackV kit ikit = wsCalleeStackV kit ikit + wsFrame := rfl
    omega
  rw [← hsum, stackAt_split_bottom s0.sp wsStack (wsCalleeStackV kit ikit - wsCalleeStack) (by omega), hsum]
  unfold decStoreExtra
  refine Entails.trans ?_ (sepConj_mono_right (Entails.pure_right hbound (Entails.of_eq rfl)))
  exact Entails.of_eq (by ac_rfl)

theorem wsStack_join_extra {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st : kit.StoreState) (ist : ikit.IdState) (s0 : State) :
    stackAt s0.sp wsStack ∗ decStoreExtra kit ikit st ist s0 ⊢
      kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
        stackAt s0.sp (wsStackV kit ikit) := by
  have hle := wsCalleeStack_le_V kit ikit
  have hlt := s0.sp.isLt
  have hsum : wsStack + (wsCalleeStackV kit ikit - wsCalleeStack) = wsStackV kit ikit := by
    have : wsStack = wsCalleeStack + wsFrame := rfl
    have : wsStackV kit ikit = wsCalleeStackV kit ikit + wsFrame := rfl
    omega
  unfold decStoreExtra
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro hbound
  rw [← hsum, stackAt_split_bottom s0.sp wsStack (wsCalleeStackV kit ikit - wsCalleeStack) (by omega), hsum]
  exact Entails.of_eq (by ac_rfl)

theorem wsCalleeStack_join_extra {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st : kit.StoreState) (ist : ikit.IdState) (s0 : State) :
    stackAt (s0.sp - 0xee0#64) wsCalleeStack ∗ decStoreExtra kit ikit st ist s0 ⊢
      ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
        kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
        stackAt (s0.sp - 0xee0#64) (wsCalleeStackV kit ikit) := by
  have hle := wsCalleeStack_le_V kit ikit
  have hlt := s0.sp.isLt
  have hsum : wsCalleeStack + (wsCalleeStackV kit ikit - wsCalleeStack) = wsCalleeStackV kit ikit := by omega
  unfold decStoreExtra
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro hbound
  have h2 : wsCalleeStackV kit ikit ≤ wsStackV kit ikit := Nat.le_add_right _ _
  have hsub : (s0.sp - 0xee0#64) - BitVec.ofNat 64 (wsCalleeStackV kit ikit) =
      s0.sp - BitVec.ofNat 64 (wsStackV kit ikit) := by
    have : wsStackV kit ikit = wsCalleeStackV kit ikit + 0xee0 := rfl
    bv_omega
  rw [← hsum, stackAt_split_bottom (s0.sp - 0xee0#64) wsCalleeStack
        (wsCalleeStackV kit ikit - wsCalleeStack) (by omega), hsum, hsub]
  exact Entails.pure_right hbound (Entails.of_eq (by ac_rfl))

theorem wsCalleeStack_split_extra {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st : kit.StoreState) (ist : ikit.IdState) (s0 : State)
    (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
      stackAt (s0.sp - 0xee0#64) (wsCalleeStackV kit ikit) ⊢
      stackAt (s0.sp - 0xee0#64) wsCalleeStack ∗ decStoreExtra kit ikit st ist s0 := by
  have hle := wsCalleeStack_le_V kit ikit
  have hlt := s0.sp.isLt
  have h2 : wsCalleeStackV kit ikit ≤ wsStackV kit ikit := Nat.le_add_right _ _
  have hsum : wsCalleeStack + (wsCalleeStackV kit ikit - wsCalleeStack) = wsCalleeStackV kit ikit := by omega
  have hsub : (s0.sp - 0xee0#64) - BitVec.ofNat 64 (wsCalleeStackV kit ikit) =
      s0.sp - BitVec.ofNat 64 (wsStackV kit ikit) := by
    have : wsStackV kit ikit = wsCalleeStackV kit ikit + 0xee0 := rfl
    bv_omega
  rw [← hsum, stackAt_split_bottom (s0.sp - 0xee0#64) wsCalleeStack
        (wsCalleeStackV kit ikit - wsCalleeStack) (by omega), hsum, hsub]
  unfold decStoreExtra
  refine Entails.trans ?_ (sepConj_mono_right (Entails.pure_right hbound (Entails.of_eq rfl)))
  exact Entails.of_eq (by ac_rfl)

theorem stack_wsCalleeV_sub (sp : BitVec 64) {n m : Nat} (hle : m ≤ n) (hn : n ≤ 2 ^ 64) :
    stackAt sp n = memRegion (sp - BitVec.ofNat 64 n) (n - m) ∗ stackAt sp m := by
  have h := stackAt_split_bottom sp m (n - m) (by omega)
  rwa [Nat.add_sub_of_le hle] at h

/-- The 12 callee-saved cells `_with_stores`' prologue writes at `sp0 - 0x60 .. sp0`. -/
def wsSavedRegs (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp0 - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

/-- Machine facts at every seam after the prologue. -/
def wsMeta (img : Obj.Image) (x : DecryptGhost) (s0 s : State) : Prop :=
  s.status = .Running ∧ s.sp = s0.sp - 0xee0#64 ∧ s0.spAligned = true ∧ s.spAligned = true ∧
    s.readReg64 .x29 = s0.sp - 96#64 ∧ s.readReg64 .x27 = x.ret ∧
    img.FrozenLoaded s ∧ s.symtab = img.symtab ∧ calleeSavedVRegs s = calleeSavedVRegs s0

/-! ## 3. Vtables and Frame Zones -/

/-- Load vtable cells (`ss_vt + 0x18` and load future vtable `[drop, size, align, poll]`). -/
def decLoadVtableAtV {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) : SepProp :=
  ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (b + kit.loadShimOff)) ∗
  ((b + kit.loadFutVtOff) ↦₆₄ᵣ (b + kit.loadFutDropOff)) ∗
  ((b + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
  ((b + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((b + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (b + kit.loadPollOff))

/-- Store vtable cells (`ss_vt + 0x20` and store future vtable `[drop, size, align, poll]`). -/
def decStoreVtableAtV {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) : SepProp :=
  ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (b + kit.storeShimOff)) ∗
  ((b + kit.storeFutVtOff) ↦₆₄ᵣ (b + kit.storeFutDropOff)) ∗
  ((b + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
  ((b + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((b + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (b + kit.storePollOff))

/-- Save vtable cells (`id_vt + 0x28` and save future vtable `[drop, size, align, poll]`). -/
def decSaveVtableAtV {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b) : SepProp :=
  ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (b + ikit.saveShimOff)) ∗
  ((b + ikit.saveFutVtOff) ↦₆₄ᵣ (b + ikit.saveFutDropOff)) ∗
  ((b + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
  ((b + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((b + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (b + ikit.savePollOff))

/-- Trust vtable cells (`id_vt + 0x30` and trust future vtable `[drop, size, align, poll]`). -/
def decTrustVtableAtV {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b) : SepProp :=
  ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (b + ikit.trustShimOff)) ∗
  ((b + ikit.trustFutVtOff) ↦₆₄ᵣ (b + ikit.trustFutDropOff)) ∗
  ((b + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
  ((b + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((b + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (b + ikit.trustPollOff))

/-- All 20 read-only vtable cells for `kit : SessionStoreSpec A b` and `ikit : IdentityStoreSpec A b`. -/
def decVtablesAtV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) : SepProp :=
  decLoadVtableAtV kit ∗ decStoreVtableAtV kit ∗ decSaveVtableAtV ikit ∗ decTrustVtableAtV ikit

/-- Read-only vtable cells used by the `E₀` hook-store specialization. -/
def decVtablesAt (b : BitVec 64) : SepProp :=
  ((b + bv% (ls_xref% (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 136) (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 140))) ↦₆₄ᵣ (b + bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 16712))) ∗ ((b + bv% (ls_xref% (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 136) (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 140) + 8)) ↦₆₄ᵣ (b + bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 16792))) ∗
  ((b + bv% (ls_xref% (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 172) (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 176) + 24)) ↦₆₄ᵣ (b + bv% (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" + 88))) ∗ ((b + bv% (ls_xref% (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 204) (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 208))) ↦₆₄ᵣ (b + bv% (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" + 184))) ∗
  ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 16)) ↦₆₄ᵣ (b + bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 15744))) ∗ ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 8)) ↦₆₄ᵣ 24#64) ∗
  ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}"))) ↦₆₄ᵣ 8#64) ∗ ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") + 8)) ↦₆₄ᵣ (b + bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 15748))) ∗
  ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") - 16)) ↦₆₄ᵣ (b + bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 15744))) ∗ ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") - 8)) ↦₆₄ᵣ 32#64) ∗
  ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"))) ↦₆₄ᵣ 8#64) ∗ ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") + 8)) ↦₆₄ᵣ (b + bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 15988))) ∗
  ((b + bv% (ls_xref% (ls_off% "<libsignal_protocol::protocol::PlaintextContent as core::convert::From<libsignal_protocol::protocol::DecryptionErrorMessage>>::from" + 600) (ls_off% "<libsignal_protocol::protocol::PlaintextContent as core::convert::From<libsignal_protocol::protocol::DecryptionErrorMessage>>::from" + 604) + 8)) ↦₆₄ᵣ (b + bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 15744))) ∗ ((b + bv% (ls_xref% (ls_off% "<libsignal_protocol::protocol::PlaintextContent as core::convert::From<libsignal_protocol::protocol::DecryptionErrorMessage>>::from" + 600) (ls_off% "<libsignal_protocol::protocol::PlaintextContent as core::convert::From<libsignal_protocol::protocol::DecryptionErrorMessage>>::from" + 604) + 16)) ↦₆₄ᵣ 32#64) ∗
  ((b + bv% (ls_xref% (ls_off% "<libsignal_protocol::proto::fingerprint::CombinedFingerprints as core::fmt::Debug>::fmt" + 60) (ls_off% "<libsignal_protocol::proto::fingerprint::CombinedFingerprints as core::fmt::Debug>::fmt" + 64))) ↦₆₄ᵣ 8#64) ∗ ((b + bv% (ls_xref% (ls_off% "<libsignal_protocol::proto::fingerprint::CombinedFingerprints as core::fmt::Debug>::fmt" + 60) (ls_off% "<libsignal_protocol::proto::fingerprint::CombinedFingerprints as core::fmt::Debug>::fmt" + 64) + 8)) ↦₆₄ᵣ (b + bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 16192))) ∗
  ((b + bv% (ls_xref% (ls_off% "<libsignal_protocol::proto::fingerprint::CombinedFingerprints as core::fmt::Debug>::fmt" + 60) (ls_off% "<libsignal_protocol::proto::fingerprint::CombinedFingerprints as core::fmt::Debug>::fmt" + 64) + 16)) ↦₆₄ᵣ (b + bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 15744))) ∗ ((b + bv% (ls_xref% (ls_off% "<libsignal_protocol::proto::fingerprint::CombinedFingerprints as core::fmt::Debug>::fmt" + 60) (ls_off% "<libsignal_protocol::proto::fingerprint::CombinedFingerprints as core::fmt::Debug>::fmt" + 64) + 24)) ↦₆₄ᵣ 32#64) ∗
  ((b + bv% (ls_xref% (ls_off% "<libsignal_protocol::proto::fingerprint::CombinedFingerprints as core::fmt::Debug>::fmt" + 60) (ls_off% "<libsignal_protocol::proto::fingerprint::CombinedFingerprints as core::fmt::Debug>::fmt" + 64) + 32)) ↦₆₄ᵣ 8#64) ∗ ((b + bv% (ls_xref% (ls_off% "<libsignal_protocol::proto::fingerprint::CombinedFingerprints as core::fmt::Debug>::fmt" + 60) (ls_off% "<libsignal_protocol::proto::fingerprint::CombinedFingerprints as core::fmt::Debug>::fmt" + 64) + 40)) ↦₆₄ᵣ (b + bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 16328)))

theorem decVtablesAt_eq_decVtablesAtV (A : RustAlloc) (b : BitVec 64) :
    decVtablesAt b = decVtablesAtV (hookSessionStoreSpec A b) (hookIdentityStoreSpec A b) := by
  unfold decVtablesAt decVtablesAtV decLoadVtableAtV decStoreVtableAtV
    decSaveVtableAtV decTrustVtableAtV hookSessionStoreSpec hookIdentityStoreSpec
    hookIdentityStoreSpecAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

/-- Fixed stack argument cells parameterized by `kit` and `ikit`. -/
def wsArgCellsV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) : SepProp :=
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
  ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗ ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
  ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗ ((sp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64))

/-- Fixed stack argument cells (`E₀` specialization). -/
def wsArgCells (img : Obj.Image) (x : DecryptGhost) (s0 : State) (sp : BitVec 64) : SepProp :=
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
  ((sp + 0x100#64) ↦₆₄ (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 100) (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 104) + 8))) ∗ ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
  ((sp + 0x110#64) ↦₆₄ (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 136) (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 140) + 16))) ∗ ((sp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64))

/-- The two argument cells the region reads (`recordDecryptSpec.pre`): `[sp+0xe0] = msgA`,
`[sp+0xf0] = locA` (`+0x48`, `+0x5c`). -/
def wsMsgCells (x : DecryptGhost) (sp : BitVec 64) : SepProp :=
  ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA)

/-- Post-prologue frame invariant parameterized by `kit` and `ikit`. -/
def wsFixedV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) : SepProp :=
  wsSavedRegs s0.sp s0 ∗ wsArgCellsV kit ikit x s0 sp ∗ decVtablesAtV kit ikit ∗
  memRegion (sp + 0xa0#64) 0x40 ∗
  memRegion (sp + 0x2c8#64) 8 ∗ memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80

/-- Post-prologue frame invariant (`E₀` specialization). -/
def wsFixed (img : Obj.Image) (x : DecryptGhost) (s0 : State) (sp : BitVec 64) : SepProp :=
  wsSavedRegs s0.sp s0 ∗ wsArgCells img x s0 sp ∗ decVtablesAt img.base ∗
  memRegion (sp + 0xa0#64) 0x40 ∗
  memRegion (sp + 0x2c8#64) 8 ∗ memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80

/-- The borrowed inputs and environment every seam keeps (as `decryptSignalSpec`), with the
callees' stack below the frame and the 48-byte sret until T-write. -/
def wsEnv (A : RustAlloc) (img : Obj.Image) (x : DecryptGhost) (sp : BitVec 64) : SepProp :=
  signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ logOff img ∗ stackAt sp wsCalleeStack ∗ A.pool

/-! ## 4. Session-API Model Helpers and Record Bridges -/

/-- Model decrypt step `try_decrypt_from_record` on a loaded `SessionRecord`. -/
def decryptRecord (C : Crypto) (S : SpqrModel) (parse : UuidParser) (x : DecryptGhost)
    (r : SessionRecord (List (BitVec 8))) :
    Except SignalProtocolError (List (BitVec 8) × SessionRecord (List (BitVec 8))) :=
  CryptoGames.LibsignalSessionApi.SessionRecord.tryDecryptFromRecord C S.spqr
    (serializeAddrVals (serviceIdParse parse) x.rem.val x.loc.val) x.msg (coinsOf x.rest) r

/-- The region's ghost for a loaded current session `(G, st)` (previous-sessions pointer `prevPtr`). -/
def recGhostOf (x : DecryptGhost) (prevPtr : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : RecordDecryptGhost :=
  { sret := x.ret, prevPtr := prevPtr, G := G, st := st, remA := x.remA, rem := x.rem,
    locA := x.locA, loc := x.loc, msgA := x.msgA, msgG := x.msgG, msg := x.msg,
    cur := x.cur, rest := x.rest }

/-- Pure model relation of `sessionStateReprAt`: `sessionStateReprAt A ss G s =
⌜sessionModelRel G s⌝ ∗ sessionStateAt A ss G s.state` (`sessionAt_eq`). -/
def sessionModelRel (G : SessionGhost) (s : Session (List (BitVec 8))) : Prop :=
  PendingRel G.pending s.pendingPreKey ∧ KyberRel G.kyber s.pendingKyberPreKey ∧
    G.alice.bytes = s.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat ∧
    (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat

theorem sessionAt_eq (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8))) :
    sessionStateReprAt A ss G s = (⌜sessionModelRel G s⌝ ∗ sessionStateAt A ss G s.state) := rfl

/-- Empty `previous_sessions` backing buffer of a `SessionRecord`. -/
def prevBufAt (A : RustAlloc) (cap ptr : BitVec 64) : SepProp :=
  vecBuf A 24 8 (fun (_ : Unit) _ => emp) cap ptr []

/-- The record cells at `sp + 0x120` the error teardown TJ (`+0x2294..+0x230c`) drops: the
`previous_sessions` header and buffer, and the current session as a triple-ratchet SS (`some`) or the
`None` niche with 336 free bytes. -/
def droppableRecordAt (A : RustAlloc) (r : BitVec 64) :
    Option (SessionGhost × SessionState (List (BitVec 8))) → SepProp
  | none =>
    (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, vecAt A 24 8 (fun (_ : Unit) _ => emp) r cap ptr []) ∗
      ((r + 0x18#64) ↦₆₄ noneCap) ∗ memRegion (r + 0x20#64) 336
  | some (G, st) =>
    (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, vecAt A 24 8 (fun (_ : Unit) _ => emp) r cap ptr []) ∗
      sessionStateAt A (r + 0x18#64) G st

/-- Record-split bridge statement: a loaded record with current session `s` splits into the
region's header cells (`prevPtr` at `+8`, `len = 0` at `+0x10`, `sessionStateAt` at `+0x18`), the
capacity cell and buffer, and `sessionModelRel G s`. -/
def RecordSplit : Prop :=
  ∀ (A : RustAlloc) (r : BitVec 64) (g : RecordGhost) (rec : SessionRecord (List (BitVec 8)))
    (s : Session (List (BitVec 8))) (G : SessionGhost),
    rec.currentSession = some s → g.cur = some G →
    sessionRecordAt A r g rec ⊢
      (⌜sessionModelRel G s⌝ ∗ (r ↦₆₄ g.prevCap) ∗ prevBufAt A g.prevCap g.prevPtr ∗
        ((r + 8#64) ↦₆₄ g.prevPtr) ∗ ((r + 16#64) ↦₆₄ 0#64) ∗
        sessionStateAt A (r + 0x18#64) G s.state)

/-- Record-join bridge statement: after `AfterRecordDecrypt G G'`, the record with updated
session state `st'` and cleared pending pre-keys reassembles into `sessionRecordAt`. -/
def RecordJoin : Prop :=
  ∀ (A : RustAlloc) (r : BitVec 64) (cap ptr : BitVec 64) (G G' : SessionGhost)
    (s : Session (List (BitVec 8))) (st' : SessionState (List (BitVec 8))),
    sessionModelRel G s → G.AfterRecordDecrypt G' →
    ((r ↦₆₄ cap) ∗ prevBufAt A cap ptr ∗ ((r + 8#64) ↦₆₄ ptr) ∗ ((r + 16#64) ↦₆₄ 0#64) ∗
        sessionStateAt A (r + 0x18#64) G' st') ⊢
      ∃∗ g : RecordGhost, sessionRecordAt A r g
        { currentSession := some { s with state := st', pendingPreKey := none,
                                          pendingKyberPreKey := none } }

/-! ## 5. Staged Result Layout -/

/-- Word `+8` of the result as T-write builds it. -/
def resWord1 (w20 w21 : BitVec 64) : BitVec 32 :=
  (w20.extractLsb' 0 24) ++ (w21.extractLsb' 0 8)

/-- Separation-logic layout of a 48-byte `ApiResult` staged for the final `sret` copy. -/
def StagedRes (A : RustAlloc) (x28 w20 w21 src : BitVec 64)
    (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) : SepProp :=
  ∃∗ bs : List (BitVec 8), ∃∗ F : SepProp,
    ⌜bs.length = 36 ∧ ∀ r : BitVec 64,
      ((r ↦₆₄ x28) ∗ ((r + 8#64) ↦₃₂ resWord1 w20 w21) ∗ ((r + 12#64) ↦ₛ bs) ∗ F) ⊢
        apiDecResultAt A r res⌝ ∗
    (src ↦ₛ bs) ∗ F

/-! ## 6. Seam States -/

/-- Seam `LoadPolled` (`+0x8c`): `load_session` shim and poll have returned. -/
def LoadPolledStateV {A : RustAlloc} (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = loadPolledPC img ∧ wsMeta img x s0 s ∧ wsStack ≤ s0.sp.toNat ∧
  s.readReg64 .x19 = sp + 0x5f0#64 ∧
  kit.loadRel st0 x.rem.val ans.loadSession ∧
  s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
  (s.mem ⊨ wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
    (∃∗ box : BitVec 64, ⌜box ≠ 0#64⌝ ∗ ((sp + 0x2d0#64) ↦₆₄ box) ∗
      ((sp + 0x2d8#64) ↦₆₄ (img.base + kit.loadFutVtOff)) ∗
      A.live box kit.loadBoxSize 8 ∗
      kit.loadBoxAt box (s0.readReg64 .x3) x.remA 1#8) ∗
    loadPollOutAtS Scope A img.base (sp + 0x5f0#64) ans.loadSession ∗
    memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗
    memRegion (sp + 0x300#64) 0x1b0 ∗ memRegion (sp + 0x4b0#64) 0x140 ∗
    memRegion (sp + 0x760#64) 0x6a0 ∗ memRegion x.ret 48 ∗ tapeAt ctl x.cur x.rest ∗
    decStoreExtra kit ikit st0 ist0 s0 ∗ R)

abbrev LoadPolledState (A : RustAlloc) (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State) : Prop :=
  LoadPolledStateV ctl encRecord img (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope x ans R s0 s

/-- The public-API frame around the region (`R` of `recordDecryptSpec`), parameterized by `kit` and `ikit`. -/
def wsRegionFrameV {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (s0 : State) (prevCap prevPtr : BitVec 64) : SepProp :=
  let sp := s0.sp - 0xee0#64
  wsSavedRegs s0.sp s0 ∗ wsArgCellsV kit ikit x s0 sp ∗ decVtablesAtV kit ikit ∗
    memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
    memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
    ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
    memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
    memRegion (sp + 0x300#64) 0x1b0 ∗
    memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
    memRegion x.ret 48

abbrev wsRegionFrame (A : RustAlloc) (img : Obj.Image) (x : DecryptGhost) (s0 : State)
    (prevCap prevPtr : BitVec 64) : SepProp :=
  wsRegionFrameV img (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) x s0 prevCap prevPtr

/-- Seam `RegionSome` (`recordRegionEntry img`, `+0x1a8`): record loaded with a `Some` current session. -/
def RegionSomeStateV (C : Crypto) {A : RustAlloc} (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State) : Prop :=
  s.pc = recordRegionEntry img ∧ wsMeta img x s0 s ∧
  ∃ (rec : SessionRecord (List (BitVec 8))) (ses : Session (List (BitVec 8))) (G : SessionGhost)
    (prevCap prevPtr : BitVec 64),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    rec.currentSession = some ses ∧ sessionModelRel G ses ∧
    s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    (s.mem ⊨ (recordDecryptSpec C A ctl parse S img).pre (recGhostOf x prevPtr G ses.state) s ∗
      wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗ decStoreExtra kit ikit st0 ist0 s0 ∗ R)

abbrev RegionSomeState (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State) : Prop :=
  RegionSomeStateV C ctl parse S encRecord img (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope x ans R s0 s

/-- The RN pre (see `recordDecryptSpec`): `recordDecryptSpec.pre` with the current session `None`
(`[sp+0x138] = noneCap`, 336 free bytes; the `none, none` arm of `sessionRecordAt`). -/
def regionNonePre (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image) (x : DecryptGhost)
    (prevPtr : BitVec 64) (s : State) : SepProp :=
  ⌜img.FrozenLoaded s ∧ s.symtab = img.symtab ∧ s.spAligned = true ∧ s.readReg64 .x27 = x.ret ∧
    s.readReg64 .x19 = x.remA ∧ s.readReg64 .x23 = s.sp + 0x5f0#64 ∧
    s.readReg64 .x24 = s.sp + 0xca0#64 ∧ rootStack ≤ s.sp.toNat⌝ ∗
  memRegion s.sp 0xa0 ∗ ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
  ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
  ((s.sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (s.sp + 0x140#64) 336 ∗
  memRegion (s.sp + 0x4b0#64) 0x950 ∗
  protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗ logOff img ∗
  stackAt s.sp rootStack ∗ A.pool

/-- Seam `RegionNone` (`+0x1a8`): `load_session` returned `Ok(Some r)` with `r.currentSession = none`. -/
def RegionNoneStateV {A : RustAlloc} (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  s.pc = recordRegionEntry img ∧ wsMeta img x s0 s ∧
  ∃ (rec : SessionRecord (List (BitVec 8))) (prevCap prevPtr : BitVec 64),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    rec.currentSession = none ∧
    s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    (s.mem ⊨ regionNonePre A ctl img x prevPtr s ∗
      wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗ decStoreExtra kit ikit st0 ist0 s0 ∗ R)

abbrev RegionNoneState (A : RustAlloc) (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  RegionNoneStateV ctl encRecord img (hookSessionStoreSpec A img.base)
    (hookIdentityStoreSpec A img.base) () () RecordInScope x ans R s0 s

/-- Seam `PostSome` (`recordRegionExit img`, `+0x1f50`): `try_decrypt_from_record` exited on a `Some` current session. -/
def PostSomeStateV (C : Crypto) {A : RustAlloc} (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  s.pc = recordRegionExit img ∧ wsMeta img x s0 s ∧
  ∃ (s1 : State) (rec : SessionRecord (List (BitVec 8))) (ses : Session (List (BitVec 8)))
    (G : SessionGhost) (prevCap prevPtr : BitVec 64),
    s1.sp = s0.sp - 0xee0#64 ∧
    s1.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    rec.currentSession = some ses ∧ sessionModelRel G ses ∧
    (s.mem ⊨ (recordDecryptSpec C A ctl parse S img).post (recGhostOf x prevPtr G ses.state) s1 s ∗
      wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗ decStoreExtra kit ikit st0 ist0 s0 ∗ R)

abbrev PostSomeState (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  PostSomeStateV C ctl parse S encRecord img (hookSessionStoreSpec A img.base)
    (hookIdentityStoreSpec A img.base) () () RecordInScope x ans R s0 s

/-- Seam `PostNone` (`+0x1f50`): `try_decrypt_from_record` exited on `r.currentSession = none`. -/
def PostNoneStateV {A : RustAlloc} (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = recordRegionExit img ∧ wsMeta img x s0 s ∧
  s.readReg64 .x26 = sp + 0xa0#64 ∧
  s.readReg64 .x28 = recordResultTag (.error (.invalidMessage .whisper .decryptionFailed)) ∧
  ∃ (rec : SessionRecord (List (BitVec 8))) (prevCap prevPtr : BitVec 64),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    rec.currentSession = none ∧
    s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    (s.mem ⊨ memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
      ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
      ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336 ∗
      recordResultAt A (sp + 0x4b0#64) (.error (.invalidMessage .whisper .decryptionFailed)) ∗
      memRegion (sp + 0x4e0#64) 0x920 ∗
      protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗ logOff img ∗
      stackAt sp rootStack ∗ A.pool ∗
      wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗ decStoreExtra kit ikit st0 ist0 s0 ∗ R)

abbrev PostNoneState (A : RustAlloc) (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  PostNoneStateV ctl encRecord img (hookSessionStoreSpec A img.base)
    (hookIdentityStoreSpec A img.base) () () RecordInScope x ans R s0 s

/-- Seam `KeyReady` (`+0x1fcc`): remote identity key extracted as `Some`. -/
def KeyReadyStateV (C : Crypto) {A : RustAlloc} (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = keyReadyPC img ∧ wsMeta img x s0 s ∧ s.readReg64 .x26 = sp + 0xa0#64 ∧
  s.readReg64 .x22 = sp + 0x294#64 ∧
  ∃ (rec rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) (ses : Session (List (BitVec 8)))
    (k : IdentityKey),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    decryptRecord C S parse x rec = .ok (pt, rec') ∧ rec'.currentSession = some ses ∧
    ses.state.remoteIdentity = some k ∧
    s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    (s.mem ⊨ wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0xca0#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x9a0 ∗ memRegion (sp + 0xcc0#64) 0x140 ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st0 ist0 s0 ∗ R)

abbrev KeyReadyState (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  KeyReadyStateV C ctl parse S encRecord img (hookSessionStoreSpec A img.base)
    (hookIdentityStoreSpec A img.base) () () RecordInScope x ans R s0 s

/-- Seam `Trusted t` (`trustedPC img t`): `is_trusted_identity` poll completed with boolean `t`. -/
def TrustedStateV (C : Crypto) {A : RustAlloc} (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (t : Bool)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = trustedPC img t ∧ wsMeta img x s0 s ∧ s.readReg64 .x26 = sp + 0xa0#64 ∧
  s.readReg64 .x19 = sp + 0x2a8#64 ∧ s.readReg64 .x22 = sp + 0x294#64 ∧
  ∃ (rec rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) (ses : Session (List (BitVec 8)))
    (k : IdentityKey),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    decryptRecord C S parse x rec = .ok (pt, rec') ∧ rec'.currentSession = some ses ∧
    ses.state.remoteIdentity = some k ∧ ans.isTrustedIdentity = .ok t ∧
    ikit.trustRel ist0 x.rem.val k .receiving ans.isTrustedIdentity ∧
    s.trace = s0.trace ++ (kit.loadEvs encRecord x.rem.val ans.loadSession ++
      ikit.trustEvs x.rem.val k .receiving ans.isTrustedIdentity) ∧
    (s.mem ⊨ wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st0 (ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity) s0 ∗ R)

abbrev TrustedState (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (t : Bool)
    (R : SepProp) (s0 s : State) : Prop :=
  TrustedStateV C ctl parse S encRecord img (hookSessionStoreSpec A img.base)
    (hookIdentityStoreSpec A img.base) () () RecordInScope x ans t R s0 s

/-- Seam `StoreCall` (`+0x2388`): `save_identity` succeeded; ready for `store_session`. -/
def StoreCallStateV (C : Crypto) {A : RustAlloc} (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = storeCallPC img ∧ wsMeta img x s0 s ∧ s.readReg64 .x26 = sp + 0xa0#64 ∧
  s.readReg64 .x22 = sp + 0x294#64 ∧
  ∃ (rec rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) (ses : Session (List (BitVec 8)))
    (k : IdentityKey) (c : IdentityChange),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    decryptRecord C S parse x rec = .ok (pt, rec') ∧ rec'.currentSession = some ses ∧
    ses.state.remoteIdentity = some k ∧ ans.isTrustedIdentity = .ok true ∧
    ans.saveIdentity = .ok c ∧
    ikit.trustRel ist0 x.rem.val k .receiving ans.isTrustedIdentity ∧
    ikit.saveRel (ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity)
      x.rem.val k ans.saveIdentity ∧
    s.trace = s0.trace ++ (kit.loadEvs encRecord x.rem.val ans.loadSession ++
      ikit.trustEvs x.rem.val k .receiving ans.isTrustedIdentity ++
      ikit.saveEvs x.rem.val k ans.saveIdentity) ∧
    (s.mem ⊨ wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ memRegion (sp + 0x2a8#64) 0x20 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st0
        (ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity)
          x.rem.val k ans.saveIdentity) s0 ∗ R)

abbrev StoreCallState (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  StoreCallStateV C ctl parse S encRecord img (hookSessionStoreSpec A img.base)
    (hookIdentityStoreSpec A img.base) () () RecordInScope x ans R s0 s

/-- Seam `ErrJoin pt` (`errJoinPC img pt`): non-panic error path entering record teardown. -/
def ErrJoinStateV (C : Crypto) {A : RustAlloc} (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (pt : Bool) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = errJoinPC img pt ∧ wsMeta img x s0 s ∧ s.readReg64 .x26 = sp + 0xa0#64 ∧
  s.readReg64 .x28 ≠ pendingTag ∧
  ∃ (ans : StoreAnswers (List (BitVec 8)) Unit) (cs : Option (SessionGhost × SessionState (List (BitVec 8)))),
    (x.model C S parse ans).1 ≠ .error .panic ∧
    (∀ p, (x.model C S parse ans).1 ≠ .ok p) ∧
    (∀ r, ans.loadSession = .ok (some r) → kit.ScopeAt Scope st0 x.rem.val r) ∧
    kit.callsRel st0 ans (x.model C S parse ans).2 ∧
    ikit.idCallsRel ist0 ans (x.model C S parse ans).2 ∧
    s.trace = s0.trace ++ ikit.traceOfWith kit encRecord ans (x.model C S parse ans).2 ∧
    (s.mem ⊨ wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) cs ∗
      (if pt then ∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p
       else memRegion (sp + 0x290#64) 24) ∗
      StagedRes A (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (sp + 0x580#64)
        (x.model C S parse ans).1 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit
        (kit.storeFinal st0 ans (x.model C S parse ans).2)
        (ikit.idFinal ist0 ans (x.model C S parse ans).2) s0 ∗ R)

abbrev ErrJoinState (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (x : DecryptGhost) (pt : Bool) (R : SepProp) (s0 s : State) : Prop :=
  ErrJoinStateV C ctl parse S encRecord img (hookSessionStoreSpec A img.base)
    (hookIdentityStoreSpec A img.base) () () RecordInScope x pt R s0 s

/-- Seam `ResultFinal` (`+0x24d4`): result staged at `sp + 0x300` before final `sret` copy. -/
def ResultFinalStateV (C : Crypto) {A : RustAlloc} (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = resultFinalPC img ∧ wsMeta img x s0 s ∧
  ∃ ans : StoreAnswers (List (BitVec 8)) Unit,
    (x.model C S parse ans).1 ≠ .error .panic ∧
    (∀ r, ans.loadSession = .ok (some r) → kit.ScopeAt Scope st0 x.rem.val r) ∧
    kit.callsRel st0 ans (x.model C S parse ans).2 ∧
    ikit.idCallsRel ist0 ans (x.model C S parse ans).2 ∧
    s.trace = s0.trace ++ ikit.traceOfWith kit encRecord ans (x.model C S parse ans).2 ∧
    (s.mem ⊨ wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      StagedRes A (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (sp + 0x300#64)
        (x.model C S parse ans).1 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x324#64) 0xadc ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit
        (kit.storeFinal st0 ans (x.model C S parse ans).2)
        (ikit.idFinal ist0 ans (x.model C S parse ans).2) s0 ∗ R)

abbrev ResultFinalState (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (x : DecryptGhost) (R : SepProp) (s0 s : State) : Prop :=
  ResultFinalStateV C ctl parse S encRecord img (hookSessionStoreSpec A img.base)
    (hookIdentityStoreSpec A img.base) () () RecordInScope x R s0 s

/-! ## 7. `_with_stores` Specifications -/

/-- Specification of `session_message_decrypt_signal_with_stores` parameterized by `kit`, `ikit`,
initial store states `st0` / `ist0`, and `Scope`. -/
def withStoresDecSpecV (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec DecryptGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.remA ∧ s.readReg64 .x2 = x.locA ∧
          s.readReg64 .x4 = kit.ss_vt ∧ s.readReg64 .x6 = ikit.id_vt ∧
          s.readReg64 .x8 = x.ret ∧ wsStackV kit ikit ≤ s.sp.toNat ∧
          kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
        kit.storeAt (s.readReg64 .x3) st0 ∗
        ikit.identityAt (s.readReg64 .x5) ist0 ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 48 ∗ tapeAt ctl x.cur x.rest ∗
        logOff img ∗ decVtablesAtV kit ikit ∗ stackAt s.sp (wsStackV kit ikit) ∗ A.pool
      post := fun x s0 sf =>
        ∃∗ answers : StoreAnswers (List (BitVec 8)) Unit,
          ⌜(x.model C S parse answers).1 ≠ .error .panic ∧
            (∀ r, answers.loadSession = .ok (some r) → kit.ScopeAt Scope st0 x.rem.val r) ∧
            kit.callsRel st0 answers (x.model C S parse answers).2 ∧
            ikit.idCallsRel ist0 answers (x.model C S parse answers).2 ∧
            sf.trace = s0.trace ++ ikit.traceOfWith kit encRecord answers (x.model C S parse answers).2⌝ ∗
          kit.storeAt (s0.readReg64 .x3)
            (kit.storeFinal st0 answers (x.model C S parse answers).2) ∗
          ikit.identityAt (s0.readReg64 .x5)
            (ikit.idFinal ist0 answers (x.model C S parse answers).2) ∗
          apiDecResultAt A x.ret (x.model C S parse answers).1 ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws C answers) ∗
          logOff img ∗ decVtablesAtV kit ikit ∗ stackAt s0.sp (wsStackV kit ikit) ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜s0.trace <+: sf.trace ∧
           (allocFailedIn s0 sf ∨
            ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
              kit.loadRel st0 x.rem.val answers.loadSession ∧
              s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
              ((x.model C S parse answers).1 = .error .panic ∨ x.recvPanics S answers))⌝ ∗
        anyHeap }
    img

/-- Extract `kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val` from `(withStoresDecSpecV ...).pre x s0 ∗ R`. -/
theorem withStoresDecSpecV_pre_addrOk {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {img : Obj.Image} {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).pre x s0 ∗ R) :
    kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val := by
  dsimp only [withStoresDecSpecV, Spec.inImage] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.2.1.2.2.2.2.2.2.2

/-- `E₀` hook-store specialization of `withStoresDecSpecV`. -/
def withStoresDecSpec (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) : Spec DecryptGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.remA ∧ s.readReg64 .x2 = x.locA ∧
          s.readReg64 .x4 = img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 100) (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 104) + 8) ∧ s.readReg64 .x6 = img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 136) (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 140) + 16) ∧
          s.readReg64 .x8 = x.ret ∧ wsStack ≤ s.sp.toNat⌝ ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 48 ∗ tapeAt ctl x.cur x.rest ∗
        logOff img ∗ decVtablesAt img.base ∗ stackAt s.sp wsStack ∗ A.pool
      post := fun x s0 sf =>
        ∃∗ answers : StoreAnswers (List (BitVec 8)) Unit,
          ⌜(x.model C S parse answers).1 ≠ .error .panic ∧
            sf.trace = s0.trace ++ (x.model C S parse answers).2.map (storeEvent encRecord answers)⌝ ∗
          apiDecResultAt A x.ret (x.model C S parse answers).1 ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws C answers) ∗
          logOff img ∗ decVtablesAt img.base ∗ stackAt s0.sp wsStack ∗ A.pool
      onPanic := fun x s0 sf => (decryptSignalSpec C A ctl parse S encRecord img).onPanic x s0 sf }
    img

/-! ## 8. Segment Specifications -/

/-- Common step relation for store-kit-parameterized `MessageDecrypt` segments. -/
def DecSegV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (R : SepProp) (s0 s : State)
    (Out : State → Prop) : Prop :=
  (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
  ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
    (Out s' ∨
      SubroutineOutcome (withStoresDecSpecV C A ctl parse S encRecord img kit ikit st0 ist0 Scope)
        x R s0 s')

abbrev DecSeg (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (x : DecryptGhost) (R : SepProp) (s0 s : State)
    (Out : State → Prop) : Prop :=
  DecSegV img C A ctl parse S encRecord abs
    (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope x R s0 s Out

/-- Every record `rec'` produced by `decryptRecord` from a record `rec` satisfying `ScopeAt`
satisfies `kit.RecOk rec'` (needed by `storeShim`). -/
def DecModelRecOk {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  ∀ (x : DecryptGhost) (st0 : kit.StoreState) (rec rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)),
    kit.ScopeAt Scope st0 x.rem.val rec →
    decryptRecord C S parse x rec = .ok (pt, rec') →
    kit.RecOk rec'

theorem hookDecModelRecOk {A : RustAlloc} {b : BitVec 64}
    (C : Crypto) (S : SpqrModel)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) :
    DecModelRecOk (hookSessionStoreSpec A b) C S uuidTryParse Scope :=
  fun _ _ _ _ _ _ _ => trivial

/-- Session-store-only `subroutine_ok` bundle (load/store shims, polls, and future drops),
decoupled from any `HookIdentityStore` assumptions. -/
structure SessionOnlyKitOkS {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop where
  loadShim : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.loadShimOff)
    ((kitLoadShimSpec kit).inImage img)
  loadPoll : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.loadPollOff)
    (kitLoadPollSpecSE img kit Scope encRecord)
  loadFutDrop : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.loadFutDropOff)
    futDropSpec
  storeShim : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.storeShimOff)
    ((kitStoreShimSpec kit).inImage img)
  storePoll : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.storePollOff)
    ((kitStorePollSpecE kit encRecord).inImage img)
  storeFutDrop : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.storeFutDropOff)
    futDropSpec

theorem SessionStoreKitOkS.toSessionOnly {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : SessionStoreKitOkS kit Scope C encRecord ctl abs) :
    SessionOnlyKitOkS kit Scope C encRecord ctl abs :=
  ⟨h.loadShim, h.loadPoll, h.loadFutDrop, h.storeShim, h.storePoll, h.storeFutDrop⟩

/-- Session-store-only `.rodata` vtable slots (`loadSlot`, `storeSlot`, and the 8 session-future
vtable words), decoupled from `IdentityKeyStore` slots. -/
structure SessionOnlyVtablesOk {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) : Prop where
  loadSlot : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗ P
  storeSlot : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗ P
  loadFutDrop : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗ P
  loadFutSize : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗ P
  loadFutAlign : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  loadFutPoll : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗ P
  storeFutDrop : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗ P
  storeFutSize : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗ P
  storeFutAlign : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  storeFutPoll : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff)) ∗ P

theorem KitVtablesOk.toSessionOnly {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} (h : KitVtablesOk img kit) :
    SessionOnlyVtablesOk img kit :=
  ⟨h.loadSlot, h.storeSlot, h.loadFutDrop, h.loadFutSize, h.loadFutAlign, h.loadFutPoll,
   h.storeFutDrop, h.storeFutSize, h.storeFutAlign, h.storeFutPoll⟩

theorem satisfies_decVtablesAtV {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {s : State} {P : SepProp}
    (hvt : SessionOnlyVtablesOk img kit) (hivt : IdentityVtablesOk img ikit)
    (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ decVtablesAtV kit ikit ∗ P := by
  unfold decVtablesAtV decLoadVtableAtV decStoreVtableAtV decSaveVtableAtV decTrustVtableAtV
  simp only [sepConj_assoc]
  exact hvt.loadSlot hF (hvt.loadFutDrop hF (hvt.loadFutSize hF (hvt.loadFutAlign hF
    (hvt.loadFutPoll hF (hvt.storeSlot hF (hvt.storeFutDrop hF (hvt.storeFutSize hF
      (hvt.storeFutAlign hF (hvt.storeFutPoll hF (hivt.saveSlot hF (hivt.saveFutDrop hF
        (hivt.saveFutSize hF (hivt.saveFutAlign hF (hivt.saveFutPoll hF (hivt.trustSlot hF
          (hivt.trustFutDrop hF (hivt.trustFutSize hF (hivt.trustFutAlign hF
            (hivt.trustFutPoll hF hP)))))))))))))))))))

/-- The hypotheses every segment may use, parameterized by `ss : SessionStoreSpec A img.base`,
`id : IdentityStoreSpec A img.base`, and `Scope`. -/
structure DecHypsV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State))
    (ss : SessionStoreSpec A img.base)
    (id : IdentityStoreSpec A img.base)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop where
  loads : Obj.Loads libsignalSessionImage img
  hooks : PublicApiHooksNoStores C A S abs
  kit : SessionOnlyKitOkS ss Scope C encRecord ctl abs
  ikit : IdentityStoreKitOkI img id C ctl abs
  scopeIn : ∀ r, Scope r → RecordInScope r
  recOk : DecModelRecOk ss C S parse Scope

/-- The hypotheses every segment may use (`E₀` specialization). -/
abbrev DecHyps (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs
    (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) RecordInScope

theorem DecHyps.toV {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (h : DecHyps img C A ctl uuidTryParse S encRecord abs) :
    DecHypsV img C A ctl uuidTryParse S encRecord abs
      (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) RecordInScope := h

/-- File-system trace and `envOk` invariant threaded from entry `s0` to `s` across both store kits. -/
abbrev DecFsCtx {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) (s0 s : State) : Prop :=
  FsCtx (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
    (tripleRatchetProgAt img.base C ctl abs) s0 s

/-- Segment `SegLoadV` (`+0x0 → +0x8c`). -/
def SegLoadSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  ∀ (x : DecryptGhost) (R : SepProp) (s0 : State),
    DecFsCtx kit ikit C ctl abs s0 s0 →
    s0.pc = wsEntryPC img → s0.status = .Running → s0.spAligned = true →
    (s0.mem ⊨ (withStoresDecSpecV C A ctl parse S encRecord img kit ikit st0 ist0 Scope).pre x s0 ∗ R) →
    DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s0
      (fun s' => ∃ ans, LoadPolledStateV ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s')

abbrev SegLoadSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegLoadSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Segment `SegDispatchV` (`+0x8c → +0x1a8 / +0x24d4`). -/
def SegDispatchSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    LoadPolledStateV ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => RegionSomeStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s' ∨
        RegionNoneStateV ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s' ∨
        ResultFinalStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x R s0 s')

abbrev SegDispatchSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegDispatchSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Every in-scope loaded record's current session has a pq state meeting `Q`. `Q := fun _ => True`
holds trivially; `Q := (· = [])` is what the SPQR-off callers know. -/
def ScopePq {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop) : Prop :=
  ∀ (rem : AddrVal) (rec : SessionRecord (List (BitVec 8))) (ses : Session (List (BitVec 8))),
    kit.ScopeAt Scope st0 rem rec → rec.currentSession = some ses → Q ses.state.pqRatchetState

theorem scopePq_true {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b)
    (st0 : kit.StoreState) (Scope : SessionRecord (List (BitVec 8)) → Prop) :
    ScopePq kit st0 Scope (fun _ => True) :=
  fun _ _ _ _ _ => trivial

/-- Segment `SegRegionSomeV` (`+0x1a8 → +0x1f50`): instantiates `recordDecryptSpec` restricted to
any PQ-state predicate `Q` satisfied by scoped sessions (`ScopePq`). -/
def SegRegionSomeSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  ∀ (Q : List (BitVec 8) → Prop),
  region_ok (tripleRatchetProgAt img.base C ctl abs) (recordRegionEntry img) (recordRegionExit img)
    ((recordDecryptSpec C A ctl uuidTryParse S img).withVRegs.restrictPre (Q ·.st.pqRatchetState)) →
  ScopePq kit st0 Scope Q →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    RegionSomeStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => PostSomeStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s')

abbrev SegRegionSomeSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegRegionSomeSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Segment `SegRegionNoneV` (`+0x1a8 → +0x1f50`). -/
def SegRegionNoneSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    RegionNoneStateV ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => PostNoneStateV ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s')

abbrev SegRegionNoneSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegRegionNoneSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Segment `SegPostSomeV` (`+0x1f50 → +0x1fcc / +0x22a8`). -/
def SegPostSomeSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  OutgoingRatchet.RemoteIdentityKeyOk img C A ctl abs →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    PostSomeStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => KeyReadyStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s' ∨
        ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x false R s0 s')

abbrev SegPostSomeSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegPostSomeSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Segment `SegPostNoneV` (`+0x1f50 → +0x22a8`). -/
def SegPostNoneSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    PostNoneStateV ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x false R s0 s')

abbrev SegPostNoneSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegPostNoneSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Segment `SegTrustV` (`+0x1fcc → +0x2150 / +0x21b0 / +0x2294`). -/
def SegTrustSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    ikit.addrOk x.rem.val →
    DecFsCtx kit ikit C ctl abs s0 s →
    KeyReadyStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => (∃ ans' t, TrustedStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans' t R s0 s') ∨
        ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x true R s0 s')

abbrev SegTrustSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegTrustSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Segment `SegUntrustedV` (`+0x21b0 → +0x2294`). -/
def SegUntrustedSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    TrustedStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans false R s0 s →
    DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x true R s0 s')

abbrev SegUntrustedSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegUntrustedSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Segment `SegSaveV` (`+0x2150 → +0x2388 / +0x2294`). -/
def SegSaveSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    ikit.addrOk x.rem.val →
    DecFsCtx kit ikit C ctl abs s0 s →
    TrustedStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans true R s0 s →
    DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => (∃ ans', StoreCallStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans' R s0 s') ∨
        ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x true R s0 s')

abbrev SegSaveSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegSaveSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Segment `SegStoreV` (`+0x2388 → +0x24d4 / +0x2294`). -/
def SegStoreSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  FromRecordCallees.DropSessionStructureLocal2Ok img.base C A ctl abs →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    kit.addrOk x.rem.val →
    DecFsCtx kit ikit C ctl abs s0 s →
    StoreCallStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => ResultFinalStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x R s0 s' ∨
        ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x true R s0 s')

abbrev SegStoreSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegStoreSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Segment `SegErrTeardownV` (`+0x2294 / +0x22a8 → +0x24d4`). -/
def SegErrTeardownSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  FromRecordCallees.DropSessionStructureLocal2Ok img.base C A ctl abs →
  ∀ (x : DecryptGhost) (pt : Bool) (R : SepProp) (s0 s : State),
    ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x pt R s0 s →
    DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => ResultFinalStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x R s0 s')

abbrev SegErrTeardownSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegErrTeardownSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Segment `SegWriteV` (`+0x24d4 → +0x2510 ret`). -/
def SegWriteSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  ∀ (x : DecryptGhost) (R : SepProp) (s0 s : State),
    ResultFinalStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x R s0 s →
    DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s (fun _ => False)

abbrev SegWriteSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegWriteSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-! ## Relocatable `[LibsignalPlacement]` Specifications -/

section Placed

open CryptoVerification.LibsignalPublicApi.Placed

/-- Mangled ELF symbol for `<alloc::string::String as core::clone::Clone>::clone`. -/
abbrev lsStringCloneSym : String :=
  "_RNvXs4_NtCs69KKACWg7bl_5alloc6stringNtB5_6StringNtNtCskxtBwYRO61I_4core5clone5Clone5clone"

/-- Mangled ELF symbol for `core::option::expect_failed`. -/
abbrev lsExpectFailedSym : String :=
  "_RNvNtCskxtBwYRO61I_4core6option13expect_failed"

/-- `_with_stores` entry `+0x0` (`(blkPl_197).base`). -/
abbrev wsEntryPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_197).base

abbrev loadPolledPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_197).base + 140#64

abbrev keyReadyPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_197).base + 8140#64

abbrev saveCallPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_197).base + 8528#64

abbrev untrustedPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_197).base + 8624#64

abbrev trustedPCPlaced [LibsignalPlacement] (t : Bool) : BitVec 64 :=
  if t then saveCallPCPlaced else untrustedPCPlaced

abbrev storeCallPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_197).base + 9096#64

/-- ErrJoin `+0x2294` (`pt = true`) or `+0x22a8` (`pt = false`). -/
abbrev errJoinPCPlaced [LibsignalPlacement] (pt : Bool) : BitVec 64 :=
  if pt then (blkPl_197).base + 8852#64 else (blkPl_197).base + 8872#64

abbrev resultFinalPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_197).base + 9428#64

/-- Extra store & stack resources threaded through `R` in the middle seams (`b := 0#64`). -/
def decStoreExtraPlaced {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (st : kit.StoreState) (ist : ikit.IdState) (s0 : State) : SepProp :=
  ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
    kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
    memRegion (s0.sp - BitVec.ofNat 64 (wsStackV kit ikit)) (wsCalleeStackV kit ikit - wsCalleeStack)

theorem wsStack_split_extra_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (st : kit.StoreState) (ist : ikit.IdState) (s0 : State)
    (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
      stackAt s0.sp (wsStackV kit ikit) ⊢
      stackAt s0.sp wsStack ∗ decStoreExtraPlaced kit ikit st ist s0 := by
  have hle := wsCalleeStack_le_V kit ikit
  have hlt := s0.sp.isLt
  have hsum : wsStack + (wsCalleeStackV kit ikit - wsCalleeStack) = wsStackV kit ikit := by
    have : wsStack = wsCalleeStack + wsFrame := rfl
    have : wsStackV kit ikit = wsCalleeStackV kit ikit + wsFrame := rfl
    omega
  rw [← hsum, stackAt_split_bottom s0.sp wsStack (wsCalleeStackV kit ikit - wsCalleeStack) (by omega), hsum]
  unfold decStoreExtraPlaced
  refine Entails.trans ?_ (sepConj_mono_right (Entails.pure_right hbound (Entails.of_eq rfl)))
  exact Entails.of_eq (by ac_rfl)

theorem wsStack_join_extra_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (st : kit.StoreState) (ist : ikit.IdState) (s0 : State) :
    stackAt s0.sp wsStack ∗ decStoreExtraPlaced kit ikit st ist s0 ⊢
      kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
        stackAt s0.sp (wsStackV kit ikit) := by
  have hle := wsCalleeStack_le_V kit ikit
  have hlt := s0.sp.isLt
  have hsum : wsStack + (wsCalleeStackV kit ikit - wsCalleeStack) = wsStackV kit ikit := by
    have : wsStack = wsCalleeStack + wsFrame := rfl
    have : wsStackV kit ikit = wsCalleeStackV kit ikit + wsFrame := rfl
    omega
  unfold decStoreExtraPlaced
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro hbound
  rw [← hsum, stackAt_split_bottom s0.sp wsStack (wsCalleeStackV kit ikit - wsCalleeStack) (by omega), hsum]
  exact Entails.of_eq (by ac_rfl)

theorem wsCalleeStack_join_extra_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (st : kit.StoreState) (ist : ikit.IdState) (s0 : State) :
    stackAt (s0.sp - 0xee0#64) wsCalleeStack ∗ decStoreExtraPlaced kit ikit st ist s0 ⊢
      ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
        kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
        stackAt (s0.sp - 0xee0#64) (wsCalleeStackV kit ikit) := by
  have hle := wsCalleeStack_le_V kit ikit
  have hlt := s0.sp.isLt
  have hsum : wsCalleeStack + (wsCalleeStackV kit ikit - wsCalleeStack) = wsCalleeStackV kit ikit := by omega
  unfold decStoreExtraPlaced
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro hbound
  have h2 : wsCalleeStackV kit ikit ≤ wsStackV kit ikit := Nat.le_add_right _ _
  have hsub : (s0.sp - 0xee0#64) - BitVec.ofNat 64 (wsCalleeStackV kit ikit) =
      s0.sp - BitVec.ofNat 64 (wsStackV kit ikit) := by
    have : wsStackV kit ikit = wsCalleeStackV kit ikit + 0xee0 := rfl
    bv_omega
  rw [← hsum, stackAt_split_bottom (s0.sp - 0xee0#64) wsCalleeStack
        (wsCalleeStackV kit ikit - wsCalleeStack) (by omega), hsum, hsub]
  exact Entails.pure_right hbound (Entails.of_eq (by ac_rfl))

theorem wsCalleeStack_split_extra_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (st : kit.StoreState) (ist : ikit.IdState) (s0 : State)
    (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
      stackAt (s0.sp - 0xee0#64) (wsCalleeStackV kit ikit) ⊢
      stackAt (s0.sp - 0xee0#64) wsCalleeStack ∗ decStoreExtraPlaced kit ikit st ist s0 := by
  have hle := wsCalleeStack_le_V kit ikit
  have hlt := s0.sp.isLt
  have h2 : wsCalleeStackV kit ikit ≤ wsStackV kit ikit := Nat.le_add_right _ _
  have hsum : wsCalleeStack + (wsCalleeStackV kit ikit - wsCalleeStack) = wsCalleeStackV kit ikit := by omega
  have hsub : (s0.sp - 0xee0#64) - BitVec.ofNat 64 (wsCalleeStackV kit ikit) =
      s0.sp - BitVec.ofNat 64 (wsStackV kit ikit) := by
    have : wsStackV kit ikit = wsCalleeStackV kit ikit + 0xee0 := rfl
    bv_omega
  rw [← hsum, stackAt_split_bottom (s0.sp - 0xee0#64) wsCalleeStack
        (wsCalleeStackV kit ikit - wsCalleeStack) (by omega), hsum, hsub]
  unfold decStoreExtraPlaced
  refine Entails.trans ?_ (sepConj_mono_right (Entails.pure_right hbound (Entails.of_eq rfl)))
  exact Entails.of_eq (by ac_rfl)

/-- Machine facts at every seam after the prologue under `[LibsignalPlacement]`. -/
def wsMetaPlaced [LibsignalPlacement] (x : DecryptGhost) (s0 s : State) : Prop :=
  s.status = .Running ∧ s.sp = s0.sp - 0xee0#64 ∧ s0.spAligned = true ∧ s.spAligned = true ∧
    s.readReg64 .x29 = s0.sp - 96#64 ∧ s.readReg64 .x27 = x.ret ∧
    StoreKit.LibsignalCodeRoLoaded lsmpl s.mem ∧ calleeSavedVRegs s = calleeSavedVRegs s0

/-- Frame pieces every post-prologue seam keeps (parameterized by `kit` and `ikit` at `b`). -/
def wsFixedVPlaced {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) : SepProp :=
  wsSavedRegs s0.sp s0 ∗ wsArgCellsV kit ikit x s0 sp ∗ decVtablesAtV kit ikit ∗
  memRegion (sp + 0xa0#64) 0x40 ∗
  memRegion (sp + 0x2c8#64) 8 ∗ memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80

/-- Borrowed inputs and environment every seam keeps under `[LibsignalPlacement]`. -/
def wsEnvPlaced [LibsignalPlacement] (A : RustAlloc) (x : DecryptGhost) (sp : BitVec 64) : SepProp :=
  signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗ stackAt sp wsCalleeStack ∗ A.pool

/-- Introduce `decVtablesAtV kit ikit` from `SessionOnlyVtablesPlacedOk` and `IdentityVtablesPlacedOk`
under `LibsignalRoLoaded lsmpl m`. -/
theorem satisfies_decVtablesAtV_placed [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {m : Memory} {P : SepProp}
    (hvt : SessionOnlyVtablesPlacedOk kit) (hivt : IdentityVtablesPlacedOk ikit)
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ decVtablesAtV kit ikit ∗ P := by
  unfold decVtablesAtV decLoadVtableAtV decStoreVtableAtV decSaveVtableAtV decTrustVtableAtV
  simp only [sepConj_assoc]
  exact hvt.loadSlot hro (hvt.loadFutDrop hro (hvt.loadFutSize hro (hvt.loadFutAlign hro
    (hvt.loadFutPoll hro (hvt.storeSlot hro (hvt.storeFutDrop hro (hvt.storeFutSize hro
      (hvt.storeFutAlign hro (hvt.storeFutPoll hro (hivt.saveSlot hro (hivt.saveFutDrop hro
        (hivt.saveFutSize hro (hivt.saveFutAlign hro (hivt.saveFutPoll hro (hivt.trustSlot hro
          (hivt.trustFutDrop hro (hivt.trustFutSize hro (hivt.trustFutAlign hro
            (hivt.trustFutPoll hro hP)))))))))))))))))))

def LoadPolledStateVPlaced [LibsignalPlacement] {A : RustAlloc} (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = loadPolledPCPlaced ∧ wsMetaPlaced x s0 s ∧ wsStack ≤ s0.sp.toNat ∧
  s.readReg64 .x19 = sp + 0x5f0#64 ∧
  kit.loadRel st0 x.rem.val ans.loadSession ∧
  s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
  (s.mem ⊨ wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
    (∃∗ box : BitVec 64, ⌜box ≠ 0#64⌝ ∗ ((sp + 0x2d0#64) ↦₆₄ box) ∗
      ((sp + 0x2d8#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
      A.live box kit.loadBoxSize 8 ∗
      kit.loadBoxAt box (s0.readReg64 .x3) x.remA 1#8) ∗
    loadPollPlacedOutAtS Scope A (sp + 0x5f0#64) ans.loadSession ∗
    memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗
    memRegion (sp + 0x300#64) 0x1b0 ∗ memRegion (sp + 0x4b0#64) 0x140 ∗
    memRegion (sp + 0x760#64) 0x6a0 ∗ memRegion x.ret 48 ∗ tapeAt ctl x.cur x.rest ∗
    decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R)

/-- Public-API frame around `Record.recordDecryptPlacedSpec`. -/
def wsRegionFrameVPlaced {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (x : DecryptGhost) (s0 : State) (prevCap prevPtr : BitVec 64) : SepProp :=
  let sp := s0.sp - 0xee0#64
  wsSavedRegs s0.sp s0 ∗ wsArgCellsV kit ikit x s0 sp ∗ decVtablesAtV kit ikit ∗
    memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
    memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
    ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
    memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
    memRegion (sp + 0x300#64) 0x1b0 ∗
    memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
    memRegion x.ret 48

def RegionSomeStateVPlaced [LibsignalPlacement] (C : Crypto) {A : RustAlloc} (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State) : Prop :=
  s.pc = Record.recEntryPlaced ∧ wsMetaPlaced x s0 s ∧
  ∃ (rec : SessionRecord (List (BitVec 8))) (ses : Session (List (BitVec 8))) (G : SessionGhost)
    (prevCap prevPtr : BitVec 64),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    rec.currentSession = some ses ∧ sessionModelRel G ses ∧
    s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    (s.mem ⊨ (Record.recordDecryptPlacedSpec C A ctl parse S).pre (recGhostOf x prevPtr G ses.state) s ∗
      wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗ decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R)

/-- Placed RN pre: `recordDecryptPlacedSpec.pre` with current session `None`. -/
def regionNonePrePlaced [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64) (x : DecryptGhost)
    (prevPtr : BitVec 64) (s : State) : SepProp :=
  ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s.mem ∧ s.spAligned = true ∧ s.readReg64 .x27 = x.ret ∧
    s.readReg64 .x19 = x.remA ∧ s.readReg64 .x23 = s.sp + 0x5f0#64 ∧
    s.readReg64 .x24 = s.sp + 0xca0#64 ∧ rootStack ≤ s.sp.toNat⌝ ∗
  memRegion s.sp 0xa0 ∗ ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
  ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
  ((s.sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (s.sp + 0x140#64) 336 ∗
  memRegion (s.sp + 0x4b0#64) 0x950 ∗
  protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
  stackAt s.sp rootStack ∗ A.pool

def RegionNoneStateVPlaced [LibsignalPlacement] {A : RustAlloc} (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  s.pc = Record.recEntryPlaced ∧ wsMetaPlaced x s0 s ∧
  ∃ (rec : SessionRecord (List (BitVec 8))) (prevCap prevPtr : BitVec 64),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    rec.currentSession = none ∧
    s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    (s.mem ⊨ regionNonePrePlaced A ctl x prevPtr s ∗
      wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗ decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R)

def PostSomeStateVPlaced [LibsignalPlacement] (C : Crypto) {A : RustAlloc} (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  s.pc = Record.recExitPlaced ∧ wsMetaPlaced x s0 s ∧
  ∃ (s1 : State) (rec : SessionRecord (List (BitVec 8))) (ses : Session (List (BitVec 8)))
    (G : SessionGhost) (prevCap prevPtr : BitVec 64),
    s1.sp = s0.sp - 0xee0#64 ∧
    s1.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    rec.currentSession = some ses ∧ sessionModelRel G ses ∧
    (s.mem ⊨ (Record.recordDecryptPlacedSpec C A ctl parse S).post (recGhostOf x prevPtr G ses.state) s1 s ∗
      wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗ decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R)

def PostNoneStateVPlaced [LibsignalPlacement] {A : RustAlloc} (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = Record.recExitPlaced ∧ wsMetaPlaced x s0 s ∧
  s.readReg64 .x26 = sp + 0xa0#64 ∧
  s.readReg64 .x28 = recordResultTag (.error (.invalidMessage .whisper .decryptionFailed)) ∧
  ∃ (rec : SessionRecord (List (BitVec 8))) (prevCap prevPtr : BitVec 64),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    rec.currentSession = none ∧
    s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    (s.mem ⊨ memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
      ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
      ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336 ∗
      recordResultAt A (sp + 0x4b0#64) (.error (.invalidMessage .whisper .decryptionFailed)) ∗
      memRegion (sp + 0x4e0#64) 0x920 ∗
      protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
      stackAt sp rootStack ∗ A.pool ∗
      wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗ decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R)

def KeyReadyStateVPlaced [LibsignalPlacement] (C : Crypto) {A : RustAlloc} (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = keyReadyPCPlaced ∧ wsMetaPlaced x s0 s ∧ s.readReg64 .x26 = sp + 0xa0#64 ∧
  s.readReg64 .x22 = sp + 0x294#64 ∧
  ∃ (rec rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) (ses : Session (List (BitVec 8)))
    (k : IdentityKey),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    decryptRecord C S parse x rec = .ok (pt, rec') ∧ rec'.currentSession = some ses ∧
    ses.state.remoteIdentity = some k ∧
    s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    (s.mem ⊨ wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0xca0#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x9a0 ∗ memRegion (sp + 0xcc0#64) 0x140 ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R)

def TrustedStateVPlaced [LibsignalPlacement] (C : Crypto) {A : RustAlloc} (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (t : Bool)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = trustedPCPlaced t ∧ wsMetaPlaced x s0 s ∧ s.readReg64 .x26 = sp + 0xa0#64 ∧
  s.readReg64 .x19 = sp + 0x2a8#64 ∧ s.readReg64 .x22 = sp + 0x294#64 ∧
  ∃ (rec rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) (ses : Session (List (BitVec 8)))
    (k : IdentityKey),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    decryptRecord C S parse x rec = .ok (pt, rec') ∧ rec'.currentSession = some ses ∧
    ses.state.remoteIdentity = some k ∧ ans.isTrustedIdentity = .ok t ∧
    ikit.trustRel ist0 x.rem.val k .receiving ans.isTrustedIdentity ∧
    s.trace = s0.trace ++ (kit.loadEvs encRecord x.rem.val ans.loadSession ++
      ikit.trustEvs x.rem.val k .receiving ans.isTrustedIdentity) ∧
    (s.mem ⊨ wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st0 (ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity) s0 ∗ R)

def StoreCallStateVPlaced [LibsignalPlacement] (C : Crypto) {A : RustAlloc} (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = storeCallPCPlaced ∧ wsMetaPlaced x s0 s ∧ s.readReg64 .x26 = sp + 0xa0#64 ∧
  s.readReg64 .x22 = sp + 0x294#64 ∧
  ∃ (rec rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) (ses : Session (List (BitVec 8)))
    (k : IdentityKey) (c : IdentityChange),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    decryptRecord C S parse x rec = .ok (pt, rec') ∧ rec'.currentSession = some ses ∧
    ses.state.remoteIdentity = some k ∧ ans.isTrustedIdentity = .ok true ∧
    ans.saveIdentity = .ok c ∧
    ikit.trustRel ist0 x.rem.val k .receiving ans.isTrustedIdentity ∧
    ikit.saveRel (ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity)
      x.rem.val k ans.saveIdentity ∧
    s.trace = s0.trace ++ (kit.loadEvs encRecord x.rem.val ans.loadSession ++
      ikit.trustEvs x.rem.val k .receiving ans.isTrustedIdentity ++
      ikit.saveEvs x.rem.val k ans.saveIdentity) ∧
    (s.mem ⊨ wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ memRegion (sp + 0x2a8#64) 0x20 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st0
        (ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity)
          x.rem.val k ans.saveIdentity) s0 ∗ R)

def ErrJoinStateVPlaced [LibsignalPlacement] (C : Crypto) {A : RustAlloc} (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (pt : Bool) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = errJoinPCPlaced pt ∧ wsMetaPlaced x s0 s ∧ s.readReg64 .x26 = sp + 0xa0#64 ∧
  s.readReg64 .x28 ≠ pendingTag ∧
  ∃ (ans : StoreAnswers (List (BitVec 8)) Unit) (cs : Option (SessionGhost × SessionState (List (BitVec 8)))),
    (x.model C S parse ans).1 ≠ .error .panic ∧
    (∀ p, (x.model C S parse ans).1 ≠ .ok p) ∧
    (∀ r, ans.loadSession = .ok (some r) → kit.ScopeAt Scope st0 x.rem.val r) ∧
    kit.callsRel st0 ans (x.model C S parse ans).2 ∧
    ikit.idCallsRel ist0 ans (x.model C S parse ans).2 ∧
    s.trace = s0.trace ++ ikit.traceOfWith kit encRecord ans (x.model C S parse ans).2 ∧
    (s.mem ⊨ wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) cs ∗
      (if pt then ∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p
       else memRegion (sp + 0x290#64) 24) ∗
      StagedRes A (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (sp + 0x580#64)
        (x.model C S parse ans).1 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit
        (kit.storeFinal st0 ans (x.model C S parse ans).2)
        (ikit.idFinal ist0 ans (x.model C S parse ans).2) s0 ∗ R)

def ResultFinalStateVPlaced [LibsignalPlacement] (C : Crypto) {A : RustAlloc} (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = resultFinalPCPlaced ∧ wsMetaPlaced x s0 s ∧
  ∃ ans : StoreAnswers (List (BitVec 8)) Unit,
    (x.model C S parse ans).1 ≠ .error .panic ∧
    (∀ r, ans.loadSession = .ok (some r) → kit.ScopeAt Scope st0 x.rem.val r) ∧
    kit.callsRel st0 ans (x.model C S parse ans).2 ∧
    ikit.idCallsRel ist0 ans (x.model C S parse ans).2 ∧
    s.trace = s0.trace ++ ikit.traceOfWith kit encRecord ans (x.model C S parse ans).2 ∧
    (s.mem ⊨ wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      StagedRes A (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (sp + 0x300#64)
        (x.model C S parse ans).1 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x324#64) 0xadc ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit
        (kit.storeFinal st0 ans (x.model C S parse ans).2)
        (ikit.idFinal ist0 ans (x.model C S parse ans).2) s0 ∗ R)

/-- Relocatable `[LibsignalPlacement]` specification of `session_message_decrypt_signal_with_stores`
(block `197`) parameterized by `kit`, `ikit`, `st0`, `ist0`, and `Scope`. -/
def withStoresDecPlacedSpecV [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec DecryptGhost :=
  StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.remA ∧ s.readReg64 .x2 = x.locA ∧
          s.readReg64 .x4 = kit.ss_vt ∧ s.readReg64 .x6 = ikit.id_vt ∧
          s.readReg64 .x8 = x.ret ∧ wsStackV kit ikit ≤ s.sp.toNat ∧
          kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
        kit.storeAt (s.readReg64 .x3) st0 ∗
        ikit.identityAt (s.readReg64 .x5) ist0 ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 48 ∗ tapeAt ctl x.cur x.rest ∗
        FromRecordCallees.lsLogOff ∗ decVtablesAtV kit ikit ∗ stackAt s.sp (wsStackV kit ikit) ∗ A.pool
      post := fun x s0 sf =>
        ∃∗ answers : StoreAnswers (List (BitVec 8)) Unit,
          ⌜(x.model C S parse answers).1 ≠ .error .panic ∧
            (∀ r, answers.loadSession = .ok (some r) → kit.ScopeAt Scope st0 x.rem.val r) ∧
            kit.callsRel st0 answers (x.model C S parse answers).2 ∧
            ikit.idCallsRel ist0 answers (x.model C S parse answers).2 ∧
            sf.trace = s0.trace ++ ikit.traceOfWith kit encRecord answers (x.model C S parse answers).2⌝ ∗
          kit.storeAt (s0.readReg64 .x3)
            (kit.storeFinal st0 answers (x.model C S parse answers).2) ∗
          ikit.identityAt (s0.readReg64 .x5)
            (ikit.idFinal ist0 answers (x.model C S parse answers).2) ∗
          apiDecResultAt A x.ret (x.model C S parse answers).1 ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws C answers) ∗
          FromRecordCallees.lsLogOff ∗ decVtablesAtV kit ikit ∗ stackAt s0.sp (wsStackV kit ikit) ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜s0.trace <+: sf.trace ∧
           (allocFailedIn s0 sf ∨
            ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
              kit.loadRel st0 x.rem.val answers.loadSession ∧
              s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
              ((x.model C S parse answers).1 = .error .panic ∨ x.recvPanics S answers))⌝ ∗
        anyHeap }

theorem withStoresDecPlacedSpecV_pre_addrOk [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).pre x s0 ∗ R) :
    kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val := by
  have ⟨_, hp⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.1.2.2.2.2.2.2.2

/-- Common segment step shape on `lsProg_197 H` under `[LibsignalPlacement]`. -/
def DecSegVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (R : SepProp) (s0 s : State)
    (Out : State → Prop) : Prop :=
  (lsProg_197 H).CodeLoaded s.mem →
  ∃ s', Steps (lsProg_197 H) s s' ∧
    (Out s' ∨
      SubroutineOutcome (withStoresDecPlacedSpecV C A ctl parse S encRecord kit ikit st0 ist0 Scope)
        x R s0 s')

/-- External hook contracts on `H : LibsignalHooks` (mangled ELF symbol names) used by Block `197`
and its `FromRecordCallees` / `FromRecordChainClone` callees. -/
structure PublicApiDecHooksPlaced (A : RustAlloc) (H : LibsignalHooks) : Prop where
  shim : HookSat H lsRustNoAllocShimSym sessionShimSpec
  alloc : HookSat H lsRustAllocSym (rustAllocSpec A)
  dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)
  memcpy : HookSat H "memcpy" sessionMemcpyRegionSpec
  stringClone : HookSat H lsStringCloneSym (stringCloneSpec A)
  handleError : H lsHandleErrorSym = some Rust.panicked
  expectFailed : H lsExpectFailedSym = some Rust.panicked

/-- Hypotheses available to every `[LibsignalPlacement]` `MessageDecrypt` segment. -/
structure DecHypsVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (ss : SessionStoreSpec A 0#64)
    (id : IdentityStoreSpec A 0#64)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop where
  hooks : PublicApiDecHooksPlaced A H
  kit : SessionOnlyKitPlacedOkSE ss Scope encRecord H
  ikit : IdentityStoreKitPlacedOkI id H
  scopeIn : ∀ r, Scope r → RecordInScope r
  recOk : DecModelRecOk ss C S parse Scope

/-- Placed fs carrier over `lsProg_197 H`. -/
abbrev DecFsCtxPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (H : LibsignalHooks) (s0 s : State) : Prop :=
  FsCtx (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
    (lsProg_197 H) s0 s

/-- Placed `<SessionState>::remote_identity_key` (Block `29`) lifted to `lsProg_197 H`. -/
abbrev RemoteIdentityKeyPlacedOk [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_197 H) (lsmpl.base 29)
    (StoreKit.withLsRoCl lsmpl (Getters.remoteIdentityKeyPlacedSpec A))

/-- Placed `drop_glue::<SessionStructure> [local#2]` (Block `139`) lifted to `lsProg_197 H`. -/
abbrev DropSessionStructureLocal2PlacedOk [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_197 H) (lsmpl.base 139)
    (StoreKit.withLsRoCl lsmpl (FromRecordCallees.dropSessionStructureLocal2Spec A))

def SegLoadSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  ∀ (x : DecryptGhost) (R : SepProp) (s0 : State),
    DecFsCtxPlaced kit ikit H s0 s0 →
    s0.pc = wsEntryPCPlaced → s0.status = .Running → s0.spAligned = true →
    (s0.mem ⊨ (withStoresDecPlacedSpecV C A ctl parse S encRecord kit ikit st0 ist0 Scope).pre x s0 ∗ R) →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s0
      (fun s' => ∃ ans, LoadPolledStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s')

def SegDispatchSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    LoadPolledStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => RegionSomeStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans R s0 s' ∨
        RegionNoneStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s' ∨
        ResultFinalStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x R s0 s')

def SegRegionSomeSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  ∀ (Q : List (BitVec 8) → Prop),
  region_ok (lsProg_197 H) Record.recEntryPlaced Record.recExitPlaced
    ((Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.restrictPre (Q ·.st.pqRatchetState)) →
  ScopePq kit st0 Scope Q →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    RegionSomeStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => PostSomeStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans R s0 s')

def SegRegionNoneSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    RegionNoneStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => PostNoneStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s')

def SegPostSomeSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  RemoteIdentityKeyPlacedOk A H →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    PostSomeStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => KeyReadyStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans R s0 s' ∨
        ErrJoinStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x false R s0 s')

def SegPostNoneSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    PostNoneStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => ErrJoinStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x false R s0 s')

def SegTrustSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    ikit.addrOk x.rem.val →
    DecFsCtxPlaced kit ikit H s0 s →
    KeyReadyStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => (∃ ans' t, TrustedStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans' t R s0 s') ∨
        ErrJoinStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x true R s0 s')

def SegUntrustedSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    TrustedStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans false R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => ErrJoinStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x true R s0 s')

def SegSaveSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    ikit.addrOk x.rem.val →
    DecFsCtxPlaced kit ikit H s0 s →
    TrustedStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans true R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => (∃ ans', StoreCallStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans' R s0 s') ∨
        ErrJoinStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x true R s0 s')

def SegStoreSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  DropSessionStructureLocal2PlacedOk A H →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    kit.addrOk x.rem.val →
    DecFsCtxPlaced kit ikit H s0 s →
    StoreCallStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => ResultFinalStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x R s0 s' ∨
        ErrJoinStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x true R s0 s')

def SegErrTeardownSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  DropSessionStructureLocal2PlacedOk A H →
  ∀ (x : DecryptGhost) (pt : Bool) (R : SepProp) (s0 s : State),
    ErrJoinStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x pt R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => ResultFinalStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x R s0 s')

def SegWriteSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  ∀ (x : DecryptGhost) (R : SepProp) (s0 s : State),
    ResultFinalStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s (fun _ => False)

end Placed

end CryptoVerification.LibsignalPublicApi.MessageDecrypt

