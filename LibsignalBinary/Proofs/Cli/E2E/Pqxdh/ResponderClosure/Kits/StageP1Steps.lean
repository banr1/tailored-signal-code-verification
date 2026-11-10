/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegTrustAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.StageP1
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Stage P1 Layouts, Stack Helpers, and Segment Lemmas

Defines Stage P1 stack budgets, the coroutine `SessionRecord` slot `p1LoadedRecordAt` (`coroPtr +
0xe0..0x250`), condition and alignment helpers, and straight-line `SepWP` segment lemmas for
`load_session` (`Some(r)` copy) and `is_trusted_identity` post-poll teardown.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

/-! ## 1. Stack Budgets & Coroutine `SessionRecord` Slot -/

/-- Stack budget for Stage P1 Part A (`load_session` shim + poll + `futDrop` + `__rust_dealloc`). -/
def loadCallStack {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) : Nat :=
  max kit.loadShimStack (max kit.loadPollStack allocHookStack)

/-- Combined callee stack budget for full Stage P1 (`load_session` followed by
`is_trusted_identity`). -/
def stageP1CallStack {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) : Nat :=
  max (loadCallStack kit) (trustCallStack ikit)

/-- Callee stack budget for the untrusted error exit (`+0x06e4 -> ret`), covering both
`<String as Clone>::clone` (`extHookStack`), `drop_in_place::<SessionStructure>`
(`dropSessionStructureLocal2Stack`), and `__rust_dealloc` (`allocHookStack`). -/
def untrustedErrCallStack : Nat :=
  max extHookStack (max dropSessionStructureLocal2Stack allocHookStack)

/-- Combined callee stack budget for Stage P1 including the untrusted identity exit path. -/
def stageP1UntrustedCallStack {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) : Nat :=
  max (stageP1CallStack kit ikit) untrustedErrCallStack

/-- Coroutine `SessionRecord` slot at `coroPtr + 0xe0..0x250` (368 bytes = 32-byte header +
336-byte body, `0xe0 + 0x170 = 0x250`) after Stage P1 Part A (`load_session`):
- `none`: initialized empty `SessionRecord` header `sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64)`
  plus untouched tail `memRegion (coroPtr + 0x100#64) 336` (fresh-session Path A).
- `some r`: loaded `SessionRecord r` satisfying `Scope r`, moved into `coroPtr + 0xe0#64` as
  `sessionRecordAt A (coroPtr + 0xe0#64) g r` via `+0x04cc..+0x04f8` + `+0x059c` (matched-session
  Path B). -/
def p1LoadedRecordAt (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc)
    (coroPtr : BitVec 64) :
    Option (SessionRecord (List (BitVec 8))) → SepProp
  | none =>
    sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
    memRegion (coroPtr + 0x100#64) 336
  | some r =>
    ⌜Scope r⌝ ∗ ∃∗ g : RecordGhost, sessionRecordAt A (coroPtr + 0xe0#64) g r

/-! ## 2. Stack, Alignment, Repack, and Condition Helpers -/

theorem stackAt_split_of_le (sp : BitVec 64) (big small : Nat)
    (hle : small ≤ big) (hbig : big ≤ 2 ^ 64) :
    stackAt sp big =
      memRegion (sp - BitVec.ofNat 64 big) (big - small) ∗ stackAt sp small := by
  have h := ProofLib.stackAt_split_bottom sp small (big - small) (by omega)
  rwa [Nat.add_sub_of_le hle] at h

/-- Proves that `sp0 - 0xcd0#64` preserves 16-byte stack alignment (`0xcd0 = 16 * 205`). -/
theorem sp_sub_cd0_align_std3 {sp0 : BitVec 64} (h : (sp0 &&& 15#64 == 0#64) = true) :
    ((sp0 - 0xcd0#64) &&& 15#64 == 0#64) = true :=
  spAligned_sub sp0 0xcd0#64 h (by decide)

theorem cond_ne_adds64_of_ne_neg3_std3 {w : BitVec 64} (h : w ≠ 0xfffffffffffffffd#64) :
    ConditionHolds CondCode.NE (addsPState64 w 3#64) = true := by
  have hne : w + 3#64 ≠ 0#64 := by bv_omega
  rw [conditionHolds_ne_addsPState64]
  exact bne_iff_ne.mpr hne

theorem cond_ne_adds64_of_ne_neg2_std3 {w : BitVec 64} (h : w ≠ 0xfffffffffffffffe#64) :
    ConditionHolds CondCode.NE (addsPState64 w 2#64) = true := by
  have hne : w + 2#64 ≠ 0#64 := by bv_omega
  rw [conditionHolds_ne_addsPState64]
  exact bne_iff_ne.mpr hne

theorem cond_eq_adds64_of_ne_neg1_std3 {w : BitVec 64} (h : w ≠ 0xffffffffffffffff#64) :
    ConditionHolds CondCode.EQ (addsPState64 w 1#64) = false := by
  have hne : w + 1#64 ≠ 0#64 := by bv_omega
  rw [conditionHolds_eq_addsPState64]
  exact beq_eq_false_iff_ne.mpr hne

/-- Split 5 words `p + 0x10 .. p + 0x38` into `(p + 0x10) ↦₃₂`, four `↦₆₄` at `+0x14..+0x34`,
and `(p + 0x34) ↦₃₂` matching `wp_steps` quadword loads/stores. -/
theorem words5_repack_sp3e0 (sp w2 w3 w4 w5 w6 : BitVec 64) :
    ((sp + 0x3f0#64) ↦₆₄ w2) ∗ ((sp + 0x3f8#64) ↦₆₄ w3) ∗ ((sp + 0x400#64) ↦₆₄ w4) ∗
        ((sp + 0x408#64) ↦₆₄ w5) ∗ ((sp + 0x410#64) ↦₆₄ w6) =
      ((sp + 0x3f0#64) ↦₃₂ w2.extractLsb' 0 32) ∗
        ((sp + 0x3f4#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
        ((sp + 0x3fc#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
        ((sp + 0x404#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
        ((sp + 0x40c#64) ↦₆₄ (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)) ∗
        ((sp + 0x414#64) ↦₃₂ w6.extractLsb' 32 32) := by
  have h := out_repack (sp + 0x3e8#64) w2 w3 w4 w5 w6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  exact h

/-- Inverse repack at `coroPtr + 0xe0`: reassemble 5 words `coroPtr + 0xf0 .. coroPtr + 0x118`
from `(coroPtr + 0xf0) ↦₃₂`, four `↦₆₄` at `+0xf4..+0x114`, and `(coroPtr + 0x114) ↦₃₂`. -/
theorem words5_unpack_coro_e0 (coroPtr w2 w3 w4 w5 w6 : BitVec 64) :
    ((coroPtr + 0xf0#64) ↦₃₂ w2.extractLsb' 0 32) ∗
        ((coroPtr + 0xf4#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
        ((coroPtr + 0xfc#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
        ((coroPtr + 0x104#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
        ((coroPtr + 0x10c#64) ↦₆₄ (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)) ∗
        ((coroPtr + 0x114#64) ↦₃₂ w6.extractLsb' 32 32) =
      ((coroPtr + 0xf0#64) ↦₆₄ w2) ∗ ((coroPtr + 0xf8#64) ↦₆₄ w3) ∗
        ((coroPtr + 0x100#64) ↦₆₄ w4) ∗ ((coroPtr + 0x108#64) ↦₆₄ w5) ∗
        ((coroPtr + 0x110#64) ↦₆₄ w6) := by
  have h := out_repack (coroPtr + 0xe8#64) w2 w3 w4 w5 w6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  exact h.symm

/-- Decompose the 336-byte uninitialized slot `coroPtr + 0x100..0x250` into 3 words at
`+0x100..+0x118` and `memRegion (coroPtr + 0x118#64) 312` for `p1_load_some_seg4_wp`. -/
theorem coro_body336_split (coroPtr : BitVec 64) :
    cells (coroPtr + 0xe0#64) 4 ∗ memRegion (coroPtr + 0x100#64) 336 ⊢
      ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
      ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64,
        ((coroPtr + 0xe0#64) ↦₆₄ c0) ∗
        ((coroPtr + 0xe8#64) ↦₆₄ c1) ∗
        ((coroPtr + 0xf0#64) ↦₃₂ c2.extractLsb' 0 32) ∗
        ((coroPtr + 0xf4#64) ↦₆₄ (c3.extractLsb' 0 32 ++ c2.extractLsb' 32 32)) ∗
        ((coroPtr + 0xfc#64) ↦₆₄ (c4.extractLsb' 0 32 ++ c3.extractLsb' 32 32)) ∗
        ((coroPtr + 0x104#64) ↦₆₄ (c5.extractLsb' 0 32 ++ c4.extractLsb' 32 32)) ∗
        ((coroPtr + 0x10c#64) ↦₆₄ (c6.extractLsb' 0 32 ++ c5.extractLsb' 32 32)) ∗
        ((coroPtr + 0x114#64) ↦₃₂ c6.extractLsb' 32 32) ∗
        memRegion (coroPtr + 0x118#64) 312 := by
  rw [ProofLib.memRegion_split (coroPtr + 0x100#64) 8 328 (by decide),
      ProofLib.memRegion_split (coroPtr + 0x100#64 + 8#64) 8 320 (by decide),
      ProofLib.memRegion_split (coroPtr + 0x100#64 + 8#64 + 8#64) 8 312 (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  dsimp only [cells]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro c6
  apply Entails.sepExists_elim; intro c5
  apply Entails.sepExists_elim; intro c4
  apply Entails.sepExists_elim; intro c3
  apply Entails.sepExists_elim; intro c2
  apply Entails.sepExists_elim; intro c1
  apply Entails.sepExists_elim; intro c0
  refine Entails.sepExists_right c3 (Entails.sepExists_right c2
    (Entails.sepExists_right c1 (Entails.sepExists_right c0
      (Entails.sepExists_right c4 (Entails.sepExists_right c5
        (Entails.sepExists_right c6 ?_))))))
  have hrep := (words5_unpack_coro_e0 coroPtr c1 c0 c4 c5 c6).symm
  refine Entails.of_eq ?_
  calc
    ((coroPtr + 224#64) ↦₆₄ c3) ∗ ((coroPtr + 232#64) ↦₆₄ c2) ∗
        ((coroPtr + 240#64) ↦₆₄ c1) ∗ ((coroPtr + 248#64) ↦₆₄ c0) ∗
        ((coroPtr + 256#64) ↦₆₄ c4) ∗ ((coroPtr + 264#64) ↦₆₄ c5) ∗
        ((coroPtr + 272#64) ↦₆₄ c6) ∗ memRegion (coroPtr + 280#64) 312
      = (((coroPtr + 240#64) ↦₆₄ c1) ∗ ((coroPtr + 248#64) ↦₆₄ c0) ∗
          ((coroPtr + 256#64) ↦₆₄ c4) ∗ ((coroPtr + 264#64) ↦₆₄ c5) ∗
          ((coroPtr + 272#64) ↦₆₄ c6)) ∗
        ((coroPtr + 224#64) ↦₆₄ c3) ∗ ((coroPtr + 232#64) ↦₆₄ c2) ∗
        memRegion (coroPtr + 280#64) 312 := by ac_rfl
    _ = _ := by rw [hrep]; ac_rfl

/-- Collapse `(sp + 0x210..0x234)` back into `memRegion (sp + 0x210#64) 36` and join with
`memRegion (sp + 0xd8#64) 312` into `memRegion (sp + 0xd8#64) 348`. -/
theorem sp_d8_348_rejoin (sp v0 v1 v2 v3 : BitVec 64) (dv4 : BitVec 32) :
    memRegion (sp + 0xd8#64) 312 ∗
      ((sp + 0x210#64) ↦₆₄ v0) ∗ ((sp + 0x218#64) ↦₆₄ v1) ∗
      ((sp + 0x220#64) ↦₆₄ v2) ∗ ((sp + 0x228#64) ↦₆₄ v3) ∗
      ((sp + 0x230#64) ↦₃₂ dv4) ⊢
      memRegion (sp + 0xd8#64) 348 := by
  have hmr : memRegion (sp + 0xd8#64) 348 =
      memRegion (sp + 0xd8#64) 312 ∗ memRegion (sp + 0x210#64) 36 :=
    ProofLib.memRegion_split' (b := sp + 0xd8#64) (n := 312) (k := 36)
      (b' := sp + 0x210#64) rfl (by bv_omega) (by decide)
  rw [hmr,
      ProofLib.memRegion_split (sp + 0x210#64) 8 28 (by decide),
      ProofLib.memRegion_split (sp + 0x210#64 + 8#64) 8 20 (by decide),
      ProofLib.memRegion_split (sp + 0x210#64 + 8#64 + 8#64) 8 12 (by decide),
      ProofLib.memRegion_split (sp + 0x210#64 + 8#64 + 8#64 + 8#64) 8 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (pointsTo32_entails_memRegion _ _)))))

/-- Unpack the 39 uninspected trailing bytes of `trustPollOutAt` (`Ok(t)`) at `sp + 0x3e9..0x410`
into the subword cells read by `p1_seg6a_any_wp`. -/
theorem trustOut39_split_p1 (sp : BitVec 64) :
    memRegion (sp + 0x3e9#64) 39 ⊢
      ∃∗ d_3e9 : BitVec 32, ∃∗ h_3ed : BitVec 16, ∃∗ b_3ef : BitVec 8,
      ∃∗ w_3f0 : BitVec 64, ∃∗ d_3f8 : BitVec 32, ∃∗ d_3fc : BitVec 32,
      ∃∗ w_400 : BitVec 64, ∃∗ w_408 : BitVec 64,
        ((sp + 0x3e9#64) ↦₃₂ d_3e9) ∗
        ((sp + 0x3ed#64) ↦₁₆ h_3ed) ∗
        ((sp + 0x3ef#64) ↦₈ b_3ef) ∗
        ((sp + 0x3f0#64) ↦₆₄ w_3f0) ∗
        ((sp + 0x3f8#64) ↦₃₂ d_3f8) ∗
        ((sp + 0x3fc#64) ↦₃₂ d_3fc) ∗
        ((sp + 0x400#64) ↦₆₄ w_400) ∗
        ((sp + 0x408#64) ↦₆₄ w_408) := by
  rw [ProofLib.memRegion_split (sp + 0x3e9#64) 4 35 (by decide),
      ProofLib.memRegion_split (sp + 0x3e9#64 + 4#64) 2 33 (by decide),
      ProofLib.memRegion_split (sp + 0x3e9#64 + 4#64 + 2#64) 1 32 (by decide),
      ProofLib.memRegion_split (sp + 0x3e9#64 + 4#64 + 2#64 + 1#64) 8 24 (by decide),
      ProofLib.memRegion_split (sp + 0x3e9#64 + 4#64 + 2#64 + 1#64 + 8#64) 4 20 (by decide),
      ProofLib.memRegion_split (sp + 0x3e9#64 + 4#64 + 2#64 + 1#64 + 8#64 + 4#64) 4 16 (by decide),
      ProofLib.memRegion_split (sp + 0x3e9#64 + 4#64 + 2#64 + 1#64 + 8#64 + 4#64 + 4#64) 8 8
        (by decide),
      ProofLib.memRegion_four, ProofLib.memRegion_two, ProofLib.memRegion_one,
      ProofLib.memRegion_eight, ProofLib.memRegion_four, ProofLib.memRegion_four,
      ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w_408
  apply Entails.sepExists_elim; intro w_400
  apply Entails.sepExists_elim; intro d_3fc
  apply Entails.sepExists_elim; intro d_3f8
  apply Entails.sepExists_elim; intro w_3f0
  apply Entails.sepExists_elim; intro b_3ef
  apply Entails.sepExists_elim; intro h_3ed
  apply Entails.sepExists_elim; intro d_3e9
  exact Entails.sepExists_right d_3e9 (Entails.sepExists_right h_3ed
    (Entails.sepExists_right b_3ef (Entails.sepExists_right w_3f0
      (Entails.sepExists_right d_3f8 (Entails.sepExists_right d_3fc
        (Entails.sepExists_right w_400 (Entails.sepExists_right w_408 (Entails.refl _))))))))

/-- Unpack the 48-byte `trustPollOutAt` (`Err(())`) at `sp + 0x3e0..0x410` into the subword cells
read by `p1_seg6a_any_wp`, preserving the read-only `storeHookStr` atom cleanly. -/
theorem trustOutErr_split_p1 (b sp : BitVec 64) :
    trustPollOutAt b (sp + 0x3e0#64) (.error ()) ⊢
      ∃∗ b_3e8 : BitVec 8, ∃∗ d_3e9 : BitVec 32, ∃∗ h_3ed : BitVec 16, ∃∗ b_3ef : BitVec 8,
      ∃∗ w_3f0 : BitVec 64, ∃∗ d_3f8 : BitVec 32, ∃∗ d_3fc : BitVec 32,
      ∃∗ w_400 : BitVec 64, ∃∗ w_408 : BitVec 64,
        ((sp + 0x3e0#64) ↦₆₄ 0x800000000000001a#64) ∗
        ((sp + 0x3e8#64) ↦₈ b_3e8) ∗
        ((sp + 0x3e9#64) ↦₃₂ d_3e9) ∗
        ((sp + 0x3ed#64) ↦₁₆ h_3ed) ∗
        ((sp + 0x3ef#64) ↦₈ b_3ef) ∗
        ((sp + 0x3f0#64) ↦₆₄ w_3f0) ∗
        ((sp + 0x3f8#64) ↦₃₂ d_3f8) ∗
        ((sp + 0x3fc#64) ↦₃₂ d_3fc) ∗
        ((sp + 0x400#64) ↦₆₄ w_400) ∗
        ((sp + 0x408#64) ↦₆₄ w_408) ∗
        ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr) := by
  let pStr : BitVec 64 := b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
  let pVt : BitVec 64 := b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)
  dsimp only [trustPollOutAt, errTailAt]
  change ((sp + 0x3e0#64) ↦₆₄ 0x800000000000001a#64) ∗
      (((sp + 0x3e0#64 + 8#64) ↦₆₄ pStr) ∗
        (((sp + 0x3e0#64 + 0x10#64) ↦₆₄ 10#64) ∗
          ((sp + 0x3e0#64 + 0x18#64) ↦₆₄ 1#64) ∗
          ((sp + 0x3e0#64 + 0x20#64) ↦₆₄ pVt) ∗
          (pStr ↦ᵣ storeHookStr)) ∗
        memRegion (sp + 0x3e0#64 + 0x28#64) 8) ⊢ _
  have h40 :
      (((sp + 0x3e0#64 + 8#64) ↦₆₄ pStr) ∗
        (((sp + 0x3e0#64 + 0x10#64) ↦₆₄ 10#64) ∗
          ((sp + 0x3e0#64 + 0x18#64) ↦₆₄ 1#64) ∗
          ((sp + 0x3e0#64 + 0x20#64) ↦₆₄ pVt) ∗
          (pStr ↦ᵣ storeHookStr)) ∗
        memRegion (sp + 0x3e0#64 + 0x28#64) 8) ⊢
      memRegion (sp + 0x3e8#64) 40 ∗ (pStr ↦ᵣ storeHookStr) := by
    rw [ProofLib.memRegion_split (sp + 0x3e8#64) 8 32 (by decide),
        ProofLib.memRegion_split (sp + 0x3e8#64 + 8#64) 8 24 (by decide),
        ProofLib.memRegion_split (sp + 0x3e8#64 + 8#64 + 8#64) 8 16 (by decide),
        ProofLib.memRegion_split (sp + 0x3e8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    have hcomm :
        ((sp + 1000#64) ↦₆₄ pStr) ∗ ((sp + 1008#64) ↦₆₄ 10#64) ∗
          ((sp + 1016#64) ↦₆₄ 1#64) ∗ ((sp + 1024#64) ↦₆₄ pVt) ∗
          (pStr ↦ᵣ storeHookStr) ∗ memRegion (sp + 1032#64) 8 =
        ((sp + 1000#64) ↦₆₄ pStr) ∗ ((sp + 1008#64) ↦₆₄ 10#64) ∗
          ((sp + 1016#64) ↦₆₄ 1#64) ∗ ((sp + 1024#64) ↦₆₄ pVt) ∗
          memRegion (sp + 1032#64) 8 ∗ (pStr ↦ᵣ storeHookStr) := by ac_rfl
    rw [hcomm]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))))
  refine Entails.trans (sepConj_mono_right h40) ?_
  rw [ProofLib.memRegion_split (sp + 0x3e8#64) 1 39 (by decide), ProofLib.memRegion_one]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro b_3e8
  refine Entails.sepExists_right b_3e8 ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
    (trustOut39_split_p1 sp)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro d_3e9
  apply Entails.sepExists_elim; intro h_3ed
  apply Entails.sepExists_elim; intro b_3ef
  apply Entails.sepExists_elim; intro w_3f0
  apply Entails.sepExists_elim; intro d_3f8
  apply Entails.sepExists_elim; intro d_3fc
  apply Entails.sepExists_elim; intro w_400
  apply Entails.sepExists_elim; intro w_408
  exact Entails.sepExists_right d_3e9 (Entails.sepExists_right h_3ed
    (Entails.sepExists_right b_3ef (Entails.sepExists_right w_3f0
      (Entails.sepExists_right d_3f8 (Entails.sepExists_right d_3fc
        (Entails.sepExists_right w_400 (Entails.sepExists_right w_408
          (Entails.of_eq (by ac_rfl)))))))))

/-! ## 3. Segment P1.3-Some (`+0x014c -> loadDropAddr` for `w_3e0 ≠ -3`) -/

set_option maxHeartbeats 1200000 in
/-- Segment P1.3-Some (`+0x014c -> +0x0234`, `loadDropAddr` on `Poll::Ready(Ok(Some(r)))`):
Reads `[sp + 0x3e0] = w_3e0` (`w_3e0 ≠ 0xfffffffffffffffd#64`), branches at `+0x0154` to `+0x01f4`,
copies the 36-byte header (`sp + 0x3f4..0x418 -> sp + 0x210..0x234`) and 312-byte tail
(`memcpy(sp + 0xd8, sp + 0x418, 312)`), keeping all copied atoms intact so `p1_load_some_seg4_wp`
can move the loaded `SessionRecord` into `coroPtr + 0xe0#64`. -/
theorem p1_load_some_seg3_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr loadFutPtr loadFutVt loadDropAddr
    w_3e0 w_3e8 w_3f4 w_3fc w_404 w_40c u0 u1 u2 u3 : BitVec 64)
    (d_3f0 d_414 du4 : BitVec 32) (bs312 : List (BitVec 8))
    (hw_ne_neg3 : w_3e0 ≠ 0xfffffffffffffffd#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x14c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs312 : bs312.length = 312)
    (hdrop_nz : loadDropAddr ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = s.sp + 0x3e0#64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (tripleRatchetProgAt b C ctl abs) loadDropAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ loadFutVt) ∗
       ((loadFutVt + 0x0#64) ↦₆₄ᵣ loadDropAddr) ∗
       memRegion (s.sp + 0xd8#64) 312 ∗
       ((s.sp + 0x210#64) ↦₆₄ u0) ∗ ((s.sp + 0x218#64) ↦₆₄ u1) ∗
       ((s.sp + 0x220#64) ↦₆₄ u2) ∗ ((s.sp + 0x228#64) ↦₆₄ u3) ∗
       ((s.sp + 0x230#64) ↦₃₂ du4) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ w_3e0) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ w_3e8) ∗
       ((s.sp + 0x3f0#64) ↦₃₂ d_3f0) ∗
       ((s.sp + 0x3f4#64) ↦₆₄ w_3f4) ∗
       ((s.sp + 0x3fc#64) ↦₆₄ w_3fc) ∗
       ((s.sp + 0x404#64) ↦₆₄ w_404) ∗
       ((s.sp + 0x40c#64) ↦₆₄ w_40c) ∗
       ((s.sp + 0x414#64) ↦₃₂ d_414) ∗
       ((s.sp + 0x418#64) ↦ₛ bs312))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ loadFutVt) ∗
          ((loadFutVt + 0x0#64) ↦₆₄ᵣ loadDropAddr) ∗
          ((s.sp + 0xd8#64) ↦ₛ bs312) ∗
          ((s.sp + 0x210#64) ↦₆₄ w_3f4) ∗ ((s.sp + 0x218#64) ↦₆₄ w_3fc) ∗
          ((s.sp + 0x220#64) ↦₆₄ w_404) ∗ ((s.sp + 0x228#64) ↦₆₄ w_40c) ∗
          ((s.sp + 0x230#64) ↦₃₂ d_414) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ w_3e0) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ w_3e8) ∗
          ((s.sp + 0x3f0#64) ↦₃₂ d_3f0) ∗
          ((s.sp + 0x3f4#64) ↦₆₄ w_3f4) ∗
          ((s.sp + 0x3fc#64) ↦₆₄ w_3fc) ∗
          ((s.sp + 0x404#64) ↦₆₄ w_404) ∗
          ((s.sp + 0x40c#64) ↦₆₄ w_40c) ∗
          ((s.sp + 0x414#64) ↦₃₂ d_414) ∗
          ((s.sp + 0x418#64) ↦ₛ bs312)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = loadFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = loadFutPtr ∧
        s1.readReg64 .x22 = d_3f0.zeroExtend 64 ∧
        s1.readReg64 .x23 = w_3e0 ∧
        s1.readReg64 .x24 = loadFutVt ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w_3e8 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x238#64) := by
  have hmemcpy := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_memcpy_ok
    (b := b) (C := C) (ctl := ctl) (abs := abs)
  have hcond := cond_ne_adds64_of_ne_neg3_std3 hw_ne_neg3
  have hcond' : (w_3e0 + 3#64 != 0#64) = true := bne_iff_ne.mpr (by bv_omega)
  have hdrop_beq : (loadDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  closure_fetches_range_cli b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x14c 0x154
  closure_fetches_range_cli b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x1f4 0x234
  dsimp only [tripleRatchetProgAt] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x3e0#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  wp_steps
  conv =>
    arg 4
    rw [show memRegion (s.sp + 0xd8#64) 312 =
      memRegion (s.sp + 0xd8#64) bs312.length by rw [hbs312]]
  wp_call hmemcpy (s.sp + 0xd8#64, s.sp + 0x418#64, bs312)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-! ## 4. Segment P1.4-Some (`+0x0238 -> trustShimAddr` for `Poll::Ready(Ok(Some(r)))`) -/

set_option maxHeartbeats 1600000 in
/-- Segment P1.4-Some (`+0x0238 -> +0x064c`, `trustShimAddr` on `Poll::Ready(Ok(Some(r)))`):
Deallocates `loadFutPtr` (`__rust_dealloc`), takes the `Some(r)` path (`x23 ≠ -2` and `x23 ≠ -1`,
`+0x0250 -> +0x04c0 -> +0x04cc..+0x04f8 -> +0x0588..+0x064c`), copies the 36-byte header from
`sp + 0x210..0x234` and 312-byte tail via `memcpy(coroPtr + 0x118, sp + 0xd8, 312)` and writes
`[coroPtr + 0xe0..0xf0] = (w_3e0, w_3e8)`, initializes `processPrekeyInnerInitAt`, and executes
`blr x8` (`trustShimAddr`) at `+0x064c`. -/
theorem p1_load_some_seg4_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr loadFutPtr loadFutVt trustShimAddr
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    w_3e0 w_3e8 v_210 v_218 v_220 v_228
    c0 c1 c_f4 c_fc c_104 c_10c : BitVec 64)
    (d_3f0 dv_230 c_f0 c_114 : BitVec 32)
    (bs312 : List (BitVec 8))
    (loadBoxSize : Nat) (b_390 : BitVec 8)
    (hw_ne_neg2 : w_3e0 ≠ 0xfffffffffffffffe#64)
    (hw_ne_neg1 : w_3e0 ≠ 0xffffffffffffffff#64)
    (hbs312 : bs312.length = 312)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x238#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs_nz : BitVec.ofNat 64 loadBoxSize ≠ 0#64)
    (hbs_lt : loadBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = loadFutPtr)
    (hx22 : s.readReg64 .x22 = d_3f0.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = w_3e0)
    (hx24 : s.readReg64 .x24 = loadFutVt)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = w_3e8) :
    SepWP (tripleRatchetProgAt b C ctl abs) trustShimAddr s
      (((loadFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 loadBoxSize) ∗
       ((loadFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live loadFutPtr loadBoxSize 8 ∗
       memRegion loadFutPtr loadBoxSize ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr sessStoreVt idStorePtr idStoreVt
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr ∗
       ((coroPtr + 0xe0#64) ↦₆₄ c0) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ c1) ∗
       ((coroPtr + 0xf0#64) ↦₃₂ c_f0) ∗
       ((coroPtr + 0xf4#64) ↦₆₄ c_f4) ∗
       ((coroPtr + 0xfc#64) ↦₆₄ c_fc) ∗
       ((coroPtr + 0x104#64) ↦₆₄ c_104) ∗
       ((coroPtr + 0x10c#64) ↦₆₄ c_10c) ∗
       ((coroPtr + 0x114#64) ↦₃₂ c_114) ∗
       memRegion (coroPtr + 0x118#64) 312 ∗
       ((s.sp + 0xd8#64) ↦ₛ bs312) ∗
       ((s.sp + 0x210#64) ↦₆₄ v_210) ∗
       ((s.sp + 0x218#64) ↦₆₄ v_218) ∗
       ((s.sp + 0x220#64) ↦₆₄ v_220) ∗
       ((s.sp + 0x228#64) ↦₆₄ v_228) ∗
       ((s.sp + 0x230#64) ↦₃₂ dv_230) ∗
       cells (coroPtr + 0x2c8#64) 25 ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((idStoreVt + 0x30#64) ↦₆₄ᵣ trustShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((loadFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 loadBoxSize) ∗
          ((loadFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr sessStoreVt idStorePtr idStoreVt
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr ∗
          ((coroPtr + 0xe0#64) ↦₆₄ w_3e0) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ w_3e8) ∗
          ((coroPtr + 0xf0#64) ↦₃₂ d_3f0) ∗
          ((coroPtr + 0xf4#64) ↦₆₄ v_210) ∗
          ((coroPtr + 0xfc#64) ↦₆₄ v_218) ∗
          ((coroPtr + 0x104#64) ↦₆₄ v_220) ∗
          ((coroPtr + 0x10c#64) ↦₆₄ v_228) ∗
          ((coroPtr + 0x114#64) ↦₃₂ dv_230) ∗
          ((coroPtr + 0x118#64) ↦ₛ bs312) ∗
          ((s.sp + 0xd8#64) ↦ₛ bs312) ∗
          ((s.sp + 0x210#64) ↦₆₄ v_210) ∗
          ((s.sp + 0x218#64) ↦₆₄ v_218) ∗
          ((s.sp + 0x220#64) ↦₆₄ v_220) ∗
          ((s.sp + 0x228#64) ↦₆₄ v_228) ∗
          ((s.sp + 0x230#64) ↦₃₂ dv_230) ∗
          processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
          ((idStoreVt + 0x30#64) ↦₆₄ᵣ trustShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idStorePtr ∧
        s1.readReg64 .x1 = remoteAddrPtr ∧
        s1.readReg64 .x2 = msgPtr + 0xc8#64 ∧
        s1.readReg64 .x3 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = coroPtr + 0x390#64 ∧
        s1.readReg64 .x23 = w_3e0 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w_3e8 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x650#64) := by
  have hdealloc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok
    (b := b) (C := C) (ctl := ctl) (abs := abs) hA
  have hmemcpy := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_memcpy_ok
    (b := b) (C := C) (ctl := ctl) (abs := abs)
  have hcond_neg2 := cond_ne_adds64_of_ne_neg2_std3 hw_ne_neg2
  have hcond_neg1 := cond_eq_adds64_of_ne_neg1_std3 hw_ne_neg1
  have hcond_neg2' : (w_3e0 + 2#64 != 0#64) = true := bne_iff_ne.mpr (by bv_omega)
  have hcond_neg1' : (w_3e0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr (by bv_omega)
  have hbs_beq : (BitVec.ofNat 64 loadBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 loadBoxSize).toNat = loadBoxSize := Nat.mod_eq_of_lt hbs_lt
  closure_fetches_range_cli b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x238 0x250
  closure_fetches_range_cli b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x4c0 0x4f8
  closure_fetches_range_cli b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x588 0x64c
  dsimp only [tripleRatchetProgAt] at hdealloc hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = loadFutPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = d_3f0.zeroExtend 64 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = w_3e0 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = loadFutVt := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx28' : s.readReg64 (Reg.gpr 28#5) = w_3e8 := hx28
  dsimp only [decryptPrekeyCoroCopyAt]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      cells, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps
  wp_call hdealloc (loadFutPtr, loadBoxSize, 8)
  wp_steps
  conv =>
    arg 4
    rw [show memRegion (coroPtr + 0x118#64) 312 =
      memRegion (coroPtr + 0x118#64) bs312.length by rw [hbs312]]
  wp_call hmemcpy (coroPtr + 0x118#64, s.sp + 0xd8#64, bs312)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  dsimp only [decryptPrekeyCoroCopyAt, processPrekeyInnerInitAt]
  exact Entails.of_eq (by ac_rfl)

/-! ## 5. Segment P1.6a-Any (`+0x066c -> trustDropAddr`) & Dealloc (`+0x06d0 -> +0x06e4`) -/

set_option maxHeartbeats 1200000 in
/-- Segment P1.6a-Any (`+0x066c -> trustDropAddr` for any `Poll::Ready(ans)`):
Reads `[sp + 0x3e0] = w_3e0` (`w_3e0 ≠ 0xfffffffffffffffd#64`) and `[sp + 0x3e8] = b_3e8`, spills
`outPtr` to `[sp + 0xc8]` and `coroPtr + 0x390` to `[sp + 0xb0]`, folds `sp + 0x3e0..0x410` back
to `memRegion (s.sp + 0x3e0#64) 48`, and calls `trustDropAddr` at `+0x06cc`. -/
theorem p1_seg6a_any_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr outPtr trustFutPtr trustFutVt trustDropAddr
    w_3e0 w_3f0 w_400 w_408 u_a8 u_b0 u_b8 u_c8 u_d0 : BitVec 64)
    (d_3e9 d_3f8 d_3fc : BitVec 32) (h_3ed : BitVec 16) (b_3e8 b_3ef : BitVec 8)
    (hw_ne_neg3 : w_3e0 ≠ 0xfffffffffffffffd#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x66c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hdrop_nz : trustDropAddr ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = coroPtr + 0x390#64)
    (hx26 : s.readReg64 .x26 = outPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) trustDropAddr s
      (((coroPtr + 0x398#64) ↦₆₄ trustFutPtr) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ trustFutVt) ∗
       ((trustFutVt + 0x0#64) ↦₆₄ᵣ trustDropAddr) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ w_3e0) ∗
       ((s.sp + 0x3e8#64) ↦₈ b_3e8) ∗
       ((s.sp + 0x3e9#64) ↦₃₂ d_3e9) ∗
       ((s.sp + 0x3ed#64) ↦₁₆ h_3ed) ∗
       ((s.sp + 0x3ef#64) ↦₈ b_3ef) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ w_3f0) ∗
       ((s.sp + 0x3f8#64) ↦₃₂ d_3f8) ∗
       ((s.sp + 0x3fc#64) ↦₃₂ d_3fc) ∗
       ((s.sp + 0x400#64) ↦₆₄ w_400) ∗
       ((s.sp + 0x408#64) ↦₆₄ w_408))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x398#64) ↦₆₄ trustFutPtr) ∗
          ((coroPtr + 0x3a0#64) ↦₆₄ trustFutVt) ∗
          ((trustFutVt + 0x0#64) ↦₆₄ᵣ trustDropAddr) ∗
          ((s.sp + 0xa8#64) ↦₆₄ d_3fc.zeroExtend 64) ∗
          ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w_3f0) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ d_3f8.zeroExtend 64) ∗
          memRegion (s.sp + 0x3e0#64) 48) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = trustFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = w_3e0 ∧
        s1.readReg64 .x21 = trustFutPtr ∧
        s1.readReg64 .x23 = b_3e8.zeroExtend 64 ∧
        s1.readReg64 .x25 = trustFutVt ∧
        s1.readReg64 .x27 = w_408 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6d0#64) := by
  have hcond := cond_ne_adds64_of_ne_neg3_std3 hw_ne_neg3
  have hcond' : (w_3e0 + 3#64 != 0#64) = true := bne_iff_ne.mpr (by bv_omega)
  have hdrop_beq : (trustDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  closure_fetches_range_cli b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x66c 0x674
  closure_fetches_range_cli b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x680 0x6cc
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = coroPtr + 0x390#64 := hx21
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  wp_steps
  apply SepWP.fold
    (trustOut48_fold_p1 s.sp w_3e0 b_3e8 d_3e9 h_3ed b_3ef w_3f0 d_3f8 d_3fc
      w_400 w_408)
    (by sep_focus)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1200000 in
/-- Segment P1.6-Dealloc (`+0x06d0 -> +0x06e4`):
Deallocates `trustFutPtr` (`__rust_dealloc(trustFutPtr, trustBoxSize, 8)`), stopping at the
post-dealloc branch point `entry + 0x6e4#64` with `x19, x20, x23, x27, x29` intact. -/
theorem p1_seg6_dealloc_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr trustFutPtr trustFutVt w_20 w_23 : BitVec 64)
    (trustBoxSize : Nat)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6d0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs_nz : BitVec.ofNat 64 trustBoxSize ≠ 0#64)
    (hbs_lt : trustBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = w_20)
    (hx21 : s.readReg64 .x21 = trustFutPtr)
    (hx23 : s.readReg64 .x23 = w_23)
    (hx25 : s.readReg64 .x25 = trustFutVt) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6e4#64) s
      (((trustFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 trustBoxSize) ∗
       ((trustFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live trustFutPtr trustBoxSize 8 ∗
       memRegion trustFutPtr trustBoxSize ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((trustFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 trustBoxSize) ∗
          ((trustFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = w_20 ∧
        s1.readReg64 .x23 = w_23 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hdealloc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok
    (b := b) (C := C) (ctl := ctl) (abs := abs) hA
  have hbs_beq : (BitVec.ofNat 64 trustBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 trustBoxSize).toNat = trustBoxSize := Nat.mod_eq_of_lt hbs_lt
  closure_fetches_range_cli b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x6d0 0x6e0
  dsimp only [tripleRatchetProgAt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = w_20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = trustFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = w_23 := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = trustFutVt := hx25
  wp_steps
  wp_call hdealloc (trustFutPtr, trustBoxSize, 8)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-! ## 6. Post-Dealloc Trusted Continuation (`+0x06e4 -> +0x0868` for `trusted == true`) -/

set_option maxHeartbeats 1200000 in
/-- Segment P1.PostDealloc-True (`+0x06e4 -> +0x0868`):
From the post-dealloc branch point `entry + 0x6e4#64` with `x20 = 0xfffffffffffffffe#64` and
`x23 = 1#64` (`trusted == true`), populates `processPrekeyPostTrustAt`, `[coroPtr + 0x4f2] = 0#8`,
`[s.sp + 0x98] = coroPtr + 0x398#64`, `[s.sp + 0xa0] = coroPtr + 0x4f2#64`, and jumps to
`entry + 0x868#64`. -/
theorem p1_post_dealloc_true_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr
    msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
    u_98 u_a0 : BitVec 64)
    (b_4f2 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6e4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx23 : s.readReg64 .x23 = 1#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x868#64) s
      (processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
         spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
       cells (coroPtr + 0x428#64) 8 ∗
       cells (coroPtr + 0x490#64) 4 ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0))
      (fun s1 P_f =>
        (P_f ⊢
          processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
          processPrekeyPostTrustAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x4f2#64) ↦₈ 0#8) ∗
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64))) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x8 = kyberStorePtr ∧
        s1.readReg64 .x9 = msgPtr ∧
        s1.readReg64 .x10 = kyberStoreVt ∧
        s1.readReg64 .x11 = preKeyStorePtr ∧
        s1.readReg64 .x12 = remoteAddrPtr ∧
        s1.readReg64 .x13 = preKeyStoreVt ∧
        s1.readReg64 .x14 = localAddrPtr ∧
        s1.readReg64 .x15 = idStorePtr ∧
        s1.readReg64 .x16 = idStoreVt ∧
        s1.readReg64 .x17 = coroPtr + 0x4f2#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  closure_fetches_range_cli b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x6e4 0x76c
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = 0xfffffffffffffffe#64 := hx20
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  dsimp only [processPrekeyInnerInitAt]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      cells, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  dsimp only [processPrekeyInnerInitAt, processPrekeyPostTrustAt]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
