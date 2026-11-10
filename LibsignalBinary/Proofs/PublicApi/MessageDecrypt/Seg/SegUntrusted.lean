/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.StringCloneFlat
import LibsignalBinary.Proofs.Common.StringClonePlaced
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegSaveAux
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts

/-!
# `MessageDecrypt` Untrusted-Identity Segment (`SegUntrusted`)

Verifies the `untrusted_identity` error-construction segment (`+0x21b0 → +0x2294`) of
`session_message_decrypt_signal_with_stores` and its relocatable `[LibsignalPlacement]` counterpart.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Instruction Decode Lemmas (`+0x21b0..+0x21c0` and `+0x2250..+0x2294`) -/

gen_decodes libsignalSessionCode_tree segUntrustedBin [0x3c73c → 0x3c748, 0x3c7dc → 0x3c81c]

/-! ## 2. Address, Repack, and Callee Helpers -/

theorem adrp_logFlag_21b0_eq {b entry : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64) (he : entry = b + 238988#64) :
    ((entry + 8624#64) &&& 18446744073709547520#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - 0x3c000) = b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) := by
  subst he
  rw [BitVec.add_assoc,
    show (18446744073709547520#64 : BitVec 64) = 0xfffffffffffff000#64 from rfl,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb,
    show (238988#64 + 8624#64 : BitVec 64) &&& 0xfffffffffffff000#64 = 245760#64 by decide]
  bv_omega

theorem stringClone_tripleRatchetExterns (C : Crypto) (ctl : BitVec 64)
    (A : RustAlloc) (abs : String → Option (State → State))
    (hSC : HookSat abs stringCloneHookName (stringCloneSpec A)) :
    HookSat (Rust.withPanics (tripleRatchetExterns C ctl abs)) stringCloneHookName (stringCloneSpec A) := by
  have habs := tripleRatchetExterns_stores_abs C ctl abs
  have h6 : Rust.withPanics (tripleRatchetExterns C ctl abs) stringCloneHookName =
      abs stringCloneHookName := Option.some.inj (congrArg (·[6]?) habs)
  simpa [HookSat, h6] using hSC

theorem stringClone_ok_at_dec {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff stringCloneHookName := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (stringCloneSpec A) := by
  have haddr :
      (tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k =
      (tripleRatchetProgAt b C ctl abs).fnAddr stringCloneHookName := by
    simp only [tripleRatchetProgAt, Program.fnAddr_rebase, BitVec.add_assoc,
      ← BitVec.ofNat_add, hk]
  rw [haddr]
  exact LibsignalBinary.Proofs.Common.StringCloneFlat.stringClone_tripleRatchetProgAt_ok b C A ctl abs hA

def vecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8_unpack_5f0 (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A (sp + 1520#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((sp + 1520#64) ↦₃₂ cap.extractLsb' 0 32) ∗
        ((sp + 1524#64) ↦₃₂ cap.extractLsb' 32 32) ∗
        ((sp + 1528#64) ↦₆₄ ptr) ∗
        ((sp + 1536#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap ptr bs := by
  unfold vecU8 vecU8At vecHeader vecU8Buf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [pointsTo64_split32 (sp + 1520#64) cap]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

theorem pointsTo64_of_cons_unpack64 (q : BitVec 64) (b0 : BitVec 8) (pad : List (BitVec 8))
    (w4 : BitVec 64) (hw4 : b0 :: pad = unpack64 w4) :
    ((q ↦₈ b0) ∗ ((q + 1#64) ↦ₛ pad)) = (q ↦₆₄ w4) := by
  rw [pointsTo64_eq_pointsToBytes, ← hw4, pointsToBytes_cons]

theorem repack_5f4_for_q0 (sp cap ptr len : BitVec 64) :
    ((sp + 1524#64) ↦₃₂ cap.extractLsb' 32 32) ∗
      ((sp + 1528#64) ↦₆₄ ptr) ∗ ((sp + 1536#64) ↦₆₄ len) =
    ((sp + 1524#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
      ((sp + 1532#64) ↦₆₄ (len.extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
      ((sp + 1540#64) ↦₃₂ len.extractLsb' 32 32) := by
  simp only [pointsTo64_append32]
  rw [pointsTo64_split32 (sp + 1528#64) ptr, pointsTo64_split32 (sp + 1536#64) len]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem repack_5f4_for_q1 (sp cap ptr len : BitVec 64) (dev : BitVec 8) (pad : List (BitVec 8))
    (devWord : BitVec 64) (hw4 : dev :: pad = unpack64 devWord) :
    ((sp + 1524#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
      ((sp + 1532#64) ↦₆₄ (len.extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
      ((sp + 1540#64) ↦₃₂ len.extractLsb' 32 32) ∗
      ((sp + 1544#64) ↦₈ dev) ∗ ((sp + 1545#64) ↦ₛ pad) =
    ((sp + 1524#64) ↦₃₂ cap.extractLsb' 32 32) ∗
      ((sp + 1528#64) ↦₆₄ ptr) ∗ ((sp + 1536#64) ↦₆₄ len) ∗
      ((sp + 1544#64) ↦₆₄ devWord) := by
  have hdev := pointsTo64_of_cons_unpack64 (sp + 1544#64) dev pad devWord hw4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hdev
  rw [hdev, pointsTo64_append32, pointsTo64_append32,
      pointsTo64_split32 (sp + 1528#64) ptr, pointsTo64_split32 (sp + 1536#64) len]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem repack_588_for_q1 (sp ptr len : BitVec 64) (e2 : BitVec 32) :
    ((sp + 1416#64) ↦₆₄ (len.extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
      ((sp + 1424#64) ↦₃₂ e2) =
    ((sp + 1416#64) ↦₃₂ ptr.extractLsb' 32 32) ∗
      ((sp + 1420#64) ↦₆₄ (e2 ++ len.extractLsb' 0 32)) := by
  simp only [pointsTo64_append32, BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem repack_580_after_q1 (sp cap ptr : BitVec 64) :
    ((sp + 1408#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
      ((sp + 1416#64) ↦₃₂ ptr.extractLsb' 32 32) =
    ((sp + 1408#64) ↦₃₂ cap.extractLsb' 32 32) ∗
      ((sp + 1412#64) ↦₆₄ ptr) := by
  rw [pointsTo64_append32, pointsTo64_split32 (sp + 1412#64) ptr]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

/-! ## 3. Core `SepWPp` for `segUntrusted` (`+0x21b0 → +0x2294`) -/

set_option maxHeartbeats 800000 in
theorem segUntrusted_wp {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (hb : b &&& 0xfff#64 = 0#64)
    {s : State} {R : SepProp}
    {addrA e0 e1 e3 devWord : BitVec 64} {e2 : BitVec 32} {d0 : BitVec 8} {pad : List (BitVec 8)}
    {addr : AddrGhost}
    (hw4 : addr.device :: pad = unpack64 devWord)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + 0x21b0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + 0x2294#64) s
      (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗
        vecGhostAt A addr.name addrA ∗
        ((addrA + 0x18#64) ↦₈ addr.device) ∗
        memRegion (s.sp + 0x5f0#64) 24 ∗
        ((s.sp + 0x608#64) ↦₈ d0) ∗ ((s.sp + 0x609#64) ↦ₛ pad) ∗
        ((s.sp + 0x580#64) ↦₆₄ e0) ∗ ((s.sp + 0x588#64) ↦₆₄ e1) ∗
        ((s.sp + 0x590#64) ↦₃₂ e2) ∗ ((s.sp + 0x594#64) ↦₆₄ e3) ∗
        A.pool ∗ stackAt s.sp extHookStack)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
          ⌜sf.readReg64 .x28 = 0x800000000000000c#64 ∧
            sf.readReg64 .x20 = ((cap.extractLsb' 0 32) >>> 8#32).zeroExtend 64 ∧
            sf.readReg64 .x21 = (cap.extractLsb' 0 32).zeroExtend 64 ∧
            sf.trace = s.trace⌝ ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗
          vecGhostAt A addr.name addrA ∗
          ((addrA + 0x18#64) ↦₈ addr.device) ∗
          ((s.sp + 0x5f0#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((s.sp + 0x5f4#64) ↦₃₂ cap.extractLsb' 32 32) ∗
          ((s.sp + 0x5f8#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x600#64) ↦₆₄ BitVec.ofNat 64 addr.name.bytes.length) ∗
          ((s.sp + 0x608#64) ↦₆₄ devWord) ∗
          ((s.sp + 0x580#64) ↦₃₂ cap.extractLsb' 32 32) ∗
          ((s.sp + 0x584#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x58c#64) ↦₆₄ BitVec.ofNat 64 addr.name.bytes.length) ∗
          ((s.sp + 0x594#64) ↦₆₄ devWord) ∗
          vecU8Buf A cap ptr addr.name.bytes ∗
          A.pool ∗ stackAt s.sp extHookStack) ∗ R) ∧
        sf.sp = s.sp ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff decWithStoresName = 0x3a58c := by
    simp only [decWithStoresName, arm64_norm]
  have hclone := stringClone_ok_at_dec (b := b) (C := C) (ctl := ctl)
    (name := decWithStoresName) (k := num% (ls_off% "<alloc::string::String as core::clone::Clone>::clone" - 0x3a58c)) hA
  have hadp_log :
      (((tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + 8624#64) &&&
        18446744073709547520#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - 0x3c000) = b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) :=
    adrp_logFlag_21b0_eq hb (by rw [tripleRatchetProgAt, Program.fnAddr_rebase, hfn])
  code_fetches_range CryptoVerification.libsignalSessionCode segUntrustedBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x3a58c 0x21b0 0x10
  code_fetches_range CryptoVerification.libsignalSessionCode segUntrustedBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x3a58c 0x2250 0x44
  dsimp only [tripleRatchetProgAt] at hpc hclone hadp_log ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr decWithStoresName = entry at *
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<alloc::string::String as core::clone::Clone>::clone" - 0x3a58c))
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  messageDecrypt_call_panic hclone (addrA, s.sp + 1520#64, addr.name)
  apply SepWP.fold (vecU8_unpack_5f0 A s.sp addr.name.bytes) (by sep_focus)
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro (cap : BitVec 64)
  apply SepWP.exists_elim; intro (ptr : BitVec 64)
  wp_steps 5
  apply SepWP.fold
    (Entails.of_eq (repack_5f4_for_q0 s.sp cap ptr (BitVec.ofNat 64 addr.name.bytes.length)))
    (by sep_focus)
  wp_step
  apply SepWP.fold
    (Entails.of_eq (repack_5f4_for_q1 s.sp cap ptr (BitVec.ofNat 64 addr.name.bytes.length) addr.device pad devWord hw4))
    (by sep_focus)
  wp_steps 3
  apply SepWP.fold
    (Entails.of_eq (repack_588_for_q1 s.sp ptr (BitVec.ofNat 64 addr.name.bytes.length) e2))
    (by sep_focus)
  wp_steps 4
  apply SepWP.fold
    (Entails.of_eq (repack_580_after_q1 s.sp cap ptr))
    (by sep_focus)
  wp_done

/-! ## 4. Session-API Model & `StagedRes` Lemmas for `untrustedIdentity` -/

theorem model_of_trust_false (C : Crypto) (S : SpqrModel) (x : DecryptGhost)
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (rec rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8))
    (ses : Session (List (BitVec 8))) (k : IdentityKey)
    (hload : ans.loadSession = .ok (some rec))
    (_hscope : RecordInScope rec)
    (hdec : decryptRecord C S uuidTryParse x rec = .ok (pt, rec'))
    (hcur : rec'.currentSession = some ses)
    (hik : ses.state.remoteIdentity = some k)
    (htrust : ans.isTrustedIdentity = .ok false) :
    (x.model C S uuidTryParse ans).1 = .error (.untrustedIdentity x.rem.val) ∧
      (x.model C S uuidTryParse ans).2 =
        [.loadSession x.rem.val,
          .isTrustedIdentity x.rem.val k .receiving] := by
  have h : x.model C S uuidTryParse ans =
      (.error (.untrustedIdentity x.rem.val),
        [.loadSession x.rem.val,
          .isTrustedIdentity x.rem.val k .receiving]) := by
    unfold DecryptGhost.model
    unfold decryptRecord at hdec
    rw [messageDecryptSignal_eq_flat]
    simp [decryptFlat, hload, hdec, hcur, hik, htrust]
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

def bytes36_untrusted (c_hi : BitVec 32) (ptr len devWord e4 : BitVec 64) : List (BitVec 8) :=
  unpack32 c_hi ++ (unpack64 ptr ++ (unpack64 len ++ (unpack64 devWord ++ unpack64 e4)))

theorem bytes36_untrusted_length (c_hi : BitVec 32) (ptr len devWord e4 : BitVec 64) :
    (bytes36_untrusted c_hi ptr len devWord e4).length = 36 := by
  simp only [bytes36_untrusted, List.length_append, unpack32_length, unpack64_length]

theorem words36_untrusted_eq_pointsToBytes (a : BitVec 64) (c_hi : BitVec 32)
    (ptr len devWord e4 : BitVec 64) :
    ((a ↦₃₂ c_hi) ∗ ((a + 4#64) ↦₆₄ ptr) ∗ ((a + 12#64) ↦₆₄ len) ∗
      ((a + 20#64) ↦₆₄ devWord) ∗ ((a + 28#64) ↦₆₄ e4)) =
    (a ↦ₛ bytes36_untrusted c_hi ptr len devWord e4) := by
  unfold bytes36_untrusted
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [unpack32_length, unpack64_length, BitVec.add_assoc, BitVec.reduceAdd,
    ← pointsTo32_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]

theorem vecU8_intro (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs) ⊢ vecU8 A v bs := by
  unfold vecU8 vecU8At vecHeader vecU8Buf
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.of_eq (by ac_rfl)

theorem pointsTo64_entails_byte_memRegion7 (q : BitVec 64) (b0 : BitVec 8) (pad : List (BitVec 8))
    (w4 : BitVec 64) (hpad : pad.length = 7) (hw4 : b0 :: pad = unpack64 w4) :
    (q ↦₆₄ w4) ⊢ (q ↦₈ b0) ∗ memRegion (q + 1#64) 7 := by
  rw [← pointsTo64_of_cons_unpack64 q b0 pad w4 hw4]
  apply sepConj_mono_right
  have h := pointsToBytes_entails_memRegion (q + 1#64) pad
  rwa [hpad] at h

theorem stagedRes_untrusted_intro (A : RustAlloc) (x28 w20 w21 src cap ptr devWord e4 : BitVec 64)
    (addr : AddrGhost) (pad : List (BitVec 8))
    (hpad : pad.length = 7) (hw4 : addr.device :: pad = unpack64 devWord)
    (hx28 : x28 = 0x800000000000000c#64)
    (hw1 : resWord1 w20 w21 = cap.extractLsb' 0 32) :
    (((src ↦₃₂ cap.extractLsb' 32 32) ∗ ((src + 4#64) ↦₆₄ ptr) ∗
      ((src + 12#64) ↦₆₄ BitVec.ofNat 64 addr.name.bytes.length) ∗
      ((src + 20#64) ↦₆₄ devWord) ∗ ((src + 28#64) ↦₆₄ e4)) ∗
      vecU8Buf A cap ptr addr.name.bytes) ⊢
      StagedRes A x28 w20 w21 src (.error (.untrustedIdentity addr.val)) := by
  rw [words36_untrusted_eq_pointsToBytes]
  unfold StagedRes
  refine Entails.sepExists_right
    (bytes36_untrusted (cap.extractLsb' 32 32) ptr
      (BitVec.ofNat 64 addr.name.bytes.length) devWord e4) ?_
  refine Entails.sepExists_right (vecU8Buf A cap ptr addr.name.bytes) ?_
  refine Entails.pure_right
    ⟨bytes36_untrusted_length (cap.extractLsb' 32 32) ptr
      (BitVec.ofNat 64 addr.name.bytes.length) devWord e4, fun r => ?_⟩
    (Entails.refl _)
  rw [hx28, hw1, ← words36_untrusted_eq_pointsToBytes]
  have hcap := (pointsTo64_split32 (r + 8#64) cap).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hcap ⊢
  have hgrp :
      ((r ↦₆₄ 0x800000000000000c#64) ∗ ((r + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
        (((r + 12#64) ↦₃₂ cap.extractLsb' 32 32) ∗ ((r + 16#64) ↦₆₄ ptr) ∗
          ((r + 24#64) ↦₆₄ BitVec.ofNat 64 addr.name.bytes.length) ∗
          ((r + 32#64) ↦₆₄ devWord) ∗ ((r + 40#64) ↦₆₄ e4)) ∗
        vecU8Buf A cap ptr addr.name.bytes) =
      ((r ↦₆₄ 0x800000000000000c#64) ∗
        ((((r + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗ ((r + 12#64) ↦₃₂ cap.extractLsb' 32 32)) ∗
          ((r + 16#64) ↦₆₄ ptr) ∗
          ((r + 24#64) ↦₆₄ BitVec.ofNat 64 addr.name.bytes.length) ∗
          vecU8Buf A cap ptr addr.name.bytes) ∗
        ((r + 32#64) ↦₆₄ devWord) ∗ ((r + 40#64) ↦₆₄ e4)) := by ac_rfl
  rw [hgrp, hcap]
  unfold apiDecResultAt apiErrAt addrCloneAt AddrGhost.val
  have htag : (0x800000000000000c#64 : BitVec 64) = speWord speUntrustedIdentity := rfl
  rw [htag]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hvec := vecU8_intro A (r + 8#64) cap ptr addr.name.bytes
  have hdev := pointsTo64_entails_byte_memRegion7 (r + 32#64) addr.device pad devWord hpad hw4
  have he4 := pointsTo64_entails_memRegion (r + 40#64) e4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hvec hdev
  rw [sepConj_assoc (vecU8 A (r + 8#64) _)]
  exact sepConj_mono_right (sepConj_mono hvec (sepConj_mono hdev he4))

/-! ## 5. Frame Split / Join & `segUntrusted_ok` -/

@[irreducible] def wsExtStackRest (sp : BitVec 64) : SepProp :=
  memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - extHookStack)

theorem stack_wsCallee_extHook (sp : BitVec 64) :
    stackAt sp wsCalleeStack =
      wsExtStackRest sp ∗ stackAt sp extHookStack := by
  unfold wsExtStackRest
  have h := stackAt_split_bottom sp extHookStack
    (wsCalleeStack - extHookStack) (by decide)
  rwa [show extHookStack + (wsCalleeStack - extHookStack) = wsCalleeStack
    by decide] at h

theorem memRegion_48_untrusted_entails (a : BitVec 64) :
    memRegion a 48 ⊢
      ∃∗ d0 : BitVec 8, ∃∗ pad : List (BitVec 8),
        ⌜pad.length = 7⌝ ∗
        memRegion a 24 ∗ ((a + 24#64) ↦₈ d0) ∗ ((a + 25#64) ↦ₛ pad) ∗
        memRegion (a + 32#64) 16 := by
  rw [memRegion_split a 24 24 (by decide),
    memRegion_split (a + 24#64) 1 23 (by decide),
    memRegion_split (a + 24#64 + 1#64) 7 16 (by decide),
    ProofLib.memRegion_one,
    memRegion_eq_exists_bytes (a + 24#64 + 1#64) 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro pad
  apply Entails.sepExists_elim; intro d0
  refine Entails.sepExists_right d0 (Entails.sepExists_right pad ?_)
  exact Entails.of_eq (by ac_rfl)

theorem cells_48_untrusted_entails_memRegion (a : BitVec 64) (c_lo c_hi : BitVec 32)
    (ptr len devWord : BitVec 64) :
    ((a ↦₃₂ c_lo) ∗ ((a + 4#64) ↦₃₂ c_hi) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
      ((a + 16#64) ↦₆₄ len) ∗ ((a + 24#64) ↦₆₄ devWord) ∗
      memRegion (a + 32#64) 16) ⊢ memRegion a 48 := by
  rw [memRegion_split a 4 44 (by decide),
    memRegion_split (a + 4#64) 4 40 (by decide),
    memRegion_split (a + 4#64 + 4#64) 8 32 (by decide),
    memRegion_split (a + 4#64 + 4#64 + 8#64) 8 24 (by decide),
    memRegion_split (a + 4#64 + 4#64 + 8#64 + 8#64) 8 16 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo32_entails_memRegion a c_lo)
    (sepConj_mono (pointsTo32_entails_memRegion (a + 4#64) c_hi)
      (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) ptr)
        (sepConj_mono (pointsTo64_entails_memRegion (a + 16#64) len)
          (sepConj_mono (pointsTo64_entails_memRegion (a + 24#64) devWord)
            (Entails.refl _)))))

theorem memRegion_36_untrusted_entails (a : BitVec 64) :
    memRegion a 0x24 ⊢
      ∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 32,
      ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64,
        (a ↦₆₄ e0) ∗ ((a + 8#64) ↦₆₄ e1) ∗ ((a + 16#64) ↦₃₂ e2) ∗
        ((a + 20#64) ↦₆₄ e3) ∗ ((a + 28#64) ↦₆₄ e4) := by
  rw [memRegion_split a 8 28 (by decide),
    memRegion_split (a + 8#64) 8 20 (by decide),
    memRegion_split (a + 8#64 + 8#64) 4 16 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 4#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_four,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro e4
  apply Entails.sepExists_elim; intro e3
  apply Entails.sepExists_elim; intro e2
  apply Entails.sepExists_elim; intro e1
  apply Entails.sepExists_elim; intro e0
  exact Entails.sepExists_right e0 (Entails.sepExists_right e1
    (Entails.sepExists_right e2 (Entails.sepExists_right e3
      (Entails.sepExists_right e4 (Entails.refl _)))))

def wsUntrustedFixedEnv (A : RustAlloc) (img : Obj.Image) (x : DecryptGhost)
    (sp : BitVec 64) : SepProp :=
  ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗
  vecGhostAt A x.rem.name x.remA ∗
  ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
  A.pool ∗ stackAt sp extHookStack

def wsUntrustedFixedRest (A : RustAlloc) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) : SepProp :=
  wsSavedRegs s0.sp s0 ∗
  ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
  ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
  ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
  ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
  ((sp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64)) ∗
  decVtablesAtV kit ikit ∗
  memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
  memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
  memRegion (x.remA + 0x19#64) 7 ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.loc x.locA ∗
  wsExtStackRest sp

theorem logOff_eq (img : Obj.Image) :
    logOff img = ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) := rfl

theorem protocolAddressAt_eq (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) :
    protocolAddressAt A g a =
      vecGhostAt A g.name a ∗ ((a + 0x18#64) ↦₈ g.device) ∗ memRegion (a + 0x19#64) 7 := rfl

attribute [local irreducible] protocolAddressAt vecGhostAt

theorem wsFixed_wsEnv_untrusted_split (A : RustAlloc) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) :
    wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp =
      wsUntrustedFixedEnv A img x sp ∗ wsUntrustedFixedRest A img kit ikit x s0 sp := by
  unfold wsFixedV wsEnv wsArgCellsV wsUntrustedFixedEnv wsUntrustedFixedRest
  rw [logOff_eq img, protocolAddressAt_eq A x.rem x.remA, stack_wsCallee_extHook sp]
  ac_rfl

def wsUntrustedPre (A : RustAlloc) (img : Obj.Image) (x : DecryptGhost) (sp : BitVec 64)
    (e0 e1 e3 : BitVec 64) (e2 : BitVec 32) (d0 : BitVec 8) (pad : List (BitVec 8)) : SepProp :=
  ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗
  vecGhostAt A x.rem.name x.remA ∗
  ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
  memRegion (sp + 0x5f0#64) 24 ∗
  ((sp + 0x608#64) ↦₈ d0) ∗ ((sp + 0x609#64) ↦ₛ pad) ∗
  ((sp + 0x580#64) ↦₆₄ e0) ∗ ((sp + 0x588#64) ↦₆₄ e1) ∗
  ((sp + 0x590#64) ↦₃₂ e2) ∗ ((sp + 0x594#64) ↦₆₄ e3) ∗
  A.pool ∗ stackAt sp extHookStack

def wsUntrustedCommonRest (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (k : IdentityKey) : SepProp :=
  wsUntrustedFixedRest A img kit ikit x s0 sp ∗ wsMsgCells x sp ∗
  (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
  vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
  memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  memRegion (sp + 0x300#64) 0x280 ∗
  (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) ∗
  memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)

def wsUntrustedFrame (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (k : IdentityKey) (e4 : BitVec 64) : SepProp :=
  ((sp + 0x59c#64) ↦₆₄ e4) ∗
  memRegion (sp + 0x610#64) 16 ∗
  wsUntrustedCommonRest C A ctl img kit ikit x ans s0 sp rec' pt k

theorem trusted_entails_untrustedPre (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (k : IdentityKey) :
    (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)) ⊢
    ∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 32,
    ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ d0 : BitVec 8, ∃∗ pad : List (BitVec 8),
      ⌜pad.length = 7⌝ ∗
      wsUntrustedPre A img x sp e0 e1 e3 e2 d0 pad ∗
      wsUntrustedFrame C A ctl img kit ikit x ans s0 sp rec' pt k e4 := by
  rw [← sepConj_assoc, wsFixed_wsEnv_untrusted_split, memRegion_300_b00_split,
    memRegion_5a4_85c_split]
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion (sp + 0x580#64) 0x24 ∗ memRegion (sp + 0x5f0#64) 48) ∗
    (wsUntrustedFixedEnv A img x sp ∗
      wsUntrustedCommonRest C A ctl img kit ikit x ans s0 sp rec' pt k) by
    unfold wsUntrustedCommonRest; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left (sepConj_mono
    (memRegion_36_untrusted_entails (sp + 0x580#64))
    (memRegion_48_untrusted_entails (sp + 0x5f0#64)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro (d0 : BitVec 8)
  apply Entails.sepExists_elim; intro (pad : List (BitVec 8))
  apply Entails.sepExists_elim; intro (e0 : BitVec 64)
  apply Entails.sepExists_elim; intro (e1 : BitVec 64)
  apply Entails.sepExists_elim; intro (e2 : BitVec 32)
  apply Entails.sepExists_elim; intro (e3 : BitVec 64)
  apply Entails.sepExists_elim; intro (e4 : BitVec 64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜pad.length = 7⌝ ∗
      (wsUntrustedPre A img x sp e0 e1 e3 e2 d0 pad ∗
        wsUntrustedFrame C A ctl img kit ikit x ans s0 sp rec' pt k e4) by
    unfold wsUntrustedPre wsUntrustedFrame wsUntrustedFixedEnv
    ac_rfl)) ?_
  apply Entails.pure_left; intro hpad
  exact Entails.sepExists_right e0 (Entails.sepExists_right e1
    (Entails.sepExists_right e2 (Entails.sepExists_right e3
      (Entails.sepExists_right e4 (Entails.sepExists_right d0
        (Entails.sepExists_right pad (Entails.pure_right hpad (Entails.refl _))))))))

def wsUntrustedPostSpatial (A : RustAlloc) (img : Obj.Image) (x : DecryptGhost) (sp : BitVec 64)
    (cap ptr devWord : BitVec 64) : SepProp :=
  ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗
  vecGhostAt A x.rem.name x.remA ∗
  ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
  ((sp + 0x5f0#64) ↦₃₂ cap.extractLsb' 0 32) ∗
  ((sp + 0x5f4#64) ↦₃₂ cap.extractLsb' 32 32) ∗
  ((sp + 0x5f8#64) ↦₆₄ ptr) ∗
  ((sp + 0x600#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
  ((sp + 0x608#64) ↦₆₄ devWord) ∗
  ((sp + 0x580#64) ↦₃₂ cap.extractLsb' 32 32) ∗
  ((sp + 0x584#64) ↦₆₄ ptr) ∗
  ((sp + 0x58c#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
  ((sp + 0x594#64) ↦₆₄ devWord) ∗
  vecU8Buf A cap ptr x.rem.name.bytes ∗
  A.pool ∗ stackAt sp extHookStack

theorem untrustedPost_entails (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (rec' : SessionRecord (List (BitVec 8)))
    (ses : Session (List (BitVec 8))) (hcur : rec'.currentSession = some ses)
    (pt : List (BitVec 8)) (k : IdentityKey)
    (x28 w20 w21 cap ptr devWord e4 : BitVec 64) (pad : List (BitVec 8))
    (hpad : pad.length = 7) (hw4 : x.rem.device :: pad = unpack64 devWord)
    (hx28 : x28 = 0x800000000000000c#64) (hw1 : resWord1 w20 w21 = cap.extractLsb' 0 32) :
    wsUntrustedPostSpatial A img x sp cap ptr devWord ∗
      wsUntrustedFrame C A ctl img kit ikit x ans s0 sp rec' pt k e4 ⊢
    ∃∗ G : SessionGhost,
      wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) (some (G, ses.state)) ∗
      (∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p) ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) (.error (.untrustedIdentity x.rem.val)) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) := by
  refine Entails.trans (Entails.of_eq (show _ =
    (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
    (((sp + 0x5f0#64) ↦₃₂ cap.extractLsb' 0 32) ∗
      ((sp + 0x5f4#64) ↦₃₂ cap.extractLsb' 32 32) ∗
      ((sp + 0x5f8#64) ↦₆₄ ptr) ∗
      ((sp + 0x600#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
      ((sp + 0x608#64) ↦₆₄ devWord) ∗
      memRegion (sp + 0x610#64) 16) ∗
    ((((sp + 0x580#64) ↦₃₂ cap.extractLsb' 32 32) ∗
      ((sp + 0x584#64) ↦₆₄ ptr) ∗
      ((sp + 0x58c#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
      ((sp + 0x594#64) ↦₆₄ devWord) ∗
      ((sp + 0x59c#64) ↦₆₄ e4)) ∗
      vecU8Buf A cap ptr x.rem.name.bytes) ∗
    vecU8 A (sp + 0x290#64) pt ∗
    ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
    ((wsUntrustedFixedEnv A img x sp ∗ wsUntrustedFixedRest A img kit ikit x s0 sp) ∗
      wsMsgCells x sp ∗ memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗
      (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)) by
    unfold wsUntrustedPostSpatial wsUntrustedFrame wsUntrustedCommonRest wsUntrustedFixedEnv
    ac_rfl)) ?_
  rw [← wsFixed_wsEnv_untrusted_split]
  have h48 := cells_48_untrusted_entails_memRegion (sp + 0x5f0#64)
    (cap.extractLsb' 0 32) (cap.extractLsb' 32 32) ptr
    (BitVec.ofNat 64 x.rem.name.bytes.length) devWord
  have hst := stagedRes_untrusted_intro A x28 w20 w21 (sp + 0x580#64)
    cap ptr devWord e4 x.rem pad hpad hw4 hx28 hw1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h48 hst
  have hrec := sessionRecordAt_some_entails_droppable A (sp + 0x120#64) rec' ses hcur
  have hpt : vecU8 A (sp + 0x290#64) pt ⊢ ∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p :=
    Entails.sepExists_right pt (Entails.refl _)
  refine Entails.trans (sepConj_mono hrec (sepConj_mono h48
    (sepConj_mono hst (sepConj_mono hpt
      (sepConj_mono_left (key_entails_memRegion_32 (sp + 0x2a8#64) k)))))) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro G
  refine Entails.sepExists_right G ?_
  rw [memRegion_5a4_85c_split]
  exact Entails.of_eq (by ac_rfl)

theorem panic_outcome_of_allocFailedInV {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s sf : State}
    (htr0 : s0.trace <+: s.trace)
    (hpan : sf.status = .Panicked)
    (hm : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) :
    SubroutineOutcome (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) x R s0 sf := by
  refine Or.inr (Or.inl ⟨hpan, ?_⟩)
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  unfold withStoresDecSpecV Spec.inImage
  dsimp only
  apply Entails.pure_left
  rintro ⟨haf, htr⟩
  refine Entails.pure_right ⟨htr0.trans htr, Or.inl (allocFailedIn_trans htr0 haf)⟩ (Entails.refl _)

attribute [local semireducible] SepWP in
theorem segUntrustedV_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegUntrustedSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope := by
  intro hyps x ans R s0 s hst hL
  rcases hst with ⟨hpc, hmeta, hx26, hx19, hx22,
    rec, rec', pt, ses, k, hload, hscope, hdec, hcur, hrem, htrust, htrustRel, htr, hm⟩
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx27, hfr, hsym, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads hyps.loads
  have hpc' : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr decWithStoresName + 0x21b0#64 := by
    rw [← entryOf_eq_tripleRatchetProgAt hyps.loads, hpc]; rfl
  rw [← hsp] at hx26 hx19 hx22 hm
  let ist1 := ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity
  let R' : SepProp := decStoreExtra kit ikit st0 ist1 s0 ∗ R
  have hm_pre : s.mem ⊨
      (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 32,
        ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ d0 : BitVec 8, ∃∗ pad : List (BitVec 8),
          ⌜pad.length = 7⌝ ∗
          wsUntrustedPre A img x s.sp e0 e1 e3 e2 d0 pad ∗
          wsUntrustedFrame C A ctl img kit ikit x ans s0 s.sp rec' pt k e4) ∗ R' := by
    refine Satisfies.mono (sepConj_mono_left
      (trusted_entails_untrustedPre C A ctl img kit ikit x ans s0 s.sp rec' pt k)) ?_
    simpa only [R', ist1, sepConj_assoc] using hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨e0, e1, e2, e3, e4, d0, pad, hm_pre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_pre
  rcases hm_pre with ⟨hpad, hm_pre⟩
  rw [sepConj_assoc] at hm_pre
  obtain ⟨devWord, hw4⟩ := exists_unpack64_of_length_8 (bs := x.rem.device :: pad) (by simp [hpad])
  obtain ⟨sf, hsteps, hout⟩ :=
    segUntrusted_wp hyps.hooks.alloc hb
      (R := wsUntrustedFrame C A ctl img kit ikit x ans s0 s.sp rec' pt k e4 ∗ R')
      hw4 hpc' hrun hsp_align
      (wsUntrustedFrame C A ctl img kit ikit x ans s0 s.sp rec' pt k e4 ∗ R') hm_pre hL
  rcases hout with ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨hpan1, P_f, hm1, hpan_post1⟩ | ⟨_, _hoom⟩
  · obtain ⟨hm1', hsp1, hx26_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1'
    rcases hm1' with ⟨cap, ptr, hm1'⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1'
    rcases hm1' with ⟨⟨hx28_1, hx20_1, hx21_1, htr1⟩, hm1'⟩
    rw [← sepConj_assoc] at hm1'
    have hmeta1 := wsMeta_of_steps hmeta hsteps hrun1 hsp1 hx29_1 hx27_1 hvregs_1
    have hw1 : resWord1 (sf.readReg64 .x20) (sf.readReg64 .x21) = cap.extractLsb' 0 32 := by
      rw [hx20_1, hx21_1, resWord1_lsr8]
    have hm1_post := Satisfies.mono (sepConj_mono_left
      (untrustedPost_entails C A ctl img kit ikit x ans s0 s.sp rec' ses hcur pt k
        (sf.readReg64 .x28) (sf.readReg64 .x20) (sf.readReg64 .x21)
        cap ptr devWord e4 pad hpad hw4 hx28_1 hw1)) hm1'
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm1_post
    rcases hm1_post with ⟨G, hm1_post⟩
    refine ⟨sf, hsteps, Or.inl ?_⟩
    have hmod := model_of_trust_false C S x ans rec rec' pt ses k
      hload (hyps.scopeIn rec hscope.1) hdec hcur hrem htrust
    refine ⟨?_, hmeta1, ?_, ?_, ans, some (G, ses.state), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpc1, ← entryOf_eq_tripleRatchetProgAt hyps.loads]; rfl
    · rw [hx26_1, hx26, hsp]
    · rw [hx28_1]; decide
    · rw [hmod.1]; exact nofun
    · intro p; rw [hmod.1]; exact nofun
    · intro r hr; rw [hload] at hr; cases hr; exact hscope
    · rw [hmod.2]; exact ⟨hload ▸ hscope.2, trivial⟩
    · rw [hmod.2]; exact ⟨htrustRel, trivial⟩
    · rw [htr1, htr, hmod.2]; simp
    · have hstf : kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2 = st0 := by
        rw [hmod.2]; rfl
      have histf : ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2 = ist1 := by
        rw [hmod.2]; rfl
      rw [hmod.1, hstf, histf]
      simpa only [R', ite_true, hsp, sepConj_assoc] using hm1_post
  · have hpan_m' : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
      have hpan_m0 := hpan_post1 hm1
      rw [← sepConj_assoc] at hpan_m0
      have hpan_m1 := Satisfies.mono (sepConj_mono_left (shim_onPanic_entails rfl)) hpan_m0
      have hreord :
          (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R' ⊢
          (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
        dsimp only [R']
        rw [← sepConj_assoc, sepConj_assoc ⌜_⌝ anyHeap]
        exact sepConj_mono_left (sepConj_mono_right (entails_anyHeap _))
      exact Satisfies.mono hreord hpan_m1
    exact ⟨sf, hsteps, Or.inr (panic_outcome_of_allocFailedInV ⟨_, htr.symm⟩ hpan1 hpan_m')⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem segUntrusted_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    SegUntrustedSpec img C A ctl uuidTryParse S encRecord abs :=
  segUntrustedV_ok

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

section Placed

open CryptoVerification.LibsignalPublicApi.Placed

attribute [local semireducible] protocolAddressAt vecGhostAt in
set_option maxHeartbeats 800000 in
theorem segUntrusted_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hH : PublicApiDecHooksPlaced A H)
    {s : State} {R : SepProp}
    {addrA e0 e1 e3 devWord : BitVec 64} {e2 : BitVec 32} {d0 : BitVec 8} {pad : List (BitVec 8)}
    {addr : AddrGhost}
    (hw4 : addr.device :: pad = unpack64 devWord)
    (hpc : s.pc = untrustedPCPlaced)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp (lsProg_197 H) (errJoinPCPlaced true) s
      (FromRecordCallees.lsLogOff ∗
        ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗
        vecGhostAt A addr.name addrA ∗
        ((addrA + 0x18#64) ↦₈ addr.device) ∗
        memRegion (s.sp + 0x5f0#64) 24 ∗
        ((s.sp + 0x608#64) ↦₈ d0) ∗ ((s.sp + 0x609#64) ↦ₛ pad) ∗
        ((s.sp + 0x580#64) ↦₆₄ e0) ∗ ((s.sp + 0x588#64) ↦₆₄ e1) ∗
        ((s.sp + 0x590#64) ↦₃₂ e2) ∗ ((s.sp + 0x594#64) ↦₆₄ e3) ∗
        A.pool ∗ stackAt s.sp extHookStack)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
          ⌜sf.readReg64 .x28 = 0x800000000000000c#64 ∧
            sf.readReg64 .x20 = ((cap.extractLsb' 0 32) >>> 8#32).zeroExtend 64 ∧
            sf.readReg64 .x21 = (cap.extractLsb' 0 32).zeroExtend 64 ∧
            sf.trace = s.trace⌝ ∗
          FromRecordCallees.lsLogOff ∗
          ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗
          vecGhostAt A addr.name addrA ∗
          ((addrA + 0x18#64) ↦₈ addr.device) ∗
          ((s.sp + 0x5f0#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((s.sp + 0x5f4#64) ↦₃₂ cap.extractLsb' 32 32) ∗
          ((s.sp + 0x5f8#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x600#64) ↦₆₄ BitVec.ofNat 64 addr.name.bytes.length) ∗
          ((s.sp + 0x608#64) ↦₆₄ devWord) ∗
          ((s.sp + 0x580#64) ↦₃₂ cap.extractLsb' 32 32) ∗
          ((s.sp + 0x584#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x58c#64) ↦₆₄ BitVec.ofNat 64 addr.name.bytes.length) ∗
          ((s.sp + 0x594#64) ↦₆₄ devWord) ∗
          vecU8Buf A cap ptr addr.name.bytes ∗
          A.pool ∗ stackAt s.sp extHookStack) ∗ R) ∧
        sf.sp = s.sp ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  unfold untrustedPCPlaced at hpc
  unfold errJoinPCPlaced FromRecordCallees.lsLogOff lsLogFilterAddr
  dsimp only [lsProg_197, ite_true]
  have hclone0 : subroutine_ok (lsProg_197 H) (0#64 + lsmpl.base 623)
      (StoreKit.withLsRoCl lsmpl (stringCloneSpec A)) := by
    rw [BitVec.zero_add]
    exact StoreKit.subroutine_ok_rocl_of_withLsCodeRoLoaded
      (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
        (LibsignalBinary.Proofs.Common.StringClonePlaced.stringClone_placed_codeLoaded_ok
          hH.shim hH.alloc hH.memcpy hH.handleError))
  have hclone := box_lscro_197 hclone0
  apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 623) hcrl
  clear hcrl
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcrl1
  messageDecrypt_call_panic_lscro hclone hcrl1 (addrA, s.sp + 1520#64, addr.name)
  clear hcrl1 hclone
  apply SepWP.fold (vecU8_unpack_5f0 A s.sp addr.name.bytes) (by sep_focus)
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro (cap : BitVec 64)
  apply SepWP.exists_elim; intro (ptr : BitVec 64)
  wp_steps 5
  apply SepWP.fold
    (Entails.of_eq (repack_5f4_for_q0 s.sp cap ptr (BitVec.ofNat 64 addr.name.bytes.length)))
    (by sep_focus)
  wp_step
  apply SepWP.fold
    (Entails.of_eq (repack_5f4_for_q1 s.sp cap ptr (BitVec.ofNat 64 addr.name.bytes.length) addr.device pad devWord hw4))
    (by sep_focus)
  wp_steps 3
  apply SepWP.fold
    (Entails.of_eq (repack_588_for_q1 s.sp ptr (BitVec.ofNat 64 addr.name.bytes.length) e2))
    (by sep_focus)
  wp_steps 4
  apply SepWP.fold
    (Entails.of_eq (repack_580_after_q1 s.sp cap ptr))
    (by sep_focus)
  wp_done

def wsUntrustedFixedEnvPlaced [LibsignalPlacement] (A : RustAlloc) (x : DecryptGhost)
    (sp : BitVec 64) : SepProp :=
  FromRecordCallees.lsLogOff ∗
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗
  vecGhostAt A x.rem.name x.remA ∗
  ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
  A.pool ∗ stackAt sp extHookStack

def wsUntrustedFixedRestPlaced (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) : SepProp :=
  wsSavedRegs s0.sp s0 ∗
  ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
  ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
  ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
  ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
  ((sp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64)) ∗
  decVtablesAtV kit ikit ∗
  memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
  memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
  memRegion (x.remA + 0x19#64) 7 ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.loc x.locA ∗
  wsExtStackRest sp

theorem wsFixed_wsEnv_untrusted_split_placed [LibsignalPlacement] (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) :
    wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp =
      wsUntrustedFixedEnvPlaced A x sp ∗ wsUntrustedFixedRestPlaced A kit ikit x s0 sp := by
  unfold wsFixedVPlaced wsEnvPlaced wsArgCellsV wsUntrustedFixedEnvPlaced wsUntrustedFixedRestPlaced
  rw [protocolAddressAt_eq A x.rem x.remA, stack_wsCallee_extHook sp]
  ac_rfl

def wsUntrustedPrePlaced [LibsignalPlacement] (A : RustAlloc) (x : DecryptGhost) (sp : BitVec 64)
    (e0 e1 e3 : BitVec 64) (e2 : BitVec 32) (d0 : BitVec 8) (pad : List (BitVec 8)) : SepProp :=
  FromRecordCallees.lsLogOff ∗
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗
  vecGhostAt A x.rem.name x.remA ∗
  ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
  memRegion (sp + 0x5f0#64) 24 ∗
  ((sp + 0x608#64) ↦₈ d0) ∗ ((sp + 0x609#64) ↦ₛ pad) ∗
  ((sp + 0x580#64) ↦₆₄ e0) ∗ ((sp + 0x588#64) ↦₆₄ e1) ∗
  ((sp + 0x590#64) ↦₃₂ e2) ∗ ((sp + 0x594#64) ↦₆₄ e3) ∗
  A.pool ∗ stackAt sp extHookStack

def wsUntrustedCommonRestPlaced (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (k : IdentityKey) : SepProp :=
  wsUntrustedFixedRestPlaced A kit ikit x s0 sp ∗ wsMsgCells x sp ∗
  (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
  vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
  memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  memRegion (sp + 0x300#64) 0x280 ∗
  (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) ∗
  memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)

def wsUntrustedFramePlaced (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (k : IdentityKey) (e4 : BitVec 64) : SepProp :=
  ((sp + 0x59c#64) ↦₆₄ e4) ∗
  memRegion (sp + 0x610#64) 16 ∗
  wsUntrustedCommonRestPlaced C A ctl kit ikit x ans s0 sp rec' pt k

theorem trusted_entails_untrustedPre_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (k : IdentityKey) :
    (wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)) ⊢
    ∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 32,
    ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ d0 : BitVec 8, ∃∗ pad : List (BitVec 8),
      ⌜pad.length = 7⌝ ∗
      wsUntrustedPrePlaced A x sp e0 e1 e3 e2 d0 pad ∗
      wsUntrustedFramePlaced C A ctl kit ikit x ans s0 sp rec' pt k e4 := by
  rw [← sepConj_assoc, wsFixed_wsEnv_untrusted_split_placed, memRegion_300_b00_split,
    memRegion_5a4_85c_split]
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion (sp + 0x580#64) 0x24 ∗ memRegion (sp + 0x5f0#64) 48) ∗
    (wsUntrustedFixedEnvPlaced A x sp ∗
      wsUntrustedCommonRestPlaced C A ctl kit ikit x ans s0 sp rec' pt k) by
    unfold wsUntrustedCommonRestPlaced; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left (sepConj_mono
    (memRegion_36_untrusted_entails (sp + 0x580#64))
    (memRegion_48_untrusted_entails (sp + 0x5f0#64)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro (d0 : BitVec 8)
  apply Entails.sepExists_elim; intro (pad : List (BitVec 8))
  apply Entails.sepExists_elim; intro (e0 : BitVec 64)
  apply Entails.sepExists_elim; intro (e1 : BitVec 64)
  apply Entails.sepExists_elim; intro (e2 : BitVec 32)
  apply Entails.sepExists_elim; intro (e3 : BitVec 64)
  apply Entails.sepExists_elim; intro (e4 : BitVec 64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜pad.length = 7⌝ ∗
      (wsUntrustedPrePlaced A x sp e0 e1 e3 e2 d0 pad ∗
        wsUntrustedFramePlaced C A ctl kit ikit x ans s0 sp rec' pt k e4) by
    unfold wsUntrustedPrePlaced wsUntrustedFramePlaced wsUntrustedFixedEnvPlaced
    ac_rfl)) ?_
  apply Entails.pure_left; intro hpad
  exact Entails.sepExists_right e0 (Entails.sepExists_right e1
    (Entails.sepExists_right e2 (Entails.sepExists_right e3
      (Entails.sepExists_right e4 (Entails.sepExists_right d0
        (Entails.sepExists_right pad (Entails.pure_right hpad (Entails.refl _))))))))

def wsUntrustedPostSpatialPlaced [LibsignalPlacement] (A : RustAlloc) (x : DecryptGhost) (sp : BitVec 64)
    (cap ptr devWord : BitVec 64) : SepProp :=
  FromRecordCallees.lsLogOff ∗
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗
  vecGhostAt A x.rem.name x.remA ∗
  ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
  ((sp + 0x5f0#64) ↦₃₂ cap.extractLsb' 0 32) ∗
  ((sp + 0x5f4#64) ↦₃₂ cap.extractLsb' 32 32) ∗
  ((sp + 0x5f8#64) ↦₆₄ ptr) ∗
  ((sp + 0x600#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
  ((sp + 0x608#64) ↦₆₄ devWord) ∗
  ((sp + 0x580#64) ↦₃₂ cap.extractLsb' 32 32) ∗
  ((sp + 0x584#64) ↦₆₄ ptr) ∗
  ((sp + 0x58c#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
  ((sp + 0x594#64) ↦₆₄ devWord) ∗
  vecU8Buf A cap ptr x.rem.name.bytes ∗
  A.pool ∗ stackAt sp extHookStack

theorem untrustedPost_entails_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (rec' : SessionRecord (List (BitVec 8)))
    (ses : Session (List (BitVec 8))) (hcur : rec'.currentSession = some ses)
    (pt : List (BitVec 8)) (k : IdentityKey)
    (x28 w20 w21 cap ptr devWord e4 : BitVec 64) (pad : List (BitVec 8))
    (hpad : pad.length = 7) (hw4 : x.rem.device :: pad = unpack64 devWord)
    (hx28 : x28 = 0x800000000000000c#64) (hw1 : resWord1 w20 w21 = cap.extractLsb' 0 32) :
    wsUntrustedPostSpatialPlaced A x sp cap ptr devWord ∗
      wsUntrustedFramePlaced C A ctl kit ikit x ans s0 sp rec' pt k e4 ⊢
    ∃∗ G : SessionGhost,
      wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) (some (G, ses.state)) ∗
      (∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p) ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) (.error (.untrustedIdentity x.rem.val)) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) := by
  refine Entails.trans (Entails.of_eq (show _ =
    (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
    (((sp + 0x5f0#64) ↦₃₂ cap.extractLsb' 0 32) ∗
      ((sp + 0x5f4#64) ↦₃₂ cap.extractLsb' 32 32) ∗
      ((sp + 0x5f8#64) ↦₆₄ ptr) ∗
      ((sp + 0x600#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
      ((sp + 0x608#64) ↦₆₄ devWord) ∗
      memRegion (sp + 0x610#64) 16) ∗
    ((((sp + 0x580#64) ↦₃₂ cap.extractLsb' 32 32) ∗
      ((sp + 0x584#64) ↦₆₄ ptr) ∗
      ((sp + 0x58c#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
      ((sp + 0x594#64) ↦₆₄ devWord) ∗
      ((sp + 0x59c#64) ↦₆₄ e4)) ∗
      vecU8Buf A cap ptr x.rem.name.bytes) ∗
    vecU8 A (sp + 0x290#64) pt ∗
    ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
    ((wsUntrustedFixedEnvPlaced A x sp ∗ wsUntrustedFixedRestPlaced A kit ikit x s0 sp) ∗
      wsMsgCells x sp ∗ memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗
      (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)) by
    unfold wsUntrustedPostSpatialPlaced wsUntrustedFramePlaced wsUntrustedCommonRestPlaced wsUntrustedFixedEnvPlaced
    ac_rfl)) ?_
  rw [← wsFixed_wsEnv_untrusted_split_placed]
  have h48 := cells_48_untrusted_entails_memRegion (sp + 0x5f0#64)
    (cap.extractLsb' 0 32) (cap.extractLsb' 32 32) ptr
    (BitVec.ofNat 64 x.rem.name.bytes.length) devWord
  have hst := stagedRes_untrusted_intro A x28 w20 w21 (sp + 0x580#64)
    cap ptr devWord e4 x.rem pad hpad hw4 hx28 hw1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h48 hst
  have hrec := sessionRecordAt_some_entails_droppable A (sp + 0x120#64) rec' ses hcur
  have hpt : vecU8 A (sp + 0x290#64) pt ⊢ ∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p :=
    Entails.sepExists_right pt (Entails.refl _)
  refine Entails.trans (sepConj_mono hrec (sepConj_mono h48
    (sepConj_mono hst (sepConj_mono hpt
      (sepConj_mono_left (key_entails_memRegion_32 (sp + 0x2a8#64) k)))))) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro G
  refine Entails.sepExists_right G ?_
  rw [memRegion_5a4_85c_split]
  exact Entails.of_eq (by ac_rfl)

attribute [local semireducible] SepWP in
theorem segUntrustedVPlaced_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegUntrustedSpecVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope := by
  intro hyps x ans R s0 s hst hL
  rcases hst with ⟨hpc, hmeta, hx26, hx19, hx22,
    rec, rec', pt, ses, k, hload, hscope, hdec, hcur, hrem, htrust, htrustRel, htr, hm⟩
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx27, hcrl, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  rw [← hsp] at hx26 hx19 hx22 hm
  let ist1 := ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity
  let R' : SepProp := decStoreExtraPlaced kit ikit st0 ist1 s0 ∗ R
  have hm_pre : s.mem ⊨
      (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 32,
        ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ d0 : BitVec 8, ∃∗ pad : List (BitVec 8),
          ⌜pad.length = 7⌝ ∗
          wsUntrustedPrePlaced A x s.sp e0 e1 e3 e2 d0 pad ∗
          wsUntrustedFramePlaced C A ctl kit ikit x ans s0 s.sp rec' pt k e4) ∗ R' := by
    refine Satisfies.mono (sepConj_mono_left
      (trusted_entails_untrustedPre_placed C A ctl kit ikit x ans s0 s.sp rec' pt k)) ?_
    simpa only [R', ist1, sepConj_assoc] using hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨e0, e1, e2, e3, e4, d0, pad, hm_pre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_pre
  rcases hm_pre with ⟨hpad, hm_pre⟩
  rw [sepConj_assoc] at hm_pre
  obtain ⟨devWord, hw4⟩ := exists_unpack64_of_length_8 (bs := x.rem.device :: pad) (by simp [hpad])
  obtain ⟨sf, hsteps, hout⟩ :=
    segUntrusted_placed_wp hyps.hooks
      (R := wsUntrustedFramePlaced C A ctl kit ikit x ans s0 s.sp rec' pt k e4 ∗ R')
      hw4 hpc hrun hsp_align hcrl
      (wsUntrustedFramePlaced C A ctl kit ikit x ans s0 s.sp rec' pt k e4 ∗ R') hm_pre hL
  rcases hout with ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨hpan1, P_f, hm1, hpan_post1⟩ | ⟨_, _hoom⟩
  · obtain ⟨hm1', hsp1, hx26_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1'
    rcases hm1' with ⟨cap, ptr, hm1'⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1'
    rcases hm1' with ⟨⟨hx28_1, hx20_1, hx21_1, htr1⟩, hm1'⟩
    rw [← sepConj_assoc] at hm1'
    have hmeta1 := wsMetaPlaced_of_steps hmeta hsteps hrun1 hsp1 hx29_1 hx27_1 hvregs_1
    have hw1 : resWord1 (sf.readReg64 .x20) (sf.readReg64 .x21) = cap.extractLsb' 0 32 := by
      rw [hx20_1, hx21_1, resWord1_lsr8]
    have hm1_post := Satisfies.mono (sepConj_mono_left
      (untrustedPost_entails_placed C A ctl kit ikit x ans s0 s.sp rec' ses hcur pt k
        (sf.readReg64 .x28) (sf.readReg64 .x20) (sf.readReg64 .x21)
        cap ptr devWord e4 pad hpad hw4 hx28_1 hw1)) hm1'
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm1_post
    rcases hm1_post with ⟨G, hm1_post⟩
    refine ⟨sf, hsteps, Or.inl ?_⟩
    have hmod := model_of_trust_false C S x ans rec rec' pt ses k
      hload (hyps.scopeIn rec hscope.1) hdec hcur hrem htrust
    refine ⟨hpc1, hmeta1, ?_, ?_, ans, some (G, ses.state), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx26_1, hx26, hsp]
    · rw [hx28_1]; decide
    · rw [hmod.1]; exact nofun
    · intro p; rw [hmod.1]; exact nofun
    · intro r hr; rw [hload] at hr; cases hr; exact hscope
    · rw [hmod.2]; exact ⟨hload ▸ hscope.2, trivial⟩
    · rw [hmod.2]; exact ⟨htrustRel, trivial⟩
    · rw [htr1, htr, hmod.2]; simp
    · have hstf : kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2 = st0 := by
        rw [hmod.2]; rfl
      have histf : ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2 = ist1 := by
        rw [hmod.2]; rfl
      rw [hmod.1, hstf, histf]
      simpa only [R', ite_true, hsp, sepConj_assoc] using hm1_post
  · have hpan_m' : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
      have hpan_m0 := hpan_post1 hm1
      rw [← sepConj_assoc] at hpan_m0
      have hpan_m1 := Satisfies.mono (sepConj_mono_left (shim_onPanic_entails rfl)) hpan_m0
      have hreord :
          (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R' ⊢
          (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
        dsimp only [R']
        rw [← sepConj_assoc, sepConj_assoc ⌜_⌝ anyHeap]
        exact sepConj_mono_left (sepConj_mono_right (entails_anyHeap _))
      exact Satisfies.mono hreord hpan_m1
    exact ⟨sf, hsteps, Or.inr (panic_outcome_of_allocFailedInVPlaced ⟨_, htr.symm⟩ hpan1 hpan_m')⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

end Placed

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted
