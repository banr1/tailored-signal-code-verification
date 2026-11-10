/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegWrite

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Decode lemmas (`0x3c97c .. 0x3c9b8`, 16 instructions) -/

gen_decodes libsignalSessionCode_tree messageDecryptWriteBin [(ls_off% "session_message_decrypt_signal" + 9428) → (ls_off% "session_message_decrypt_signal" + 9488)]

/-! ## 2. 36-byte Staged Buffer & 48-byte `sret` Helpers -/

theorem exists_unpack32_of_length_4 {bs : List (BitVec 8)} (h : bs.length = 4) :
    ∃ w : BitVec 32, bs = unpack32 w := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> try (simp at h)
  exact ⟨b3 ++ b2 ++ b1 ++ b0, (unpack32_pack32 b0 b1 b2 b3).symm⟩

theorem exists_split_36 {bs : List (BitVec 8)} (h : bs.length = 36) :
    ∃ (w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 32),
      bs = unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ unpack32 w4 := by
  have hw0 : (bs.take 8).length = 8 := by simp [h]
  have hw1 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have hw2 : ((bs.drop 16).take 8).length = 8 := by simp [h]
  have hw3 : ((bs.drop 24).take 8).length = 8 := by simp [h]
  have hw4 : (bs.drop 32).length = 4 := by simp [h]
  obtain ⟨w0, hw0_eq⟩ := exists_unpack64_of_length_8 hw0
  obtain ⟨w1, hw1_eq⟩ := exists_unpack64_of_length_8 hw1
  obtain ⟨w2, hw2_eq⟩ := exists_unpack64_of_length_8 hw2
  obtain ⟨w3, hw3_eq⟩ := exists_unpack64_of_length_8 hw3
  obtain ⟨w4, hw4_eq⟩ := exists_unpack32_of_length_4 hw4
  refine ⟨w0, w1, w2, w3, w4, ?_⟩
  rw [← hw0_eq, ← hw1_eq, ← hw2_eq, ← hw3_eq, ← hw4_eq]
  simp only [List.append_assoc]
  have s3 : (bs.drop 24).take 8 ++ bs.drop 32 = bs.drop 24 := by
    have := List.take_append_drop 8 (bs.drop 24)
    rwa [List.drop_drop] at this
  have s2 : (bs.drop 16).take 8 ++ bs.drop 24 = bs.drop 16 := by
    have := List.take_append_drop 8 (bs.drop 16)
    rwa [List.drop_drop] at this
  have s1 : (bs.drop 8).take 8 ++ bs.drop 16 = bs.drop 8 := by
    have := List.take_append_drop 8 (bs.drop 8)
    rwa [List.drop_drop] at this
  rw [s3, s2, s1, List.take_append_drop]

theorem pointsToBytes_36_eq (a : BitVec 64) (w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 32) :
    (a ↦ₛ (unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ unpack32 w4)) =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₃₂ w4) := by
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length,
    ← pointsTo64_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_48_sret_split (r : BitVec 64) :
    memRegion r 48 =
      (∃∗ v0 : BitVec 64, (r ↦₆₄ v0)) ∗
      (∃∗ v1 : BitVec 32, ((r + 8#64) ↦₃₂ v1)) ∗
      (∃∗ v2 : BitVec 64, ((r + 12#64) ↦₆₄ v2)) ∗
      (∃∗ v3 : BitVec 64, ((r + 20#64) ↦₆₄ v3)) ∗
      (∃∗ v4 : BitVec 64, ((r + 28#64) ↦₆₄ v4)) ∗
      (∃∗ v5 : BitVec 64, ((r + 36#64) ↦₆₄ v5)) ∗
      (∃∗ v6 : BitVec 32, ((r + 44#64) ↦₃₂ v6)) := by
  rw [memRegion_split r 8 40 (by decide),
      memRegion_split (r + 8#64) 4 36 (by decide),
      memRegion_split (r + 8#64 + 4#64) 8 28 (by decide),
      memRegion_split (r + 8#64 + 4#64 + 8#64) 8 20 (by decide),
      memRegion_split (r + 8#64 + 4#64 + 8#64 + 8#64) 8 12 (by decide),
      memRegion_split (r + 8#64 + 4#64 + 8#64 + 8#64 + 8#64) 8 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    ProofLib.memRegion_eight, ProofLib.memRegion_four]

theorem bfm_24_23_eq_resWord1 (w20 w21 : BitVec 64) :
    BitVec.truncate 32
      (BitVec.zeroExtend 64 (BitVec.truncate 32 w21) &&& 18446744069414584575#64 |||
        (BitVec.zeroExtend 64 (BitVec.truncate 32 w20) &&& 16777215#64) <<< 8) =
    resWord1 w20 w21 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [resWord1, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    hi, decide_true, Bool.true_and]
  have h64 : i < 64 := by omega
  simp only [h64, decide_true, Bool.true_and]
  by_cases h8 : i < 8
  · have hmask1 : (18446744069414584575#64).getLsbD i = true := by
      revert h8; decide +revert
    simp [h8, hmask1]
  · have hmask1 : (18446744069414584575#64).getLsbD i = false := by
      revert hi h8; decide +revert
    have hge8 : ¬ i < 8 := h8
    have hi8_32 : i - 8 < 32 := by omega
    have hi8_64 : i - 8 < 64 := by omega
    have hi8_24 : i - 8 < 24 := by omega
    have hmask2 : ∀ k < 24, (16777215#64).getLsbD k = true := by decide
    simp [hge8, hmask1, hi8_32, hi8_64, hi8_24, hmask2 (i - 8) hi8_24]

theorem sret_36_fold (r : BitVec 64) (w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 32)
    {bs : List (BitVec 8)}
    (hbs : bs = unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ unpack32 w4) :
    ((r + 12#64) ↦₆₄ w0) ∗ ((r + 20#64) ↦₆₄ w1) ∗ ((r + 28#64) ↦₆₄ w2) ∗
      ((r + 36#64) ↦₆₄ w3) ∗ ((r + 44#64) ↦₃₂ w4) ⊢
      ((r + 12#64) ↦ₛ bs) := by
  subst hbs
  rw [pointsToBytes_36_eq (r + 12#64) w0 w1 w2 w3 w4]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

theorem staged36_entails_memRegion (sp : BitVec 64) (w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 32) :
    ((sp + 0x300#64) ↦₆₄ w0) ∗ ((sp + 0x308#64) ↦₆₄ w1) ∗ ((sp + 0x310#64) ↦₆₄ w2) ∗
      ((sp + 0x318#64) ↦₆₄ w3) ∗ ((sp + 0x320#64) ↦₃₂ w4) ⊢
      memRegion (sp + 0x300#64) 0x24 := by
  have h := pointsToBytes_entails_memRegion (sp + 0x300#64)
    (unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ unpack32 w4)
  rw [pointsToBytes_36_eq] at h
  simp only [List.length_append, unpack64_length, unpack32_length,
    BitVec.add_assoc, BitVec.reduceAdd] at h
  exact h

theorem savedRegs_entails_cells12 (sp0 : BitVec 64) (s0 : State) :
    ((sp0 - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp0 - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
    ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
    ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
      memRegion (sp0 - 96#64) 96 := by
  rw [ProofLib.memRegion_cells (sp0 - 96#64) 12 (by decide)]
  simp (config := { decide := true }) only [cells_succ, cells_zero, sepConj_emp,
    bv_sub_add_lit, Nat.reduceSub]
  exact Entails.sepExists_right _ (sepConj_mono_right (Entails.sepExists_right _ (sepConj_mono_right
    (Entails.sepExists_right _ (sepConj_mono_right (Entails.sepExists_right _ (sepConj_mono_right
      (Entails.sepExists_right _ (sepConj_mono_right (Entails.sepExists_right _ (sepConj_mono_right
        (Entails.sepExists_right _ (sepConj_mono_right (Entails.sepExists_right _ (sepConj_mono_right
          (Entails.sepExists_right _ (sepConj_mono_right (Entails.sepExists_right _ (sepConj_mono_right
            (Entails.sepExists_right _ (sepConj_mono_right
              (Entails.sepExists_right _ (Entails.refl _)))))))))))))))))))))))

theorem argMsgCellsV_entails_memRegion {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) :
    wsMsgCells x sp ∗ wsArgCellsV kit ikit x s0 sp ⊢ memRegion (sp + 0xe0#64) 0x40 := by
  unfold wsMsgCells wsArgCellsV
  have hreord :
      (((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA)) ∗
      (((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
       ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗ ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
       ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗ ((sp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64))) =
      ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xe8#64) ↦₆₄ x.remA) ∗
      ((sp + 0xf0#64) ↦₆₄ x.locA) ∗ ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
      ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗ ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
      ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗ ((sp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64)) := by
    ac_rfl
  rw [hreord, ProofLib.memRegion_cells (sp + 0xe0#64) 8 (by decide)]
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right _ (sepConj_mono_right (Entails.sepExists_right _ (sepConj_mono_right
    (Entails.sepExists_right _ (sepConj_mono_right (Entails.sepExists_right _ (sepConj_mono_right
      (Entails.sepExists_right _ (sepConj_mono_right (Entails.sepExists_right _ (sepConj_mono_right
        (Entails.sepExists_right _ (sepConj_mono_right
          (Entails.sepExists_right _ (Entails.refl _)))))))))))))))

theorem frame_regions_fold_wsStack (sp0 : BitVec 64) :
    let sp := sp0 - 0xee0#64
    stackAt sp wsCalleeStack ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0xe0#64) 0x40 ∗
      memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2c8#64) 8 ∗
      memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x2e0#64) 0x20 ∗
      memRegion (sp + 0x300#64) 0x24 ∗ memRegion (sp + 0x324#64) 0xadc ∗
      memRegion (sp + 0xe00#64) 0x80 ∗ memRegion (sp0 - 96#64) 96 ⊢
      stackAt sp0 wsStack := by
  intro sp
  have hframe :
      memRegion sp 0xe80 =
        memRegion sp 0xa0 ∗ (memRegion (sp + 0xa0#64) 0x40 ∗ (memRegion (sp + 0xe0#64) 0x40 ∗
        (memRegion (sp + 0x120#64) 0x1a8 ∗ (memRegion (sp + 0x2c8#64) 8 ∗
        (memRegion (sp + 0x2d0#64) 0x10 ∗ (memRegion (sp + 0x2e0#64) 0x20 ∗
        (memRegion (sp + 0x300#64) 0x24 ∗ (memRegion (sp + 0x324#64) 0xadc ∗
        memRegion (sp + 0xe00#64) 0x80)))))))) := by
    rw [memRegion_split sp 0xa0 0xde0 (by decide),
        memRegion_split (sp + 0xa0#64) 0x40 0xda0 (by decide),
        memRegion_split (sp + 0xa0#64 + 0x40#64) 0x40 0xd60 (by decide),
        memRegion_split (sp + 0xa0#64 + 0x40#64 + 0x40#64) 0x1a8 0xbb8 (by decide),
        memRegion_split (sp + 0xa0#64 + 0x40#64 + 0x40#64 + 0x1a8#64) 8 0xbb0 (by decide),
        memRegion_split (sp + 0xa0#64 + 0x40#64 + 0x40#64 + 0x1a8#64 + 8#64) 0x10 0xba0 (by decide),
        memRegion_split (sp + 0xa0#64 + 0x40#64 + 0x40#64 + 0x1a8#64 + 8#64 + 0x10#64) 0x20 0xb80 (by decide),
        memRegion_split (sp + 0xa0#64 + 0x40#64 + 0x40#64 + 0x1a8#64 + 8#64 + 0x10#64 + 0x20#64) 0x24 0xb5c (by decide),
        memRegion_split (sp + 0xa0#64 + 0x40#64 + 0x40#64 + 0x1a8#64 + 8#64 + 0x10#64 + 0x20#64 + 0x24#64) 0xadc 0x80 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hstack :
      stackAt sp0 wsStack =
        stackAt sp wsCalleeStack ∗ (memRegion sp 0xe80 ∗ memRegion (sp0 - 96#64) 96) := by
    simp only [stackAt, sp]
    have hsp1 := memRegion_split (sp0 - BitVec.ofNat 64 wsStack) wsCalleeStack 0xee0 (by decide)
    rw [show wsCalleeStack + 0xee0 = wsStack by decide] at hsp1
    rw [hsp1]
    have e1 : sp0 - BitVec.ofNat 64 wsStack = sp0 - 0xee0#64 - BitVec.ofNat 64 wsCalleeStack := by
      dsimp only [wsStack, wsCalleeStack, entryStack, wsFrame]; bv_omega
    have e2 : sp0 - BitVec.ofNat 64 wsStack + BitVec.ofNat 64 wsCalleeStack = sp0 - 0xee0#64 := by
      dsimp only [wsStack, wsCalleeStack, entryStack, wsFrame]; bv_omega
    rw [e2, e1, memRegion_split (sp0 - 0xee0#64) 0xe80 96 (by decide)]
    have e3 : sp0 - 0xee0#64 + 0xe80#64 = sp0 - 96#64 := by bv_omega
    rw [e3]
  rw [hstack, hframe]
  exact Entails.of_eq (by ac_rfl)

theorem segWriteV_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegWriteSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope := by
  intro hH x R s0 s hRF hL
  obtain ⟨hpc, ⟨hrun, hsp, hal0, hal, hx29, hx27, _hfrozen, _hsym, hvregs⟩,
    ans, hno_pan, hscope, hcalls, hid_calls, htrace, hmem⟩ := hRF
  have hentry := entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) hH.loads
    msgDecryptName
  have hfn : libsignalSessionCode.fnOff msgDecryptName = num% (ls_off% "session_message_decrypt_signal") :=
    CryptoVerification.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8
  unfold resultFinalPC at hpc
  rw [hentry] at hpc
  simp only [wp_norm, arm64_norm] at hx29 hx27
  dsimp only [StagedRes] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_pure_left_comm, satisfies_pure_sepConj, sepConj_assoc] at hmem
  obtain ⟨bs, F, ⟨hbs_len, hres_ent⟩, hmem⟩ := hmem
  obtain ⟨w0, w1, w2, w3, w4, hbs_eq⟩ := exists_split_36 hbs_len
  let sp := s0.sp - 0xee0#64
  let stf := kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2
  let istf := ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2
  have hmem_act : s.mem ⊨
      (((sp + 0x300#64) ↦₆₄ w0) ∗ ((sp + 0x300#64 + 8#64) ↦₆₄ w1) ∗
       ((sp + 0x300#64 + 16#64) ↦₆₄ w2) ∗ ((sp + 0x300#64 + 24#64) ↦₆₄ w3) ∗
       ((sp + 0x300#64 + 32#64) ↦₃₂ w4) ∗ memRegion x.ret 48 ∗ wsSavedRegs s0.sp s0) ∗
      (wsArgCellsV kit ikit x s0 sp ∗ wsMsgCells x sp ∗ decVtablesAtV kit ikit ∗
       memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
       memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
       wsEnv A img x sp ∗ F ∗
       memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
       memRegion (sp + 0x324#64) 0xadc ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
       decStoreExtra kit ikit stf istf s0 ∗ R) := by
    rw [hbs_eq, pointsToBytes_36_eq] at hmem
    dsimp only [wsFixedV, sp, stf, istf] at hmem ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  clear hmem
  have hwp : SepWP (tripleRatchetProgAt img.base C ctl abs) (s0.readReg64 .x30) s
      (((sp + 0x300#64) ↦₆₄ w0) ∗ ((sp + 0x300#64 + 8#64) ↦₆₄ w1) ∗
       ((sp + 0x300#64 + 16#64) ↦₆₄ w2) ∗ ((sp + 0x300#64 + 24#64) ↦₆₄ w3) ∗
       ((sp + 0x300#64 + 32#64) ↦₃₂ w4) ∗ memRegion x.ret 48 ∗ wsSavedRegs s0.sp s0)
      (fun sf Pf =>
        (Pf ⊢ memRegion (sp + 0x300#64) 0x24 ∗
          ((x.ret ↦₆₄ s.readReg64 .x28) ∗
           ((x.ret + 8#64) ↦₃₂ resWord1 (s.readReg64 .x20) (s.readReg64 .x21)) ∗
           ((x.ret + 12#64) ↦ₛ bs)) ∗
          memRegion (s0.sp - 96#64) 96) ∧
        sf.sp = s0.sp ∧ sf.trace = s.trace ∧
        CalleeSavedPreserved s0 sf) := by
    code_fetches_range CryptoVerification.libsignalSessionCode messageDecryptWriteBin img.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (num% (ls_off% "session_message_decrypt_signal")) 0x24d4 0x40
    dsimp only [tripleRatchetProgAt] at hpc ⊢
    generalize (libsignalSessionCode.rebase img.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr msgDecryptName = entry at *
    examples_hide_fetches
    rw [memRegion_48_sret_split x.ret]
    unfold wsSavedRegs
    dsimp only [sp]
    wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    repeat' (apply SepWP.exists_elim; intro _)
    have hal_s0 : (s0.sp &&& 15#64 == 0#64) = true := hal0
    have hal_s : (s.sp &&& 15#64 == 0#64) = true := hal
    have hal_sub96 : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
      ProofLib.spAligned_sub s0.sp 96 hal0 (by decide)
    wp_steps
    rw [bfm_24_23_eq_resWord1]
    apply SepWP.fold (staged36_entails_memRegion (s0.sp - 0xee0#64) w0 w1 w2 w3 w4) (by sep_focus)
    apply SepWP.fold (sret_36_fold x.ret w0 w1 w2 w3 w4 hbs_eq) (by sep_focus)
    apply SepWP.fold (savedRegs_entails_cells12 s0.sp s0) (by sep_focus)
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    refine ⟨?_, ?_, rfl, ?_⟩
    · simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub, Reg.x20, Reg.x21, Reg.x28]
      exact Entails.of_eq (by ac_rfl)
    · wp_norm_lhs
    · simp only [CalleeSavedPreserved, wp_norm, arm64_norm, hvregs]
  obtain ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, Pf, hmf, hent_pf, hsp_sf, htr_sf, hcs_sf⟩ | ⟨_, _hoom⟩⟩ :=
    hwp.elim hmem_act hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨sf, hsteps, Or.inr (Or.inl ⟨⟨hpc_sf, hsp_sf, hrun_sf⟩, ⟨hsp_sf, hcs_sf⟩, ?_⟩)⟩
  have hmf1 := Satisfies.mono (sepConj_mono_left hent_pf) hmf
  clear hmf hent_pf
  dsimp only [withStoresDecSpecV, Spec.inImage]
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨ans, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hno_pan, hscope, hcalls, hid_calls, htr_sf.trans htrace⟩, ?_⟩
  have hcomb :
      (memRegion (sp + 0x300#64) 0x24 ∗
        ((x.ret ↦₆₄ s.readReg64 .x28) ∗
         ((x.ret + 8#64) ↦₃₂ resWord1 (s.readReg64 .x20) (s.readReg64 .x21)) ∗
         ((x.ret + 12#64) ↦ₛ bs)) ∗
        memRegion (s0.sp - 96#64) 96) ∗
      (wsArgCellsV kit ikit x s0 sp ∗ wsMsgCells x sp ∗ decVtablesAtV kit ikit ∗
       memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
       memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
       wsEnv A img x sp ∗ F ∗
       memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
       memRegion (sp + 0x324#64) 0xadc ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
       decStoreExtra kit ikit stf istf s0 ∗ R) ⊢
      (kit.storeAt (s0.readReg64 .x3) stf ∗
       ikit.identityAt (s0.readReg64 .x5) istf ∗
       apiDecResultAt A x.ret (x.model C S uuidTryParse ans).1 ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
       logOff img ∗ decVtablesAtV kit ikit ∗ stackAt s0.sp (wsStackV kit ikit) ∗ A.pool) ∗ R := by
    unfold wsEnv
    have hreord :
        (memRegion (sp + 0x300#64) 0x24 ∗
          ((x.ret ↦₆₄ s.readReg64 .x28) ∗
           ((x.ret + 8#64) ↦₃₂ resWord1 (s.readReg64 .x20) (s.readReg64 .x21)) ∗
           ((x.ret + 12#64) ↦ₛ bs)) ∗
          memRegion (s0.sp - 96#64) 96) ∗
        (wsArgCellsV kit ikit x s0 sp ∗ wsMsgCells x sp ∗ decVtablesAtV kit ikit ∗
         memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
         memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
         (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗ logOff img ∗ stackAt sp wsCalleeStack ∗ A.pool) ∗ F ∗
         memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
         memRegion (sp + 0x324#64) 0xadc ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
         decStoreExtra kit ikit stf istf s0 ∗ R) =
        (((x.ret ↦₆₄ s.readReg64 .x28) ∗
          ((x.ret + 8#64) ↦₃₂ resWord1 (s.readReg64 .x20) (s.readReg64 .x21)) ∗
          ((x.ret + 12#64) ↦ₛ bs) ∗ F) ∗
         ((stackAt sp wsCalleeStack ∗ memRegion sp 0xa0 ∗ memRegion (sp + 0xa0#64) 0x40 ∗
           (wsMsgCells x sp ∗ wsArgCellsV kit ikit x s0 sp) ∗
           memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2c8#64) 8 ∗
           memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x2e0#64) 0x20 ∗
           memRegion (sp + 0x300#64) 0x24 ∗ memRegion (sp + 0x324#64) 0xadc ∗
           memRegion (sp + 0xe00#64) 0x80 ∗ memRegion (s0.sp - 96#64) 96) ∗
          decStoreExtra kit ikit stf istf s0) ∗
         (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
          logOff img ∗ decVtablesAtV kit ikit ∗ A.pool ∗ R)) := by
      ac_rfl
    rw [hreord]
    have hstk :
        (stackAt sp wsCalleeStack ∗ memRegion sp 0xa0 ∗ memRegion (sp + 0xa0#64) 0x40 ∗
          (wsMsgCells x sp ∗ wsArgCellsV kit ikit x s0 sp) ∗
          memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2c8#64) 8 ∗
          memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x2e0#64) 0x20 ∗
          memRegion (sp + 0x300#64) 0x24 ∗ memRegion (sp + 0x324#64) 0xadc ∗
          memRegion (sp + 0xe00#64) 0x80 ∗ memRegion (s0.sp - 96#64) 96) ∗
        decStoreExtra kit ikit stf istf s0 ⊢
        kit.storeAt (s0.readReg64 .x3) stf ∗ ikit.identityAt (s0.readReg64 .x5) istf ∗
          stackAt s0.sp (wsStackV kit ikit) := by
      refine Entails.trans (sepConj_mono_left ?_) (wsStack_join_extra kit ikit stf istf s0)
      refine Entails.trans ?_ (frame_regions_fold_wsStack s0.sp)
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (argMsgCellsV_entails_memRegion kit ikit x s0 sp))))
    refine Entails.trans (sepConj_mono (hres_ent x.ret) (sepConj_mono_left hstk)) ?_
    exact Entails.of_eq (by ac_rfl)
  exact Satisfies.mono hcomb hmf1

theorem segWrite_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    SegWriteSpec img C A ctl uuidTryParse S encRecord abs :=
  segWriteV_ok

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

section Placed

open CryptoVerification.LibsignalPublicApi.Placed

private theorem argMsgCellsV_entails_memRegion_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) :
    wsMsgCells x sp ∗ wsArgCellsV kit ikit x s0 sp ⊢ memRegion (sp + 0xe0#64) 0x40 := by
  unfold wsMsgCells wsArgCellsV
  have hreord :
      (((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA)) ∗
      (((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
       ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗ ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
       ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗ ((sp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64))) =
      ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xe8#64) ↦₆₄ x.remA) ∗
      ((sp + 0xf0#64) ↦₆₄ x.locA) ∗ ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
      ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗ ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
      ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗ ((sp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64)) := by
    ac_rfl
  rw [hreord, ProofLib.memRegion_cells (sp + 0xe0#64) 8 (by decide)]
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right _ (sepConj_mono_right (Entails.sepExists_right _ (sepConj_mono_right
    (Entails.sepExists_right _ (sepConj_mono_right (Entails.sepExists_right _ (sepConj_mono_right
      (Entails.sepExists_right _ (sepConj_mono_right (Entails.sepExists_right _ (sepConj_mono_right
        (Entails.sepExists_right _ (sepConj_mono_right
          (Entails.sepExists_right _ (Entails.refl _)))))))))))))))

theorem segWriteVPlaced_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegWriteSpecVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope := by
  intro _hH x R s0 s hRF hL
  obtain ⟨hpc, ⟨hrun, hsp, hal0, hal, hx29, hx27, _hcrl, hvregs⟩,
    ans, hno_pan, hscope, hcalls, hid_calls, htrace, hmem⟩ := hRF
  unfold resultFinalPCPlaced at hpc
  simp only [wp_norm, arm64_norm] at hx29 hx27
  dsimp only [StagedRes] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_pure_left_comm, satisfies_pure_sepConj, sepConj_assoc] at hmem
  obtain ⟨bs, F, ⟨hbs_len, hres_ent⟩, hmem⟩ := hmem
  obtain ⟨w0, w1, w2, w3, w4, hbs_eq⟩ := exists_split_36 hbs_len
  let sp := s0.sp - 0xee0#64
  let stf := kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2
  let istf := ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2
  have hmem_act : s.mem ⊨
      (((sp + 0x300#64) ↦₆₄ w0) ∗ ((sp + 0x300#64 + 8#64) ↦₆₄ w1) ∗
       ((sp + 0x300#64 + 16#64) ↦₆₄ w2) ∗ ((sp + 0x300#64 + 24#64) ↦₆₄ w3) ∗
       ((sp + 0x300#64 + 32#64) ↦₃₂ w4) ∗ memRegion x.ret 48 ∗ wsSavedRegs s0.sp s0) ∗
      (wsArgCellsV kit ikit x s0 sp ∗ wsMsgCells x sp ∗ decVtablesAtV kit ikit ∗
       memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
       memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
       wsEnvPlaced A x sp ∗ F ∗
       memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
       memRegion (sp + 0x324#64) 0xadc ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
       decStoreExtraPlaced kit ikit stf istf s0 ∗ R) := by
    rw [hbs_eq, pointsToBytes_36_eq] at hmem
    dsimp only [wsFixedVPlaced, sp, stf, istf] at hmem ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  clear hmem
  have hwp : SepWP (lsProg_197 H) (s0.readReg64 .x30) s
      (((sp + 0x300#64) ↦₆₄ w0) ∗ ((sp + 0x300#64 + 8#64) ↦₆₄ w1) ∗
       ((sp + 0x300#64 + 16#64) ↦₆₄ w2) ∗ ((sp + 0x300#64 + 24#64) ↦₆₄ w3) ∗
       ((sp + 0x300#64 + 32#64) ↦₃₂ w4) ∗ memRegion x.ret 48 ∗ wsSavedRegs s0.sp s0)
      (fun sf Pf =>
        (Pf ⊢ memRegion (sp + 0x300#64) 0x24 ∗
          ((x.ret ↦₆₄ s.readReg64 .x28) ∗
           ((x.ret + 8#64) ↦₃₂ resWord1 (s.readReg64 .x20) (s.readReg64 .x21)) ∗
           ((x.ret + 12#64) ↦ₛ bs)) ∗
          memRegion (s0.sp - 96#64) 96) ∧
        sf.sp = s0.sp ∧ sf.trace = s.trace ∧
        CalleeSavedPreserved s0 sf) := by
    dsimp only [lsProg_197]
    rw [memRegion_48_sret_split x.ret]
    unfold wsSavedRegs
    dsimp only [sp]
    wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    repeat' (apply SepWP.exists_elim; intro _)
    have hal_s0 : (s0.sp &&& 15#64 == 0#64) = true := hal0
    have hal_s : (s.sp &&& 15#64 == 0#64) = true := hal
    have hal_sub96 : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
      ProofLib.spAligned_sub s0.sp 96 hal0 (by decide)
    wp_steps
    rw [bfm_24_23_eq_resWord1]
    apply SepWP.fold (staged36_entails_memRegion (s0.sp - 0xee0#64) w0 w1 w2 w3 w4) (by sep_focus)
    apply SepWP.fold (sret_36_fold x.ret w0 w1 w2 w3 w4 hbs_eq) (by sep_focus)
    apply SepWP.fold (savedRegs_entails_cells12 s0.sp s0) (by sep_focus)
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    refine ⟨?_, ?_, rfl, ?_⟩
    · simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub, Reg.x20, Reg.x21, Reg.x28]
      exact Entails.of_eq (by ac_rfl)
    · wp_norm_lhs
    · simp only [CalleeSavedPreserved, wp_norm, arm64_norm, hvregs]
  obtain ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, Pf, hmf, hent_pf, hsp_sf, htr_sf, hcs_sf⟩ | ⟨_, _hoom⟩⟩ :=
    hwp.elim hmem_act hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨sf, hsteps, Or.inr (Or.inl ⟨⟨hpc_sf, hsp_sf, hrun_sf⟩, ⟨hsp_sf, hcs_sf⟩, ?_⟩)⟩
  have hmf1 := Satisfies.mono (sepConj_mono_left hent_pf) hmf
  clear hmf hent_pf
  dsimp only [withStoresDecPlacedSpecV, StoreKit.withLsCodeRoLoaded]
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨ans, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hno_pan, hscope, hcalls, hid_calls, htr_sf.trans htrace⟩, ?_⟩
  have hcomb :
      (memRegion (sp + 0x300#64) 0x24 ∗
        ((x.ret ↦₆₄ s.readReg64 .x28) ∗
         ((x.ret + 8#64) ↦₃₂ resWord1 (s.readReg64 .x20) (s.readReg64 .x21)) ∗
         ((x.ret + 12#64) ↦ₛ bs)) ∗
        memRegion (s0.sp - 96#64) 96) ∗
      (wsArgCellsV kit ikit x s0 sp ∗ wsMsgCells x sp ∗ decVtablesAtV kit ikit ∗
       memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
       memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
       wsEnvPlaced A x sp ∗ F ∗
       memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
       memRegion (sp + 0x324#64) 0xadc ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
       decStoreExtraPlaced kit ikit stf istf s0 ∗ R) ⊢
      (kit.storeAt (s0.readReg64 .x3) stf ∗
       ikit.identityAt (s0.readReg64 .x5) istf ∗
       apiDecResultAt A x.ret (x.model C S uuidTryParse ans).1 ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
       FromRecordCallees.lsLogOff ∗ decVtablesAtV kit ikit ∗ stackAt s0.sp (wsStackV kit ikit) ∗ A.pool) ∗ R := by
    unfold wsEnvPlaced
    have hreord :
        (memRegion (sp + 0x300#64) 0x24 ∗
          ((x.ret ↦₆₄ s.readReg64 .x28) ∗
           ((x.ret + 8#64) ↦₃₂ resWord1 (s.readReg64 .x20) (s.readReg64 .x21)) ∗
           ((x.ret + 12#64) ↦ₛ bs)) ∗
          memRegion (s0.sp - 96#64) 96) ∗
        (wsArgCellsV kit ikit x s0 sp ∗ wsMsgCells x sp ∗ decVtablesAtV kit ikit ∗
         memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
         memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
         (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗ stackAt sp wsCalleeStack ∗ A.pool) ∗ F ∗
         memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
         memRegion (sp + 0x324#64) 0xadc ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
         decStoreExtraPlaced kit ikit stf istf s0 ∗ R) =
        (((x.ret ↦₆₄ s.readReg64 .x28) ∗
          ((x.ret + 8#64) ↦₃₂ resWord1 (s.readReg64 .x20) (s.readReg64 .x21)) ∗
          ((x.ret + 12#64) ↦ₛ bs) ∗ F) ∗
         ((stackAt sp wsCalleeStack ∗ memRegion sp 0xa0 ∗ memRegion (sp + 0xa0#64) 0x40 ∗
           (wsMsgCells x sp ∗ wsArgCellsV kit ikit x s0 sp) ∗
           memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2c8#64) 8 ∗
           memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x2e0#64) 0x20 ∗
           memRegion (sp + 0x300#64) 0x24 ∗ memRegion (sp + 0x324#64) 0xadc ∗
           memRegion (sp + 0xe00#64) 0x80 ∗ memRegion (s0.sp - 96#64) 96) ∗
          decStoreExtraPlaced kit ikit stf istf s0) ∗
         (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
          FromRecordCallees.lsLogOff ∗ decVtablesAtV kit ikit ∗ A.pool ∗ R)) := by
      ac_rfl
    rw [hreord]
    have hstk :
        (stackAt sp wsCalleeStack ∗ memRegion sp 0xa0 ∗ memRegion (sp + 0xa0#64) 0x40 ∗
          (wsMsgCells x sp ∗ wsArgCellsV kit ikit x s0 sp) ∗
          memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2c8#64) 8 ∗
          memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x2e0#64) 0x20 ∗
          memRegion (sp + 0x300#64) 0x24 ∗ memRegion (sp + 0x324#64) 0xadc ∗
          memRegion (sp + 0xe00#64) 0x80 ∗ memRegion (s0.sp - 96#64) 96) ∗
        decStoreExtraPlaced kit ikit stf istf s0 ⊢
        kit.storeAt (s0.readReg64 .x3) stf ∗ ikit.identityAt (s0.readReg64 .x5) istf ∗
          stackAt s0.sp (wsStackV kit ikit) := by
      refine Entails.trans (sepConj_mono_left ?_) (wsStack_join_extra_placed kit ikit stf istf s0)
      refine Entails.trans ?_ (frame_regions_fold_wsStack s0.sp)
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (argMsgCellsV_entails_memRegion_placed kit ikit x s0 sp))))
    refine Entails.trans (sepConj_mono (hres_ent x.ret) (sepConj_mono_left hstk)) ?_
    exact Entails.of_eq (by ac_rfl)
  exact Satisfies.mono hcomb hmf1

end Placed

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegWrite
