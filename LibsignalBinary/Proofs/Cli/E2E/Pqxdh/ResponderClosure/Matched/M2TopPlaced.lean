/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2OkPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TailPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Top
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop

/-!
# Relocatable Top-Level Stage P2 Matched-Session Contract

Relocatable `[LibsignalPlacement]` counterpart of `Matched.M2Top` on Block `518` (`lsProg_518 ext`,
`(blkPl_518).base = lsmpl.base 518`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

noncomputable section

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (entails_replace_sub)
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

theorem publicKey_beq_false_of_ne_placed [LibsignalPlacement] {remIdKey ik : IdentityKey}
    (hne : some ik ≠ some remIdKey) :
    (remIdKey.publicKey == ik.publicKey) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  apply hne
  cases remIdKey with | mk pk1 =>
  cases ik with | mk pk2 =>
  dsimp only at heq
  subst heq
  rfl

theorem coro_2a0_split32_placed [LibsignalPlacement] (coroPtr w : BitVec 64) :
    ((coroPtr + 0x2a0#64) ↦₆₄ w) =
      ((coroPtr + 0x2a0#64) ↦₃₂ w.extractLsb' 0 32) ∗
      ((coroPtr + 0x2a4#64) ↦₃₂ w.extractLsb' 32 32) := by
  rw [pointsTo64_split32 (coroPtr + 0x2a0#64) w]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem panicOomProp_frame_placed [LibsignalPlacement] {s0 sf : State} {Pf : SepProp} (F : SepProp)
    (h : CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0 sf Pf) :
    CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0 sf (Pf ∗ F) :=
  panicOomProp_frame F h

abbrev stageP2MatchedMismatchPostPlaced [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      kyberStorePtr kyberStoreVt
      v_330 v_388 u_80 u_88 u_90 u_b0
      u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (u_2a8 u_b8 : BitVec 32)
    (outerVerByte innerVerByte b_3ac : BitVec 8)
    (baseKey : PublicKey) (remIdKey : IdentityKey) (F : SepProp) : SepProp :=
  processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    kyberStorePtr kyberStoreVt ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗
  cells (coroPtr + 0x250#64) 6 ∗
  ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗
  ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
  ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
  ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
  ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
  ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
  ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
  ((sp + 0x80#64) ↦₆₄ u_80) ∗
  ((sp + 0x88#64) ↦₆₄ u_88) ∗
  ((sp + 0x90#64) ↦₆₄ u_90) ∗
  ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
  ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
  ((sp + 0xa8#64) ↦₆₄ 3#64) ∗
  ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
  ((sp + 0xb8#64) ↦₃₂ u_b8) ∗
  ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((sp + 0xd0#64) ↦₆₄ 70#64) ∗
  memRegion (sp + 0x370#64) 36 ∗
  ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗
  ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
  ((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗
  ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
  ((sp + 0x3c0#64) ↦₆₄ u_3c0) ∗
  ((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
  ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗
  ((sp + 0x3d8#64) ↦₆₄ u_3d8) ∗
  memRegion (sp + 0x3e0#64) 34 ∗
  memRegion (sp + 0x920#64) 6 ∗
  memRegion (sp + 0xa90#64) 48 ∗
  apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  A.pool ∗
  ((msgPtr + 0x70#64) ↦₈ innerVerByte) ∗
  ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
  ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
  ((msgPtr + 0xf0#64) ↦₈ outerVerByte) ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  stackAt sp rootStack ∗
  F

abbrev stageP2MatchedMatchPrePlaced [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      kyberStorePtr kyberStoreVt
      v_330 v_388 v_d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (outerVerByte innerVerByte b_2c0 : BitVec 8)
    (baseKey : PublicKey) (remIdKey : IdentityKey)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (F : SepProp) : SepProp :=
  processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    kyberStorePtr kyberStoreVt ∗
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
  prevSessionsEmptyAt A coroPtr g ∗
  sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
  cells (coroPtr + 0x250#64) 6 ∗
  ((coroPtr + 0x298#64) ↦₃₂ 2#32) ∗
  ((coroPtr + 0x29c#64) ↦₃₂ opkHi) ∗
  ((coroPtr + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
  ((coroPtr + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
  ((coroPtr + 0x2a8#64) ↦₃₂ v_d0.truncate 32) ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
  ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
  ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
  ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
  ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
  ((msgPtr + 0x70#64) ↦₈ innerVerByte) ∗
  ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
  ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
  ((msgPtr + 0xf0#64) ↦₈ outerVerByte) ∗
  ((sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
  ((sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
  ((sp + 0x90#64) ↦₆₄ v_388) ∗
  ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
  ((sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗
  ((sp + 0xa8#64) ↦₆₄ v_330) ∗
  ((sp + 0xb0#64) ↦₆₄ msgPtr) ∗
  ((sp + 0xb8#64) ↦₃₂ innerVerByte.zeroExtend 32) ∗
  ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
  memRegion (sp + 0x370#64) 36 ∗
  ((sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗
  ((sp + 0x3ac#64) ↦₈ 3#8) ∗
  ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
  ((sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
  ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
  ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
  ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
  ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
  memRegion (sp + 0x3e0#64) 34 ∗
  memRegion (sp + 0x920#64) 6 ∗
  memRegion (sp + 0xa90#64) 48 ∗
  memRegion outPtr 48 ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  A.pool ∗
  stackAt sp rootStack ∗
  F

abbrev stageP2MatchedPrePlaced [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      v_330 v_388 u_80 u_88 u_90 u_a8 u_b0 v_d0
      u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (u_2a8 u_b8 : BitVec 32)
    (outerVerByte innerVerByte b_4f1 b_4f2 b_390 b_2c0 b_3ac : BitVec 8)
    (baseKey : PublicKey) (remIdKey : IdentityKey)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    (F : SepProp) : SepProp :=
  cells (coroPtr + 0x3f8#64) 6 ∗
  cells (coroPtr + 0x468#64) 4 ∗
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
  sessionRecordAt A (coroPtr + 0xe0#64) g r ∗
  cells (coroPtr + 0x250#64) 6 ∗
  ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗
  ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
  ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
  ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
  ((coroPtr + 0x390#64) ↦₈ b_390) ∗
  ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
  ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
  ((msgPtr + 0x70#64) ↦₈ innerVerByte) ∗
  ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
  ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
  ((msgPtr + 0xf0#64) ↦₈ outerVerByte) ∗
  ((sp + 0x80#64) ↦₆₄ u_80) ∗
  ((sp + 0x88#64) ↦₆₄ u_88) ∗
  ((sp + 0x90#64) ↦₆₄ u_90) ∗
  ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
  ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
  ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
  ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
  ((sp + 0xb8#64) ↦₃₂ u_b8) ∗
  ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
  memRegion (sp + 0x370#64) 36 ∗
  ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗
  ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
  ((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗
  ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
  ((sp + 0x3c0#64) ↦₆₄ u_3c0) ∗
  ((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
  ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗
  ((sp + 0x3d8#64) ↦₆₄ u_3d8) ∗
  memRegion (sp + 0x3e0#64) 34 ∗
  memRegion (sp + 0x920#64) 6 ∗
  memRegion (sp + 0xa90#64) 48 ∗
  memRegion outPtr 48 ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  A.pool ∗
  stackAt sp rootStack ∗
  F

private theorem bind_sepWPp_steps_frame_panicF_placed
    {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P F P_stage P_stage_post F_inner : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf,
      CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0 sf Pf → Qp sf (Pf ∗ F))
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post) ∧ Q_regs sm)
      (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0))
    (hP : P = (P_stage ∗ F) ∗ F_inner)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Q_regs sm →
      SepWPp prog ret sm (P_stage_post ∗ (F_inner ∗ F)) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hP_re : P = P_stage ∗ (F_inner ∗ F) := by
    rw [hP]; ac_rfl
  rw [hP_re, sepConj_assoc P_stage (F_inner ∗ F) R] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨hp, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage ((F_inner ∗ F) ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post ∗ (F_inner ∗ F)) ∗ R := by
      rw [sepConj_assoc P_stage_post (F_inner ∗ F) R]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc P_m (F_inner ∗ F) R, ← sepConj_assoc P_m F_inner F] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hp, (P_m ∗ F_inner) ∗ F, hmm,
      hpan sm (P_m ∗ F_inner) (panicOomProp_frame F_inner hpanm)⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 1200000 in
/-- Relocatable `[LibsignalPlacement]` Stage P2 remote-identity mismatch branch
(`(blkPl_518).base + 0x094c → s0.readReg64 .x30` when `recSt.remoteIdentity ≠ some remIdKey`). -/
theorem stageP2_matched_094c_mismatch_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hto : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (strToOwnedLocal2Spec A)))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    (h_bb : Rust.withPanics ext lsBlackBoxU8Sym =
      some CryptoVerification.LibsignalSession.blackBoxHook)
    (hdrop_ss : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State)
    (sp coroPtr outPtr msgPtr u_a8 u_d0 : BitVec 64)
    (b_4f2 b_390 b_2c0 : BitVec 8)
    (remIdKey : IdentityKey)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hrem_ne : recSt.remoteIdentity ≠ some remIdKey)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s0.trace <+: s.trace)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x94c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (Getters.remoteIdentityOkAt (sp + 0x3e0#64) recSt.remoteIdentity ∗
       prevSessionsEmptyAt A coroPtr g ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x920#64) 6 ∗
       memRegion (sp + 0xa90#64) 48 ∗
       memRegion outPtr 48 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt sp rootStack)
      (fun sf P_f =>
        (P_f ⊢
          memRegion (sp + 0x3e0#64) 34 ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
          cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((sp + 0xa8#64) ↦₆₄ 3#64) ∗
          ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ 70#64) ∗
          memRegion (sp + 0x370#64) 36 ∗
          memRegion (sp + 0x920#64) 6 ∗
          memRegion (sp + 0xa90#64) 48 ∗
          apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt sp rootStack) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0) := by
  cases hrem : recSt.remoteIdentity with
  | none =>
    conv =>
      arg 4
      rw [remoteIdentityOkAt_none_eq sp, memRegion_32_eq_chunks32 (sp + 0x3e2#64),
          memRegion_920_6_split sp, memRegion_a90_48_split_10_38 sp]
    dsimp only [chunks32At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    sep_norm
    refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun h1 =>
      SepWPp.exists_elim fun q2 => SepWPp.exists_elim fun q3 =>
      SepWPp.exists_elim fun q4 => SepWPp.exists_elim fun h5 =>
      SepWPp.exists_elim fun u_920 => SepWPp.exists_elim fun u_924 =>
      SepWPp.exists_elim fun u_a90 => SepWPp.exists_elim fun u_a98 => ?_
    have h094c := p2_seg_094c_ok_placed_wp ext s coroPtr outPtr hpc hrun hsp_align hx19
    rw [hsp_eq] at h094c
    refine bind_sepWP_lscro_steps_m2_placed hcro h094c (by sep_focus)
      fun s1 _ hpc1 hrun1 hcro1 hregs1 => ?_
    rcases hregs1 with ⟨hsp1_s, htr1_s, hvregs1, hx19_1, hx21_1, _, _, hx25_1, hx26_1, _, hx28_1, _, _⟩
    have hsp1 : s1.sp = sp := hsp1_s
    have hx21_1' : s1.readReg64 .x21 = s1.sp + 0x370#64 := by rw [hsp1]; exact hx21_1.trans hx21
    have h1064 := p2_seg_1064_none_placed_wp ext s1 coroPtr q2 q3 q4 u_a90
      w0 u_920 h1 h5 u_924 u_a98 hpc1 hrun1 (by rw [hsp1, ← hsp_eq]; exact hsp_align) hx19_1 hx21_1'
    rw [hsp1] at h1064
    refine bind_sepWP_lscro_steps_m2_placed hcro1 h1064 (by sep_focus)
      fun s2 _ hpc2 hrun2 hcro2 hregs2 => ?_
    rcases hregs2 with ⟨hsp2_1, htr2_1, hvregs2, hx19_2, hx25_2, hx26_2, _, hx28_2, _, _⟩
    have hsp2 : s2.sp = sp := hsp2_1
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
    have htr2_s : s2.trace = s.trace := htr2_1.trans htr1_s
    have htr2 : s0.trace <+: s2.trace := by rw [htr2_s]; exact htr
    have hx25_2' : s2.readReg64 .x25 = sp + 0x210#64 := hx25_2.trans (hx25_1.trans hx25)
    have hx26_2' : s2.readReg64 .x26 = outPtr := hx26_2.trans hx26_1
    have hx28_2' : s2.readReg64 .x28 = sp + 0xa90#64 := hx28_2.trans (hx28_1.trans hx28)
    have hvregs2_s : calleeSavedVRegs s2 = calleeSavedVRegs s :=
      congrArg VRegFile.calleeSaved (hvregs2.trans hvregs1)
    have hrem34 := rem34_bytes_entails_memRegion34 sp 0#8 0#8 w0 h1 q2 q3 q4 h5
    dsimp only [chunks32At] at hrem34
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrem34
    refine P3P4.SepWPp.weaken_frame hrem34 (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (memRegion_920_6_join sp w0 h1) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (memRegion_a90_48_join_10_38 sp q4 h5) (by sep_focus) ?_
    conv => arg 4; rw [memRegion_34_split_24_10 sp]
    simp only [sepConj_assoc]
    have htail := stageP2_matched_mismatch_tail_placed hto hdealloc hdrop_ss s0 s2 sp coroPtr outPtr
      u_a8 u_d0 b_4f2 b_390 b_2c0 g recG recSt hcro2 htr2 hsp2 hsp_root hpc2 hrun2
      hsp2_align hx19_2 hx25_2' hx26_2' hx28_2'
    refine SepWPp.bind_sepWPp_steps_frame htail (by sep_focus)
      fun sf _ hpcf hrunf ⟨hspf, htrf_2, hcsf, hvregsf_2, hcrof⟩ => ?_
    refine SepWPp.done hpcf hrunf
      ⟨?_, hspf, htrf_2.trans htr2_s, hcsf, hvregsf_2.trans hvregs2_s, hcrof⟩
    have hjoin34 : memRegion (sp + 0x3e0#64) 24 ∗ memRegion (sp + 0x3f8#64) 10 ⊢
        memRegion (sp + 0x3e0#64) 34 :=
      Entails.of_eq (memRegion_34_split_24_10 sp).symm
    exact entails_replace_sub hjoin34 (by sep_focus) (eq_of_sep_emp (by sep_focus))
  | some ik =>
    have hne_ik : some ik ≠ some remIdKey := by rw [← hrem]; exact hrem_ne
    have hchk := stageP2_matched_094c_some_to_10cc_placed (Qp := CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0)
      h_bb s sp coroPtr outPtr msgPtr remIdKey ik hcro hsp_eq hsp_root hpc hrun hsp_align
      hx19 hx21 hx25 hx28
    refine SepWPp.bind_sepWPp_steps_frame hchk (by sep_focus)
      fun s1 _ hpc1 hrun1 ⟨hsp1, htr1_s, hx0_1, hx19_1, hx25_1, hx26_1, hx28_1, _, hvregs1, hcro1⟩ => ?_
    have hx0_zero : s1.readReg64 .x0 = 0#64 := by
      simpa [publicKey_beq_false_of_ne_placed hne_ik] using hx0_1
    have h10cc := p2_seg_10cc_mismatch_placed_wp ext s1 coroPtr hpc1 hrun1 hx0_zero hx19_1
    refine bind_sepWP_lscro_steps_m2_placed hcro1 h10cc (by sep_focus)
      fun s2 _ hpc2 hrun2 hcro2 hregs2 => ?_
    rcases hregs2 with ⟨hsp2_1, htr2_1, hvregs2, hx19_2, hx25_2, hx26_2, _, hx28_2, _, _⟩
    have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
    have htr2_s : s2.trace = s.trace := htr2_1.trans htr1_s
    have htr2 : s0.trace <+: s2.trace := by rw [htr2_s]; exact htr
    have hx25_2' : s2.readReg64 .x25 = sp + 0x210#64 := hx25_2.trans hx25_1
    have hx26_2' : s2.readReg64 .x26 = outPtr := hx26_2.trans hx26_1
    have hx28_2' : s2.readReg64 .x28 = sp + 0xa90#64 := hx28_2.trans hx28_1
    have hvregs2_s : calleeSavedVRegs s2 = calleeSavedVRegs s :=
      (congrArg VRegFile.calleeSaved hvregs2).trans hvregs1
    conv => arg 4; rw [memRegion_34_split_24_10 sp]
    simp only [sepConj_assoc]
    have htail := stageP2_matched_mismatch_tail_placed hto hdealloc hdrop_ss s0 s2 sp coroPtr outPtr
      u_a8 u_d0 b_4f2 b_390 b_2c0 g recG recSt hcro2 htr2 hsp2 hsp_root hpc2 hrun2
      hsp2_align hx19_2 hx25_2' hx26_2' hx28_2'
    refine SepWPp.bind_sepWPp_steps_frame htail (by sep_focus)
      fun sf _ hpcf hrunf ⟨hspf, htrf_2, hcsf, hvregsf_2, hcrof⟩ => ?_
    refine SepWPp.done hpcf hrunf
      ⟨?_, hspf, htrf_2.trans htr2_s, hcsf, hvregsf_2.trans hvregs2_s, hcrof⟩
    have hjoin34 : memRegion (sp + 0x3e0#64) 24 ∗ memRegion (sp + 0x3f8#64) 10 ⊢
        memRegion (sp + 0x3e0#64) 34 :=
      Entails.of_eq (memRegion_34_split_24_10 sp).symm
    exact entails_replace_sub hjoin34 (by sep_focus) (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
/-- Framed-panic form of `stageP2_matched_ok_placed` accepting
`(hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf (Pf ∗ F))` directly. -/
theorem stageP2_matched_ok_framed_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Q Qp : State → SepProp → Prop}
    (hser : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec A)))
    (hto : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (strToOwnedLocal2Spec A)))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    (h_bb : Rust.withPanics ext lsBlackBoxU8Sym = some blackBoxHook)
    (hdrop_ss : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
      v_330 v_388 u_80 u_88 u_90 u_a8 u_b0 v_d0
      u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (u_2a8 u_b8 : BitVec 32)
    (outerVerByte innerVerByte b_4f1 b_4f2 b_390 b_2c0 b_3ac : BitVec 8)
    (baseKey : PublicKey) (remIdKey : IdentityKey)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (F : SepProp)
    (hcur : r.currentSession = some sess)
    (hver : sess.state.version = outerVerByte.zeroExtend 32)
    (halice : sess.aliceBaseKey = baseKey.serialize)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s0.trace <+: s.trace)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hx29 : s.readReg64 .x29 = sp + 0xc70#64)
    (hpan : ∀ sf Pf,
      CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0 sf Pf → Qp sf (Pf ∗ F))
    (hmismatch : sess.state.remoteIdentity ≠ some remIdKey →
      ∀ (sf : State) (Pf : SepProp),
        sf.pc = s0.readReg64 .x30 →
        sf.status = .Running →
        Steps (lsProg_518 (Rust.withPanics ext)) s sf →
        sf.sp = sp + 0xcd0#64 →
        sf.trace = s.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        (Pf ⊢ stageP2MatchedMismatchPostPlaced A s0 sp coroPtr outPtr msgPtr
          remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
          kyberStorePtr kyberStoreVt v_330 v_388 u_80 u_88 u_90 u_b0
          u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
          u_2a8 u_b8 outerVerByte innerVerByte b_3ac baseKey remIdKey F) →
        Q sf Pf)
    (hmatch : sess.state.remoteIdentity = some remIdKey →
      ∀ (s2 : State) (recG : SessionGhost) (opkHi kyberPreKeyId signedPreKeyId : BitVec 32),
        g.cur = some recG →
        SessionExtraRel recG sess →
        Steps (lsProg_518 (Rust.withPanics ext)) s s2 →
        s2.pc = (blkPl_518).base + 0x1778#64 →
        s2.status = .Running →
        s2.sp = sp →
        (s2.sp &&& 15#64 == 0#64) = true →
        s2.trace = s.trace →
        s2.readReg64 .x19 = coroPtr →
        s2.readReg64 .x27 = sp + 0x370#64 →
        s2.readReg64 .x29 = sp + 0xc70#64 →
        calleeSavedVRegs s2 = calleeSavedVRegs s →
        StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem →
        SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s2
          (stageP2MatchedMatchPrePlaced A s0 sp coroPtr outPtr msgPtr
            remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt v_330 v_388 v_d0
            opkHi kyberPreKeyId signedPreKeyId outerVerByte innerVerByte b_2c0
            baseKey remIdKey g recG sess.state F)
          Q Qp) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stageP2MatchedPrePlaced A s0 sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
        v_330 v_388 u_80 u_88 u_90 u_a8 u_b0 v_d0
        u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
        u_2a8 u_b8 outerVerByte innerVerByte b_4f1 b_4f2 b_390 b_2c0 b_3ac
        baseKey remIdKey g r F)
      Q Qp := by
  dsimp only [stageP2MatchedPrePlaced, stageP2MatchedMismatchPostPlaced, stageP2MatchedMatchPrePlaced]
    at hmismatch hmatch ⊢
  have hpre := stageP2_matched_0868_to_094c_placed hser hdealloc h_bb s0 s sp coroPtr msgPtr
    remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt outerVerByte b_4f1 baseKey
    g r sess hcur hver halice hcro htr hsp_eq hsp_root hpc hrun hsp_align
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28 hx29
  refine bind_sepWPp_steps_frame_panicF_placed hpan hpre (by sep_focus)
    fun sm hsteps01 hpcm hrunm hregsm => ?_
  rcases hregsm with ⟨hspm, htrm, hx19m, hx21m, hx25m, hx28m, hx29m, hvregsm, hcrom⟩
  have hspm_align : (sm.sp &&& 15#64 == 0#64) = true := by rw [hspm, ← hsp_eq]; exact hsp_align
  have htr0m : s0.trace <+: sm.trace := by rw [htrm]; exact htr
  sep_norm
  refine SepWPp.exists_elim fun recG => SepWPp.pure_elim fun ⟨hgc, hextra⟩ => ?_
  by_cases hrem : sess.state.remoteIdentity = some remIdKey
  · conv =>
      arg 4
      rw [processPrekeyActive10At_eq]
    simp only [sepConj_assoc]
    have hm := stageP2_matched_094c_match_placed (A := A) (s0 := s0)
      h_bb sm sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr v_330 v_388
      u_80 u_88 u_90 u_a8 u_b0 v_d0 u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
      u_2a8 u_b8 innerVerByte b_4f2 b_390 b_3ac remIdKey recG sess.state hrem
      hcrom hspm hsp_root hpcm hrunm hspm_align hx19m hx21m hx25m hx28m
    refine bind_sepWPp_steps_frame_panicF_placed hpan hm (by sep_focus)
      fun s2 hsteps12 hpc2 hrun2 hregs2 => ?_
    rcases hregs2 with ⟨hsp2, htr2, hx19_2, hx27_2, hx29_2, hvregs2, hcro2⟩
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
    sep_norm
    refine SepWPp.exists_elim fun opkHi => SepWPp.exists_elim fun kyberPacked => ?_
    have hgoal := hmatch hrem s2 recG opkHi
      (kyberPacked.extractLsb' 0 32) (kyberPacked.extractLsb' 32 32)
      hgc hextra (hsteps01.trans hsteps12) hpc2 hrun2 hsp2 hsp2_align
      (htr2.trans htrm) hx19_2 hx27_2 (hx29_2.trans hx29m) (hvregs2.trans hvregsm) hcro2
    refine fun R hmR hL => hgoal R (Arm64.Satisfies.mono (sepConj_mono_left ?_) hmR) hL
    rw [coro_2a0_split32_placed coroPtr kyberPacked, processPrekeyActive10At_eq]
    simp only [sepConj_assoc]
    exact Entails.of_eq (eq_of_sep_emp (by sep_focus))
  · conv =>
      arg 4
      rw [processPrekeyActive10At_eq]
    simp only [sepConj_assoc]
    have hmm := stageP2_matched_094c_mismatch_placed hto hdealloc h_bb hdrop_ss s0 sm
      sp coroPtr outPtr msgPtr u_a8 v_d0 b_4f2 b_390 b_2c0 remIdKey g recG sess.state
      hrem hcrom htr0m hspm hsp_root hpcm hrunm hspm_align hx19m hx21m hx25m hx28m
    refine bind_sepWPp_steps_frame_panicF_placed hpan hmm (by sep_focus)
      fun sf hsteps1f hpcf hrunf hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hcsf, hvregsf, hcrof⟩
    refine SepWPp.done hpcf hrunf (hmismatch hrem sf _ hpcf hrunf
      (hsteps01.trans hsteps1f) hspf (htrf.trans htrm) hcsf (hvregsf.trans hvregsm) hcrof ?_)
    rw [processPrekeyActive10At_eq]
    simp only [sepConj_assoc]
    exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

/-- Relocatable `[LibsignalPlacement]` top-level Stage P2 matched-session contract
(`(blkPl_518).base + 0x0868 → +0x1778` / `s0.readReg64 .x30`). -/
theorem stageP2_matched_ok_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Q Qp : State → SepProp → Prop}
    (hser : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec A)))
    (hto : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (strToOwnedLocal2Spec A)))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    (h_bb : Rust.withPanics ext lsBlackBoxU8Sym = some blackBoxHook)
    (hdrop_ss : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
      v_330 v_388 u_80 u_88 u_90 u_a8 u_b0 v_d0
      u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (u_2a8 u_b8 : BitVec 32)
    (outerVerByte innerVerByte b_4f1 b_4f2 b_390 b_2c0 b_3ac : BitVec 8)
    (baseKey : PublicKey) (remIdKey : IdentityKey)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (F : SepProp)
    (hcur : r.currentSession = some sess)
    (hver : sess.state.version = outerVerByte.zeroExtend 32)
    (halice : sess.aliceBaseKey = baseKey.serialize)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s0.trace <+: s.trace)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hx29 : s.readReg64 .x29 = sp + 0xc70#64)
    (hpan : ∀ sf Pf,
      CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0 sf Pf → Qp sf Pf)
    (hmismatch : sess.state.remoteIdentity ≠ some remIdKey →
      ∀ (sf : State) (Pf : SepProp),
        sf.pc = s0.readReg64 .x30 →
        sf.status = .Running →
        Steps (lsProg_518 (Rust.withPanics ext)) s sf →
        sf.sp = sp + 0xcd0#64 →
        sf.trace = s.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        (Pf ⊢ stageP2MatchedMismatchPostPlaced A s0 sp coroPtr outPtr msgPtr
          remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
          kyberStorePtr kyberStoreVt v_330 v_388 u_80 u_88 u_90 u_b0
          u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
          u_2a8 u_b8 outerVerByte innerVerByte b_3ac baseKey remIdKey F) →
        Q sf Pf)
    (hmatch : sess.state.remoteIdentity = some remIdKey →
      ∀ (s2 : State) (recG : SessionGhost) (opkHi kyberPreKeyId signedPreKeyId : BitVec 32),
        g.cur = some recG →
        SessionExtraRel recG sess →
        Steps (lsProg_518 (Rust.withPanics ext)) s s2 →
        s2.pc = (blkPl_518).base + 0x1778#64 →
        s2.status = .Running →
        s2.sp = sp →
        (s2.sp &&& 15#64 == 0#64) = true →
        s2.trace = s.trace →
        s2.readReg64 .x19 = coroPtr →
        s2.readReg64 .x27 = sp + 0x370#64 →
        s2.readReg64 .x29 = sp + 0xc70#64 →
        calleeSavedVRegs s2 = calleeSavedVRegs s →
        StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem →
        SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s2
          (stageP2MatchedMatchPrePlaced A s0 sp coroPtr outPtr msgPtr
            remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt v_330 v_388 v_d0
            opkHi kyberPreKeyId signedPreKeyId outerVerByte innerVerByte b_2c0
            baseKey remIdKey g recG sess.state F)
          Q Qp) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stageP2MatchedPrePlaced A s0 sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
        v_330 v_388 u_80 u_88 u_90 u_a8 u_b0 v_d0
        u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
        u_2a8 u_b8 outerVerByte innerVerByte b_4f1 b_4f2 b_390 b_2c0 b_3ac
        baseKey remIdKey g r F)
      Q Qp :=
  stageP2_matched_ok_framed_placed hser hto hdealloc h_bb hdrop_ss s0 s sp coroPtr outPtr msgPtr
    remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt v_330 v_388 u_80 u_88 u_90 u_a8 u_b0 v_d0
    u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 u_2a8 u_b8
    outerVerByte innerVerByte b_4f1 b_4f2 b_390 b_2c0 b_3ac baseKey remIdKey g r sess F
    hcur hver halice hcro htr hsp_eq hsp_root hpc hrun hsp_align
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28 hx29
    (fun sf Pf hp => hpan sf (Pf ∗ F) (panicOomProp_frame F hp)) hmismatch hmatch

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
end
