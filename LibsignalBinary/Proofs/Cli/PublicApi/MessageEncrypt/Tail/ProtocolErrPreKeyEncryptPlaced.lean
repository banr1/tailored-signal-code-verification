/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.ProtocolErrCommonPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrPreKeyEncrypt
public import ProofLib.SepLogic.WP.Apply
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable (`[LibsignalPlacement]`) T5 Kyber Tail (`tailPreKeyEncryptErr`)
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon hiding words64At pollWith otrSlotAt cmSlotAt dropRecordSlots tailRegs EncTailV EncTail TailModel

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?

set_option maxHeartbeats 800000 in
theorem kyber_placed_run [LibsignalPlacement] {A : RustAlloc} {Hk : LibsignalHooks}
    (hdealloc_sat : HookSat Hk lsRustDeallocSym (rustDeallocSpec A))
    (w0 w1 w2 w3 w4 w5 kyPtr : BitVec 64) (kp : Option KyberPayload) (s : State)
    (hpc : s.pc = encEntryPlaced + 0xc38#64) (hrun : s.status = .Running)
    (hal : s.spAligned = true) (hx29 : s.readReg64 .x29 = s.sp + 0xb80#64)
    (hregs : tailRegs w0 w1 w2 s.sp s) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0x46c#64) s
      (memRegion (s.sp + 0x9d0#64) 24 ∗ words64At (s.sp + 0xb00#64) [w3, w4, w5] ∗
        optKyberAt A (s.sp + 0x8a0#64) kyPtr kp ∗ A.pool ∗ stackAt s.sp allocHookStack)
      (fun s' P => s'.sp = s.sp ∧ s'.trace = s.trace ∧ s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s' = calleeSavedVRegs s ∧ tailRegs w0 w1 w2 s.sp s' ∧
        ∀ m F, (m ⊨ P ∗ F) →
          (m ⊨ (words64At (s.sp + 0x9d0#64) [w3, w4, w5] ∗ memRegion (s.sp + 0xb00#64) 24 ∗
            memRegion (s.sp + 0x8a0#64) 24 ∗ A.pool ∗ stackAt s.sp allocHookStack) ∗ F)) := by
  obtain ⟨hx26, hx28, hx27, hx21, hx23⟩ := hregs
  have hal' : (s.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hal
  have hdealloc : subroutine_ok ((blkPC_464).rebase (blkPl_464).base Hk)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A) :=
    ls_hook_ok_of_mem hdealloc_sat
  unfold encEntryPlaced at hpc ⊢
  rw [memRegion_24_eq]
  simp only [sepExists_sepConj_left]
  refine SepWP.exists_elim fun u2 => SepWP.exists_elim fun u1 => SepWP.exists_elim fun u0 => ?_
  simp only [words64At, sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
  dsimp only [lsProg_464, ite_true]
  cases kp with
  | none =>
    simp only [optKyberAt, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
    · unfold tailRegs
      simp only [wp_norm, arm64_norm, *]
    · intro m F hm
      have hb := words64At_three_entails (s.sp + 2816#64) w3 w4 w5
      simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd] at hb
      have hk := kyberNone_entails (s.sp + 2208#64)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hk
      simp only [sepConj_assoc] at hm
      exact Satisfies.mono (kyberPost_two hb hk) hm
  | some k =>
    simp only [optKyberAt, boxU8At, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    wp_focus_pure
    rintro ⟨hptr_ne, hlen_lt⟩
    have hptr_beq : (kyPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_ne
    by_cases hbs : k.ciphertext = []
    · simp only [hbs, List.length_nil, ite_true, emp_sepConj]
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
      · unfold tailRegs
        simp only [wp_norm, arm64_norm, *]
      · intro m F hm
        have hb := words64At_three_entails (s.sp + 2816#64) w3 w4 w5
        simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd] at hb
        have hk := kyberSome_entails (s.sp + 2208#64) kyPtr 0#64 k.preKeyId
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hk
        simp only [sepConj_assoc] at hm
        exact Satisfies.mono (kyberPost_four hb hk) hm
    · have hpos : 0 < k.ciphertext.length := List.length_pos_iff.mpr hbs
      have hlen_toNat : (BitVec.ofNat 64 k.ciphertext.length).toNat = k.ciphertext.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have hlen_ne : BitVec.ofNat 64 k.ciphertext.length ≠ 0#64 := by
        intro h
        have ht := congrArg BitVec.toNat h
        rw [hlen_toNat] at ht
        change k.ciphertext.length = 0 at ht
        omega
      have hlen_beq0 : (BitVec.ofNat 64 k.ciphertext.length == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hlen_ne
      simp only [hbs, ite_false]
      refine SepWP.weaken_pre
        (by have _ := pointsToBytes_entails_memRegion kyPtr k.ciphertext; sep_frame) ?_
      wp_steps
      wp_apply
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
      · unfold tailRegs
        simp only [wp_norm, arm64_norm, *]
      · intro m F hm
        have hb := words64At_three_entails (s.sp + 2816#64) w3 w4 w5
        simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd] at hb
        have hk := kyberSome_entails (s.sp + 2208#64) kyPtr (BitVec.ofNat 64 k.ciphertext.length)
          k.preKeyId
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hk
        simp only [sepConj_assoc] at hm
        exact Satisfies.mono (kyberPost_four' hb hk) hm

theorem tailPreKeyEncryptErrPlaced [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hdealloc_sat : HookSat Hk lsRustDeallocSym (rustDeallocSpec A))
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State}
    {answers : StoreAnswers (List (BitVec 8)) Unit} {e : ApiError AddrVal Unit}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {H : SepProp} {scratch : BitVec 64 → SepProp}
    {g : RecordGhost} {rec : SessionRecord (List (BitVec 8))}
    {ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8)))}
    {kyPtr : BitVec 64} {kp : Option KyberPayload}
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hs : EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers
      (encEntryPlaced + 0xc38#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A sp scratch g rec ot none
          (memRegion (sp + 0x46a#64) 0x436 ∗ optKyberAt A (sp + 0x8a0#64) kyPtr kp ∗
            memRegion (sp + 0x8b8#64) 0x248 ∗ words64At (sp + 0xb00#64) [w3, w4, w5] ∗
            memRegion (sp + 0xb18#64) 0x68) ∗ H)
      R s0 s)
    (hT1 : ∀ s', TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s' →
      EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers
        (encEntryPlaced + 0x46c#64) (tailRegs w0 w1 w2)
        (fun sp => dropRecordSlots A sp scratch g rec ot none (pollWith sp 0x9d0 [w3, w4, w5]) ∗ H)
        R s0 s' →
      SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s' (fun _ => False)) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s (fun _ => False) := by
  have hn : allocHookStack ≤ encSubStack := by decide
  refine segExit_placed_of_run hm (fun hL => ?_) hT1
  refine encTail_placed_run_withEncCommon (C := C) (Hk := Hk)
    (Act := memRegion (s0.sp - 0xbe0#64 + 0x9d0#64) 24 ∗
      words64At (s0.sp - 0xbe0#64 + 0xb00#64) [w3, w4, w5] ∗
      optKyberAt A (s0.sp - 0xbe0#64 + 0x8a0#64) kyPtr kp ∗ A.pool ∗
      stackAt (s0.sp - 0xbe0#64) allocHookStack)
    (Act' := words64At (s0.sp - 0xbe0#64 + 0x9d0#64) [w3, w4, w5] ∗
      memRegion (s0.sp - 0xbe0#64 + 0xb00#64) 24 ∗ memRegion (s0.sp - 0xbe0#64 + 0x8a0#64) 24 ∗
      A.pool ∗ stackAt (s0.sp - 0xbe0#64) allocHookStack)
    (Fr := (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x436 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x8b8#64) 0x118 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x118 ∗
        memRegion (s0.sp - 0xbe0#64 + 0xb18#64) 0x68) ∗
      dropRecordBase A (s0.sp - 0xbe0#64) scratch g rec ot ∗ cmSlotAt A (s0.sp - 0xbe0#64) none ∗
      H ∗ encCommonPlacedFr A ctl x (x.draws S answers) s0 allocHookStack)
    hs ?_ ?_ ?_ hL
  · refine Entails.of_eq ?_
    rw [dropRecordSlots_eq, encCommonPlaced_eq A ctl x (x.draws S answers) s0 _ hn, kyberPoll_eq]
    sep_ac_rfl
  · refine Entails.of_eq ?_
    rw [dropRecordSlots_eq, encCommonPlaced_eq A ctl x (x.draws S answers) s0 _ hn, kyberDropRecordPoll_eq]
    sep_ac_rfl
  · intro hpc hmeta hregs
    obtain ⟨hrun, hssp, _, hspal, hx29, -⟩ := hmeta
    rw [← hssp] at hregs ⊢
    exact kyber_placed_run hdealloc_sat w0 w1 w2 w3 w4 w5 kyPtr kp s hpc hrun hspal
      (by rw [hx29, hssp]; bv_omega) hregs

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr
