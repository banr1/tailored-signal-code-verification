/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitChain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-!
# `DhStep` Pure Unfolding & Error-Exit Branch Proofs

Pure `RatchetState.dhRatchetStep` unfolding lemmas, error-tail staging (`+0x2dc → +0x30c` and
`+0x7f8 → +0x30c`), `missingSenderChain` handling, and post-`create_chain` #1 branch lemmas.

## `RatchetState.dhRatchetStep` Pure Unfolding Lemmas
-/

theorem sat_sub_one_eq (idx : BitVec 32) :
    (if idx = 0 then 0 else idx - 1) = BitVec.ofNat 32 (idx.toNat - 1) := by
  by_cases h : idx = 0
  · subst h; rfl
  · simp only [h, ↓reduceIte]
    have hpos : 1 ≤ idx.toNat := Nat.pos_of_ne_zero (fun h0 => h (BitVec.eq_of_toNat_eq h0))
    have hlt := idx.isLt
    apply BitVec.eq_of_toNat_eq
    have h1 : (idx - 1).toNat = idx.toNat - 1 := by
      change (idx - 1#32).toNat = idx.toNat - 1
      rw [BitVec.toNat_sub_of_le]
      · rfl
      · rw [BitVec.le_def]; exact hpos
    rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem dhRatchetStep_none (C : Crypto) (srk : PublicKey) (coins : BitVec 256) (r : RatchetState)
    (hsc : r.senderChain = none) :
    Mut.exec (RatchetState.dhRatchetStep C srk coins) r =
      (.error (.invalidSessionStructure .missingSenderChain), r) := by
  rcases r with ⟨rk, scOpt, rcs, pc, mfj⟩
  simp only at hsc
  subst hsc
  rfl

theorem dhRatchetStep_some_eq (C : Crypto) (srk : PublicKey) (coins : BitVec 256) (r : RatchetState)
    (sc : SenderChain) (hsc : r.senderChain = some sc) :
    Mut.exec (RatchetState.dhRatchetStep C srk coins) r =
      match rootCreateChain C r.rootKey srk sc.ratchetKey.privateKey with
      | .error e => (.error e, { r with rootKey := 0 })
      | .ok (newRootKey, receiverChainKey) =>
        match rootCreateChain C newRootKey srk (KeyPair.generate C coins).privateKey with
        | .error e => (.error e, { r with rootKey := 0 })
        | .ok (finalRootKey, senderChainKey) =>
          (.ok receiverChainKey,
           { r with
             senderChain := some ⟨KeyPair.generate C coins, senderChainKey⟩
             rootKey := finalRootKey
             previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
             receiverChains :=
               RatchetState.evictReceiverChains
                 (r.receiverChains ++ [{ senderRatchetKey := srk, chainKey := some receiverChainKey, messageKeys := [] }]) }) := by
  rcases r with ⟨rk, scOpt, rcs, pc, mfj⟩
  simp only at hsc
  subst hsc
  unfold Mut.exec RatchetState.dhRatchetStep RatchetState.takeRootKey
  dsimp only [Bind.bind, ExceptT.bind, ExceptT.mk, StateT.bind, ExceptT.run, StateT.run,
    MonadState.get, getThe, MonadStateOf.get, StateT.get, MonadLift.monadLift, monadLift,
    ExceptT.lift, liftM, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    modify, MonadState.set, StateT.set, StateT.map, Pure.pure, ExceptT.pure, StateT.pure,
    Functor.map, ExceptT.map, ExceptT.bindCont, throw, throwThe, MonadExceptOf.throw,
    liftE, Id.run]
  cases rootCreateChain C rk srk sc.ratchetKey.privateKey with
  | error e => rfl
  | ok p1 =>
    rcases p1 with ⟨newRootKey, receiverChainKey⟩
    dsimp only [StateT.bind, StateT.pure, ExceptT.bindCont, modify, MonadState.set, StateT.set,
      ExceptT.lift, MonadLift.monadLift, monadLift, liftM, StateT.map, Functor.map, ExceptT.map,
      Pure.pure, ExceptT.pure, ExceptT.mk, ExceptT.run]
    cases rootCreateChain C newRootKey srk (KeyPair.generate C coins).privateKey with
    | error e => rfl
    | ok p2 =>
      rcases p2 with ⟨finalRootKey, senderChainKey⟩
      rw [sat_sub_one_eq]
      rfl

theorem dhRatchetStep_some_err1 (C : Crypto) (srk : PublicKey) (coins : BitVec 256) (r : RatchetState)
    (sc : SenderChain) (e : SignalProtocolError)
    (hsc : r.senderChain = some sc)
    (hcc1 : rootCreateChain C r.rootKey srk sc.ratchetKey.privateKey = .error e) :
    Mut.exec (RatchetState.dhRatchetStep C srk coins) r =
      (.error e, { r with rootKey := 0 }) := by
  rw [dhRatchetStep_some_eq C srk coins r sc hsc, hcc1]

theorem dhRatchetStep_some_err2 (C : Crypto) (srk : PublicKey) (coins : BitVec 256) (r : RatchetState)
    (sc : SenderChain) (newRootKey : RootKey) (receiverChainKey : ChainKey) (e : SignalProtocolError)
    (hsc : r.senderChain = some sc)
    (hcc1 : rootCreateChain C r.rootKey srk sc.ratchetKey.privateKey = .ok (newRootKey, receiverChainKey))
    (hcc2 : rootCreateChain C newRootKey srk (KeyPair.generate C coins).privateKey = .error e) :
    Mut.exec (RatchetState.dhRatchetStep C srk coins) r =
      (.error e, { r with rootKey := 0 }) := by
  rw [dhRatchetStep_some_eq C srk coins r sc hsc, hcc1]
  dsimp only
  rw [hcc2]

theorem dhRatchetStep_some_ok (C : Crypto) (srk : PublicKey) (coins : BitVec 256) (r : RatchetState)
    (sc : SenderChain) (newRootKey finalRootKey : RootKey) (receiverChainKey senderChainKey : ChainKey)
    (hsc : r.senderChain = some sc)
    (hcc1 : rootCreateChain C r.rootKey srk sc.ratchetKey.privateKey = .ok (newRootKey, receiverChainKey))
    (hcc2 : rootCreateChain C newRootKey srk (KeyPair.generate C coins).privateKey = .ok (finalRootKey, senderChainKey)) :
    Mut.exec (RatchetState.dhRatchetStep C srk coins) r =
      (.ok receiverChainKey,
       { r with
         senderChain := some ⟨KeyPair.generate C coins, senderChainKey⟩
         rootKey := finalRootKey
         previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
         receiverChains :=
           RatchetState.evictReceiverChains
             (r.receiverChains ++ [{ senderRatchetKey := srk, chainKey := some receiverChainKey, messageKeys := [] }]) }) := by
  rw [dhRatchetStep_some_eq C srk coins r sc hsc, hcc1]
  dsimp only
  rw [hcc2]

theorem decryptDraws_of_senderChain_none (C : Crypto) (st st1 : SessionState (List (BitVec 8)))
    (tr : TripleRatchet (List (BitVec 8))) (srk : PublicKey) (rest : List (BitVec 8))
    (hfrom : Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1))
    (hfind : tr.ratchet.findReceiverChainKey srk = .ok none)
    (hsc : tr.ratchet.senderChain = none) :
    decryptDraws C st srk rest = 0 := by
  rw [decryptDraws_eq_of_fromSessionState C st st1 tr srk rest hfrom hfind, hsc]

theorem decryptDraws_of_cc1_err (C : Crypto) (st st1 : SessionState (List (BitVec 8)))
    (tr : TripleRatchet (List (BitVec 8))) (srk : PublicKey) (rest : List (BitVec 8))
    (sc : SenderChain) (e : SignalProtocolError)
    (hfrom : Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1))
    (hfind : tr.ratchet.findReceiverChainKey srk = .ok none)
    (hsc : tr.ratchet.senderChain = some sc)
    (hcc1 : rootCreateChain C tr.ratchet.rootKey srk sc.ratchetKey.privateKey = .error e) :
    decryptDraws C st srk rest = 0 := by
  rw [decryptDraws_eq_of_fromSessionState C st st1 tr srk rest hfrom hfind, hsc]
  dsimp only
  rw [hcc1]

theorem decryptDraws_of_cc1_ok (C : Crypto) (st st1 : SessionState (List (BitVec 8)))
    (tr : TripleRatchet (List (BitVec 8))) (srk : PublicKey) (rest : List (BitVec 8))
    (sc : SenderChain) (newRootKey : RootKey) (receiverChainKey : ChainKey)
    (hfrom : Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1))
    (hfind : tr.ratchet.findReceiverChainKey srk = .ok none)
    (hsc : tr.ratchet.senderChain = some sc)
    (hcc1 : rootCreateChain C tr.ratchet.rootKey srk sc.ratchetKey.privateKey = .ok (newRootKey, receiverChainKey)) :
    decryptDraws C st srk rest = min 32 rest.length := by
  rw [decryptDraws_eq_of_fromSessionState C st st1 tr srk rest hfrom hfind, hsc]
  dsimp only
  rw [hcc1]

theorem keyToBytes32_zero : keyToBytes32 (0 : RootKey) = List.replicate 32 0#8 := by
  decide +kernel

theorem pointsTo64_zero_8 (p : BitVec 64) :
    (p ↦₆₄ 0#64) = (p ↦ₛ List.replicate 8 0#8) := by
  have h8 : unpack64 0#64 = List.replicate 8 0#8 := by decide
  rw [pointsTo64_eq_pointsToBytes, h8]

theorem pointsTo64_pair_eq_pointsTo128 (a : BitVec 64) (w0 w1 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) = (a ↦₁₂₈ (w1 ++ w0)) := by
  unfold pointsTo128
  have h0 : (w1 ++ w0).extractLsb' 0 64 = w0 := by bv_kernel
  have h1 : (w1 ++ w0).extractLsb' 64 64 = w1 := by bv_kernel
  rw [h0, h1]

theorem pointsTo128_zero_16 (p : BitVec 64) :
    (p ↦₁₂₈ 0#128) = (p ↦ₛ List.replicate 16 0#8) := by
  rw [show (0#128 : BitVec 128) = 0#64 ++ 0#64 from rfl, ← pointsTo64_pair_eq_pointsTo128 p 0#64 0#64,
      pointsTo64_zero_8 p, pointsTo64_zero_8 (p + 8#64)]
  have h16 : List.replicate 16 0#8 = List.replicate 8 0#8 ++ List.replicate 8 0#8 := rfl
  have hlen : (List.replicate 8 0#8).length = 8 := rfl
  rw [h16, pointsToBytes_append, hlen]

theorem pointsTo128_zero_32 (p : BitVec 64) :
    ((p ↦₁₂₈ 0#128) ∗ ((p + 16#64) ↦₁₂₈ 0#128)) = (p ↦ₛ keyToBytes32 (0 : RootKey)) := by
  rw [keyToBytes32_zero, pointsTo128_zero_16 p, pointsTo128_zero_16 (p + 16#64)]
  have h16 : List.replicate 32 0#8 = List.replicate 16 0#8 ++ List.replicate 16 0#8 := rfl
  have hlen : (List.replicate 16 0#8).length = 16 := rfl
  rw [h16, pointsToBytes_append, hlen]

/-! ## 6. First Half of `DhStepSpec` (`+0x500 → +0x8ac` and Error Exits `→ +0x30c`) -/

private theorem rodata_missingSenderChain_bytes :
    (libsignalSessionImage.data.drop (num% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1780) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1784)) - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 20 =
      invalidSessionStructureStr .missingSenderChain := by
  rfl_kernel

private theorem rodata_missingSenderChain_mem :
    (num% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1780) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1784)), 20) ∈ libsignalSessionImage.roData := by
  decide +kernel

theorem satisfies_rodata_missingSenderChain {img : Obj.Image} {m : Memory} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1780) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1784))) ↦ᵣ invalidSessionStructureStr .missingSenderChain) ∗ P := by
  obtain ⟨hm_ro, hm_read⟩ :=
    ProofLib.ObjectLoad.rodata_readBytes_disjoint himg rfl rodata_missingSenderChain_mem
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) m hro
  change m.readBytes (img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1780) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1784))) 20 =
    (libsignalSessionImage.data.drop (num% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1780) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1784)) - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 20 at hm_read
  rw [rodata_missingSenderChain_bytes] at hm_read
  have hlen : (invalidSessionStructureStr .missingSenderChain).length = 20 := issStr_lengths.1
  refine Satisfies.rodata_intro ?_ ?_ (by rw [hlen]; decide) hP
  · rwa [hlen]
  · rwa [hlen]

theorem reassoc_4_8_8_to_8_8_4 (a : BitVec 64) (w0 : BitVec 32) (q0 q1 : BitVec 64) :
    ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₆₄ q0) ∗ ((a + 12#64) ↦₆₄ q1)) =
      ((a ↦₆₄ (q0.extractLsb' 0 32 ++ w0)) ∗
       ((a + 8#64) ↦₆₄ (q1.extractLsb' 0 32 ++ q0.extractLsb' 32 32)) ∗
       ((a + 16#64) ↦₃₂ q1.extractLsb' 32 32)) := by
  have h4 : (a + 4#64) + 4#64 = a + 8#64 := by bv_arith
  have h8 : (a + 8#64) + 4#64 = a + 12#64 := by bv_arith
  have h12 : (a + 12#64) + 4#64 = a + 16#64 := by bv_arith
  rw [pointsTo64_split32 (a + 4#64) q0, pointsTo64_split32 (a + 12#64) q1, h4, h12,
      ← pointsTo32_pair a w0 (q0.extractLsb' 0 32),
      ← pointsTo32_pair (a + 8#64) (q0.extractLsb' 32 32) (q1.extractLsb' 0 32), h8]
  ac_rfl

/-- Shared error-tail staging block `+0x2dc → +0x30c`:
copies the 16-byte pair `(w2c0, w2c8)` from `sp + 0x2c0..0x2d0` to `sp + 0x168..0x178` and
leaves `sp + 0x178..0x190` (`24` B) and `sp + 0x190..0x580` (`0x3f0` B) as `memRegion`. -/
theorem dhStep_err_tail_from_2dc {img : Obj.Image} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (w2c0 w2c8 : BitVec 64) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = tryDecryptEntry img + 0x2dc#64)
    (hmeta : tryDecryptMidMeta img s0 s)
    (hx12 : s.readReg64 .x12 = s0.sp - 1504#64 + 0x2c0#64)
    (hx20 : s.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hmem : s.mem ⊨
      memRegion (s0.sp - 1504#64 + 0x140#64) 0x180 ∗
      ((s0.sp - 1504#64 + 0x2c0#64) ↦₆₄ w2c0) ∗
      ((s0.sp - 1504#64 + 0x2c8#64) ↦₆₄ w2c8) ∗
      memRegion (s0.sp - 1504#64 + 0x2d0#64) 0x2b0 ∗ Rest)
    (hcode : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      s'.pc = errTailPC img ∧
      tryDecryptMidMeta img s0 s' ∧
      s'.readReg64 .x19 = s.readReg64 .x19 ∧
      s'.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64 ∧
      s'.readReg64 .x26 = s.readReg64 .x26 ∧
      (s'.mem ⊨
        memRegion (s0.sp - 1504#64 + 0x140#64) 0x28 ∗
        ((s0.sp - 1504#64 + 0x168#64) ↦₆₄ w2c0) ∗
        ((s0.sp - 1504#64 + 0x170#64) ↦₆₄ w2c8) ∗
        memRegion (s0.sp - 1504#64 + 0x178#64) 24 ∗
        memRegion (s0.sp - 1504#64 + 0x190#64) 0x3f0 ∗ Rest) := by
  have hentry := entryOf_eq_tripleRatchetProgAtExt ext himg tryDecryptName
  unfold tryDecryptEntry at hpc
  rw [hentry] at hpc
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hfr, hsym, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hfn : libsignalSessionCode.fnOff tryDecryptName = num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  td_fetches img.base (Rust.withPanics ext) hfn 732 48

  have h140_split : memRegion (sp + 0x140#64) 0x180 =
      memRegion (sp + 0x140#64) 0x28 ∗
      (∃∗ u168 : BitVec 64, (sp + 0x168#64) ↦₆₄ u168) ∗
      (∃∗ u170 : BitVec 64, (sp + 0x170#64) ↦₆₄ u170) ∗
      (∃∗ u178 : BitVec 64, (sp + 0x178#64) ↦₆₄ u178) ∗
      (∃∗ u180 : BitVec 64, (sp + 0x180#64) ↦₆₄ u180) ∗
      (∃∗ u188 : BitVec 32, (sp + 0x188#64) ↦₃₂ u188) ∗
      (∃∗ u18c : BitVec 32, (sp + 0x18c#64) ↦₃₂ u18c) ∗
      memRegion (sp + 0x190#64) 0x120 ∗
      (∃∗ u2b0 : BitVec 64, (sp + 0x2b0#64) ↦₆₄ u2b0) ∗
      (∃∗ u2b8 : BitVec 64, (sp + 0x2b8#64) ↦₆₄ u2b8) := by
    rw [memRegion_split' (b' := sp + 0x168#64) (n := 0x28) (k := 0x158) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x168#64) (b' := sp + 0x170#64) (n := 0x8) (k := 0x150) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x170#64) (b' := sp + 0x178#64) (n := 0x8) (k := 0x148) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x178#64) (b' := sp + 0x180#64) (n := 0x8) (k := 0x140) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x180#64) (b' := sp + 0x188#64) (n := 0x8) (k := 0x138) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x188#64) (b' := sp + 0x18c#64) (n := 0x4) (k := 0x134) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x18c#64) (b' := sp + 0x190#64) (n := 0x4) (k := 0x130) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x190#64) (b' := sp + 0x2b0#64) (n := 0x120) (k := 0x10) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x2b0#64) (b' := sp + 0x2b8#64) (n := 0x8) (k := 0x8) rfl (by bv_arith) (by decide),
        memRegion_eight (sp + 0x168#64), memRegion_eight (sp + 0x170#64),
        memRegion_eight (sp + 0x178#64), memRegion_eight (sp + 0x180#64),
        memRegion_four (sp + 0x188#64), memRegion_four (sp + 0x18c#64),
        memRegion_eight (sp + 0x2b0#64), memRegion_eight (sp + 0x2b8#64)]
  have h2d0_split : memRegion (sp + 0x2d0#64) 0x2b0 =
      (∃∗ u2d0 : BitVec 32, (sp + 0x2d0#64) ↦₃₂ u2d0) ∗
      memRegion (sp + 0x2d4#64) 0x5c ∗
      (∃∗ u330 : BitVec 64, (sp + 0x330#64) ↦₆₄ u330) ∗
      (∃∗ u338 : BitVec 64, (sp + 0x338#64) ↦₆₄ u338) ∗
      (∃∗ u340 : BitVec 32, (sp + 0x340#64) ↦₃₂ u340) ∗
      (∃∗ u344 : BitVec 64, (sp + 0x344#64) ↦₆₄ u344) ∗
      (∃∗ u34c : BitVec 64, (sp + 0x34c#64) ↦₆₄ u34c) ∗
      memRegion (sp + 0x354#64) 0x22c := by
    rw [memRegion_split' (b := sp + 0x2d0#64) (b' := sp + 0x2d4#64) (n := 0x4) (k := 0x2ac) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x2d4#64) (b' := sp + 0x330#64) (n := 0x5c) (k := 0x250) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x330#64) (b' := sp + 0x338#64) (n := 0x8) (k := 0x248) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x338#64) (b' := sp + 0x340#64) (n := 0x8) (k := 0x240) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x340#64) (b' := sp + 0x344#64) (n := 0x4) (k := 0x23c) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x344#64) (b' := sp + 0x34c#64) (n := 0x8) (k := 0x234) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x34c#64) (b' := sp + 0x354#64) (n := 0x8) (k := 0x22c) rfl (by bv_arith) (by decide),
        memRegion_four (sp + 0x2d0#64), memRegion_eight (sp + 0x330#64),
        memRegion_eight (sp + 0x338#64), memRegion_four (sp + 0x340#64),
        memRegion_eight (sp + 0x344#64), memRegion_eight (sp + 0x34c#64)]
  rw [h140_split, h2d0_split] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u34c, u344, u340, u338, u330, u2d0, u2b8, u2b0, u18c, u188, u180, u178, u170, u168, hmem⟩

  have hwp : SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 780#64) s
      ((memRegion (sp + 0x140#64) 0x28 ∗
        (sp + 0x168#64) ↦₆₄ u168 ∗
        (sp + 0x170#64) ↦₆₄ u170 ∗
        (sp + 0x178#64) ↦₆₄ u178 ∗
        (sp + 0x180#64) ↦₆₄ u180 ∗
        (sp + 0x188#64) ↦₃₂ u188 ∗
        (sp + 0x18c#64) ↦₃₂ u18c ∗
        memRegion (sp + 0x190#64) 0x120 ∗
        (sp + 0x2b0#64) ↦₆₄ u2b0 ∗
        (sp + 0x2b8#64) ↦₆₄ u2b8) ∗
       (sp + 0x2c0#64) ↦₆₄ w2c0 ∗
       (sp + 0x2c8#64) ↦₆₄ w2c8 ∗
       ((sp + 0x2d0#64) ↦₃₂ u2d0 ∗
        memRegion (sp + 0x2d4#64) 0x5c ∗
        (sp + 0x330#64) ↦₆₄ u330 ∗
        (sp + 0x338#64) ↦₆₄ u338 ∗
        (sp + 0x340#64) ↦₃₂ u340 ∗
        (sp + 0x344#64) ↦₆₄ u344 ∗
        (sp + 0x34c#64) ↦₆₄ u34c ∗
        memRegion (sp + 0x354#64) 0x22c))
      (fun sf P_f =>
        sf.sp = s0.sp - 1504#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        (∀ m R, (m ⊨ P_f ∗ R) →
          (m ⊨ (memRegion (sp + 0x140#64) 0x28 ∗
                ((sp + 0x168#64) ↦₆₄ w2c0) ∗
                ((sp + 0x170#64) ↦₆₄ w2c8) ∗
                memRegion (sp + 0x178#64) 24 ∗
                memRegion (sp + 0x190#64) 0x3f0) ∗ R))) := by
    dsimp only [tripleRatchetProgAtExt] at *
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr tryDecryptName = entry
    wp_steps
    have hre : ((sp + 832#64) ↦₃₂ u2d0 ∗ (sp + 836#64) ↦₆₄ u2b0 ∗ (sp + 844#64) ↦₆₄ u2b8 ∗ memRegion (sp + 852#64) 556) =
        ((sp + 832#64) ↦₆₄ (u2b0.extractLsb' 0 32 ++ u2d0) ∗
         (sp + 840#64) ↦₆₄ (u2b8.extractLsb' 0 32 ++ u2b0.extractLsb' 32 32) ∗
         (sp + 848#64) ↦₃₂ u2b8.extractLsb' 32 32 ∗
         memRegion (sp + 852#64) 556) := by
      have := congrArg (· ∗ memRegion (sp + 852#64) 556) (reassoc_4_8_8_to_8_8_4 (sp + 832#64) u2d0 u2b0 u2b8)
      have h1 : sp + 832#64 + 4#64 = sp + 836#64 := by bv_arith
      have h2 : sp + 832#64 + 12#64 = sp + 844#64 := by bv_arith
      have h3 : sp + 832#64 + 8#64 = sp + 840#64 := by bv_arith
      have h4 : sp + 832#64 + 16#64 = sp + 848#64 := by bv_arith
      rw [h1, h2, h3, h4] at this
      exact Eq.trans (by ac_rfl) (Eq.trans this (by ac_rfl))
    rw [hre]
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx29], by simp, by simp [hx20, sp], by simp, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    have h178_fold : memRegion (sp + 0x178#64) 24 =
        memRegion (sp + 376#64) 8 ∗
        memRegion (sp + 384#64) 8 ∗
        memRegion (sp + 392#64) 4 ∗
        memRegion (sp + 396#64) 4 := by
      rw [show sp + 0x178#64 = sp + 376#64 from rfl,
          memRegion_split' (b := sp + 376#64) (b' := sp + 384#64) (n := 8) (k := 16) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 384#64) (b' := sp + 392#64) (n := 8) (k := 8) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 392#64) (b' := sp + 396#64) (n := 4) (k := 4) rfl (by bv_arith) (by decide)]
    have h190_fold : memRegion (sp + 0x190#64) 0x3f0 =
        memRegion (sp + 400#64) 288 ∗
        memRegion (sp + 688#64) 8 ∗
        memRegion (sp + 696#64) 8 ∗
        memRegion (sp + 704#64) 8 ∗
        memRegion (sp + 712#64) 8 ∗
        memRegion (sp + 720#64) 4 ∗
        memRegion (sp + 724#64) 92 ∗
        memRegion (sp + 816#64) 8 ∗
        memRegion (sp + 824#64) 8 ∗
        memRegion (sp + 832#64) 8 ∗
        memRegion (sp + 840#64) 8 ∗
        memRegion (sp + 848#64) 4 ∗
        memRegion (sp + 852#64) 556 := by
      rw [show sp + 0x190#64 = sp + 400#64 from rfl,
          memRegion_split' (b := sp + 400#64) (b' := sp + 688#64) (n := 288) (k := 720) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 688#64) (b' := sp + 696#64) (n := 8) (k := 712) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 696#64) (b' := sp + 704#64) (n := 8) (k := 704) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 704#64) (b' := sp + 712#64) (n := 8) (k := 696) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 712#64) (b' := sp + 720#64) (n := 8) (k := 688) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 720#64) (b' := sp + 724#64) (n := 4) (k := 684) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 724#64) (b' := sp + 816#64) (n := 92) (k := 592) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 816#64) (b' := sp + 824#64) (n := 8) (k := 584) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 824#64) (b' := sp + 832#64) (n := 8) (k := 576) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 832#64) (b' := sp + 840#64) (n := 8) (k := 568) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 840#64) (b' := sp + 848#64) (n := 8) (k := 560) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 848#64) (b' := sp + 852#64) (n := 4) (k := 556) rfl (by bv_arith) (by decide)]
    rw [h178_fold, h190_fold]
    change m ⊨ _
    arm64_sep_close
  have hmem_framed : s.mem ⊨
      (((memRegion (sp + 0x140#64) 0x28 ∗
        (sp + 0x168#64) ↦₆₄ u168 ∗
        (sp + 0x170#64) ↦₆₄ u170 ∗
        (sp + 0x178#64) ↦₆₄ u178 ∗
        (sp + 0x180#64) ↦₆₄ u180 ∗
        (sp + 0x188#64) ↦₃₂ u188 ∗
        (sp + 0x18c#64) ↦₃₂ u18c ∗
        memRegion (sp + 0x190#64) 0x120 ∗
        (sp + 0x2b0#64) ↦₆₄ u2b0 ∗
        (sp + 0x2b8#64) ↦₆₄ u2b8) ∗
       (sp + 0x2c0#64) ↦₆₄ w2c0 ∗
       (sp + 0x2c8#64) ↦₆₄ w2c8 ∗
       ((sp + 0x2d0#64) ↦₃₂ u2d0 ∗
        memRegion (sp + 0x2d4#64) 0x5c ∗
        (sp + 0x330#64) ↦₆₄ u330 ∗
        (sp + 0x338#64) ↦₆₄ u338 ∗
        (sp + 0x340#64) ↦₃₂ u340 ∗
        (sp + 0x344#64) ↦₆₄ u344 ∗
        (sp + 0x34c#64) ↦₆₄ u34c ∗
        memRegion (sp + 0x354#64) 0x22c)) ∗ Rest) := by
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hmem
  obtain ⟨s', hsteps, hout⟩ := hwp.elim hmem_framed hcode
  obtain ⟨hpcs', hruns', P_f, hmem', hsp', hx29', hx19', hx20', hx26', htrace', hvregs', hent⟩ :=
    hout.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al' : s'.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp', ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  refine ⟨s', hsteps, ?_, ⟨hruns', hsp', hsp0_al, hsp_al', hx29', htrace', hsteps.frozenLoaded hfr, hsteps.symtab_eq.trans hsym, hvregs'⟩, hx19', hx20', hx26', ?_⟩
  · unfold errTailPC tryDecryptEntry
    rw [hentry]
    exact hpcs'
  · have hm := hent s'.mem Rest hmem'
    exact Eq.mp (congrArg (s'.mem ⊨ ·) (by ac_rfl)) hm

theorem reassoc_8_8_to_4_8_4 (a : BitVec 64) (q0 q1 : BitVec 64) :
    ((a ↦₆₄ q0) ∗ ((a + 8#64) ↦₆₄ q1)) =
      ((a ↦₃₂ q0.extractLsb' 0 32) ∗
       ((a + 4#64) ↦₆₄ (q1.extractLsb' 0 32 ++ q0.extractLsb' 32 32)) ∗
       ((a + 12#64) ↦₃₂ q1.extractLsb' 32 32)) := by
  have h4 : (a + 4#64) + 4#64 = a + 8#64 := by bv_arith
  have h8 : (a + 8#64) + 4#64 = a + 12#64 := by bv_arith
  rw [pointsTo64_split32 a q0, pointsTo64_split32 (a + 8#64) q1, h8,
      ← pointsTo32_pair (a + 4#64) (q0.extractLsb' 32 32) (q1.extractLsb' 0 32), h4]
  ac_rfl

theorem reassoc_4_8_4_zero_to_8_8 (a : BitVec 64) :
    ((a ↦₃₂ 4#32) ∗ ((a + 4#64) ↦₆₄ 0#64) ∗ ((a + 12#64) ↦₃₂ 0#32)) =
      ((a ↦₆₄ 4#64) ∗ ((a + 8#64) ↦₆₄ 0#64)) :=
  (reassoc_8_8_to_4_8_4 a 4#64 0#64).symm

theorem fold_four64_memRegion32 (a : BitVec 64) (v0 v1 v2 v3 : BitVec 64) :
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3)) ⊢
      memRegion a 32 := by
  rw [memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 24) rfl (by bv_arith) (by decide),
      memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 16) rfl (by bv_arith) (by decide),
      memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k := 8) rfl (by bv_arith) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a v0)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) v1)
      (sepConj_mono (pointsTo64_entails_memRegion (a + 16#64) v2)
        (pointsTo64_entails_memRegion (a + 24#64) v3)))

theorem pointsTo64_32_entails_memRegion12 (a : BitVec 64) (v0 : BitVec 64) (v1 : BitVec 32) :
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₃₂ v1)) ⊢ memRegion a 12 := by
  rw [memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 4) rfl (by bv_arith) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a v0)
    (pointsTo32_entails_memRegion (a + 8#64) v1)

theorem split_memRegion_for_7f8 (sp : BitVec 64) :
    memRegion (sp + 0x1a0#64) 0x3e0 =
      memRegion (sp + 0x1a0#64) 0x110 ∗
      (∃∗ u2b0 : BitVec 64, (sp + 0x2b0#64) ↦₆₄ u2b0) ∗
      (∃∗ u2b8 : BitVec 64, (sp + 0x2b8#64) ↦₆₄ u2b8) ∗
      (∃∗ u2c0 : BitVec 64, (sp + 0x2c0#64) ↦₆₄ u2c0) ∗
      (∃∗ u2c8 : BitVec 64, (sp + 0x2c8#64) ↦₆₄ u2c8) ∗
      (∃∗ u2d0 : BitVec 32, (sp + 0x2d0#64) ↦₃₂ u2d0) ∗
      memRegion (sp + 0x2d4#64) 0x22c ∗
      (∃∗ u500 : BitVec 64, (sp + 0x500#64) ↦₆₄ u500) ∗
      (∃∗ u508 : BitVec 64, (sp + 0x508#64) ↦₆₄ u508) ∗
      memRegion (sp + 0x510#64) 0x70 := by
  rw [memRegion_split' (b := sp + 0x1a0#64) (b' := sp + 0x2b0#64) (n := 0x110) (k := 0x2d0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x2b0#64) (b' := sp + 0x2b8#64) (n := 0x8) (k := 0x2c8) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x2b8#64) (b' := sp + 0x2c0#64) (n := 0x8) (k := 0x2c0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x2c0#64) (b' := sp + 0x2c8#64) (n := 0x8) (k := 0x2b8) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x2c8#64) (b' := sp + 0x2d0#64) (n := 0x8) (k := 0x2b0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x2d0#64) (b' := sp + 0x2d4#64) (n := 0x4) (k := 0x2ac) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x2d4#64) (b' := sp + 0x500#64) (n := 0x22c) (k := 0x80) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x500#64) (b' := sp + 0x508#64) (n := 0x8) (k := 0x78) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x508#64) (b' := sp + 0x510#64) (n := 0x8) (k := 0x70) rfl (by bv_arith) (by decide),
      memRegion_eight (sp + 0x2b0#64), memRegion_eight (sp + 0x2b8#64),
      memRegion_eight (sp + 0x2c0#64), memRegion_eight (sp + 0x2c8#64),
      memRegion_four (sp + 0x2d0#64),
      memRegion_eight (sp + 0x500#64), memRegion_eight (sp + 0x508#64)]

/-- Shared `.invalidKeyAgreement` error-exit block `+0x7f8 → +0x2dc → +0x30c`:
loads `x26 = speTag .invalidKeyAgreement` (`speWord 10`) from `[sp + 0x198]` (`+0x7fc`),
stores to `[x26] = [sp + 0x2c0]`, `[x23]`, `[sp + 0x2d0]`, `[x25 + 0x120] = [sp + 0x2b0]`,
branches at `+0x814` (`b.ne +0x2dc`) since `speWord 10 + 2 ≠ 0`, and runs `dhStep_err_tail_from_2dc`
to reach `errTailPC img` (`+0x30c`). -/
theorem dhStep_err_tail_from_7f8 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = tryDecryptEntry img + 0x7f8#64)
    (hmeta : tryDecryptMidMeta img s0 s)
    (hx20 : s.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64)
    (hx23 : s.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hx26 : s.readReg64 .x26 = s0.sp - 1504#64 + 0x2c0#64)
    (hmem : s.mem ⊨
      memRegion (s0.sp - 1504#64 + 0x140#64) 0x58 ∗
      ((s0.sp - 1504#64 + 0x198#64) ↦₆₄ speWord 10) ∗
      memRegion (s0.sp - 1504#64 + 0x1a0#64) 0x3e0 ∗ Rest)
    (hcode : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      s'.pc = errTailPC img ∧
      tryDecryptMidMeta img s0 s' ∧
      s'.readReg64 .x19 = s.readReg64 .x19 ∧
      s'.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64 ∧
      s'.readReg64 .x26 = speTag .invalidKeyAgreement ∧
      (s'.mem ⊨
        memRegion (s0.sp - 1504#64 + 0x140#64) 0x28 ∗
        speBodyAt A (utf8 "decrypt") (s0.sp - 1504#64 + 0x168#64) .invalidKeyAgreement ∗
        memRegion (s0.sp - 1504#64 + 0x190#64) 0x3f0 ∗ Rest) := by
  have hentry := entryOf_eq_tripleRatchetProgAtExt ext himg tryDecryptName
  unfold tryDecryptEntry at hpc
  rw [hentry] at hpc
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hfr, hsym, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hfn : libsignalSessionCode.fnOff tryDecryptName = num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  td_fetches img.base (Rust.withPanics ext) hfn 2040 32
  rw [split_memRegion_for_7f8 sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u508, u500, u2d0, u2c8, u2c0, u2b8, u2b0, hmem⟩
  have hwp : SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 732#64) s
      (memRegion (sp + 0x140#64) 0x58 ∗
       ((sp + 0x198#64) ↦₆₄ speWord 10) ∗
       memRegion (sp + 0x1a0#64) 0x110 ∗
       ((sp + 0x2b0#64) ↦₆₄ u2b0) ∗
       ((sp + 0x2b8#64) ↦₆₄ u2b8) ∗
       ((sp + 0x2c0#64) ↦₆₄ u2c0) ∗
       ((sp + 0x2c8#64) ↦₆₄ u2c8) ∗
       ((sp + 0x2d0#64) ↦₃₂ u2d0) ∗
       memRegion (sp + 0x2d4#64) 0x22c ∗
       ((sp + 0x500#64) ↦₆₄ u500) ∗
       ((sp + 0x508#64) ↦₆₄ u508) ∗
       memRegion (sp + 0x510#64) 0x70)
      (fun sm P_m =>
        sm.sp = s0.sp - 1504#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x12 = s0.sp - 1504#64 + 0x2c0#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64 ∧
        sm.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64 ∧
        sm.readReg64 .x26 = speTag .invalidKeyAgreement ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        (∀ m R, (m ⊨ P_m ∗ R) →
          (m ⊨ memRegion (sp + 0x140#64) 0x440 ∗ R))) := by
    dsimp only [tripleRatchetProgAtExt] at *
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr tryDecryptName = entry
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx29], by simp [sp], by simp, by simp [hx20, sp],
       by simp [hx25, sp], rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    have h140_fold : memRegion (sp + 0x140#64) 0x440 =
        memRegion (sp + 320#64) 88 ∗
        memRegion (sp + 408#64) 8 ∗
        memRegion (sp + 416#64) 272 ∗
        memRegion (sp + 688#64) 8 ∗
        memRegion (sp + 696#64) 8 ∗
        memRegion (sp + 704#64) 8 ∗
        memRegion (sp + 712#64) 8 ∗
        memRegion (sp + 720#64) 4 ∗
        memRegion (sp + 724#64) 556 ∗
        memRegion (sp + 1280#64) 8 ∗
        memRegion (sp + 1288#64) 8 ∗
        memRegion (sp + 1296#64) 112 := by
      rw [show sp + 0x140#64 = sp + 320#64 from rfl,
          memRegion_split' (b := sp + 320#64) (b' := sp + 408#64) (n := 88) (k := 1000) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 408#64) (b' := sp + 416#64) (n := 8) (k := 992) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 416#64) (b' := sp + 688#64) (n := 272) (k := 720) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 688#64) (b' := sp + 696#64) (n := 8) (k := 712) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 696#64) (b' := sp + 704#64) (n := 8) (k := 704) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 704#64) (b' := sp + 712#64) (n := 8) (k := 696) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 712#64) (b' := sp + 720#64) (n := 8) (k := 688) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 720#64) (b' := sp + 724#64) (n := 4) (k := 684) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 724#64) (b' := sp + 1280#64) (n := 556) (k := 128) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 1280#64) (b' := sp + 1288#64) (n := 8) (k := 120) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 1288#64) (b' := sp + 1296#64) (n := 8) (k := 112) rfl (by bv_arith) (by decide)]
    rw [h140_fold]
    change m ⊨ _
    arm64_sep_close
  have hmem_framed : s.mem ⊨
      (memRegion (sp + 0x140#64) 0x58 ∗
       ((sp + 0x198#64) ↦₆₄ speWord 10) ∗
       memRegion (sp + 0x1a0#64) 0x110 ∗
       ((sp + 0x2b0#64) ↦₆₄ u2b0) ∗
       ((sp + 0x2b8#64) ↦₆₄ u2b8) ∗
       ((sp + 0x2c0#64) ↦₆₄ u2c0) ∗
       ((sp + 0x2c8#64) ↦₆₄ u2c8) ∗
       ((sp + 0x2d0#64) ↦₃₂ u2d0) ∗
       memRegion (sp + 0x2d4#64) 0x22c ∗
       ((sp + 0x500#64) ↦₆₄ u500) ∗
       ((sp + 0x508#64) ↦₆₄ u508) ∗
       memRegion (sp + 0x510#64) 0x70) ∗ Rest :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hmem
  obtain ⟨sm, hsteps1, hout⟩ := hwp.elim hmem_framed hcode
  obtain ⟨hpcm, hrunm, P_m, hmem_m, hsp_m, hx29_m, hx12_m, hx19_m, hx20_m, hx25_m, hx26_m, htrace_m, hvregs_m, hent_m⟩ :=
    hout.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_m : sm.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_m, ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hpcm' : sm.pc = tryDecryptEntry img + 0x2dc#64 := by
    unfold tryDecryptEntry; rw [hentry]; exact hpcm
  have hmeta_m : tryDecryptMidMeta img s0 sm :=
    ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hsteps1.frozenLoaded hfr, hsteps1.symtab_eq.trans hsym, hvregs_m⟩
  have hmem_m0 := hent_m sm.mem Rest hmem_m
  have h2c0_split : memRegion (sp + 0x140#64) 0x440 =
      memRegion (sp + 0x140#64) 0x180 ∗
      (∃∗ w2c0 : BitVec 64, (sp + 0x2c0#64) ↦₆₄ w2c0) ∗
      (∃∗ w2c8 : BitVec 64, (sp + 0x2c8#64) ↦₆₄ w2c8) ∗
      memRegion (sp + 0x2d0#64) 0x2b0 := by
    rw [memRegion_split' (b := sp + 0x140#64) (b' := sp + 0x2c0#64) (n := 0x180) (k := 0x2c0) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x2c0#64) (b' := sp + 0x2c8#64) (n := 0x8) (k := 0x2b8) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x2c8#64) (b' := sp + 0x2d0#64) (n := 0x8) (k := 0x2b0) rfl (by bv_arith) (by decide),
        memRegion_eight (sp + 0x2c0#64), memRegion_eight (sp + 0x2c8#64)]
  rw [h2c0_split] at hmem_m0
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem_m0
  rcases hmem_m0 with ⟨w2c8, w2c0, hmem_m0⟩
  have hmem_m' : sm.mem ⊨
      memRegion (sp + 0x140#64) 0x180 ∗
      ((sp + 0x2c0#64) ↦₆₄ w2c0) ∗
      ((sp + 0x2c8#64) ↦₆₄ w2c8) ∗
      memRegion (sp + 0x2d0#64) 0x2b0 ∗ Rest :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmem_m0
  obtain ⟨s', hsteps2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
    dhStep_err_tail_from_2dc (ext := ext)
      himg w2c0 w2c8 Rest s0 sm
      hpcm' hmeta_m hx12_m hx20_m hx25_m hmem_m' (hsteps1.codeLoaded hcode)
  refine ⟨s', Steps.trans hsteps1 hsteps2, hpcs', hmetas', hx19s'.trans hx19_m, hx20s',
    hx26s'.trans hx26_m, ?_⟩
  dsimp only [speBodyAt]
  have h168_fold : memRegion (sp + 0x168#64) 40 =
      memRegion (sp + 0x168#64) 8 ∗
      memRegion (sp + 0x170#64) 8 ∗
      memRegion (sp + 0x178#64) 24 := by
    rw [memRegion_split' (b := sp + 0x168#64) (b' := sp + 0x170#64) (n := 8) (k := 32) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x170#64) (b' := sp + 0x178#64) (n := 8) (k := 24) rfl (by bv_arith) (by decide)]
  rw [h168_fold]
  dsimp only [sp] at hmems' ⊢
  change s'.mem ⊨ _
  arm64_sep_close

theorem optSenderChainBytes_none_pointsTo32 (a : BitVec 64) (pad : List (BitVec 8)) :
    (a ↦ₛ optSenderChainBytes none pad) =
      ((a ↦₃₂ 0#32) ∗ ((a + 4#64) ↦ₛ pad)) := by
  unfold optSenderChainBytes
  have h0 : (a ↦ₛ leBytes 4 0) = (a ↦₃₂ 0#32) := by
    rw [pointsTo32_eq_pointsToBytes]
    rfl
  rw [pointsToBytes_append, show (leBytes 4 0).length = 4 from rfl, h0]

/-- When `tr.ratchet.senderChain = none`, `DhStepState` at `segDhStepPC img` (`+0x500`) branches to
`+0x6f4` (`0x34a90`), stages `("missing sender chain", 20)` at `sp + 0x2c0..0x2d0`, jumps to
`+0x2d0` (`0x3466c`, setting `x26 = speWord 20`), and runs `dhStep_err_tail_from_2dc` to reach
`errTailPC img` (`+0x30c`) in `ErrTailState` with `e = .invalidSessionStructure .missingSenderChain`
and `draws = 0`. -/
theorem dhStep_missing_sender_chain {img : Obj.Image} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State)
    (hnone : tr.ratchet.senderChain = none)
    (hs3 : DhStepState A ctl img x trG tr st1 R s0 s) :
    reaches_pc (tripleRatchetProgAtExt img.base ext) (errTailPC img) s
      (ErrTailState A ctl img x trG tr st1 (.invalidSessionStructure .missingSenderChain) 0 R s0) := by
  intro hcode
  obtain ⟨hpc, hmeta, hx12, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hmem⟩ := hs3
  have hentry := entryOf_eq_tripleRatchetProgAtExt ext himg tryDecryptName
  unfold segDhStepPC tryDecryptEntry at hpc
  rw [hentry] at hpc
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hfr, hsym, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hfn : libsignalSessionCode.fnOff tryDecryptName = num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  have hpage : img.base &&& 0xfff#64 = 0#64 :=
    ProofLib.ObjectLoad.base_aligned_of_loads himg
  td_fetches img.base (Rust.withPanics ext) hfn 1280 12
  td_fetches img.base (Rust.withPanics ext) hfn 1780 24
  td_fetches img.base (Rust.withPanics ext) hfn 720 12
  have hsc_tag : ((sp + 0x38#64 + 24#64) ↦ₛ optSenderChainBytes tr.ratchet.senderChain trG.ratchet.senderPad) =
      (((sp + 0x50#64) ↦₃₂ 0#32) ∗ ((sp + 0x54#64) ↦ₛ trG.ratchet.senderPad)) := by
    rw [hnone, show sp + 0x38#64 + 24#64 = sp + 0x50#64 by bv_arith,
        optSenderChainBytes_none_pointsTo32 (sp + 0x50#64) trG.ratchet.senderPad,
        show sp + 0x50#64 + 4#64 = sp + 0x54#64 by bv_arith]
  have h2c0_split : memRegion (sp + 0x140#64) 0x440 =
      memRegion (sp + 0x140#64) 0x180 ∗
      (∃∗ u2c0 : BitVec 64, (sp + 0x2c0#64) ↦₆₄ u2c0) ∗
      (∃∗ u2c8 : BitVec 64, (sp + 0x2c8#64) ↦₆₄ u2c8) ∗
      memRegion (sp + 0x2d0#64) 0x2b0 := by
    rw [memRegion_split' (b := sp + 0x140#64) (b' := sp + 0x2c0#64) (n := 0x180) (k := 0x2c0) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x2c0#64) (b' := sp + 0x2c8#64) (n := 0x8) (k := 0x2b8) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x2c8#64) (b' := sp + 0x2d0#64) (n := 0x8) (k := 0x2b0) rfl (by bv_arith) (by decide),
        memRegion_eight (sp + 0x2c0#64), memRegion_eight (sp + 0x2c8#64)]
  unfold trAt ratchetAt at hmem
  rw [hsc_tag, h2c0_split] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u2c8, u2c0, hmem⟩
  have hwp : SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 732#64) s
      (((sp + 0x50#64) ↦₃₂ 0#32) ∗
       memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       ((sp + 0x2c0#64) ↦₆₄ u2c0) ∗
       ((sp + 0x2c8#64) ↦₆₄ u2c8))
      (fun sm P_m =>
        sm.sp = s0.sp - 1504#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x12 = s0.sp - 1504#64 + 0x2c0#64 ∧
        sm.readReg64 .x19 = x.ret ∧
        sm.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64 ∧
        sm.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64 ∧
        sm.readReg64 .x26 = speTag (.invalidSessionStructure .missingSenderChain) ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        (∀ m R, (m ⊨ P_m ∗ R) →
          (m ⊨ (((sp + 0x50#64) ↦₃₂ 0#32) ∗
                memRegion sp 0x38 ∗
                ((sp + 0x2c0#64) ↦₆₄ (img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1780) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1784)))) ∗
                ((sp + 0x2c8#64) ↦₆₄ 20#64)) ∗ R))) := by
    dsimp only [tripleRatchetProgAtExt] at *
    have hadrp : ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr tryDecryptName + 1780#64 &&& 0xffff_ffff_ffff_f000#64) + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1780) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1784) - page% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 500)) =
        img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1780) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1784)) := by
      rw [Program.fnAddr_rebase, hfn]
      bv_kernel
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr tryDecryptName = entry
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx29], by simp [hx12, sp], by simp [hx19], by simp [hx20, sp],
       by simp [hx25, sp], rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    have hsp38_fold : memRegion sp 0x38 =
        memRegion sp 0x20 ∗
        memRegion (sp + 0x20#64) 8 ∗
        memRegion (sp + 0x28#64) 4 ∗
        memRegion (sp + 0x2c#64) 4 ∗
        memRegion (sp + 0x30#64) 8 := by
      rw [memRegion_split' (b := sp) (b' := sp + 0x20#64) (n := 0x20) (k := 0x18) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 0x20#64) (b' := sp + 0x28#64) (n := 0x8) (k := 0x10) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 0x28#64) (b' := sp + 0x2c#64) (n := 0x4) (k := 0xc) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 0x2c#64) (b' := sp + 0x30#64) (n := 0x4) (k := 0x8) rfl (by bv_arith) (by decide)]
    rw [hsp38_fold]
    change m ⊨ _
    arm64_sep_close
  have hmem_framed : s.mem ⊨
      (((sp + 0x50#64) ↦₃₂ 0#32) ∗
       memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       ((sp + 0x2c0#64) ↦₆₄ u2c0) ∗
       ((sp + 0x2c8#64) ↦₆₄ u2c8)) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       (⌜∀ sc, tr.ratchet.senderChain = some sc →
          Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
        (⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
          trG.ratchet.senderPad.length = 100 ∧ tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
         vecAt A 104 8 (chainAt A) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr
           (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
         ((sp + 0x54#64) ↦ₛ trG.ratchet.senderPad) ∗
         ((sp + 0x38#64 + 128#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) ∗
         ((sp + 0x38#64 + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
         ((sp + 0x38#64 + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗
         memRegion (sp + 0x38#64 + 172#64) 4) ∗
        vecU8At A (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
        ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
        ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) ∗
       memRegion x.ret 48 ∗
       memRegion (sp + 0x140#64) 0x180 ∗
       memRegion (sp + 0x2d0#64) 0x2b0 ∗
       tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hmem
  obtain ⟨sm, hsteps1, hout⟩ := hwp.elim hmem_framed hcode
  obtain ⟨hpcm, hrunm, P_m, hmem_m, hsp_m, hx29_m, hx12_m, hx19_m, hx20_m, hx25_m, hx26_m, htrace_m, hvregs_m, hent_m⟩ :=
    hout.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_m : sm.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_m, ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hpcm' : sm.pc = tryDecryptEntry img + 0x2dc#64 := by
    unfold tryDecryptEntry; rw [hentry]; exact hpcm
  have hmeta_m : tryDecryptMidMeta img s0 sm :=
    ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hsteps1.frozenLoaded hfr, hsteps1.symtab_eq.trans hsym, hvregs_m⟩
  have hmem_m0 := hent_m sm.mem _ hmem_m
  have hmem_m' : sm.mem ⊨
      memRegion (sp + 0x140#64) 0x180 ∗
      ((sp + 0x2c0#64) ↦₆₄ (img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1780) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1784)))) ∗
      ((sp + 0x2c8#64) ↦₆₄ 20#64) ∗
      memRegion (sp + 0x2d0#64) 0x2b0 ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x38 ∗
       tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    unfold trAt ratchetAt
    rw [hsc_tag]
    exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmem_m0
  obtain ⟨s', hsteps2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
    dhStep_err_tail_from_2dc (ext := ext)
      himg (img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1780) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1784))) 20#64
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x38 ∗
       tryDecryptCommonHeap A ctl img x 0 s0 ∗ R)
      s0 sm hpcm' hmeta_m hx12_m hx20_m hx25_m hmem_m' (hsteps1.codeLoaded hcode)
  refine ⟨s', Steps.trans hsteps1 hsteps2, Or.inl ⟨hpcs', hmetas'.1, ?_⟩⟩
  refine ⟨hpcs', hmetas', hx19s'.trans hx19_m, hx20s', hx26s'.trans hx26_m, ?_⟩
  dsimp only [speBodyAt]
  unfold strRefAt
  have hro : s'.mem ⊨ ((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1780) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1784))) ↦ᵣ invalidSessionStructureStr .missingSenderChain) ∗
      (memRegion (sp + 0x140#64) 0x28 ∗
       ((sp + 0x168#64) ↦₆₄ (img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1780) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1784)))) ∗
       ((sp + 0x170#64) ↦₆₄ 20#64) ∗
       memRegion (sp + 0x178#64) 24 ∗
       memRegion (sp + 0x190#64) 0x3f0 ∗
       (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 0x38#64) trG tr ∗
        memRegion x.ret 48 ∗
        memRegion sp 0x38 ∗
        tryDecryptCommonHeap A ctl img x 0 s0 ∗ R)) :=
    satisfies_rodata_missingSenderChain himg hmetas'.2.2.2.2.2.2.1.roData hmems'
  have hlen : BitVec.ofNat 64 (invalidSessionStructureStr .missingSenderChain).length = 20#64 := by
    rw [issStr_lengths.1]
  rw [hlen, show sp + 0x168#64 + 8#64 = sp + 0x170#64 by bv_arith,
      show sp + 0x168#64 + 16#64 = sp + 0x178#64 by bv_arith]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1780) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 1784)), ?_⟩
  dsimp only [sp] at hro ⊢
  exact Eq.mp (congrArg (s'.mem ⊨ ·) (by ac_rfl)) hro

/-- Intermediate state at `+0x70c` (`0x34aa8`) right after `RootKey::create_chain` #1 returns
`.ok (rk1, rck)` and `+0x548..+0x54c` (`ldr w8, [sp, #0x190]; tbz w8, #0, 0x34aa8`) branches to
`+0x70c`. -/
def DhStepAfterRecvChainState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (rk1 : RootKey) (rck : ChainKey)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = tryDecryptEntry img + 0x70c#64 ∧
  tryDecryptMidMeta img s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  s.readReg64 .x26 = sp + 0x2c0#64 ∧
  s.readReg64 .x27 = sp + 0x38#64 ∧
  s.readReg64 .x28 = sp + 0x2c0#64 ∧
  (s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x50 ∗
    ((sp + 0x190#64) ↦₃₂ 0#32) ∗
    ((sp + 0x194#64) ↦ₛ keyToBytes32 rk1) ∗
    ((sp + 0x1b4#64) ↦ₛ chainKeyBytes rck) ∗
    memRegion (sp + 0x1d8#64) 0x3a8 ∗
    tryDecryptCommonHeap A ctl img x 0 s0 ∗ R)

/-- Split `memRegion (sp + 0x1a0) 56` into `8 + 8 + 4 + 8 + 8 + 4 + 16` for the dummy reads at
`+0x550..+0x55c` and `+0x7e4..+0x7f0`. -/
theorem split_1a0_56 (sp : BitVec 64) :
    memRegion (sp + 0x1a0#64) 56 =
      ((∃∗ u1a0 : BitVec 64, (sp + 0x1a0#64) ↦₆₄ u1a0) ∗
       (∃∗ u1a8 : BitVec 64, (sp + 0x1a8#64) ↦₆₄ u1a8) ∗
       (∃∗ u1b0 : BitVec 32, (sp + 0x1b0#64) ↦₃₂ u1b0) ∗
       (∃∗ u1b4 : BitVec 64, (sp + 0x1b4#64) ↦₆₄ u1b4) ∗
       (∃∗ u1bc : BitVec 64, (sp + 0x1bc#64) ↦₆₄ u1bc) ∗
       (∃∗ u1c4 : BitVec 32, (sp + 0x1c4#64) ↦₃₂ u1c4) ∗
       memRegion (sp + 0x1c8#64) 16) := by
  rw [memRegion_split' (b := sp + 0x1a0#64) (b' := sp + 0x1a8#64) (n := 8) (k := 48) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x1a8#64) (b' := sp + 0x1b0#64) (n := 8) (k := 40) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x1b0#64) (b' := sp + 0x1b4#64) (n := 4) (k := 36) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x1b4#64) (b' := sp + 0x1bc#64) (n := 8) (k := 28) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x1bc#64) (b' := sp + 0x1c4#64) (n := 8) (k := 20) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x1c4#64) (b' := sp + 0x1c8#64) (n := 4) (k := 16) rfl (by bv_arith) (by decide),
      memRegion_eight (sp + 0x1a0#64), memRegion_eight (sp + 0x1a8#64),
      memRegion_four (sp + 0x1b0#64), memRegion_eight (sp + 0x1b4#64),
      memRegion_eight (sp + 0x1bc#64), memRegion_four (sp + 0x1c4#64)]

/-- Fold the `.error .invalidKeyAgreement` buffer at `sp + 0x140..0x580` into the layout expected
by `dhStep_err_tail_from_7f8`. -/
theorem fold_for_7f8 (sp : BitVec 64) (u190 : BitVec 32) (u1a0 u1a8 u1b4 u1bc : BitVec 64)
    (u1b0 u1c4 : BitVec 32) :
    (memRegion (sp + 0x140#64) 0x50 ∗
     ((sp + 0x190#64) ↦₃₂ u190) ∗
     memRegion (sp + 0x194#64) 4 ∗
     ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗
     ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗
     ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗
     ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗
     ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗
     ((sp + 0x1c4#64) ↦₃₂ u1c4) ∗
     memRegion (sp + 0x1c8#64) 16 ∗
     memRegion (sp + 0x1d8#64) 0x3a8) ⊢
    (memRegion (sp + 0x140#64) 0x58 ∗
     memRegion (sp + 0x1a0#64) 0x3e0) := by
  have h58 : (memRegion (sp + 0x140#64) 0x50 ∗ ((sp + 0x190#64) ↦₃₂ u190) ∗ memRegion (sp + 0x194#64) 4) ⊢
      memRegion (sp + 0x140#64) 0x58 := by
    rw [memRegion_split' (b := sp + 0x140#64) (b' := sp + 0x190#64) (n := 0x50) (k := 8) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x190#64) (b' := sp + 0x194#64) (n := 4) (k := 4) rfl (by bv_arith) (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (pointsTo32_entails_memRegion _ _))
  have h3e0 : (((sp + 0x1a0#64) ↦₆₄ u1a0) ∗ ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗
      ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗ ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗
      ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗ ((sp + 0x1c4#64) ↦₃₂ u1c4) ∗
      memRegion (sp + 0x1c8#64) 16 ∗ memRegion (sp + 0x1d8#64) 0x3a8) ⊢
      memRegion (sp + 0x1a0#64) 0x3e0 := by
    rw [memRegion_split' (b := sp + 0x1a0#64) (b' := sp + 0x1a8#64) (n := 8) (k := 0x3d8) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x1a8#64) (b' := sp + 0x1b0#64) (n := 8) (k := 0x3d0) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x1b0#64) (b' := sp + 0x1b4#64) (n := 4) (k := 0x3cc) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x1b4#64) (b' := sp + 0x1bc#64) (n := 8) (k := 0x3c4) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x1bc#64) (b' := sp + 0x1c4#64) (n := 8) (k := 0x3bc) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x1c4#64) (b' := sp + 0x1c8#64) (n := 4) (k := 0x3b8) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x1c8#64) (b' := sp + 0x1d8#64) (n := 16) (k := 0x3a8) rfl (by bv_arith) (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono_left (pointsTo32_entails_memRegion _ _))))))
  refine Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono h58 h3e0)

/-- Error branch after `RootKey::create_chain` #1 (`+0x548 → +0x7f8 → +0x30c`): when `[sp + 0x190]`
holds tag `1#32` (`.error .invalidKeyAgreement`), `tbz w8, #0, +448` is not taken, `+0x550..+0x560`
loads from `sp + 0x1a0..0x1c8` and branches to `+0x7f8`, and `dhStep_err_tail_from_7f8` steps to
`errTailPC img` (`+0x30c`). -/
theorem dhStep_cc1_err_branch {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 1352#64)
    (hmeta : tryDecryptMidMeta img s0 s)
    (hx20 : s.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64)
    (hx23 : s.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hx26 : s.readReg64 .x26 = s0.sp - 1504#64 + 0x2c0#64)
    (hmem : s.mem ⊨
      memRegion (s0.sp - 1504#64 + 0x140#64) 0x50 ∗
      createChainResultAt (s0.sp - 1504#64 + 0x190#64) (.error .invalidKeyAgreement) ∗
      memRegion (s0.sp - 1504#64 + 0x1d8#64) 0x3a8 ∗ Rest)
    (hcode : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      s'.pc = errTailPC img ∧
      tryDecryptMidMeta img s0 s' ∧
      s'.readReg64 .x19 = s.readReg64 .x19 ∧
      s'.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64 ∧
      s'.readReg64 .x26 = speTag .invalidKeyAgreement ∧
      (s'.mem ⊨
        memRegion (s0.sp - 1504#64 + 0x140#64) 0x28 ∗
        speBodyAt A (utf8 "decrypt") (s0.sp - 1504#64 + 0x168#64) .invalidKeyAgreement ∗
        memRegion (s0.sp - 1504#64 + 0x190#64) 0x3f0 ∗ Rest) := by
  have hentry := entryOf_eq_tripleRatchetProgAtExt ext himg tryDecryptName
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hfr, hsym, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hfn : libsignalSessionCode.fnOff tryDecryptName = num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  td_fetches img.base (Rust.withPanics ext) hfn 1352 28
  dsimp only [createChainResultAt] at hmem
  rw [show sp + 0x190#64 + 4#64 = sp + 0x194#64 by bv_arith,
      show sp + 0x190#64 + 8#64 = sp + 0x198#64 by bv_arith,
      show sp + 0x190#64 + 16#64 = sp + 0x1a0#64 by bv_arith,
      split_1a0_56 sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u1c4, u1bc, u1b4, u1b0, u1a8, u1a0, hmem⟩
  have hwp : SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 2040#64) s
      (((sp + 0x190#64) ↦₃₂ 1#32) ∗
       ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗
       ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗
       ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗
       ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗
       ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗
       ((sp + 0x1c4#64) ↦₃₂ u1c4))
      (fun sm P_m =>
        sm.sp = s0.sp - 1504#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64 ∧
        sm.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64 ∧
        sm.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64 ∧
        sm.readReg64 .x26 = s0.sp - 1504#64 + 0x2c0#64 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        (∀ m R, (m ⊨ P_m ∗ R) →
          (m ⊨ (((sp + 0x190#64) ↦₃₂ 1#32) ∗
                ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗
                ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗
                ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗
                ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗
                ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗
                ((sp + 0x1c4#64) ↦₃₂ u1c4)) ∗ R))) := by
    dsimp only [tripleRatchetProgAtExt] at *
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr tryDecryptName = entry
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx29], rfl, by simp [hx20, sp], by simp [hx23, sp],
       by simp [hx25, sp], by simp [hx26, sp], by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  have hmem_framed : s.mem ⊨
      (((sp + 0x190#64) ↦₃₂ 1#32) ∗
       ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗
       ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗
       ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗
       ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗
       ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗
       ((sp + 0x1c4#64) ↦₃₂ u1c4)) ∗
      (memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x194#64) 4 ∗
       ((sp + 0x198#64) ↦₆₄ speWord 10) ∗
       memRegion (sp + 0x1c8#64) 16 ∗
       memRegion (sp + 0x1d8#64) 0x3a8 ∗ Rest) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hmem
  obtain ⟨sm, hsteps1, hout⟩ := hwp.elim hmem_framed hcode
  obtain ⟨hpcm, hrunm, P_m, hmem_m, hsp_m, hx29_m, hx19_m, hx20_m, hx23_m, hx25_m, hx26_m, htrace_m, hvregs_m, hent_m⟩ :=
    hout.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_m : sm.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_m, ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hpcm' : sm.pc = tryDecryptEntry img + 0x7f8#64 := by
    unfold tryDecryptEntry; rw [hentry]; exact hpcm
  have hmeta_m : tryDecryptMidMeta img s0 sm :=
    ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hsteps1.frozenLoaded hfr, hsteps1.symtab_eq.trans hsym, hvregs_m⟩
  have hmem_m0 := hent_m sm.mem _ hmem_m
  have hmem_m1 : sm.mem ⊨
      (memRegion (sp + 0x140#64) 0x50 ∗
       ((sp + 0x190#64) ↦₃₂ 1#32) ∗
       memRegion (sp + 0x194#64) 4 ∗
       ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗
       ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗
       ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗
       ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗
       ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗
       ((sp + 0x1c4#64) ↦₃₂ u1c4) ∗
       memRegion (sp + 0x1c8#64) 16 ∗
       memRegion (sp + 0x1d8#64) 0x3a8) ∗
      (((sp + 0x198#64) ↦₆₄ speWord 10) ∗ Rest) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmem_m0
  have hmem_m2 := Satisfies.mono (sepConj_mono_left (fold_for_7f8 sp 1#32 u1a0 u1a8 u1b4 u1bc u1b0 u1c4)) hmem_m1
  have hmem_m3 : sm.mem ⊨
      memRegion (sp + 0x140#64) 0x58 ∗
      ((sp + 0x198#64) ↦₆₄ speWord 10) ∗
      memRegion (sp + 0x1a0#64) 0x3e0 ∗ Rest :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmem_m2
  obtain ⟨s', hsteps2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
    dhStep_err_tail_from_7f8 (A := A) (ext := ext)
      himg Rest s0 sm hpcm' hmeta_m hx20_m hx23_m hx25_m hx26_m hmem_m3 (hsteps1.codeLoaded hcode)
  exact ⟨s', Steps.trans hsteps1 hsteps2, hpcs', hmetas', hx19s'.trans hx19_m, hx20s', hx26s', hmems'⟩

/-- Success branch after `RootKey::create_chain` #1 (`+0x548 → +0x70c`): when `[sp + 0x190]`
holds tag `0#32` (`.ok (rk1, rck)`), `tbz w8, #0, +448` branches to `+0x70c` (`1804`). -/
theorem dhStep_cc1_ok_branch {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (rk1 : RootKey) (rck : ChainKey) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 1352#64)
    (hmeta : tryDecryptMidMeta img s0 s)
    (hmem : s.mem ⊨
      createChainResultAt (s0.sp - 1504#64 + 0x190#64) (.ok (rk1, rck)) ∗ Rest)
    (hcode : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      s'.pc = tryDecryptEntry img + 0x70c#64 ∧
      tryDecryptMidMeta img s0 s' ∧
      CalleeSavedPreserved s s' ∧
      (s'.mem ⊨
        ((s0.sp - 1504#64 + 0x190#64) ↦₃₂ 0#32) ∗
        ((s0.sp - 1504#64 + 0x194#64) ↦ₛ keyToBytes32 rk1) ∗
        ((s0.sp - 1504#64 + 0x1b4#64) ↦ₛ chainKeyBytes rck) ∗ Rest) := by
  have hentry := entryOf_eq_tripleRatchetProgAtExt ext himg tryDecryptName
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hfr, hsym, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hfn : libsignalSessionCode.fnOff tryDecryptName = num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  td_fetches img.base (Rust.withPanics ext) hfn 1352 8
  dsimp only [createChainResultAt] at hmem
  rw [show sp + 0x190#64 + 4#64 = sp + 0x194#64 by bv_arith,
      show sp + 0x190#64 + 0x24#64 = sp + 0x1b4#64 by bv_arith] at hmem
  have hwp : SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 1804#64) s
      ((sp + 0x190#64) ↦₃₂ 0#32)
      (fun sm P_m =>
        sm.sp = s0.sp - 1504#64 ∧
        CalleeSavedPreserved s sm ∧
        sm.trace = s0.trace ∧
        (∀ m R, (m ⊨ P_m ∗ R) → (m ⊨ ((sp + 0x190#64) ↦₃₂ 0#32) ∗ R))) := by
    dsimp only [tripleRatchetProgAtExt] at *
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr tryDecryptName = entry
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  have hmem_framed : s.mem ⊨
      ((sp + 0x190#64) ↦₃₂ 0#32) ∗
      (((sp + 0x194#64) ↦ₛ keyToBytes32 rk1) ∗
       ((sp + 0x1b4#64) ↦ₛ chainKeyBytes rck) ∗ Rest) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hmem
  obtain ⟨sm, hsteps1, hout⟩ := hwp.elim hmem_framed hcode
  obtain ⟨hpcm, hrunm, P_m, hmem_m, hsp_m, hcs_m, htrace_m, hent_m⟩ :=
    hout.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_m : sm.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_m, ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hpcm' : sm.pc = tryDecryptEntry img + 0x70c#64 := by
    unfold tryDecryptEntry; rw [hentry]; exact hpcm
  have hx29_m : sm.readReg64 .x29 = s0.sp - 96#64 := by reg_chain
  have hmeta_m : tryDecryptMidMeta img s0 sm :=
    ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hsteps1.frozenLoaded hfr, hsteps1.symtab_eq.trans hsym, by reg_chain⟩
  have hmem_m0 := hent_m sm.mem _ hmem_m
  exact ⟨sm, hsteps1, hpcm', hmeta_m, hcs_m, Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmem_m0⟩

/-- Propagate an allocator failure panic from `createChainSpec` to `tryDecryptSpec.onPanic`. -/
theorem onPanic_of_createChain {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {ccG : CreateChainGhost} {s0 sc sm : State} {Frame R : SepProp}
    (htrace : sc.trace = s0.trace)
    (hpost : sm.mem ⊨ ((createChainSpec C A).inImage img).onPanic ccG sc sm ∗ (Frame ∗ R)) :
    sm.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sm ∗ R := by
  dsimp only [createChainSpec, tryDecryptSpec, Spec.inImage] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  obtain ⟨⟨halloc, hpre⟩, hmem⟩ := hpost
  unfold allocFailedIn at halloc ⊢
  rw [htrace] at halloc hpre
  refine ⟨⟨Or.inr (Or.inr halloc), hpre⟩, ?_⟩
  have hmem' : sm.mem ⊨ (anyHeap ∗ Frame) ∗ R :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmem
  exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmem'

end CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep
