/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhDefs
import ProofLib.SepLogic.WPp

/-!
# Pure Unfolding and Error-Branch Helpers for `S3Spec`

Pure `RatchetState.dhRatchetStep` branch lemmas and stack-layout staging helpers for the early error
exits (`→ +0x30c`) and first `RootKey::create_chain` transition of `S3Spec`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegB

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.DecryptPq
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `RatchetState.dhRatchetStep` Pure Unfolding Lemmas -/

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
                 (r.receiverChains ++
                   [{ senderRatchetKey := srk
                      chainKey := some receiverChainKey
                      messageKeys := [] }]) }) := by
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

theorem dhRatchetStep_some_err1 (C : Crypto) (srk : PublicKey) (coins : BitVec 256) (r :
    RatchetState)
    (sc : SenderChain) (e : SignalProtocolError)
    (hsc : r.senderChain = some sc)
    (hcc1 : rootCreateChain C r.rootKey srk sc.ratchetKey.privateKey = .error e) :
    Mut.exec (RatchetState.dhRatchetStep C srk coins) r =
      (.error e, { r with rootKey := 0 }) := by
  rw [dhRatchetStep_some_eq C srk coins r sc hsc, hcc1]

theorem dhRatchetStep_some_err2 (C : Crypto) (srk : PublicKey) (coins : BitVec 256) (r :
    RatchetState)
    (sc : SenderChain) (newRootKey : RootKey) (receiverChainKey : ChainKey) (e :
      SignalProtocolError)
    (hsc : r.senderChain = some sc)
    (hcc1 : rootCreateChain C r.rootKey srk sc.ratchetKey.privateKey = .ok (newRootKey,
      receiverChainKey))
    (hcc2 : rootCreateChain C newRootKey srk (KeyPair.generate C coins).privateKey = .error e) :
    Mut.exec (RatchetState.dhRatchetStep C srk coins) r =
      (.error e, { r with rootKey := 0 }) := by
  rw [dhRatchetStep_some_eq C srk coins r sc hsc, hcc1]
  dsimp only
  rw [hcc2]

theorem dhRatchetStep_some_ok (C : Crypto) (srk : PublicKey) (coins : BitVec 256) (r : RatchetState)
    (sc : SenderChain) (newRootKey finalRootKey : RootKey) (receiverChainKey senderChainKey :
      ChainKey)
    (hsc : r.senderChain = some sc)
    (hcc1 : rootCreateChain C r.rootKey srk sc.ratchetKey.privateKey = .ok (newRootKey,
      receiverChainKey))
    (hcc2 : rootCreateChain C newRootKey srk (KeyPair.generate C coins).privateKey =
      .ok (finalRootKey, senderChainKey)) :
    Mut.exec (RatchetState.dhRatchetStep C srk coins) r =
      (.ok receiverChainKey,
       { r with
         senderChain := some ⟨KeyPair.generate C coins, senderChainKey⟩
         rootKey := finalRootKey
         previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
         receiverChains :=
           RatchetState.evictReceiverChains
             (r.receiverChains ++
               [{ senderRatchetKey := srk
                  chainKey := some receiverChainKey
                  messageKeys := [] }]) }) := by
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
    (hcc1 : rootCreateChain C tr.ratchet.rootKey srk sc.ratchetKey.privateKey = .ok (newRootKey,
      receiverChainKey)) :
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
  have h0 : (w1 ++ w0).extractLsb' 0 64 = w0 := by
    ext i hi; simp
  have h1 : (w1 ++ w0).extractLsb' 64 64 = w1 := bv128_extractLsb'_append w1 w0
  rw [h0, h1]

theorem pointsTo128_zero_16 (p : BitVec 64) :
    (p ↦₁₂₈ 0#128) = (p ↦ₛ List.replicate 16 0#8) := by
  rw [show (0#128 : BitVec 128) = 0#64 ++ 0#64 from rfl,
      ← pointsTo64_pair_eq_pointsTo128 p 0#64 0#64,
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

theorem pointsTo128_entails_memRegion (a : BitVec 64) (v : BitVec 128) :
    (a ↦₁₂₈ v) ⊢ memRegion a 16 := by
  unfold pointsTo128
  rw [show (16 : Nat) = 8 + 8 from rfl, memRegion_split a 8 8 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a _) (pointsTo64_entails_memRegion (a + 8#64) _)

theorem memRegion_sixteen (a : BitVec 64) :
    memRegion a 16 =
      (∃∗ w0 : BitVec 64, (a ↦₆₄ w0)) ∗ (∃∗ w1 : BitVec 64, ((a + 8#64) ↦₆₄ w1)) := by
  rw [show (16 : Nat) = 8 + 8 from rfl, memRegion_split a 8 8 (by decide),
      memRegion_eight a, memRegion_eight (a + 8#64)]

/-! ## 2. First Half of `S3Spec` (`+0x500 → +0x8ac` and Error Exits `→ +0x30c`) -/

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
      memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k :=
        16) rfl (by bv_arith) (by decide),
      memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k :=
        8) rfl (by bv_arith) (by decide)]
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
  rw [memRegion_split' (b := sp + 0x1a0#64) (b' := sp + 0x2b0#64) (n := 0x110) (k :=
      0x2d0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x2b0#64) (b' := sp + 0x2b8#64) (n := 0x8) (k :=
        0x2c8) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x2b8#64) (b' := sp + 0x2c0#64) (n := 0x8) (k :=
        0x2c0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x2c0#64) (b' := sp + 0x2c8#64) (n := 0x8) (k :=
        0x2b8) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x2c8#64) (b' := sp + 0x2d0#64) (n := 0x8) (k :=
        0x2b0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x2d0#64) (b' := sp + 0x2d4#64) (n := 0x4) (k :=
        0x2ac) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x2d4#64) (b' := sp + 0x500#64) (n := 0x22c) (k :=
        0x80) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x500#64) (b' := sp + 0x508#64) (n := 0x8) (k :=
        0x78) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x508#64) (b' := sp + 0x510#64) (n := 0x8) (k :=
        0x70) rfl (by bv_arith) (by decide),
      memRegion_eight (sp + 0x2b0#64), memRegion_eight (sp + 0x2b8#64),
      memRegion_eight (sp + 0x2c0#64), memRegion_eight (sp + 0x2c8#64),
      memRegion_four (sp + 0x2d0#64),
      memRegion_eight (sp + 0x500#64), memRegion_eight (sp + 0x508#64)]

theorem optSenderChainBytes_none_pointsTo32 (a : BitVec 64) (pad : List (BitVec 8)) :
    (a ↦ₛ optSenderChainBytes none pad) =
      ((a ↦₃₂ 0#32) ∗ ((a + 4#64) ↦ₛ pad)) := by
  unfold optSenderChainBytes
  have h0 : (a ↦ₛ leBytes 4 0) = (a ↦₃₂ 0#32) := by
    rw [pointsTo32_eq_pointsToBytes]
    rfl
  rw [pointsToBytes_append, show (leBytes 4 0).length = 4 from rfl, h0]

/-- Intermediate state at `+0x70c` (`0x34aa8`) right after `RootKey::create_chain` #1 returns
`.ok (rk1, rck)` and `+0x548..+0x54c` (`ldr w8, [sp, #0x190]; tbz w8, #0, 0x34aa8`) branches to
`+0x70c`. -/
def S3AfterCc1State (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
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
  rw [memRegion_split' (b := sp + 0x1a0#64) (b' := sp + 0x1a8#64) (n := 8) (k :=
      48) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x1a8#64) (b' := sp + 0x1b0#64) (n := 8) (k :=
        40) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x1b0#64) (b' := sp + 0x1b4#64) (n := 4) (k :=
        36) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x1b4#64) (b' := sp + 0x1bc#64) (n := 8) (k :=
        28) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x1bc#64) (b' := sp + 0x1c4#64) (n := 8) (k :=
        20) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x1c4#64) (b' := sp + 0x1c8#64) (n := 4) (k :=
        16) rfl (by bv_arith) (by decide),
      memRegion_eight (sp + 0x1a0#64), memRegion_eight (sp + 0x1a8#64),
      memRegion_four (sp + 0x1b0#64), memRegion_eight (sp + 0x1b4#64),
      memRegion_eight (sp + 0x1bc#64), memRegion_four (sp + 0x1c4#64)]

/-- Fold the `.error .invalidKeyAgreement` buffer at `sp + 0x140..0x580` into the layout expected
by `s3_err_tail_from_7f8`. -/
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
  have h58 : (memRegion (sp + 0x140#64) 0x50 ∗ ((sp + 0x190#64) ↦₃₂ u190) ∗
      memRegion (sp + 0x194#64) 4) ⊢
      memRegion (sp + 0x140#64) 0x58 := by
    rw [memRegion_split' (b := sp + 0x140#64) (b' := sp + 0x190#64) (n := 0x50) (k :=
        8) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x190#64) (b' := sp + 0x194#64) (n := 4) (k :=
          4) rfl (by bv_arith) (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (pointsTo32_entails_memRegion _ _))
  have h3e0 : (((sp + 0x1a0#64) ↦₆₄ u1a0) ∗ ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗
      ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗ ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗
      ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗ ((sp + 0x1c4#64) ↦₃₂ u1c4) ∗
      memRegion (sp + 0x1c8#64) 16 ∗ memRegion (sp + 0x1d8#64) 0x3a8) ⊢
      memRegion (sp + 0x1a0#64) 0x3e0 := by
    rw [memRegion_split' (b := sp + 0x1a0#64) (b' := sp + 0x1a8#64) (n := 8) (k :=
        0x3d8) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x1a8#64) (b' := sp + 0x1b0#64) (n := 8) (k :=
          0x3d0) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x1b0#64) (b' := sp + 0x1b4#64) (n := 4) (k :=
          0x3cc) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x1b4#64) (b' := sp + 0x1bc#64) (n := 8) (k :=
          0x3c4) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x1bc#64) (b' := sp + 0x1c4#64) (n := 8) (k :=
          0x3bc) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x1c4#64) (b' := sp + 0x1c8#64) (n := 4) (k :=
          0x3b8) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x1c8#64) (b' := sp + 0x1d8#64) (n := 16) (k :=
          0x3a8) rfl (by bv_arith) (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono_left (pointsTo32_entails_memRegion _ _))))))
  refine Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono h58 h3e0)

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

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegB
