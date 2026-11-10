/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepErr
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitChain
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# `DhStep` Receiving `create_chain` & Post-Call Branch Lemmas

Proves 32-byte SIMD load/store splitting helpers, the receiving `RootKey::create_chain` call step
(`dhStep_recv_create_chain`, `+0x500 → +0x70c / +0x30c`), and the sending `RootKey::create_chain`
result branches (`dhStep_cc2_ok_branch`, `dhStep_cc2_err_branch`).
-/

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

private theorem extractLsb'_shiftLeft8_or_zero (w : Nat) (hw : 8 ≤ w) (acc : BitVec w) (b : BitVec 8) :
    ((acc <<< 8) ||| b.zeroExtend w).extractLsb' 0 8 = b := by
  ext i hi
  simp [hi]
  omega

private theorem extractLsb'_shiftLeft8_or_succ (w : Nat) (acc : BitVec w) (b : BitVec 8) (k : Nat)
    (hk : 8 * (k + 1) + 8 ≤ w) :
    ((acc <<< 8) ||| b.zeroExtend w).extractLsb' (8 * (k + 1)) 8 =
      acc.extractLsb' (8 * k) 8 := by
  ext i hi
  have h1 : ¬ (8 * (k + 1) + i < 8) := by omega
  have hltw : 8 * (k + 1) + i < w := by omega
  have hsub : 8 * (k + 1) + i - 8 = 8 * k + i := by omega
  have hb : b.getLsbD (8 * (k + 1) + i) = false := BitVec.getLsbD_of_ge b _ (by omega)
  simp [h1, hltw, hsub, hb]
  rfl

private def bytesOfBV {w : Nat} (n : Nat) (v : BitVec w) : List (BitVec 8) :=
  (List.range n).map fun j => v.extractLsb' (8 * j) 8

protected def packBV (w : Nat) (bs : List (BitVec 8)) : BitVec w :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b.zeroExtend w) 0

private theorem bytesOfBV_packBV (w : Nat) :
    ∀ (bs : List (BitVec 8)), 8 * bs.length ≤ w → bytesOfBV bs.length (DhStep.packBV w bs) = bs
  | [], _ => rfl
  | b :: bs, hlen => by
    have hlen_cons : 8 * (bs.length + 1) ≤ w := hlen
    unfold bytesOfBV
    rw [DhStep.packBV, List.foldr_cons, ← DhStep.packBV]
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      Nat.mul_zero, extractLsb'_shiftLeft8_or_zero w (by omega), List.cons.injEq]
    refine ⟨trivial, ?_⟩
    have hmap :
        List.map ((fun j => ((DhStep.packBV w bs <<< 8) ||| b.zeroExtend w).extractLsb' (8 * j) 8) ∘ Nat.succ)
          (List.range bs.length) =
        bytesOfBV bs.length (DhStep.packBV w bs) := by
      unfold bytesOfBV
      apply List.map_congr_left
      intro k hk
      rw [List.mem_range] at hk
      exact extractLsb'_shiftLeft8_or_succ w (DhStep.packBV w bs) b k (by omega)
    rw [hmap]
    exact bytesOfBV_packBV w bs (by omega)

/-- Pack 8 bytes (little-endian) into a `BitVec 64`. -/
def pack64 (bs : List (BitVec 8)) : BitVec 64 := DhStep.packBV 64 bs

theorem unpack64_pack64 (bs : List (BitVec 8)) (h : bs.length = 8) :
    unpack64 (pack64 bs) = bs := by
  have h1 : unpack64 (pack64 bs) = bytesOfBV bs.length (DhStep.packBV 64 bs) := by
    rw [h]
    unfold unpack64 bytesOfBV pack64
    rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
    rfl
  rw [h1]
  exact bytesOfBV_packBV 64 bs (by omega)

theorem pointsToBytes_8_eq_pointsTo64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 8) :
    (a ↦ₛ bs) = (a ↦₆₄ pack64 bs) := by
  rw [pointsTo64_eq_pointsToBytes, unpack64_pack64 bs h]

/-- Split any 32-byte slice `a ↦ₛ bs` (`bs.length = 32`) into four 64-bit points-to assertions
so `ldur q0` / `ldur q1` and `stp q0, q1` can step through `wp_steps` and then fold back to
`a' ↦ₛ bs` at any destination `a'`. -/
theorem pointsTo_32_as_four_64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) =
      ((a ↦₆₄ pack64 (bs.take 8)) ∗
       ((a + 8#64) ↦₆₄ pack64 ((bs.drop 8).take 8)) ∗
       ((a + 16#64) ↦₆₄ pack64 ((bs.drop 16).take 8)) ∗
       ((a + 24#64) ↦₆₄ pack64 (bs.drop 24))) := by
  have h1 : (bs.take 8).length = 8 := by simp [h]
  have h2 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have h3 : ((bs.drop 16).take 8).length = 8 := by simp [h]
  have h4 : (bs.drop 24).length = 8 := by simp [h]
  have hsplit : bs = bs.take 8 ++ ((bs.drop 8).take 8 ++ ((bs.drop 16).take 8 ++ bs.drop 24)) := by
    conv_lhs => rw [← List.take_append_drop 8 bs]
    congr 1
    conv_lhs => rw [← List.take_append_drop 8 (bs.drop 8)]
    rw [List.drop_drop]
    congr 1
    conv_lhs => rw [← List.take_append_drop 8 (bs.drop 16)]
    rw [List.drop_drop]
  conv_lhs => rw [hsplit]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, h1, h2, h3,
      pointsToBytes_8_eq_pointsTo64 a (bs.take 8) h1,
      pointsToBytes_8_eq_pointsTo64 (a + 8#64) ((bs.drop 8).take 8) h2,
      pointsToBytes_8_eq_pointsTo64 (a + 8#64 + 8#64) ((bs.drop 16).take 8) h3,
      pointsToBytes_8_eq_pointsTo64 (a + 8#64 + 8#64 + 8#64) (bs.drop 24) h4,
      show a + 8#64 + 8#64 = a + 16#64 by bv_arith,
      show a + 16#64 + 8#64 = a + 24#64 by bv_arith]

theorem pointsTo64_zero_32 (a : BitVec 64) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 0#64) ∗
     ((a + 16#64) ↦₆₄ 0#64) ∗ ((a + 24#64) ↦₆₄ 0#64)) =
      (a ↦ₛ keyToBytes32 (0 : RootKey)) := by
  have h1 := pointsTo64_pair_eq_pointsTo128 a 0#64 0#64
  have h2 := pointsTo64_pair_eq_pointsTo128 (a + 16#64) 0#64 0#64
  have h0 : (0#64 ++ 0#64 : BitVec 128) = 0#128 := by decide
  rw [h0] at h1 h2
  rw [show a + 16#64 + 8#64 = a + 24#64 by bv_arith] at h2
  rw [← pointsTo128_zero_32 a, ← h1, ← h2]
  ac_rfl

/-- Split `optSenderChainBytes (some sc) pad` at `sp + 0x50` into the `1#32` tag at `sp + 0x50`,
the 32-byte public key at `sp + 0x54`, the 32-byte private key at `sp + 0x74`, and the 36-byte
`chainKeyBytes sc.chainKey` at `sp + 0x94`. -/
theorem optSenderChainBytes_some_split (sp : BitVec 64) (sc : SenderChain) (pad : List (BitVec 8)) :
    ((sp + 0x50#64) ↦ₛ optSenderChainBytes (some sc) pad) =
      (((sp + 0x50#64) ↦₃₂ 1#32) ∗
       ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
       ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey)) := by
  unfold optSenderChainBytes senderChainBytes
  dsimp only
  rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  have h1 : (leBytes 4 1).length = 4 := by decide
  have h1_eq : leBytes 4 1 = unpack32 1#32 := by decide
  have h2 : sc.ratchetKey.publicKey.bytes.toList.length = 32 := sc.ratchetKey.publicKey.bytes.2
  have h3 : sc.ratchetKey.privateKey.bytes.toList.length = 32 := sc.ratchetKey.privateKey.bytes.2
  rw [h1, h2, h3, h1_eq, ← pointsTo32_eq_pointsToBytes]
  have ha1 : sp + 0x50#64 + 4#64 = sp + 0x54#64 := by bv_arith
  have ha2 : sp + 0x54#64 + 32#64 = sp + 0x74#64 := by bv_arith
  have ha3 : sp + 0x74#64 + 32#64 = sp + 0x94#64 := by bv_arith
  rw [ha1, ha2, ha3]

/-- Split `stackAt sp tryDecryptSubStack` into `stackAt sp createChainStack` and the remaining
stack region below it. -/
theorem stackAt_subStack_createChain (sp : BitVec 64) :
    stackAt sp tryDecryptSubStack =
      (stackAt (sp - BitVec.ofNat 64 createChainStack) (tryDecryptSubStack - createChainStack) ∗
       stackAt sp createChainStack) := by
  dsimp only [stackAt]
  have hadd : BitVec.ofNat 64 tryDecryptSubStack =
      BitVec.ofNat 64 createChainStack + BitVec.ofNat 64 (tryDecryptSubStack - createChainStack) := by
    decide
  rw [show sp - BitVec.ofNat 64 createChainStack - BitVec.ofNat 64 (tryDecryptSubStack - createChainStack) =
        sp - BitVec.ofNat 64 tryDecryptSubStack by rw [hadd]; bv_arith]
  exact memRegion_split'
    (b := sp - BitVec.ofNat 64 tryDecryptSubStack)
    (b' := sp - BitVec.ofNat 64 createChainStack)
    (n := tryDecryptSubStack - createChainStack)
    (k := createChainStack)
    (by decide) (by rw [hadd]; bv_arith) (by decide)

/-- All fields of `signalMessageAt A g a m` except `((a + 0x38#64) ↦ₛ m.senderRatchetKey.bytes.toList)`. -/
def signalMessageRestAt (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64) (m : SignalMessage) :
    SepProp :=
  ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    vecU8At A a g.pqCap g.pqPtr m.pqRatchet ∗
    boxU8At A (a + 0x18#64) g.ctPtr m.ciphertext ∗
    boxU8At A (a + 0x28#64) g.serPtr m.serialized ∗
    optBoxU8At A (a + 0x58#64) g.addrPtr m.addresses ∗
    ((a + 0x68#64) ↦₃₂ m.counter) ∗ ((a + 0x6c#64) ↦₃₂ m.previousCounter) ∗
    ((a + 0x70#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0x71#64) 7

theorem signalMessageAt_senderRatchetKey (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (msg : SignalMessage) :
    signalMessageAt A g a msg =
      (((a + 0x38#64) ↦ₛ msg.senderRatchetKey.bytes.toList) ∗
       signalMessageRestAt A g a msg) := by
  unfold signalMessageAt signalMessageRestAt
  ac_rfl

/-- Split `memRegion (sp + 0x140) 0x440` for the first `RootKey::create_chain` call (`+0x544`):
exposes `memRegion (sp + 0x190) 72` (`ret`), four 64-bit slots at `sp + 0x390..0x3b0` (`ourA`),
and four 64-bit slots at `sp + 0x3b0..0x3d0` (`rkA`). -/
theorem split_140_for_cc1 (sp : BitVec 64) :
    memRegion (sp + 0x140#64) 0x440 =
      (memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x190#64) 72 ∗
       memRegion (sp + 0x1d8#64) 0x1b8 ∗
       (∃∗ u390 : BitVec 64, (sp + 0x390#64) ↦₆₄ u390) ∗
       (∃∗ u398 : BitVec 64, (sp + 0x398#64) ↦₆₄ u398) ∗
       (∃∗ u3a0 : BitVec 64, (sp + 0x3a0#64) ↦₆₄ u3a0) ∗
       (∃∗ u3a8 : BitVec 64, (sp + 0x3a8#64) ↦₆₄ u3a8) ∗
       (∃∗ u3b0 : BitVec 64, (sp + 0x3b0#64) ↦₆₄ u3b0) ∗
       (∃∗ u3b8 : BitVec 64, (sp + 0x3b8#64) ↦₆₄ u3b8) ∗
       (∃∗ u3c0 : BitVec 64, (sp + 0x3c0#64) ↦₆₄ u3c0) ∗
       (∃∗ u3c8 : BitVec 64, (sp + 0x3c8#64) ↦₆₄ u3c8) ∗
       memRegion (sp + 0x3d0#64) 0x1b0) := by
  rw [memRegion_split' (b := sp + 0x140#64) (b' := sp + 0x190#64) (n := 0x50) (k := 0x3f0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x190#64) (b' := sp + 0x1d8#64) (n := 72) (k := 0x3a8) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x1d8#64) (b' := sp + 0x390#64) (n := 0x1b8) (k := 0x1f0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x390#64) (b' := sp + 0x398#64) (n := 8) (k := 0x1e8) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x398#64) (b' := sp + 0x3a0#64) (n := 8) (k := 0x1e0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3a0#64) (b' := sp + 0x3a8#64) (n := 8) (k := 0x1d8) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3a8#64) (b' := sp + 0x3b0#64) (n := 8) (k := 0x1d0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3b0#64) (b' := sp + 0x3b8#64) (n := 8) (k := 0x1c8) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3b8#64) (b' := sp + 0x3c0#64) (n := 8) (k := 0x1c0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3c0#64) (b' := sp + 0x3c8#64) (n := 8) (k := 0x1b8) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3c8#64) (b' := sp + 0x3d0#64) (n := 8) (k := 0x1b0) rfl (by bv_arith) (by decide),
      memRegion_eight (sp + 0x390#64), memRegion_eight (sp + 0x398#64),
      memRegion_eight (sp + 0x3a0#64), memRegion_eight (sp + 0x3a8#64),
      memRegion_eight (sp + 0x3b0#64), memRegion_eight (sp + 0x3b8#64),
      memRegion_eight (sp + 0x3c0#64), memRegion_eight (sp + 0x3c8#64)]

/-- Fold the temporary 32-byte copies at `sp + 0x390..0x3b0` and `sp + 0x3b0..0x3d0` back into
`memRegion (sp + 0x1d8) 0x3a8` after `RootKey::create_chain` #1 returns. -/
theorem fold_390_3b0_to_memRegion (sp : BitVec 64) (bs1 bs2 : List (BitVec 8))
    (h1 : bs1.length = 32) (h2 : bs2.length = 32) :
    (memRegion (sp + 0x1d8#64) 0x1b8 ∗
     ((sp + 0x390#64) ↦ₛ bs1) ∗
     ((sp + 0x3b0#64) ↦ₛ bs2) ∗
     memRegion (sp + 0x3d0#64) 0x1b0) ⊢
    memRegion (sp + 0x1d8#64) 0x3a8 := by
  have e1 := pointsToBytes_entails_memRegion (sp + 0x390#64) bs1
  rw [h1] at e1
  have e2 := pointsToBytes_entails_memRegion (sp + 0x3b0#64) bs2
  rw [h2] at e2
  rw [memRegion_split' (b := sp + 0x1d8#64) (b' := sp + 0x390#64) (n := 0x1b8) (k := 0x1f0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x390#64) (b' := sp + 0x3b0#64) (n := 32) (k := 0x1d0) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3b0#64) (b' := sp + 0x3d0#64) (n := 32) (k := 0x1b0) rfl (by bv_arith) (by decide)]
  exact sepConj_mono_right (sepConj_mono e1 (sepConj_mono_left e2))

/-- Step `+0x500 → +0x70c` (or `+0x30c` `ErrTailState` on `.error .invalidKeyAgreement`, or panic):
when `tr.ratchet.senderChain = some sc`, prepares the arguments for `RootKey::create_chain` #1,
zeros `tr.ratchet.rootKey` on the stack, calls `RootKey::create_chain` (`+0x544`), and branches on
the result tag (`+0x548..+0x54c`). -/
theorem dhStep_recv_create_chain {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hcc : CreateChainOkExt img C A ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (sc : SenderChain) (R : SepProp) (s0 s : State)
    (hsc : tr.ratchet.senderChain = some sc)
    (hrk1_ne : s0.sp - 1504#64 + 0x3b0#64 ≠ 0#64)
    (hs3 : DhStepState A ctl img x trG tr st1 R s0 s)
    (hcode : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    match rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | .ok (rk1, rck) =>
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (DhStepAfterRecvChainState A ctl img x trG tr st1 rk1 rck R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)))
    | .error e =>
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        ((∃ trG' r1, ErrTailState A ctl img x trG' { tr with ratchet := r1 } st1 e 0 R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  obtain ⟨hpc, hmeta, hx12, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hmem⟩ := hs3
  have hentry := entryOf_eq_tripleRatchetProgAtExt ext himg tryDecryptName
  unfold segDhStepPC tryDecryptEntry at hpc
  rw [hentry] at hpc
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hfr, hsym, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hfn : libsignalSessionCode.fnOff tryDecryptName = num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  have hfn_cc : libsignalSessionCode.fnOff createChainName = num% (ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain") := (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::RootKey>::create_chain")
  td_fetches img.base (Rust.withPanics ext) hfn 1280 72
  have hpriv_len : sc.ratchetKey.privateKey.bytes.toList.length = 32 := sc.ratchetKey.privateKey.bytes.2
  have hrk_len : (keyToBytes32 tr.ratchet.rootKey).length = 32 := length_keyToBytes32 _
  obtain ⟨p0, hp0⟩ : ∃ v, pack64 (sc.ratchetKey.privateKey.bytes.toList.take 8) = v := ⟨_, rfl⟩
  obtain ⟨p1, hp1⟩ : ∃ v, pack64 ((sc.ratchetKey.privateKey.bytes.toList.drop 8).take 8) = v := ⟨_, rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ v, pack64 ((sc.ratchetKey.privateKey.bytes.toList.drop 16).take 8) = v := ⟨_, rfl⟩
  obtain ⟨p3, hp3⟩ : ∃ v, pack64 (sc.ratchetKey.privateKey.bytes.toList.drop 24) = v := ⟨_, rfl⟩
  obtain ⟨k0, hk0⟩ : ∃ v, pack64 ((keyToBytes32 tr.ratchet.rootKey).take 8) = v := ⟨_, rfl⟩
  obtain ⟨k1, hk1⟩ : ∃ v, pack64 (((keyToBytes32 tr.ratchet.rootKey).drop 8).take 8) = v := ⟨_, rfl⟩
  obtain ⟨k2, hk2⟩ : ∃ v, pack64 (((keyToBytes32 tr.ratchet.rootKey).drop 16).take 8) = v := ⟨_, rfl⟩
  obtain ⟨k3, hk3⟩ : ∃ v, pack64 ((keyToBytes32 tr.ratchet.rootKey).drop 24) = v := ⟨_, rfl⟩
  have hsc_split : ((sp + 0x38#64 + 24#64) ↦ₛ optSenderChainBytes tr.ratchet.senderChain trG.ratchet.senderPad) =
      (((sp + 0x50#64) ↦₃₂ 1#32) ∗
       ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
       ((sp + 0x74#64) ↦₆₄ p0) ∗
       ((sp + 0x7c#64) ↦₆₄ p1) ∗
       ((sp + 0x84#64) ↦₆₄ p2) ∗
       ((sp + 0x8c#64) ↦₆₄ p3) ∗
       ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey)) := by
    rw [hsc, show sp + 0x38#64 + 24#64 = sp + 0x50#64 by bv_arith,
        optSenderChainBytes_some_split sp sc trG.ratchet.senderPad,
        pointsTo_32_as_four_64 (sp + 0x74#64) sc.ratchetKey.privateKey.bytes.toList hpriv_len,
        hp0, hp1, hp2, hp3,
        show sp + 0x74#64 + 8#64 = sp + 0x7c#64 by bv_arith,
        show sp + 0x74#64 + 16#64 = sp + 0x84#64 by bv_arith,
        show sp + 0x74#64 + 24#64 = sp + 0x8c#64 by bv_arith]
    ac_rfl
  have hrk_split : ((sp + 0x38#64 + 128#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) =
      (((sp + 0xb8#64) ↦₆₄ k0) ∗
       ((sp + 0xc0#64) ↦₆₄ k1) ∗
       ((sp + 0xc8#64) ↦₆₄ k2) ∗
       ((sp + 0xd0#64) ↦₆₄ k3)) := by
    rw [show sp + 0x38#64 + 128#64 = sp + 0xb8#64 by bv_arith,
        pointsTo_32_as_four_64 (sp + 0xb8#64) (keyToBytes32 tr.ratchet.rootKey) hrk_len,
        hk0, hk1, hk2, hk3,
        show sp + 0xb8#64 + 8#64 = sp + 0xc0#64 by bv_arith,
        show sp + 0xb8#64 + 16#64 = sp + 0xc8#64 by bv_arith,
        show sp + 0xb8#64 + 24#64 = sp + 0xd0#64 by bv_arith]
  unfold trAt ratchetAt at hmem
  rw [hsc_split, hrk_split, split_140_for_cc1 sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u3c8, u3c0, u3b8, u3b0, u3a8, u3a0, u398, u390, hmem⟩
  have hwp1 : SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName - 129296#64) s
      (((sp + 0x50#64) ↦₃₂ 1#32) ∗
       ((sp + 0x74#64) ↦₆₄ p0) ∗
       ((sp + 0x7c#64) ↦₆₄ p1) ∗
       ((sp + 0x84#64) ↦₆₄ p2) ∗
       ((sp + 0x8c#64) ↦₆₄ p3) ∗
       ((sp + 0xb8#64) ↦₆₄ k0) ∗
       ((sp + 0xc0#64) ↦₆₄ k1) ∗
       ((sp + 0xc8#64) ↦₆₄ k2) ∗
       ((sp + 0xd0#64) ↦₆₄ k3) ∗
       ((sp + 0x390#64) ↦₆₄ u390) ∗
       ((sp + 0x398#64) ↦₆₄ u398) ∗
       ((sp + 0x3a0#64) ↦₆₄ u3a0) ∗
       ((sp + 0x3a8#64) ↦₆₄ u3a8) ∗
       ((sp + 0x3b0#64) ↦₆₄ u3b0) ∗
       ((sp + 0x3b8#64) ↦₆₄ u3b8) ∗
       ((sp + 0x3c0#64) ↦₆₄ u3c0) ∗
       ((sp + 0x3c8#64) ↦₆₄ u3c8))
      (fun sc1 P_c1 =>
        sc1.sp = s0.sp - 1504#64 ∧
        sc1.readReg64 .x0 = s0.sp - 1504#64 + 0x3b0#64 ∧
        sc1.readReg64 .x1 = x.msgA + 56#64 ∧
        sc1.readReg64 .x2 = s0.sp - 1504#64 + 0x390#64 ∧
        sc1.readReg64 .x8 = s0.sp - 1504#64 + 0x190#64 ∧
        sc1.readReg64 .x19 = x.ret ∧
        sc1.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64 ∧
        sc1.readReg64 .x21 = x.ss ∧
        sc1.readReg64 .x22 = x.msgA ∧
        sc1.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64 ∧
        (sc1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        sc1.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64 ∧
        sc1.readReg64 .x26 = s0.sp - 1504#64 + 0x2c0#64 ∧
        sc1.readReg64 .x27 = s0.sp - 1504#64 + 0x38#64 ∧
        sc1.readReg64 .x28 = s0.sp - 1504#64 + 0x2c0#64 ∧
        sc1.readReg64 .x29 = s0.sp - 96#64 ∧
        sc1.readReg64 .x30 = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 1352#64 ∧
        sc1.trace = s0.trace ∧
        calleeSavedVRegs sc1 = calleeSavedVRegs s0 ∧
        (∀ m R, (m ⊨ P_c1 ∗ R) →
          (m ⊨ (((sp + 0x50#64) ↦₃₂ 1#32) ∗
                ((sp + 0x74#64) ↦₆₄ p0) ∗
                ((sp + 0x7c#64) ↦₆₄ p1) ∗
                ((sp + 0x84#64) ↦₆₄ p2) ∗
                ((sp + 0x8c#64) ↦₆₄ p3) ∗
                ((sp + 0xb8#64) ↦₆₄ 0#64) ∗
                ((sp + 0xc0#64) ↦₆₄ 0#64) ∗
                ((sp + 0xc8#64) ↦₆₄ 0#64) ∗
                ((sp + 0xd0#64) ↦₆₄ 0#64) ∗
                ((sp + 0x390#64) ↦₆₄ p0) ∗
                ((sp + 0x398#64) ↦₆₄ p1) ∗
                ((sp + 0x3a0#64) ↦₆₄ p2) ∗
                ((sp + 0x3a8#64) ↦₆₄ p3) ∗
                ((sp + 0x3b0#64) ↦₆₄ k0) ∗
                ((sp + 0x3b8#64) ↦₆₄ k1) ∗
                ((sp + 0x3c0#64) ↦₆₄ k2) ∗
                ((sp + 0x3c8#64) ↦₆₄ k3)) ∗ R))) := by
    dsimp only [tripleRatchetProgAtExt] at *
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr tryDecryptName = entry
    wp_steps
    refine SepWP.done (by change entry + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) = entry - 129296#64; bv_omega) (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [sp], by simp, by simp [sp], by simp [sp],
       by simp [hx19], by simp [hx20, sp], by simp [hx21], by simp [hx22], by simp [hx23, sp],
       by simp [hx24], by simp [hx25, sp], by simp [sp], by simp [hx27, sp],
       by simp [hx28, sp], by simp [hx29], rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  have hmem_framed : s.mem ⊨
      (((sp + 0x50#64) ↦₃₂ 1#32) ∗
       ((sp + 0x74#64) ↦₆₄ p0) ∗
       ((sp + 0x7c#64) ↦₆₄ p1) ∗
       ((sp + 0x84#64) ↦₆₄ p2) ∗
       ((sp + 0x8c#64) ↦₆₄ p3) ∗
       ((sp + 0xb8#64) ↦₆₄ k0) ∗
       ((sp + 0xc0#64) ↦₆₄ k1) ∗
       ((sp + 0xc8#64) ↦₆₄ k2) ∗
       ((sp + 0xd0#64) ↦₆₄ k3) ∗
       ((sp + 0x390#64) ↦₆₄ u390) ∗
       ((sp + 0x398#64) ↦₆₄ u398) ∗
       ((sp + 0x3a0#64) ↦₆₄ u3a0) ∗
       ((sp + 0x3a8#64) ↦₆₄ u3a8) ∗
       ((sp + 0x3b0#64) ↦₆₄ u3b0) ∗
       ((sp + 0x3b8#64) ↦₆₄ u3b8) ∗
       ((sp + 0x3c0#64) ↦₆₄ u3c0) ∗
       ((sp + 0x3c8#64) ↦₆₄ u3c8)) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       (⌜∀ sc', tr.ratchet.senderChain = some sc' →
          Ratchet.clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes⌝ ∗
        (⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
          trG.ratchet.senderPad.length = 100 ∧ tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
         vecAt A 104 8 (chainAt A) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr
           (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
         ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
         ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗
         ((sp + 0x38#64 + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
         ((sp + 0x38#64 + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗
         memRegion (sp + 0x38#64 + 172#64) 4) ∗
        vecU8At A (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
        ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
        ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x190#64) 72 ∗
       memRegion (sp + 0x1d8#64) 0x1b8 ∗
       memRegion (sp + 0x3d0#64) 0x1b0 ∗
       tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hmem
  obtain ⟨sc1, hsteps1, hout1⟩ := hwp1.elim hmem_framed hcode
  obtain ⟨hpcc1, hrunc1, P_c1, hmem_c1, hsp_c1, hx0_c1, hx1_c1, hx2_c1, hx8_c1,
    hx19_c1, hx20_c1, hx21_c1, hx22_c1, hx23_c1, hx24_c1, hx25_c1, hx26_c1, hx27_c1, hx28_c1,
    hx29_c1, hx30_c1, htrace_c1, hvregs_c1, hent_c1⟩ :=
    hout1.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_c1 : sc1.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_c1, ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hfr_c1 : img.FrozenLoaded sc1 := hsteps1.frozenLoaded hfr
  have hsym_c1 : sc1.symtab = img.symtab := hsteps1.symtab_eq.trans hsym
  have hpc_cc1 : sc1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr createChainName := by
    rw [hpcc1]
    dsimp only [tripleRatchetProgAtExt]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hfn, hfn_cc]
    bv_arith
  have hmem_c1_0 := hent_c1 sc1.mem _ hmem_c1
  have h74_fold : ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) =
      (((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗
       ((sp + 0x84#64) ↦₆₄ p2) ∗ ((sp + 0x8c#64) ↦₆₄ p3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x74#64) sc.ratchetKey.privateKey.bytes.toList hpriv_len,
        hp0, hp1, hp2, hp3,
        show sp + 0x74#64 + 8#64 = sp + 0x7c#64 by bv_arith,
        show sp + 0x74#64 + 16#64 = sp + 0x84#64 by bv_arith,
        show sp + 0x74#64 + 24#64 = sp + 0x8c#64 by bv_arith]
  have h390_fold : ((sp + 0x390#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) =
      (((sp + 0x390#64) ↦₆₄ p0) ∗ ((sp + 0x398#64) ↦₆₄ p1) ∗
       ((sp + 0x3a0#64) ↦₆₄ p2) ∗ ((sp + 0x3a8#64) ↦₆₄ p3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x390#64) sc.ratchetKey.privateKey.bytes.toList hpriv_len,
        hp0, hp1, hp2, hp3,
        show sp + 0x390#64 + 8#64 = sp + 0x398#64 by bv_arith,
        show sp + 0x390#64 + 16#64 = sp + 0x3a0#64 by bv_arith,
        show sp + 0x390#64 + 24#64 = sp + 0x3a8#64 by bv_arith]
  have h3b0_fold : ((sp + 0x3b0#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) =
      (((sp + 0x3b0#64) ↦₆₄ k0) ∗ ((sp + 0x3b8#64) ↦₆₄ k1) ∗
       ((sp + 0x3c0#64) ↦₆₄ k2) ∗ ((sp + 0x3c8#64) ↦₆₄ k3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x3b0#64) (keyToBytes32 tr.ratchet.rootKey) hrk_len,
        hk0, hk1, hk2, hk3,
        show sp + 0x3b0#64 + 8#64 = sp + 0x3b8#64 by bv_arith,
        show sp + 0x3b0#64 + 16#64 = sp + 0x3c0#64 by bv_arith,
        show sp + 0x3b0#64 + 24#64 = sp + 0x3c8#64 by bv_arith]
  have hb8_zero : ((sp + 0x38#64 + 128#64) ↦ₛ keyToBytes32 (0 : RootKey)) =
      (((sp + 0xb8#64) ↦₆₄ 0#64) ∗ ((sp + 0xc0#64) ↦₆₄ 0#64) ∗
       ((sp + 0xc8#64) ↦₆₄ 0#64) ∗ ((sp + 0xd0#64) ↦₆₄ 0#64)) := by
    rw [show sp + 0x38#64 + 128#64 = sp + 0xb8#64 by bv_arith,
        ← pointsTo64_zero_32 (sp + 0xb8#64),
        show sp + 0xb8#64 + 8#64 = sp + 0xc0#64 by bv_arith,
        show sp + 0xb8#64 + 16#64 = sp + 0xc8#64 by bv_arith,
        show sp + 0xb8#64 + 24#64 = sp + 0xd0#64 by bv_arith]
  have htr0_fold : trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } =
      (⌜∀ sc', tr.ratchet.senderChain = some sc' →
          Ratchet.clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes⌝ ∗
       (⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
         trG.ratchet.senderPad.length = 100 ∧ tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
        vecAt A 104 8 (chainAt A) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr
          (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
        (((sp + 0x50#64) ↦₃₂ 1#32) ∗
         ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
         (((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗
          ((sp + 0x84#64) ↦₆₄ p2) ∗ ((sp + 0x8c#64) ↦₆₄ p3)) ∗
         ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey)) ∗
        (((sp + 0xb8#64) ↦₆₄ 0#64) ∗ ((sp + 0xc0#64) ↦₆₄ 0#64) ∗
         ((sp + 0xc8#64) ↦₆₄ 0#64) ∗ ((sp + 0xd0#64) ↦₆₄ 0#64)) ∗
        ((sp + 0x38#64 + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
        ((sp + 0x38#64 + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗
        memRegion (sp + 0x38#64 + 172#64) 4) ∗
       vecU8At A (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
       ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
       ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) := by
    unfold trAt ratchetAt
    dsimp only
    rw [hsc, show sp + 0x38#64 + 24#64 = sp + 0x50#64 by bv_arith,
        optSenderChainBytes_some_split sp sc trG.ratchet.senderPad,
        h74_fold, hb8_zero]
  let ccG1 : CreateChainGhost :=
    { rkA := sp + 0x3b0#64
      rk := tr.ratchet.rootKey
      theirA := x.msgA + 56#64
      their := x.msg.senderRatchetKey
      ourA := sp + 0x390#64
      our := sc.ratchetKey.privateKey
      ret := sp + 0x190#64 }
  let Frame1 : SepProp :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x1d8#64) 0x1b8 ∗
    memRegion (sp + 0x3d0#64) 0x1b0 ∗
    protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗
    signalMessageRestAt A x.msgG x.msgA x.msg ∗
    tapeAfter ctl x.cur x.rest 0 ∗
    logOff img ∗
    stackAt (sp - BitVec.ofNat 64 createChainStack) (tryDecryptSubStack - createChainStack) ∗
    tryDecryptSavedRegs s0.sp s0
  have hpre_cc1 : sc1.mem ⊨ ((createChainSpec C A).inImage img).pre ccG1 sc1 ∗ (Frame1 ∗ R) := by
    dsimp only [createChainSpec, Spec.inImage, ccG1, Frame1]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfr_c1, hsym_c1⟩, ⟨hx0_c1, hx1_c1, hx2_c1, hx8_c1, hrk1_ne⟩, ?_⟩
    rw [htr0_fold, h390_fold, h3b0_fold, show sc1.sp = sp from hsp_c1]
    unfold tryDecryptCommonHeap at hmem_c1_0
    rw [signalMessageAt_senderRatchetKey A x.msgG x.msgA x.msg,
        show s0.sp - 1504#64 = sp from rfl,
        stackAt_subStack_createChain sp] at hmem_c1_0
    exact Eq.mp (congrArg (sc1.mem ⊨ ·) (by ac_rfl)) hmem_c1_0
  obtain ⟨sm, hsteps_cc1, hout_cc1, -⟩ :=
    hcc.no_fault_before_outcome ccG1 (Frame1 ∗ R) sc1 hpc_cc1 hrunc1 hpre_cc1 hsp_al_c1
      (hsteps1.codeLoaded hcode)
  have hsteps12 : Steps (tripleRatchetProgAtExt img.base ext) s sm := Steps.trans hsteps1 hsteps_cc1
  rcases hout_cc1 with ⟨hret_m, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, -, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
  · -- Normal return from `RootKey::create_chain` #1
    have hpcm : sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 1352#64 :=
      hret_m.1.trans hx30_c1
    have hrunm : sm.status = .Running := hret_m.2.2
    dsimp only [createChainSpec, Spec.inImage, ccG1] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hfr_m : img.FrozenLoaded sm := hsteps_cc1.frozenLoaded hfr_c1
    have hsym_m : sm.symtab = img.symtab := hsteps_cc1.symtab_eq.trans hsym_c1
    have htrace_m0 := hpost.1
    have hpost := hpost.2
    have htrace_m : sm.trace = s0.trace := htrace_m0.trans htrace_c1
    have hsp_m : sm.sp = s0.sp - 1504#64 := hspm.trans hsp_c1
    have hsp_al_m : sm.spAligned = true := by
      unfold State.spAligned at hsp_al_c1 ⊢
      rw [hspm]
      exact hsp_al_c1
    have hx19_m : sm.readReg64 .x19 = x.ret := hcsm.1.trans hx19_c1
    have hx20_m : sm.readReg64 .x20 = sp + 0x140#64 := hcsm.2.1.trans hx20_c1
    have hx21_m : sm.readReg64 .x21 = x.ss := hcsm.2.2.1.trans hx21_c1
    have hx22_m : sm.readReg64 .x22 = x.msgA := hcsm.2.2.2.1.trans hx22_c1
    have hx23_m : sm.readReg64 .x23 = sp + 0x500#64 := hcsm.2.2.2.2.1.trans hx23_c1
    have hx24_m : (sm.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType := by
      rw [hcsm.2.2.2.2.2.1]; exact hx24_c1
    have hx25_m : sm.readReg64 .x25 = sp + 0x190#64 := hcsm.2.2.2.2.2.2.1.trans hx25_c1
    have hx26_m : sm.readReg64 .x26 = sp + 0x2c0#64 := hcsm.2.2.2.2.2.2.2.1.trans hx26_c1
    have hx27_m : sm.readReg64 .x27 = sp + 0x38#64 := hcsm.2.2.2.2.2.2.2.2.1.trans hx27_c1
    have hx28_m : sm.readReg64 .x28 = sp + 0x2c0#64 := hcsm.2.2.2.2.2.2.2.2.2.1.trans hx28_c1
    have hx29_m : sm.readReg64 .x29 = s0.sp - 96#64 := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hx29_c1
    have hmeta_m : tryDecryptMidMeta img s0 sm :=
      ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hfr_m, hsym_m, by reg_chain⟩
    have hpost_grouped : sm.mem ⊨
        (memRegion (sp + 0x1d8#64) 0x1b8 ∗
         ((sp + 0x390#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
         ((sp + 0x3b0#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) ∗
         memRegion (sp + 0x3d0#64) 0x1b0) ∗
        (memRegion (sp + 0x140#64) 0x50 ∗
         createChainResultAt (sp + 0x190#64) (rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
         memRegion x.ret 48 ∗
         memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
         memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
         tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
      dsimp only [Frame1] at hpost
      rw [show sc1.sp = sp from hsp_c1] at hpost
      unfold tryDecryptCommonHeap
      rw [signalMessageAt_senderRatchetKey A x.msgG x.msgA x.msg,
          show s0.sp - 1504#64 = sp from rfl,
          stackAt_subStack_createChain sp]
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hpost
    have hpost_folded :=
      Satisfies.mono (sepConj_mono_left (fold_390_3b0_to_memRegion sp _ _ hpriv_len hrk_len)) hpost_grouped
    unfold rootCreateChain at hpost_folded ⊢
    cases hcc1 : Ratchet.createChain C.F C.X tr.ratchet.rootKey x.msg.senderRatchetKey.bytes sc.ratchetKey.privateKey.bytes with
    | none =>
      rw [hcc1] at hpost_folded
      dsimp only [hcc1] at hpost_folded ⊢
      let Rest_err : SepProp :=
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
        memRegion x.ret 48 ∗
        memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
        memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
        tryDecryptCommonHeap A ctl img x 0 s0 ∗ R
      have hmem_err : sm.mem ⊨
          memRegion (sp + 0x140#64) 0x50 ∗
          createChainResultAt (sp + 0x190#64) (.error .invalidKeyAgreement) ∗
          memRegion (sp + 0x1d8#64) 0x3a8 ∗ Rest_err :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [Rest_err]; ac_rfl)) hpost_folded
      obtain ⟨s', hsteps2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
        dhStep_cc1_err_branch (A := A) (ext := ext)
          himg Rest_err s0 sm hpcm hmeta_m hx20_m hx23_m hx25_m hx26_m hmem_err
          (hsteps12.codeLoaded hcode)
      refine ⟨s', Steps.trans hsteps12 hsteps2, Or.inl ⟨trG, { tr.ratchet with rootKey := (0 : RootKey) }, ?_⟩⟩
      refine ⟨hpcs', hmetas', hx19s'.trans hx19_m, hx20s', hx26s', ?_⟩
      dsimp only [Rest_err] at hmems'
      have hsp38_ent :
          (memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA)) ⊢
          memRegion sp 0x38 := by
        rw [memRegion_split' (b := sp) (b' := sp + 0x20#64) (n := 0x20) (k := 0x18) rfl (by bv_arith) (by decide),
            memRegion_split' (b := sp + 0x20#64) (b' := sp + 0x28#64) (n := 0x8) (k := 0x10) rfl (by bv_arith) (by decide),
            memRegion_split' (b := sp + 0x28#64) (b' := sp + 0x2c#64) (n := 0x4) (k := 0xc) rfl (by bv_arith) (by decide),
            memRegion_split' (b := sp + 0x2c#64) (b' := sp + 0x30#64) (n := 0x4) (k := 0x8) rfl (by bv_arith) (by decide)]
        exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo32_entails_memRegion _ _)
            (sepConj_mono_right (pointsTo64_entails_memRegion _ _))))
      have hmems1 : s'.mem ⊨
          (memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA)) ∗
          (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
           memRegion x.ret 48 ∗
           memRegion (sp + 0x140#64) 0x28 ∗
           speBodyAt A (utf8 "decrypt") (sp + 0x168#64) .invalidKeyAgreement ∗
           memRegion (sp + 0x190#64) 0x3f0 ∗
           tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) :=
        Eq.mp (congrArg (s'.mem ⊨ ·) (by dsimp only [sp] at hmems' ⊢; ac_rfl)) hmems'
      have hmems2 := Satisfies.mono (sepConj_mono_left hsp38_ent) hmems1
      dsimp only [sp] at hmems2 ⊢
      exact Eq.mp (congrArg (s'.mem ⊨ ·) (by ac_rfl)) hmems2
    | some p1 =>
      rcases p1 with ⟨rk1, rckKey⟩
      rw [hcc1] at hpost_folded
      dsimp only [hcc1] at hpost_folded ⊢
      let Rest_ok : SepProp :=
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
        memRegion x.ret 48 ∗
        memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
        memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
        memRegion (sp + 0x140#64) 0x50 ∗
        memRegion (sp + 0x1d8#64) 0x3a8 ∗
        tryDecryptCommonHeap A ctl img x 0 s0 ∗ R
      have hmem_ok : sm.mem ⊨
          createChainResultAt (sp + 0x190#64) (.ok (rk1, ⟨rckKey, 0⟩)) ∗ Rest_ok :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [Rest_ok]; ac_rfl)) hpost_folded
      obtain ⟨s', hsteps2, hpcs', hmetas', hcss', hmems'⟩ :=
        dhStep_cc1_ok_branch (ext := ext)
          himg rk1 ⟨rckKey, 0⟩ Rest_ok s0 sm hpcm hmeta_m hmem_ok
          (hsteps12.codeLoaded hcode)
      refine ⟨s', Steps.trans hsteps12 hsteps2, Or.inl ?_⟩
      refine ⟨hpcs', hmetas',
        hcss'.1.trans hx19_m,
        hcss'.2.1.trans hx20_m,
        hcss'.2.2.1.trans hx21_m,
        hcss'.2.2.2.1.trans hx22_m,
        hcss'.2.2.2.2.1.trans hx23_m,
        by rw [hcss'.2.2.2.2.2.1]; exact hx24_m,
        hcss'.2.2.2.2.2.2.1.trans hx25_m,
        hcss'.2.2.2.2.2.2.2.1.trans hx26_m,
        hcss'.2.2.2.2.2.2.2.2.1.trans hx27_m,
        hcss'.2.2.2.2.2.2.2.2.2.1.trans hx28_m, ?_⟩
      dsimp only [Rest_ok, sp] at hmems' ⊢
      exact Eq.mp (congrArg (s'.mem ⊨ ·) (by ac_rfl)) hmems'
  · -- Panic in `RootKey::create_chain` #1
    have hpan_td := onPanic_of_createChain (ctl := ctl) (S := S) (x := x) htrace_c1 hpost
    cases rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | ok p1 =>
      rcases p1 with ⟨rk1, rck⟩
      exact ⟨sm, hsteps12, Or.inr ⟨hpan, hpan_td⟩⟩
    | error e =>
      exact ⟨sm, hsteps12, Or.inr ⟨hpan, hpan_td⟩⟩
  · -- Impossible `.Exited` case
    dsimp only [createChainSpec, Spec.inImage] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1

theorem rk_ne_zero (sp0 sp : BitVec 64) (hsp : sp = sp0 - 1504#64) (hb : 2 ^ 18 ≤ sp0.toNat) :
    sp + 0x3b0#64 ≠ 0#64 ∧ sp + 0x4a0#64 ≠ 0#64 := by
  subst hsp; constructor <;> bv_omega

/-- Pack 4 bytes (little-endian) into a `BitVec 32`. -/
def pack32 (bs : List (BitVec 8)) : BitVec 32 := DhStep.packBV 32 bs

theorem unpack32_pack32 (bs : List (BitVec 8)) (h : bs.length = 4) :
    unpack32 (pack32 bs) = bs := by
  have h1 : unpack32 (pack32 bs) = bytesOfBV bs.length (DhStep.packBV 32 bs) := by
    rw [h]
    unfold unpack32 bytesOfBV pack32
    rw [show List.range 4 = [0, 1, 2, 3] from rfl]
    rfl
  rw [h1]
  exact bytesOfBV_packBV 32 bs (by omega)

theorem pointsToBytes_4_eq_pointsTo32 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 4) :
    (a ↦ₛ bs) = (a ↦₃₂ pack32 bs) := by
  rw [pointsTo32_eq_pointsToBytes, unpack32_pack32 bs h]

theorem pointsTo_16_as_two_64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 16) :
    (a ↦ₛ bs) =
      ((a ↦₆₄ pack64 (bs.take 8)) ∗
       ((a + 8#64) ↦₆₄ pack64 (bs.drop 8))) := by
  have h1 : (bs.take 8).length = 8 := by simp [h]
  have h2 : (bs.drop 8).length = 8 := by simp [h]
  conv_lhs => rw [← List.take_append_drop 8 bs]
  rw [pointsToBytes_append, h1,
      pointsToBytes_8_eq_pointsTo64 a (bs.take 8) h1,
      pointsToBytes_8_eq_pointsTo64 (a + 8#64) (bs.drop 8) h2]

theorem pointsTo_32_as_4_8_8_8_4 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) =
      ((a ↦₃₂ pack32 (bs.take 4)) ∗
       ((a + 4#64) ↦₆₄ pack64 ((bs.drop 4).take 8)) ∗
       ((a + 12#64) ↦₆₄ pack64 ((bs.drop 12).take 8)) ∗
       ((a + 20#64) ↦₆₄ pack64 ((bs.drop 20).take 8)) ∗
       ((a + 28#64) ↦₃₂ pack32 (bs.drop 28))) := by
  have h1 : (bs.take 4).length = 4 := by simp [h]
  have h2 : ((bs.drop 4).take 8).length = 8 := by simp [h]
  have h3 : ((bs.drop 12).take 8).length = 8 := by simp [h]
  have h4 : ((bs.drop 20).take 8).length = 8 := by simp [h]
  have h5 : (bs.drop 28).length = 4 := by simp [h]
  have hsplit : bs = bs.take 4 ++ ((bs.drop 4).take 8 ++ ((bs.drop 12).take 8 ++ ((bs.drop 20).take 8 ++ bs.drop 28))) := by
    conv_lhs => rw [← List.take_append_drop 4 bs]
    congr 1
    conv_lhs => rw [← List.take_append_drop 8 (bs.drop 4)]
    rw [List.drop_drop]
    congr 1
    conv_lhs => rw [← List.take_append_drop 8 (bs.drop 12)]
    rw [List.drop_drop]
    congr 1
    conv_lhs => rw [← List.take_append_drop 8 (bs.drop 20)]
    rw [List.drop_drop]
  conv_lhs => rw [hsplit]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      h1, h2, h3, h4,
      pointsToBytes_4_eq_pointsTo32 a (bs.take 4) h1,
      pointsToBytes_8_eq_pointsTo64 (a + 4#64) ((bs.drop 4).take 8) h2,
      pointsToBytes_8_eq_pointsTo64 (a + 4#64 + 8#64) ((bs.drop 12).take 8) h3,
      pointsToBytes_8_eq_pointsTo64 (a + 4#64 + 8#64 + 8#64) ((bs.drop 20).take 8) h4,
      pointsToBytes_4_eq_pointsTo32 (a + 4#64 + 8#64 + 8#64 + 8#64) (bs.drop 28) h5,
      show a + 4#64 + 8#64 = a + 12#64 by bv_arith,
      show a + 12#64 + 8#64 = a + 20#64 by bv_arith,
      show a + 20#64 + 8#64 = a + 28#64 by bv_arith]

theorem pointsTo_36_as_8_8_4_8_8 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 36) :
    (a ↦ₛ bs) =
      ((a ↦₆₄ pack64 (bs.take 8)) ∗
       ((a + 8#64) ↦₆₄ pack64 ((bs.drop 8).take 8)) ∗
       ((a + 16#64) ↦₃₂ pack32 ((bs.drop 16).take 4)) ∗
       ((a + 20#64) ↦₆₄ pack64 ((bs.drop 20).take 8)) ∗
       ((a + 28#64) ↦₆₄ pack64 (bs.drop 28))) := by
  have h1 : (bs.take 8).length = 8 := by simp [h]
  have h2 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have h3 : ((bs.drop 16).take 4).length = 4 := by simp [h]
  have h4 : ((bs.drop 20).take 8).length = 8 := by simp [h]
  have h5 : (bs.drop 28).length = 8 := by simp [h]
  have hsplit : bs = bs.take 8 ++ ((bs.drop 8).take 8 ++ ((bs.drop 16).take 4 ++ ((bs.drop 20).take 8 ++ bs.drop 28))) := by
    conv_lhs => rw [← List.take_append_drop 8 bs]
    congr 1
    conv_lhs => rw [← List.take_append_drop 8 (bs.drop 8)]
    rw [List.drop_drop]
    congr 1
    conv_lhs => rw [← List.take_append_drop 4 (bs.drop 16)]
    rw [List.drop_drop]
    congr 1
    conv_lhs => rw [← List.take_append_drop 8 (bs.drop 20)]
    rw [List.drop_drop]
  conv_lhs => rw [hsplit]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      h1, h2, h3, h4,
      pointsToBytes_8_eq_pointsTo64 a (bs.take 8) h1,
      pointsToBytes_8_eq_pointsTo64 (a + 8#64) ((bs.drop 8).take 8) h2,
      pointsToBytes_4_eq_pointsTo32 (a + 8#64 + 8#64) ((bs.drop 16).take 4) h3,
      pointsToBytes_8_eq_pointsTo64 (a + 8#64 + 8#64 + 4#64) ((bs.drop 20).take 8) h4,
      pointsToBytes_8_eq_pointsTo64 (a + 8#64 + 8#64 + 4#64 + 8#64) (bs.drop 28) h5,
      show a + 8#64 + 8#64 = a + 16#64 by bv_arith,
      show a + 16#64 + 4#64 = a + 20#64 by bv_arith,
      show a + 20#64 + 8#64 = a + 28#64 by bv_arith]

theorem pointsTo8_eq_pointsToBytes1 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) = (a ↦ₛ [b]) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem vec32_toList_split_ends (v : List.Vector (BitVec 8) 32) :
    v.toList =
      [v.get ⟨0, by decide⟩] ++ ((v.toList.drop 1).take 30 ++ [v.get ⟨31, by decide⟩]) := by
  rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    first | (dsimp [List.Vector.toList, List.Vector.get]; rfl) | cases hl

theorem vec32_clampScalar_toList_eq (v : List.Vector (BitVec 8) 32) :
    (Ratchet.clampScalar v).toList =
      [v.get ⟨0, by decide⟩ &&& 0xf8#8] ++
        ((v.toList.drop 1).take 30 ++ [(v.get ⟨31, by decide⟩ &&& 0x7f#8) ||| 0x40#8]) := by
  rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    first | (dsimp [List.Vector.toList, List.Vector.get, Ratchet.clampScalar, List.Vector.set]; rfl) | cases hl

theorem pointsTo_vec32_split_ends (a : BitVec 64) (v : List.Vector (BitVec 8) 32) :
    (a ↦ₛ v.toList) =
      ((a ↦₈ v.get ⟨0, by decide⟩) ∗
       ((a + 1#64) ↦ₛ (v.toList.drop 1).take 30) ∗
       ((a + 31#64) ↦₈ v.get ⟨31, by decide⟩)) := by
  have hmid : ((v.toList.drop 1).take 30).length = 30 := by simp
  conv_lhs => rw [vec32_toList_split_ends v]
  rw [pointsToBytes_append, pointsToBytes_append,
      show ([v.get ⟨0, by decide⟩] : List (BitVec 8)).length = 1 from rfl, hmid,
      ← pointsTo8_eq_pointsToBytes1 a,
      ← pointsTo8_eq_pointsToBytes1 (a + 1#64 + 30#64),
      show a + 1#64 + 30#64 = a + 31#64 by bv_arith]

theorem pointsTo_vec32_clamp_fold (a : BitVec 64) (v : List.Vector (BitVec 8) 32) :
    ((a ↦₈ (v.get ⟨0, by decide⟩ &&& 0xf8#8)) ∗
     ((a + 1#64) ↦ₛ (v.toList.drop 1).take 30) ∗
     ((a + 31#64) ↦₈ ((v.get ⟨31, by decide⟩ &&& 0x7f#8) ||| 0x40#8))) =
      (a ↦ₛ (Ratchet.clampScalar v).toList) := by
  have hmid : ((v.toList.drop 1).take 30).length = 30 := by simp
  conv_rhs => rw [vec32_clampScalar_toList_eq v]
  rw [pointsToBytes_append, pointsToBytes_append,
      show ([v.get ⟨0, by decide⟩ &&& 0xf8#8] : List (BitVec 8)).length = 1 from rfl, hmid,
      ← pointsTo8_eq_pointsToBytes1 a,
      ← pointsTo8_eq_pointsToBytes1 (a + 1#64 + 30#64),
      show a + 1#64 + 30#64 = a + 31#64 by bv_arith]

/-- Success branch after `RootKey::create_chain` #2 (`+0x7d8 → +0x8ac`): when `[sp + 0x190]`
holds tag `0#32` (`.ok (finalRootKey, senderChainKey)`), `subs wzr, w8, #1; b.ne +0xcc` branches to
`segDhCommitPC img` (`+0x8ac` = `entry + 2220`). -/
theorem dhStep_cc2_ok_branch {img : Obj.Image} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (finalRootKey : RootKey) (senderChainKey : ChainKey) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 2008#64)
    (hmeta : tryDecryptMidMeta img s0 s)
    (hmem : s.mem ⊨
      createChainResultAt (s0.sp - 1504#64 + 0x190#64) (.ok (finalRootKey, senderChainKey)) ∗ Rest)
    (hcode : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      s'.pc = segDhCommitPC img ∧
      tryDecryptMidMeta img s0 s' ∧
      CalleeSavedPreserved s s' ∧
      (s'.mem ⊨
        ((s0.sp - 1504#64 + 0x190#64) ↦₃₂ 0#32) ∗
        ((s0.sp - 1504#64 + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
        ((s0.sp - 1504#64 + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗ Rest) := by
  have hentry := entryOf_eq_tripleRatchetProgAtExt (ext := ext)
    himg tryDecryptName
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hfr, hsym, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hfn : libsignalSessionCode.fnOff tryDecryptName = num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  td_fetches img.base (Rust.withPanics ext) hfn 2008 12
  dsimp only [createChainResultAt] at hmem
  rw [show sp + 0x190#64 + 4#64 = sp + 0x194#64 by bv_arith,
      show sp + 0x190#64 + 0x24#64 = sp + 0x1b4#64 by bv_arith] at hmem
  have hwp : SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 2220#64) s
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
      (((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
       ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗ Rest) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hmem
  obtain ⟨sm, hsteps1, hout1⟩ := hwp.elim hmem_framed hcode
  obtain ⟨hpcm, hrunm, P_m, hmem_m, hsp_m, hcs_m, htrace_m, hent_m⟩ :=
    hout1.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_m : sm.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_m, ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hpcm' : sm.pc = segDhCommitPC img := by
    unfold segDhCommitPC tryDecryptEntry; rw [hentry]; exact hpcm
  have hx29_m : sm.readReg64 .x29 = s0.sp - 96#64 := hcs_m.2.2.2.2.2.2.2.2.2.2.1.trans hx29
  have hmeta_m : tryDecryptMidMeta img s0 sm :=
    ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hsteps1.frozenLoaded hfr, hsteps1.symtab_eq.trans hsym, by reg_chain⟩
  have hmem_m0 := hent_m sm.mem _ hmem_m
  exact ⟨sm, hsteps1, hpcm', hmeta_m, hcs_m, Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmem_m0⟩

/-- Error branch after `RootKey::create_chain` #2 (`+0x7d8 → +0x7f8 → +0x30c`). -/
theorem dhStep_cc2_err_branch {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (msgW : BitVec 32) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 2008#64)
    (hmeta : tryDecryptMidMeta img s0 s)
    (hx20 : s.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64)
    (hx23 : s.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hx26 : s.readReg64 .x26 = s0.sp - 1504#64 + 0x2c0#64)
    (hmem : s.mem ⊨
      ((s0.sp - 1504#64 + 0x1c#64) ↦₃₂ msgW) ∗
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
        ((s0.sp - 1504#64 + 0x1c#64) ↦₃₂ msgW) ∗
        memRegion (s0.sp - 1504#64 + 0x140#64) 0x28 ∗
        speBodyAt A (utf8 "decrypt") (s0.sp - 1504#64 + 0x168#64) .invalidKeyAgreement ∗
        memRegion (s0.sp - 1504#64 + 0x190#64) 0x3f0 ∗ Rest) := by
  have hentry := entryOf_eq_tripleRatchetProgAtExt (ext := ext)
    himg tryDecryptName
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hfr, hsym, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hfn : libsignalSessionCode.fnOff tryDecryptName = num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  td_fetches img.base (Rust.withPanics ext) hfn 2008 32
  dsimp only [createChainResultAt] at hmem
  rw [show sp + 0x190#64 + 4#64 = sp + 0x194#64 by bv_arith,
      show sp + 0x190#64 + 8#64 = sp + 0x198#64 by bv_arith,
      show sp + 0x190#64 + 16#64 = sp + 0x1a0#64 by bv_arith,
      split_1a0_56 sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u1c4, u1bc, u1b4, u1b0, u1a8, u1a0, hmem⟩
  have hwp : SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 2040#64) s
      (((sp + 0x1c#64) ↦₃₂ msgW) ∗
       ((sp + 0x190#64) ↦₃₂ 1#32) ∗
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
          (m ⊨ (((sp + 0x1c#64) ↦₃₂ msgW) ∗
                ((sp + 0x190#64) ↦₃₂ 1#32) ∗
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
      (((sp + 0x1c#64) ↦₃₂ msgW) ∗
       ((sp + 0x190#64) ↦₃₂ 1#32) ∗
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
  obtain ⟨sm, hsteps1, hout1⟩ := hwp.elim hmem_framed hcode
  obtain ⟨hpcm, hrunm, P_m, hmem_m, hsp_m, hx29_m, hx19_m, hx20_m, hx23_m, hx25_m, hx26_m, htrace_m, hvregs_m, hent_m⟩ :=
    hout1.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
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
      (((sp + 0x198#64) ↦₆₄ speWord 10) ∗ ((sp + 0x1c#64) ↦₃₂ msgW) ∗ Rest) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmem_m0
  have hmem_m2 := Satisfies.mono (sepConj_mono_left (fold_for_7f8 sp 1#32 u1a0 u1a8 u1b4 u1bc u1b0 u1c4)) hmem_m1
  have hmem_m3 : sm.mem ⊨
      memRegion (sp + 0x140#64) 0x58 ∗
      ((sp + 0x198#64) ↦₆₄ speWord 10) ∗
      memRegion (sp + 0x1a0#64) 0x3e0 ∗ (((sp + 0x1c#64) ↦₃₂ msgW) ∗ Rest) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmem_m2
  obtain ⟨s', hsteps2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
    dhStep_err_tail_from_7f8 (A := A) (ext := ext)
      himg (((sp + 0x1c#64) ↦₃₂ msgW) ∗ Rest) s0 sm hpcm' hmeta_m hx20_m hx23_m hx25_m hx26_m hmem_m3
      (hsteps1.codeLoaded hcode)
  exact ⟨s', Steps.trans hsteps1 hsteps2, hpcs', hmetas', hx19s'.trans hx19_m, hx20s', hx26s',
    Eq.mp (congrArg (s'.mem ⊨ ·) (by dsimp only [sp] at hmems' ⊢; ac_rfl)) hmems'⟩

end CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep
