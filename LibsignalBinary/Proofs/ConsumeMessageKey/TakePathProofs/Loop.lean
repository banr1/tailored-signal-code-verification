/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
public import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.Common
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Model
import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.DuplicatedMessageReturn
import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.Fetch
import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.Remove
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalSession.TakePath

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.SessionModel
open ProofLib.ProgramReflection

set_option maxHeartbeats 1600000

@[local simp] theorem bv_add_48_8 (x : BitVec 64) : x + 48#64 + 8#64 = x + 56#64 := by bv_omega
@[local simp] theorem bv_add_48_16 (x : BitVec 64) : x + 48#64 + 16#64 = x + 64#64 := by bv_omega
@[local simp] theorem bv_add_56_40 (x : BitVec 64) : x + 56#64 + 40#64 = x + 96#64 := by bv_omega

@[local simp] theorem truncate_32_zeroExtend_64 (x : BitVec 32) :
    (x.zeroExtend 64).truncate 32 = x := by
  ext i hi
  simp

/-! ## `ratchetAt` Chain Exposure and Reassembly -/

/-- Pure invariants extracted when splitting `ratchetAt A self G st` at receiver chain `ci`. -/
structure RatchetChainProps (G : RatchetGhost) (st : RatchetState) (ci : Nat)
    (hgi : ci < G.chains.length) (hci : ci < st.receiverChains.length) : Prop where
  chains_len : G.chains.length = st.receiverChains.length
  pad_len : G.senderPad.length = 100
  max_jumps : st.maxForwardJumps < 2 ^ 64
  cap_le : st.receiverChains.length ≤ G.chainsCap.toNat
  cap_lt : G.chainsCap.toNat * 104 < 2 ^ 63
  ptr_ne : G.chainsPtr ≠ 0
  cap_ne : G.chainsCap ≠ 0
  srk_ok : PublicKey.deserialize G.chains[ci].srk.bytes = .ok st.receiverChains[ci].senderRatchetKey
  mk_max : st.receiverChains[ci].messageKeys.length ≤ maxMessageKeys
  keys_len : G.chains[ci].keys.length = st.receiverChains[ci].messageKeys.length
  srk_len : G.chains[ci].srk.bytes.length = 33
  priv_nil : G.chains[ci].priv.bytes = []

/-- The framed portion of `ratchetAt A self G st` when chain `ci`'s `mkPtr` cell (`+56`),
`mkLen` cell (`+64`), and `vecBuf` of `MessageKey`s are focused. -/
def ratchetChainRest (A : RustAlloc) (self : BitVec 64) (G : RatchetGhost)
    (st : RatchetState) (ci : Nat) (hgi : ci < G.chains.length)
    (hci : ci < st.receiverChains.length) : SepProp :=
  let chAddr := G.chainsPtr + BitVec.ofNat 64 (ci * 104)
  let g := G.chains[ci]
  let c := st.receiverChains[ci]
  vecHeader self G.chainsCap G.chainsPtr (BitVec.ofNat 64 st.receiverChains.length) ∗
  A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
  vecGhostAt A g.srk chAddr ∗
  vecGhostAt A g.priv (chAddr + 24#64) ∗
  ((chAddr + 48#64) ↦₆₄ g.mkCap) ∗
  optChainKeyAt A g.ck c.chainKey (chAddr + 72#64) ∗
  arrayAt (chainAt A) 104 G.chainsPtr ((G.chains.zip st.receiverChains).take ci) ∗
  arrayAt (chainAt A) 104 (G.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
    ((G.chains.zip st.receiverChains).drop (ci + 1)) ∗
  memRegion (G.chainsPtr + BitVec.ofNat 64 (st.receiverChains.length * 104))
    ((G.chainsCap.toNat - st.receiverChains.length) * 104) ∗
  ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
  ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
  ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
  ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4

theorem vecAt_messageKeyAt_eq (A : RustAlloc) (chAddr mkCap mkPtr : BitVec 64)
    (gks : List (MessageKeyGhost × MessageKeyGenerator)) :
    vecAt A 104 8 (messageKeyAt A) (chAddr + 48#64) mkCap mkPtr gks =
      ((chAddr + 48#64) ↦₆₄ mkCap) ∗
      ((chAddr + 56#64) ↦₆₄ mkPtr) ∗
      ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
      vecBuf A 104 8 (messageKeyAt A) mkCap mkPtr gks := by
  unfold vecAt vecHeader
  simp only [bv_add_48_8, bv_add_48_16, sepConj_assoc]

theorem chainAt_expose_mk (A : RustAlloc) (g : ChainGhost) (c : ReceiverChain) (chAddr : BitVec 64) :
    chainAt A (g, c) chAddr =
      ⌜PublicKey.deserialize g.srk.bytes = .ok c.senderRatchetKey ∧
        c.messageKeys.length ≤ maxMessageKeys ∧ g.keys.length = c.messageKeys.length ∧
        g.srk.bytes.length = 33 ∧ g.priv.bytes = []⌝ ∗
      vecGhostAt A g.srk chAddr ∗
      vecGhostAt A g.priv (chAddr + 24#64) ∗
      (((chAddr + 48#64) ↦₆₄ g.mkCap) ∗
        ((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
        ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 (g.keys.zip c.messageKeys).length) ∗
        vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr (g.keys.zip c.messageKeys)) ∗
      optChainKeyAt A g.ck c.chainKey (chAddr + 72#64) := by
  unfold chainAt
  rw [vecAt_messageKeyAt_eq]

theorem ratchetAt_expose_chain (A : RustAlloc) (self : BitVec 64) (G : RatchetGhost)
    (st : RatchetState) {ci : Nat} (hci : ci < st.receiverChains.length)
    (hgi : ci < G.chains.length) :
    ratchetAt A self G st ⊢
      ⌜RatchetChainProps G st ci hgi hci⌝ ∗
      ((G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ G.chains[ci].mkPtr) ∗
      ((G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄
        BitVec.ofNat 64 (G.chains[ci].keys.zip st.receiverChains[ci].messageKeys).length) ∗
      vecBuf A 104 8 (messageKeyAt A) G.chains[ci].mkCap G.chains[ci].mkPtr
        (G.chains[ci].keys.zip st.receiverChains[ci].messageKeys) ∗
      ratchetChainRest A self G st ci hgi hci := by
  set chAddr := G.chainsPtr + BitVec.ofNat 64 (ci * 104)
  set g := G.chains[ci]
  set c := st.receiverChains[ci]
  set gks := g.keys.zip c.messageKeys
  refine Entails.trans (ratchetAt_split_chain A self G st hci hgi) ?_
  apply Entails.pure_left
  rintro ⟨hchains_len, hpad_len, hmax_jumps, hcap_le, hcap_lt, hptr_ne, hcap_ne⟩
  rw [chainAt_expose_mk A g c chAddr]
  unfold ratchetChainRest
  dsimp only [chAddr, g, c, gks]
  have hpull :
      (vecHeader self G.chainsCap G.chainsPtr (BitVec.ofNat 64 st.receiverChains.length) ∗
        A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
        (⌜PublicKey.deserialize g.srk.bytes = .ok c.senderRatchetKey ∧
          c.messageKeys.length ≤ maxMessageKeys ∧ g.keys.length = c.messageKeys.length ∧
          g.srk.bytes.length = 33 ∧ g.priv.bytes = []⌝ ∗
          vecGhostAt A g.srk chAddr ∗
          vecGhostAt A g.priv (chAddr + 24#64) ∗
          (((chAddr + 48#64) ↦₆₄ g.mkCap) ∗
            ((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
            ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
            vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks) ∗
          optChainKeyAt A g.ck c.chainKey (chAddr + 72#64)) ∗
        arrayAt (chainAt A) 104 G.chainsPtr ((G.chains.zip st.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (G.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((G.chains.zip st.receiverChains).drop (ci + 1)) ∗
        memRegion (G.chainsPtr + BitVec.ofNat 64 (st.receiverChains.length * 104))
          ((G.chainsCap.toNat - st.receiverChains.length) * 104) ∗
        ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
        ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
        ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
        ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4) =
      (⌜PublicKey.deserialize g.srk.bytes = .ok c.senderRatchetKey ∧
        c.messageKeys.length ≤ maxMessageKeys ∧ g.keys.length = c.messageKeys.length ∧
        g.srk.bytes.length = 33 ∧ g.priv.bytes = []⌝ ∗
       (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
        ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
        vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks ∗
        (vecHeader self G.chainsCap G.chainsPtr (BitVec.ofNat 64 st.receiverChains.length) ∗
          A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
          vecGhostAt A g.srk chAddr ∗
          vecGhostAt A g.priv (chAddr + 24#64) ∗
          ((chAddr + 48#64) ↦₆₄ g.mkCap) ∗
          optChainKeyAt A g.ck c.chainKey (chAddr + 72#64) ∗
          arrayAt (chainAt A) 104 G.chainsPtr ((G.chains.zip st.receiverChains).take ci) ∗
          arrayAt (chainAt A) 104 (G.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
            ((G.chains.zip st.receiverChains).drop (ci + 1)) ∗
          memRegion (G.chainsPtr + BitVec.ofNat 64 (st.receiverChains.length * 104))
            ((G.chainsCap.toNat - st.receiverChains.length) * 104) ∗
          ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
          ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
          ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
          ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4))) := by
    ac_rfl
  rw [hpull]
  apply Entails.pure_left
  rintro ⟨hsrk, hmax, hklen, hsrk_len, hpriv⟩
  exact Entails.pure_right
    ⟨hchains_len, hpad_len, hmax_jumps, hcap_le, hcap_lt, hptr_ne, hcap_ne,
      hsrk, hmax, hklen, hsrk_len, hpriv⟩
    (Entails.refl _)

/-- Reassemble `ratchetAt` when chain `ci` is unchanged. -/
theorem ratchetAt_reassemble_self (A : RustAlloc) (self : BitVec 64) (G : RatchetGhost)
    (st : RatchetState) {ci : Nat} (hci : ci < st.receiverChains.length)
    (hgi : ci < G.chains.length)
    (hprops : RatchetChainProps G st ci hgi hci) :
    (((G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ G.chains[ci].mkPtr) ∗
      ((G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄
        BitVec.ofNat 64 (G.chains[ci].keys.zip st.receiverChains[ci].messageKeys).length) ∗
      vecBuf A 104 8 (messageKeyAt A) G.chains[ci].mkCap G.chains[ci].mkPtr
        (G.chains[ci].keys.zip st.receiverChains[ci].messageKeys) ∗
      ratchetChainRest A self G st ci hgi hci) ⊢
      ratchetAt A self G st := by
  set chAddr := G.chainsPtr + BitVec.ofNat 64 (ci * 104)
  set g := G.chains[ci]
  set c := st.receiverChains[ci]
  set gks := g.keys.zip c.messageKeys
  have hsetG : G.setChain ci g = G := by
    cases G
    simp [RatchetGhost.setChain, g, List.set_getElem_self]
  have hsetSt : st.setChain ci c = st := by
    cases st
    simp [RatchetState.setChain, c, List.set_getElem_self]
  conv => rhs; rw [← hsetG, ← hsetSt]
  refine Entails.trans ?_
    (ratchetAt_set_chain A self G st hci g c
      hprops.chains_len hprops.pad_len hprops.max_jumps
      hprops.cap_le hprops.cap_lt hprops.ptr_ne)
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (chainAt_of_update_messageKeys A g c chAddr g.mkCap g.mkPtr g.keys c.messageKeys
        hprops.srk_ok hprops.mk_max hprops.keys_len hprops.srk_len hprops.priv_nil))))
  rw [vecAt_messageKeyAt_eq]
  unfold ratchetChainRest
  dsimp only [chAddr, g, c, gks]
  exact entails_of_eq (by ac_rfl) (Entails.refl _)

/-- Reassemble `ratchetAt` after removing index `p` from chain `ci`'s `messageKeys`. -/
theorem ratchetAt_reassemble_eraseIdx (A : RustAlloc) (self : BitVec 64) (G : RatchetGhost)
    (st : RatchetState) {ci : Nat} (hci : ci < st.receiverChains.length)
    (hgi : ci < G.chains.length)
    (hprops : RatchetChainProps G st ci hgi hci)
    {p : Nat} (hp : p < (G.chains[ci].keys.zip st.receiverChains[ci].messageKeys).length) :
    (((G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ G.chains[ci].mkPtr) ∗
      ((G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄
        BitVec.ofNat 64 ((G.chains[ci].keys.zip st.receiverChains[ci].messageKeys).length - 1)) ∗
      vecBuf A 104 8 (messageKeyAt A) G.chains[ci].mkCap G.chains[ci].mkPtr
        ((G.chains[ci].keys.zip st.receiverChains[ci].messageKeys).eraseIdx p) ∗
      ratchetChainRest A self G st ci hgi hci) ⊢
      ratchetAt A self
        (G.setChain ci { G.chains[ci] with keys := G.chains[ci].keys.eraseIdx p })
        (st.setChain ci { st.receiverChains[ci] with messageKeys := st.receiverChains[ci].messageKeys.eraseIdx p }) := by
  set chAddr := G.chainsPtr + BitVec.ofNat 64 (ci * 104)
  set g := G.chains[ci]
  set c := st.receiverChains[ci]
  set gks := g.keys.zip c.messageKeys
  set g' : ChainGhost := { g with keys := g.keys.eraseIdx p }
  set c' : ReceiverChain := { c with messageKeys := c.messageKeys.eraseIdx p }
  have hkl : g.keys.length = c.messageKeys.length := hprops.keys_len
  have hmax : c.messageKeys.length ≤ maxMessageKeys := hprops.mk_max
  have hzip_len : gks.length = c.messageKeys.length := by
    simp [gks, hkl]
  have hp_c : p < c.messageKeys.length := by omega
  have hp_g : p < g.keys.length := by omega
  have hmax' : c'.messageKeys.length ≤ maxMessageKeys := by
    simp only [c', List.length_eraseIdx_of_lt hp_c]
    omega
  have hklen' : g'.keys.length = c'.messageKeys.length := by
    simp only [g', c', List.length_eraseIdx_of_lt hp_g, List.length_eraseIdx_of_lt hp_c, hkl]
  have hzip_erase : g'.keys.zip c'.messageKeys = gks.eraseIdx p :=
    zip_eraseIdx_eq g.keys c.messageKeys p
  have herase_len : (gks.eraseIdx p).length = gks.length - 1 :=
    List.length_eraseIdx_of_lt hp
  refine Entails.trans ?_
    (ratchetAt_set_chain A self G st hci g' c'
      hprops.chains_len hprops.pad_len hprops.max_jumps
      hprops.cap_le hprops.cap_lt hprops.ptr_ne)
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (chainAt_of_update_messageKeys A g c chAddr g.mkCap g.mkPtr g'.keys c'.messageKeys
        hprops.srk_ok hmax' hklen' hprops.srk_len hprops.priv_nil))))
  rw [hzip_erase, vecAt_messageKeyAt_eq, herase_len]
  unfold ratchetChainRest
  dsimp only [chAddr, g, c, gks]
  exact entails_of_eq (by ac_rfl) (Entails.refl _)

/-! ## `remove(p)` and `Ok` Return Outcome (`+0x5e4 → +0x77c`) -/

theorem cmk_model_past_hit (F : ShaState → List (BitVec 8) → ShaState) (x : ConsumeMessageKeyGhost)
    {ci : Nat} (hci : x.st.findReceiverChainIndex x.their = some ci)
    (hi : ci < x.st.receiverChains.length)
    {p : Nat} (hp : p < x.st.receiverChains[ci].messageKeys.length)
    (hfind : x.st.receiverChains[ci].messageKeys.findIdx? (fun k => k.counter == x.counter) = some p)
    (hc_lt : x.counter < x.ck.index) :
    x.model F =
      (.ok x.st.receiverChains[ci].messageKeys[p],
       x.st.setChain ci
         { x.st.receiverChains[ci] with
           messageKeys := x.st.receiverChains[ci].messageKeys.eraseIdx p }) := by
  unfold ConsumeMessageKeyGhost.model RatchetState.setChain
  simp only [consumeMessageKey_past F x.st x.their x.ck x.counter x.msgType hc_lt,
    hci, List.getElem?_eq_getElem hi, Option.map_some, hfind,
    List.getElem?_eq_getElem hp]

theorem cmk_model_past_miss_chain (F : ShaState → List (BitVec 8) → ShaState) (x : ConsumeMessageKeyGhost)
    {ci : Nat} (hci : x.st.findReceiverChainIndex x.their = some ci)
    (hi : ci < x.st.receiverChains.length)
    (hfind : x.st.receiverChains[ci].messageKeys.findIdx? (fun k => k.counter == x.counter) = none)
    (hc_lt : x.counter < x.ck.index) :
    x.model F = (.error (.duplicatedMessage x.ck.index x.counter), x.st) := by
  unfold ConsumeMessageKeyGhost.model
  simp only [consumeMessageKey_past F x.st x.their x.ck x.counter x.msgType hc_lt,
    hci, List.getElem?_eq_getElem hi, Option.map_some, hfind]

theorem cmk_model_past_no_chain (F : ShaState → List (BitVec 8) → ShaState) (x : ConsumeMessageKeyGhost)
    (hci : x.st.findReceiverChainIndex x.their = none)
    (hc_lt : x.counter < x.ck.index) :
    x.model F = (.error (.duplicatedMessage x.ck.index x.counter), x.st) := by
  unfold ConsumeMessageKeyGhost.model
  simp only [consumeMessageKey_past F x.st x.their x.ck x.counter x.msgType hc_lt, hci]

theorem stackAt_7712_split (sp : BitVec 64) :
    stackAt sp 7712 = stackAt sp allocHookStack ∗ stackAt (sp - 4096#64) 3616 := by
  unfold stackAt allocHookStack
  rw [show sp - 4096#64 - 3616#64 = sp - 7712#64 by bv_omega,
      show sp - 4096#64 = (sp - 7712#64) + 3616#64 by bv_omega,
      sepConj_comm,
      ← memRegion_split (sp - 7712#64) 3616 4096 (by decide)]

theorem cmk_remove_0x5e4_outcome {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {A : RustAlloc}
    (hA : AllocHooks A alloc)
    (himg : Obj.Loads libsignalSessionImage img)
    (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 s : State)
    {ci : Nat} (hci : x.st.findReceiverChainIndex x.their = some ci)
    (hi : ci < x.st.receiverChains.length)
    (hgi : ci < x.G.chains.length)
    (hprops : RatchetChainProps x.G x.st ci hgi hi)
    {p : Nat} (hp : p < (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length)
    (hfind : x.st.receiverChains[ci].messageKeys.findIdx? (fun k => k.counter == x.counter) = some p)
    (hc_lt : x.counter < x.ck.index)
    (hpc : s.pc = (SP img.base F alloc).fnAddr cmkSym + 1508#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx2 : s.readReg64 .x2 =
      BitVec.ofNat 64 (((x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length - 1 - p) * 104))
    (hx8 : s.readReg64 .x8 = x.G.chains[ci].mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (hx19 : s.readReg64 .x19 = x.G.chainsPtr + BitVec.ofNat 64 (ci * 104))
    (hx22 : s.readReg64 .x22 = x.ret)
    (hx24 : s.readReg64 .x24 =
      BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hm : s.mem ⊨
      (((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ x.G.chains[ci].mkPtr) ∗
       ((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄
         BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length) ∗
       vecBuf A 104 8 (messageKeyAt A) x.G.chains[ci].mkCap x.G.chains[ci].mkPtr
         (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys) ∗
       ratchetChainRest A x.self x.G x.st ci hgi hi ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
       memRegion x.ret 88 ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       memRegion (s0.sp - 480#64) 384 ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    reaches_outcome (sessionProg img F alloc) (consumeMessageKeySpec F A img) x R s0 s := by
  set chAddr := x.G.chainsPtr + BitVec.ofNat 64 (ci * 104)
  set g := x.G.chains[ci]
  set c := x.st.receiverChains[ci]
  set gks := g.keys.zip c.messageKeys
  have hm_pre : s.mem ⊨
      (A.pool ∗
       stackAt (s0.sp - 480#64) allocHookStack ∗
       memRegion (s0.sp - 480#64) 384 ∗
       memRegion x.ret 88 ∗
       ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
       vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks) ∗
      (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
       ratchetChainRest A x.self x.G x.st ci hgi hi ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64 - 4096#64) 3616 ∗
       cmkSavedRegs s0.sp s0 ∗ R) := by
    rw [stackAt_7712_split (s0.sp - 480#64)] at hm
    have hm1 := Satisfies.mono
      (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (chainKeyBytes_entails_memRegion x.ckA x.ck)))))))) hm
    exact Satisfies.of_eq hm1
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  have hL_sp : (SP img.base F alloc).CodeLoaded s.mem := by
    rwa [← sessionProg_eq_SP F alloc himg]
  obtain ⟨s1, hsteps1, hpc1, hrun1, P1, hm1, hsp1, hsp1_align, hx29_1, htr1, hP1⟩ :=
    sepWP_to_reaches_pc
      (cmk_remove_0x5e4_wp hA g.mkCap g.mkPtr chAddr x.ret gks p hp
        s0 s hpc hrun hsp hsp_align hx2 hx8 hx19 hx22 hx24 hx29)
      hm_pre hL_sp
  have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
  have hkl : g.keys.length = c.messageKeys.length := hprops.keys_len
  have hzip_len : gks.length = c.messageKeys.length := by
    simp [gks, hkl]
  have hp_c : p < c.messageKeys.length := by omega
  have hgks_snd : gks[p].2 = c.messageKeys[p] := by
    simp [gks, List.getElem_zip]
  have hmodel := cmk_model_past_hit F x hci hi hp_c hfind hc_lt
  set g' : ChainGhost := { g with keys := g.keys.eraseIdx p }
  set c' : ReceiverChain := { c with messageKeys := c.messageKeys.eraseIdx p }
  set G' : RatchetGhost := x.G.setChain ci g'
  have hm1_ep : s1.mem ⊨
      (stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗ cmkSavedRegs s0.sp s0) ∗
      (ratchetAt A x.self G' (x.model F).2 ∗
       consumeMessageKeyResultAt A x.ret (x.model F).1 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗
       A.pool ∗ R) := by
    rw [hmodel, ← hgks_snd, stackAt_7712_split (s0.sp - 480#64)]
    have hreassemble := ratchetAt_reassemble_eraseIdx A x.self x.G x.st hi hgi hprops hp
    have hm1'' : s1.mem ⊨
        (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
          ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 (gks.length - 1)) ∗
          vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr (gks.eraseIdx p) ∗
          ratchetChainRest A x.self x.G x.st ci hgi hi) ∗
        (stackAt (s0.sp - 480#64) allocHookStack ∗
          stackAt (s0.sp - 480#64 - 4096#64) 3616 ∗
          memRegion (s0.sp - 480#64) 384 ∗
          cmkSavedRegs s0.sp s0 ∗
          consumeMessageKeyResultAt A x.ret (.ok gks[p].2) ∗
          (x.theirA ↦ₛ x.their.bytes.toList) ∗
          memRegion x.ckA 36 ∗
          (logFilterAddr img ↦₆₄ 0#64) ∗
          A.pool ∗ R) :=
      Satisfies.of_eq hm1'
    exact Satisfies.of_eq (Satisfies.mono (sepConj_mono_left hreassemble) hm1'')
  have hnpan : (x.model F).1 ≠ .error .panic := by
    rw [hmodel]; intro h; cases h
  have htouch : x.touched F = some ci := by
    unfold ConsumeMessageKeyGhost.touched; rw [hmodel]; exact hci
  have hG' : x.G.AgreeExcept G' (x.touched F) := by
    rw [htouch]
    exact RatchetGhost.AgreeExcept.setChain x.G hgi g' rfl rfl
  have hsteps1_prog : Steps (sessionProg img F alloc) s s1 := by
    rwa [sessionProg_eq_SP F alloc himg]
  exact reaches_outcome_steps hsteps1_prog
    (cmk_epilogue_77c_outcome himg x G' R s0 s1 hpc1 hrun1 hsp1 hsp1_align
      (by reg_chain) hnpan hG' hm1_ep)

/-! ## Counter Position Search Loop (`+0x94 .. +0xb0`) -/

@[local simp] theorem sub32_not_add_one (a b : BitVec 32) :
    a + (~~~b + 1#32) = a - b := by
  have := @BitVec.toNat_not 32 b
  bv_omega

@[local simp] theorem sub32_add_not_add_one (a b : BitVec 32) :
    a + ~~~b + 1#32 = a - b := by
  have := @BitVec.toNat_not 32 b
  bv_omega

theorem messageKeyAt_expose_counter (A : RustAlloc)
    (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) :
    messageKeyAt A gk a =
      ((a + 96#64) ↦₃₂ gk.2.counter) ∗
      (⌜gk.2.seed ≠ []⌝ ∗ vecU8At A a gk.1.cipher.cap gk.1.cipher.ptr [] ∗
        vecU8At A (a + 24#64) gk.1.mac.cap gk.1.mac.ptr [] ∗
        vecU8At A (a + 48#64) gk.1.iv.cap gk.1.iv.ptr [] ∗
        vecU8At A (a + 72#64) gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
        memRegion (a + 100#64) 4) := by
  unfold messageKeyAt
  ac_rfl

theorem cmk_loop_hit_wp {A : RustAlloc} {b : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)}
    (mkCap mkPtr v2 v19 v22 v24 v27 v28 v29 : BitVec 64)
    (counter : BitVec 32)
    (gks : List (MessageKeyGhost × MessageKeyGenerator))
    (p : Nat) (hp : p < gks.length)
    (heq : gks[p].2.counter = counter)
    (s0 s : State)
    (hpc : s.pc = (SP b F alloc).fnAddr cmkSym + 148#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = v2)
    (hx8 : s.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (hx19 : s.readReg64 .x19 = v19)
    (hx20 : s.readReg64 .x20 = counter.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = v22)
    (hx24 : s.readReg64 .x24 = v24)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = v28)
    (hx29 : s.readReg64 .x29 = v29) :
    SepWP (SP b F alloc) ((SP b F alloc).fnAddr cmkSym + 1508#64) s
      (vecBuf A 104 8 (messageKeyAt A) mkCap mkPtr gks)
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x2 = v2 ∧
        s1.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64 ∧
        s1.readReg64 .x19 = v19 ∧
        s1.readReg64 .x20 = counter.zeroExtend 64 ∧
        s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x24 = v24 ∧
        s1.readReg64 .x27 = v27 ∧
        s1.readReg64 .x28 = v28 ∧
        s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ vecBuf A 104 8 (messageKeyAt A) mkCap mkPtr gks)) := by
  cmk_fetches_range b (Rust.withPanics (sessionExterns F alloc)) 0x94 0x9c
  generalize_entry (SP b F alloc).fnAddr cmkSym = entry
  examples_hide_fetches
  refine SepWP.weaken_pre (vecBuf_split_at A 104 8 (messageKeyAt A) mkCap mkPtr gks hp) ?_
  rw [messageKeyAt_expose_counter A gks[p] (mkPtr + BitVec.ofNat 64 (p * 104))]
  simp only [sepConj_assoc]
  wp_step
  wp_step
  wp_step
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩, ?_⟩
  refine Entails.trans ?_ (vecBuf_reassemble_self A 104 8 (messageKeyAt A) mkCap mkPtr gks hp)
  unfold messageKeyAt
  exact entails_of_eq (by ac_rfl) (Entails.refl _)

theorem cmk_loop_miss_head_wp {A : RustAlloc} {b : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)}
    (mkCap mkPtr v2 v19 v22 v24 v27 v28 v29 : BitVec 64)
    (counter : BitVec 32)
    (gks : List (MessageKeyGhost × MessageKeyGenerator))
    (p : Nat) (hp : p < gks.length)
    (hne : gks[p].2.counter ≠ counter)
    (s0 s : State)
    (hpc : s.pc = (SP b F alloc).fnAddr cmkSym + 148#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = v2)
    (hx8 : s.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (hx19 : s.readReg64 .x19 = v19)
    (hx20 : s.readReg64 .x20 = counter.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = v22)
    (hx24 : s.readReg64 .x24 = v24)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = v28)
    (hx29 : s.readReg64 .x29 = v29) :
    SepWP (SP b F alloc) ((SP b F alloc).fnAddr cmkSym + 160#64) s
      (vecBuf A 104 8 (messageKeyAt A) mkCap mkPtr gks)
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x2 = v2 ∧
        s1.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64 ∧
        s1.readReg64 .x19 = v19 ∧
        s1.readReg64 .x20 = counter.zeroExtend 64 ∧
        s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x24 = v24 ∧
        s1.readReg64 .x27 = v27 ∧
        s1.readReg64 .x28 = v28 ∧
        s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ vecBuf A 104 8 (messageKeyAt A) mkCap mkPtr gks)) := by
  cmk_fetches_range b (Rust.withPanics (sessionExterns F alloc)) 0x94 0x9c
  generalize_entry (SP b F alloc).fnAddr cmkSym = entry
  examples_hide_fetches
  refine SepWP.weaken_pre (vecBuf_split_at A 104 8 (messageKeyAt A) mkCap mkPtr gks hp) ?_
  rw [messageKeyAt_expose_counter A gks[p] (mkPtr + BitVec.ofNat 64 (p * 104))]
  simp only [sepConj_assoc]
  wp_step
  wp_step
  wp_step
  apply SepWP.ite_false (by rfl) (by simp [arm64_norm]; exact hne)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩, ?_⟩
  refine Entails.trans ?_ (vecBuf_reassemble_self A 104 8 (messageKeyAt A) mkCap mkPtr gks hp)
  unfold messageKeyAt
  exact entails_of_eq (by ac_rfl) (Entails.refl _)

@[local simp] theorem bv_sub_104_add_104 (x : BitVec 64) : x - 104#64 + 104#64 = x := by
  bv_omega

@[local simp] theorem bv_add_neg104_add_104 (x : BitVec 64) :
    x + bv% (2 ^ 64 - 104) + 104#64 = x := by
  bv_omega

theorem remBytes_sub_104_eq {p len : Nat} (hp1 : p + 1 < len) :
    BitVec.ofNat 64 ((len - 1 - p) * 104) - 104#64 =
      BitVec.ofNat 64 ((len - 1 - (p + 1)) * 104) := by
  have h : (len - 1 - p) * 104 = (len - 1 - (p + 1)) * 104 + 104 := by
    have : len - 1 - p = (len - 1 - (p + 1)) + 1 := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  rw [h, BitVec.ofNat_add]
  change BitVec.ofNat 64 ((len - 1 - (p + 1)) * 104) + 104#64 - 104#64 =
    BitVec.ofNat 64 ((len - 1 - (p + 1)) * 104)
  bv_omega

theorem remBytes_ne_zero {p len : Nat} (hp1 : p + 1 < len)
    (hmax : len ≤ maxMessageKeys) :
    BitVec.ofNat 64 ((len - 1 - p) * 104) ≠ 0#64 := by
  have hpos : 0 < (len - 1 - p) * 104 := by omega
  have hlt : (len - 1 - p) * 104 < 2 ^ 64 := by
    unfold maxMessageKeys at hmax; omega
  intro h0
  have hnat := congrArg BitVec.toNat h0
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at hnat
  change (len - 1 - p) * 104 = 0 at hnat
  omega

theorem remBytes_last_eq_zero {p len : Nat} (hp1 : p + 1 = len) :
    BitVec.ofNat 64 ((len - 1 - p) * 104) = 0#64 := by
  have : (len - 1 - p) * 104 = 0 := by omega
  rw [this]

theorem ofNat_p_add_one (p : Nat) :
    BitVec.ofNat 64 p + 1#64 = BitVec.ofNat 64 (p + 1) := by
  rw [BitVec.ofNat_add]

theorem x8_step_84 (mkPtr : BitVec 64) (p : Nat) :
    mkPtr + BitVec.ofNat 64 (p * 104) + 160#64 =
      mkPtr + BitVec.ofNat 64 ((p + 1) * 104) + 56#64 := by
  have h : mkPtr + BitVec.ofNat 64 (p * 104) + 160#64 =
      (mkPtr + BitVec.ofNat 64 (p * 104) + 104#64) + 56#64 := by bv_omega
  rw [h, elemAddr_add_104]

theorem cmk_loop_miss_cont_wp {b : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)}
    (mkPtr v19 v20 v22 v24 v28 v29 : BitVec 64)
    (p mkLen : Nat) (hp1 : p + 1 < mkLen) (hmax : mkLen ≤ maxMessageKeys)
    (s0 s : State)
    (hpc : s.pc = (SP b F alloc).fnAddr cmkSym + 160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 ((mkLen - 1 - p) * 104))
    (hx8 : s.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (hx19 : s.readReg64 .x19 = v19)
    (hx20 : s.readReg64 .x20 = v20)
    (hx22 : s.readReg64 .x22 = v22)
    (hx24 : s.readReg64 .x24 = v24)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 p)
    (hx28 : s.readReg64 .x28 = v28)
    (hx29 : s.readReg64 .x29 = v29) :
    SepWP (SP b F alloc) ((SP b F alloc).fnAddr cmkSym + 148#64) s emp
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 ((mkLen - 1 - (p + 1)) * 104) ∧
        s1.readReg64 .x8 = mkPtr + BitVec.ofNat 64 ((p + 1) * 104) + 56#64 ∧
        s1.readReg64 .x19 = v19 ∧
        s1.readReg64 .x20 = v20 ∧
        s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x24 = v24 ∧
        s1.readReg64 .x27 = BitVec.ofNat 64 (p + 1) ∧
        s1.readReg64 .x28 = v28 ∧
        s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ emp)) := by
  cmk_fetches_range b (Rust.withPanics (sessionExterns F alloc)) 0xa0 0xb0
  generalize_entry (SP b F alloc).fnAddr cmkSym = entry
  examples_hide_fetches
  wp_step
  wp_step
  wp_step
  wp_step
  wp_step
  apply SepWP.ite_true (by rfl) (by simp [arm64_norm]; exact remBytes_ne_zero hp1 hmax)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
    ?_, ?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], ?_,
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    Entails.refl _⟩
  · simp only [arm64_norm]
    exact remBytes_sub_104_eq hp1
  · simp only [arm64_norm]
    exact x8_step_84 mkPtr p
  · simp only [arm64_norm]
    exact ofNat_p_add_one p

theorem cmk_loop_miss_done_wp {b : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)}
    (mkPtr v19 v20 v22 v24 v28 v29 : BitVec 64)
    (p mkLen : Nat) (hp1 : p + 1 = mkLen)
    (s0 s : State)
    (hpc : s.pc = (SP b F alloc).fnAddr cmkSym + 160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 ((mkLen - 1 - p) * 104))
    (_hx8 : s.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (_hx19 : s.readReg64 .x19 = v19)
    (hx20 : s.readReg64 .x20 = v20)
    (hx22 : s.readReg64 .x22 = v22)
    (_hx24 : s.readReg64 .x24 = v24)
    (_hx27 : s.readReg64 .x27 = BitVec.ofNat 64 p)
    (hx28 : s.readReg64 .x28 = v28)
    (_hx29 : s.readReg64 .x29 = v29) :
    SepWP (SP b F alloc) ((SP b F alloc).fnAddr cmkSym + 180#64) s emp
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x20 = v20 ∧
        s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x28 = v28 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ emp)) := by
  cmk_fetches_range b (Rust.withPanics (sessionExterns F alloc)) 0xa0 0xb0
  generalize_entry (SP b F alloc).fnAddr cmkSym = entry
  examples_hide_fetches
  wp_step
  wp_step
  wp_step
  wp_step
  wp_step
  apply SepWP.ite_false (by rfl) (by simp [arm64_norm]; exact remBytes_last_eq_zero hp1)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩, Entails.refl _⟩

theorem findIdx_go_step {ks : List MessageKeyGenerator} {c : BitVec 32} {p : Nat}
    (hp : p < ks.length) :
    List.findIdx?.go (fun k => k.counter == c) (ks.drop p) p =
      if ks[p].counter == c then some p
      else List.findIdx?.go (fun k => k.counter == c) (ks.drop (p + 1)) (p + 1) := by
  rw [List.drop_eq_getElem_cons hp, List.findIdx?.go]

/-- Loop induction over `rem = gks.length - p` for the counter search at `+0x94`. -/
theorem cmk_pos_loop_0x94_outcome {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {A : RustAlloc}
    (hA : AllocHooks A alloc)
    (himg : Obj.Loads libsignalSessionImage img)
    (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 : State)
    {ci : Nat} (hci : x.st.findReceiverChainIndex x.their = some ci)
    (hi : ci < x.st.receiverChains.length)
    (hgi : ci < x.G.chains.length)
    (hprops : RatchetChainProps x.G x.st ci hgi hi)
    (hc_lt : x.counter < x.ck.index) :
    ∀ (rem p : Nat) (s : State),
      rem = (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length - p →
      p < (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length →
      x.st.receiverChains[ci].messageKeys.findIdx? (fun k => k.counter == x.counter) =
        List.findIdx?.go (fun k => k.counter == x.counter)
          (x.st.receiverChains[ci].messageKeys.drop p) p →
      s.pc = (SP img.base F alloc).fnAddr cmkSym + 148#64 →
      s.status = .Running →
      s.sp = s0.sp - 480#64 →
      s.spAligned = true →
      (s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) →
      s.readReg64 .x2 =
        BitVec.ofNat 64 (((x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length - 1 - p) * 104) →
      s.readReg64 .x8 = x.G.chains[ci].mkPtr + BitVec.ofNat 64 (p * 104) + 56#64 →
      s.readReg64 .x19 = x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) →
      s.readReg64 .x20 = x.counter.zeroExtend 64 →
      s.readReg64 .x22 = x.ret →
      s.readReg64 .x24 =
        BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length →
      s.readReg64 .x27 = BitVec.ofNat 64 p →
      s.readReg64 .x28 = x.ck.index.zeroExtend 64 →
      s.readReg64 .x29 = s0.sp - 96#64 →
      (s.mem ⊨
        (((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ x.G.chains[ci].mkPtr) ∗
         ((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄
           BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length) ∗
         vecBuf A 104 8 (messageKeyAt A) x.G.chains[ci].mkCap x.G.chains[ci].mkPtr
           (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys) ∗
         ratchetChainRest A x.self x.G x.st ci hgi hi ∗
         (x.theirA ↦ₛ x.their.bytes.toList) ∗
         (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
         memRegion x.ret 88 ∗
         (logFilterAddr img ↦₆₄ 0#64) ∗
         stackAt (s0.sp - 480#64) 7712 ∗
         memRegion (s0.sp - 480#64) 384 ∗
         cmkSavedRegs s0.sp s0 ∗
         A.pool) ∗ R) →
      reaches_outcome (sessionProg img F alloc) (consumeMessageKeySpec F A img) x R s0 s := by
  intro rem
  induction rem with
  | zero =>
    intro p s hrem hp
    omega
  | succ k ih =>
    intro p s hrem hp hfind hpc hrun hsp hsp_align htrace
      hx2 hx8 hx19 hx20 hx22 hx24 hx27 hx28 hx29 hm
    set chAddr := x.G.chainsPtr + BitVec.ofNat 64 (ci * 104)
    set g := x.G.chains[ci]
    set c := x.st.receiverChains[ci]
    set gks := g.keys.zip c.messageKeys
    have hkl : g.keys.length = c.messageKeys.length := hprops.keys_len
    have hzip_len : gks.length = c.messageKeys.length := by
      simp [gks, hkl]
    have hp_c : p < c.messageKeys.length := by omega
    have hgks_snd : gks[p].2 = c.messageKeys[p] := by
      simp [gks, List.getElem_zip]
    have hm_vec : s.mem ⊨
        vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks ∗
        (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
         ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
         ratchetChainRest A x.self x.G x.st ci hgi hi ∗
         (x.theirA ↦ₛ x.their.bytes.toList) ∗
         (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
         memRegion x.ret 88 ∗
         (logFilterAddr img ↦₆₄ 0#64) ∗
         stackAt (s0.sp - 480#64) 7712 ∗
         memRegion (s0.sp - 480#64) 384 ∗
         cmkSavedRegs s0.sp s0 ∗
         A.pool ∗ R) :=
      Satisfies.of_eq hm
    by_cases heq : gks[p].2.counter = x.counter
    ·
      have hfind_some : c.messageKeys.findIdx? (fun k => k.counter == x.counter) = some p := by
        rw [hfind, findIdx_go_step hp_c]
        have hbeq : (c.messageKeys[p].counter == x.counter) = true := by
          rw [← hgks_snd]; exact beq_iff_eq.mpr heq
        simp [hbeq]
      refine reaches_outcome.of_codeLoaded fun hL => ?_
      have hL_sp : (SP img.base F alloc).CodeLoaded s.mem := by
        rwa [← sessionProg_eq_SP F alloc himg]
      obtain ⟨s1, hsteps1, hpc1, hrun1, P1, hm1, hsp1, hsp1_align,
        hx2_1, hx8_1, hx19_1, hx20_1, hx22_1, hx24_1, hx27_1, hx28_1, hx29_1, htr1, hP1⟩ :=
        sepWP_to_reaches_pc
          (cmk_loop_hit_wp g.mkCap g.mkPtr _ chAddr x.ret (BitVec.ofNat 64 gks.length)
            (BitVec.ofNat 64 p) (x.ck.index.zeroExtend 64) (s0.sp - 96#64)
            x.counter gks p hp heq s0 s hpc hrun hsp hsp_align
            hx2 hx8 hx19 hx20 hx22 hx24 hx27 hx28 hx29)
          hm_vec hL_sp
      have hm1' : s1.mem ⊨
          (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
           ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
           vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks ∗
           ratchetChainRest A x.self x.G x.st ci hgi hi ∗
           (x.theirA ↦ₛ x.their.bytes.toList) ∗
           (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
           memRegion x.ret 88 ∗
           (logFilterAddr img ↦₆₄ 0#64) ∗
           stackAt (s0.sp - 480#64) 7712 ∗
           memRegion (s0.sp - 480#64) 384 ∗
           cmkSavedRegs s0.sp s0 ∗
           A.pool) ∗ R :=
        Satisfies.of_eq (Satisfies.mono (sepConj_mono_left hP1) hm1)
      have hsteps1_prog : Steps (sessionProg img F alloc) s s1 := by
        rwa [sessionProg_eq_SP F alloc himg]
      exact reaches_outcome_steps hsteps1_prog
        (cmk_remove_0x5e4_outcome hA himg x R s0 s1 hci hi hgi hprops hp hfind_some hc_lt
          hpc1 hrun1 hsp1 hsp1_align (by reg_chain)
          hx2_1 hx8_1 hx19_1 hx22_1 hx24_1 hx29_1 hm1')
    ·
      have hfind_next :
          c.messageKeys.findIdx? (fun k => k.counter == x.counter) =
            List.findIdx?.go (fun k => k.counter == x.counter)
              (c.messageKeys.drop (p + 1)) (p + 1) := by
        rw [hfind, findIdx_go_step hp_c]
        have hbeq : (c.messageKeys[p].counter == x.counter) = false := by
          rw [← hgks_snd]; exact beq_eq_false_iff_ne.mpr heq
        simp [hbeq]
      refine reaches_outcome.of_codeLoaded fun hL => ?_
      have hL_sp : (SP img.base F alloc).CodeLoaded s.mem := by
        rwa [← sessionProg_eq_SP F alloc himg]
      obtain ⟨s1, hsteps1, hpc1, hrun1, P1, hm1, hsp1, hsp1_align,
        hx2_1, hx8_1, hx19_1, hx20_1, hx22_1, hx24_1, hx27_1, hx28_1, hx29_1, htr1, hP1⟩ :=
        sepWP_to_reaches_pc
          (cmk_loop_miss_head_wp g.mkCap g.mkPtr _ chAddr x.ret (BitVec.ofNat 64 gks.length)
            (BitVec.ofNat 64 p) (x.ck.index.zeroExtend 64) (s0.sp - 96#64)
            x.counter gks p hp heq s0 s hpc hrun hsp hsp_align
            hx2 hx8 hx19 hx20 hx22 hx24 hx27 hx28 hx29)
          hm_vec hL_sp
      have hm1_emp : s1.mem ⊨
          emp ∗
          (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
           ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
           vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks ∗
           ratchetChainRest A x.self x.G x.st ci hgi hi ∗
           (x.theirA ↦ₛ x.their.bytes.toList) ∗
           (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
           memRegion x.ret 88 ∗
           (logFilterAddr img ↦₆₄ 0#64) ∗
           stackAt (s0.sp - 480#64) 7712 ∗
           memRegion (s0.sp - 480#64) 384 ∗
           cmkSavedRegs s0.sp s0 ∗
           A.pool ∗ R) :=
        Satisfies.of_eq (Satisfies.mono (sepConj_mono_left hP1) hm1)
      have hsteps1_prog : Steps (sessionProg img F alloc) s s1 := by
        rwa [sessionProg_eq_SP F alloc himg]
      have hL1 : (SP img.base F alloc).CodeLoaded s1.mem :=
        hsteps1.codeLoaded hL_sp
      by_cases hp1 : p + 1 < gks.length
      ·
        have hmax_gks : gks.length ≤ maxMessageKeys := by
          rw [hzip_len]; exact hprops.mk_max
        obtain ⟨s2, hsteps2, hpc2, hrun2, P2, hm2, hsp2, hsp2_align,
          hx2_2, hx8_2, hx19_2, hx20_2, hx22_2, hx24_2, hx27_2, hx28_2, hx29_2, htr2, hP2⟩ :=
          sepWP_to_reaches_pc
            (cmk_loop_miss_cont_wp g.mkPtr chAddr (x.counter.zeroExtend 64) x.ret
              (BitVec.ofNat 64 gks.length) (x.ck.index.zeroExtend 64) (s0.sp - 96#64)
              p gks.length hp1 hmax_gks s0 s1 hpc1 hrun1 hsp1 hsp1_align
              hx2_1 hx8_1 hx19_1 hx20_1 hx22_1 hx24_1 hx27_1 hx28_1 hx29_1)
            hm1_emp hL1
        have hm2' : s2.mem ⊨
            (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
             ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
             vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks ∗
             ratchetChainRest A x.self x.G x.st ci hgi hi ∗
             (x.theirA ↦ₛ x.their.bytes.toList) ∗
             (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
             memRegion x.ret 88 ∗
             (logFilterAddr img ↦₆₄ 0#64) ∗
             stackAt (s0.sp - 480#64) 7712 ∗
             memRegion (s0.sp - 480#64) 384 ∗
             cmkSavedRegs s0.sp s0 ∗
             A.pool) ∗ R :=
          Satisfies.of_eq (Satisfies.mono (sepConj_mono_left hP2) hm2)
        have hsteps2_prog : Steps (sessionProg img F alloc) s1 s2 := by
          rwa [sessionProg_eq_SP F alloc himg]
        exact reaches_outcome_steps (hsteps1_prog.trans hsteps2_prog)
          (ih (p + 1) s2 (by omega) hp1 hfind_next hpc2 hrun2 hsp2 hsp2_align
            (by reg_chain)
            hx2_2 hx8_2 hx19_2 hx20_2 hx22_2 hx24_2 hx27_2 hx28_2 hx29_2 hm2')
      ·
        have hp1_eq : p + 1 = gks.length := by omega
        obtain ⟨s2, hsteps2, hpc2, hrun2, P2, hm2, hsp2, hsp2_align,
          hx20_2, hx22_2, hx28_2, htr2, hP2⟩ :=
          sepWP_to_reaches_pc
            (cmk_loop_miss_done_wp g.mkPtr chAddr (x.counter.zeroExtend 64) x.ret
              (BitVec.ofNat 64 gks.length) (x.ck.index.zeroExtend 64) (s0.sp - 96#64)
              p gks.length hp1_eq s0 s1 hpc1 hrun1 hsp1 hsp1_align
              hx2_1 hx8_1 hx19_1 hx20_1 hx22_1 hx24_1 hx27_1 hx28_1 hx29_1)
            hm1_emp hL1
        have hm2_pre : s2.mem ⊨ cmkPreLoopHeap A img x s0 ∗ R := by
          unfold cmkPreLoopHeap
          have hm2' := Satisfies.mono (sepConj_mono_left hP2) hm2
          have hreassemble := ratchetAt_reassemble_self A x.self x.G x.st hi hgi hprops
          have hm2'' : s2.mem ⊨
              (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
                ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
                vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks ∗
                ratchetChainRest A x.self x.G x.st ci hgi hi) ∗
              ((x.theirA ↦ₛ x.their.bytes.toList) ∗
                (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
                memRegion x.ret 88 ∗
                (logFilterAddr img ↦₆₄ 0#64) ∗
                stackAt (s0.sp - 480#64) 7712 ∗
                memRegion (s0.sp - 480#64) 384 ∗
                cmkSavedRegs s0.sp s0 ∗
                A.pool ∗ R) :=
            Satisfies.of_eq hm2'
          exact Satisfies.of_eq (Satisfies.mono (sepConj_mono_left hreassemble) hm2'')
        have hfind_none : c.messageKeys.findIdx? (fun k => k.counter == x.counter) = none := by
          rw [hfind_next, List.drop_eq_nil_of_le (by omega), List.findIdx?.go]
        have hmodel := cmk_model_past_miss_chain F x hci hi hfind_none hc_lt
        have hsteps2_prog : Steps (sessionProg img F alloc) s1 s2 := by
          rwa [sessionProg_eq_SP F alloc himg]
        exact reaches_outcome_steps (hsteps1_prog.trans hsteps2_prog)
          (cmk_dup_0xb4_outcome himg x R s0 s2 hpc2 hrun2 hsp2 hsp2_align
            (by reg_chain) hx20_2 hx22_2 hx28_2 hmodel hm2_pre)

/-! ## Relocatable `[LibsignalPlacement]` Search Loop and `remove(p)` Outcome -/

theorem cmk_remove_0x5e4_placed_outcome [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {H : String → Option (State → State)} {A : RustAlloc}
    (hA : CmkAllocHooks A H)
    (hmemmove_eq : H cmkMemmoveSym = some hookMemmove)
    (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 s : State)
    {ci : Nat} (hci : x.st.findReceiverChainIndex x.their = some ci)
    (hi : ci < x.st.receiverChains.length)
    (hgi : ci < x.G.chains.length)
    (hprops : RatchetChainProps x.G x.st ci hgi hi)
    {p : Nat} (hp : p < (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length)
    (hfind : x.st.receiverChains[ci].messageKeys.findIdx? (fun k => k.counter == x.counter) = some p)
    (hc_lt : x.counter < x.ck.index)
    (hpc : s.pc = (blkPl_24).base + 1508#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx2 : s.readReg64 .x2 =
      BitVec.ofNat 64 (((x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length - 1 - p) * 104))
    (hx8 : s.readReg64 .x8 = x.G.chains[ci].mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (hx19 : s.readReg64 .x19 = x.G.chainsPtr + BitVec.ofNat 64 (ci * 104))
    (hx22 : s.readReg64 .x22 = x.ret)
    (hx24 : s.readReg64 .x24 =
      BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hm : s.mem ⊨
      (((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ x.G.chains[ci].mkPtr) ∗
       ((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄
         BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length) ∗
       vecBuf A 104 8 (messageKeyAt A) x.G.chains[ci].mkCap x.G.chains[ci].mkPtr
         (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys) ∗
       ratchetChainRest A x.self x.G x.st ci hgi hi ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
       memRegion x.ret 88 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       memRegion (s0.sp - 480#64) 384 ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    reaches_outcome ((blkPC_24).rebase (blkPl_24).base H) (cmkPlacedSpec F A) x R s0 s := by
  set chAddr := x.G.chainsPtr + BitVec.ofNat 64 (ci * 104)
  set g := x.G.chains[ci]
  set c := x.st.receiverChains[ci]
  set gks := g.keys.zip c.messageKeys
  have hm_pre : s.mem ⊨
      (A.pool ∗
       stackAt (s0.sp - 480#64) allocHookStack ∗
       memRegion (s0.sp - 480#64) 384 ∗
       memRegion x.ret 88 ∗
       ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
       vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks) ∗
      (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
       ratchetChainRest A x.self x.G x.st ci hgi hi ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64 - 4096#64) 3616 ∗
       cmkSavedRegs s0.sp s0 ∗ R) := by
    rw [stackAt_7712_split (s0.sp - 480#64)] at hm
    have hm1 := Satisfies.mono
      (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (chainKeyBytes_entails_memRegion x.ckA x.ck)))))))) hm
    exact Satisfies.of_eq hm1
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨s1, hsteps1, hpc1, hrun1, P1, hm1, hsp1, hsp1_align, hx29_1, htr1, hP1⟩ :=
    sepWP_to_reaches_pc
      (cmk_remove_0x5e4_placed_wp hA hmemmove_eq g.mkCap g.mkPtr chAddr x.ret gks p hp
        s0 s hpc hrun hsp hsp_align hx2 hx8 hx19 hx22 hx24 hx29)
      hm_pre hL
  have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
  have hkl : g.keys.length = c.messageKeys.length := hprops.keys_len
  have hzip_len : gks.length = c.messageKeys.length := by
    simp [gks, hkl]
  have hp_c : p < c.messageKeys.length := by omega
  have hgks_snd : gks[p].2 = c.messageKeys[p] := by
    simp [gks, List.getElem_zip]
  have hmodel := cmk_model_past_hit F x hci hi hp_c hfind hc_lt
  set g' : ChainGhost := { g with keys := g.keys.eraseIdx p }
  set c' : ReceiverChain := { c with messageKeys := c.messageKeys.eraseIdx p }
  set G' : RatchetGhost := x.G.setChain ci g'
  have hm1_ep : s1.mem ⊨
      (stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗ cmkSavedRegs s0.sp s0) ∗
      (ratchetAt A x.self G' (x.model F).2 ∗
       consumeMessageKeyResultAt A x.ret (x.model F).1 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       A.pool ∗ R) := by
    rw [hmodel, ← hgks_snd, stackAt_7712_split (s0.sp - 480#64)]
    have hreassemble := ratchetAt_reassemble_eraseIdx A x.self x.G x.st hi hgi hprops hp
    have hm1'' : s1.mem ⊨
        (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
          ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 (gks.length - 1)) ∗
          vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr (gks.eraseIdx p) ∗
          ratchetChainRest A x.self x.G x.st ci hgi hi) ∗
        (stackAt (s0.sp - 480#64) allocHookStack ∗
          stackAt (s0.sp - 480#64 - 4096#64) 3616 ∗
          memRegion (s0.sp - 480#64) 384 ∗
          cmkSavedRegs s0.sp s0 ∗
          consumeMessageKeyResultAt A x.ret (.ok gks[p].2) ∗
          (x.theirA ↦ₛ x.their.bytes.toList) ∗
          memRegion x.ckA 36 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          A.pool ∗ R) :=
      Satisfies.of_eq hm1'
    exact Satisfies.of_eq (Satisfies.mono (sepConj_mono_left hreassemble) hm1'')
  have hnpan : (x.model F).1 ≠ .error .panic := by
    rw [hmodel]; intro h; cases h
  have htouch : x.touched F = some ci := by
    unfold ConsumeMessageKeyGhost.touched; rw [hmodel]; exact hci
  have hG' : x.G.AgreeExcept G' (x.touched F) := by
    rw [htouch]
    exact RatchetGhost.AgreeExcept.setChain x.G hgi g' rfl rfl
  exact reaches_outcome_steps hsteps1
    (cmk_epilogue_77c_placed_outcome x G' R s0 s1 hpc1 hrun1 hsp1 hsp1_align
      (by reg_chain) hnpan hG' hm1_ep)

theorem cmk_loop_hit_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (mkCap mkPtr v2 v19 v22 v24 v27 v28 v29 : BitVec 64)
    (counter : BitVec 32)
    (gks : List (MessageKeyGhost × MessageKeyGenerator))
    (p : Nat) (hp : p < gks.length)
    (heq : gks[p].2.counter = counter)
    (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 148#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = v2)
    (hx8 : s.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (hx19 : s.readReg64 .x19 = v19)
    (hx20 : s.readReg64 .x20 = counter.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = v22)
    (hx24 : s.readReg64 .x24 = v24)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = v28)
    (hx29 : s.readReg64 .x29 = v29) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1508#64) s
      (vecBuf A 104 8 (messageKeyAt A) mkCap mkPtr gks)
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x2 = v2 ∧
        s1.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64 ∧
        s1.readReg64 .x19 = v19 ∧
        s1.readReg64 .x20 = counter.zeroExtend 64 ∧
        s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x24 = v24 ∧
        s1.readReg64 .x27 = v27 ∧
        s1.readReg64 .x28 = v28 ∧
        s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ vecBuf A 104 8 (messageKeyAt A) mkCap mkPtr gks)) := by
  refine SepWP.weaken_pre (vecBuf_split_at A 104 8 (messageKeyAt A) mkCap mkPtr gks hp) ?_
  rw [messageKeyAt_expose_counter A gks[p] (mkPtr + BitVec.ofNat 64 (p * 104))]
  simp only [sepConj_assoc]
  wp_step
  wp_step
  wp_step
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩, ?_⟩
  refine Entails.trans ?_ (vecBuf_reassemble_self A 104 8 (messageKeyAt A) mkCap mkPtr gks hp)
  unfold messageKeyAt
  exact entails_of_eq (by ac_rfl) (Entails.refl _)

theorem cmk_loop_miss_head_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (mkCap mkPtr v2 v19 v22 v24 v27 v28 v29 : BitVec 64)
    (counter : BitVec 32)
    (gks : List (MessageKeyGhost × MessageKeyGenerator))
    (p : Nat) (hp : p < gks.length)
    (hne : gks[p].2.counter ≠ counter)
    (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 148#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = v2)
    (hx8 : s.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (hx19 : s.readReg64 .x19 = v19)
    (hx20 : s.readReg64 .x20 = counter.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = v22)
    (hx24 : s.readReg64 .x24 = v24)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = v28)
    (hx29 : s.readReg64 .x29 = v29) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 160#64) s
      (vecBuf A 104 8 (messageKeyAt A) mkCap mkPtr gks)
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x2 = v2 ∧
        s1.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64 ∧
        s1.readReg64 .x19 = v19 ∧
        s1.readReg64 .x20 = counter.zeroExtend 64 ∧
        s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x24 = v24 ∧
        s1.readReg64 .x27 = v27 ∧
        s1.readReg64 .x28 = v28 ∧
        s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ vecBuf A 104 8 (messageKeyAt A) mkCap mkPtr gks)) := by
  refine SepWP.weaken_pre (vecBuf_split_at A 104 8 (messageKeyAt A) mkCap mkPtr gks hp) ?_
  rw [messageKeyAt_expose_counter A gks[p] (mkPtr + BitVec.ofNat 64 (p * 104))]
  simp only [sepConj_assoc]
  wp_step
  wp_step
  wp_step
  apply SepWP.ite_false (by rfl) (by simp [arm64_norm]; exact hne)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩, ?_⟩
  refine Entails.trans ?_ (vecBuf_reassemble_self A 104 8 (messageKeyAt A) mkCap mkPtr gks hp)
  unfold messageKeyAt
  exact entails_of_eq (by ac_rfl) (Entails.refl _)

theorem cmk_loop_miss_cont_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)}
    (mkPtr v19 v20 v22 v24 v28 v29 : BitVec 64)
    (p mkLen : Nat) (hp1 : p + 1 < mkLen) (hmax : mkLen ≤ maxMessageKeys)
    (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 ((mkLen - 1 - p) * 104))
    (hx8 : s.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (hx19 : s.readReg64 .x19 = v19)
    (hx20 : s.readReg64 .x20 = v20)
    (hx22 : s.readReg64 .x22 = v22)
    (hx24 : s.readReg64 .x24 = v24)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 p)
    (hx28 : s.readReg64 .x28 = v28)
    (hx29 : s.readReg64 .x29 = v29) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 148#64) s emp
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 ((mkLen - 1 - (p + 1)) * 104) ∧
        s1.readReg64 .x8 = mkPtr + BitVec.ofNat 64 ((p + 1) * 104) + 56#64 ∧
        s1.readReg64 .x19 = v19 ∧
        s1.readReg64 .x20 = v20 ∧
        s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x24 = v24 ∧
        s1.readReg64 .x27 = BitVec.ofNat 64 (p + 1) ∧
        s1.readReg64 .x28 = v28 ∧
        s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ emp)) := by
  wp_step
  wp_step
  wp_step
  wp_step
  wp_step
  apply SepWP.ite_true (by rfl) (by simp [arm64_norm]; exact remBytes_ne_zero hp1 hmax)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
    ?_, ?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], ?_,
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    Entails.refl _⟩
  · simp only [arm64_norm]
    exact remBytes_sub_104_eq hp1
  · simp only [arm64_norm]
    exact x8_step_84 mkPtr p
  · simp only [arm64_norm]
    exact ofNat_p_add_one p

theorem cmk_loop_miss_done_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)}
    (mkPtr v19 v20 v22 v24 v28 v29 : BitVec 64)
    (p mkLen : Nat) (hp1 : p + 1 = mkLen)
    (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 ((mkLen - 1 - p) * 104))
    (_hx8 : s.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (_hx19 : s.readReg64 .x19 = v19)
    (hx20 : s.readReg64 .x20 = v20)
    (hx22 : s.readReg64 .x22 = v22)
    (_hx24 : s.readReg64 .x24 = v24)
    (_hx27 : s.readReg64 .x27 = BitVec.ofNat 64 p)
    (hx28 : s.readReg64 .x28 = v28)
    (_hx29 : s.readReg64 .x29 = v29) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 180#64) s emp
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x20 = v20 ∧
        s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x28 = v28 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ emp)) := by
  wp_step
  wp_step
  wp_step
  wp_step
  wp_step
  apply SepWP.ite_false (by rfl) (by simp [arm64_norm]; exact remBytes_last_eq_zero hp1)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩, Entails.refl _⟩

theorem cmk_pos_loop_0x94_placed_outcome [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {H : String → Option (State → State)} {A : RustAlloc}
    (hA : CmkAllocHooks A H)
    (hmemmove_eq : H cmkMemmoveSym = some hookMemmove)
    (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 : State)
    {ci : Nat} (hci : x.st.findReceiverChainIndex x.their = some ci)
    (hi : ci < x.st.receiverChains.length)
    (hgi : ci < x.G.chains.length)
    (hprops : RatchetChainProps x.G x.st ci hgi hi)
    (hc_lt : x.counter < x.ck.index) :
    ∀ (rem p : Nat) (s : State),
      rem = (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length - p →
      p < (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length →
      x.st.receiverChains[ci].messageKeys.findIdx? (fun k => k.counter == x.counter) =
        List.findIdx?.go (fun k => k.counter == x.counter)
          (x.st.receiverChains[ci].messageKeys.drop p) p →
      s.pc = (blkPl_24).base + 148#64 →
      s.status = .Running →
      s.sp = s0.sp - 480#64 →
      s.spAligned = true →
      (s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) →
      s.readReg64 .x2 =
        BitVec.ofNat 64 (((x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length - 1 - p) * 104) →
      s.readReg64 .x8 = x.G.chains[ci].mkPtr + BitVec.ofNat 64 (p * 104) + 56#64 →
      s.readReg64 .x19 = x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) →
      s.readReg64 .x20 = x.counter.zeroExtend 64 →
      s.readReg64 .x22 = x.ret →
      s.readReg64 .x24 =
        BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length →
      s.readReg64 .x27 = BitVec.ofNat 64 p →
      s.readReg64 .x28 = x.ck.index.zeroExtend 64 →
      s.readReg64 .x29 = s0.sp - 96#64 →
      (s.mem ⊨
        (((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ x.G.chains[ci].mkPtr) ∗
         ((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄
           BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length) ∗
         vecBuf A 104 8 (messageKeyAt A) x.G.chains[ci].mkCap x.G.chains[ci].mkPtr
           (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys) ∗
         ratchetChainRest A x.self x.G x.st ci hgi hi ∗
         (x.theirA ↦ₛ x.their.bytes.toList) ∗
         (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
         memRegion x.ret 88 ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗
         stackAt (s0.sp - 480#64) 7712 ∗
         memRegion (s0.sp - 480#64) 384 ∗
         cmkSavedRegs s0.sp s0 ∗
         A.pool) ∗ R) →
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H) (cmkPlacedSpec F A) x R s0 s := by
  intro rem
  induction rem with
  | zero =>
    intro p s hrem hp
    omega
  | succ k ih =>
    intro p s hrem hp hfind hpc hrun hsp hsp_align htrace
      hx2 hx8 hx19 hx20 hx22 hx24 hx27 hx28 hx29 hm
    set chAddr := x.G.chainsPtr + BitVec.ofNat 64 (ci * 104)
    set g := x.G.chains[ci]
    set c := x.st.receiverChains[ci]
    set gks := g.keys.zip c.messageKeys
    have hkl : g.keys.length = c.messageKeys.length := hprops.keys_len
    have hzip_len : gks.length = c.messageKeys.length := by
      simp [gks, hkl]
    have hp_c : p < c.messageKeys.length := by omega
    have hgks_snd : gks[p].2 = c.messageKeys[p] := by
      simp [gks, List.getElem_zip]
    have hm_vec : s.mem ⊨
        vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks ∗
        (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
         ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
         ratchetChainRest A x.self x.G x.st ci hgi hi ∗
         (x.theirA ↦ₛ x.their.bytes.toList) ∗
         (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
         memRegion x.ret 88 ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗
         stackAt (s0.sp - 480#64) 7712 ∗
         memRegion (s0.sp - 480#64) 384 ∗
         cmkSavedRegs s0.sp s0 ∗
         A.pool ∗ R) :=
      Satisfies.of_eq hm
    by_cases heq : gks[p].2.counter = x.counter
    · have hfind_some : c.messageKeys.findIdx? (fun k => k.counter == x.counter) = some p := by
        rw [hfind, findIdx_go_step hp_c]
        have hbeq : (c.messageKeys[p].counter == x.counter) = true := by
          rw [← hgks_snd]; exact beq_iff_eq.mpr heq
        simp [hbeq]
      refine reaches_outcome.of_codeLoaded fun hL => ?_
      obtain ⟨s1, hsteps1, hpc1, hrun1, P1, hm1, hsp1, hsp1_align,
        hx2_1, hx8_1, hx19_1, hx20_1, hx22_1, hx24_1, hx27_1, hx28_1, hx29_1, htr1, hP1⟩ :=
        sepWP_to_reaches_pc
          (cmk_loop_hit_placed_wp g.mkCap g.mkPtr _ chAddr x.ret (BitVec.ofNat 64 gks.length)
            (BitVec.ofNat 64 p) (x.ck.index.zeroExtend 64) (s0.sp - 96#64)
            x.counter gks p hp heq s0 s hpc hrun hsp hsp_align
            hx2 hx8 hx19 hx20 hx22 hx24 hx27 hx28 hx29)
          hm_vec hL
      have hm1' : s1.mem ⊨
          (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
           ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
           vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks ∗
           ratchetChainRest A x.self x.G x.st ci hgi hi ∗
           (x.theirA ↦ₛ x.their.bytes.toList) ∗
           (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
           memRegion x.ret 88 ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗
           stackAt (s0.sp - 480#64) 7712 ∗
           memRegion (s0.sp - 480#64) 384 ∗
           cmkSavedRegs s0.sp s0 ∗
           A.pool) ∗ R :=
        Satisfies.of_eq (Satisfies.mono (sepConj_mono_left hP1) hm1)
      exact reaches_outcome_steps hsteps1
        (cmk_remove_0x5e4_placed_outcome hA hmemmove_eq x R s0 s1 hci hi hgi hprops hp hfind_some hc_lt
          hpc1 hrun1 hsp1 hsp1_align (by reg_chain)
          hx2_1 hx8_1 hx19_1 hx22_1 hx24_1 hx29_1 hm1')
    · have hfind_next :
          c.messageKeys.findIdx? (fun k => k.counter == x.counter) =
            List.findIdx?.go (fun k => k.counter == x.counter)
              (c.messageKeys.drop (p + 1)) (p + 1) := by
        rw [hfind, findIdx_go_step hp_c]
        have hbeq : (c.messageKeys[p].counter == x.counter) = false := by
          rw [← hgks_snd]; exact beq_eq_false_iff_ne.mpr heq
        simp [hbeq]
      refine reaches_outcome.of_codeLoaded fun hL => ?_
      obtain ⟨s1, hsteps1, hpc1, hrun1, P1, hm1, hsp1, hsp1_align,
        hx2_1, hx8_1, hx19_1, hx20_1, hx22_1, hx24_1, hx27_1, hx28_1, hx29_1, htr1, hP1⟩ :=
        sepWP_to_reaches_pc
          (cmk_loop_miss_head_placed_wp g.mkCap g.mkPtr _ chAddr x.ret (BitVec.ofNat 64 gks.length)
            (BitVec.ofNat 64 p) (x.ck.index.zeroExtend 64) (s0.sp - 96#64)
            x.counter gks p hp heq s0 s hpc hrun hsp hsp_align
            hx2 hx8 hx19 hx20 hx22 hx24 hx27 hx28 hx29)
          hm_vec hL
      have hm1_emp : s1.mem ⊨
          emp ∗
          (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
           ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
           vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks ∗
           ratchetChainRest A x.self x.G x.st ci hgi hi ∗
           (x.theirA ↦ₛ x.their.bytes.toList) ∗
           (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
           memRegion x.ret 88 ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗
           stackAt (s0.sp - 480#64) 7712 ∗
           memRegion (s0.sp - 480#64) 384 ∗
           cmkSavedRegs s0.sp s0 ∗
           A.pool ∗ R) :=
        Satisfies.of_eq (Satisfies.mono (sepConj_mono_left hP1) hm1)
      have hL1 : ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s1.mem :=
        hsteps1.codeLoaded hL
      by_cases hp1 : p + 1 < gks.length
      · have hmax_gks : gks.length ≤ maxMessageKeys := by
          rw [hzip_len]; exact hprops.mk_max
        obtain ⟨s2, hsteps2, hpc2, hrun2, P2, hm2, hsp2, hsp2_align,
          hx2_2, hx8_2, hx19_2, hx20_2, hx22_2, hx24_2, hx27_2, hx28_2, hx29_2, htr2, hP2⟩ :=
          sepWP_to_reaches_pc
            (cmk_loop_miss_cont_placed_wp g.mkPtr chAddr (x.counter.zeroExtend 64) x.ret
              (BitVec.ofNat 64 gks.length) (x.ck.index.zeroExtend 64) (s0.sp - 96#64)
              p gks.length hp1 hmax_gks s0 s1 hpc1 hrun1 hsp1 hsp1_align
              hx2_1 hx8_1 hx19_1 hx20_1 hx22_1 hx24_1 hx27_1 hx28_1 hx29_1)
            hm1_emp hL1
        have hm2' : s2.mem ⊨
            (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
             ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
             vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks ∗
             ratchetChainRest A x.self x.G x.st ci hgi hi ∗
             (x.theirA ↦ₛ x.their.bytes.toList) ∗
             (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
             memRegion x.ret 88 ∗
             (lsLogFilterAddr ↦₆₄ 0#64) ∗
             stackAt (s0.sp - 480#64) 7712 ∗
             memRegion (s0.sp - 480#64) 384 ∗
             cmkSavedRegs s0.sp s0 ∗
             A.pool) ∗ R :=
          Satisfies.of_eq (Satisfies.mono (sepConj_mono_left hP2) hm2)
        exact reaches_outcome_steps (hsteps1.trans hsteps2)
          (ih (p + 1) s2 (by omega) hp1 hfind_next hpc2 hrun2 hsp2 hsp2_align
            (by reg_chain)
            hx2_2 hx8_2 hx19_2 hx20_2 hx22_2 hx24_2 hx27_2 hx28_2 hx29_2 hm2')
      · have hp1_eq : p + 1 = gks.length := by omega
        obtain ⟨s2, hsteps2, hpc2, hrun2, P2, hm2, hsp2, hsp2_align,
          hx20_2, hx22_2, hx28_2, htr2, hP2⟩ :=
          sepWP_to_reaches_pc
            (cmk_loop_miss_done_placed_wp g.mkPtr chAddr (x.counter.zeroExtend 64) x.ret
              (BitVec.ofNat 64 gks.length) (x.ck.index.zeroExtend 64) (s0.sp - 96#64)
              p gks.length hp1_eq s0 s1 hpc1 hrun1 hsp1 hsp1_align
              hx2_1 hx8_1 hx19_1 hx20_1 hx22_1 hx24_1 hx27_1 hx28_1 hx29_1)
            hm1_emp hL1
        have hm2_pre : s2.mem ⊨ cmkPreLoopHeap_placed A x s0 ∗ R := by
          unfold cmkPreLoopHeap_placed
          have hm2' := Satisfies.mono (sepConj_mono_left hP2) hm2
          have hreassemble := ratchetAt_reassemble_self A x.self x.G x.st hi hgi hprops
          have hm2'' : s2.mem ⊨
              (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
                ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
                vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks ∗
                ratchetChainRest A x.self x.G x.st ci hgi hi) ∗
              ((x.theirA ↦ₛ x.their.bytes.toList) ∗
                (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
                memRegion x.ret 88 ∗
                (lsLogFilterAddr ↦₆₄ 0#64) ∗
                stackAt (s0.sp - 480#64) 7712 ∗
                memRegion (s0.sp - 480#64) 384 ∗
                cmkSavedRegs s0.sp s0 ∗
                A.pool ∗ R) :=
            Satisfies.of_eq hm2'
          exact Satisfies.of_eq (Satisfies.mono (sepConj_mono_left hreassemble) hm2'')
        have hfind_none : c.messageKeys.findIdx? (fun k => k.counter == x.counter) = none := by
          rw [hfind_next, List.drop_eq_nil_of_le (by omega), List.findIdx?.go]
        have hmodel := cmk_model_past_miss_chain F x hci hi hfind_none hc_lt
        exact reaches_outcome_steps (hsteps1.trans hsteps2)
          (cmk_dup_0xb4_placed_outcome x R s0 s2 hpc2 hrun2 hsp2 hsp2_align
            (by reg_chain) hx20_2 hx22_2 hx28_2 hmodel hm2_pre)

end CryptoVerification.LibsignalSession.TakePath
