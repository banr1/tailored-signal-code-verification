/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Bin.OpenSegs
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base

/-!
# Store-Session Segment Proof for `libsignal_e2e::open` (`0x43c6c..0x43ca0`)

Proves segment 7 (`open_seg_store_session'`, `+0x234..+0x268`) of `libsignal_e2e::open`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Bin

set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open Arm64 ProofLib ProofLib.ObjectLoad CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.InMem

variable {C : Crypto} {A : RustAlloc} {S : SpqrModel}

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  tpidrEl0_setPC_pre_open tpidrEl0_setMem_setPC_pre_open
  trace_setPC_pre_open trace_setMem_setPC_pre_open
  fastStateSP fastReadReg64 fastReadReg32 fastReadReg
attribute [-arm64_norm, -wp_norm]
  ProofLib.reduceStateSP ProofLib.reduceStateReadReg64
  ProofLib.reduceStateReadReg32 ProofLib.reduceStateReadReg

/-! ## Segment 7: `open_seg_store_session'` (`+0x234..+0x268`, 13 insns) -/

attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg

private theorem exists_mem_zip_of_mem_left :
    ∀ {α β : Type} {xs : List α} {ys : List β} {x : α},
      xs.length = ys.length → x ∈ xs → ∃ y, (x, y) ∈ xs.zip ys
  | _, _, [], [], _, _, hx => by simp at hx
  | _, _, x' :: xs, y' :: ys, x, hlen, hx => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨y', List.mem_cons_self ..⟩
    · obtain ⟨y, hy⟩ := exists_mem_zip_of_mem_left hlen hx
      exact ⟨y, List.mem_cons_of_mem _ hy⟩

private theorem binCanonSession_of_canonSession_storeSession {G0 G : SessionGhost} {s : Session (List (BitVec 8))}
    (h0 : BinCanonSession G0 s) (hG : Record.Serialization.CanonSession G s) :
    BinCanonSession G s := by
  rcases h0 with ⟨_, hwf, _, _, _, hrc_len, hrc_mk, _, halice, hkyber, hpq, henc⟩
  rcases hG with ⟨hlocal, hrem, hsender, hlen_eq, hzip, hpend⟩
  refine ⟨⟨hlocal, hrem, hsender, hlen_eq, hzip, hpend⟩,
    hwf, hlocal, ?_, ?_, hrc_len, hrc_mk, ?_, halice, hkyber, hpq, henc⟩
  · cases hri : s.state.remoteIdentity <;> simpa [hri] using hrem
  · revert hsender; unfold Record.Serialization.CanonSender
    cases G.sender <;> cases s.state.senderChain <;> intro hsender
    · exact True.intro
    · exact hsender
    · exact hsender
    · exact hsender.1
  · intro cg hcg
    obtain ⟨rc, hmem⟩ := exists_mem_zip_of_mem_left hlen_eq hcg
    have hcc := hzip (cg, rc) hmem
    have hser_len : rc.senderRatchetKey.serialize.length = 33 := by
      unfold PublicKey.serialize; simp [List.Vector.toList_length]
    exact ⟨hcc.1 ▸ hser_len, hcc.2⟩

private theorem sessionRecordAt_entails_memRegion_0x170_anyHeap (A : RustAlloc) (r : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    sessionRecordAt A r ⟨0#64, 8#64, some G⟩ ⟨some sess⟩ ⊢ memRegion r 0x170 ∗ anyHeap := by
  rw [sessionRecordAt_eq_word0_sep_tail_sep_heap A r G sess]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; rintro ⟨hlen, _⟩
  have h0 : (r ↦₆₄ 0#64) ⊢ memRegion r 8 := pointsTo64_entails_memRegion r 0#64
  have h1 : ((r + 8#64) ↦ₛ (unpack64 8#64 ++ unpack64 0#64 ++ bs)) ⊢ memRegion (r + 8#64) 360 := by
    have h := ProofLib.pointsToBytes_entails_memRegion (r + 8#64) (unpack64 8#64 ++ unpack64 0#64 ++ bs)
    have hlen' : (unpack64 8#64 ++ unpack64 0#64 ++ bs).length = 360 := by simp [unpack64_length, hlen]
    rwa [hlen'] at h
  have hany : sessionRecordHeap A G sess ⊢ anyHeap := ProofLib.entails_anyHeap _
  rw [memRegion_split r 8 360 (by decide), ← sepConj_assoc]
  exact sepConj_mono (sepConj_mono h0 h1) hany

private theorem if_entry_mono (c : Prop) [Decidable c] {P Q R : SepProp} (h : P ⊢ Q) :
    (if c then P else R) ⊢ (if c then Q else R) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact h
  · simp only [hc, ↓reduceIte]; exact Entails.refl _

private theorem arrayAt_mono_entry4 (stride : Nat) (base : BitVec 64) (k : Nat)
    {entry1 entry2 : BitVec 64 → SepProp} (he : ∀ a, entry1 a ⊢ entry2 a) :
    arrayAt (fun i a => if i ∈ [k] then entry1 a else memRegion a stride) stride base (List.range 4).reverse ⊢
      arrayAt (fun i a => if i ∈ [k] then entry2 a else memRegion a stride) stride base (List.range 4).reverse := by
  change arrayAt (fun i a => if i ∈ [k] then entry1 a else memRegion a stride) stride base [3, 2, 1, 0] ⊢
    arrayAt (fun i a => if i ∈ [k] then entry2 a else memRegion a stride) stride base [3, 2, 1, 0]
  dsimp only [arrayAt]
  exact sepConj_mono (if_entry_mono _ (he _))
    (sepConj_mono (if_entry_mono _ (he _))
      (sepConj_mono (if_entry_mono _ (he _))
        (sepConj_mono (if_entry_mono _ (he _)) (Entails.refl _))))

private theorem table4SingleAt_sessionBucketEntryAt_entails_inMemSessionStoreAt
    (A : RustAlloc) (img : Obj.Image) (out k0 k1 : BitVec 64) (peer : Role)
    (gPeer clonedG : AddrGhost) (G0 clonedRecG : SessionGhost) (sess : Session (List (BitVec 8)))
    (k : Nat) (hPeer : gPeer.val = peer.addrVal)
    (hcName : clonedG.name.bytes = gPeer.name.bytes) (hcDev : clonedG.device = gPeer.device)
    (hCan0 : BinCanonSession G0 sess) (hCan : Record.Serialization.CanonSession clonedRecG sess) :
    HashbrownBin.table4SingleAt A HashbrownBin.sessionBucketStride out k0 k1 k
        gPeer.name.bytes gPeer.device (HashbrownBin.sessionBucketEntryAt A clonedG clonedRecG sess) ⊢
      inMemSessionStoreAt A img out peer (some sess) := by
  have hPeerName : gPeer.name.bytes = peer.nameBytes := by injection hPeer with h1 _
  have hPeerDev : gPeer.device = 1#8 := by injection hPeer with _ h2
  have hcVal : clonedG.val = peer.addrVal := by
    unfold AddrGhost.val Role.addrVal; rw [hcName, hcDev, hPeerName, hPeerDev]
  have hBinCan : BinCanonSession clonedRecG sess := binCanonSession_of_canonSession_storeSession hCan0 hCan
  unfold inMemSessionStoreAt
  refine Entails.sepExists_right k0 (Entails.sepExists_right k1 (Entails.sepExists_right k
    (Entails.sepExists_right clonedG (Entails.sepExists_right clonedRecG ?_))))
  refine Entails.pure_right ⟨hcVal, hBinCan⟩ ?_
  rw [hPeerName, hPeerDev]
  unfold HashbrownBin.table4SingleAt HashbrownBin.table4At
  refine sepConj_mono_right (Entails.sepExists_elim fun ctrl => Entails.sepExists_right ctrl ?_)
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (arrayAt_mono_entry4 _ _ _ fun a => ?_)))))))))
  unfold HashbrownBin.sessionBucketEntryAt
  exact Entails.pure_left fun _ => Entails.refl _

end CryptoVerification.E2E.Bin
