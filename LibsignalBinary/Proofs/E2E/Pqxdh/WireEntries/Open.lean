/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.OpenEmptyPrefix
import LibsignalBinary.Proofs.E2E.Bin.DeserializeX -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.OpenDeserId -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.L1GX.Glue -- shake: keep

/-!
# `libsignal_pqxdh_e2e::open` (`0x75f48`) — Store-Session Segment (`+0x264..+0x2a4`)

Proves Segment 3d (`<InMemSessionStore>::store_session` and `poll_once`) of the non-empty-state
branch of `libsignal_pqxdh_e2e::open`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.WireEntries

set_option warningAsError false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
export CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec
open CryptoVerification.E2E.InMem

/-! ## Segment 3d (`+0x264..+0x2a4`): `<InMemSessionStore>::store_session` and `poll_once` -/

private theorem mem_zip_of_mem_left_openP :
    ∀ {α β : Type} {xs : List α} {ys : List β} {x : α},
      xs.length = ys.length → x ∈ xs → ∃ y, (x, y) ∈ xs.zip ys
  | _, _, [], [], _, _, hx => by simp at hx
  | _, _, x' :: xs, y' :: ys, x, hlen, hx => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨y', List.mem_cons_self ..⟩
    · obtain ⟨y, hy⟩ := mem_zip_of_mem_left_openP hlen hx
      exact ⟨y, List.mem_cons_of_mem _ hy⟩

private theorem binCanonSession_of_l2_openP {G0 G : SessionGhost} {s : Session (List (BitVec 8))}
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
    obtain ⟨rc, hmem⟩ := mem_zip_of_mem_left_openP hlen_eq hcg
    have hcc := hzip (cg, rc) hmem
    have hser_len : rc.senderRatchetKey.serialize.length = 33 := by
      unfold PublicKey.serialize; simp [List.Vector.toList_length]
    exact ⟨hcc.1 ▸ hser_len, hcc.2⟩

private theorem sessionRecordAt_entails_memRegion_0x170_anyHeap_openP (A : RustAlloc) (r : BitVec
    64)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    sessionRecordAt A r ⟨0#64, 8#64, some G⟩ ⟨some sess⟩ ⊢ memRegion r 0x170 ∗ anyHeap := by
  rw [sessionRecordAt_eq_word0_sep_tail_sep_heap A r G sess]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; rintro ⟨hlen, _⟩
  have h0 : (r ↦₆₄ 0#64) ⊢ memRegion r 8 := pointsTo64_entails_memRegion r 0#64
  have h1 : ((r + 8#64) ↦ₛ (unpack64 8#64 ++ unpack64 0#64 ++ bs)) ⊢ memRegion (r + 8#64) 360 := by
    have h := ProofLib.pointsToBytes_entails_memRegion (r +
      8#64) (unpack64 8#64 ++ unpack64 0#64 ++ bs)
    have hlen' : (unpack64 8#64 ++ unpack64 0#64 ++ bs).length = 360 := by
      simp [unpack64_length, hlen]
    rwa [hlen'] at h
  have hany : sessionRecordHeap A G sess ⊢ anyHeap := ProofLib.entails_anyHeap _
  rw [memRegion_split r 8 360 (by decide), ← sepConj_assoc]
  exact sepConj_mono (sepConj_mono h0 h1) hany

private theorem if_entry_mono_openP (c : Prop) [Decidable c] {P Q R : SepProp} (h : P ⊢ Q) :
    (if c then P else R) ⊢ (if c then Q else R) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact h
  · simp only [hc, ↓reduceIte]; exact Entails.refl _

private theorem arrayAt_mono_entry4_openP (stride : Nat) (base : BitVec 64) (k : Nat)
    {entry1 entry2 : BitVec 64 → SepProp} (he : ∀ a, entry1 a ⊢ entry2 a) :
    arrayAt (fun i a => if i ∈ [k] then entry1 a else memRegion a stride) stride base (List.range
      4).reverse ⊢
      arrayAt (fun i a => if i ∈ [k] then entry2 a else memRegion a stride) stride base (List.range
        4).reverse := by
  change arrayAt (fun i a => if i ∈ [k] then entry1 a else memRegion a stride) stride base [3, 2,
      1, 0] ⊢
    arrayAt (fun i a => if i ∈ [k] then entry2 a else memRegion a stride) stride base [3, 2, 1, 0]
  dsimp only [arrayAt]
  exact sepConj_mono (if_entry_mono_openP _ (he _))
    (sepConj_mono (if_entry_mono_openP _ (he _))
      (sepConj_mono (if_entry_mono_openP _ (he _))
        (sepConj_mono (if_entry_mono_openP _ (he _)) (Entails.refl _))))

private theorem table4SingleAt_sessionBucketEntryAt_entails_inMemSessionStoreAt_openP
    (A : RustAlloc) (img : Obj.Image) (out k0 k1 : BitVec 64) (peer : Role)
    (gPeer clonedG : AddrGhost) (G0 clonedRecG : SessionGhost) (sess : Session (List (BitVec 8)))
    (k : Nat) (hPeer : gPeer.val = peer.addrVal)
    (hcName : clonedG.name.bytes = gPeer.name.bytes) (hcDev : clonedG.device = gPeer.device)
    (hCan0 : BinCanonSession G0 sess) (hCan : Record.Serialization.CanonSession clonedRecG sess) :
    HashbrownBin.table4SingleAt A HashbrownBin.sessionBucketStride out k0 k1 k
        gPeer.name.bytes gPeer.device (HashbrownBin.sessionBucketEntryAt A clonedG clonedRecG sess)
          ⊢
      inMemSessionStoreAt A img out peer (some sess) := by
  have hPeerName : gPeer.name.bytes = peer.nameBytes := by injection hPeer with h1 _
  have hPeerDev : gPeer.device = 1#8 := by injection hPeer with _ h2
  have hcVal : clonedG.val = peer.addrVal := by
    unfold AddrGhost.val Role.addrVal; rw [hcName, hcDev, hPeerName, hPeerDev]
  have hBinCan : BinCanonSession clonedRecG sess := binCanonSession_of_l2_openP hCan0 hCan
  unfold inMemSessionStoreAt
  refine Entails.sepExists_right k0 (Entails.sepExists_right k1 (Entails.sepExists_right k
    (Entails.sepExists_right clonedG (Entails.sepExists_right clonedRecG ?_))))
  refine Entails.pure_right ⟨hcVal, hBinCan⟩ ?_
  rw [hPeerName, hPeerDev]
  unfold HashbrownBin.table4SingleAt HashbrownBin.table4At
  refine sepConj_mono_right (Entails.sepExists_elim fun ctrl => Entails.sepExists_right ctrl ?_)
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (arrayAt_mono_entry4_openP _ _ _ fun a => ?_)))))))))
  unfold HashbrownBin.sessionBucketEntryAt
  exact Entails.pure_left fun _ => Entails.refl _

theorem word_and_40_entails_memRegion_48 (sp w : BitVec 64) :
    ((sp + 0x260#64) ↦₆₄ w) ∗ memRegion (sp + 0x268#64) 40 ⊢
      memRegion (sp + 0x260#64) 48 := by
  rw [memRegion_split' (b := sp + 0x260#64) (b' := sp + 0x268#64)
        (N := 48) (n := 8) (k := 40) (by decide) (by bv_lin) (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)

theorem memRegion_openP_0x0f0_0x360_store_join (sp w0 w1 w2 w3 : BitVec 64) :
    (memRegion (sp + 0x0f0#64) 0x170 ∗
     ((sp + 0x260#64) ↦₆₄ w0) ∗ memRegion (sp + 0x268#64) 40 ∗
     memRegion (sp + 0x290#64) 0x160 ∗
     ((sp + 0x3f0#64) ↦₆₄ w1) ∗ ((sp + 0x3f8#64) ↦₆₄ w2) ∗
     ((sp + 0x400#64) ↦₆₄ w3) ∗ memRegion (sp + 0x408#64) 0x48) ⊢
      memRegion (sp + 0x0f0#64) 0x360 := by
  have h48 := word_and_40_entails_memRegion_48 sp w0
  have h24 : (((sp + 0x3f0#64) ↦₆₄ w1) ∗ ((sp + 0x3f8#64) ↦₆₄ w2) ∗ ((sp + 0x400#64) ↦₆₄ w3)) ⊢
      memRegion (sp + 0x3f0#64) 24 := by
    rw [memRegion_split' (b := sp + 0x3f0#64) (b' := sp + 0x3f8#64)
          (N := 24) (n := 8) (k := 16) (by decide) (by bv_lin) (by decide),
        memRegion_split' (b := sp + 0x3f8#64) (b' := sp + 0x400#64)
          (N := 16) (n := 8) (k := 8) (by decide) (by bv_lin) (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
  rw [memRegion_split' (b := sp + 0x0f0#64) (b' := sp + 0x260#64)
        (N := 0x360) (n := 0x170) (k := 496) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x260#64) (b' := sp + 0x290#64)
        (N := 496) (n := 48) (k := 448) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x290#64) (b' := sp + 0x3f0#64)
        (N := 448) (n := 0x160) (k := 96) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x3f0#64) (b' := sp + 0x408#64)
        (N := 96) (n := 24) (k := 0x48) (by decide) (by bv_lin) (by decide)]
  refine sepConj_mono_right ?_
  rw [← sepConj_assoc ((sp + 0x260#64) ↦₆₄ w0)]
  refine sepConj_mono h48 (sepConj_mono_right ?_)
  rw [← sepConj_assoc ((sp + 0x3f0#64) ↦₆₄ w1), ← sepConj_assoc (((sp + 0x3f0#64) ↦₆₄ w1) ∗ _),
      sepConj_assoc ((sp + 0x3f0#64) ↦₆₄ w1) ((sp + 0x3f8#64) ↦₆₄ w2) ((sp + 0x400#64) ↦₆₄ w3)]
  exact sepConj_mono_left h24

def OpenSeam2a4P (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (img : Obj.Image) (abs : String → Option (State → State))
    (g : OpenGhostP) (role : Role) (R : SepProp) (s0 s : State) : Prop :=
  s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr openPqxdhName + 0x2a4#64 ∧
    s.status = .Running ∧ s.spAligned = true ∧
    s0.spAligned = true ∧ openPqxdhStack ≤ s0.sp.toNat ∧
    s.sp = s0.sp - 0x4b0#64 ∧
    s.trace = s0.trace ∧
    s.readReg64 .x19 = g.outPtr ∧
    OpenX27VPreserved s s0 ∧
    (s.mem ⊨
      callAtP A img (s.sp + 0x008#64) role
        (meKeyPairBytes C.pubKey g.meBytes) (meRegId g.meBytes) g.sess ∗
      memRegion s.sp 8 ∗ memRegion (s.sp + 0x0f0#64) 0x360 ∗
      openSavedRegsAtP s0 ∗
      memRegion g.outPtr 232 ∗ (g.mePtr ↦ₛ g.meBytes) ∗
      (g.statePtr ↦ₛ g.stateBytes) ∗ logOff img ∗
      (∃∗ tlsCur, tlsKeysAt (s0.tpidrEl0 + tlsKeysTpoff) tlsCur) ∗
      A.pool ∗ memRegion (s0.sp - openPqxdhStack) (openPqxdhStack - 0x4b0) ∗
      R ∗ anyHeap)


end CryptoVerification.E2E.Pqxdh.WireEntries
