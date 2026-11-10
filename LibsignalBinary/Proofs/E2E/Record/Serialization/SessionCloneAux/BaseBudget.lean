/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneBaseBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-threaded helpers and allocation-envelope bridge for `SessionStructure::clone`

Relocatable `[LibsignalPlacement]` helpers for block `80` (`lsProg_80 H`) and the deterministic
trace-to-envelope bridge (`sessionCloneEnv_segCloneEvents`, `fitsEvents_segCloneEvents_of_fitsEnv`),
showing that `FitsEnv M lim st (SessionCloneEnv G s)` implies `FitsEvents M lim st` for
`segCloneEvents G s.state` and rules out OOM and `handle_error` branches.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.BaseBudget

open Arm64 ProofLib SepProp
open Arm64.Obj (MultiPlacement)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize mallocngAlignedEffSize)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoGames.LibsignalSession (ReceiverChain MessageKeyGenerator)
open CryptoVerification (
  LibsignalPlacement LibsignalCodeLoaded lsmpl lsρ ls_hook_ok_of_mem ls_subroutine_ok_of_block
  lsRustNoAllocShimSym lsRustAllocSym lsMemcpySym
  sepWP_mono_lscl withLsCodeLoaded subroutine_ok_withLsCodeLoaded_of_plain
)
open CryptoVerification.LibsignalSessionRepr (VecGhost ChainGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SessionGhost SenderChainGhost TailVecGhost
)
open CryptoVerification.LibsignalProtoCodec (WireType encodeKey encodeVarint encodeVarintAux)
open CryptoVerification.LibsignalPublicApiRepr (PendingRel KyberRel)
open CryptoVerification.E2E.Record (
  lenField bytesField msgField encChainKey encMessageKey encPendingKyber
)
open CryptoVerification.E2E.Record.Placed (
  blkPl_80 blkPl_82 lsProg_80
)
open CryptoVerification.E2E.Record.Serialization (
  SessionCloneGhost encChainMem encSenderFieldMem encPendingFieldMem encSessionMem
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
  FitsStep FitsEvent FitsEvents FitsEnv
  rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (
  rustAllocShimVmSpec allocMemcpyVmSpec
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  chainCloneEvents senderChainAsProtoGhost senderChainCloneEvents
  ChainCloneEnv SenderChainCloneEnv chainCloneSpec senderChainCloneSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  vecCloneEvents optTailCloneEvents segCloneEvents
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (
  BoundedRustEvs SessionCloneEnv PlacedSerializeHooks
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneBaseBudget (
  protoChainCloneSpec ProtoChainCloneLocal1PlacedOk
  ChainCloneLocal1PlacedOk SenderChainCloneLocal1PlacedOk
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## `BoundedRustEvs` and encoded-length lower bounds -/

private theorem encodeVarint_length_pos (v : BitVec 64) : 1 ≤ (encodeVarint v).length := by
  unfold encodeVarint encodeVarintAux
  split <;> simp

private theorem lenField_length_ge (tag : Nat) (payload : List (BitVec 8)) :
    2 + payload.length ≤ (lenField tag payload).length := by
  unfold lenField encodeKey
  have h1 := encodeVarint_length_pos (BitVec.ofNat 64 (tag * 8 + WireType.lengthDelimited.toNat))
  have h2 := encodeVarint_length_pos (BitVec.ofNat 64 payload.length)
  simp only [List.length_append]
  omega

private theorem bytesField_length_ge (tag : Nat) (v : List (BitVec 8)) :
    v.length ≤ (bytesField tag v).length := by
  unfold bytesField
  split
  · subst_vars; simp
  · have := lenField_length_ge tag v; omega

theorem boundedRustEvs_rustAlloc {n al r : Nat}
    (hal : al = 1 ∨ al = 8) (hn : n ≤ r) (hr : r ≤ MallocngMaxAllocSize) :
    BoundedRustEvs 1 r (rustAllocEvents n al) := by
  have hal16 : max al 8 ≤ 16 := by rcases hal with rfl | rfl <;> decide
  unfold rustAllocEvents
  split
  · refine ⟨by simp, fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev; subst hev
    exact ⟨Nat.le_trans hn hr, hn, by rintro _ _ ⟨⟩, by rintro _ _ _ ⟨⟩⟩
  · refine ⟨by simp, fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev; subst hev
    have heff : mallocngAlignedEffSize (max al 8) n = n := by
      unfold mallocngAlignedEffSize; simp [hal16]
    refine ⟨?_, ?_, ?_, by rintro _ _ _ ⟨⟩⟩
    · dsimp only [AllocEvent.withinMaxAlloc]; rw [heff]; exact Nat.le_trans hn hr
    · dsimp only [AllocEvent.reqBytes]; rw [heff]; exact hn
    · intro al' _ h; cases h; exact hal16

theorem boundedRustEvs_append_same {c₁ c₂ r : Nat} {evs₁ evs₂ : List AllocEvent}
    (h1 : BoundedRustEvs c₁ r evs₁) (h2 : BoundedRustEvs c₂ r evs₂) :
    BoundedRustEvs (c₁ + c₂) r (evs₁ ++ evs₂) := by
  simpa [Nat.max_self] using BoundedRustEvs.append h1 h2

theorem boundedRustEvs_vecClone {v : VecGhost} {r : Nat}
    (hlen : v.bytes.length ≤ r) (hr : r ≤ MallocngMaxAllocSize) :
    BoundedRustEvs 1 r (vecCloneEvents v) := by
  unfold vecCloneEvents
  split
  · exact BoundedRustEvs.nil 1 r
  · exact boundedRustEvs_rustAlloc (Or.inl rfl) hlen hr

private theorem encMsgKeys_bounds :
    ∀ (mks : List MessageKeyGenerator) {r : Nat},
      ((mks.map fun mkg => lenField 4 (encMessageKey mkg)).flatten).length ≤ r →
      r ≤ MallocngMaxAllocSize →
      2 * mks.length ≤ ((mks.map fun mkg => lenField 4 (encMessageKey mkg)).flatten).length ∧
      BoundedRustEvs mks.length r (mks.flatMap fun mkg => rustAllocEvents mkg.seed.length 1)
  | [], _, _, _ => ⟨by simp, BoundedRustEvs.nil 0 _⟩
  | mkg :: tl, r, hlen, hr => by
    simp only [List.map_cons, List.flatten_cons, List.length_append] at hlen ⊢
    have hmk_ge := lenField_length_ge 4 (encMessageKey mkg)
    have hseed_ge : mkg.seed.length ≤ (encMessageKey mkg).length := by
      unfold encMessageKey; simp only [List.length_append]
      have := bytesField_length_ge 5 mkg.seed; omega
    have hseed_le_r : mkg.seed.length ≤ r := by omega
    have htl_le_r : ((tl.map fun mkg => lenField 4 (encMessageKey mkg)).flatten).length ≤ r := by
      omega
    obtain ⟨htl_cnt, htl_ev⟩ := encMsgKeys_bounds tl htl_le_r hr
    refine ⟨by simp only [List.length_cons]; omega, ?_⟩
    simp only [List.flatMap_cons]
    have h1 := boundedRustEvs_rustAlloc (n := mkg.seed.length) (al := 1) (Or.inl rfl) hseed_le_r hr
    simpa [Nat.add_comm] using boundedRustEvs_append_same h1 htl_ev

theorem boundedRustEvs_chainClone (gc : ChainGhost × ReceiverChain) {r : Nat}
    (h32 : 32 ≤ r) (h52 : 52 * (encChainMem gc).length ≤ r) (hr : r ≤ MallocngMaxAllocSize) :
    BoundedRustEvs (4 + gc.2.messageKeys.length) r (chainCloneEvents gc) ∧
      2 * gc.2.messageKeys.length ≤ (encChainMem gc).length := by
  have henc : (encChainMem gc).length =
      (bytesField 1 gc.1.srk.bytes).length + (bytesField 2 gc.1.priv.bytes).length +
      (msgField 3 (gc.2.chainKey.map encChainKey)).length +
      ((gc.2.messageKeys.map fun mkg => lenField 4 (encMessageKey mkg)).flatten).length := by
    unfold encChainMem; simp only [List.length_append, Nat.add_assoc]
  have hsrk_ge := bytesField_length_ge 1 gc.1.srk.bytes
  have hpriv_ge := bytesField_length_ge 2 gc.1.priv.bytes
  have hsrk_le : gc.1.srk.bytes.length ≤ r := by omega
  have hpriv_le : gc.1.priv.bytes.length ≤ r := by omega
  have hmks_le :
      ((gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length ≤ r := by
    omega
  obtain ⟨hmks_cnt, hmks_ev⟩ := encMsgKeys_bounds gc.2.messageKeys hmks_le hr
  have hcnt2 : 2 * gc.2.messageKeys.length ≤ (encChainMem gc).length := by omega
  have h104 : 104 * gc.2.messageKeys.length ≤ r := by omega
  have hsrk_ev : BoundedRustEvs 1 r
      (if gc.1.srk.bytes.length = 0 then [] else rustAllocEvents gc.1.srk.bytes.length 1) := by
    split
    · exact BoundedRustEvs.nil 1 r
    · exact boundedRustEvs_rustAlloc (Or.inl rfl) hsrk_le hr
  have hpriv_ev : BoundedRustEvs 1 r
      (if gc.1.priv.bytes.length = 0 then [] else rustAllocEvents gc.1.priv.bytes.length 1) := by
    split
    · exact BoundedRustEvs.nil 1 r
    · exact boundedRustEvs_rustAlloc (Or.inl rfl) hpriv_le hr
  have hck_ev : BoundedRustEvs 1 r
      (match gc.2.chainKey with | none => [] | some _ => rustAllocEvents 32 1) := by
    cases gc.2.chainKey
    · exact BoundedRustEvs.nil 1 r
    · exact boundedRustEvs_rustAlloc (Or.inl rfl) h32 hr
  have hmk_ev : BoundedRustEvs (1 + gc.2.messageKeys.length) r
      (if gc.2.messageKeys = [] then []
       else rustAllocEvents (104 * gc.2.messageKeys.length) 8 ++
         gc.2.messageKeys.flatMap (fun mkg => rustAllocEvents mkg.seed.length 1)) := by
    split
    · exact BoundedRustEvs.nil _ r
    · exact boundedRustEvs_append_same
        (boundedRustEvs_rustAlloc (Or.inr rfl) h104 hr) hmks_ev
  unfold chainCloneEvents
  have h12 := boundedRustEvs_append_same hsrk_ev hpriv_ev
  have h123 := boundedRustEvs_append_same h12 hck_ev
  have h1234 := boundedRustEvs_append_same h123 hmk_ev
  have h1234' := BoundedRustEvs.mono (c₂ := 4 + gc.2.messageKeys.length)
    (by omega) (Nat.le_refl r) h1234
  refine ⟨?_, hcnt2⟩
  convert h1234' using 1
  cases gc.2.chainKey <;> by_cases hmk : gc.2.messageKeys = [] <;>
    simp only [hmk, ↓reduceIte, List.append_assoc]

private theorem encChains_bounds :
    ∀ (gcs : List (ChainGhost × ReceiverChain)) {r : Nat},
      32 ≤ r →
      52 * ((gcs.map fun gc => lenField 7 (encChainMem gc)).flatten).length ≤ r →
      r ≤ MallocngMaxAllocSize →
      2 * gcs.length ≤ ((gcs.map fun gc => lenField 7 (encChainMem gc)).flatten).length ∧
      BoundedRustEvs
        (2 * ((gcs.map fun gc => lenField 7 (encChainMem gc)).flatten).length)
        r (gcs.flatMap chainCloneEvents)
  | [], r, _, _, _ => ⟨by simp, BoundedRustEvs.nil 0 r⟩
  | gc :: tl, r, h32, h52, hr => by
    simp only [List.map_cons, List.flatten_cons, List.length_append] at h52 ⊢
    have hgc_ge := lenField_length_ge 7 (encChainMem gc)
    have hgc_52 : 52 * (encChainMem gc).length ≤ r := by omega
    have htl_52 : 52 * ((tl.map fun gc => lenField 7 (encChainMem gc)).flatten).length ≤ r := by
      omega
    obtain ⟨hgc_ev, hgc_cnt2⟩ := boundedRustEvs_chainClone gc h32 hgc_52 hr
    obtain ⟨htl_len, htl_ev⟩ := encChains_bounds tl h32 htl_52 hr
    refine ⟨by simp only [List.length_cons]; omega, ?_⟩
    simp only [List.flatMap_cons]
    have hgc_ev' : BoundedRustEvs (2 * (lenField 7 (encChainMem gc)).length) r
        (chainCloneEvents gc) :=
      BoundedRustEvs.mono (by omega) (Nat.le_refl r) hgc_ev
    exact BoundedRustEvs.mono (by omega) (Nat.le_refl r)
      (boundedRustEvs_append_same hgc_ev' htl_ev)

/-! ## `SessionCloneEnv` request ceiling and `segCloneEvents` bridge -/

theorem maxReq_le_mallocngMaxAllocSize_of_fitsEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {G : SessionGhost} {s : Session (List (BitVec 8))}
    (hfit : FitsEnv M lim st (SessionCloneEnv G s)) :
    256 * ((encSessionMem G s).length + 16) ≤ MallocngMaxAllocSize := by
  let encLen := (encSessionMem G s).length
  let r := 256 * (encLen + 16)
  let req₀ := min MallocngMaxAllocSize r
  have henv₀ : SessionCloneEnv G s [.alloc req₀] := by
    refine ⟨by simp, fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev; subst hev
    exact ⟨Nat.min_le_left _ _, Nat.min_le_right _ _,
      by rintro _ _ ⟨⟩, by rintro _ _ _ ⟨⟩⟩
  have hfe : FitsEvent M lim st (.alloc req₀) := (hfit [.alloc req₀] henv₀).1
  have hstep : FitsStep lim (M.stepReserve (.alloc req₀) st) (M.maxDynIvs st) (M.footprint st) :=
    hfe.2
  unfold FitsStep at hstep
  rcases hstep with ⟨_, _, hva⟩
  have hreq : req₀ ≤ M.stepReserve (.alloc req₀) st := M.req_le_stepReserve (.alloc req₀) st
  have hva' : M.stepReserve (.alloc req₀) st ≤ 2 ^ 48 := by omega
  have hmax : 2 ^ 48 < MallocngMaxAllocSize := by decide
  have hlt : min MallocngMaxAllocSize r < MallocngMaxAllocSize :=
    Nat.lt_of_le_of_lt (Nat.le_trans hreq hva') hmax
  omega

/-- Under `sessionStateReprAt` bounds and `256 * (encLen + 16) ≤ MallocngMaxAllocSize`, the
deterministic event list `segCloneEvents G s.state` satisfies `SessionCloneEnv G s`. -/
theorem sessionCloneEnv_segCloneEvents {G : SessionGhost} {s : Session (List (BitVec 8))}
    (hr : 256 * ((encSessionMem G s).length + 16) ≤ MallocngMaxAllocSize)
    (h_pend_rel : PendingRel G.pending s.pendingPreKey)
    (h_kyb_rel : KyberRel G.kyber s.pendingKyberPreKey)
    (h_alice_eq : G.alice.bytes = s.aliceBaseKey)
    (h_chains_len : G.chains.length = s.state.receiverChains.length)
    (h_loc_len : G.localIk.bytes.length = 33)
    (h_rem_len : G.remoteIk.bytes = [] ∨ G.remoteIk.bytes.length = 33) :
    SessionCloneEnv G s (segCloneEvents G s.state) := by
  let encLen := (encSessionMem G s).length
  let r := 256 * (encLen + 16)
  have henc_parts :
      (encSenderFieldMem G.sender s.state.senderChain).length +
      (((G.chains.zip s.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten).length +
      (bytesField 13 s.aliceBaseKey).length +
      (msgField 14 (s.pendingKyberPreKey.map encPendingKyber)).length +
      (bytesField 15 s.state.pqRatchetState).length ≤ encLen := by
    change _ ≤ (encSessionMem G s).length
    unfold encSessionMem
    simp only [List.length_append]
    omega
  have h33_le : 33 ≤ r := by omega
  have h32_le : 32 ≤ r := by omega
  have h_loc : BoundedRustEvs 1 r (vecCloneEvents G.localIk) :=
    boundedRustEvs_vecClone (by omega) hr
  have h_rem : BoundedRustEvs 1 r (vecCloneEvents G.remoteIk) := by
    have : G.remoteIk.bytes.length ≤ r := by
      rcases h_rem_len with h0 | h33
      · rw [h0]; exact Nat.zero_le r
      · omega
    exact boundedRustEvs_vecClone this hr
  have h_root : BoundedRustEvs 1 r (rustAllocEvents 32 1) :=
    boundedRustEvs_rustAlloc (Or.inl rfl) h32_le hr
  have h_sc : BoundedRustEvs 4 r
      (match G.sender, s.state.senderChain with
       | some gs, some sc => senderChainCloneEvents gs sc
       | _, _ => []) := by
    cases hgs : G.sender <;> cases hsc : s.state.senderChain
    · exact BoundedRustEvs.nil 4 r
    · exact BoundedRustEvs.nil 4 r
    · exact BoundedRustEvs.nil 4 r
    · rename_i gs sc
      have hsc_ge : 2 + (encChainMem (senderChainAsProtoGhost gs sc)).length ≤
          (encSenderFieldMem (some gs) (some sc)).length :=
        lenField_length_ge 6 (encChainMem (senderChainAsProtoGhost gs sc))
      have hsc_52 : 52 * (encChainMem (senderChainAsProtoGhost gs sc)).length ≤ r := by
        rw [hgs, hsc] at henc_parts; omega
      exact (boundedRustEvs_chainClone (senderChainAsProtoGhost gs sc) h32_le hsc_52 hr).1
  have h_rcs : BoundedRustEvs (1 + 2 * encLen) r
      (if s.state.receiverChains = [] then []
       else rustAllocEvents (104 * s.state.receiverChains.length) 8 ++
         (G.chains.zip s.state.receiverChains).flatMap chainCloneEvents) := by
    split
    · exact BoundedRustEvs.nil _ r
    · have hzip_len : (G.chains.zip s.state.receiverChains).length =
          s.state.receiverChains.length := by simp [h_chains_len]
      have h52_c :
          52 * (((G.chains.zip s.state.receiverChains).map
            fun gc => lenField 7 (encChainMem gc)).flatten).length ≤ r := by omega
      obtain ⟨h2len, hflat_ev⟩ :=
        encChains_bounds (G.chains.zip s.state.receiverChains) h32_le h52_c hr
      have h104_le : 104 * s.state.receiverChains.length ≤ r := by omega
      have harr_ev := boundedRustEvs_rustAlloc (n := 104 * s.state.receiverChains.length)
        (al := 8) (Or.inr rfl) h104_le hr
      exact BoundedRustEvs.mono (by omega) (Nat.le_refl r)
        (boundedRustEvs_append_same harr_ev hflat_ev)
  have h_pend : BoundedRustEvs 1 r (optTailCloneEvents G.pending) := by
    cases hp : G.pending <;> cases hsp : s.pendingPreKey
    · exact BoundedRustEvs.nil 1 r
    · rw [hp, hsp] at h_pend_rel; exact h_pend_rel.elim
    · rw [hp, hsp] at h_pend_rel; exact h_pend_rel.elim
    · rename_i g p
      rw [hp, hsp] at h_pend_rel
      have h33 : g.vec.bytes.length = 33 := h_pend_rel.2.2.2.2
      exact boundedRustEvs_vecClone (by omega) hr
  have h_kyb : BoundedRustEvs 1 r (optTailCloneEvents G.kyber) := by
    cases hk : G.kyber <;> cases hsk : s.pendingKyberPreKey
    · exact BoundedRustEvs.nil 1 r
    · rw [hk, hsk] at h_kyb_rel; exact h_kyb_rel.elim
    · rw [hk, hsk] at h_kyb_rel; exact h_kyb_rel.elim
    · rename_i g k
      rw [hk, hsk] at h_kyb_rel
      have hct_ge : k.ciphertext.length ≤ (msgField 14 (some (encPendingKyber k))).length := by
        have hlf := lenField_length_ge 14 (encPendingKyber k)
        have hbf := bytesField_length_ge 2 k.ciphertext
        unfold msgField encPendingKyber at *
        simp only [List.length_append] at *; omega
      have hlen_le : g.vec.bytes.length ≤ r := by
        rw [h_kyb_rel.1]; rw [hsk] at henc_parts; dsimp only [Option.map] at henc_parts; omega
      exact boundedRustEvs_vecClone hlen_le hr
  have h_alice : BoundedRustEvs 1 r (vecCloneEvents G.alice) := by
    have hbf := bytesField_length_ge 13 s.aliceBaseKey
    exact boundedRustEvs_vecClone (by rw [h_alice_eq]; omega) hr
  have h_pq : BoundedRustEvs 1 r
      (if s.state.pqRatchetState.length = 0 then []
       else rustAllocEvents s.state.pqRatchetState.length 1) := by
    split
    · exact BoundedRustEvs.nil 1 r
    · have hbf := bytesField_length_ge 15 s.state.pqRatchetState
      exact boundedRustEvs_rustAlloc (Or.inl rfl) (by omega) hr
  unfold SessionCloneEnv segCloneEvents
  have c12 := boundedRustEvs_append_same h_loc h_rem
  have c13 := boundedRustEvs_append_same c12 h_root
  have c14 := boundedRustEvs_append_same c13 h_sc
  have c15 := boundedRustEvs_append_same c14 h_rcs
  have c16 := boundedRustEvs_append_same c15 h_pend
  have c17 := boundedRustEvs_append_same c16 h_kyb
  have c18 := boundedRustEvs_append_same c17 h_alice
  have c19 := boundedRustEvs_append_same c18 h_pq
  have c19' := BoundedRustEvs.mono (c₂ := 4 * (encSessionMem G s).length + 64)
    (by dsimp only [encLen]; omega) (Nat.le_refl r) c19
  dsimp only [r, encLen] at c19'
  convert c19' using 1
  cases G.sender <;> cases s.state.senderChain <;>
    by_cases hrc : s.state.receiverChains = [] <;>
    simp only [hrc, ↓reduceIte, List.append_assoc]

/-- `FitsEnv M lim st (SessionCloneEnv G s)` implies both `SessionCloneEnv G s` and
`FitsEvents M lim st` on `segCloneEvents G s.state`. -/
theorem fitsEvents_segCloneEvents_of_fitsEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {G : SessionGhost} {s : Session (List (BitVec 8))}
    (hfit : FitsEnv M lim st (SessionCloneEnv G s))
    (h_pend_rel : PendingRel G.pending s.pendingPreKey)
    (h_kyb_rel : KyberRel G.kyber s.pendingKyberPreKey)
    (h_alice_eq : G.alice.bytes = s.aliceBaseKey)
    (h_chains_len : G.chains.length = s.state.receiverChains.length)
    (h_loc_len : G.localIk.bytes.length = 33)
    (h_rem_len : G.remoteIk.bytes = [] ∨ G.remoteIk.bytes.length = 33) :
    SessionCloneEnv G s (segCloneEvents G s.state) ∧
      FitsEvents M lim st (segCloneEvents G s.state) := by
  have hr := maxReq_le_mallocngMaxAllocSize_of_fitsEnv hfit
  have henv := sessionCloneEnv_segCloneEvents hr h_pend_rel h_kyb_rel h_alice_eq
    h_chains_len h_loc_len h_rem_len
  exact ⟨henv, hfit (segCloneEvents G s.state) henv⟩

/-! ## Relocatable `[LibsignalPlacement]` stepping and hook helpers (block `80`) -/

section Placed

/-- Lifts a `VmPreserved` `SepWP` basic block into `SepWPp` while preserving `LibsignalCodeLoaded`. -/
theorem sepWPp_of_sepWP_lscl_vm_sc {prog : Program} {pl : MultiPlacement}
    {mid ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      VmPreserved s sm ∧
        (VmPreserved s sm → LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp))) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h fun _ _ _ _ hclm ⟨hvm, hnext⟩ => hnext hvm hclm)

theorem sc_transport_pool {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {prog : Program} {ret : BitVec 64}
    {s_old s : State} {Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hvm : VmPreserved s_old s)
    (h : SepWPp prog ret s (A.pool lim st s ∗ Rest) Q Qp) :
    SepWPp prog ret s (A.pool lim st s_old ∗ Rest) Q Qp :=
  SepWPp.weaken_pre
    (sepConj_mono_left (Entails.of_eq (A.pool_transport lim st s_old s hvm).symm)) h

/-- Unsatisfiable panic postcondition (`onPanic = ⌜False⌝`). -/
abbrev scNoPanicPost : State → SepProp → Prop :=
  fun sf P_f => ∀ R, sf.mem ⊨ P_f ∗ R → False

theorem sc_noPanic_of_false {F : SepProp} (sf : State) (_hpan : sf.status = .Panicked) :
    scNoPanicPost sf (⌜False⌝ ∗ F) := by
  intro R hm
  rw [sepConj_assoc] at hm
  exact not_satisfies_false_sepConj hm

theorem sc_protoChainClone_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hpcc : ProtoChainCloneLocal1PlacedOk M A lim H) :
    subroutine_ok (lsProg_80 H) (blkPl_82).base
      (withLsCodeLoaded lsmpl (protoChainCloneSpec M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := lsProg_80 H)
    (subroutine_ok_withLsCodeLoaded_of_plain hpcc)

theorem sc_chainClone_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hcc : ChainCloneLocal1PlacedOk M A lim H) :
    subroutine_ok (lsProg_80 H) (blkPl_82).base
      (withLsCodeLoaded lsmpl (chainCloneSpec M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := lsProg_80 H)
    (subroutine_ok_withLsCodeLoaded_of_plain hcc)

theorem sc_senderChainClone_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hscc : SenderChainCloneLocal1PlacedOk M A lim H) :
    subroutine_ok (lsProg_80 H) (blkPl_82).base
      (withLsCodeLoaded lsmpl (senderChainCloneSpec M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := lsProg_80 H)
    (subroutine_ok_withLsCodeLoaded_of_plain hscc)

/-- Budget-threaded external hook bundle for `SessionStructure::clone` (block `80`). -/
structure ScExternKit_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop where
  shim : subroutine_ok (lsProg_80 H) (lsρ lsRustNoAllocShimSym) rustAllocShimVmSpec
  alloc : subroutine_ok (lsProg_80 H) (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false)
  memcpy : subroutine_ok (lsProg_80 H) (lsρ lsMemcpySym) allocMemcpyVmSpec

theorem ScExternKit_placed.allocNoOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hkit : ScExternKit_placed A lim H) :
    subroutine_ok (lsProg_80 H) (lsρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
  subroutine_ok_allocNoOom_of_budget hkit.alloc

theorem scExternKit_placed_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    ScExternKit_placed A lim H :=
  ⟨ls_hook_ok_of_mem hshim, ls_hook_ok_of_mem halloc, ls_hook_ok_of_mem hmemcpy⟩

theorem scExternKit_placed_of_serializeHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h : PlacedSerializeHooks M A H) :
    ScExternKit_placed A lim H :=
  scExternKit_placed_of_hooks h.shim (h.alloc lim) h.memcpy

end Placed

end LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.BaseBudget
