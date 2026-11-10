/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.FromPb
public import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbLoopClPlaced
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbDecodes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Code-Loaded Proof of `<spqr::chain::Chain>::from_pb` (Block `364`)

Code-loaded `[LibsignalPlacement]` loop and subroutine contracts (`fromPb_loop_step_cl_placed`,
`fromPb_loop_cl_placed`, `chain_from_pb_body_cl_placed`, `chain_from_pb_cl_placed_ok`) for
`<spqr::chain::Chain>::from_pb` (Block `364`), with `withLsCodeLoaded lsmpl` contracts on
cross-block drop-glue callees (Blocks `287` and `288`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.CodeLayout
open FromPbDecodes

set_option maxRecDepth 800000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm]
private theorem neg33_eq_mask : (-33#64 : BitVec 64) = 0xffffffffffffffdf#64 := rfl

set_option maxHeartbeats 800000 in
theorem fromPb_loop_step_ok_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec A)))
    (x : ChainFromPbCall) (s0 s : State) (dir : Direction)
    (prefG : List ChainEpochGhost) (pref : List ChainEpoch) (prefPB : List ChainEpochPB)
    (curG : ChainEpochPBGhost) (sendPb recvPb : EpochDirectionPB)
    (restG : List ChainEpochPBGhost) (restPB : List ChainEpochPB) (sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hdir : Direction.fromI32? x.pb.direction = some dir) (hdir_i32 : dir.toI32 = x.pb.direction)
    (hpref_ok : Chain.linksFromPb prefPB = .ok pref)
    (hprefG_len : prefG.length = pref.length) (hpref_len : prefPB.length = pref.length)
    (hrestG_len : restG.length = restPB.length)
    (hsplit_links : x.pb.links = prefPB ++ { send := some sendPb, recv := some recvPb } :: restPB)
    (hsn1 : sendPb.next.length ≤ curG.send.next.cap.toNat)
    (hsn2 : curG.send.next.cap.toNat < 2 ^ 63) (hsn3 : curG.send.next.ptr ≠ 0)
    (hsp1 : sendPb.prev.length ≤ curG.send.prev.cap.toNat)
    (hsp2 : curG.send.prev.cap.toNat < 2 ^ 63) (hsp3 : curG.send.prev.ptr ≠ 0)
    (hrn1 : recvPb.next.length ≤ curG.recv.next.cap.toNat)
    (hrn2 : curG.recv.next.cap.toNat < 2 ^ 63) (hrn3 : curG.recv.next.ptr ≠ 0)
    (hrp1 : recvPb.prev.length ≤ curG.recv.prev.cap.toNat)
    (hrp2 : curG.recv.prev.cap.toNat < 2 ^ 63) (hrp3 : curG.recv.prev.ptr ≠ 0)
    (hs_tst : (BitVec.ofNat 64 sendPb.next.length &&& 0xffffffffffffffdf#64 == 0#64) = true)
    (hr_tst : (BitVec.ofNat 64 recvPb.next.length &&& 0xffffffffffffffdf#64 == 0#64) = true)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 136#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (x.pb.links.length * 112))
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (pref.length * 112)) :
    let cur := x.gPb.linksPtr + BitVec.ofNat 64 (pref.length * 112)
    let curEp := mkChainEpochFromPb sendPb recvPb
    let curEpG := toChainEpochGhost curG
    SepWP ((blkPC_364).rebase (blkPl_364).base H)
      (if restPB = [] then s0.readReg64 .lr
       else (blkPl_364).base + 136#64) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (prefG.zip pref) ∗
        epochDirPBCellsAt cur curG.send sendPb ∗
        vecU8BufAt A curG.send.next.cap curG.send.next.ptr sendPb.next ∗
        vecU8BufAt A curG.send.prev.cap curG.send.prev.ptr sendPb.prev ∗
        recvDirPBCellsAt56 cur curG.recv recvPb ∗
        vecU8BufAt A curG.recv.next.cap curG.recv.next.ptr recvPb.next ∗
        vecU8BufAt A curG.recv.prev.cap curG.recv.prev.ptr recvPb.prev ∗
        arrayAt (chainEpochPBAt A) 112 (x.gPb.linksPtr + BitVec.ofNat 64 ((pref.length + 1) * 112))
          (restG.zip restPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (if restPB = [] then
         fromPbRetPost A x s0
       else
         fun sm Pm =>
           (Pm ⊢ memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
             arrayAt (chainEpochAt A) 112 x.gPb.linksPtr
               ((prefG ++ [curEpG]).zip (pref ++ [curEp])) ∗
             arrayAt (chainEpochPBAt A) 112
               (x.gPb.linksPtr + BitVec.ofNat 64 ((pref ++ [curEp]).length * 112))
               (restG.zip restPB) ∗
             linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
             vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
             loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
             stackAt (s0.sp - 192#64) chainFromPbSubStack) ∧
           sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
           sm.readReg64 .fp = s0.sp - 96#64 ∧
           sm.readReg64 .x8 = BitVec.ofNat 64 (x.pb.links.length * 112) ∧
           sm.readReg64 .x11 = x.gPb.linksPtr ∧
           sm.readReg64 .x25 = BitVec.ofNat 64 ((pref ++ [curEp]).length * 112) ∧
           Chain.linksFromPb (prefPB ++ [{ send := some sendPb, recv := some recvPb }]) =
             .ok (pref ++ [curEp])) := by
  intro cur curEp curEpG
  dsimp only [cur] at *
  have hjoin_ok := @fromPb_join_ok_cl_placed _ A H hdealloc hchain_slice hproto_slice x s0
  have htotal : pref.length + 1 + restPB.length = x.pb.links.length := by
    rw [hsplit_links, List.length_append, List.length_cons, hpref_len]; omega
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hsn_ne : (curG.send.next.cap + 1#64 == 0#64) = false := add_one_beq_zero_of_lt_pow63 hsn2
  have hrn_ne : (curG.recv.next.cap + 1#64 == 0#64) = false := add_one_beq_zero_of_lt_pow63 hrn2
  have hrepack := repack_cur_chainEpochAt A cur curG sendPb recvPb
    hsn1 hsn2 hsn3 hsp1 hsp2 hsp3 hrn1 hrn2 hrn3 hrp1 hrp2 hrp3
  have hsnoc := arrayAt_chainEpochAt_snoc A x.gPb.linksPtr prefG pref curEpG curEp hprefG_len
  have hpref_append_len : (pref ++ [curEp]).length = pref.length + 1 := by simp
  have hsend_ok : ChainEpochDirection.fromPb sendPb =
      .ok { ctr := sendPb.ctr, next := sendPb.next, prev := { data := sendPb.prev } } :=
    ced_fromPb_of_tst_true (lt_of_le_of_lt hsn1 hsn2) hs_tst
  have hrecv_ok : ChainEpochDirection.fromPb recvPb =
      .ok { ctr := recvPb.ctr, next := recvPb.next, prev := { data := recvPb.prev } } :=
    ced_fromPb_of_tst_true (lt_of_le_of_lt hrn1 hrn2) hr_tst
  have hpref_next_ok :
      Chain.linksFromPb (prefPB ++ [{ send := some sendPb, recv := some recvPb }]) =
        .ok (pref ++ [curEp]) := by
    rw [linksFromPb_append_of_ok hpref_ok,
        linksFromPb_cons_ok sendPb recvPb _ _ [] hsend_ok hrecv_ok]
    rfl
  have hlinks_ok_of_nil : restPB = [] → Chain.linksFromPb x.pb.links = .ok (pref ++ [curEp]) := by
    rintro rfl; rw [hsplit_links]; exact hpref_next_ok
  clear hsplit_links
  try dsimp only [BitVec.ofNat_eq_ofNat] at hjoin_ok hpc ⊢
  by_cases hrest_nil : restPB = []
  · have hlinks_ok : Chain.linksFromPb x.pb.links = .ok (pref ++ [curEp]) :=
      hlinks_ok_of_nil hrest_nil
    subst hrest_nil
    have hrestG_nil : restG = [] := List.eq_nil_of_length_eq_zero (by simpa using hrestG_len)
    subst hrestG_nil
    simp only [↓reduceIte, List.length_nil, Nat.add_zero] at htotal ⊢
    have hcmp_eq : BitVec.ofNat 64 ((pref.length + 1) * 112) =
        BitVec.ofNat 64 (x.pb.links.length * 112) := by rw [htotal]
    have hconvG_len : (prefG ++ [curEpG]).length = (pref ++ [curEp]).length := by
      simp [hprefG_len]
    have hconv_pb_len : (pref ++ [curEp]).length = x.pb.links.length := by
      rw [hpref_append_len, htotal]
    refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 792#64)
      (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr ((prefG ++ [curEpG]).zip (pref ++ [curEp])) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧
        sm.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 ((pref ++ [curEp]).length * 112) ∧
        sm.readReg64 .x11 = x.gPb.linksPtr ∧ sm.readReg64 .x19 = 1#64 ∧
        sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 ((pref ++ [curEp]).length * 112) ∧
        sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
        sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 ((pref ++ [curEp]).length * 112) ∧
        sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x25 = x.pbPtr) ?_ ?_
    · simp only [List.zip_nil_right, arrayAt, emp_sepConj]
      unfold epochDirPBCellsAt recvDirPBCellsAt56 loopScratchAt
      wp_steps
      refine SepWP.focus_weaken hrepack (by
        unfold epochDirPBCellsAt recvDirPBCellsAt56; dsimp only [cur, curEp, curEpG]; sep_focus) ?_
      refine SepWP.focus_weaken hsnoc (by dsimp only [curEp, curEpG]; sep_focus) ?_
      refine SepWP.focus_weaken (loopScratchAt_entails_joinScratchAt s0 x sp0_val)
        (by unfold loopScratchAt; sep_focus) ?_
      rw [hconv_pb_len]
      wp_done
    · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx0_1, hx11_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1⟩
      exact hjoin_ok s1 dir (prefG ++ [curEpG]) (pref ++ [curEp]) sp0_val hcl1 hsp0_align
        hdir hdir_i32 hlinks_ok hconvG_len hconv_pb_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne
        hpc1 hrun1 hsp1 htr1 hfp1 hx0_1 hx11_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1
  · simp only [hrest_nil, ↓reduceIte]
    have hpos : restPB.length > 0 := List.length_pos_iff.mpr hrest_nil
    have hne_len : x.pb.links.length ≠ pref.length + 1 := by omega
    have h1_lt : (pref.length + 1) * 112 < 2 ^ 63 := by
      have : (pref.length + 1) * 112 ≤ x.pb.links.length * 112 :=
        Nat.mul_le_mul_right 112 (by omega)
      omega
    have hcmp_ne : (BitVec.ofNat 64 (x.pb.links.length * 112) ==
        BitVec.ofNat 64 ((pref.length + 1) * 112)) = false :=
      ofNat_mul_112_beq_false hne_len hlen_lt h1_lt
    have hcmp_bne : (BitVec.ofNat 64 (x.pb.links.length * 112) !=
        BitVec.ofNat 64 ((pref.length + 1) * 112)) = true := by
      simp [bne, hcmp_ne]
    unfold epochDirPBCellsAt recvDirPBCellsAt56
    wp_steps
    refine SepWP.focus_weaken hrepack (by
      unfold epochDirPBCellsAt recvDirPBCellsAt56; dsimp only [cur, curEp, curEpG]; sep_focus) ?_
    refine SepWP.focus_weaken hsnoc (by dsimp only [curEp, curEpG]; sep_focus) ?_
    rw [hpref_append_len]
    wp_done

set_option maxHeartbeats 800000 in
theorem fromPb_loop_step_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec A)))
    (x : ChainFromPbCall) (s0 s : State) (dir : Direction)
    (prefG : List ChainEpochGhost) (pref : List ChainEpoch) (prefPB : List ChainEpochPB)
    (curG : ChainEpochPBGhost) (curPB : ChainEpochPB)
    (restG : List ChainEpochPBGhost) (restPB : List ChainEpochPB) (sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hdir : Direction.fromI32? x.pb.direction = some dir) (hdir_i32 : dir.toI32 = x.pb.direction)
    (hpref_ok : Chain.linksFromPb prefPB = .ok pref)
    (hprefG_len : prefG.length = pref.length) (hpref_len : prefPB.length = pref.length)
    (hrestG_len : restG.length = restPB.length)
    (hsplit_links : x.pb.links = prefPB ++ curPB :: restPB)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 136#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (x.pb.links.length * 112))
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (pref.length * 112)) :
    let cur := x.gPb.linksPtr + BitVec.ofNat 64 (pref.length * 112)
    SepWP ((blkPC_364).rebase (blkPl_364).base H)
      (match curPB.send, curPB.recv with
       | some sendPb, some recvPb =>
         if (BitVec.ofNat 64 sendPb.next.length &&& 0xffffffffffffffdf#64 == 0#64) = true ∧
            (BitVec.ofNat 64 recvPb.next.length &&& 0xffffffffffffffdf#64 == 0#64) = true ∧
            restPB ≠ [] then
           (blkPl_364).base + 136#64
         else
           s0.readReg64 .lr
       | _, _ => s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (prefG.zip pref) ∗
        chainEpochPBAt A (curG, curPB) cur ∗
        arrayAt (chainEpochPBAt A) 112 (x.gPb.linksPtr + BitVec.ofNat 64 ((pref.length + 1) * 112))
          (restG.zip restPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (match curPB.send, curPB.recv with
       | some sendPb, some recvPb =>
         if (BitVec.ofNat 64 sendPb.next.length &&& 0xffffffffffffffdf#64 == 0#64) = true ∧
            (BitVec.ofNat 64 recvPb.next.length &&& 0xffffffffffffffdf#64 == 0#64) = true ∧
            restPB ≠ [] then
           let curEp := mkChainEpochFromPb sendPb recvPb
           let curEpG := toChainEpochGhost curG
           fun sm Pm =>
             (Pm ⊢ memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
               arrayAt (chainEpochAt A) 112 x.gPb.linksPtr
                 ((prefG ++ [curEpG]).zip (pref ++ [curEp])) ∗
               arrayAt (chainEpochPBAt A) 112
                 (x.gPb.linksPtr + BitVec.ofNat 64 ((pref ++ [curEp]).length * 112))
                 (restG.zip restPB) ∗
               linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
               vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
               loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
               stackAt (s0.sp - 192#64) chainFromPbSubStack) ∧
             sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
             sm.readReg64 .fp = s0.sp - 96#64 ∧
             sm.readReg64 .x8 = BitVec.ofNat 64 (x.pb.links.length * 112) ∧
             sm.readReg64 .x11 = x.gPb.linksPtr ∧
             sm.readReg64 .x25 = BitVec.ofNat 64 ((pref ++ [curEp]).length * 112) ∧
             Chain.linksFromPb (prefPB ++ [curPB]) = .ok (pref ++ [curEp])
         else
           fromPbRetPost A x s0
       | _, _ => fromPbRetPost A x s0) := by
  intro cur
  dsimp only [cur] at *
  have htotal : pref.length + 1 + restPB.length = x.pb.links.length := by
    rw [hsplit_links, List.length_append, List.length_cons, hpref_len]; omega
  dsimp only [chainEpochPBAt, CryptoVerification.SpqrV1.ProtoRepr.chainEpochPBPinnedAt]
  change SepWP _ _ _
    (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (prefG.zip pref) ∗
      (optEpochDirectionPBAt A curG.send cur curPB.send ∗
        optEpochDirectionPBAt A curG.recv (cur + 56#64) curPB.recv) ∗
      arrayAt (chainEpochPBAt A) 112 (x.gPb.linksPtr + BitVec.ofNat 64 ((pref.length + 1) * 112))
        (restG.zip restPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
      loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack) _
  cases hsend : curPB.send with
  | none =>
    cases hrecv : curPB.recv with
    | none =>
      have hlinks_err : Chain.linksFromPb x.pb.links = .error .stateDecode := by
        rw [hsplit_links, linksFromPb_append_of_ok hpref_ok]
        have hcur : curPB = { send := none, recv := none } := by cases curPB; congr
        rw [hcur, linksFromPb_cons_send_none]
      have hfromPb_err : Chain.fromPb x.pb = .error .stateDecode :=
        chainFromPb_of_links_err hdir hlinks_err
      have herr520 := @fromPb_loop_err_520_none_cl_placed _ A H hdealloc hchain_slice hproto_slice x s0
      rw [optEpochDirectionPBAt_none_unpack A curG.send cur,
          recv_none_unpack_at_56 A curG.recv cur]
      wp_pull_exists
      try dsimp only [BitVec.ofNat_eq_ofNat] at herr520 hpc ⊢
      refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 520#64)
        (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
          arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (prefG.zip pref) ∗
          memRegion cur 112 ∗
          arrayAt (chainEpochPBAt A) 112 (x.gPb.linksPtr + BitVec.ofNat 64 ((pref.length + 1) * 112))
            (restG.zip restPB) ∗
          linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
          vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
          loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 192#64) chainFromPbSubStack)
        (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
          sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
          sm.readReg64 .x20 = 0xffffffffffffffff#64 ∧ sm.readReg64 .x23 = cur) ?_ ?_
      · wp_steps
        refine SepWP.focus_weaken
          (sendNone_recvNone_entails_memRegion_112 cur _ _ _ _ _ _ _ _ _ _)
          (by dsimp only [cur]; sep_focus) ?_
        wp_done
      · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx11_1, hx20_1, hx23_1⟩
        exact herr520 s1 prefG pref restG restPB sp0_val hcl1 hsp0_align hfromPb_err
          hprefG_len hrestG_len htotal hl_le hl_lt hl_ne hn_le hn_lt hn_ne
          hpc1 hrun1 hsp1 htr1 hfp1 hx11_1 hx20_1 hx23_1
    | some recvPb =>
      have hlinks_err : Chain.linksFromPb x.pb.links = .error .stateDecode := by
        rw [hsplit_links, linksFromPb_append_of_ok hpref_ok]
        have hcur : curPB = { send := none, recv := some recvPb } := by cases curPB; congr
        rw [hcur, linksFromPb_cons_send_none]
      have hfromPb_err : Chain.fromPb x.pb = .error .stateDecode :=
        chainFromPb_of_links_err hdir hlinks_err
      have herr520 := @fromPb_loop_err_520_some_cl_placed _ A H hdealloc hchain_slice hproto_slice x s0
      rw [optEpochDirectionPBAt_none_unpack A curG.send cur]
      wp_pull_exists
      refine SepWP.focus_weaken
        (optEpochDirectionPBAt_some_unpack A curG.recv (cur + 56#64) recvPb) (by sep_focus) ?_
      wp_focus_pure
      rintro ⟨hrn1, hrn2, hrn3, hrp1, hrp2, hrp3⟩
      rw [epochDirPBCellsAt_56_eq cur curG.recv recvPb]
      try dsimp only [BitVec.ofNat_eq_ofNat] at herr520 hpc ⊢
      refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 520#64)
        (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
          arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (prefG.zip pref) ∗
          memRegion cur 112 ∗
          vecCapPtrDealloc A curG.recv.next.cap curG.recv.next.ptr ∗
          vecCapPtrDealloc A curG.recv.prev.cap curG.recv.prev.ptr ∗
          arrayAt (chainEpochPBAt A) 112 (x.gPb.linksPtr + BitVec.ofNat 64 ((pref.length + 1) * 112))
            (restG.zip restPB) ∗
          linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
          vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
          loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 192#64) chainFromPbSubStack)
        (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
          sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
          sm.readReg64 .x12 = curG.recv.prev.ptr ∧ sm.readReg64 .x19 = curG.recv.next.ptr ∧
          sm.readReg64 .x20 = curG.recv.next.cap ∧ sm.readReg64 .x23 = cur ∧
          sm.readReg64 .x26 = curG.recv.prev.cap) ?_ ?_
      · unfold recvDirPBCellsAt56
        wp_steps
        refine SepWP.focus_weaken
          (sendNone_recvSome_entails_err520 A cur _ _ _ _ _ curG.recv recvPb hrn1 hrn2 hrp1 hrp2)
          (by unfold recvDirPBCellsAt56; dsimp only [cur]; sep_focus) ?_
        wp_done
      · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx11_1, hx12_1, hx19_1, hx20_1, hx23_1, hx26_1⟩
        exact herr520 s1 prefG pref restG restPB
          curG.recv.next.cap curG.recv.next.ptr curG.recv.prev.cap curG.recv.prev.ptr sp0_val hcl1
          hsp0_align hfromPb_err hprefG_len hrestG_len htotal
          hl_le hl_lt hl_ne hn_le hn_lt hn_ne hrn2 hrn3 hrp2 hrp3
          hpc1 hrun1 hsp1 htr1 hfp1 hx11_1 hx12_1 hx19_1 hx20_1 hx23_1 hx26_1
  | some sendPb =>
    refine SepWP.focus_weaken
      (optEpochDirectionPBAt_some_unpack A curG.send cur sendPb) (by sep_focus) ?_
    wp_focus_pure
    rintro ⟨hsn1, hsn2, hsn3, hsp1, hsp2, hsp3⟩
    have hsn_ne : (curG.send.next.cap + 1#64 == 0#64) = false := add_one_beq_zero_of_lt_pow63 hsn2
    cases hrecv : curPB.recv with
    | none =>
      rw [recv_none_unpack_at_56 A curG.recv cur]
      wp_pull_exists
      by_cases hs_tst : (BitVec.ofNat 64 sendPb.next.length &&& 0xffffffffffffffdf#64 == 0#64) = true
      · have hsend_ok : ChainEpochDirection.fromPb sendPb =
            .ok { ctr := sendPb.ctr, next := sendPb.next, prev := { data := sendPb.prev } } :=
          ced_fromPb_of_tst_true (lt_of_le_of_lt hsn1 hsn2) hs_tst
        have hlinks_err : Chain.linksFromPb x.pb.links = .error .stateDecode := by
          rw [hsplit_links, linksFromPb_append_of_ok hpref_ok]
          have hcur : curPB = { send := some sendPb, recv := none } := by cases curPB; congr
          rw [hcur, linksFromPb_cons_recv_none sendPb _ restPB hsend_ok]
        have hfromPb_err : Chain.fromPb x.pb = .error .stateDecode :=
          chainFromPb_of_links_err hdir hlinks_err
        have herr380 := @fromPb_loop_err_380_cl_placed _ A H hdealloc hchain_slice hproto_slice x s0
        try dsimp only [BitVec.ofNat_eq_ofNat] at herr380 hpc ⊢
        refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 380#64)
          (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
            arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (prefG.zip pref) ∗
            memRegion cur 112 ∗
            vecCapPtrDealloc A curG.send.next.cap curG.send.next.ptr ∗
            vecCapPtrDealloc A curG.send.prev.cap curG.send.prev.ptr ∗
            arrayAt (chainEpochPBAt A) 112 (x.gPb.linksPtr + BitVec.ofNat 64 ((pref.length + 1) * 112))
              (restG.zip restPB) ∗
            linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
            vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
            loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
            sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
            sm.readReg64 .x21 = curG.send.next.ptr ∧ sm.readReg64 .x24 = curG.send.next.cap ∧
            sm.readReg64 .x25 = BitVec.ofNat 64 (pref.length * 112) ∧
            sm.readReg64 .x27 = curG.send.prev.cap ∧ sm.readReg64 .x28 = curG.send.prev.ptr) ?_ ?_
        · unfold epochDirPBCellsAt
          wp_steps
          refine SepWP.focus_weaken
            (sendSome_recvNone_entails_err A cur curG.send sendPb _ _ _ _ _ hsn1 hsn2 hsp1 hsp2)
            (by unfold epochDirPBCellsAt; dsimp only [cur]; sep_focus) ?_
          wp_done
        · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx11_1, hx21_1, hx24_1, hx25_1, hx27_1, hx28_1⟩
          exact herr380 s1 prefG pref restG restPB
            curG.send.next.cap curG.send.next.ptr curG.send.prev.cap curG.send.prev.ptr sp0_val hcl1
            hsp0_align hfromPb_err hprefG_len hrestG_len htotal
            hl_le hl_lt hl_ne hn_le hn_lt hn_ne hsn2 hsn3 hsp2 hsp3
            hpc1 hrun1 hsp1 htr1 hfp1 hx11_1 hx21_1 hx24_1 hx25_1 hx27_1 hx28_1
      · have hs_tst_f : (BitVec.ofNat 64 sendPb.next.length &&& 0xffffffffffffffdf#64 == 0#64) = false :=
          Bool.eq_false_iff.mpr hs_tst
        have hsend_err : ChainEpochDirection.fromPb sendPb = .error .stateDecode :=
          ced_fromPb_of_tst_false (lt_of_le_of_lt hsn1 hsn2) hs_tst_f
        have hlinks_err : Chain.linksFromPb x.pb.links = .error .stateDecode := by
          rw [hsplit_links, linksFromPb_append_of_ok hpref_ok]
          have hcur : curPB = { send := some sendPb, recv := none } := by cases curPB; congr
          rw [hcur, linksFromPb_cons_send_err sendPb none restPB hsend_err]
        have hfromPb_err : Chain.fromPb x.pb = .error .stateDecode :=
          chainFromPb_of_links_err hdir hlinks_err
        have herr452 := @fromPb_loop_err_452_none_cl_placed _ A H hdealloc hchain_slice hproto_slice x s0
        try dsimp only [BitVec.ofNat_eq_ofNat] at herr452 hpc ⊢
        refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 452#64)
          (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
            arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (prefG.zip pref) ∗
            memRegion cur 112 ∗
            vecCapPtrDealloc A curG.send.next.cap curG.send.next.ptr ∗
            vecCapPtrDealloc A curG.send.prev.cap curG.send.prev.ptr ∗
            arrayAt (chainEpochPBAt A) 112 (x.gPb.linksPtr + BitVec.ofNat 64 ((pref.length + 1) * 112))
              (restG.zip restPB) ∗
            linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
            vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
            loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
            sm.readReg64 .fp = s0.sp - 96#64 ∧
            sm.readReg64 .x9 = BitVec.ofNat 64 sendPb.next.length ∧
            sm.readReg64 .x11 = x.gPb.linksPtr ∧ sm.readReg64 .x20 = 0xffffffffffffffff#64 ∧
            sm.readReg64 .x21 = curG.send.next.ptr ∧ sm.readReg64 .x23 = cur ∧
            sm.readReg64 .x24 = curG.send.next.cap ∧ sm.readReg64 .x27 = curG.send.prev.cap ∧
            sm.readReg64 .x28 = curG.send.prev.ptr) ?_ ?_
        · unfold epochDirPBCellsAt
          wp_steps
          refine SepWP.focus_weaken
            (sendSome_recvNone_entails_err A cur curG.send sendPb _ _ _ _ _ hsn1 hsn2 hsp1 hsp2)
            (by unfold epochDirPBCellsAt; dsimp only [cur]; sep_focus) ?_
          wp_done
        · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx9_1, hx11_1, hx20_1, hx21_1, hx23_1, hx24_1, hx27_1, hx28_1⟩
          exact herr452 s1 prefG pref restG restPB
            curG.send.next.cap curG.send.next.ptr curG.send.prev.cap curG.send.prev.ptr
            (BitVec.ofNat 64 sendPb.next.length) sp0_val hcl1
            hsp0_align hfromPb_err hprefG_len hrestG_len htotal
            hl_le hl_lt hl_ne hn_le hn_lt hn_ne hsn2 hsn3 hsp2 hsp3
            hpc1 hrun1 hsp1 htr1 hfp1 hx9_1 hx11_1 hx20_1 hx21_1 hx23_1 hx24_1 hx27_1 hx28_1
    | some recvPb =>
      refine SepWP.focus_weaken
        (optEpochDirectionPBAt_some_unpack A curG.recv (cur + 56#64) recvPb) (by sep_focus) ?_
      wp_focus_pure
      rintro ⟨hrn1, hrn2, hrn3, hrp1, hrp2, hrp3⟩
      rw [epochDirPBCellsAt_56_eq cur curG.recv recvPb]
      have hrn_ne : (curG.recv.next.cap + 1#64 == 0#64) = false := add_one_beq_zero_of_lt_pow63 hrn2
      by_cases hs_tst : (BitVec.ofNat 64 sendPb.next.length &&& 0xffffffffffffffdf#64 == 0#64) = true
      · by_cases hr_tst : (BitVec.ofNat 64 recvPb.next.length &&& 0xffffffffffffffdf#64 == 0#64) = true
        · have hcur : curPB = { send := some sendPb, recv := some recvPb } := by cases curPB; congr
          have hsplit' : x.pb.links = prefPB ++ { send := some sendPb, recv := some recvPb } :: restPB := by
            rw [← hcur]; exact hsplit_links
          have hok := fromPb_loop_step_ok_cl_placed hdealloc hchain_slice hproto_slice x s0 s dir prefG pref prefPB
            curG sendPb recvPb restG restPB sp0_val hcl hsp0_align hdir hdir_i32
            hpref_ok hprefG_len hpref_len hrestG_len hsplit'
            hsn1 hsn2 hsn3 hsp1 hsp2 hsp3 hrn1 hrn2 hrn3 hrp1 hrp2 hrp3
            hs_tst hr_tst hl_le hl_lt hl_ne hn_le hn_lt hn_ne
            hpc hrun hsp htr hfp hx8 hx11 hx25
          by_cases hrest_nil : restPB = []
          · simp only [hs_tst, hr_tst, hrest_nil, ne_eq, not_true_eq_false, and_false, ↓reduceIte] at hok ⊢
            exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hok
          · simp only [hs_tst, hr_tst, hrest_nil, ne_eq, not_false_eq_true, and_self, ↓reduceIte,
              ← hcur] at hok ⊢
            exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hok
        · have hr_tst_f : (BitVec.ofNat 64 recvPb.next.length &&& 0xffffffffffffffdf#64 == 0#64) = false :=
            Bool.eq_false_iff.mpr hr_tst
          simp only [hs_tst, hr_tst_f, Bool.false_eq_true, false_and, and_false, ↓reduceIte]
          have hsend_ok : ChainEpochDirection.fromPb sendPb =
              .ok { ctr := sendPb.ctr, next := sendPb.next, prev := { data := sendPb.prev } } :=
            ced_fromPb_of_tst_true (lt_of_le_of_lt hsn1 hsn2) hs_tst
          have hrecv_err : ChainEpochDirection.fromPb recvPb = .error .stateDecode :=
            ced_fromPb_of_tst_false (lt_of_le_of_lt hrn1 hrn2) hr_tst_f
          have hlinks_err : Chain.linksFromPb x.pb.links = .error .stateDecode := by
            rw [hsplit_links, linksFromPb_append_of_ok hpref_ok]
            have hcur : curPB = { send := some sendPb, recv := some recvPb } := by cases curPB; congr
            rw [hcur, linksFromPb_cons_recv_err sendPb recvPb _ restPB hsend_ok hrecv_err]
          have hfromPb_err : Chain.fromPb x.pb = .error .stateDecode :=
            chainFromPb_of_links_err hdir hlinks_err
          have herr644 := @fromPb_loop_err_644_cl_placed _ A H hdealloc hchain_slice hproto_slice x s0
          try dsimp only [BitVec.ofNat_eq_ofNat] at herr644 hpc ⊢
          refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 644#64)
            (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
              arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (prefG.zip pref) ∗
              memRegion cur 112 ∗
              vecCapPtrDealloc A curG.send.next.cap curG.send.next.ptr ∗
              vecCapPtrDealloc A curG.send.prev.cap curG.send.prev.ptr ∗
              vecCapPtrDealloc A curG.recv.next.cap curG.recv.next.ptr ∗
              vecCapPtrDealloc A curG.recv.prev.cap curG.recv.prev.ptr ∗
              arrayAt (chainEpochPBAt A) 112 (x.gPb.linksPtr + BitVec.ofNat 64 ((pref.length + 1) * 112))
                (restG.zip restPB) ∗
              linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
              vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
              loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
              stackAt (s0.sp - 192#64) chainFromPbSubStack)
            (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
              sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
              sm.readReg64 .x12 = curG.recv.prev.ptr ∧ sm.readReg64 .x19 = curG.recv.next.ptr ∧
              sm.readReg64 .x20 = curG.recv.next.cap ∧ sm.readReg64 .x21 = curG.send.next.ptr ∧
              sm.readReg64 .x22 = BitVec.ofNat 64 recvPb.next.length ∧
              sm.readReg64 .x24 = curG.send.next.cap ∧
              sm.readReg64 .x25 = BitVec.ofNat 64 (pref.length * 112) ∧
              sm.readReg64 .x26 = curG.recv.prev.cap ∧ sm.readReg64 .x27 = curG.send.prev.cap ∧
              sm.readReg64 .x28 = curG.send.prev.ptr) ?_ ?_
          · unfold epochDirPBCellsAt recvDirPBCellsAt56
            wp_steps
            refine SepWP.focus_weaken
              (sendSome_recvSome_entails_err A cur curG.send curG.recv sendPb recvPb
                hsn1 hsn2 hsp1 hsp2 hrn1 hrn2 hrp1 hrp2)
              (by unfold epochDirPBCellsAt recvDirPBCellsAt56; dsimp only [cur]; sep_focus) ?_
            wp_done
          · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx11_1, hx12_1, hx19_1, hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1⟩
            exact herr644 s1 prefG pref restG restPB
              curG.send.next.cap curG.send.next.ptr curG.send.prev.cap curG.send.prev.ptr
              curG.recv.next.cap curG.recv.next.ptr curG.recv.prev.cap curG.recv.prev.ptr
              (BitVec.ofNat 64 recvPb.next.length) sp0_val hcl1
              hsp0_align hfromPb_err hprefG_len hrestG_len htotal
              hl_le hl_lt hl_ne hn_le hn_lt hn_ne hsn2 hsn3 hsp2 hsp3 hrn2 hrn3 hrp2 hrp3
              hpc1 hrun1 hsp1 htr1 hfp1 hx11_1 hx12_1 hx19_1 hx20_1 hx21_1 hx22_1
              hx24_1 hx25_1 hx26_1 hx27_1 hx28_1
      · have hs_tst_f : (BitVec.ofNat 64 sendPb.next.length &&& 0xffffffffffffffdf#64 == 0#64) = false :=
          Bool.eq_false_iff.mpr hs_tst
        simp only [hs_tst_f, Bool.false_eq_true, false_and, ↓reduceIte]
        have hsend_err : ChainEpochDirection.fromPb sendPb = .error .stateDecode :=
          ced_fromPb_of_tst_false (lt_of_le_of_lt hsn1 hsn2) hs_tst_f
        have hlinks_err : Chain.linksFromPb x.pb.links = .error .stateDecode := by
          rw [hsplit_links, linksFromPb_append_of_ok hpref_ok]
          have hcur : curPB = { send := some sendPb, recv := some recvPb } := by cases curPB; congr
          rw [hcur, linksFromPb_cons_send_err sendPb (some recvPb) restPB hsend_err]
        have hfromPb_err : Chain.fromPb x.pb = .error .stateDecode :=
          chainFromPb_of_links_err hdir hlinks_err
        have herr452 := @fromPb_loop_err_452_some_cl_placed _ A H hdealloc hchain_slice hproto_slice x s0
        try dsimp only [BitVec.ofNat_eq_ofNat] at herr452 hpc ⊢
        refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 452#64)
          (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
            arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (prefG.zip pref) ∗
            memRegion cur 112 ∗
            vecCapPtrDealloc A curG.send.next.cap curG.send.next.ptr ∗
            vecCapPtrDealloc A curG.send.prev.cap curG.send.prev.ptr ∗
            vecCapPtrDealloc A curG.recv.next.cap curG.recv.next.ptr ∗
            vecCapPtrDealloc A curG.recv.prev.cap curG.recv.prev.ptr ∗
            arrayAt (chainEpochPBAt A) 112 (x.gPb.linksPtr + BitVec.ofNat 64 ((pref.length + 1) * 112))
              (restG.zip restPB) ∗
            linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
            vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
            loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
            sm.readReg64 .fp = s0.sp - 96#64 ∧
            sm.readReg64 .x9 = BitVec.ofNat 64 sendPb.next.length ∧
            sm.readReg64 .x11 = x.gPb.linksPtr ∧ sm.readReg64 .x12 = curG.recv.prev.ptr ∧
            sm.readReg64 .x19 = curG.recv.next.ptr ∧ sm.readReg64 .x20 = curG.recv.next.cap ∧
            sm.readReg64 .x21 = curG.send.next.ptr ∧ sm.readReg64 .x23 = cur ∧
            sm.readReg64 .x24 = curG.send.next.cap ∧ sm.readReg64 .x26 = curG.recv.prev.cap ∧
            sm.readReg64 .x27 = curG.send.prev.cap ∧ sm.readReg64 .x28 = curG.send.prev.ptr) ?_ ?_
        · unfold epochDirPBCellsAt recvDirPBCellsAt56
          wp_steps
          refine SepWP.focus_weaken
            (sendSome_recvSome_entails_err A cur curG.send curG.recv sendPb recvPb
              hsn1 hsn2 hsp1 hsp2 hrn1 hrn2 hrp1 hrp2)
            (by unfold epochDirPBCellsAt recvDirPBCellsAt56; dsimp only [cur]; sep_focus) ?_
          wp_done
        · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx9_1, hx11_1, hx12_1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx26_1, hx27_1, hx28_1⟩
          exact herr452 s1 prefG pref restG restPB
            curG.send.next.cap curG.send.next.ptr curG.send.prev.cap curG.send.prev.ptr
            curG.recv.next.cap curG.recv.next.ptr curG.recv.prev.cap curG.recv.prev.ptr
            (BitVec.ofNat 64 sendPb.next.length) sp0_val hcl1
            hsp0_align hfromPb_err hprefG_len hrestG_len htotal
            hl_le hl_lt hl_ne hn_le hn_lt hn_ne hsn2 hsn3 hsp2 hsp3 hrn2 hrn3 hrp2 hrp3
            hpc1 hrun1 hsp1 htr1 hfp1 hx9_1 hx11_1 hx12_1 hx19_1 hx20_1 hx21_1
            hx23_1 hx24_1 hx26_1 hx27_1 hx28_1

theorem fromPb_loop_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec A)))
    (x : ChainFromPbCall) (s0 : State) (dir : Direction)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hdir : Direction.fromI32? x.pb.direction = some dir) (hdir_i32 : dir.toI32 = x.pb.direction)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0) :
    ∀ (restPB : List ChainEpochPB) (restG : List ChainEpochPBGhost)
      (prefG : List ChainEpochGhost) (pref : List ChainEpoch) (prefPB : List ChainEpochPB)
      (sp0_val : BitVec 64) (s : State)
      (_hcl : LibsignalCodeLoaded lsmpl s.mem)
      (_hne : restPB ≠ [])
      (_hpref_ok : Chain.linksFromPb prefPB = .ok pref)
      (_hprefG_len : prefG.length = pref.length) (_hpref_len : prefPB.length = pref.length)
      (_hrestG_len : restG.length = restPB.length)
      (_hsplit_links : x.pb.links = prefPB ++ restPB)
      (_hpc : s.pc = (blkPl_364).base + 136#64)
      (_hrun : s.status = .Running) (_hsp : s.sp = s0.sp - 192#64) (_htr : TraceCalleeSaved s s0)
      (_hfp : s.readReg64 .fp = s0.sp - 96#64)
      (_hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (x.pb.links.length * 112))
      (_hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
      (_hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (pref.length * 112)),
      SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
        (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
          arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (prefG.zip pref) ∗
          arrayAt (chainEpochPBAt A) 112 (x.gPb.linksPtr + BitVec.ofNat 64 (pref.length * 112))
            (restG.zip restPB) ∗
          linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
          vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
          loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 192#64) chainFromPbSubStack)
        (fromPbRetPost A x s0)
  | [], _, _, _, _, _, _, _, hne, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd rfl hne
  | curPB :: restPB, [], _, _, _, _, _, _, _, _, _, _, hrestG_len, _, _, _, _, _, _, _, _, _ => by
    cases hrestG_len
  | curPB :: restPB, curG :: restG, prefG, pref, prefPB, sp0_val, s, hcl,
    _, hpref_ok, hprefG_len, hpref_len, hrestG_len, hsplit_links,
    hpc, hrun, hsp, htr, hfp, hx8, hx11, hx25 => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hrestG_len
    dsimp only [List.zip_cons_cons, arrayAt]
    rw [add_curPtr_112 x.gPb.linksPtr pref.length]
    simp only [sepConj_assoc]
    have hstep := fromPb_loop_step_cl_placed hdealloc hchain_slice hproto_slice x s0 s dir prefG pref prefPB
      curG curPB restG restPB sp0_val hcl hsp0_align hdir hdir_i32
      hpref_ok hprefG_len hpref_len hrestG_len hsplit_links
      hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc hrun hsp htr hfp hx8 hx11 hx25
    dsimp only at hstep
    cases hsend : curPB.send with
    | none =>
      rw [hsend] at hstep; exact hstep
    | some sendPb =>
      cases hrecv : curPB.recv with
      | none =>
        rw [hsend, hrecv] at hstep; exact hstep
      | some recvPb =>
        rw [hsend, hrecv] at hstep
        by_cases hcond :
            (BitVec.ofNat 64 sendPb.next.length &&& 0xffffffffffffffdf#64 == 0#64) = true ∧
            (BitVec.ofNat 64 recvPb.next.length &&& 0xffffffffffffffdf#64 == 0#64) = true ∧
            restPB ≠ []
        · rcases hcond with ⟨hs_tst, hr_tst, hrest_ne⟩
          simp only [hs_tst, hr_tst, hrest_ne, ne_eq, not_false_eq_true, and_self, ↓reduceIte] at hstep
          rcases restPB with _ | ⟨nextPB, restPB⟩
          · exact absurd rfl hrest_ne
          · refine fromPb_seq_clean_lscl hcl
              (mid := (blkPl_364).base + 136#64)
              (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
                arrayAt (chainEpochAt A) 112 x.gPb.linksPtr
                  ((prefG ++ [toChainEpochGhost curG]).zip (pref ++ [mkChainEpochFromPb sendPb recvPb])) ∗
                arrayAt (chainEpochPBAt A) 112
                  (x.gPb.linksPtr + BitVec.ofNat 64 ((pref ++ [mkChainEpochFromPb sendPb recvPb]).length * 112))
                  (restG.zip (nextPB :: restPB)) ∗
                linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
                vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
                loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
                stackAt (s0.sp - 192#64) chainFromPbSubStack)
              (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
                sm.readReg64 .fp = s0.sp - 96#64 ∧
                sm.readReg64 .x8 = BitVec.ofNat 64 (x.pb.links.length * 112) ∧
                sm.readReg64 .x11 = x.gPb.linksPtr ∧
                sm.readReg64 .x25 = BitVec.ofNat 64 ((pref ++ [mkChainEpochFromPb sendPb recvPb]).length * 112) ∧
                Chain.linksFromPb (prefPB ++ [curPB]) = .ok (pref ++ [mkChainEpochFromPb sendPb recvPb]))
              hstep ?_
            rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx8_1, hx11_1, hx25_1, hpref_next_ok⟩
            exact fromPb_loop_cl_placed hdealloc hchain_slice hproto_slice x s0 dir hsp0_align hdir hdir_i32
              hl_le hl_lt hl_ne hn_le hn_lt hn_ne
              (nextPB :: restPB) restG
              (prefG ++ [toChainEpochGhost curG])
              (pref ++ [mkChainEpochFromPb sendPb recvPb])
              (prefPB ++ [curPB]) sp0_val s1 hcl1
              (List.cons_ne_nil _ _) hpref_next_ok
              (by simp [hprefG_len]) (by simp [hpref_len]) hrestG_len
              (by rw [List.append_assoc, List.singleton_append]; exact hsplit_links)
              hpc1 hrun1 hsp1 htr1 hfp1 hx8_1 hx11_1 hx25_1
        · simp only [hcond, ↓reduceIte] at hstep
          exact hstep

set_option maxHeartbeats 800000 in
theorem chain_from_pb_body_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec A)))
    (x : ChainFromPbCall) (s0 : State)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_364).base)
    (hrun : s0.status = .Running)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hx8 : s0.readReg64 .x8 = x.out)
    (hx0 : s0.readReg64 .x0 = x.pbPtr) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s0
      (memRegion x.out 88 ∗ chainPBAt A x.gPb x.pbPtr x.pb ∗
        A.pool ∗ stackAt s0.sp chainFromPbStackX)
      (fromPbRetPost A x s0) := by
  have hbad := @fromPb_bad_direction_cl_placed _ A H hdealloc hproto_slice x s0
  have hjoin_ok := @fromPb_join_ok_cl_placed _ A H hdealloc hchain_slice hproto_slice x s0
  have hloop := @fromPb_loop_cl_placed _ A H hdealloc hchain_slice hproto_slice x s0
  refine SepWP.focus_weaken (chainPBAt_unpack A x.gPb x.pbPtr x.pb) (by sep_focus) ?_
  wp_focus_pure
  rintro ⟨hlen, hl_le, hl_lt, hl_ne, hn_le, hn_lt, hn_ne⟩
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  rw [stackAt_chainFromPb_prologue_split s0.sp]
  wp_pull_exists
  try dsimp only [BitVec.ofNat_eq_ofNat] at hbad hjoin_ok hloop hpc ⊢
  by_cases hdir_uge : BitVec.ule 2#32 x.pb.direction = true
  · have hge2 : x.pb.direction.toNat ≥ 2 := by simpa [BitVec.ule] using hdir_uge
    have hult2 : BitVec.ult x.pb.direction 2#32 = false := by simp [BitVec.ult]; omega
    refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 292#64)
      (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochPBAt A) 112 x.gPb.linksPtr (x.gPb.epochs.zip x.pb.links) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x25 = x.pbPtr) ?_ ?_
    · unfold chainPBHeadersAt calleeSavedFromPbAt
      wp_steps
      wp_done
    · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hx24_1, hx25_1⟩
      exact hbad s1 hcl1 hsp0_align hdir_uge hlen hl_le hl_lt hl_ne hn_le hn_lt hn_ne
        hpc1 hrun1 hsp1 htr1 hx24_1 hx25_1
  · have hdir_ult : BitVec.ule 2#32 x.pb.direction = false := Bool.eq_false_iff.mpr hdir_uge
    have hge2 : ¬(x.pb.direction.toNat ≥ 2) := by simpa [BitVec.ule] using hdir_ult
    have hult2 : BitVec.ult x.pb.direction 2#32 = true := by simp [BitVec.ult]; omega
    obtain ⟨dir, hdir, hdir_i32⟩ := direction_fromI32_of_ult_two hdir_ult
    have hlsl : (BitVec.ofNat 64 x.pb.links.length <<< (7 : Nat)) -
        (BitVec.ofNat 64 x.pb.links.length <<< (4 : Nat)) =
        BitVec.ofNat 64 (x.pb.links.length * 112) :=
      mul_112_shift_eq x.pb.links.length hlen_lt
    rw [memRegion_96_scratch_split s0.sp]
    wp_pull_exists
    rename_i s58 s50 s48 s40 s38 s30 s2c s20 s18 s10 s08 s00
    by_cases hlinks_nil : x.pb.links = []
    · have hlen0 : x.pb.links.length = 0 := by rw [hlinks_nil]; rfl
      have hcbz : (BitVec.ofNat 64 x.pb.links.length == 0#64) = true := by rw [hlen0]; rfl
      have hzip_nil : x.gPb.epochs.zip x.pb.links = [] := by rw [hlinks_nil, List.zip_nil_right]
      have hlinks_ok : Chain.linksFromPb x.pb.links = .ok [] := by rw [hlinks_nil]; rfl
      refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 792#64)
        (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
          arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (([] : List ChainEpochGhost).zip []) ∗
          linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
          vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
          joinScratchAt s0 x.gPb x.pb s00 ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 192#64) chainFromPbSubStack)
        (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
          sm.readReg64 .fp = s0.sp - 96#64 ∧
          sm.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 (([] : List ChainEpoch).length * 112) ∧
          sm.readReg64 .x11 = x.gPb.linksPtr ∧ sm.readReg64 .x19 = 1#64 ∧
          sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (([] : List ChainEpoch).length * 112) ∧
          sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
          sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (([] : List ChainEpoch).length * 112) ∧
          sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x25 = x.pbPtr) ?_ ?_
      · rw [hzip_nil]
        simp only [List.zip_nil_right, arrayAt, emp_sepConj]
        unfold chainPBHeadersAt calleeSavedFromPbAt
        wp_steps
        refine SepWP.focus_weaken
          (scratch_entails_joinScratchAt s0 x.gPb x.pb s00 s08 s30 s38 s40 s48)
          (by sep_focus) ?_
        rw [hlen0]
        wp_done
      · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx0_1, hx11_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1⟩
        exact hjoin_ok s1 dir [] [] s00 hcl1 hsp0_align hdir hdir_i32 hlinks_ok
          rfl hlen0.symm hl_le hl_lt hl_ne hn_le hn_lt hn_ne
          hpc1 hrun1 hsp1 htr1 hfp1 hx0_1 hx11_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1
    · have hne_nil : x.pb.links ≠ [] := hlinks_nil
      have hpos : x.pb.links.length > 0 := List.length_pos_iff.mpr hne_nil
      have hcbz : (BitVec.ofNat 64 x.pb.links.length == 0#64) = false := by
        have h64 : x.pb.links.length < 2 ^ 64 := by omega
        rw [beq_eq_false_iff_ne]
        intro heq
        have htn := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64] at htn
        omega
      refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 136#64)
        (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
          arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (([] : List ChainEpochGhost).zip []) ∗
          arrayAt (chainEpochPBAt A) 112 (x.gPb.linksPtr + BitVec.ofNat 64 (([] : List ChainEpoch).length * 112))
            (x.gPb.epochs.zip x.pb.links) ∗
          linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
          vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
          loopScratchAt s0 x s00 ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 192#64) chainFromPbSubStack)
        (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
          sm.readReg64 .fp = s0.sp - 96#64 ∧
          sm.readReg64 .x8 = BitVec.ofNat 64 (x.pb.links.length * 112) ∧
          sm.readReg64 .x11 = x.gPb.linksPtr ∧
          sm.readReg64 .x25 = BitVec.ofNat 64 (([] : List ChainEpoch).length * 112)) ?_ ?_
      · simp only [List.zip_nil_right, List.length_nil, Nat.zero_mul, arrayAt,
          emp_sepConj, BitVec.add_zero]
        unfold chainPBHeadersAt loopScratchAt calleeSavedFromPbAt
        wp_steps
        wp_done
      · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx8_1, hx11_1, hx25_1⟩
        exact hloop dir hsp0_align hdir hdir_i32 hl_le hl_lt hl_ne hn_le hn_lt hn_ne
          x.pb.links x.gPb.epochs [] [] [] s00 s1 hcl1
          hne_nil rfl rfl rfl hlen rfl
          hpc1 hrun1 hsp1 htr1 hfp1 hx8_1 hx11_1 hx25_1

/-- Code-loaded `[LibsignalPlacement]` proof of `<spqr::chain::Chain>::from_pb` (Block `364`). -/
theorem chain_from_pb_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec A))) :
    subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (blkPl_364).base
      (withLsCodeLoaded lsmpl (chainFromPbSpecX A)) := by
  refine subroutine_ok_of_sepWP fun x R s0 hpc hrun hpre hsp0_align => ?_
  have ⟨hcl, hpre'⟩ := extract_withLsCodeLoaded hpre
  refine ⟨(chainFromPbSpecX A).pre x s0, R, hpre', ?_⟩
  dsimp only [chainFromPbSpecX]
  wp_focus_pure
  rintro ⟨hx8, hx0⟩
  refine SepWP.mono (chain_from_pb_body_cl_placed hdealloc hchain_slice hproto_slice x s0 hcl hpc hrun hsp0_align hx8 hx0) ?_
  rintro sf P_f _ _ ⟨⟨hsp, hcs⟩, hP_f⟩
  refine ⟨fun hm => Satisfies.mono (sepConj_mono_left hP_f) hm, hsp, hcs⟩

end CryptoVerification.SpqrV1.ChainProofs
