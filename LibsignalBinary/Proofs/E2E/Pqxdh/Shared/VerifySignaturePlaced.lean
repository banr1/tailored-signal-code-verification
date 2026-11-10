/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonicalPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignaturePlacedA
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignaturePlacedB
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.Shared

open Arm64 ProofLib CryptoVerification
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Pqxdh
open SignalPqxdh

/-!
# Relocatable `<PublicKey>::verify_signature` (Blocks `203` and `204`)

Proves relocatable `[LibsignalPlacement]` contracts for unmutated Blocks `204`
(`verify_signature_for_multipart_message`) and `203` (`verify_signature`), parameterized over an
explicit `h_canon` contract on Block `202` (`PublicKey::is_canonical`) via
`curveVerifyAndCanon_placed_ok_of_canon`, along with `[LibsignalFullPlacement]` corollaries.

## Block `204` (`verify_signature_for_multipart_message`)
-/

set_option maxHeartbeats 2400000 in
/-- Full end-to-end `SepWP` theorem for Block `204` (`verify_signature_for_multipart_message`)
    under `[LibsignalPlacement]`, returning `xeddsaVerifyRef P pk m sig` in `x0`. -/
theorem verifySignatureMultipart_sepWP_placed [LibsignalPlacement]
    (P : Primitives) (H : LibsignalHooks) (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks' P H)
    (s : State) (fsp pkPtr slicesPtr msgPtr sigPtr retAddr : BitVec 64)
    (pk m sig : Bytes) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : Obj.HoldsBytes s.mem (lsmpl.ρ lsVerifySha512IVRoSym) sha512IVBytesLE (fun _ => Perm.ro))
    (hpk : pk.length = 32)
    (hm : m.length = 33 ∨ m.length = 1569)
    (hsig : sig.length = 64)
    (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base)
    (hsp : s.sp = fsp + 1248#64)
    (hx0 : s.readReg64 (.gpr 0#5) = pkPtr)
    (hx1 : s.readReg64 (.gpr 1#5) = slicesPtr)
    (hx2 : s.readReg64 (.gpr 2#5) = 1#64)
    (hx3 : s.readReg64 (.gpr 3#5) = sigPtr)
    (hx4 : s.readReg64 (.gpr 4#5) = 64#64)
    (hx30 : s.readReg64 (.gpr 30#5) = retAddr) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H) retAddr s
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (slicesPtr ↦₆₄ msgPtr) ∗
       ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
       (msgPtr ↦ₛ bytesToBv8 m) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
       stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (pkPtr ↦ₛ bytesToBv8 pk) ∗ (slicesPtr ↦₆₄ msgPtr) ∗
          ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
          (msgPtr ↦ₛ bytesToBv8 m) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
          stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧ sm.pc = retAddr ∧ sm.sp = fsp + 1248#64 ∧
        sm.readReg64 (.gpr 0#5) = (if xeddsaVerifyRef P pk m sig = true then 1#64 else 0#64) ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
        sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
        sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (verifySig_stackAt_1248_split fsp))
    (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (verifySig_memRegion_1152_seg1a_split fsp))
    (by sep_frame)
  apply verifySig_seq_seg_lscro ⟨hcl, hro⟩ (verifySig_seg1a_placed P H hH s fsp pkPtr slicesPtr sigPtr
    retAddr pk sig
    ((slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
     (msgPtr ↦ₛ bytesToBv8 m) ∗ memRegion (fsp + 8#64) 8 ∗
     memRegion (fsp + 48#64) 752 ∗ memRegion (fsp + 968#64) 184 ∗ Frame)
    hpk hsig hfsp_align hrun hpc hsp hx0 hx1 hx2 hx3 hx4 hx30)
    (Entails.of_eq (by ac_rfl))
  intro s1 hpc1 hrun1 ⟨hcl1, hro1⟩ ⟨_, _, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx29_1, hv1, htr1⟩
  cases hmont : P.montToEd pk ((sig.getD 63 0 &&& 0x80) >>> 7) with
  | none =>
    have hxed : xeddsaVerifyRef P pk m sig = false := verifySig_xeddsaVerifyRef_of_montToEd_none P hmont
    apply verifySig_seq_seg (verifySig_seg1a_none_placed P H s1 fsp pk ((sig.getD 63 0 &&& 0x80) >>> 7)
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗ (fsp ↦₆₄ 0#64) ∗
       memRegion (fsp + 8#64) 8 ∗ memRegion (fsp + 16#64) 32 ∗
       memRegion (fsp + 48#64) 752 ∗ memRegion (fsp + 968#64) 184 ∗
       ((fsp + 1152#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
       ((fsp + 1168#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
       ((fsp + 1176#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
       ((fsp + 1184#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗
       ((fsp + 1192#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
       ((fsp + 1200#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
       ((fsp + 1208#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
       ((fsp + 1216#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗
       ((fsp + 1224#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
       ((fsp + 1232#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗
       ((fsp + 1240#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗
       stackAt fsp pqxdhHookStack ∗ (slicesPtr ↦₆₄ msgPtr) ∗
       ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
       (msgPtr ↦ₛ bytesToBv8 m) ∗ Frame)
      hmont hfsp_align hrun1 hpc1 hsp1)
      (Entails.of_eq (by ac_rfl))
    intro s2 hpc2 hrun2 ⟨_, _, hsp2, hv2, htr2⟩
    apply ProofLib.SepWP.replace_pre (hPQ := verifySig_memRegion_1152_seg1a_merge fsp) (by sep_frame)
    apply verifySig_end_seg (verifySig_epilogue_false_placed H s2 fsp retAddr
      (s.readReg64 (.gpr 19#5)) (s.readReg64 (.gpr 20#5)) (s.readReg64 (.gpr 21#5))
      (s.readReg64 (.gpr 22#5)) (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 24#5))
      (s.readReg64 (.gpr 25#5)) (s.readReg64 (.gpr 26#5)) (s.readReg64 (.gpr 27#5))
      (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 29#5))
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (slicesPtr ↦₆₄ msgPtr) ∗
       ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
       (msgPtr ↦ₛ bytesToBv8 m) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗ Frame)
      hfsp_align hrun2 hpc2 hsp2)
      (Entails.of_eq (by ac_rfl))
    intro s3 P3 hP3 ⟨hrun3, hpc3, hsp3, hx0_3, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28,
      h29, hv3, htr3⟩
    rw [hxed]
    exact ⟨Entails.trans hP3 (Entails.of_eq (by ac_rfl)), hrun3, hpc3, hsp3, hx0_3,
      h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
      hv3.trans (hv2.trans hv1), htr3.trans (htr2.trans htr1)⟩
  | some edPt =>
    have hedPt : edPt.length = 160 := hWF.montToEd_len pk _ edPt hmont
    have hcapA : (P.compress edPt).length = 32 := hWF.compress_len edPt
    apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (verifySig_memRegion_752_seg1b_split fsp))
      (by sep_frame)
    apply verifySig_seq_seg_lscro ⟨hcl1, hro1⟩ (verifySig_seg1b_placed P H hWF hH s1 fsp pk edPt
      ((sig.getD 63 0 &&& 0x80) >>> 7)
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗ (fsp ↦₆₄ 0#64) ∗
       memRegion (fsp + 8#64) 8 ∗ memRegion (fsp + 16#64) 32 ∗
       memRegion (fsp + 400#64) 400 ∗ memRegion (fsp + 968#64) 184 ∗
       ((fsp + 1152#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
       ((fsp + 1168#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
       ((fsp + 1176#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
       ((fsp + 1184#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗
       ((fsp + 1192#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
       ((fsp + 1200#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
       ((fsp + 1208#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
       ((fsp + 1216#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗
       ((fsp + 1224#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
       ((fsp + 1232#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗
       ((fsp + 1240#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗
       (slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
       (msgPtr ↦ₛ bytesToBv8 m) ∗ Frame)
      hmont hfsp_align hrun1 hpc1 hsp1)
      (Entails.of_eq (by ac_rfl))
    intro s2 hpc2 hrun2 ⟨hcl2, hro2⟩ ⟨_, _, hsp2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx29_2,
      hv2, htr2⟩
    have hx19_s2 : s2.readReg64 (.gpr 19#5) = sigPtr := hx19_2.trans hx19_1
    have hx20_s2 : s2.readReg64 (.gpr 20#5) = slicesPtr := hx20_2.trans hx20_1
    have hx21_s2 : s2.readReg64 (.gpr 21#5) = 1#64 := hx21_2.trans hx21_1
    have hx22_s2 : s2.readReg64 (.gpr 22#5) = BitVec.zeroExtend 64 (sig.getD 63 0).toBitVec := by
      rw [hx22_2, hx22_1, bytesToBv8_getD_eq sig 63]
      generalize sig.getD 63 0 = b; rcases b with ⟨bv⟩; revert bv; decide
    have hx29_s2 : s2.readReg64 (.gpr 29#5) = fsp + 1152#64 := hx29_2.trans hx29_1
    cases h60 : (sig.getD 63 0 &&& 0x60 == 0) with
    | false =>
      have hxed : xeddsaVerifyRef P pk m sig = false := verifySig_xeddsaVerifyRef_of_60_false P h60
      apply verifySig_seq_seg (verifySig_seg1c_invalid_placed H s2 sig
        (memRegion (fsp + 48#64) 160 ∗ ((fsp + 208#64) ↦ₛ bytesToBv8 edPt) ∗
         ((fsp + 368#64) ↦ₛ bytesToBv8 (P.compress edPt)) ∗ memRegion (fsp + 800#64) 168 ∗
         stackAt fsp pqxdhHookStack ∗ (pkPtr ↦ₛ bytesToBv8 pk) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
         (fsp ↦₆₄ 0#64) ∗ memRegion (fsp + 8#64) 8 ∗ memRegion (fsp + 16#64) 32 ∗
         memRegion (fsp + 400#64) 400 ∗ memRegion (fsp + 968#64) 184 ∗
         ((fsp + 1152#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
         ((fsp + 1168#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
         ((fsp + 1176#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
         ((fsp + 1184#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗
         ((fsp + 1192#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
         ((fsp + 1200#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
         ((fsp + 1208#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
         ((fsp + 1216#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗
         ((fsp + 1224#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
         ((fsp + 1232#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗
         ((fsp + 1240#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗
         (slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
         (msgPtr ↦ₛ bytesToBv8 m) ∗ Frame)
        h60 hrun2 hpc2 hx22_s2)
        (Entails.of_eq (by ac_rfl))
      intro s3 hpc3 hrun3 ⟨_, _, hsp3, hv3, htr3⟩
      have hsp3_eq : s3.sp = fsp := hsp3.trans hsp2
      apply ProofLib.SepWP.replace_pre (hPQ := verifySig_memRegion_752_seg1b_merge fsp hedPt hcapA)
        (by sep_frame)
      apply ProofLib.SepWP.replace_pre (hPQ := verifySig_memRegion_1152_seg1a_merge fsp) (by sep_frame)
      apply verifySig_end_seg (verifySig_epilogue_false_placed H s3 fsp retAddr
        (s.readReg64 (.gpr 19#5)) (s.readReg64 (.gpr 20#5)) (s.readReg64 (.gpr 21#5))
        (s.readReg64 (.gpr 22#5)) (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 24#5))
        (s.readReg64 (.gpr 25#5)) (s.readReg64 (.gpr 26#5)) (s.readReg64 (.gpr 27#5))
        (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 29#5))
        ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (slicesPtr ↦₆₄ msgPtr) ∗
         ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
         (msgPtr ↦ₛ bytesToBv8 m) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗ Frame)
        hfsp_align hrun3 hpc3 hsp3_eq)
        (Entails.of_eq (by ac_rfl))
      intro s4 P4 hP4 ⟨hrun4, hpc4, hsp4, hx0_4, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28,
        h29, hv4, htr4⟩
      rw [hxed]
      exact ⟨Entails.trans hP4 (Entails.of_eq (by ac_rfl)), hrun4, hpc4, hsp4, hx0_4,
        h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
        hv4.trans (hv3.trans (hv2.trans hv1)), htr4.trans (htr3.trans (htr2.trans htr1))⟩
    | true =>
      have hxed_eq := verifySig_xeddsaVerifyRef_of_some P m hpk hsig h60 hmont
      apply ProofLib.SepWP.replace_pre (hPQ := verifySig_seg1b_to_seg1c_split fsp) (by sep_frame)
      apply verifySig_seq_seg_lscl hcl2 (verifySig_seg1c_placed P H hWF hH s2 fsp sigPtr edPt sig
        (memRegion (fsp + 16#64) 32 ∗ memRegion (fsp + 48#64) 160 ∗
         memRegion (fsp + 624#64) 63 ∗ memRegion (fsp + 768#64) 32 ∗
         memRegion (fsp + 800#64) 168 ∗ memRegion (fsp + 968#64) 184 ∗
         ((fsp + 1152#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
         ((fsp + 1168#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
         ((fsp + 1176#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
         ((fsp + 1184#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗
         ((fsp + 1192#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
         ((fsp + 1200#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
         ((fsp + 1208#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
         ((fsp + 1216#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗
         ((fsp + 1224#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
         ((fsp + 1232#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗
         ((fsp + 1240#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗
         (pkPtr ↦ₛ bytesToBv8 pk) ∗ (slicesPtr ↦₆₄ msgPtr) ∗
         ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
         (msgPtr ↦ₛ bytesToBv8 m) ∗ Frame)
        hro2 hedPt hsig h60 hfsp_align hrun2 hpc2 hsp2 hx19_s2 hx22_s2)
        (Entails.of_eq (by ac_rfl))
      intro s3 hpc3 hrun3 hcl3 ⟨_, _, hsp3, hx20_3, hx21_3, hx23_3, hx29_3, hv3, htr3⟩
      have hx20_s3 : s3.readReg64 (.gpr 20#5) = slicesPtr := hx20_3.trans hx20_s2
      have hx21_s3 : s3.readReg64 (.gpr 21#5) = 1#64 := hx21_3.trans hx21_s2
      have hx23_s3 : s3.readReg64 (.gpr 23#5) = fsp + 800#64 := hx23_3.trans hx23_2
      have hx29_s3 : s3.readReg64 (.gpr 29#5) = fsp + 1152#64 := hx29_3.trans hx29_s2
      have hpre64 : (sig.take 32 ++ P.compress edPt).length = 64 := by simp [hsig, hcapA]
      have hshaIV : sha512IVBytesLE = bytesToBv8 (revWords64 sha512InitState) := rfl
      have hst0 : (revWords64 sha512InitState).length = 64 := revWords64_length (by decide)
      rw [hshaIV]
      rcases hm with hm33 | hm1569
      · rw [hm33, show BitVec.ofNat 64 33 = 33#64 from rfl]
        apply verifySig_seq_seg_lscl hcl3 (verifySig_seg2_33_placed P H hH s3 fsp slicesPtr msgPtr
          (sig.take 32 ++ P.compress edPt) m (revWords64 sha512InitState)
          (memRegion fsp 4 ∗
           ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
           ((fsp + 8#64) ↦₆₄ sigPtr) ∗ memRegion (fsp + 16#64) 32 ∗
           memRegion (fsp + 48#64) 160 ∗ memRegion (fsp + 208#64) 160 ∗
           ((fsp + 368#64) ↦ₛ bytesToBv8 (P.compress edPt)) ∗
           ((fsp + 400#64) ↦ₛ bytesToBv8 (P.edNeg edPt)) ∗
           memRegion (fsp + 768#64) 32 ∗ memRegion (fsp + 800#64) 168 ∗
           memRegion (fsp + 968#64) 184 ∗
           ((fsp + 1152#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
           ((fsp + 1168#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
           ((fsp + 1176#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
           ((fsp + 1184#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗
           ((fsp + 1192#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
           ((fsp + 1200#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
           ((fsp + 1208#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
           ((fsp + 1216#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗
           ((fsp + 1224#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
           ((fsp + 1232#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗
           ((fsp + 1240#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗
           (pkPtr ↦ₛ bytesToBv8 pk) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗ Frame)
          hpre64 hm33 hfsp_align hrun3 hpc3 hsp3 hx20_s3 hx21_s3)
          (Entails.of_eq (by ac_rfl))
        intro s4 hpc4 hrun4 hcl4 ⟨_, _, hsp4, hx23_4, hx29_4, hv4, htr4⟩
        have hx23_s4 : s4.readReg64 (.gpr 23#5) = fsp + 800#64 := hx23_4.trans hx23_s3
        have hx29_s4 : s4.readReg64 (.gpr 29#5) = fsp + 1152#64 := hx29_4.trans hx29_s3
        have htail97 : ((sig.take 32 ++ P.compress edPt) ++ m).length = 97 := by
          simp [hsig, hcapA, hm33]
        have hsha_eq : revWords64 (sha512CompressOutBytes P (revWords64 sha512InitState)
            (((sig.take 32 ++ P.compress edPt) ++ m) ++ [0x80] ++ List.replicate 14 0 ++
            encodeBitLen128BE 97)) =
            P.sha512 (sig.take 32 ++ P.compress edPt ++ m) := by
          rw [hWF.sha512_eq_ref, sha512Ref_of_length_97 P htail97]
        apply verifySig_end_seg (verifySig_tail_from_548_placed P H hWF hH s4 fsp sigPtr retAddr
          (s.readReg64 (.gpr 19#5)) (s.readReg64 (.gpr 20#5)) (s.readReg64 (.gpr 21#5))
          (s.readReg64 (.gpr 22#5)) (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 24#5))
          (s.readReg64 (.gpr 25#5)) (s.readReg64 (.gpr 26#5)) (s.readReg64 (.gpr 27#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 29#5))
          edPt m sig ((sig.take 32 ++ P.compress edPt) ++ m) (revWords64 sha512InitState) 0#64 97
          ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (slicesPtr ↦₆₄ msgPtr) ∗
           ((slicesPtr + 8#64) ↦₆₄ 33#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗ Frame)
          hcl4 hedPt hsig htail97 hst0 (Or.inl ⟨rfl, rfl⟩)
          hsha_eq hfsp_align hrun4 hpc4 hsp4 hx23_s4 hx29_s4)
          (Entails.of_eq (by ac_rfl))
        intro s5 P5 hP5 ⟨hrun5, hpc5, hsp5, hx0_5, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28,
          h29, hv5, htr5⟩
        exact ⟨Entails.trans hP5 (Entails.of_eq (by ac_rfl)), hrun5, hpc5, hsp5,
          hx0_5.trans hxed_eq, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
          hv5.trans (hv4.trans (hv3.trans (hv2.trans hv1))),
          htr5.trans (htr4.trans (htr3.trans (htr2.trans htr1)))⟩
      · rw [hm1569, show BitVec.ofNat 64 1569 = 1569#64 from rfl]
        apply verifySig_seq_seg_lscl hcl3 (verifySig_seg2_1569_placed P H hH s3 fsp slicesPtr msgPtr
          (sig.take 32 ++ P.compress edPt) m (revWords64 sha512InitState)
          (memRegion fsp 4 ∗
           ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
           ((fsp + 8#64) ↦₆₄ sigPtr) ∗ memRegion (fsp + 16#64) 32 ∗
           memRegion (fsp + 48#64) 160 ∗ memRegion (fsp + 208#64) 160 ∗
           ((fsp + 368#64) ↦ₛ bytesToBv8 (P.compress edPt)) ∗
           ((fsp + 400#64) ↦ₛ bytesToBv8 (P.edNeg edPt)) ∗
           memRegion (fsp + 768#64) 32 ∗ memRegion (fsp + 800#64) 168 ∗
           memRegion (fsp + 968#64) 184 ∗
           ((fsp + 1152#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
           ((fsp + 1168#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
           ((fsp + 1176#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
           ((fsp + 1184#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗
           ((fsp + 1192#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
           ((fsp + 1200#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
           ((fsp + 1208#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
           ((fsp + 1216#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗
           ((fsp + 1224#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
           ((fsp + 1232#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗
           ((fsp + 1240#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗
           (pkPtr ↦ₛ bytesToBv8 pk) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗ Frame)
          hpre64 hm1569 hst0 hfsp_align hrun3 hpc3 hsp3 hx20_s3 hx21_s3)
          (Entails.of_eq (by ac_rfl))
        intro s4 hpc4 hrun4 hcl4 ⟨_, _, hsp4, hx23_4, hx29_4, hv4, htr4⟩
        have hx23_s4 : s4.readReg64 (.gpr 23#5) = fsp + 800#64 := hx23_4.trans hx23_s3
        have hx29_s4 : s4.readReg64 (.gpr 29#5) = fsp + 1152#64 := hx29_4.trans hx29_s3
        have hblk0 : ((sig.take 32 ++ P.compress edPt) ++ m.take 64).length = 128 := by
          simp [hsig, hcapA, hm1569]
        have hblks11 : ((m.drop 64).take 1408).length = 1408 := by simp [hm1569]
        have htail97 : (m.drop 1472).length = 97 := by simp [hm1569]
        have hm_split : ((sig.take 32 ++ P.compress edPt) ++ m.take 64) ++ (m.drop 64).take 1408 ++
            m.drop 1472 = sig.take 32 ++ P.compress edPt ++ m := by
          have h1 : (m.drop 64).take 1408 ++ m.drop 1472 = m.drop 64 := by
            rw [show (1472 : Nat) = 64 + 1408 from rfl, ← List.drop_drop, List.take_append_drop]
          rw [List.append_assoc, List.append_assoc ((sig.take 32 ++ P.compress edPt)), h1,
            List.take_append_drop]
        have hst12 : (sha512CompressOutBytes P (sha512CompressOutBytes P
            (revWords64 sha512InitState) ((sig.take 32 ++ P.compress edPt) ++ m.take 64))
            ((m.drop 64).take 1408)).length = 64 :=
          sha512CompressOutBytes_length P _ _
        have hsha_eq : revWords64 (sha512CompressOutBytes P
            (sha512CompressOutBytes P (sha512CompressOutBytes P (revWords64 sha512InitState)
              ((sig.take 32 ++ P.compress edPt) ++ m.take 64)) ((m.drop 64).take 1408))
            (m.drop 1472 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE 1633)) =
            P.sha512 (sig.take 32 ++ P.compress edPt ++ m) := by
          rw [hWF.sha512_eq_ref, ← hm_split, sha512Ref_of_length_1633 P hblk0 hblks11 htail97]
        apply verifySig_end_seg (verifySig_tail_from_548_placed P H hWF hH s4 fsp sigPtr retAddr
          (s.readReg64 (.gpr 19#5)) (s.readReg64 (.gpr 20#5)) (s.readReg64 (.gpr 21#5))
          (s.readReg64 (.gpr 22#5)) (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 24#5))
          (s.readReg64 (.gpr 25#5)) (s.readReg64 (.gpr 26#5)) (s.readReg64 (.gpr 27#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 29#5))
          edPt m sig (m.drop 1472)
          (sha512CompressOutBytes P (sha512CompressOutBytes P (revWords64 sha512InitState)
            ((sig.take 32 ++ P.compress edPt) ++ m.take 64)) ((m.drop 64).take 1408))
          12#64 1633
          ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (slicesPtr ↦₆₄ msgPtr) ∗
           ((slicesPtr + 8#64) ↦₆₄ 1569#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗ Frame)
          hcl4 hedPt hsig htail97 hst12 (Or.inr ⟨rfl, rfl⟩)
          hsha_eq hfsp_align hrun4 hpc4 hsp4 hx23_s4 hx29_s4)
          (Entails.of_eq (by ac_rfl))
        intro s5 P5 hP5 ⟨hrun5, hpc5, hsp5, hx0_5, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28,
          h29, hv5, htr5⟩
        exact ⟨Entails.trans hP5 (Entails.of_eq (by ac_rfl)), hrun5, hpc5, hsp5,
          hx0_5.trans hxed_eq, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
          hv5.trans (hv4.trans (hv3.trans (hv2.trans hv1))),
          htr5.trans (htr4.trans (htr3.trans (htr2.trans htr1)))⟩

/-- Ghost arguments of `<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message`
    (Block `204`, 1-slice invocation). -/
structure VerifySignatureMultipartPlacedGhost where
  pkPtr : BitVec 64
  pk : Bytes
  slicesPtr : BitVec 64
  msgPtr : BitVec 64
  m : Bytes
  sigPtr : BitVec 64
  sig : Bytes

/-- Relocatable `Spec` for Block `204` (`verify_signature_for_multipart_message`, 1-slice case). -/
def verifySignatureMultipartCallSpec (P : Primitives) :
    Spec VerifySignatureMultipartPlacedGhost where
  pre g s :=
    ⌜s.readReg64 .x0 = g.pkPtr ∧
      s.readReg64 .x1 = g.slicesPtr ∧
      s.readReg64 .x2 = 1#64 ∧
      s.readReg64 .x3 = g.sigPtr ∧
      s.readReg64 .x4 = 64#64 ∧
      g.pk.length = 32 ∧
      (g.m.length = 33 ∨ g.m.length = 1569) ∧
      g.sig.length = 64⌝ ∗
      (g.pkPtr ↦ₛ bytesToBv8 g.pk) ∗
      (g.slicesPtr ↦₆₄ g.msgPtr) ∗
      ((g.slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 g.m.length) ∗
      (g.msgPtr ↦ₛ bytesToBv8 g.m) ∗
      (g.sigPtr ↦ₛ bytesToBv8 g.sig) ∗
      stackAt s.sp (pqxdhHookStack + 1248)
  post g s0 sf :=
    ⌜sf.readReg64 .x0 = (if xeddsaVerifyRef P g.pk g.m g.sig = true then 1#64 else 0#64) ∧
      sf.trace = s0.trace⌝ ∗
      (g.pkPtr ↦ₛ bytesToBv8 g.pk) ∗
      (g.slicesPtr ↦₆₄ g.msgPtr) ∗
      ((g.slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 g.m.length) ∗
      (g.msgPtr ↦ₛ bytesToBv8 g.m) ∗
      (g.sigPtr ↦ₛ bytesToBv8 g.sig) ∗
      stackAt s0.sp (pqxdhHookStack + 1248)

theorem verifySignatureMultipart_placed_ok' [LibsignalPlacement]
    {P : Primitives} {H : LibsignalHooks}
    (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks' P H) :
    subroutine_ok ((blkPC_204).rebase (blkPl_204).base H)
      (blkPl_204).base
      (withLsCodeRoLoaded lsmpl (verifySignatureMultipartCallSpec P)) := by
  refine subroutine_ok_of_sepWP fun g R s0 hpc hrun hpre hsp => ?_
  obtain ⟨⟨hcl, hro_all⟩, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  have hro := sha512IV_placed_holdsBytes hro_all
  dsimp only [verifySignatureMultipartCallSpec] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hpk, hm, hsig⟩, hmem⟩
  have hfsp_align : ((s0.sp - 1248#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1248#64 hsp (by decide)
  have hfsp_add : (s0.sp - 1248#64) + 1248#64 = s0.sp := by bv_omega
  refine ⟨((g.pkPtr ↦ₛ bytesToBv8 g.pk) ∗ (g.slicesPtr ↦₆₄ g.msgPtr) ∗
      ((g.slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 g.m.length) ∗
      (g.msgPtr ↦ₛ bytesToBv8 g.m) ∗ (g.sigPtr ↦ₛ bytesToBv8 g.sig) ∗
      stackAt ((s0.sp - 1248#64) + 1248#64) (pqxdhHookStack + 1248) ∗ emp), R, ?_, ?_⟩
  · rw [hfsp_add, sepConj_emp]
    exact Arm64.Satisfies.of_eq hmem (by ac_rfl)
  · refine SepWP.mono
      (verifySignatureMultipart_sepWP_placed P H hWF hH s0 (s0.sp - 1248#64)
        g.pkPtr g.slicesPtr g.msgPtr g.sigPtr (s0.readReg64 Reg.lr)
        g.pk g.m g.sig emp hcl hro hpk hm hsig hfsp_align hrun hpc hfsp_add.symm
        hx0 hx1 hx2 hx3 hx4 rfl) ?_
    intro sf Pf _ _ ⟨hPf, _, _, hsp_f, hx0_f,
      h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hvregs, htr⟩
    refine ⟨fun hsat => ?_, hsp_f.trans hfsp_add,
      ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hvregs⟩⟩
    rw [hfsp_add, sepConj_emp] at hPf
    dsimp only [verifySignatureMultipartCallSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_f, htr⟩,
      Arm64.Satisfies.mono (sepConj_mono_left (Entails.trans hPf (Entails.of_eq (by ac_rfl)))) hsat⟩

theorem verifySignatureMultipart_placed_ok_of_block' [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {P : Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks' P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 204)
      (withLsCodeRoLoaded lsmpl (verifySignatureMultipartCallSpec P)) := by
  simpa only [ls_blockPlacement_base] using
    keys_ls_subroutine_ok_of_block_cro (j := 204)
      (verifySignatureMultipart_placed_ok' hWF hH) hi

theorem verifySignatureMultipart_placed_frozen_ok_of_block' [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {P : Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks' P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 204)
      (withLsFrozen lsmpl (verifySignatureMultipartCallSpec P)) :=
  subroutine_ok_withLsFrozen_of_withLsCodeRoLoaded
    (verifySignatureMultipart_placed_ok_of_block' hWF hH hi)

/-- `subroutine_ok` for Block `204` (`verify_signature_for_multipart_message`) on its own block
    program under `[LibsignalPlacement]`. -/
theorem verifySignatureMultipart_placed_ok [LibsignalPlacement]
    {P : Primitives} {H : LibsignalHooks}
    (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks P H) :
    subroutine_ok ((blkPC_204).rebase (blkPl_204).base H)
      (blkPl_204).base
      (withLsCodeRoLoaded lsmpl (verifySignatureMultipartCallSpec P)) :=
  verifySignatureMultipart_placed_ok' hWF (.of_hooks hH)

theorem verifySignatureMultipart_placed_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {P : Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 204)
      (withLsCodeRoLoaded lsmpl (verifySignatureMultipartCallSpec P)) :=
  verifySignatureMultipart_placed_ok_of_block' hWF (.of_hooks hH) hi

theorem verifySignatureMultipart_placed_frozen_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {P : Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 204)
      (withLsFrozen lsmpl (verifySignatureMultipartCallSpec P)) :=
  verifySignatureMultipart_placed_frozen_ok_of_block' hWF (.of_hooks hH) hi

/-! ## Block `203` (`verify_signature`) -/

private theorem verifySig_stackAt_1280_split (fsp : BitVec 64) :
    stackAt (fsp + 1280#64) (pqxdhHookStack + 1280) =
      stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ∗ cells (fsp + 1248#64) 4 := by
  have h1 : fsp + 1280#64 - 32#64 = fsp + 1248#64 := by bv_omega
  have h2 : pqxdhHookStack + 1280 = (pqxdhHookStack + 1248) + 4 * 8 := by decide
  rw [h2, stackAt_split_cells (fsp + 1280#64) (pqxdhHookStack + 1248) 4 (by decide), h1]

private theorem verifySig_stackAt_1280_merge (fsp v0 v1 v2 v3 : BitVec 64) :
    ((fsp + 1248#64) ↦₆₄ v0) ∗ ((fsp + 1256#64) ↦₆₄ v1) ∗
    ((fsp + 1264#64) ↦₆₄ v2) ∗ ((fsp + 1272#64) ↦₆₄ v3) ∗
    stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ⊢
      stackAt (fsp + 1280#64) (pqxdhHookStack + 1280) := by
  rw [verifySig_stackAt_1280_split fsp, sepConj_comm (stackAt _ _),
    ← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc]
  refine sepConj_mono_left ?_
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.sepExists_right v3 <| Entails.refl _

theorem verifySignature_prologue_placed [LibsignalPlacement]
    (H : LibsignalHooks)
    (s : State) (fsp pkPtr msgPtr msgLen sigPtr retAddr : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_203).base)
    (hsp : s.sp = fsp + 1280#64)
    (hx0 : s.readReg64 (.gpr 0#5) = pkPtr)
    (hx1 : s.readReg64 (.gpr 1#5) = msgPtr)
    (hx2 : s.readReg64 (.gpr 2#5) = msgLen)
    (hx3 : s.readReg64 (.gpr 3#5) = sigPtr)
    (hx4 : s.readReg64 (.gpr 4#5) = 64#64)
    (hx30 : s.readReg64 (.gpr 30#5) = retAddr) :
    SepWP ((blkPC_203).rebase (blkPl_203).base H)
      (lsmpl.base 204)
      s
      (cells (fsp + 1248#64) 4 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 1248#64) ↦₆₄ msgPtr) ∗
          ((fsp + 1256#64) ↦₆₄ msgLen) ∗
          ((fsp + 1264#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗
          ((fsp + 1272#64) ↦₆₄ retAddr) ∗
          Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = lsmpl.base 204 ∧
        sm.sp = fsp + 1248#64 ∧
        sm.readReg64 (.gpr 0#5) = pkPtr ∧
        sm.readReg64 (.gpr 1#5) = fsp + 1248#64 ∧
        sm.readReg64 (.gpr 2#5) = 1#64 ∧
        sm.readReg64 (.gpr 3#5) = sigPtr ∧
        sm.readReg64 (.gpr 4#5) = 64#64 ∧
        sm.readReg64 (.gpr 30#5) = (blkPl_203).base + 28#64 ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
        sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
        sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.trace = s.trace) := by
  cells_pre_unfold_fast
  wp_extract_exists
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), ?_⟩
  refine ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal⟩

theorem verifySignature_epilogue_placed [LibsignalPlacement]
    (H : LibsignalHooks)
    (s : State) (fsp msgPtr msgLen x29_0 retAddr : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_203).base + 28#64)
    (hsp : s.sp = fsp + 1248#64) :
    SepWP ((blkPC_203).rebase (blkPl_203).base H)
      retAddr
      s
      (((fsp + 1248#64) ↦₆₄ msgPtr) ∗
       ((fsp + 1256#64) ↦₆₄ msgLen) ∗
       ((fsp + 1264#64) ↦₆₄ x29_0) ∗
       ((fsp + 1272#64) ↦₆₄ retAddr) ∗
       stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢ stackAt (fsp + 1280#64) (pqxdhHookStack + 1280) ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = retAddr ∧
        sm.sp = fsp + 1280#64 ∧
        sm.readReg64 (.gpr 0#5) = s.readReg64 (.gpr 0#5) ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
        sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
        sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
        sm.readReg64 (.gpr 29#5) = x29_0 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.trace = s.trace) := by
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨?_, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono_left (verifySig_stackAt_1280_merge fsp msgPtr msgLen x29_0 retAddr))

/-- Full end-to-end `SepWP` theorem for Block `203` (`verify_signature`) under
    `[LibsignalPlacement]`, returning `P.sigVerify pk m sig` in `x0`. -/
theorem verifySignature_sepWP_placed [LibsignalPlacement]
    (P : Primitives) (H : LibsignalHooks) (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks' P H)
    (s : State) (fsp pkPtr msgPtr sigPtr retAddr : BitVec 64)
    (pk m sig : Bytes)
    (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : Obj.HoldsBytes s.mem (lsmpl.ρ lsVerifySha512IVRoSym) sha512IVBytesLE (fun _ => Perm.ro))
    (hpk : pk.length = 32)
    (hm : m.length = 33 ∨ m.length = 1569)
    (hsig : sig.length = 64)
    (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_203).base)
    (hsp : s.sp = fsp + 1280#64)
    (hx0 : s.readReg64 (.gpr 0#5) = pkPtr)
    (hx1 : s.readReg64 (.gpr 1#5) = msgPtr)
    (hx2 : s.readReg64 (.gpr 2#5) = BitVec.ofNat 64 m.length)
    (hx3 : s.readReg64 (.gpr 3#5) = sigPtr)
    (hx4 : s.readReg64 (.gpr 4#5) = 64#64)
    (hx30 : s.readReg64 (.gpr 30#5) = retAddr) :
    SepWP ((blkPC_203).rebase (blkPl_203).base H)
      retAddr
      s
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗
       (msgPtr ↦ₛ bytesToBv8 m) ∗
       (sigPtr ↦ₛ bytesToBv8 sig) ∗
       stackAt (fsp + 1280#64) (pqxdhHookStack + 1280) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          (pkPtr ↦ₛ bytesToBv8 pk) ∗
          (msgPtr ↦ₛ bytesToBv8 m) ∗
          (sigPtr ↦ₛ bytesToBv8 sig) ∗
          stackAt (fsp + 1280#64) (pqxdhHookStack + 1280) ∗
          Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = retAddr ∧
        sm.sp = fsp + 1280#64 ∧
        sm.readReg64 (.gpr 0#5) = (if P.sigVerify pk m sig = true then 1#64 else 0#64) ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
        sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
        sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.trace = s.trace) := by
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (verifySig_stackAt_1280_split fsp))
    (by sep_frame)
  apply verifySig_seq_seg_lscro ⟨hcl, hro⟩
    (verifySignature_prologue_placed H s fsp pkPtr msgPtr (BitVec.ofNat 64 m.length) sigPtr retAddr
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
       stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ∗ Frame)
      hfsp_align hrun hpc hsp hx0 hx1 hx2 hx3 hx4 hx30)
    (Entails.of_eq (by ac_rfl))
  intro s1 hpc1 hrun1 ⟨hcl1, hro1⟩ ⟨_, _, hsp1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx30_1,
    h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hv1, htr1⟩
  have hpc1_204 : s1.pc = (blkPl_204).base := hpc1
  have hmp_on_203 := lsjump_blk (callerProg := (blkPC_203).rebase (blkPl_203).base H)
    hcl1 (by decide) (by decide) (by decide)
    (verifySignatureMultipart_sepWP_placed P H hWF hH s1 fsp pkPtr (fsp + 1248#64) msgPtr sigPtr
      ((blkPl_203).base + 28#64) pk m sig
      (((fsp + 1264#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((fsp + 1272#64) ↦₆₄ retAddr) ∗ Frame)
      hcl1 hro1 hpk hm hsig hfsp_align hrun1 hpc1_204 hsp1 hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx30_1)
  apply verifySig_seq_seg hmp_on_203
    (Entails.of_eq (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl))
  intro s2 hpc2 hrun2 ⟨_, _, hsp2, hx0_2, h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2,
    h27_2, h28_2, _, hv2, htr2⟩
  apply verifySig_end_seg
    (verifySignature_epilogue_placed H s2 fsp msgPtr (BitVec.ofNat 64 m.length)
      (s.readReg64 (.gpr 29#5)) retAddr
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗ Frame)
      hfsp_align hrun2 hpc2 hsp2)
    (Entails.of_eq (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl))
  intro s3 P3 hP3 ⟨hrun3, hpc3, hsp3, hx0_3, h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3,
    h27_3, h28_3, h29_3, hv3, htr3⟩
  rw [hWF.sigVerify_eq_xeddsaVerifyRef pk m sig]
  exact ⟨Entails.trans hP3 (Entails.of_eq (by ac_rfl)), hrun3, hpc3, hsp3,
    hx0_3.trans hx0_2,
    h19_3.trans (h19_2.trans h19_1), h20_3.trans (h20_2.trans h20_1),
    h21_3.trans (h21_2.trans h21_1), h22_3.trans (h22_2.trans h22_1),
    h23_3.trans (h23_2.trans h23_1), h24_3.trans (h24_2.trans h24_1),
    h25_3.trans (h25_2.trans h25_1), h26_3.trans (h26_2.trans h26_1),
    h27_3.trans (h27_2.trans h27_1), h28_3.trans (h28_2.trans h28_1),
    h29_3, hv3.trans (hv2.trans hv1), htr3.trans (htr2.trans htr1)⟩

/-- Ghost arguments of `<libsignal_core::curve::PublicKey>::verify_signature` (Block `203`). -/
structure VerifySignaturePlacedGhost where
  pkPtr : BitVec 64
  pk : Bytes
  msgPtr : BitVec 64
  m : Bytes
  sigPtr : BitVec 64
  sig : Bytes

/-- Relocatable `Spec` for `<libsignal_core::curve::PublicKey>::verify_signature` (Block `203`). -/
def verifySignatureCallSpec (P : Primitives) : Spec VerifySignaturePlacedGhost where
  pre g s :=
    ⌜s.readReg64 .x0 = g.pkPtr ∧
      s.readReg64 .x1 = g.msgPtr ∧
      s.readReg64 .x2 = BitVec.ofNat 64 g.m.length ∧
      s.readReg64 .x3 = g.sigPtr ∧
      s.readReg64 .x4 = 64#64 ∧
      g.pk.length = 32 ∧
      (g.m.length = 33 ∨ g.m.length = 1569) ∧
      g.sig.length = 64⌝ ∗
      (g.pkPtr ↦ₛ bytesToBv8 g.pk) ∗
      (g.msgPtr ↦ₛ bytesToBv8 g.m) ∗
      (g.sigPtr ↦ₛ bytesToBv8 g.sig) ∗
      stackAt s.sp (pqxdhHookStack + 1280)
  post g s0 sf :=
    ⌜sf.readReg64 .x0 = (if P.sigVerify g.pk g.m g.sig = true then 1#64 else 0#64) ∧
      sf.trace = s0.trace⌝ ∗
      (g.pkPtr ↦ₛ bytesToBv8 g.pk) ∗
      (g.msgPtr ↦ₛ bytesToBv8 g.m) ∗
      (g.sigPtr ↦ₛ bytesToBv8 g.sig) ∗
      stackAt s0.sp (pqxdhHookStack + 1280)

theorem verifySignature_placed_ok' [LibsignalPlacement]
    {P : Primitives} {H : LibsignalHooks}
    (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks' P H) :
    subroutine_ok ((blkPC_203).rebase (blkPl_203).base H)
      (blkPl_203).base
      (withLsCodeRoLoaded lsmpl (verifySignatureCallSpec P)) := by
  refine subroutine_ok_of_sepWP fun g R s0 hpc hrun hpre hsp => ?_
  obtain ⟨⟨hcl, hro_all⟩, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  have hro := sha512IV_placed_holdsBytes hro_all
  dsimp only [verifySignatureCallSpec] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hpk, hm, hsig⟩, hmem⟩
  have hfsp_align : ((s0.sp - 1280#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1280#64 hsp (by decide)
  have hfsp_add : (s0.sp - 1280#64) + 1280#64 = s0.sp := by bv_omega
  refine ⟨((g.pkPtr ↦ₛ bytesToBv8 g.pk) ∗ (g.msgPtr ↦ₛ bytesToBv8 g.m) ∗
      (g.sigPtr ↦ₛ bytesToBv8 g.sig) ∗
      stackAt ((s0.sp - 1280#64) + 1280#64) (pqxdhHookStack + 1280) ∗ emp), R, ?_, ?_⟩
  · rw [hfsp_add, sepConj_emp]
    exact Arm64.Satisfies.of_eq hmem (by ac_rfl)
  · refine SepWP.mono
      (verifySignature_sepWP_placed P H hWF hH s0 (s0.sp - 1280#64)
        g.pkPtr g.msgPtr g.sigPtr (s0.readReg64 Reg.lr)
        g.pk g.m g.sig emp hcl hro hpk hm hsig hfsp_align hrun hpc hfsp_add.symm
        hx0 hx1 hx2 hx3 hx4 rfl) ?_
    intro sf Pf _ _ ⟨hPf, _, _, hsp_f, hx0_f,
      h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hvregs, htr⟩
    refine ⟨fun hsat => ?_, hsp_f.trans hfsp_add,
      ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hvregs⟩⟩
    rw [hfsp_add, sepConj_emp] at hPf
    dsimp only [verifySignatureCallSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_f, htr⟩,
      Arm64.Satisfies.mono (sepConj_mono_left (Entails.trans hPf (Entails.of_eq (by ac_rfl)))) hsat⟩

theorem verifySignature_placed_ok_of_block' [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {P : Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks' P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 203)
      (withLsCodeRoLoaded lsmpl (verifySignatureCallSpec P)) := by
  simpa only [ls_blockPlacement_base] using
    keys_ls_subroutine_ok_of_block_cro (j := 203)
      (verifySignature_placed_ok' hWF hH) hi

theorem verifySignature_placed_frozen_ok_of_block' [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {P : Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks' P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 203)
      (withLsFrozen lsmpl (verifySignatureCallSpec P)) :=
  subroutine_ok_withLsFrozen_of_withLsCodeRoLoaded
    (verifySignature_placed_ok_of_block' hWF hH hi)

/-- `subroutine_ok` for Block `203` (`verify_signature`) on its own block program under
    `[LibsignalPlacement]`. -/
theorem verifySignature_placed_ok [LibsignalPlacement]
    {P : Primitives} {H : LibsignalHooks}
    (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks P H) :
    subroutine_ok ((blkPC_203).rebase (blkPl_203).base H)
      (blkPl_203).base
      (withLsCodeRoLoaded lsmpl (verifySignatureCallSpec P)) :=
  verifySignature_placed_ok' hWF (.of_hooks hH)

theorem verifySignature_placed_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {P : Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 203)
      (withLsCodeRoLoaded lsmpl (verifySignatureCallSpec P)) :=
  verifySignature_placed_ok_of_block' hWF (.of_hooks hH) hi

theorem verifySignature_placed_frozen_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {P : Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 203)
      (withLsFrozen lsmpl (verifySignatureCallSpec P)) :=
  verifySignature_placed_frozen_ok_of_block' hWF (.of_hooks hH) hi

/-! ## Explicit-`h_canon` `[LibsignalPlacement]` Bundle -/

/-- Bundled relocatable contracts on `callerProg` for Curve25519 key-canonicality (`Block 202`,
    parameterized by an arbitrary `canonSpec`) together with XEdDSA signature verification
    (`Blocks 203` and `204`). -/
structure CurveVerifyAndCanonPlacedOk [LibsignalPlacement] {α : Type}
    (P : Primitives) (callerProg : Program) (canonSpec : Spec α) : Prop where
  isCanonical              : subroutine_ok callerProg (lsmpl.base 202) canonSpec
  verifySignature          : subroutine_ok callerProg (lsmpl.base 203)
                               (withLsCodeRoLoaded lsmpl (verifySignatureCallSpec P))
  verifySignatureMultipart : subroutine_ok callerProg (lsmpl.base 204)
                               (withLsCodeRoLoaded lsmpl (verifySignatureMultipartCallSpec P))

theorem curveVerifyAndCanon_placed_ok_of_canon' [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i : Nat} {P : Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    {canonSpec : Spec α}
    (h_canon : subroutine_ok callerProg (lsmpl.base 202) canonSpec)
    (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks' P H)
    (hi : i < 619 := by decide) :
    CurveVerifyAndCanonPlacedOk P callerProg canonSpec where
  isCanonical              := h_canon
  verifySignature          := verifySignature_placed_ok_of_block' hWF hH hi
  verifySignatureMultipart := verifySignatureMultipart_placed_ok_of_block' hWF hH hi

/-- Primary `[LibsignalPlacement]` modularity theorem: given an explicit contract `h_canon` for
    Block `202` (`PublicKey::is_canonical` — either the real contract or a mutated disproof
    contract), provides the combined Curve25519 canonicality + signature verification bundle
    without requiring `[LibsignalFullPlacement]`. -/
theorem curveVerifyAndCanon_placed_ok_of_canon [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i : Nat} {P : Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    {canonSpec : Spec α}
    (h_canon : subroutine_ok callerProg (lsmpl.base 202) canonSpec)
    (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks P H)
    (hi : i < 619 := by decide) :
    CurveVerifyAndCanonPlacedOk P callerProg canonSpec :=
  curveVerifyAndCanon_placed_ok_of_canon' h_canon hWF (.of_hooks hH) hi

/-! ## `[LibsignalFullPlacement]` Corollaries -/

theorem verifySignatureMultipart_full_placed_ok' [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {P : Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hH : VerifySignaturePlacedHooks' P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 204)
      (withLsCodeRoLoaded lsmpl (verifySignatureMultipartCallSpec P)) :=
  verifySignatureMultipart_placed_ok_of_block' (.of_structuralPrims hWF) hH hi

theorem verifySignature_full_placed_ok' [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {P : Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hH : VerifySignaturePlacedHooks' P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 203)
      (withLsCodeRoLoaded lsmpl (verifySignatureCallSpec P)) :=
  verifySignature_placed_ok_of_block' (.of_structuralPrims hWF) hH hi

theorem curveVerifyAndCanon_full_placed_ok'_placed [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {P : Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hisCanon : ∀ k, P.isCanonicalEC k = isCanonicalRef P k)
    (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks' P H)
    (htorsHook : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubSpec P.isTorsionFree 160))
    (hi : i < 619 := by decide) :
    CurveVerifyAndCanonPlacedOk P callerProg
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)) :=
  curveVerifyAndCanon_placed_ok_of_canon'
    (isCanonical_placed_ok'_cl_placed hisCanon hWF.montToEd_len hH.montToEd htorsHook)
    hWF hH hi

theorem curveVerifyAndCanon_full_placed_ok_placed [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {P : Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hH : VerifySignaturePlacedHooks' P H)
    (htorsHook : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubSpec P.isTorsionFree 160))
    (hi : i < 619 := by decide) :
    CurveVerifyAndCanonPlacedOk P callerProg
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)) :=
  curveVerifyAndCanon_placed_ok_of_canon'
    (isCanonical_placed_ok_cl_placed hWF hH.montToEd htorsHook)
    (.of_structuralPrims hWF) hH hi

theorem verifySignatureMultipart_full_placed_ok [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {P : Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hH : VerifySignaturePlacedHooks P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 204)
      (withLsCodeRoLoaded lsmpl (verifySignatureMultipartCallSpec P)) :=
  verifySignatureMultipart_full_placed_ok' hWF (.of_hooks hH) hi

theorem verifySignature_full_placed_ok [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {P : Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hH : VerifySignaturePlacedHooks P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 203)
      (withLsCodeRoLoaded lsmpl (verifySignatureCallSpec P)) :=
  verifySignature_full_placed_ok' hWF (.of_hooks hH) hi

theorem curveVerifyAndCanon_full_placed_ok' [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {P : Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hisCanon : ∀ k, P.isCanonicalEC k = isCanonicalRef P k)
    (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks P H)
    (htorsHook : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubSpec P.isTorsionFree 160))
    (hi : i < 619 := by decide) :
    CurveVerifyAndCanonPlacedOk P callerProg
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)) :=
  curveVerifyAndCanon_full_placed_ok'_placed hisCanon hWF (.of_hooks hH) htorsHook hi

theorem curveVerifyAndCanon_full_placed_ok [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {P : Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hH : VerifySignaturePlacedHooks P H)
    (htorsHook : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubSpec P.isTorsionFree 160))
    (hi : i < 619 := by decide) :
    CurveVerifyAndCanonPlacedOk P callerProg
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)) :=
  curveVerifyAndCanon_full_placed_ok_placed hWF (.of_hooks hH) htorsHook hi

end CryptoVerification.E2E.Pqxdh.Shared
