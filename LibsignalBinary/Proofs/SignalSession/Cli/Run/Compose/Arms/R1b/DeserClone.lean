/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneErr
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParse
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpk
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpk
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.RoFrame
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# Stage 4a (`spk` / `kpk` Deserialization and Heap Signature Clones) of Arm `R1b` (`0x24ec → 0x25f4`)

Proves `r1b_step_deser_clone`, deserializing `spkKey` via `<PublicKey>::deserialize` (`0x24ec → 0x24fc`),
cloning the 64-byte `spkSig` onto the heap (`0x251c → 0x2584`), deserializing `kpkKey` via
`<kem::Key<Public>>::deserialize` (`0x2584 → 0x2594`), and cloning `kpkSig` onto the heap
(`0x2594 → 0x25f4`) to establish `readBundleV = some bundle`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

gen_decodes CryptoVerification.libsignalSessionCode_tree r1bDecDeserClone
  [(ls_off% "libsignal_cli::run" + 0x24ec) → (ls_off% "libsignal_cli::run" + 0x25f4),
   (ls_off% "libsignal_cli::run" + 0x2634) → (ls_off% "libsignal_cli::run" + 0x26a8),
   (ls_off% "libsignal_cli::run" + 0x26cc) → (ls_off% "libsignal_cli::run" + 0x2740)]


set_option maxHeartbeats 800000 in
/-- Second half of Stage 4a (`0x2584 → 0x25f4`): deserializes `kpkKey`, clones `kpkSig` onto the heap (`kpkSigPtr`), and establishes `readBundleV = some bundle`. -/
private theorem r1b_step_kpk_clone_2584 {S : RunSem} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {needs : RunNeeds}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {kpkCap kpkPtr spkCap spkPtr regCap regPtr spkSigPtr : BitVec 64}
    {kpkBs kpkKey kpkSig spkBs spkKey spkSig opkBs : List (BitVec 8)}
    {kpkId spkId v11c : BitVec 32}
    {spk : PublicKey}
    {spkW0 : BitVec 64} {spkW8 spkW12 : BitVec 32} {spkW16 spkW24 : BitVec 64}
    {opk : Option (BitVec 32 × PublicKey)}
    {b0 b1 b2 b3 b4 b5 b6 : BitVec 8}
    {w0e0 w0e4 w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64} {b31 : BitVec 8}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hc : RunCallees img A ext B (slotsOf A img S needs))
    (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hok : r1b_OkCtx S img ext g d s0 s 0x2584)
    (hreg_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") =
      .ok [r0, r1, r2, r3])
    (hspk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs)
    (hspk_sp : splitSigned spkBs = some (spkId, spkKey, spkSig))
    (hspk_d : PublicKey.deserialize spkKey = .ok spk)
    (hspk_bytes : spk.bytes.toList = r1b_spkBytesOf spkW0 spkW8 spkW12 spkW16 spkW24)
    (hspk_ptr : spkSigPtr ≠ 0)
    (hspk_sig : spkSig.length = 64)
    (hkpk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") = .ok kpkBs)
    (hkpk_sp : splitSigned kpkBs = some (kpkId, kpkKey, kpkSig))
    (hopk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") = .ok opkBs)
    (hopk_sem : (opkBs = [] ∧ opk = none) ∨
      (∃ opkId opkKey opkPk, opkBs ≠ [] ∧ splitId opkBs = some (opkId, opkKey) ∧
        PublicKey.deserialize opkKey = .ok opkPk ∧ opk = some (opkId, opkPk)))
    (hx23 : s.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64)
    (hx24 : s.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length)
    (hx26 : s.readReg64 (.gpr 26#5) = spkSigPtr)
    (hx27 : s.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64)
    (hx28 : s.readReg64 (.gpr 28#5) = 64#64)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp)
    (hk : ∀ (sf : State) (kpk : List (BitVec 8)) (kpkSigPtr kpkBuf : BitVec 64),
      r1b_OkCtx S img ext g d s0 sf 0x25f4 →
      readBundleV (runFiles g.i) d.dir d.peerV.device = some {
        idKey := d.idKey, regId := ofLe32 r0 r1 r2 r3, device := d.peerV.device,
        spkId := spkId, spk := spk, spkSig := spkSig,
        kpkId := kpkId, kpk := kpk, kpkSig := kpkSig, opk := opk
      } →
      spk.bytes.toList = r1b_spkBytesOf spkW0 spkW8 spkW12 spkW16 spkW24 →
      (spkSigPtr ≠ 0 ∧ kpkSigPtr ≠ 0 ∧ kpkBuf ≠ 0) →
      (spkSig.length = 64 ∧ kpkSig.length = 64 ∧ kpk.length = 1568) →
      sf.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
      sf.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 →
      sf.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length →
      sf.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64 →
      sf.readReg64 (.gpr 28#5) = 64#64 →
      let fsp := runFsp s0
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (memRegion (fsp + 0x4d0#64) 48 ∗
          A.live spkSigPtr 64 1 ∗ (spkSigPtr ↦ₛ spkSig) ∗
          A.live kpkSigPtr 64 1 ∗ (kpkSigPtr ↦ₛ kpkSig) ∗
          A.live kpkBuf 1568 1 ∗ (kpkBuf ↦ₛ kpk) ∗
          ownedBytes A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
          ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCoreBase A img g d s0 ∗ logOff img ∗
          ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          r1b_opkStage1SpkAt fsp spkW0 spkW8 spkW16 spkW24
            b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ∗
          ((fsp + 0x110#64) ↦₆₄ spkSigPtr) ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
          ((fsp + 0x120#64) ↦₆₄ 64#64) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
          ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
          ((fsp + 0x138#64) ↦₆₄ kpkSigPtr) ∗
          ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
          ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
          ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
          ((fsp + 0x158#64) ↦₆₄ 64#64) ∗
          ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          ((fsp + 0x178#64) ↦₆₄ kpkBuf) ∗
          ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool)
        Q Qp (runOom s0)) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (memRegion (fsp + 0x4d0#64) 24 ∗ memRegion (fsp + 0x4e8#64) 24 ∗
        A.live spkSigPtr 64 1 ∗ (spkSigPtr ↦ₛ spkSig) ∗
        ownedBytes A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
        r1b_invCoreBase A img g d s0 ∗ logOff img ∗
        ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        r1b_opkStage1SpkAt fsp spkW0 spkW8 spkW16 spkW24
          b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ∗
        memRegion (fsp + 0x110#64) 8 ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        ((fsp + 0x120#64) ↦₆₄ 64#64) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
        ((fsp + 0x138#64) ↦₆₄ BitVec.ofNat 64 kpkKey.length) ∗
        ((fsp + 0x140#64) ↦₆₄ (kpkPtr + 4#64)) ∗
        ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
        ((fsp + 0x158#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
        ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ∗
        ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool)
      Q Qp (runOom s0) := by
  intro fsp
  let _ := hx23; let _ := hx24; let _ := hx25; let _ := hx26; let _ := hx27; let _ := hx28
  have hst := hok.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hal138 : (fsp + 0x138#64) &&& 7#64 = 0#64 := by bv_bits
  have hal130 : (fsp + 0x130#64) &&& 7#64 = 0#64 := by bv_bits
  let _ := hal; let _ := hal138; let _ := hal130
  have ⟨hkpk_cat, hkpk_t4, hkpk_sig_len, hkpk_len_eq⟩ := r1b_splitSigned_bytes hkpk_sp
  rw [ProofLib.memRegion_eight (fsp + 0x110#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v110_in => ?_
  refine r1b_sepWPp_frame (by r1b_ac)
    (Entails.of_eq (r1b_ownedBytes_borrow A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs))
    (by r1b_ac) ?_
  simp only [sepConj_assoc]
  refine r1b_sepWPp_pure_left fun ⟨_, hkpk_le, hkpk_cap63, hkpk_ne⟩ => ?_
  have hkpk_key63 : kpkKey.length < 2 ^ 63 := by omega
  rw [r1b_splitSigned_slice_eq (ptr := kpkPtr) hkpk_cat hkpk_t4]
  simp only [sepConj_assoc]
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecDeserClone img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x2584 0x70
  have hpc0 := hst.pc
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc0 ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage
    (mid := fnBase + bv% ((2 ^ 64 +
      ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize" -
      ls_off% "libsignal_cli::run") % 2 ^ 64)) hst.inv
  have hpc := hpc0; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  clear hpc hrun hsp
  refine r1b_bind_state fun sm1 hsm1 hinv1 => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  try rw [hx26]
  refine r1b_call_frame <|
    r1b_call_kemDeserialize hh hc hbnd hinv1
      (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm, hst.run])
      (by simpa [hsm1, arm64_norm] using hst.sp)
      (by simpa [hsm1, arm64_norm] using hst.fp)
      (by simpa [calleeSavedVRegs, hsm1, arm64_norm] using hst.vregs)
      hst.spAligned (retOff := 0x2594)
      (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm])
      (r := fsp + 0x4d0#64) (p := kpkPtr + 4#64) (bs := kpkKey)
      (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm])
      hkpk_key63
      (by simpa [hsm1, arm64_norm] using hok.trace) hpanic
      (fun sf1 hin1 hcs1 hfs1 htr1 => ?_)
  have hok1 : r1b_OkCtx S img ext g d s0 sf1 0x2594 := hok.after_call
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
    hin1 hcs1 hfs1 htr1
  have hx23_1 : sf1.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 :=
    hcs1.2.2.2.2.1.trans (by first | (simp [hsm1, arm64_norm]; done) | simpa [hsm1, arm64_norm] using hx23)
  have hx24_1 : sf1.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 :=
    hcs1.2.2.2.2.2.1.trans (by first | (simp [hsm1, arm64_norm]; done) | simpa [hsm1, arm64_norm] using hx24)
  have hx25_1 : sf1.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length :=
    hcs1.2.2.2.2.2.2.1.trans (by first | (simp [hsm1, arm64_norm]; done) | simpa [hsm1, arm64_norm] using hx25)
  have hx27_1 : sf1.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64 :=
    hcs1.2.2.2.2.2.2.2.2.1.trans (by first | (simp [hsm1, arm64_norm]; done) | simpa [hsm1, arm64_norm] using hx27)
  have hx28_1 : sf1.readReg64 (.gpr 28#5) = 64#64 :=
    hcs1.2.2.2.2.2.2.2.2.2.1.trans (by first | (simp [hsm1, arm64_norm]; done) | simpa [hsm1, arm64_norm] using hx28)
  let _ := hx23_1; let _ := hx24_1; let _ := hx25_1; let _ := hx27_1; let _ := hx28_1
  have hkpk_rejoin :
      ((kpkPtr ↦ₛ kpkBs.take 4) ∗ ((kpkPtr + 4#64) ↦ₛ kpkKey) ∗
        ((kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length) ↦ₛ kpkSig) ∗
        r1b_ownedRest A kpkCap kpkPtr kpkBs.length) ⊢
      ownedBytes A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs := by
    refine Entails.trans (r1b_entails_frame (by r1b_ac)
      (Entails.of_eq (r1b_splitSigned_slice_eq (ptr := kpkPtr) hkpk_cat hkpk_t4).symm) (by r1b_ac)) ?_
    exact r1b_ownedBytes_rejoin A kpkCap kpkPtr kpkBs hkpk_le hkpk_cap63 hkpk_ne
  cases hkpk_d : RunProofs.kemPkDeserialize kpkKey with
  | noKeyType =>
    have hc1 := hok1.to_err
      (r1b_none_kpk_deser hkpk_rd hkpk_sp fun _ h => by rw [hkpk_d] at h; cases h)
    dsimp only [RunProofs.kemDeserResAt]
    refine r1b_sepWPp_frame (by r1b_ac) hkpk_rejoin (by r1b_ac) ?_
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [r1b_split_region fsp 0x4d8 8 8,
      ProofLib.memRegion_eight (fsp + 0x4d8#64),
      ProofLib.memRegion_eight (fsp + 0x4e0#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun w4d8 => SepWPp.exists_elim fun w4e0 => ?_
    dsimp only [speWord]
    have hpc1 := hin1.pc
    dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc1 ⊢
    rw [heq_fnBase] at hpc1
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2654#64) hin1.inv
    have hpc := hpc1; have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state fun sm2 hsm2 hinv2 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hc2 : r1b_ErrCtx img ext g d s0 sm2 0x2654 := hc1.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm]
        run := by simp [hsm2, arm64_norm, hin1.run]
        sp := by simpa [hsm2, arm64_norm] using hin1.sp
        fp := by simpa [hsm2, arm64_norm] using hin1.fp
        inv := hinv2
        vregs := by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs
        spAligned := hst.spAligned }
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
    exact MainHops.sepWPp_weaken_pre (Entails.of_eq (by dsimp only [speWord]; r1b_ac))
      (r1b_kem_err_2654 (i := 7) hh hdrop hbnd hc2 (by decide) hspk_ptr hspk_sig hpanic hrej)
  | badType t =>
    have hc1 := hok1.to_err
      (r1b_none_kpk_deser hkpk_rd hkpk_sp fun _ h => by rw [hkpk_d] at h; cases h)
    dsimp only [RunProofs.kemDeserResAt]
    have h4d8 : ((fsp + 0x4d0#64 + 8#64) ↦₈ t) ∗ memRegion (fsp + 0x4d0#64 + 9#64) 15 ⊢
        memRegion (fsp + 0x4d8#64) 16 := by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      refine Entails.trans (sepConj_mono_left (r1b_cell8_to_region _ _)) ?_
      rw [r1b_join_region fsp 0x4d8 1 15]; exact Entails.refl _
    refine r1b_sepWPp_frame (by r1b_ac) (sepConj_mono hkpk_rejoin h4d8) (by r1b_ac) ?_
    rw [r1b_split_region fsp 0x4d8 8 8,
      ProofLib.memRegion_eight (fsp + 0x4d8#64),
      ProofLib.memRegion_eight (fsp + 0x4e0#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, sepConj_assoc]
    refine SepWPp.exists_elim fun w4d8 => SepWPp.exists_elim fun w4e0 => ?_
    dsimp only [speWord]
    have hpc1 := hin1.pc
    dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc1 ⊢
    rw [heq_fnBase] at hpc1
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2654#64) hin1.inv
    have hpc := hpc1; have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state fun sm2 hsm2 hinv2 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hc2 : r1b_ErrCtx img ext g d s0 sm2 0x2654 := hc1.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm]
        run := by simp [hsm2, arm64_norm, hin1.run]
        sp := by simpa [hsm2, arm64_norm] using hin1.sp
        fp := by simpa [hsm2, arm64_norm] using hin1.fp
        inv := hinv2
        vregs := by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs
        spAligned := hst.spAligned }
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
    exact MainHops.sepWPp_weaken_pre (Entails.of_eq (by dsimp only [speWord]; r1b_ac))
      (r1b_kem_err_2654 (i := 31) hh hdrop hbnd hc2 (by decide) hspk_ptr hspk_sig hpanic hrej)
  | badLength n =>
    have hc1 := hok1.to_err
      (r1b_none_kpk_deser hkpk_rd hkpk_sp fun _ h => by rw [hkpk_d] at h; cases h)
    dsimp only [RunProofs.kemDeserResAt]
    refine r1b_sepWPp_frame (by r1b_ac) hkpk_rejoin (by r1b_ac) ?_
    rw [show fsp + 0x4d0#64 + 16#64 = fsp + 0x4e0#64 from by bv_omega,
      ProofLib.memRegion_eight (fsp + 0x4e0#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc,
      BitVec.reduceAdd]
    refine SepWPp.exists_elim fun w4e0 => ?_
    dsimp only [speWord]
    have hpc1 := hin1.pc
    dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc1 ⊢
    rw [heq_fnBase] at hpc1
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2654#64) hin1.inv
    have hpc := hpc1; have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state fun sm2 hsm2 hinv2 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hc2 : r1b_ErrCtx img ext g d s0 sm2 0x2654 := hc1.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm]
        run := by simp [hsm2, arm64_norm, hin1.run]
        sp := by simpa [hsm2, arm64_norm] using hin1.sp
        fp := by simpa [hsm2, arm64_norm] using hin1.fp
        inv := hinv2
        vregs := by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs
        spAligned := hst.spAligned }
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
    exact MainHops.sepWPp_weaken_pre (Entails.of_eq (by dsimp only [speWord]; r1b_ac))
      (r1b_kem_err_2654 (i := 33) hh hdrop hbnd hc2 (by decide) hspk_ptr hspk_sig hpanic hrej)
  | ok kpk =>
    have hbundle := r1b_readBundleV_some (dev := d.peerV.device) hok.ikSem hreg_rd hspk_rd hspk_sp
      hkpk_rd hkpk_sp hopk_rd hopk_sem hspk_d hkpk_d
    have h1568 : kpk.length = 1568 := (readBundleV_slice_lengths hbundle).2.2
    dsimp only [RunProofs.kemDeserResAt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc,
      BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.exists_elim fun kpkBuf => ?_
    refine r1b_sepWPp_frame (by r1b_ac)
      (r1b_box1568_unpack A (fsp + 0x4d8#64) kpkBuf kpk h1568) (by r1b_ac) ?_
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine MainHops.sepWPp_weaken_pre (Entails.of_eq (by r1b_ac))
      (r1b_sepWPp_pure_left (φ := kpkBuf ≠ 0) fun hkpk_buf => ?_)
    have hpc1 := hin1.pc
    dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc1 ⊢
    rw [heq_fnBase] at hpc1
    apply MainHops.sepWPp_seq_inImage
      (mid := fnBase + bv% ((2 ^ 64 +
        ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]" -
        ls_off% "libsignal_cli::run") % 2 ^ 64)) hin1.inv
    have hpc := hpc1; have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state fun sm2 hsm2 hinv2 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have h4d0_24 :
        ((fsp + 0x4d0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((fsp + 0x4d8#64) ↦₆₄ kpkBuf) ∗ ((fsp + 0x4e0#64) ↦₆₄ 1568#64) ⊢
          memRegion (fsp + 0x4d0#64) 24 := by
      refine Entails.trans (sepConj_mono_right (by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          r1b_cells2_to_region16 (fsp + 0x4d8#64) kpkBuf 1568#64)) ?_
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        r1b_cell64_cons (a := fsp + 0x4d0#64) 0xfffffffffffffffe#64 (n := 16) (by decide)
    refine r1b_sepWPp_frame (by r1b_ac) h4d0_24 (by r1b_ac) ?_
    refine r1b_call_frame <|
      r1b_call_tryAlloc hh hbnd hinv2
        (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm, hin1.run])
        (by simpa [hsm2, arm64_norm] using hin1.sp)
        (by simpa [hsm2, arm64_norm] using hin1.fp)
        (by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs)
        hst.spAligned (retOff := 0x25c8)
        (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm])
        (out := fsp + 0x4d0#64) (new := 64#64) (align := 1#64) (stride := 1#64)
        (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm])
        (by decide) (by decide) (r1b_layout1 64) hpanic
        (fun sf2 hin2 _ _ htr_err => ?_)
        (fun sf2 kpkSigPtr hin2 hcs2 hkpk_ptr hfs2 htr2 => ?_)
    ·
      simp only [Nat.reduceMul, Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod,
        BitVec.add_assoc, BitVec.reduceAdd]
      have hpc2 := hin2.pc
      dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc2 ⊢
      rw [heq_fnBase] at hpc2
      apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2d74#64) hin2.inv
      have hpc := hpc2; have hrun := hin2.run; have hsp : sf2.sp = fsp := hin2.sp
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      clear hpc hrun hsp
      refine r1b_bind_state fun sm3 hsm3 hinv3 => ?_
      change SepWPp (mProg img ext) _ _ _ _ _ _
      have hin3 : InRun img ext s0 sm3 0x2d74 := {
        pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm3, arm64_norm]
        run := by simp [hsm3, arm64_norm, hin2.run]
        sp := by simpa [hsm3, arm64_norm] using hin2.sp
        fp := by simpa [hsm3, arm64_norm] using hin2.fp
        inv := hinv3
        vregs := by simpa [calleeSavedVRegs, hsm3, arm64_norm] using hin2.vregs
        spAligned := hst.spAligned
      }
      have hfail : allocFailedIn s0 sm3 :=
        r1b_allocFailedIn_mono
          (r1b_allocFailed_of_null (by simpa [hsm2, arm64_norm] using hok1.trace) htr_err)
          (by simp [hsm3, arm64_norm])
      exact r1b_call_frame <|
        r1b_oom_2d74 (v0 := 1#64) (v1 := 64#64)
          hin3 hpanic hfail
    ·
      have hok2 : r1b_OkCtx S img ext g d s0 sf2 0x25c8 := hok1.after_call
        (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        hin2 hcs2 (congrArg FsState.files hfs2) htr2
      have hx23_2 : sf2.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 :=
        hcs2.2.2.2.2.1.trans (by first | (simp [hsm2, arm64_norm]; done) | simpa [hsm2, arm64_norm] using hx23_1)
      have hx24_2 : sf2.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 :=
        hcs2.2.2.2.2.2.1.trans (by first | (simp [hsm2, arm64_norm]; done) | simpa [hsm2, arm64_norm] using hx24_1)
      have hx25_2 : sf2.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length :=
        hcs2.2.2.2.2.2.2.1.trans (by first | (simp [hsm2, arm64_norm]; done) | simpa [hsm2, arm64_norm] using hx25_1)
      have hx27_2 : sf2.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64 :=
        hcs2.2.2.2.2.2.2.2.2.1.trans (by first | (simp [hsm2, arm64_norm]; done) | simpa [hsm2, arm64_norm] using hx27_1)
      have hx28_2 : sf2.readReg64 (.gpr 28#5) = 64#64 :=
        hcs2.2.2.2.2.2.2.2.2.2.1.trans (by first | (simp [hsm2, arm64_norm]; done) | simpa [hsm2, arm64_norm] using hx28_1)
      let _ := hx23_2; let _ := hx24_2; let _ := hx25_2; let _ := hx27_2; let _ := hx28_2
      simp only [Nat.reduceMul, Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod,
        BitVec.add_assoc, BitVec.reduceAdd]
      have hpc2 := hin2.pc
      dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc2 ⊢
      rw [heq_fnBase] at hpc2
      apply MainHops.sepWPp_seq_inImage
        (mid := fnBase + bv% (ls_off% "memcpy" - ls_off% "libsignal_cli::run")) hin2.inv
      have hpc := hpc2; have hrun := hin2.run; have hsp : sf2.sp = fsp := hin2.sp
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      clear hpc hrun hsp
      refine r1b_bind_state fun sm3 hsm3 hinv3 => ?_
      change SepWPp (mProg img ext) _ _ _ _ _ _
      rw [show memRegion kpkSigPtr 64 = memRegion kpkSigPtr kpkSig.length from by rw [hkpk_sig_len]]
      refine r1b_call_frame <|
        r1b_call_memcpy_region hh hbnd hinv3
          (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm3, arm64_norm])
          (by simp [hsm3, arm64_norm, hin2.run])
          (by simpa [hsm3, arm64_norm] using hin2.sp)
          (by simpa [hsm3, arm64_norm] using hin2.fp)
          (by simpa [calleeSavedVRegs, hsm3, arm64_norm] using hin2.vregs)
          hst.spAligned (retOff := 0x25f4)
          (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm3, arm64_norm])
          (dst := kpkSigPtr) (src := kpkPtr + (4#64 + BitVec.ofNat 64 kpkKey.length)) (bs := kpkSig)
          (by simp [hsm3, arm64_norm])
          (by simp [hsm3, arm64_norm])
          (by simp only [hsm3, arm64_norm, hkpk_sig_len]; try rw [hx28_2])
          hpanic
          (fun sf3 hin3 hcs3 _ hfs3 htr3 => ?_)
      have hok3 : r1b_OkCtx S img ext g d s0 sf3 0x25f4 := hok2.after_call
        (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
        (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
        (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
        hin3 hcs3 (congrArg FsState.files hfs3) htr3
      have h4d0_48 :
          ((fsp + 0x4d0#64) ↦₆₄ 0#64) ∗ ((fsp + 0x4d8#64) ↦₆₄ 64#64) ∗
            ((fsp + 0x4e0#64) ↦₆₄ kpkSigPtr) ∗ memRegion (fsp + 0x4e8#64) 24 ⊢
            memRegion (fsp + 0x4d0#64) 48 := by
        have h24 :
            ((fsp + 0x4d0#64) ↦₆₄ 0#64) ∗ ((fsp + 0x4d8#64) ↦₆₄ 64#64) ∗
              ((fsp + 0x4e0#64) ↦₆₄ kpkSigPtr) ⊢ memRegion (fsp + 0x4d0#64) 24 := by
          refine Entails.trans (sepConj_mono_right (by
            simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
              r1b_cells2_to_region16 (fsp + 0x4d8#64) 64#64 kpkSigPtr)) ?_
          simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
            r1b_cell64_cons (a := fsp + 0x4d0#64) 0#64 (n := 16) (by decide)
        refine Entails.trans (Entails.of_eq (show _ =
            (((fsp + 0x4d0#64) ↦₆₄ 0#64) ∗ ((fsp + 0x4d8#64) ↦₆₄ 64#64) ∗
              ((fsp + 0x4e0#64) ↦₆₄ kpkSigPtr)) ∗ memRegion (fsp + 0x4e8#64) 24 by r1b_ac))
          (Entails.trans (sepConj_mono_left h24) ?_)
        rw [r1b_join_region fsp 0x4d0 24 24]; exact Entails.refl _
      rw [show kpkPtr + (4#64 + BitVec.ofNat 64 kpkKey.length) =
        kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length from (BitVec.add_assoc _ _ _).symm]
      refine r1b_sepWPp_frame (by r1b_ac) (sepConj_mono hkpk_rejoin h4d0_48) (by r1b_ac) ?_
      exact MainHops.sepWPp_weaken_pre (Entails.of_eq (by r1b_ac))
        (hk sf3 kpk kpkSigPtr kpkBuf hok3 hbundle hspk_bytes
          ⟨hspk_ptr, hkpk_ptr, hkpk_buf⟩
          ⟨hspk_sig, hkpk_sig_len, h1568⟩
          (hcs3.2.2.2.2.1.trans (by first | (simp [hsm3, arm64_norm]; done) | simpa [hsm3, arm64_norm] using hx23_2))
          (hcs3.2.2.2.2.2.1.trans (by first | (simp [hsm3, arm64_norm]; done) | simpa [hsm3, arm64_norm] using hx24_2))
          (hcs3.2.2.2.2.2.2.1.trans (by first | (simp [hsm3, arm64_norm]; done) | simpa [hsm3, arm64_norm] using hx25_2))
          (hcs3.2.2.2.2.2.2.2.2.1.trans (by first | (simp [hsm3, arm64_norm]; done) | simpa [hsm3, arm64_norm] using hx27_2))
          (hcs3.2.2.2.2.2.2.2.2.2.1.trans (by first | (simp [hsm3, arm64_norm]; done) | simpa [hsm3, arm64_norm] using hx28_2)))

set_option maxHeartbeats 800000 in
/-- Full Stage 4a step (`0x24ec → 0x25f4`): deserializes `spk` and `kpk`, clones `spkSig` and `kpkSig` onto the heap, and establishes `readBundleV = some bundle`. -/
theorem r1b_step_deser_clone {S : RunSem} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {needs : RunNeeds}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {kpkCap kpkPtr spkCap spkPtr regCap regPtr : BitVec 64}
    {kpkBs kpkKey kpkSig spkBs spkKey spkSig opkBs : List (BitVec 8)}
    {kpkId spkId v11c : BitVec 32}
    {opk : Option (BitVec 32 × PublicKey)}
    {b0 b1 b2 b3 b4 b5 b6 : BitVec 8}
    {w0e0 w0e4 w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64} {b31 : BitVec 8}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hc : RunCallees img A ext B (slotsOf A img S needs))
    (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hok : r1b_OkCtx S img ext g d s0 s 0x24ec)
    (hreg_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") =
      .ok [r0, r1, r2, r3])
    (hspk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs)
    (hspk_sp : splitSigned spkBs = some (spkId, spkKey, spkSig))
    (hkpk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") = .ok kpkBs)
    (hkpk_sp : splitSigned kpkBs = some (kpkId, kpkKey, kpkSig))
    (hopk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") = .ok opkBs)
    (hopk_sem : (opkBs = [] ∧ opk = none) ∨
      (∃ opkId opkKey opkPk, opkBs ≠ [] ∧ opkBs.length < 2 ^ 63 ∧
        splitId opkBs = some (opkId, opkKey) ∧
        PublicKey.deserialize opkKey = .ok opkPk ∧ opk = some (opkId, opkPk) ∧
        v11c = opkId ∧
        opkPk.bytes.toList = Wire.pkBytesOf b0 b1 b2 b3 b4 b5 b6
          (w0e4.truncate 8) (w0e0.truncate 8) w9 w13 w15 w23 b31))
    (hx23 : s.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64)
    (hx24 : s.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length)
    (hx27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length)
    (hx28 : s.readReg64 (.gpr 28#5) = 64#64)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp)
    (hk : ∀ (sf : State) (spk : PublicKey) (kpk : List (BitVec 8))
        (spkSigPtr kpkSigPtr kpkBuf : BitVec 64)
        (spkW0 : BitVec 64) (spkW8 spkW12 : BitVec 32) (spkW16 spkW24 : BitVec 64),
      r1b_OkCtx S img ext g d s0 sf 0x25f4 →
      readBundleV (runFiles g.i) d.dir d.peerV.device = some {
        idKey := d.idKey, regId := ofLe32 r0 r1 r2 r3, device := d.peerV.device,
        spkId := spkId, spk := spk, spkSig := spkSig,
        kpkId := kpkId, kpk := kpk, kpkSig := kpkSig, opk := opk
      } →
      spk.bytes.toList = r1b_spkBytesOf spkW0 spkW8 spkW12 spkW16 spkW24 →
      (spkSigPtr ≠ 0 ∧ kpkSigPtr ≠ 0 ∧ kpkBuf ≠ 0) →
      (spkSig.length = 64 ∧ kpkSig.length = 64 ∧ kpk.length = 1568) →
      sf.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
      sf.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 →
      sf.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length →
      sf.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64 →
      sf.readReg64 (.gpr 28#5) = 64#64 →
      let fsp := runFsp s0
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (memRegion (fsp + 0x4d0#64) 48 ∗
          A.live spkSigPtr 64 1 ∗ (spkSigPtr ↦ₛ spkSig) ∗
          A.live kpkSigPtr 64 1 ∗ (kpkSigPtr ↦ₛ kpkSig) ∗
          A.live kpkBuf 1568 1 ∗ (kpkBuf ↦ₛ kpk) ∗
          ownedBytes A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
          ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCoreBase A img g d s0 ∗ logOff img ∗
          ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          r1b_opkStage1SpkAt fsp spkW0 spkW8 spkW16 spkW24
            b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ∗
          ((fsp + 0x110#64) ↦₆₄ spkSigPtr) ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
          ((fsp + 0x120#64) ↦₆₄ 64#64) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
          ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
          ((fsp + 0x138#64) ↦₆₄ kpkSigPtr) ∗
          ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
          ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
          ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
          ((fsp + 0x158#64) ↦₆₄ 64#64) ∗
          ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          ((fsp + 0x178#64) ↦₆₄ kpkBuf) ∗
          ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool)
        Q Qp (runOom s0)) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (memRegion (fsp + 0x4d0#64) 48 ∗
        ownedBytes A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
        r1b_invCoreBase A img g d s0 ∗ logOff img ∗
        ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        r1b_opkStage1At fsp b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ∗
        memRegion (fsp + 0x110#64) 8 ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        memRegion (fsp + 0x120#64) 8 ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
        ((fsp + 0x138#64) ↦₆₄ BitVec.ofNat 64 kpkKey.length) ∗
        ((fsp + 0x140#64) ↦₆₄ (kpkPtr + 4#64)) ∗
        ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
        ((fsp + 0x158#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
        ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ∗
        ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool)
      Q Qp (runOom s0) := by
  intro fsp
  let _ := hx23; let _ := hx24; let _ := hx25; let _ := hx27; let _ := hx28
  have hst := hok.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hal100 : (fsp + 0x100#64) &&& 7#64 = 0#64 := by bv_bits
  let _ := hal; let _ := hal100
  have hopk_sem_b : (opkBs = [] ∧ opk = none) ∨
      (∃ opkId opkKey opkPk, opkBs ≠ [] ∧ splitId opkBs = some (opkId, opkKey) ∧
        PublicKey.deserialize opkKey = .ok opkPk ∧ opk = some (opkId, opkPk)) :=
    hopk_sem.imp id fun ⟨opkId, opkKey, opkPk, h1, _, h2, h3, h4, _, _⟩ =>
      ⟨opkId, opkKey, opkPk, h1, h2, h3, h4⟩
  have ⟨hspk_cat, hspk_t4, hspk_sig_len, hspk_len_eq⟩ := r1b_splitSigned_bytes hspk_sp
  rw [r1b_split_region fsp 0x4d0 33 15]
  simp only [Nat.reduceAdd]
  refine r1b_sepWPp_frame (by r1b_ac)
    (Entails.of_eq (r1b_ownedBytes_borrow A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs))
    (by r1b_ac) ?_
  simp only [sepConj_assoc]
  refine r1b_sepWPp_pure_left fun ⟨_, hspk_le, hspk_cap63, hspk_ne⟩ => ?_
  have hspk_key63 : spkKey.length < 2 ^ 63 := by omega
  have hspk_key_nat : (BitVec.ofNat 64 spkKey.length).toNat = spkKey.length := by
    simp only [BitVec.toNat_ofNat]; omega
  rw [r1b_splitSigned_slice_eq (ptr := spkPtr) hspk_cat hspk_t4]
  simp only [sepConj_assoc]
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecDeserClone img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x24ec 0x9c
  have hpc0 := hst.pc
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc0 ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage
    (mid := fnBase + bv% ((2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey>::deserialize" -
      ls_off% "libsignal_cli::run") % 2 ^ 64)) hst.inv
  have hpc := hpc0; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  clear hpc hrun hsp
  refine r1b_bind_state fun sm1 hsm1 hinv1 => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  refine r1b_call_frame <|
    r1b_call_pkDeserialize himg hh hinv1
      (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm, hst.run])
      (by simpa [hsm1, arm64_norm] using hst.sp)
      (by simpa [hsm1, arm64_norm] using hst.fp)
      (by simpa [calleeSavedVRegs, hsm1, arm64_norm] using hst.vregs)
      hst.spAligned (retOff := 0x24fc)
      (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm])
      (ptr := spkPtr + 4#64) (sret := fsp + 0x4d0#64) (bs := spkKey)
      (by simp [hsm1, arm64_norm])
      (by simp only [hsm1, arm64_norm]; exact hspk_key_nat)
      (by simp [hsm1, arm64_norm])
      hspk_key63 hpanic
      (fun sf1 hin1 hcs1 hfs1 htr1 => ?_)
  have hok1 : r1b_OkCtx S img ext g d s0 sf1 0x24fc := hok.after_call
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
    hin1 hcs1 hfs1 htr1
  have hx23_1 : sf1.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 :=
    hcs1.2.2.2.2.1.trans (by first | (simp [hsm1, arm64_norm]; done) | simpa [hsm1, arm64_norm] using hx23)
  have hx24_1 : sf1.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 :=
    hcs1.2.2.2.2.2.1.trans (by first | (simp [hsm1, arm64_norm]; done) | simpa [hsm1, arm64_norm] using hx24)
  have hx25_1 : sf1.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length :=
    hcs1.2.2.2.2.2.2.1.trans (by first | (simp [hsm1, arm64_norm]; done) | simpa [hsm1, arm64_norm] using hx25)
  have hx28_1 : sf1.readReg64 (.gpr 28#5) = 64#64 :=
    hcs1.2.2.2.2.2.2.2.2.2.1.trans (by first | (simp [hsm1, arm64_norm]; done) | simpa [hsm1, arm64_norm] using hx28)
  let _ := hx23_1; let _ := hx24_1; let _ := hx25_1; let _ := hx28_1
  have hspk_rejoin :
      ((spkPtr ↦ₛ spkBs.take 4) ∗ ((spkPtr + 4#64) ↦ₛ spkKey) ∗
        ((spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length) ↦ₛ spkSig) ∗
        r1b_ownedRest A spkCap spkPtr spkBs.length) ⊢
      ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs := by
    refine Entails.trans (r1b_entails_frame (by r1b_ac)
      (Entails.of_eq (r1b_splitSigned_slice_eq (ptr := spkPtr) hspk_cat hspk_t4).symm) (by r1b_ac)) ?_
    exact r1b_ownedBytes_rejoin A spkCap spkPtr spkBs hspk_le hspk_cap63 hspk_ne
  cases hspk_d : PublicKey.deserialize spkKey with
  | error e =>
    have hc1 := hok1.to_err (r1b_none_spk_deser hspk_rd hspk_sp hspk_d)
    have h11c : ((fsp + 0x11c#64) ↦₃₂ v11c) ⊢ memRegion (fsp + 0x11c#64) 4 :=
      pointsTo32_entails_memRegion _ _
    have h130 :
        ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
          ((fsp + 0x138#64) ↦₆₄ BitVec.ofNat 64 kpkKey.length) ∗
          ((fsp + 0x140#64) ↦₆₄ (kpkPtr + 4#64)) ∗
          ((fsp + 0x148#64) ↦₆₄ 64#64) ⊢ memRegion (fsp + 0x130#64) 0x20 := by
      refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (pointsTo64_entails_memRegion _ _)))) ?_
      rw [r1b_join_region fsp 0x140 8 8, r1b_join_region fsp 0x138 8 16,
        r1b_join_region fsp 0x130 8 24]
      exact Entails.refl _
    have h158 : ((fsp + 0x158#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ⊢
        memRegion (fsp + 0x158#64) 8 := pointsTo64_entails_memRegion _ _
    have h178 : ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ⊢ memRegion (fsp + 0x178#64) 8 :=
      pointsTo64_entails_memRegion _ _
    refine r1b_sepWPp_frame (by r1b_ac)
      (sepConj_mono hspk_rejoin
        (sepConj_mono (r1b_opkStage1_to_regions fsp b0 b1 b2 b3 b4 b5 b6
            w0e0 w0e4 w9 w13 w15 w23 b31)
          (sepConj_mono h11c (sepConj_mono h130 (sepConj_mono h158 h178)))))
      (by r1b_ac) ?_
    have hinv_rejoin :
        r1b_invCoreBase A img g d s0 ∗
          memRegion (fsp + 0x1d0#64) 0x90 ∗ memRegion (fsp + 0x2c0#64) 0x210 ⊢
        r1b_invCore A img g d s0 :=
      Entails.of_eq (r1b_invCore_split_mid A img g d s0).symm
    refine r1b_sepWPp_frame (by r1b_ac) hinv_rejoin (by r1b_ac) ?_
    have herr_c := r1b_stage_to_err A img g d s0 resStack (ofLe32 r0 r1 r2 r3)
    dsimp only at herr_c
    refine r1b_sepWPp_frame (by r1b_ac) herr_c (by r1b_ac) ?_
    exact MainHops.sepWPp_weaken_pre (Entails.of_eq (by r1b_ac))
      (r1b_spk_err_24fc hh hdrop hbnd hc1 hspk_d hpanic hrej)
  | ok spk =>
    rcases r1b_exists_spkBytesOf spk.bytes.toList (by simp) with
      ⟨spkW0, spkW8, spkW12, spkW16, spkW24, hspk_bytes⟩
    dsimp only [Wire.deserializeResult33At]
    rw [hspk_bytes, ← r1b_spkLayoutAt_eq]
    dsimp only [r1b_spkLayoutAt, r1b_opkStage1At]
    rw [r1b_split_region fsp 0x0f0 8 24, r1b_split_region fsp 0x0f8 8 16,
      r1b_split_region fsp 0x100 8 8,
      ProofLib.memRegion_eight (fsp + 0x0f0#64),
      ProofLib.memRegion_eight (fsp + 0x0f8#64),
      ProofLib.memRegion_eight (fsp + 0x100#64),
      ProofLib.memRegion_eight (fsp + 0x108#64),
      ProofLib.memRegion_eight (fsp + 0x120#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc,
      BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.exists_elim fun m0f0 => SepWPp.exists_elim fun m0f8 =>
      SepWPp.exists_elim fun m100 => SepWPp.exists_elim fun m108 =>
      SepWPp.exists_elim fun m120 => ?_
    have hpc1 := hin1.pc
    dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc1 ⊢
    rw [heq_fnBase] at hpc1
    apply MainHops.sepWPp_seq_inImage
      (mid := fnBase + bv% ((2 ^ 64 +
        ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]" -
        ls_off% "libsignal_cli::run") % 2 ^ 64)) hin1.inv
    have hpc := hpc1; have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state fun sm2 hsm2 hinv2 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have h4d0_split :
        ((fsp + 0x4d0#64) ↦₈ 0#8) ∗
          ((fsp + 0x4d1#64) ↦₆₄ spkW0) ∗ ((fsp + 0x4d9#64) ↦₃₂ spkW8) ∗
          ((fsp + 0x4dd#64) ↦₃₂ spkW12) ∗ ((fsp + 0x4e1#64) ↦₆₄ spkW16) ∗
          ((fsp + 0x4e9#64) ↦₆₄ spkW24) ∗ memRegion (fsp + 0x4f1#64) 15 ⊢
          memRegion (fsp + 0x4d0#64) 24 ∗ memRegion (fsp + 0x4e8#64) 24 := by
      have hspk_reg :
          ((fsp + 0x4d1#64) ↦₆₄ spkW0) ∗ ((fsp + 0x4d9#64) ↦₃₂ spkW8) ∗
            ((fsp + 0x4dd#64) ↦₃₂ spkW12) ∗ ((fsp + 0x4e1#64) ↦₆₄ spkW16) ∗
            ((fsp + 0x4e9#64) ↦₆₄ spkW24) ⊢ memRegion (fsp + 0x4d1#64) 32 := by
        have hlay := r1b_spkLayoutAt_eq (fsp + 0x4d1#64) spkW0 spkW8 spkW12 spkW16 spkW24
        dsimp only [r1b_spkLayoutAt] at hlay
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hlay
        rw [hlay, ← hspk_bytes]
        simpa using pointsToBytes_entails_memRegion (fsp + 0x4d1#64) spk.bytes.toList
      refine Entails.trans
        (r1b_entails_frame (by r1b_ac)
          (sepConj_mono (r1b_cell8_to_region _ _) hspk_reg) (by r1b_ac)) ?_
      simp only [sepConj_assoc]
      rw [r1b_join_region fsp 0x4d1 32 15, r1b_join_region fsp 0x4d0 1 47,
        r1b_split_region fsp 0x4d0 24 24]
      exact Entails.of_eq (by r1b_ac)
    have hfold_spk1 :
        (memRegion fsp 0x0e0 ∗
          ((fsp + 0x0e0#64) ↦₃₂ w0e0) ∗ ((fsp + 0x0e4#64) ↦₃₂ w0e4) ∗
          ((fsp + 0x0e8#64) ↦₆₄ w15) ∗
          ((fsp + 0x0f0#64) ↦₆₄ spkW8.zeroExtend 64) ∗
          ((fsp + 0x0f8#64) ↦₆₄ spkW24) ∗
          ((fsp + 0x100#64) ↦₆₄ spkW16) ∗
          ((fsp + 0x108#64) ↦₆₄ spkW0) ∗
          memRegion (fsp + 0x1d0#64) 0x50 ∗
          ((fsp + 0x220#64) ↦₆₄ w23) ∗ ((fsp + 0x228#64) ↦₈ b31) ∗
          memRegion (fsp + 0x229#64) 0x37 ∗
          memRegion (fsp + 0x2c0#64) 0xf8 ∗
          Wire.sevenBytesHeadAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6 ∗
          memRegion (fsp + 0x3bf#64) 0x19 ∗
          ((fsp + 0x3d8#64) ↦₃₂ w9) ∗ ((fsp + 0x3dc#64) ↦₁₆ w13) ∗
          memRegion (fsp + 0x3de#64) 0xf2) ⊢
        r1b_opkStage1SpkAt fsp spkW0 spkW8 spkW16 spkW24
          b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 := by
      dsimp only [r1b_opkStage1SpkAt]; exact Entails.of_eq (by r1b_ac)
    refine r1b_sepWPp_frame (by r1b_ac) (sepConj_mono h4d0_split hfold_spk1) (by r1b_ac) ?_
    refine r1b_call_frame <|
      r1b_call_tryAlloc hh hbnd hinv2
        (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm, hin1.run])
        (by simpa [hsm2, arm64_norm] using hin1.sp)
        (by simpa [hsm2, arm64_norm] using hin1.fp)
        (by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs)
        hst.spAligned (retOff := 0x2554)
        (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm])
        (out := fsp + 0x4d0#64) (new := 64#64) (align := 1#64) (stride := 1#64)
        (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm])
        (by decide) (by decide) (r1b_layout1 64) hpanic
        (fun sf2 hin2 _ _ htr_err => ?_)
        (fun sf2 spkSigPtr hin2 hcs2 hspk_ptr hfs2 htr2 => ?_)
    ·
      simp only [Nat.reduceMul, Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod,
        BitVec.add_assoc, BitVec.reduceAdd]
      have hpc2 := hin2.pc
      dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc2 ⊢
      rw [heq_fnBase] at hpc2
      apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2d5c#64) hin2.inv
      have hpc := hpc2; have hrun := hin2.run; have hsp : sf2.sp = fsp := hin2.sp
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      clear hpc hrun hsp
      refine r1b_bind_state fun sm3 hsm3 hinv3 => ?_
      change SepWPp (mProg img ext) _ _ _ _ _ _
      have hin3 : InRun img ext s0 sm3 0x2d5c := {
        pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm3, arm64_norm]
        run := by simp [hsm3, arm64_norm, hin2.run]
        sp := by simpa [hsm3, arm64_norm] using hin2.sp
        fp := by simpa [hsm3, arm64_norm] using hin2.fp
        inv := hinv3
        vregs := by simpa [calleeSavedVRegs, hsm3, arm64_norm] using hin2.vregs
        spAligned := hst.spAligned
      }
      have hfail : allocFailedIn s0 sm3 :=
        r1b_allocFailedIn_mono
          (r1b_allocFailed_of_null (by simpa [hsm2, arm64_norm] using hok1.trace) htr_err)
          (by simp [hsm3, arm64_norm])
      exact r1b_call_frame <|
        r1b_oom_2d5c (v0 := 1#64) (v1 := 64#64) hin3 hpanic hfail
    ·
      have hok2 : r1b_OkCtx S img ext g d s0 sf2 0x2554 := hok1.after_call
        (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        hin2 hcs2 (congrArg FsState.files hfs2) htr2
      have hx23_2 : sf2.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 :=
        hcs2.2.2.2.2.1.trans (by first | (simp [hsm2, arm64_norm]; done) | simpa [hsm2, arm64_norm] using hx23_1)
      have hx24_2 : sf2.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 :=
        hcs2.2.2.2.2.2.1.trans (by first | (simp [hsm2, arm64_norm]; done) | simpa [hsm2, arm64_norm] using hx24_1)
      have hx25_2 : sf2.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length :=
        hcs2.2.2.2.2.2.2.1.trans (by first | (simp [hsm2, arm64_norm]; done) | simpa [hsm2, arm64_norm] using hx25_1)
      have hx27_2 : sf2.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64 :=
        hcs2.2.2.2.2.2.2.2.2.1.trans (by simp [hsm2, arm64_norm])
      have hx28_2 : sf2.readReg64 (.gpr 28#5) = 64#64 :=
        hcs2.2.2.2.2.2.2.2.2.2.1.trans (by first | (simp [hsm2, arm64_norm]; done) | simpa [hsm2, arm64_norm] using hx28_1)
      let _ := hx23_2; let _ := hx24_2; let _ := hx25_2; let _ := hx27_2; let _ := hx28_2
      simp only [Nat.reduceMul, Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod,
        BitVec.add_assoc, BitVec.reduceAdd]
      have hpc2 := hin2.pc
      dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc2 ⊢
      rw [heq_fnBase] at hpc2
      apply MainHops.sepWPp_seq_inImage
        (mid := fnBase + bv% (ls_off% "memcpy" - ls_off% "libsignal_cli::run")) hin2.inv
      have hpc := hpc2; have hrun := hin2.run; have hsp : sf2.sp = fsp := hin2.sp
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      clear hpc hrun hsp
      refine r1b_bind_state fun sm3 hsm3 hinv3 => ?_
      change SepWPp (mProg img ext) _ _ _ _ _ _
      rw [show memRegion spkSigPtr 64 = memRegion spkSigPtr spkSig.length from by rw [hspk_sig_len]]
      refine r1b_call_frame <|
        r1b_call_memcpy_region hh hbnd hinv3
          (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm3, arm64_norm])
          (by simp [hsm3, arm64_norm, hin2.run])
          (by simpa [hsm3, arm64_norm] using hin2.sp)
          (by simpa [hsm3, arm64_norm] using hin2.fp)
          (by simpa [calleeSavedVRegs, hsm3, arm64_norm] using hin2.vregs)
          hst.spAligned (retOff := 0x2584)
          (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm3, arm64_norm])
          (dst := spkSigPtr) (src := spkPtr + (4#64 + BitVec.ofNat 64 spkKey.length)) (bs := spkSig)
          (by simp [hsm3, arm64_norm])
          (by simp [hsm3, arm64_norm])
          (by simp [hsm3, arm64_norm, hspk_sig_len])
          hpanic
          (fun sf3 hin3 hcs3 _ hfs3 htr3 => ?_)
      have hok3 : r1b_OkCtx S img ext g d s0 sf3 0x2584 := hok2.after_call
        (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
        (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
        (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
        hin3 hcs3 (congrArg FsState.files hfs3) htr3
      have h4d0_24 :
          ((fsp + 0x4d0#64) ↦₆₄ 0#64) ∗ ((fsp + 0x4d8#64) ↦₆₄ 64#64) ∗
            ((fsp + 0x4e0#64) ↦₆₄ spkSigPtr) ⊢ memRegion (fsp + 0x4d0#64) 24 := by
        refine Entails.trans (sepConj_mono_right (by
            simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
              r1b_cells2_to_region16 (fsp + 0x4d8#64) 64#64 spkSigPtr)) ?_
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          r1b_cell64_cons (a := fsp + 0x4d0#64) 0#64 (n := 16) (by decide)
      rw [show spkPtr + (4#64 + BitVec.ofNat 64 spkKey.length) =
        spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length from (BitVec.add_assoc _ _ _).symm,
        show kpkPtr + (4#64 + BitVec.ofNat 64 kpkKey.length) =
        kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length from (BitVec.add_assoc _ _ _).symm]
      refine r1b_sepWPp_frame (by r1b_ac) (sepConj_mono hspk_rejoin h4d0_24) (by r1b_ac) ?_
      exact MainHops.sepWPp_weaken_pre (Entails.of_eq (by r1b_ac))
        (r1b_step_kpk_clone_2584 hh hc hdrop hbnd hok3
          hreg_rd hspk_rd hspk_sp hspk_d hspk_bytes hspk_ptr hspk_sig_len
          hkpk_rd hkpk_sp hopk_rd hopk_sem_b
          (hcs3.2.2.2.2.1.trans (by first | (simp [hsm3, arm64_norm]; done) | simpa [hsm3, arm64_norm] using hx23_2))
          (hcs3.2.2.2.2.2.1.trans (by first | (simp [hsm3, arm64_norm]; done) | simpa [hsm3, arm64_norm] using hx24_2))
          (hcs3.2.2.2.2.2.2.1.trans (by first | (simp [hsm3, arm64_norm]; done) | simpa [hsm3, arm64_norm] using hx25_2))
          (hcs3.2.2.2.2.2.2.2.1.trans (by simp [hsm3, arm64_norm]))
          (hcs3.2.2.2.2.2.2.2.2.1.trans (by first | (simp [hsm3, arm64_norm]; done) | simpa [hsm3, arm64_norm] using hx27_2))
          (hcs3.2.2.2.2.2.2.2.2.2.1.trans (by first | (simp [hsm3, arm64_norm]; done) | simpa [hsm3, arm64_norm] using hx28_2))
          hpanic hrej
          fun sf4 kpk kpkSigPtr kpkBuf => hk sf4 spk kpk spkSigPtr kpkSigPtr kpkBuf
            spkW0 spkW8 spkW12 spkW16 spkW24)

end CryptoVerification.SignalSession.Cli.RunCompose
