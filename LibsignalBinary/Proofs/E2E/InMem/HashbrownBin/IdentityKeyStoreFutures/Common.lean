/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Transport
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.RoundLemmas
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.Decodes -- shake: keep
import LibsignalBinary.Proofs.Common.StringCloneFlat

/-!
# Shared Helpers for the `InMemIdentityKeyStore` Future-Closure Leaves
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel
open CryptoVerification.E2E.InMem.SipHashBin
open CryptoVerification.E2E.InMem.HashbrownBin

/-! ## Call-Site Specializations (`bcmp`, `String::clone`, `PublicKey::eq`) -/

theorem bcmp_ok_at_getIdentity (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr getIdentityClosureName + bv% (ls_off% "bcmp" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}")) e2eBcmpSpec :=
  hook_ok_at_raw getIdentityClosure_fnOff (by decide : num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}") + num% (ls_off% "bcmp" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}") = num% (ls_off% "bcmp"))
    (by decide) (ls_hook% "bcmp") hHooks.bcmp

theorem bcmp_ok_at_isTrustedIdentity (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr isTrustedIdentityClosureName + bv% (ls_off% "bcmp" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}")) e2eBcmpSpec :=
  hook_ok_at_raw isTrustedIdentityClosure_fnOff (by decide : num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") + num% (ls_off% "bcmp" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") = num% (ls_off% "bcmp"))
    (by decide) (ls_hook% "bcmp") hHooks.bcmp

theorem bcmp_ok_at_saveIdentity (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr saveIdentityClosureName + bv% (ls_off% "bcmp" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")) e2eBcmpSpec :=
  hook_ok_at_raw saveIdentityClosure_fnOff (by decide : num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") + num% (ls_off% "bcmp" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") = num% (ls_off% "bcmp"))
    (by decide) (ls_hook% "bcmp") hHooks.bcmp

theorem stringClone_ok_at_saveIdentity (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr saveIdentityClosureName + bv% (ls_off% "<alloc::string::String as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")) (stringCloneSpec A) := by
  refine inImage_ok_at (callee := stringCloneHookName) ?_
    (LibsignalBinary.Proofs.Common.StringCloneFlat.stringClone_rebase_hooks_ok b A ext
      hHooks.shim hHooks.alloc_sat hHooks.memcpy hHooks.rawVecHandleError)
  rw [HashbrownBin.saveIdentityClosure_fnOff,
    LibsignalBinary.Proofs.Common.StringCloneFlat.stringCloneName_fnOff]

theorem publicKeyEq_fnOff :
    libsignalSessionCode.fnOff ConsumeMessageKeyTransfer.publicKeyEqName = num% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq") :=
  (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq")

theorem publicKeyEq_ok_at_isTrustedIdentity (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr isTrustedIdentityClosureName + bv% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"))
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqSpec := by
  refine inImage_ok_at (callee := ConsumeMessageKeyTransfer.publicKeyEqName) ?_
    (CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKey_eq_ok b hHooks.blackBox)
  rw [HashbrownBin.isTrustedIdentityClosure_fnOff, publicKeyEq_fnOff]

theorem publicKeyEq_ok_at_saveIdentity (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr saveIdentityClosureName + bv% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqSpec := by
  refine inImage_ok_at (callee := ConsumeMessageKeyTransfer.publicKeyEqName) ?_
    (CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKey_eq_ok b hHooks.blackBox)
  rw [HashbrownBin.saveIdentityClosure_fnOff, publicKeyEq_fnOff]

/-! ## Unaligned 8-Byte Control-Group Load and `table4SingleAt` Bucket Splitting -/

theorem probePos_3_eq_ofNat (hash : BitVec 64) :
    hash &&& 3#64 = BitVec.ofNat 64 (probePos hash 3#64).toNat := by
  simp [probePos]

theorem pack64_eq_packGroupWord (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    pack64 b0 b1 b2 b3 b4 b5 b6 b7 = packGroupWord b0 b1 b2 b3 b4 b5 b6 b7 :=
  SipHashBin.pack64_eq_or_shifts b0 b1 b2 b3 b4 b5 b6 b7

theorem getD_default_of_lt {α : Type} (xs : List α) (i : Nat) (d1 d2 : α)
    (hi : i < xs.length) :
    xs.getD i d1 = xs.getD i d2 := by
  simp [List.getD, List.getElem?_eq_getElem hi]

theorem loadGroupAt_eq_pack64 (cbs : List (BitVec 8)) (pos : Nat)
    (h : pos + 8 ≤ cbs.length) :
    loadGroupAt cbs pos =
      pack64 (cbs.getD pos 0#8) (cbs.getD (pos + 1) 0#8)
        (cbs.getD (pos + 2) 0#8) (cbs.getD (pos + 3) 0#8)
        (cbs.getD (pos + 4) 0#8) (cbs.getD (pos + 5) 0#8)
        (cbs.getD (pos + 6) 0#8) (cbs.getD (pos + 7) 0#8) := by
  rw [pack64_eq_packGroupWord]
  unfold loadGroupAt
  rw [Nat.add_zero,
      getD_default_of_lt cbs pos emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 1) emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 2) emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 3) emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 4) emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 5) emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 6) emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 7) emptyTag 0#8 (by omega)]

/-- Split a 12-byte control array `ctrl ↦ₛ cbs` at any offset `pos < 4` so an unaligned 8-byte
`ldr d, [ctrl, pos]` sees `((ctrl + BitVec.ofNat 64 pos) ↦₆₄ loadGroupAt cbs pos)`. -/
theorem pointsToBytes_ctrl12_split_at (ctrl : BitVec 64) (cbs : List (BitVec 8))
    (hlen : cbs.length = 12) (pos : Nat) (hpos : pos < 4) :
    (ctrl ↦ₛ cbs) =
      ((ctrl + BitVec.ofNat 64 pos) ↦₆₄ loadGroupAt cbs pos) ∗
      (ctrl ↦ₛ cbs.take pos) ∗
      ((ctrl + BitVec.ofNat 64 (pos + 8)) ↦ₛ cbs.drop (pos + 8)) := by
  have h1 : pos ≤ cbs.length := by omega
  have h2 : 8 ≤ (cbs.drop pos).length := by simp [List.length_drop, hlen]; omega
  have h3 : pos + 8 ≤ cbs.length := by omega
  rw [pointsToBytes_take_drop ctrl pos cbs h1,
      pointsToBytes_take_drop (ctrl + BitVec.ofNat 64 pos) 8 (cbs.drop pos) h2,
      List.drop_drop,
      pointsToBytes_take8_eq_pointsTo64 (ctrl + BitVec.ofNat 64 pos) cbs pos h3,
      ← loadGroupAt_eq_pack64 cbs pos h3,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  ac_rfl

theorem add_not_shl6_eq_bucketAddr (ctrl : BitVec 64) (k : Nat) (hk : k < 4) :
    ctrl + (~~~(BitVec.ofNat 64 k) <<< 6) = bucketAddr ctrl 64 k := by
  unfold bucketAddr
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> bv_omega

def singleBucketRestAt (stride : Nat) (ctrl : BitVec 64) (k : Nat) : SepProp :=
  arrayAt
    (fun i a => if i = k then emp else memRegion a stride) stride
    (ctrl - BitVec.ofNat 64 (4 * stride)) [3, 2, 1, 0]

private theorem sub256_add64 (ctrl : BitVec 64) :
    ctrl - 256#64 + 64#64 = ctrl - 192#64 := by bv_omega

private theorem sub192_add64 (ctrl : BitVec 64) :
    ctrl - 192#64 + 64#64 = ctrl - 128#64 := by bv_omega

private theorem sub128_add64 (ctrl : BitVec 64) :
    ctrl - 128#64 + 64#64 = ctrl - 64#64 := by bv_omega

theorem arrayAt_single_split_64 (ctrl : BitVec 64) (k : Nat) (hk : k < 4)
    (entryAt : BitVec 64 → SepProp) :
    arrayAt
      (fun i a => if i ∈ [k] then entryAt a else memRegion a 64) 64
      (ctrl - BitVec.ofNat 64 (4 * 64)) (List.range 4).reverse =
    entryAt (bucketAddr ctrl 64 k) ∗ singleBucketRestAt 64 ctrl k := by
  change arrayAt
      (fun i a => if i ∈ [k] then entryAt a else memRegion a 64) 64
      (ctrl - 256#64) [3, 2, 1, 0] =
    entryAt (bucketAddr ctrl 64 k) ∗ singleBucketRestAt 64 ctrl k
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [singleBucketRestAt, bucketAddr, arrayAt, List.mem_singleton,
      Nat.reduceAdd, Nat.reduceMul,
      sub256_add64, sub192_add64, sub128_add64, ite_true]
    ac_rfl

/-! ## 64-Bit SIMD (`D64`) Load/Store Step Rules -/

theorem step_ldrSimd64 {prog : Program} {target_pc : BitVec 64}
    {s s' : Arm64.State} {P : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt : BitVec 5} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldrSimd .D64 vt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad64 ea P v)
    (hexec : ((applyWriteback s wb).writeVReg128 vt (v.zeroExtend 128)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldrSimd .D64 vt addr) := hpc.symm ▸ hfetch
  have hread : s.mem.read64 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 8 = true := hload.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : execInst (.ldrSimd .D64 vt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [execInst, execInstWithSvc, Memory.readSimdSized, applyWriteback,
      Arm64.State.advancePC, Arm64.State.setPC, hsp, haddr, hread, hcan,
      SimdMemSize.bytes, hpc]
  rw [Program.evalInst_of_isSvc0Instr_false _ _ _ rfl, hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

theorem step_ldpSimd64 {prog : Program} {target_pc : BitVec 64}
    {s s' : Arm64.State} {P : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldpSimd .D64 vt1 vt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hload1 : SepLoad64 ea P v1)
    (hload2 : SepLoad64 ea2 P v2)
    (hexec : (((applyWriteback s wb).writeVReg128 vt1 (v1.zeroExtend 128)).writeVReg128 vt2 (v2.zeroExtend 128)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldpSimd .D64 vt1 vt2 addr) := hpc.symm ▸ hfetch
  have hread1 : s.mem.read64 ea = v1 := hload1.load hm
  have hread2 : s.mem.read64 ea2 = v2 := hload2.load hm
  have hcan1 : s.mem.canRead ea 8 = true := hload1.readable hm
  have hcan2 : s.mem.canRead ea2 8 = true := hload2.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : execInst (.ldpSimd .D64 vt1 vt2 addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [execInst, execInstWithSvc, Memory.readSimdSized, applyWriteback,
      Arm64.State.advancePC, Arm64.State.setPC, hsp, haddr, hea2,
      hread1, hread2, hcan1, hcan2, SimdMemSize.bytes, hpc]
  rw [Program.evalInst_of_isSvc0Instr_false _ _ _ rfl, hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

theorem step_stpSimd64 {prog : Program} {target_pc : BitVec 64}
    {s s' : Arm64.State} {P P1 P2 : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stpSimd .D64 vt1 vt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hv1 : (s.readVReg128 vt1).setWidth 64 = v1)
    (hv2 : (s.readVReg128 vt2).setWidth 64 = v2)
    (hstore1 : SepStore64 ea v1 P P1)
    (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P2 post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.stpSimd .D64 vt1 vt2 addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1
  let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm
  have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  apply reaches_pc_step hrun hfetch'
  have hstep : execInst (.stpSimd .D64 vt1 vt2 addr) s = s'.setMem m2 := by
    rw [← hexec]
    cases wb <;> simp [execInst, execInstWithSvc, Memory.writeSimdSized, applyWriteback,
      Arm64.State.advancePC, Arm64.State.setPC, Arm64.State.setMem, Arm64.State.writeReg64,
      hsp, haddr, hea2, hv1, hv2, hcan1, hcan2, SimdMemSize.bytes, hpc, m1, m2]
  rw [Program.evalInst_of_isSvc0Instr_false _ _ _ rfl, hstep]
  exact hnext m2 R hm2

theorem step_stpSimd64_sp {prog : Program} {target_pc : BitVec 64}
    {s : Arm64.State} {P P1 P2 : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {off ea ea2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stpSimd .D64 vt1 vt2 (.Offset .sp off)))
    (hsp : checkRegSPAligned s .sp = true)
    (hea : s.sp + off = ea)
    (hea2 : ea + 8#64 = ea2)
    (hstore1 : SepStore64 ea ((s.readVReg128 vt1).setWidth 64) P P1)
    (hstore2 : SepStore64 ea2 ((s.readVReg128 vt2).setWidth 64) P1 P2)
    (hnext : ∀ m' : Memory, SepWP prog target_pc ((s.setPC (pc + 4#64)).setMem m') P2 post) :
    SepWP prog target_pc s P post :=
  step_stpSimd64 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, AddrMode.baseReg, hsp])
    (by simp [evalAddrMode, Arm64.State.readReg64, hea])
    hea2 rfl rfl hstore1 hstore2 rfl hnext

theorem step_ldpSimd64_sp {prog : Program} {target_pc : BitVec 64}
    {s : Arm64.State} {P : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {off ea ea2 v1 v2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldpSimd .D64 vt1 vt2 (.Offset .sp off)))
    (hsp : checkRegSPAligned s .sp = true)
    (hea : s.sp + off = ea)
    (hea2 : ea + 8#64 = ea2)
    (hload1 : SepLoad64 ea P v1)
    (hload2 : SepLoad64 ea2 P v2)
    (hnext : SepWP prog target_pc
      (((s.writeVReg128 vt1 (v1.zeroExtend 128)).writeVReg128 vt2 (v2.zeroExtend 128)).setPC (pc + 4#64))
      P post) :
    SepWP prog target_pc s P post :=
  step_ldpSimd64 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, AddrMode.baseReg, hsp])
    (by simp [evalAddrMode, Arm64.State.readReg64, hea])
    hea2 hload1 hload2 rfl hnext

theorem step_ldrSimd64_reg {prog : Program} {target_pc : BitVec 64}
    {s : Arm64.State} {P : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt rn rm : BitVec 5} {ea v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldrSimd .D64 vt (.RegOffset (.gpr rn) (.gpr rm) .UXTX 0)))
    (hea : s.readReg64 (.gpr rn) + s.readReg64 (.gpr rm) = ea)
    (hload : SepLoad64 ea P v)
    (hnext : SepWP prog target_pc
      ((s.writeVReg128 vt (v.zeroExtend 128)).setPC (pc + 4#64))
      P post) :
    SepWP prog target_pc s P post :=
  step_ldrSimd64 (wb := none) hpc hrun hfetch rfl
    (by simp [evalAddrMode, extendVal, hea])
    hload rfl hnext

@[arm64_norm ↓, wp_norm ↓]
theorem calleeSavedVRegs_reconstruct_d8_d9 (s0 : Arm64.State) :
    (BitVec.setWidth 64 (s0.readVReg128 8#5), BitVec.setWidth 64 (s0.readVReg128 9#5),
     (calleeSavedVRegs s0).2.2.1, (calleeSavedVRegs s0).2.2.2.1, (calleeSavedVRegs s0).2.2.2.2.1,
     (calleeSavedVRegs s0).2.2.2.2.2.1, (calleeSavedVRegs s0).2.2.2.2.2.2.1,
     (calleeSavedVRegs s0).2.2.2.2.2.2.2) = calleeSavedVRegs s0 := rfl

end CryptoVerification.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures
