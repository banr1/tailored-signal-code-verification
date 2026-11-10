/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.FrameROExt
public import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGt64
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.SpqrV1.Kdf.HooksExt
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSlice -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGen -- shake: keep

/-!
# Contract-Backed Long-Key Prefix Segments of `Hmac<Sha256>::new_from_slice`

Contract-backed (`RunsToE` / `S2Frame`) symbolic execution of the `key.length > 64` branch from
entry (`0x66fa0`) through tail padding (`0x6707c`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf.Nfs3Ext

open Arm64 ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.CBC
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet (
  tripleRatchetProgAtExt extHookStack
  zeroExtend64_truncate32_ofNat64 zeroExtend64_ofNat8 xor_63_of_lt_64
  ult_7_of_lt_56 toLEBytes_8_read64 readBytes_56_eq_append_8 readBytes_56_of_buf_eq)
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame)
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof hiding
  NfsMemInv3 NfsRegInv3
  read64_write8_stack_iv write64_quad_400_iv write64_quad_0_ivsw
  Nfs3OpadPostHook Nfs3OpadMidState Nfs3OpadEndState
  Nfs3PreCompress2 Nfs3PostCompress2 rodata_sha256IV_0x837d8
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3GenProof hiding
  write64_quad_240_iv NfsGt64Common StateG0 StateG1 StateG2a StateG2 StateG3 StateG2b StateG2c
open ProofLib.ProgramReflection
open CryptoVerification.CodeLayout

attribute [-arm64_norm, -simp] CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof.read64_write8_stack_iv

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write8_base_off_disjoint
  Memory.read8_write8_base_zero_off
  Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint
  Memory.read8_write64_base_zero_off
  Memory.read8_write64_base_off_zero
  Memory.read8_write64_base_off_inbounds
  Memory.read64_write64_base_off_disjoint
  Memory.read64_write64_base_zero_off
  Memory.read64_write64_base_off_zero

@[local simp, local arm64_norm]
private theorem adrp_newFromSlice3_mask' :
    (bv% (ls_off% newFromSlice3Name + 40) &&& 0xfffffffffffff000#64 : BitVec 64) =
      bv% (page% (ls_off% newFromSlice3Name + 40)) := rfl

@[local simp, local arm64_norm] private
gen_decodes libsignalSessionCode_tree libsignalSessionCode [(ls_off% newFromSlice3Name) → (ls_off% newFromSlice3Name + 224)]

local macro "nfs3gt_step" : tactic =>
  `(tactic| (
    refine RunsTo.step (inst := ?inst) ?hrun ?hfetch ?_
    case hfetch => (
      (try simp (config := { decide := true }) only [arm64_norm, *])
      refine libsignalSessionCode_fetch_rebase_text ?_ (by decide) (by decide)
      (try simp only [arm64_norm]) <;> rfl)
    case hrun => (simp only [arm64_norm, *])
    try dsimp only [execInst, execAddSubImm, execAddSubExt, execAddSubShift, execAddSubCarry, execLogicalImm,
      execLogicalShift, execMoveWide, execBitfield, execCondSelect, execCondCompare,
      execDataProc1, execDataProc2, execDataProc3, execLdr, execLdrLit, execStr, execLdp, execStp,
      evalLogical, evalBitfield, evalAddrMode, AddrMode.baseReg, checkRegSPAligned,
      checkAddrSPAligned, MemWidth.isAligned, State.spAligned, extendVal, Reg.fromZRBits,
      Reg.fromSPBits]
    try simp (config := { decide := true }) only [arm64_norm, *]
    try arm64_discharge_perms_internal))

private theorem nfs_ule_65_true {x : BitVec 64} (h : 64 < x.toNat) :
    BitVec.ule 0x41#64 x = true := by
  simp [BitVec.ule]; omega

private theorem nfs3_adrp_x22' {b : BitVec 64} (hb : (b &&& 0xfff#64) = 0#64) :
    ((b + bv% (ls_off% newFromSlice3Name + 40)) &&& 0xfffffffffffff000#64) +
      bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) - page% (ls_off% newFromSlice3Name + 40)) =
      b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44)) := by
  bv_bits

private theorem nfs3_adrp_x22_assoc' {b : BitVec 64} (hb : (b &&& 0xfff#64) = 0#64) :
    (((b + bv% (ls_off% newFromSlice3Name + 40)) &&& 0xfffffffffffff000#64) +
      bv% (page% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44)) - page% (ls_off% newFromSlice3Name + 40))) +
      bv% ((ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44)) % 4096) =
      b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44)) := by
  bv_bits

private theorem write64_quad_240_iv' (b : BitVec 64) (m₁ m₂ : Memory) (sp : BitVec 64)
    (hiv : m₂.readBytes (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 = shaStateBytes sha256IV) :
    ((((m₁.write64 (sp + 240#64) (m₂.read64 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))))).write64
      (sp + 248#64) (m₂.read64 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 8)))).write64
      (sp + 256#64) (m₂.read64 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 16)))).write64
      (sp + 264#64) (m₂.read64 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 24)))) =
    m₁.writeBytes (sp + 240#64) (shaStateBytes sha256IV) := by
  have hd1 : sp + 248#64 = (sp + 240#64) + 8#64 := by bv_omega
  have hd2 : sp + 256#64 = (sp + 240#64) + 16#64 := by bv_omega
  have hd3 : sp + 264#64 = (sp + 240#64) + 24#64 := by bv_omega
  have hs1 : b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 8) = (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) + 8#64 := by bv_omega
  have hs2 : b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 16) = (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) + 16#64 := by bv_omega
  have hs3 : b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 24) = (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) + 24#64 := by bv_omega
  rw [hd1, hd2, hd3, hs1, hs2, hs3, write64_quad_read64_eq_writeBytes_32, hiv]

private theorem hmacRunsTo_to_runsToE {prog : Program} {s₀ : State} {P : State → Prop}
    (h : RunsTo prog s₀ P) : RunsToE prog s₀ P := by
  intro hL
  obtain ⟨sf, hst, htr, hvregs, hP, hLf⟩ := h hL
  exact ⟨sf, hst, ⟨htr, hvregs⟩, hP, hLf⟩

private theorem s2Frame_readBytes_eq_of_readable {m₁ m₂ : Memory} {regs : List (BitVec 64 × ℕ)}
    (h : S2Frame m₁ m₂ regs) {a : BitVec 64} {n : ℕ} (hread : m₁.Readable a n)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 a n) (hn : n ≤ 2 ^ 64 := by decide) :
    m₂.readBytes a n = m₁.readBytes a n := by
  refine Memory.readBytes_congr_region hn fun b hb => ?_
  exact h.1 b (hread b hb).1 (hread b hb).2 fun r hr_mem => (hd r hr_mem).outside hb hn

private theorem s2Frame_hook_readBytes_stack_eq' {sp off k : BitVec 64} {sz n : ℕ} {m m' : Memory}
    (hf : S2Frame m m' [(sp + off, sz), (sp - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hrw_stk : m.RW sp 544)
    (hd_stk_ext : DisjointRegions sp 544 (sp - 16384#64) 16384)
    (hk : 0 < n ∧ k.toNat + n ≤ 544)
    (hd_off_k : sz ≤ (k - off).toNat ∧ n ≤ (off - k).toNat) :
    m'.readBytes (sp + k) n = m.readBytes (sp + k) n := by
  have hrw_k : RW m (sp + k) n := hrw_stk.sub (by have := hk.2; clear * - this; bv_omega)
  refine hf.readBytes_eq hrw_k (fun r hr => ?_) (by have := hk.2; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rcases hd_off_k with ⟨h1, h2⟩
    clear * - h1 h2
    simp only [DisjointRegions]
    bv_omega
  · exact (hd_stk_ext.sub_left (sp + k) ⟨hk.1, by have := hk.2; clear * - this; bv_omega⟩).symm

private theorem s2Frame_hook_read64_stack_eq' {sp off k : BitVec 64} {sz : ℕ} {m m' : Memory}
    (hf : S2Frame m m' [(sp + off, sz), (sp - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hrw_stk : m.RW sp 544)
    (hd_stk_ext : DisjointRegions sp 544 (sp - 16384#64) 16384)
    (hk : k.toNat + 8 ≤ 544)
    (hd_off_k : sz = 0 ∨ (sz ≤ (k - off).toNat ∧ 8 ≤ (off - k).toNat)) :
    m'.read64 (sp + k) = m.read64 (sp + k) := by
  have hrw_k : RW m (sp + k) 8 := hrw_stk.sub (by clear * - hk; bv_omega)
  refine Memory.read64_congr fun b hb => ?_
  obtain ⟨hperm_b, hlf_b⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw_k b hb)
  have hr : (m.perm b).r = true := by rw [hperm_b]; rfl
  refine hf.1 b hr hlf_b fun r hr_mem => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
  rcases hr_mem with rfl | rfl
  · rcases hd_off_k with rfl | ⟨h1, h2⟩
    · simp [OutsideRegion]
    · have hd : DisjointRegions (sp + off) sz (sp + k) 8 := by
        clear * - h1 h2; simp only [DisjointRegions]; bv_omega
      exact hd.outside hb (by decide)
  · exact (hd_stk_ext.sub_left (sp + k) ⟨by decide, by clear * - hk; bv_omega⟩).symm.outside hb (by decide)

/-! ## `S2Frame` Helpers and `NfsGt64CommonExt` (`hex:66fe8 .. hex:670e4`) -/

theorem s2Frame_zero_of_agreesOutside {s₀ : State} {m₁ m₂ : Memory} {off : BitVec 64} {sz : ℕ}
    (h1 : S2Frame (nfsZeroMem s₀) m₁
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (h2 : AgreesOutside m₁ m₂ (nfsSp s₀ + off) sz)
    (hoff : 176 ≤ off.toNat ∧ off.toNat + sz ≤ 464) :
    S2Frame (nfsZeroMem s₀) m₂
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
  refine h1.trans ((S2Frame.of_frame (agreesOutside_toFrame h2)).mono fun a ha r hr => ?_)
  have ha1 := ha (nfsSp s₀ + 176#64, 288) (by simp)
  simp only [List.mem_singleton] at hr
  subst hr
  rcases hoff with ⟨hlo, hhi⟩
  clear * - ha1 hlo hhi
  simp only [OutsideRegion] at ha1 ⊢
  bv_omega

theorem s2Frame_zero_of_hook {s₀ : State} {m₁ m₂ : Memory} {off : BitVec 64} {sz : ℕ}
    (h1 : S2Frame (nfsZeroMem s₀) m₁
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (h2 : S2Frame m₁ m₂
      [(nfsSp s₀ + off, sz), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hoff : 176 ≤ off.toNat ∧ off.toNat + sz ≤ 464) :
    S2Frame (nfsZeroMem s₀) m₂
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
  refine h1.trans (h2.mono fun a ha r hr => ?_)
  have ha1 := ha (nfsSp s₀ + 176#64, 288) (by simp)
  have ha2 := ha (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rcases hoff with ⟨hlo, hhi⟩
    clear * - ha1 hlo hhi
    simp only [OutsideRegion] at ha1 ⊢
    bv_omega
  · exact ha2

theorem s2Frame_pro_112_of_zero {s₀ : State} {m : Memory}
    (h : S2Frame (nfsZeroMem s₀) m
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    S2Frame (nfsPrologueMem s₀) m
      [(nfsSp s₀ + 112#64, 352), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
  have h0 : S2Frame (nfsPrologueMem s₀) (nfsZeroMem s₀)
      [(nfsSp s₀ + 112#64, 352), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    refine (S2Frame.of_frame (agreesOutside_toFrame (agreesOutside_nfsZeroMem s₀))).mono fun a ha r hr => ?_
    have ha1 := ha (nfsSp s₀ + 112#64, 352) (by simp)
    simp only [List.mem_singleton] at hr
    subst hr
    clear * - ha1
    simp only [OutsideRegion] at ha1 ⊢
    bv_omega
  refine h0.trans (h.mono fun a ha r hr => ?_)
  have ha1 := ha (nfsSp s₀ + 112#64, 352) (by simp)
  have ha2 := ha (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · clear * - ha1
    simp only [OutsideRegion] at ha1 ⊢
    bv_omega
  · exact ha2

theorem s2Frame_16928_of_pro_112 {s₀ : State} {m : Memory}
    (h : S2Frame (nfsPrologueMem s₀) m
      [(nfsSp s₀ + 112#64, 352), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    S2Frame s₀.mem m [(s₀.sp - 16928#64, 16928)] := by
  have hpro : S2Frame s₀.mem (nfsPrologueMem s₀) [(s₀.sp - 16928#64, 16928)] := by
    refine (S2Frame.of_frame (agreesOutside_toFrame (agreesOutside_nfsPrologueMem s₀))).mono fun a ha r hr => ?_
    have ha1 := ha (s₀.sp - 16928#64, 16928) (by simp)
    simp only [List.mem_singleton] at hr
    subst hr
    clear * - ha1
    simp only [OutsideRegion, nfsSp] at ha1 ⊢
    bv_omega
  refine hpro.trans (h.mono fun a ha r hr => ?_)
  have ha1 := ha (s₀.sp - 16928#64, 16928) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · clear * - ha1
    simp only [OutsideRegion, nfsSp] at ha1 ⊢
    bv_omega
  · clear * - ha1
    simp only [OutsideRegion, nfsSp, extHookStack] at ha1 ⊢
    bv_omega

theorem s2Frame_16928_of_zero {s₀ : State} {m : Memory}
    (h : S2Frame (nfsZeroMem s₀) m
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    S2Frame s₀.mem m [(s₀.sp - 16928#64, 16928)] :=
  s2Frame_16928_of_pro_112 (s2Frame_pro_112_of_zero h)

theorem s2Frame_out_16928_of_16928 {s₀ : State} {m₁ m₂ : Memory}
    (h : S2Frame m₁ m₂ [(s₀.sp - 16928#64, 16928)]) :
    S2Frame m₁ m₂ [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] := by
  refine h.mono fun a ha r hr => ?_
  simp only [List.mem_singleton] at hr
  subst hr
  exact ha (s₀.sp - 16928#64, 16928) (by simp)

/-- Common register & frame invariant across `hex:66fe8 .. hex:670e4` on the `> 64` key path. -/
structure NfsGt64CommonExt (b : BitVec 64) (s₀ s : State) : Prop where
  status : s.status = .Running
  sp_eq : s.sp = nfsSp s₀
  sp_align : (nfsSp s₀ &&& 0b1111#64) = 0#64
  x29_eq : s.readReg64 .x29 = nfsSp s₀ + 464#64
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x22_eq : s.readReg64 .x22 = b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))
  x25_eq : s.readReg64 .x25 = s₀.readReg64 .x25
  x26_eq : s.readReg64 .x26 = s₀.readReg64 .x26
  x27_eq : s.readReg64 .x27 = s₀.readReg64 .x27
  frame_zero : S2Frame (nfsZeroMem s₀) s.mem
    [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]

theorem NfsGt64CommonExt.frame_16928 {b : BitVec 64} {s₀ s : State}
    (hc : NfsGt64CommonExt b s₀ s) :
    S2Frame s₀.mem s.mem [(s₀.sp - 16928#64, 16928)] :=
  s2Frame_16928_of_zero hc.frame_zero

theorem NfsGt64CommonExt.rw_of_rw {b : BitVec 64} {s₀ s : State} {a : BitVec 64} {n : ℕ}
    (hc : NfsGt64CommonExt b s₀ s) (hrw : s₀.mem.RW a n) :
    s.mem.RW a n :=
  S2Frame.rw_of_rw hc.frame_16928 a n hrw

theorem NfsGt64CommonExt.readable_of_readable {b : BitVec 64} {s₀ s : State} {a : BitVec 64} {n : ℕ}
    (hc : NfsGt64CommonExt b s₀ s) (hr : s₀.mem.Readable a n) :
    s.mem.Readable a n :=
  fun x hx => hc.frame_16928.2.2 x (hr x hx).1 (hr x hx).2

theorem NfsGt64CommonExt.rw_stack {b : BitVec 64} {s₀ s : State}
    (hc : NfsGt64CommonExt b s₀ s) (hrw : s₀.mem.RW (s₀.sp - 16928#64) 16928) :
    s.mem.RW (nfsSp s₀) 544 :=
  (hc.rw_of_rw hrw).sub (by clear * -; simp only [nfsSp]; bv_omega)

theorem NfsGt64CommonExt.rw_extstk {b : BitVec 64} {s₀ s : State}
    (hc : NfsGt64CommonExt b s₀ s) (hrw : s₀.mem.RW (s₀.sp - 16928#64) 16928) :
    s.mem.RW (nfsSp s₀ - 16384#64) 16384 :=
  (hc.rw_of_rw hrw).sub (by clear * -; simp only [nfsSp]; bv_omega)

theorem NfsGt64CommonExt.of_cc_hook {b : BitVec 64} {s₀ s1 s2 : State}
    {off : BitVec 64} {sz : ℕ}
    (hstat2 : s2.status = .Running)
    (hsp1 : s1.sp = nfsSp s₀)
    (hal_nfs : (nfsSp s₀ &&& 0b1111#64) = 0#64)
    (hx29_1 : s1.readReg64 .x29 = nfsSp s₀ + 464#64)
    (hx19_1 : s1.readReg64 .x19 = s₀.readReg64 .x0)
    (hx22_1 : s1.readReg64 .x22 = b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44)))
    (hx25_1 : s1.readReg64 .x25 = s₀.readReg64 .x25)
    (hx26_1 : s1.readReg64 .x26 = s₀.readReg64 .x26)
    (hx27_1 : s1.readReg64 .x27 = s₀.readReg64 .x27)
    (hcc : CallingConventionPreserved s1 s2)
    (hf1 : S2Frame (nfsZeroMem s₀) s1.mem
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hf12 : S2Frame s1.mem s2.mem
      [(nfsSp s₀ + off, sz), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hoff : 176 ≤ off.toNat ∧ off.toNat + sz ≤ 464) :
    NfsGt64CommonExt b s₀ s2 :=
  { status := hstat2
    sp_eq := hcc.1.trans hsp1
    sp_align := hal_nfs
    x29_eq := hcc.2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
    x19_eq := hcc.2.1.trans hx19_1
    x22_eq := hcc.2.2.2.2.1.trans hx22_1
    x25_eq := hcc.2.2.2.2.2.2.2.1.trans hx25_1
    x26_eq := hcc.2.2.2.2.2.2.2.2.1.trans hx26_1
    x27_eq := hcc.2.2.2.2.2.2.2.2.2.1.trans hx27_1
    frame_zero := s2Frame_zero_of_hook hf1 hf12 hoff }

theorem disj_stk_extstk_of_disj_16928 {s₀ : State} {a : BitVec 64} {n : ℕ}
    (hd : DisjointRegions a n (s₀.sp - 16928#64) 16928) :
    DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384 := by
  clear * - hd
  simp only [DisjointRegions, nfsSp] at hd ⊢
  bv_omega

/-! ## Cut `G0Ext` (`hex:66fe8`) and Prologue (`hex:66fa0 → hex:66fe8`) -/

structure StateG0Ext (b : BitVec 64) (s₀ s : State) : Prop where
  pc_eq : s.pc = b + bv% (ls_off% newFromSlice3Name + 72)
  common : NfsGt64CommonExt b s₀ s
  x1_eq : s.readReg64 .x1 = s₀.readReg64 .x1
  x2_eq : s.readReg64 .x2 = s₀.readReg64 .x2

theorem nfs3_seg0_pro_gt64_ext {b : BitVec 64} {ext : String → Option (State → State)} {s₀ : State}
    (hpc : s₀.pc = b + bv% (ls_off% newFromSlice3Name))
    (hstat : s₀.status = .Running)
    (hgt : 64 < (s₀.readReg64 .x2).toNat)
    (hb : (b &&& 0xfff#64) = 0#64)
    (hrw_stack : RW s₀.mem (s₀.sp - 16928#64) 16928)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    RunsTo (tripleRatchetProgAtExt b ext) s₀ (StateG0Ext b s₀) := by
  have hsp₀ : s₀.sp = nfsSp s₀ + 544#64 := nfs_sp_eq_add s₀
  have hal_nfs : (nfsSp s₀ &&& 0b1111#64) = 0#64 := nfs_sp_align hal
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hal_544 : ((nfsSp s₀ + 544#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_544_align hal
  have hRW_stack : s₀.mem.RW (nfsSp s₀) 544 :=
    hrw_stack.sub (by clear * -; simp only [nfsSp]; bv_omega)
  have hcond : BitVec.ule 0x41#64 (s₀.readReg64 .x2) = true := nfs_ule_65_true hgt
  have hadrp1 := nfs3_adrp_x22_assoc' hb
  have hadrp2 := nfs3_adrp_x22' hb
  iterate 15 nfs3gt_step
  refine RunsTo.refl ?_
  have hmem_eq :
      ((((((((nfsPrologueMem s₀).write64 (nfsSp s₀ + 112#64) 0#64).write64
        (nfsSp s₀ + 120#64) 0#64).write64 (nfsSp s₀ + 128#64) 0#64).write64
        (nfsSp s₀ + 136#64) 0#64).write64 (nfsSp s₀ + 144#64) 0#64).write64
        (nfsSp s₀ + 152#64) 0#64).write64 (nfsSp s₀ + 160#64) 0#64).write64
        (nfsSp s₀ + 168#64) 0#64 = nfsZeroMem s₀ :=
    write64_oct_zero_eq_writeBytes_64 (nfsPrologueMem s₀) (nfsSp s₀)
  refine
    { pc_eq := by simp only [arm64_norm]
      common :=
        { status := by simp only [arm64_norm, hstat]
          sp_eq := by simp only [arm64_norm]
          sp_align := hal_nfs
          x29_eq := by simp only [arm64_norm]
          x19_eq := by simp only [arm64_norm]
          x22_eq := by simp only [arm64_norm, hadrp1, hadrp2]; try bv_bits
          x25_eq := by simp only [arm64_norm]
          x26_eq := by simp only [arm64_norm]
          x27_eq := by simp only [arm64_norm]
          frame_zero := by
            dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
            dsimp only [nfsPrologueMem, Reg.x29, Reg.x30, Reg.x28, Reg.x24, Reg.x23,
              Reg.x22, Reg.x21, Reg.x20, Reg.x19] at hmem_eq
            rw [hmem_eq]
            exact S2Frame.refl (nfsZeroMem s₀) _ }
      x1_eq := by simp only [arm64_norm]
      x2_eq := by simp only [arm64_norm] }

/-! ## Cut `G1Ext` (`hex:6702c`) and Sub-segment 0a (`hex:66fe8 → hex:6702c`) -/

structure StateG1Ext (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (s₀ s : State) : Prop where
  pc_eq : s.pc = b + bv% (ls_off% newFromSlice3Name + 140)
  common : NfsGt64CommonExt b s₀ s
  tail_bytes : s.mem.readBytes (nfsSp s₀ + 176#64) (key.length - 64 * (key.length / 64)) =
    key.drop (64 * (key.length / 64))
  pos_byte : s.mem.read8 (nfsSp s₀ + 239#64) = BitVec.ofNat 8 (key.length - 64 * (key.length / 64))
  st0_bytes : s.mem.readBytes (nfsSp s₀ + 240#64) 32 =
    shaStateBytes ((chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV)
  nblk_word : s.mem.read64 (nfsSp s₀ + 272#64) = BitVec.ofNat 64 (key.length / 64)

set_option maxHeartbeats 1600000 in
theorem nfs3_seg0a1_gt64_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {s₀ s : State}
    (hs : StateG0Ext b s₀ s)
    (hgt : 64 < (s₀.readReg64 .x2).toNat)
    (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s₀.mem.readBytes (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32)
    (hdisj_iv_stack : DisjointRegions (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (s₀.sp - 16928#64) 16928)
    (hrw_stack : RW s₀.mem (s₀.sp - 16928#64) 16928) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s1 =>
      s1.pc = b + bv% (ls_off% "sha2::sha256::compress256") ∧
      NfsGt64CommonExt b s₀ s1 ∧
      s1.readReg64 .x0 = nfsSp s₀ + 240#64 ∧
      s1.readReg64 .x1 = s₀.readReg64 .x1 ∧
      (s1.readReg64 .x2).toNat = key.length / 64 ∧
      s1.readReg64 .lr = b + bv% (ls_off% newFromSlice3Name + 120) ∧
      s1.readReg64 .x20 = s₀.readReg64 .x2 &&& 63#64 ∧
      s1.readReg64 .x21 = s₀.readReg64 .x1 ∧
      s1.readReg64 .x23 = s₀.readReg64 .x2 &&& 9223372036854775744#64 ∧
      s1.mem.readBytes (nfsSp s₀ + 240#64) 32 = shaStateBytes sha256IV ∧
      s1.mem.read64 (nfsSp s₀ + 272#64) = BitVec.ofNat 64 (key.length / 64)) := by
  intro key
  generalize hPost : (fun s1 : State => _) = Post
  rcases hs with ⟨hpc, hcom, hx1, hx2⟩
  have hRW_s : s.mem.RW (nfsSp s₀) 544 := hcom.rw_stack hrw_stack
  have hf_16928 : S2Frame s₀.mem s.mem [(s₀.sp - 16928#64, 16928)] := hcom.frame_16928
  rcases hcom with ⟨hstat, hsp, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27, hf_zero⟩
  have hread_iv_s : s.mem.Readable (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 :=
    fun a ha => hf_16928.2.2 a (hread_iv a ha).1 (hread_iv a ha).2
  have hiv_s : s.mem.readBytes (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 = shaStateBytes sha256IV :=
    (s2Frame_readBytes_eq_of_readable hf_16928 hread_iv
      (by simp [hdisj_iv_stack.symm]) (by decide)).trans hiv
  iterate 12 nfs3gt_step
  subst hPost
  refine RunsTo.refl ?_
  set m_pre_c1 := ((s.mem.write8 (nfsSp s₀ + 239#64) 0#8).writeBytes
    (nfsSp s₀ + 240#64) (shaStateBytes sha256IV)).write64
    (nfsSp s₀ + 272#64) (s₀.readReg64 .x2 >>> 6)
  have hm_pre_c1 :
      (((((s.mem.write8 (nfsSp s₀ + 239#64) 0#8).write64
        (nfsSp s₀ + 240#64) (s.mem.read64 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))))).write64
        (nfsSp s₀ + 248#64) (s.mem.read64 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 8)))).write64
        (nfsSp s₀ + 256#64) (s.mem.read64 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 16)))).write64
        (nfsSp s₀ + 264#64) (s.mem.read64 (b + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44) + 24)))).write64
        (nfsSp s₀ + 272#64) (s₀.readReg64 .x2 >>> 6) = m_pre_c1 := by
    dsimp only [m_pre_c1]
    rw [write64_quad_240_iv' b _ s.mem (nfsSp s₀) hiv_s]
  have hf_pre_c1 : S2Frame (nfsZeroMem s₀) m_pre_c1
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    have h1 := s2Frame_zero_of_agreesOutside hf_zero
      (AgreesOutside.write8_self s.mem (nfsSp s₀ + 239#64) 0#8) (by decide)
    have h2 : AgreesOutside (s.mem.write8 (nfsSp s₀ + 239#64) 0#8)
        ((s.mem.write8 (nfsSp s₀ + 239#64) 0#8).writeBytes (nfsSp s₀ + 240#64) (shaStateBytes sha256IV))
        (nfsSp s₀ + 240#64) 32 := by
      have hlen : (shaStateBytes sha256IV).length = 32 := shaStateBytes_length sha256IV
      rw [← hlen]
      exact ProofLib.agreesOutside_writeBytes _ _ _
    have h3 := s2Frame_zero_of_agreesOutside h1 h2 (by decide)
    exact s2Frame_zero_of_agreesOutside h3
      (AgreesOutside.write64_self _ (nfsSp s₀ + 272#64) (s₀.readReg64 .x2 >>> 6)) (by decide)
  have hst_pre_c1 : m_pre_c1.readBytes (nfsSp s₀ + 240#64) 32 = shaStateBytes sha256IV := by
    dsimp only [m_pre_c1]
    have hd : DisjointRegions (nfsSp s₀ + 272#64) 8 (nfsSp s₀ + 240#64) 32 := by
      clear * -; simp only [DisjointRegions]; bv_omega
    rw [(agreesOutside_toFrame (AgreesOutside.write64_self _ (nfsSp s₀ + 272#64) _)).readBytes_eq
      (by simp [hd]) (by decide)]
    exact CryptoVerification.LibsignalAesCbc.Run.Layout.readBytes_writeBytes_eq _ _ _ 32
      (shaStateBytes_length sha256IV) (by decide)
  have hkey_len : key.length = (s₀.readReg64 .x2).toNat := Memory.readBytes_length _ _ _
  have hkey_lt : key.length < 2 ^ 63 := by omega
  obtain ⟨hs1, _, _, _, _⟩ := ikm_split_lemmas hkey_lt
  have hx2_eq : s₀.readReg64 .x2 = BitVec.ofNat 64 key.length := by
    rw [hkey_len, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hnblk_pre_c1 : m_pre_c1.read64 (nfsSp s₀ + 272#64) = BitVec.ofNat 64 (key.length / 64) := by
    dsimp only [m_pre_c1]
    rw [Memory.read64_write64_same, hx2_eq]
    apply BitVec.eq_of_toNat_eq
    rw [hs1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by simp only [arm64_norm],
    { status := by simp only [arm64_norm, hstat]
      sp_eq := by simp only [arm64_norm, hsp]
      sp_align := hal_nfs
      x29_eq := by simp only [arm64_norm, hx29]
      x19_eq := by simp only [arm64_norm, hx19]
      x22_eq := by simp only [arm64_norm, hx22]
      x25_eq := by simp only [arm64_norm, hx25]
      x26_eq := by simp only [arm64_norm, hx26]
      x27_eq := by simp only [arm64_norm, hx27]
      frame_zero := by
        dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
        rw [hm_pre_c1]
        exact hf_pre_c1 },
    by simp only [arm64_norm],
    by simp only [arm64_norm, hx1],
    by simp only [arm64_norm]; rw [hx2_eq, hs1],
    by simp only [arm64_norm],
    by simp only [arm64_norm, hx2],
    by simp only [arm64_norm, hx1],
    by simp only [arm64_norm, hx2],
    by
      dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
      rw [hm_pre_c1]; exact hst_pre_c1,
    by
      dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
      rw [hm_pre_c1]; exact hnblk_pre_c1⟩

set_option maxHeartbeats 1600000 in
theorem nfs3_seg0a2_gt64_ext {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {s₀ s : State}
    (hgt : 64 < (s₀.readReg64 .x2).toNat)
    (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hrw_stack : RW s₀.mem (s₀.sp - 16928#64) 16928)
    (hpc : s.pc = b + bv% (ls_off% newFromSlice3Name + 120))
    (hcom : NfsGt64CommonExt b s₀ s)
    (hx20 : s.readReg64 .x20 = s₀.readReg64 .x2 &&& 63#64)
    (hx21 : s.readReg64 .x21 = s₀.readReg64 .x1)
    (hx23 : s.readReg64 .x23 = s₀.readReg64 .x2 &&& 9223372036854775744#64)
    (hst0 : s.mem.readBytes (nfsSp s₀ + 240#64) 32 =
      shaStateBytes ((chunks64 ((s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat).take
        (64 * ((s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat).length / 64)))).foldl F sha256IV))
    (hnblk : s.mem.read64 (nfsSp s₀ + 272#64) =
      BitVec.ofNat 64 ((s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat).length / 64)) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s2 =>
      s2.pc = b + bv% (ls_off% "memcpy") ∧
      NfsGt64CommonExt b s₀ s2 ∧
      s2.readReg64 .x0 = nfsSp s₀ + 176#64 ∧
      s2.readReg64 .x1 = s₀.readReg64 .x1 + (s₀.readReg64 .x2 &&& 9223372036854775744#64) ∧
      (s2.readReg64 .x2).toNat = key.length - 64 * (key.length / 64) ∧
      s2.readReg64 .lr = b + bv% (ls_off% newFromSlice3Name + 140) ∧
      s2.mem.read8 (nfsSp s₀ + 239#64) = BitVec.ofNat 8 (key.length - 64 * (key.length / 64)) ∧
      s2.mem.readBytes (nfsSp s₀ + 240#64) 32 =
        shaStateBytes ((chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV) ∧
      s2.mem.read64 (nfsSp s₀ + 272#64) = BitVec.ofNat 64 (key.length / 64)) := by
  intro key
  generalize hPost : (fun s2 : State => _) = Post
  have hRW_s : s.mem.RW (nfsSp s₀) 544 := hcom.rw_stack hrw_stack
  rcases hcom with ⟨hstat, hsp, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27, hf_zero⟩
  have hstep : RunsTo (tripleRatchetProgAtExt b ext) s (fun s2 =>
      s2 = ((((((s.setMem (s.mem.write8 (nfsSp s₀ + 239#64)
        (BitVec.truncate 8 (s₀.readReg64 .x2 &&& 63#64)))).advancePC).writeReg64
        .x0 (nfsSp s₀ + 176#64)).advancePC.writeReg64
        .x1 (s₀.readReg64 .x1 + (s₀.readReg64 .x2 &&& 9223372036854775744#64))).advancePC.writeReg64
        .x2 (s₀.readReg64 .x2 &&& 63#64)).advancePC.writeReg64
        .lr (b + bv% (ls_off% newFromSlice3Name + 140))).setPC (b + bv% (ls_off% "memcpy"))) := by
    clear hPost hst0 hnblk key hgt hlt hrw_stack hf_zero
    iterate 5 nfs3gt_step
    exact RunsTo.refl rfl
  refine hstep.mono fun s2 hs2 => ?_
  subst hPost hs2
  have hkey_len : key.length = (s₀.readReg64 .x2).toNat := Memory.readBytes_length _ _ _
  have hkey_lt : key.length < 2 ^ 63 := by omega
  obtain ⟨_, _, _, hs4, hs5⟩ := ikm_split_lemmas hkey_lt
  have hx2_eq : s₀.readReg64 .x2 = BitVec.ofNat 64 key.length := by
    rw [hkey_len, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  set m_pre_mc := s.mem.write8 (nfsSp s₀ + 239#64) (BitVec.truncate 8 (s₀.readReg64 .x2 &&& 63#64))
  have hag_239 : AgreesOutside s.mem m_pre_mc (nfsSp s₀ + 239#64) 1 :=
    AgreesOutside.write8_self s.mem (nfsSp s₀ + 239#64) _
  have hf_pre_mc : S2Frame (nfsZeroMem s₀) m_pre_mc
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] :=
    s2Frame_zero_of_agreesOutside hf_zero hag_239 (by decide)
  have hpos_pre_mc : m_pre_mc.read8 (nfsSp s₀ + 239#64) =
      BitVec.ofNat 8 (key.length - 64 * (key.length / 64)) := by
    dsimp only [m_pre_mc]
    rw [Memory.read8_write8_same, hx2_eq, hs5]
  have hst0_pre_mc : m_pre_mc.readBytes (nfsSp s₀ + 240#64) 32 =
      shaStateBytes ((chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV) := by
    have hd : DisjointRegions (nfsSp s₀ + 239#64) 1 (nfsSp s₀ + 240#64) 32 := by
      clear * -; simp only [DisjointRegions]; bv_omega
    rw [(agreesOutside_toFrame hag_239).readBytes_eq (by simp [hd]) (by decide)]
    exact hst0
  have hnblk_pre_mc : m_pre_mc.read64 (nfsSp s₀ + 272#64) = BitVec.ofNat 64 (key.length / 64) := by
    have hd : DisjointRegions (nfsSp s₀ + 239#64) 1 (nfsSp s₀ + 272#64) 8 := by
      clear * -; simp only [DisjointRegions]; bv_omega
    rw [(agreesOutside_toFrame hag_239).read64_eq (by simp [hd])]
    exact hnblk
  refine ⟨by simp only [arm64_norm],
    { status := by simp only [arm64_norm, hstat]
      sp_eq := by simp only [arm64_norm, hsp]
      sp_align := hal_nfs
      x29_eq := by simp only [arm64_norm, hx29]
      x19_eq := by simp only [arm64_norm, hx19]
      x22_eq := by simp only [arm64_norm, hx22]
      x25_eq := by simp only [arm64_norm, hx25]
      x26_eq := by simp only [arm64_norm, hx26]
      x27_eq := by simp only [arm64_norm, hx27]
      frame_zero := by
        dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
        exact hf_pre_mc },
    by simp only [arm64_norm],
    by simp only [arm64_norm],
    by simp only [arm64_norm, hx2_eq, hs4],
    by simp only [arm64_norm],
    by
      dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
      exact hpos_pre_mc,
    by
      dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
      exact hst0_pre_mc,
    by
      dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
      exact hnblk_pre_mc⟩

set_option maxHeartbeats 1600000 in
theorem nfs3_seg0a_gt64_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hHooks : SpqrKdfHooksExt img F ext)
    {s₀ s : State}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hs : StateG0Ext img.base s₀ s)
    (hgt : 64 < (s₀.readReg64 .x2).toNat)
    (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s₀.mem.readBytes (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32)
    (hdisj_iv_stack : DisjointRegions (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (s₀.sp - 16928#64) 16928)
    (hrw_key : s₀.mem.RW (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hrw_stack : RW s₀.mem (s₀.sp - 16928#64) 16928)
    (hdisj_key_stack : DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 16928#64) 16928) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateG1Ext img.base F key s₀) := by
  intro key
  have hkey_len : key.length = (s₀.readReg64 .x2).toNat := Memory.readBytes_length _ _ _
  have hkey_gt : 64 < key.length := by omega
  have hkey_lt : key.length < 2 ^ 63 := by omega
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := ikm_split_lemmas hkey_lt
  have hx2_eq : s₀.readReg64 .x2 = BitVec.ofNat 64 key.length := by
    rw [hkey_len, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384 :=
    disj_stk_extstk_of_disj_16928 hdisj_iv_stack
  have hstep1 : RunsToE (tripleRatchetProgAtExt img.base ext) s _ :=
    hmacRunsTo_to_runsToE (nfs3_seg0a1_gt64_ext hs hgt hlt hiv hread_iv hdisj_iv_stack hrw_stack)
  refine hstep1.trans_full fun s1 h1 hkf1 hsym1 => ?_
  rcases h1 with ⟨hpc1, hcom1, hx0_1, hx1_1, hx2_1, hlr_1, hx20_1, hx21_1, hx23_1, hst_1, hnblk_1⟩
  have hfrz1 : img.FrozenLoaded s1 := hfrz.of_keepsFrozen hkf1
  have hsym1' : s1.symtab = img.symtab := hsym1.trans hsym
  have hf1_16928 : S2Frame s₀.mem s1.mem [(s₀.sp - 16928#64, 16928)] := hcom1.frame_16928
  have hrw_stk1 : s1.mem.RW (nfsSp s₀) 544 := hcom1.rw_stack hrw_stack
  have hrw_extstk1 : s1.mem.RW (nfsSp s₀ - 16384#64) 16384 := hcom1.rw_extstk hrw_stack
  have hrw_key1 : s1.mem.RW (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat :=
    hcom1.rw_of_rw hrw_key
  have hkey_s1 : s1.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat = key :=
    s2Frame_readBytes_eq_of_readable hf1_16928 hrw_key.readable
      (by simp [hdisj_key_stack.symm]) (by omega)
  set pfx := key.take (64 * (key.length / 64))
  have hpfx_len : pfx.length = 64 * (key.length / 64) := by simp [pfx]; omega
  have hpfx_le : pfx.length ≤ 2 ^ 64 := by omega
  have hx2_1' : 64 * (s1.readReg64 .x2).toNat = pfx.length := by rw [hx2_1, hpfx_len]
  have hpfx_s1 : s1.mem.readBytes (s₀.readReg64 .x1) pfx.length = pfx := by
    rw [hpfx_len, readBytes_take_of_le s1.mem (s₀.readReg64 .x1)
      (by omega : 64 * (key.length / 64) ≤ (s₀.readReg64 .x2).toNat), hkey_s1]
  have hrw_pfx1 : s1.mem.RW (s₀.readReg64 .x1) pfx.length := by
    rw [hpfx_len]
    exact hrw_key1.sub (by clear * - hkey_len; bv_omega)
  have hd_st_pfx1 : DisjointRegions (nfsSp s₀ + 240#64) 32
      (s₀.readReg64 .x1) pfx.length := by
    rw [hpfx_len]
    refine (hdisj_key_stack.sub_left (s₀.readReg64 .x1)
      ⟨by omega, by clear * - hkey_len; bv_omega⟩).symm.sub_left (nfsSp s₀ + 240#64)
      ⟨by decide, by clear * -; simp only [nfsSp]; bv_omega⟩
  have hd_st_ext1 : DisjointRegions (nfsSp s₀ + 240#64) 32
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hcom1.sp_eq]
    exact hd_stk_ext.sub_left (nfsSp s₀ + 240#64) ⟨by decide, by clear * -; bv_omega⟩
  have hd_pfx_ext1 : DisjointRegions (s₀.readReg64 .x1) pfx.length
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hcom1.sp_eq, hpfx_len]
    have hd_k : DisjointRegions (s₀.readReg64 .x1) (64 * (key.length / 64))
        (s₀.sp - 16928#64) 16928 :=
      hdisj_key_stack.sub_left (s₀.readReg64 .x1) ⟨by omega, by clear * - hkey_len; bv_omega⟩
    exact hd_k.sub_right (nfsSp s₀ - BitVec.ofNat 64 extHookStack)
      ⟨by decide, by clear * -; simp only [nfsSp, extHookStack]; bv_omega⟩
  have hc1 := compress256_subroutine_runsTo hHooks.compress256 (by decide)
    hfrz1 hsym1' hpc1 hcom1.status hx0_1 hx1_1 hx2_1' hpfx_le hst_1 hpfx_s1
    (hrw_stk1.sub (by clear * -; bv_omega)) hrw_pfx1
    (by rw [hcom1.sp_eq]; exact hrw_extstk1)
    hd_st_pfx1 hd_st_ext1 hd_pfx_ext1
    (by rw [hcom1.sp_eq]; exact hcom1.sp_align)
  refine hc1.trans_full fun s2 ⟨hpc2, hstat2, hcc12, hst0_2, _, hfr12⟩ hkf2 hsym2 => ?_
  rw [hlr_1] at hpc2
  have hfrz2 : img.FrozenLoaded s2 := hfrz1.of_keepsFrozen hkf2
  have hsym2' : s2.symtab = img.symtab := hsym2.trans hsym1'
  have hfr12_stk : S2Frame s1.mem s2.mem
      [(nfsSp s₀ + 240#64, 32), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    rwa [hcom1.sp_eq] at hfr12
  have hcom2 : NfsGt64CommonExt img.base s₀ s2 :=
    NfsGt64CommonExt.of_cc_hook hstat2 hcom1.sp_eq hcom1.sp_align
      hcom1.x29_eq hcom1.x19_eq hcom1.x22_eq hcom1.x25_eq hcom1.x26_eq hcom1.x27_eq
      hcc12 hcom1.frame_zero hfr12_stk (by decide)
  have hnblk_2 : s2.mem.read64 (nfsSp s₀ + 272#64) = BitVec.ofNat 64 (key.length / 64) :=
    (s2Frame_hook_read64_stack_eq' hfr12_stk hrw_stk1 hd_stk_ext
      (by decide) (by decide)).trans hnblk_1
  have hstep3 : RunsToE (tripleRatchetProgAtExt img.base ext) s2 _ :=
    hmacRunsTo_to_runsToE (nfs3_seg0a2_gt64_ext hgt hlt hrw_stack hpc2 hcom2
      (hcc12.2.2.1.trans hx20_1) (hcc12.2.2.2.1.trans hx21_1)
      (hcc12.2.2.2.2.2.1.trans hx23_1) hst0_2 hnblk_2)
  refine hstep3.trans_full fun s3 h3 hkf3 hsym3 => ?_
  rcases h3 with ⟨hpc3, hcom3, hx0_3, hx1_3, hx2_3, hlr_3, hpos_3, hst0_3, hnblk_3⟩
  have hfrz3 : img.FrozenLoaded s3 := hfrz2.of_keepsFrozen hkf3
  have hsym3' : s3.symtab = img.symtab := hsym3.trans hsym2'
  have hf3_16928 : S2Frame s₀.mem s3.mem [(s₀.sp - 16928#64, 16928)] := hcom3.frame_16928
  have hrw_stk3 : s3.mem.RW (nfsSp s₀) 544 := hcom3.rw_stack hrw_stack
  have hrw_extstk3 : s3.mem.RW (nfsSp s₀ - 16384#64) 16384 := hcom3.rw_extstk hrw_stack
  have hrw_key3 : s3.mem.RW (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat :=
    hcom3.rw_of_rw hrw_key
  have hkey_s3 : s3.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat = key :=
    s2Frame_readBytes_eq_of_readable hf3_16928 hrw_key.readable
      (by simp [hdisj_key_stack.symm]) (by omega)
  set tail := key.drop (64 * (key.length / 64))
  have htail_len : key.length - 64 * (key.length / 64) = tail.length := by simp [tail]
  rw [htail_len] at hx2_3
  have htail_lt64 : tail.length < 64 := by simp [tail]; omega
  have htail_s3 : s3.mem.readBytes
      (s₀.readReg64 .x1 + (s₀.readReg64 .x2 &&& 9223372036854775744#64)) tail.length =
      tail := by
    rw [hx2_eq, hs3]
    have hsplit : (s₀.readReg64 .x2).toNat = 64 * (key.length / 64) + tail.length := by omega
    have hadd := CryptoVerification.LibsignalAesCbc.Run.Bytes.readBytes_add s3.mem (s₀.readReg64 .x1) (64 * (key.length / 64)) tail.length
    rw [← hsplit, hkey_s3] at hadd
    have hdrop := congrArg (List.drop (64 * (key.length / 64))) hadd.symm
    rwa [List.drop_left' (Memory.readBytes_length _ _ _)] at hdrop
  have hrw_tail3 : s3.mem.RW
      (s₀.readReg64 .x1 + (s₀.readReg64 .x2 &&& 9223372036854775744#64)) tail.length := by
    rw [hx2_eq, hs3]
    exact hrw_key3.sub (by
      have := hdisj_key_stack.1
      clear * - hkey_len hkey_gt hkey_lt htail_len this
      bv_omega)
  have hd_dst_src3 : tail.length = 0 ∨ DisjointRegions
      (nfsSp s₀ + 176#64) tail.length
      (s₀.readReg64 .x1 + (s₀.readReg64 .x2 &&& 9223372036854775744#64)) tail.length := by
    by_cases ht0 : tail.length = 0
    · exact Or.inl ht0
    · refine Or.inr ?_
      rw [hx2_eq, hs3]
      have hd_sub : DisjointRegions
          (s₀.readReg64 .x1 + BitVec.ofNat 64 (64 * (key.length / 64))) tail.length
          (s₀.sp - 16928#64) 16928 :=
        hdisj_key_stack.sub_left _ ⟨by omega, by
          have := hdisj_key_stack.1
          clear * - hkey_len hkey_gt hkey_lt htail_len this
          bv_omega⟩
      exact (hd_sub.sub_right (nfsSp s₀ + 176#64)
        ⟨by omega, by clear * - htail_lt64; simp only [nfsSp]; bv_omega⟩).symm
  have hd_dst_ext3 : DisjointRegions (nfsSp s₀ + 176#64) tail.length
      (s3.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hcom3.sp_eq]
    clear * - hd_stk_ext htail_lt64
    simp only [DisjointRegions, extHookStack] at hd_stk_ext ⊢
    bv_omega
  have hd_src_ext3 : tail.length = 0 ∨ DisjointRegions
      (s₀.readReg64 .x1 + (s₀.readReg64 .x2 &&& 9223372036854775744#64)) tail.length
      (s3.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    by_cases ht0 : tail.length = 0
    · exact Or.inl ht0
    · refine Or.inr ?_
      rw [hcom3.sp_eq, hx2_eq, hs3]
      have hd_sub : DisjointRegions
          (s₀.readReg64 .x1 + BitVec.ofNat 64 (64 * (key.length / 64))) tail.length
          (s₀.sp - 16928#64) 16928 :=
        hdisj_key_stack.sub_left _ ⟨by omega, by
          have := hdisj_key_stack.1
          clear * - hkey_len hkey_gt hkey_lt htail_len this
          bv_omega⟩
      exact hd_sub.sub_right (nfsSp s₀ - BitVec.ofNat 64 extHookStack)
        ⟨by decide, by clear * -; simp only [nfsSp, extHookStack]; bv_omega⟩
  have hmc := memcpy_opt_subroutine_runsTo hHooks.memcpy hfrz3 hsym3' hpc3 hcom3.status
    hx0_3 hx1_3 hx2_3 htail_s3
    (hrw_stk3.sub (by clear * - htail_lt64; bv_omega)) hrw_tail3
    (by rw [hcom3.sp_eq]; exact hrw_extstk3)
    hd_dst_src3 (Or.inr hd_dst_ext3) hd_src_ext3
    (by rw [hcom3.sp_eq]; exact hcom3.sp_align)
  refine hmc.mono fun s4 ⟨hpc4, hstat4, hcc34, _, hdst4, _, hfr34⟩ => ?_
  rw [hlr_3] at hpc4
  have hfr34_stk : S2Frame s3.mem s4.mem
      [(nfsSp s₀ + 176#64, tail.length), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    rwa [hcom3.sp_eq] at hfr34
  have hcom4 : NfsGt64CommonExt img.base s₀ s4 :=
    NfsGt64CommonExt.of_cc_hook hstat4 hcom3.sp_eq hcom3.sp_align
      hcom3.x29_eq hcom3.x19_eq hcom3.x22_eq hcom3.x25_eq hcom3.x26_eq hcom3.x27_eq
      hcc34 hcom3.frame_zero hfr34_stk ⟨by decide, by clear * - htail_lt64; bv_omega⟩
  have hpos_4 : s4.mem.read8 (nfsSp s₀ + 239#64) = BitVec.ofNat 8 (key.length - 64 * (key.length / 64)) := by
    have hread8 : s4.mem.read8 (nfsSp s₀ + 239#64) = s3.mem.read8 (nfsSp s₀ + 239#64) := by
      have hr239 := hrw_stk3.readable (nfsSp s₀ + 239#64) (by clear * -; simp only [InRegion]; bv_omega)
      refine hfr34_stk.1 (nfsSp s₀ + 239#64) hr239.1 hr239.2 ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      refine ⟨?_, ?_⟩
      · clear * - htail_lt64; simp only [OutsideRegion]; bv_omega
      · clear * - hd_stk_ext
        simp only [DisjointRegions, OutsideRegion, extHookStack] at hd_stk_ext ⊢
        bv_omega
    exact hread8.trans hpos_3
  have hst0_4 : s4.mem.readBytes (nfsSp s₀ + 240#64) 32 =
      shaStateBytes ((chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV) :=
    (s2Frame_hook_readBytes_stack_eq' hfr34_stk hrw_stk3 hd_stk_ext
      ⟨by decide, by decide⟩ (by clear * - htail_lt64; bv_omega)).trans hst0_3
  have hnblk_4 : s4.mem.read64 (nfsSp s₀ + 272#64) = BitVec.ofNat 64 (key.length / 64) :=
    (s2Frame_hook_read64_stack_eq' hfr34_stk hrw_stk3 hd_stk_ext
      (by decide) (by clear * - htail_lt64; bv_omega)).trans hnblk_3
  exact
    { pc_eq := hpc4
      common := hcom4
      tail_bytes := htail_len.symm ▸ hdst4
      pos_byte := hpos_4
      st0_bytes := hst0_4
      nblk_word := hnblk_4 }

/-! ## Cut `G2Ext` (`hex:6707c`) and Sub-segment 0b (`hex:6702c → hex:6707c`) -/

structure StateG2aExt (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (s₀ s : State) : Prop where
  pc_eq : s.pc = b + bv% (ls_off% "memset")
  common : NfsGt64CommonExt b s₀ s
  x0_eq : s.readReg64 .x0 =
    nfsSp s₀ + 288#64 + BitVec.ofNat 64 (key.length - 64 * (key.length / 64)) + 1#64
  x1_eq : (s.readReg64 .x1).truncate 8 = 0#8
  x2_eq : (s.readReg64 .x2).toNat = 63 - (key.length - 64 * (key.length / 64))
  lr_eq : s.readReg64 .lr = b + bv% (ls_off% newFromSlice3Name + 220)
  x20_eq : s.readReg64 .x20 = nfsSp s₀ + 352#64
  x21_eq : s.readReg64 .x21 = BitVec.ofNat 64 (key.length / 64)
  x23_eq : s.readReg64 .x23 = BitVec.ofNat 64 (key.length - 64 * (key.length / 64))
  x24_eq : s.readReg64 .x24 = BitVec.ofNat 64 (63 - (key.length - 64 * (key.length / 64)))
  mem_copy : ∃ m_copy : Memory,
    s.mem = m_copy.write8
      (nfsSp s₀ + 288#64 + BitVec.ofNat 64 (key.length - 64 * (key.length / 64))) 128#8 ∧
    m_copy.readBytes (nfsSp s₀ + 288#64) (key.length - 64 * (key.length / 64)) =
      key.drop (64 * (key.length / 64)) ∧
    m_copy.readBytes (nfsSp s₀ + 352#64) 32 =
      shaStateBytes ((chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV)

structure StateG2Ext (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (s₀ s : State) : Prop where
  pc_eq : s.pc = b + bv% (ls_off% newFromSlice3Name + 220)
  common : NfsGt64CommonExt b s₀ s
  x20_eq : s.readReg64 .x20 = nfsSp s₀ + 352#64
  x21_eq : s.readReg64 .x21 = BitVec.ofNat 64 (key.length / 64)
  x23_eq : s.readReg64 .x23 = BitVec.ofNat 64 (key.length - 64 * (key.length / 64))
  x24_eq : s.readReg64 .x24 = BitVec.ofNat 64 (63 - (key.length - 64 * (key.length / 64)))
  buf_eq : s.mem.readBytes (nfsSp s₀ + 288#64) 64 =
    innerPadBlock1 (key.drop (64 * (key.length / 64)))
  st0_bytes : s.mem.readBytes (nfsSp s₀ + 352#64) 32 =
    shaStateBytes ((chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV)

set_option maxHeartbeats 1600000 in
theorem nfs3_seg0b1_gt64_ext {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG1Ext b F key s₀ s)
    (hkey_gt : 64 < key.length)
    (hkey_lt : key.length < 2 ^ 63)
    (hrw_stack : RW s₀.mem (s₀.sp - 16928#64) 16928) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateG2aExt b F key s₀) := by
  rcases hs with ⟨hpc, hcom, htail_bytes, hpos_byte, hst0_bytes, hnblk_word⟩
  have hRW_s : s.mem.RW (nfsSp s₀) 544 := hcom.rw_stack hrw_stack
  rcases hcom with ⟨hstat, hsp, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27, hf_zero⟩
  set tail := key.drop (64 * (key.length / 64))
  have htail_len : key.length - 64 * (key.length / 64) = tail.length := by simp [tail]
  rw [htail_len] at htail_bytes hpos_byte
  clear htail_len
  have htail_lt : tail.length < 64 := by simp [tail]; omega
  have hze32 := zeroExtend64_truncate32_ofNat64 htail_lt
  have hze64 := zeroExtend64_ofNat8 htail_lt
  have hxor63 := xor_63_of_lt_64 htail_lt
  have hcw_pos1 : s.mem.canWrite (nfsSp s₀ + 288#64 + BitVec.ofNat 64 tail.length) 1 = true :=
    hRW_s.canWrite_sub (by bv_omega) (by decide)
  have hcw_pos2 : s.mem.canWrite (nfsSp s₀ + (288#64 + BitVec.ofNat 64 tail.length)) 1 = true :=
    hRW_s.canWrite_sub (by bv_omega) (by decide)
  iterate 20 nfs3gt_step
  refine RunsTo.refl ?_
  have hf_copy : S2Frame (nfsZeroMem s₀)
      (nfsCopy288Mem s.mem (nfsSp s₀) (BitVec.ofNat 64 (key.length / 64)))
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] :=
    s2Frame_zero_of_agreesOutside hf_zero
      (agreesOutside_nfsCopy288Mem s.mem (nfsSp s₀) (BitVec.ofNat 64 (key.length / 64))) (by decide)
  have hf_pre_ms : S2Frame (nfsZeroMem s₀)
      ((nfsCopy288Mem s.mem (nfsSp s₀) (BitVec.ofNat 64 (key.length / 64))).write8
        (nfsSp s₀ + 288#64 + BitVec.ofNat 64 tail.length) 128#8)
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] :=
    s2Frame_zero_of_agreesOutside hf_copy
      (by
        rw [BitVec.add_assoc]
        exact AgreesOutside.write8_self _ (nfsSp s₀ + (288#64 + BitVec.ofNat 64 tail.length)) 128#8)
      (by bv_omega)
  have htoNat_sub : (BitVec.ofNat 64 (63 - tail.length)).toNat = 63 - tail.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx0_ms : nfsSp s₀ + (288#64 + (BitVec.ofNat 64 tail.length + 1#64)) =
      nfsSp s₀ + 288#64 + BitVec.ofNat 64 tail.length + 1#64 := by
    simp only [BitVec.add_assoc]
  have htail_len' : tail.length = key.length - 64 * (key.length / 64) := by simp [tail]
  refine
    { pc_eq := rfl
      common :=
        { status := by simp only [arm64_norm, hstat]
          sp_eq := by simp only [arm64_norm, hsp]
          sp_align := hal_nfs
          x29_eq := by simp only [arm64_norm, hx29]
          x19_eq := by simp only [arm64_norm, hx19]
          x22_eq := by simp only [arm64_norm, hx22]
          x25_eq := by simp only [arm64_norm, hx25]
          x26_eq := by simp only [arm64_norm, hx26]
          x27_eq := by simp only [arm64_norm, hx27]
          frame_zero := by
            dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
            exact hf_pre_ms }
      x0_eq := by simp only [arm64_norm, hx0_ms, htail_len']
      x1_eq := by simp only [arm64_norm]
      x2_eq := by simp only [arm64_norm]; exact htail_len' ▸ htoNat_sub
      lr_eq := by simp only [arm64_norm]
      x20_eq := by simp only [arm64_norm]
      x21_eq := by simp only [arm64_norm]
      x23_eq := by simp only [arm64_norm, htail_len']
      x24_eq := by simp only [arm64_norm, htail_len']
      mem_copy := ⟨nfsCopy288Mem s.mem (nfsSp s₀) (BitVec.ofNat 64 (key.length / 64)),
        by
          dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
          rw [← htail_len', BitVec.add_assoc]
          rfl,
        by
          rw [← htail_len',
              readBytes_take_of_le _ (nfsSp s₀ + 288#64) (by omega : tail.length ≤ 64),
              readBytes_288_nfsCopy288Mem,
              ← readBytes_take_of_le s.mem (nfsSp s₀ + 176#64) (by omega : tail.length ≤ 64),
              htail_bytes],
        by rw [readBytes_352_nfsCopy288Mem, hst0_bytes]⟩ }

theorem readBytes_64_after_pad_memset_s2 {m_copy m' : Memory} {sp : BitVec 64}
    {tail : List (BitVec 8)}
    (htail_copy : m_copy.readBytes (sp + 288#64) tail.length = tail)
    (htail_lt : tail.length < 64)
    (hrw_stk : (m_copy.write8 (sp + 288#64 + BitVec.ofNat 64 tail.length) 128#8).RW (sp) 544)
    (hd_stk_ext : DisjointRegions sp 544 (sp - 16384#64) 16384)
    (hdst : m'.readBytes (sp + 288#64 + BitVec.ofNat 64 tail.length + 1#64) (63 - tail.length) =
      List.replicate (63 - tail.length) 0#8)
    (hfr : S2Frame (m_copy.write8 (sp + 288#64 + BitVec.ofNat 64 tail.length) 128#8) m'
      [(sp + 288#64 + BitVec.ofNat 64 tail.length + 1#64, 63 - tail.length),
       (sp - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    m'.readBytes (sp + 288#64) 64 = innerPadBlock1 tail := by
  set m_pre := m_copy.write8 (sp + 288#64 + BitVec.ofNat 64 tail.length) 128#8
  set m_hook := m_pre.writeBytes (sp + 288#64 + BitVec.ofNat 64 tail.length + 1#64)
    (List.replicate (63 - tail.length) 0#8)
  have hsplit : 64 = (tail.length + 1) + (63 - tail.length) := by omega
  have hadd1 := CryptoVerification.LibsignalAesCbc.Run.Bytes.readBytes_add m' (sp + 288#64) (tail.length + 1) (63 - tail.length)
  have hadd2 := CryptoVerification.LibsignalAesCbc.Run.Bytes.readBytes_add m_hook (sp + 288#64) (tail.length + 1) (63 - tail.length)
  rw [← hsplit] at hadd1 hadd2
  have h_addr : sp + 288#64 + BitVec.ofNat 64 (tail.length + 1) =
      sp + 288#64 + BitVec.ofNat 64 tail.length + 1#64 := by
    clear * - htail_lt; bv_omega
  rw [h_addr] at hadd1 hadd2
  have h_hi_hook : m_hook.readBytes (sp + 288#64 + BitVec.ofNat 64 tail.length + 1#64) (63 - tail.length) =
      List.replicate (63 - tail.length) 0#8 :=
    CryptoVerification.LibsignalAesCbc.Run.Layout.readBytes_writeBytes_eq m_pre
      (sp + 288#64 + BitVec.ofNat 64 tail.length + 1#64)
      (List.replicate (63 - tail.length) 0#8) (63 - tail.length) List.length_replicate (by omega)
  have hag_ms : AgreesOutside m_pre m_hook
      (sp + 288#64 + BitVec.ofNat 64 tail.length + 1#64) (63 - tail.length) := by
    have hlen : (List.replicate (63 - tail.length) 0#8).length = 63 - tail.length := List.length_replicate
    rw [← hlen]
    exact ProofLib.agreesOutside_writeBytes m_pre _ _
  have hd_lo : DisjointRegions (sp + 288#64 + BitVec.ofNat 64 tail.length + 1#64) (63 - tail.length)
      (sp + 288#64) (tail.length + 1) := by
    clear * - htail_lt; simp only [DisjointRegions]; bv_omega
  have hd_lo_ext : DisjointRegions (sp - BitVec.ofNat 64 extHookStack) extHookStack
      (sp + 288#64) (tail.length + 1) :=
    (hd_stk_ext.sub_left (sp + 288#64) ⟨by omega, by clear * - htail_lt; bv_omega⟩).symm
  have h_lo_m' : m'.readBytes (sp + 288#64) (tail.length + 1) =
      m_pre.readBytes (sp + 288#64) (tail.length + 1) :=
    s2Frame_readBytes_eq_of_readable hfr
      (hrw_stk.sub (by clear * - htail_lt; bv_omega)).readable
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hd_lo
        · exact hd_lo_ext)
      (by omega)
  have h_lo_hook : m_hook.readBytes (sp + 288#64) (tail.length + 1) =
      m_pre.readBytes (sp + 288#64) (tail.length + 1) :=
    (agreesOutside_toFrame hag_ms).readBytes_eq (by simp [hd_lo]) (by omega)
  have h_eq : m'.readBytes (sp + 288#64) 64 = m_hook.readBytes (sp + 288#64) 64 := by
    rw [hadd1, hadd2, h_lo_m', h_lo_hook, hdst, h_hi_hook]
  rw [h_eq]
  exact readBytes_64_after_pad_memset_lt64 m_copy (sp + 288#64) tail htail_copy htail_lt

theorem nfs3_seg0b2_gt64_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hHooks : SpqrKdfHooksExt img F ext)
    {key : List (BitVec 8)} {s₀ s : State}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hs : StateG2aExt img.base F key s₀ s)
    (hrw_stack : RW s₀.mem (s₀.sp - 16928#64) 16928)
    (hdisj_iv_stack : DisjointRegions (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (s₀.sp - 16928#64) 16928) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateG2Ext img.base F key s₀) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hlr, hx20, hx21, hx23, hx24,
    ⟨m_copy, hmem_s, htail_copy, hst0_copy⟩⟩
  have hRW_s : s.mem.RW (nfsSp s₀) 544 := hcom.rw_stack hrw_stack
  have hrw_extstk : s.mem.RW (nfsSp s₀ - 16384#64) 16384 := hcom.rw_extstk hrw_stack
  have hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384 :=
    disj_stk_extstk_of_disj_16928 hdisj_iv_stack
  set tail := key.drop (64 * (key.length / 64))
  have htail_len : key.length - 64 * (key.length / 64) = tail.length := by simp [tail]
  rw [htail_len] at hx0 hx2 hx23 hx24 hmem_s htail_copy
  clear htail_len
  have htail_lt : tail.length < 64 := by simp [tail]; omega
  set dst := nfsSp s₀ + 288#64 + BitVec.ofNat 64 tail.length + 1#64
  set len := 63 - tail.length
  have hrw_dst : s.mem.RW dst len := hRW_s.sub (by clear * - htail_lt; simp only [dst, len]; bv_omega)
  have hd_dst_ext : DisjointRegions dst len (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hcom.sp_eq]
    have h_dst : dst = nfsSp s₀ + BitVec.ofNat 64 (289 + tail.length) := by
      clear * - htail_lt; simp only [dst]; bv_omega
    rw [h_dst]
    clear * - hd_stk_ext htail_lt
    simp only [DisjointRegions, extHookStack, len] at hd_stk_ext ⊢
    bv_omega
  have hms := memset_subroutine_runsTo hHooks.memset
    hfrz hsym hpc hcom.status hx0 hx1 hx2 hrw_dst
    (by rw [hcom.sp_eq]; exact hrw_extstk)
    hd_dst_ext (by rw [hcom.sp_eq]; exact hcom.sp_align)
  refine hms.mono fun s' ⟨hpc', hstat', hcc, _, hdst', hfr⟩ => ?_
  rw [hlr] at hpc'
  have hfr_stk : S2Frame s.mem s'.mem
      [(nfsSp s₀ + (288#64 + BitVec.ofNat 64 tail.length + 1#64), len),
       (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    have h_assoc : dst = nfsSp s₀ + (288#64 + BitVec.ofNat 64 tail.length + 1#64) := by
      simp only [dst, BitVec.add_assoc]
    rwa [hcom.sp_eq, h_assoc] at hfr
  have hcom' : NfsGt64CommonExt img.base s₀ s' :=
    NfsGt64CommonExt.of_cc_hook hstat' hcom.sp_eq hcom.sp_align
      hcom.x29_eq hcom.x19_eq hcom.x22_eq hcom.x25_eq hcom.x26_eq hcom.x27_eq
      hcc hcom.frame_zero hfr_stk ⟨by clear * - htail_lt; bv_omega, by clear * - htail_lt; simp only [len]; bv_omega⟩
  have hst0_s : s.mem.readBytes (nfsSp s₀ + 352#64) 32 =
      shaStateBytes ((chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV) := by
    rw [hmem_s]
    have hag8 : AgreesOutside m_copy (m_copy.write8 (nfsSp s₀ + 288#64 + BitVec.ofNat 64 tail.length) 128#8)
        (nfsSp s₀ + 288#64 + BitVec.ofNat 64 tail.length) 1 :=
      AgreesOutside.write8_self _ _ _
    have hd8 : DisjointRegions (nfsSp s₀ + 288#64 + BitVec.ofNat 64 tail.length) 1
        (nfsSp s₀ + 352#64) 32 := by
      clear * - htail_lt; simp only [DisjointRegions]; bv_omega
    exact ((agreesOutside_toFrame hag8).readBytes_eq (by simp [hd8]) (by decide)).trans hst0_copy
  have hst0' : s'.mem.readBytes (nfsSp s₀ + 352#64) 32 =
      shaStateBytes ((chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV) := by
    by_cases hlen0 : len = 0
    · have hfr0 : S2Frame s.mem s'.mem
          [(nfsSp s₀ + 288#64, 0), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
        refine hfr_stk.mono fun a ha r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simp only [OutsideRegion, hlen0]
          exact Nat.zero_le _
        · exact ha _ (by simp)
      exact (s2Frame_hook_readBytes_stack_eq' hfr0 hRW_s hd_stk_ext
        ⟨by decide, by decide⟩ (by decide)).trans hst0_s
    · exact (s2Frame_hook_readBytes_stack_eq' hfr_stk hRW_s hd_stk_ext
        ⟨by decide, by decide⟩
        (by clear * - htail_lt hlen0; simp only [DisjointRegions, len] at hlen0 ⊢; bv_omega)).trans hst0_s
  have htail_len' : tail.length = key.length - 64 * (key.length / 64) := by simp [tail]
  exact
    { pc_eq := hpc'
      common := hcom'
      x20_eq := hcc.2.2.1.trans hx20
      x21_eq := hcc.2.2.2.1.trans hx21
      x23_eq := hcc.2.2.2.2.2.1.trans (htail_len' ▸ hx23)
      x24_eq := hcc.2.2.2.2.2.2.1.trans (htail_len' ▸ hx24)
      buf_eq := readBytes_64_after_pad_memset_s2 htail_copy htail_lt
        (hmem_s ▸ hRW_s) hd_stk_ext hdst'
        (by rwa [hmem_s, hcom.sp_eq] at hfr)
      st0_bytes := hst0' }

theorem nfs3_seg0b_gt64_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hHooks : SpqrKdfHooksExt img F ext)
    {key : List (BitVec 8)} {s₀ s : State}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hs : StateG1Ext img.base F key s₀ s)
    (hkey_gt : 64 < key.length)
    (hkey_lt : key.length < 2 ^ 63)
    (hrw_stack : RW s₀.mem (s₀.sp - 16928#64) 16928)
    (hdisj_iv_stack : DisjointRegions (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (s₀.sp - 16928#64) 16928) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateG2Ext img.base F key s₀) := by
  have h1 : RunsToE (tripleRatchetProgAtExt img.base ext) s _ :=
    hmacRunsTo_to_runsToE (nfs3_seg0b1_gt64_ext hs hkey_gt hkey_lt hrw_stack)
  refine h1.trans_full fun s1 hs1 hkf1 hsym1 => ?_
  exact nfs3_seg0b2_gt64_ext hHooks (hfrz.of_keepsFrozen hkf1) (hsym1.trans hsym)
    hs1 hrw_stack hdisj_iv_stack

end CryptoVerification.SpqrV1.Kdf.Nfs3Ext
