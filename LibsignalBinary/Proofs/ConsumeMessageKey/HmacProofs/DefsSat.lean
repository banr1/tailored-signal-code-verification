/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.Defs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import

/-!
# `HookSat` `memset` / `HookSatExactMemcpy` Steps and `S2Frame` Bridges for `HmacProofs`

Provides `placed_memset_step_sat` under `HookSat H lsMemsetSym sessionMemsetRegionSpec` and
`placed_memcpy_step_sat_exact` under `HookSatExactMemcpy H lsMemcpySym` (siblings of
`CryptoHmacSha256.RunsTo.placed_memset_step` and `CryptoHmacSha256.RunsTo.placed_memcpy_step` in
`ConsumeMessageKey/HmacProofs/Defs.lean:938`), together with `S2Frame` and `AgreesOn` bridge lemmas
for `CryptoHmacSha256.Frame` and `HmacSaved`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat

open Arm64 ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsρ)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
  (Frame HmacSaved RunsTo RunsToFrom TraceEq lsMemcpySym lsMemsetSym ls_externAt?_of_mem)
open CryptoVerification.LibsignalTripleRatchet (sessionMemsetRegionSpec)
open CryptoVerification.LibsignalTripleRatchet.Extract (S2Frame)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt (AgreesOn AgreesOn.read64_eq AgreesOn.readBytes_eq)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (MemcpyClobber applyMemcpyClobber)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
  (HookSatExactMemcpy placed_memcpy_step_of_exact)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (hookOk_sessionMemsetRegion_elim)

public theorem s2Frame_of_hmacFrame {m₁ m₂ : Memory} {rs : List (BitVec 64 × Nat)}
    (hf : Frame m₁ m₂ rs) : S2Frame m₁ m₂ rs := by
  refine ⟨fun a _ _ hout => hf.1 a hout, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · intro a hrw
    obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hrw
    exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨by rw [hf.2.1, hp], hf.2.2.2.1 a hlf⟩
  · intro a hp; rw [hf.2.1, hp]
  · intro a ⟨hm, han⟩; rw [hf.2.1]; exact ⟨hm, hf.2.2.2.2 a han⟩
  · intro a hp hout
    refine ⟨by rw [hf.2.1, hp], fun hlf => ⟨hf.1 a hout, hf.2.2.2.1 a hlf⟩⟩
  · intro a hr hlf; rw [hf.2.1]; exact ⟨hr, hf.2.2.2.1 a hlf⟩

public theorem s2Frame_readable_of_readable {m₁ m₂ : Memory} {rs : List (BitVec 64 × Nat)}
    (hf : S2Frame m₁ m₂ rs) {base : BitVec 64} {len : Nat}
    (hread : m₁.Readable base len) : m₂.Readable base len :=
  fun a ha => hf.2.2 a (hread a ha).1 (hread a ha).2

public theorem s2Frame_readBytes_eq_of_readable {m₁ m₂ : Memory} {rs : List (BitVec 64 × Nat)}
    (hf : S2Frame m₁ m₂ rs) {base : BitVec 64} {len : Nat}
    (hread : m₁.Readable base len) (hlen : len ≤ 2 ^ 64)
    (hd : ∀ r ∈ rs, DisjointRegions r.1 r.2 base len) :
    m₂.readBytes base len = m₁.readBytes base len := by
  refine AgreesOn.readBytes_eq (P := fun a => InRegion base len a)
    (fun a hin => hf.1 a (hread a hin).1 (hread a hin).2 fun r hr => ?_)
    base len hlen (fun _ ha => ha)
  have hdr := hd r hr
  dsimp only [DisjointRegions] at hdr
  dsimp only [InRegion] at hin
  dsimp only [OutsideRegion]
  bv_omega

public theorem hmacSaved_of_agreesOn {P : BitVec 64 → Prop} {s₀ : State} {hsp_addr : BitVec 64}
    {m₁ m₂ : Memory}
    (hag : AgreesOn P m₁ m₂)
    (hs : HmacSaved s₀ hsp_addr m₂)
    (hP : ∀ a, InRegion (hsp_addr + 384#64) 96 a → P a) :
    HmacSaved s₀ hsp_addr m₁ := by
  rcases hs with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have sub8 (off : BitVec 64) (hoff : (off - (hsp_addr + 384#64)).toNat + 8 ≤ 96) :
      ∀ a, InRegion off 8 a → P a :=
    fun a ha => hP a (by unfold InRegion at ha ⊢; bv_omega)
  exact ⟨(AgreesOn.read64_eq hag (hsp_addr + 384#64) (sub8 _ (by clear * -; bv_omega))).trans h1,
         (AgreesOn.read64_eq hag (hsp_addr + 392#64) (sub8 _ (by clear * -; bv_omega))).trans h2,
         (AgreesOn.read64_eq hag (hsp_addr + 400#64) (sub8 _ (by clear * -; bv_omega))).trans h3,
         (AgreesOn.read64_eq hag (hsp_addr + 416#64) (sub8 _ (by clear * -; bv_omega))).trans h4,
         (AgreesOn.read64_eq hag (hsp_addr + 424#64) (sub8 _ (by clear * -; bv_omega))).trans h5,
         (AgreesOn.read64_eq hag (hsp_addr + 432#64) (sub8 _ (by clear * -; bv_omega))).trans h6,
         (AgreesOn.read64_eq hag (hsp_addr + 440#64) (sub8 _ (by clear * -; bv_omega))).trans h7,
         (AgreesOn.read64_eq hag (hsp_addr + 448#64) (sub8 _ (by clear * -; bv_omega))).trans h8,
         (AgreesOn.read64_eq hag (hsp_addr + 456#64) (sub8 _ (by clear * -; bv_omega))).trans h9,
         (AgreesOn.read64_eq hag (hsp_addr + 464#64) (sub8 _ (by clear * -; bv_omega))).trans h10,
         (AgreesOn.read64_eq hag (hsp_addr + 472#64) (sub8 _ (by clear * -; bv_omega))).trans h11⟩

/-- Step `lsMemsetSym` in a placed block under `HookSat H lsMemsetSym sessionMemsetRegionSpec`. -/
public theorem placed_memset_step_sat [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    (h_memset : HookSat H lsMemsetSym sessionMemsetRegionSpec)
    {s₀ s : State} {P_post : State → Prop}
    {m₀ : Memory} {dst lr : BitVec 64} {val : BitVec 8} {len : Nat}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemsetSym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = val)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hmem : s.mem = m₀)
    (hrw : m₀.RW dst len)
    (h : ∀ s' : State,
      TraceEq s₀ s' →
      s'.pc = lr →
      s'.status = .Running →
      CallingConventionPreserved s s' →
      s'.readReg64 .x0 = dst →
      m₀.KeepsFrozen s'.mem →
      s'.mem.readBytes dst len = List.replicate len val →
      S2Frame m₀ s'.mem [(dst, len)] →
      AgreesOn (fun a => (m₀.perm a).r = true ∧ m₀.isLazyFree a = false)
        s'.mem (m₀.writeBytes dst (List.replicate len val)) →
      RunsToFrom prog s₀ s' P_post)
    (htr_s : TraceEq s₀ s := by
      repeat' (first
        | with_reducible apply TraceEq.advancePC_step
        | with_reducible apply TraceEq.setMem_step
        | with_reducible apply TraceEq.setPC_step
        | with_reducible apply TraceEq.setPState_step
        | with_reducible apply TraceEq.writeReg64_step
        | with_reducible apply TraceEq.writeReg32_step
        | with_reducible apply TraceEq.writeVReg128_step (by decide)
        | with_reducible exact TraceEq.refl _))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s P_post := by
  obtain ⟨f, hfH, hfOk⟩ := h_memset
  have hhook : prog.externAt? s.pc = some f := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, hfH]
  have hrw_s : s.mem.RW dst len := hmem ▸ hrw
  obtain ⟨hkf, hsym, hret, hcc, hx0', htr', hread', hs2', hag'⟩ :=
    hookOk_sessionMemsetRegion_elim hfOk hrun hx0 hx1 hx2 hsp_al hrw_s
  have htr_s' : TraceEq s₀ (f s) :=
    ⟨htr'.trans htr_s.1, hcc.2.2.2.2.2.2.2.2.2.2.2.2.trans htr_s.2⟩
  have hpc' : (f s).pc = lr := hret.1.trans hlr
  have hkf_m₀ : m₀.KeepsFrozen (f s).mem := hmem ▸ hkf
  have hs2_m₀ : S2Frame m₀ (f s).mem [(dst, len)] := hmem ▸ hs2'
  have hag_m₀ : AgreesOn (fun a => (m₀.perm a).r = true ∧ m₀.isLazyFree a = false)
      (f s).mem (m₀.writeBytes dst (List.replicate len val)) := hmem ▸ hag'
  exact RunsTo.hook hrun hhook hkf hsym
    (h (f s) htr_s' hpc' hret.2.2 hcc hx0' hkf_m₀ hread' hs2_m₀ hag_m₀)

/-- `HookSatExactMemcpy` sibling of `CryptoHmacSha256.RunsTo.placed_memcpy_step`
(`ConsumeMessageKey/HmacProofs/Defs.lean:938`), stepping through `lsρ lsMemcpySym` under
`HookSatExactMemcpy H lsMemcpySym` into `applyMemcpyClobber s (m₀.writeBytes dst bs) lr c`
with exact memory `m₀.writeBytes dst bs` (zero `S2Frame` re-anchoring). -/
public theorem placed_memcpy_step_sat_exact [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    {s₀ s : State} {P_post : State → Prop}
    {m₀ : Memory} {dst src lr : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemcpySym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hmem : s.mem = m₀)
    (hread : m₀.readBytes src len = bs)
    (hrw : m₀.RW dst len)
    (hreadable : m₀.Readable src len)
    (hdisj : len = 0 ∨ DisjointRegions dst len src len)
    (h : ∀ c : MemcpyClobber,
      RunsToFrom prog s₀ (applyMemcpyClobber s (m₀.writeBytes dst bs) lr c) P_post)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s P_post := by
  have hsp : s.spAligned = true := by simpa [State.spAligned] using hsp_al
  exact placed_memcpy_step_of_exact h_memcpy hrun hsp hpc hx0 hx1 hx2 hlr
    hmem hread hrw hreadable hdisj h hi hunmut

end LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat
