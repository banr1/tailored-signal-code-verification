/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyber
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.Fetch
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyberb
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes

/-!
# `PreKeySignalMessage::try_from`: Missing-Kyber v4 Error and Full Kyber Dispatch (`+0x684..+0x830` / `+0xa24`)

Proves the 54-byte missing-Kyber v4 error branch (`kyber_neither_v4_err_wpE`,
`+0x6c8 → +0xa24` / `+0xa80`) and assembles the full Kyber `Ok` (`w5b_kyber_ok_wp`,
`+0x684 → +0x830`) and `Err` (`w5b_kyber_err_wpE`, `+0x684 → +0xa24`) transitions.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack SepWPp
open CryptoVerification.SignalSession.Cli

private abbrev SepWPp := Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
private abbrev SepWPp.of_sepWP_frozen := @Wire.SepWPp.of_sepWP_frozen
private abbrev SepWPp.of_sepWP_end := @Wire.SepWPp.of_sepWP_end
private abbrev SepWPp.panic := @Wire.SepWPp.panic
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.bind_entails := @Wire.SepWPp.bind_entails
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.call_noPanic_tryFromX := @Wire.SepWPp.call_noPanic_tryFrom

open Lean Meta Elab Tactic in
local elab "pksm_fetches " b:term:max H:term:max hfn:ident
    k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat
    (← `(ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))
    "pksm_fetches"
  let offLit := Syntax.mkNumLit (toString off)
  evalTactic (← `(tactic|
    responder_wire_fetches_from $b $H $hfn $offLit $k0 $len))

private theorem bv_sub_add_lit_k (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem bv_sub_sub_lit_k (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega
private theorem bv_add_neg_8X (x : BitVec 64) : x + bv% (2 ^ 64 - 8) = x - 8#64 := by bv_omega
private theorem bv_add_neg_16X (x : BitVec 64) : x + bv% (2 ^ 64 - 16) = x - 16#64 := by bv_omega
private theorem bv_add_neg_24X (x : BitVec 64) : x + bv% (2 ^ 64 - 24) = x - 24#64 := by bv_omega
private theorem bv_add_neg_32X (x : BitVec 64) : x + bv% (2 ^ 64 - 32) = x - 32#64 := by bv_omega
private theorem bv_add_neg_40X (x : BitVec 64) : x + bv% (2 ^ 64 - 40) = x - 40#64 := by bv_omega
private theorem bv_add_neg_48X (x : BitVec 64) : x + bv% (2 ^ 64 - 48) = x - 48#64 := by bv_omega
private theorem bv_add_neg_56X (x : BitVec 64) : x + bv% (2 ^ 64 - 56) = x - 56#64 := by bv_omega
private theorem bv_add_neg_512X (x : BitVec 64) : x + bv% (2 ^ 64 - 512) = x - 512#64 := by bv_omega

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
ls_attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit_k bv_sub_sub_lit_k BitVec.toNat_zero
  bv_add_neg_8X bv_add_neg_16X bv_add_neg_24X bv_add_neg_32X bv_add_neg_40X
  bv_add_neg_48X bv_add_neg_56X bv_add_neg_512X
  bv_reconstruct_low8 bv_reconstruct_low8_dec bv_zext8_mask truncate16_zext32
  append64_extract_lo append64_extract_hi append32_extract_lo append32_extract_hi
  append32_truncate zeroExtend32_truncate8_eq extractLsb0_8_append56
  zeroExtend32_lsr4_truncate8
  (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "alloc::raw_vec::handle_error")

theorem L1_PksmWire_W5bKyberc : True := trivial

/-! ## 1. Pure `pksmParse` Bridges for Kyber Dispatch Errors -/

/-- Pure `pksmParse` corollary (`m.kyberPreKeyId = none`, `m.kyberCiphertext = none`,
`0x40 ≤ vb.toNat`): `Pksm.pksmParse (vb :: body) = none`. -/
theorem pksmParse_eq_none_of_kyber_neither_v4 {vb : BitVec 8} {body : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} (hd : Pksm.decodeProto body = some m)
    (hvb_ge : 0x40 ≤ vb.toNat)
    (h1 : m.kyberPreKeyId = none) (h2 : m.kyberCiphertext = none) :
    Pksm.pksmParse (vb :: body) = none := by
  by_cases h4f : vb ≤ 0x4f#8
  · have hv : 0x40#8 ≤ vb := BitVec.le_def.mpr hvb_ge
    exact pksmParse_kyberBad hd (kyberOk_false_of_neither_v4 hv h4f h1 h2)
  · have hgt : 0x4f#8 < vb := by
      rw [BitVec.le_def] at h4f
      rw [BitVec.lt_def]
      change 79 < vb.toNat
      change ¬ (vb.toNat ≤ 79) at h4f
      omega
    exact pksmParse_unrec hgt

/-- Combined pure `pksmParse` corollary for Kyber dispatch `Err` branches. -/
theorem pksmParse_eq_none_of_w5b_kyber_err {vb : BitVec 8} {body : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} (hd : Pksm.decodeProto body = some m)
    (herr : (m.kyberPreKeyId.isSome != m.kyberCiphertext.isSome) = true ∨
      (m.kyberPreKeyId = none ∧ m.kyberCiphertext = none ∧ 0x40 ≤ vb.toNat)) :
    Pksm.pksmParse (vb :: body) = none := by
  rcases herr with hhalf | ⟨h1, h2, hvb_ge⟩
  · exact pksmParse_eq_none_of_kyber_half hd hhalf
  · exact pksmParse_eq_none_of_kyber_neither_v4 hd hvb_ge h1 h2

/-! ## 2. ``kyber_neither_v4_err_wpE``: (`+0x6c8 → +0xa24` / `+0xa80`) -/

/-- (``+0x6c8 → +0xa24` / `+0xa80`, dec `1736 → 2596``):
When `kpkTag = 0#32`, `kyberOpt = none` (`kyberCap = noneCap`), and `0x40 ≤ vb.toNat`:
branches `+0x6c8` (`1736`) → `+0x718` (`1816`) → `+0x818` (`2072`) → `+0x998` (`2456`),
allocates the 54-byte `.rodata` error string (`"PreKeySignalMessage missing Kyber prekey or ciphertext"`),
panics via `+0xa80` (`handle_error`) on OOM (`tryFromQp s0`), otherwise writes
`pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext)` keeping the 54-byte `String` inside
`speAt` as `vecU8`, and reaches `+0xa24` (`2596`) in `KyberExitA24State`. -/
theorem kyber_neither_v4_err_wpE {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext)
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen ikCap msgCap : BitVec 64}
    {vb : BitVec 8}
    (hvb_ge : 0x40 ≤ vb.toNat)
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1736#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState32 0#32 1#32)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (_hx25 : s.readReg64 .x25 = kyberPtr) (hx23 : s.readReg64 .x23 = ikCap)
    (hx22 : s.readReg64 .x22 = vb.zeroExtend 64) (hx21 : s.readReg64 .x21 = ptr0)
    (hx20 : s.readReg64 .x20 = len) (hx19 : s.readReg64 .x19 = sret) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 2596#64) s
      (optVecU8Buf A kyberCap kyberPtr kyberLen none ∗
        memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        KyberExitA24State img s0 sp' sret len ptr0 ikCap msgCap vb sf ∧
        (Pf ⊢ (pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  dsimp only [optVecU8Buf]
  refine SepWPp.pure_pre fun hcap => ?_
  subst hcap
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hshim := shim_ok_at_prekeyX hA
  have halloc := alloc_ok_at_prekeyX hA
  have hpan := panic_at_prekey_handle_errorX (b := img.base) (ext := ext)
  clear hA
  have hvb_ule := ule_64_vb_eq_true hvb_ge
  let H := Rust.withPanics ext
  have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
      num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  pksm_fetches img.base H hfn 1736 4
  pksm_fetches img.base H hfn 1816 8
  pksm_fetches img.base H hfn 2072 8
  pksm_fetches img.base H hfn 2456 88
  pksm_fetches img.base H hfn 2688 12; clear hfn
  have hadrp := adrp_prekey_2476 (H := H) (ProofLib.ObjectLoad.base_aligned_of_loads himg)
  dsimp only [contractProg, tripleRatchetProgAtExt] at hshim halloc hpan hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hstack := stackAt_skipFieldStackX_ext sp'
  refine SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% preKeyTryFromName)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine SepWPp.call_noPanic_tryFromX () hshim
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by tryFromPost_sp_align hsp) hF1 hsym1
    (ret_pc := entry + 2460#64) (by simp [arm64_norm])
    (T := stackAt sp' extHookStack)
    (φ := True)
    (by simp [session2ShimSpecX, hsp_eq, arm64_norm])
    trivial
    (by rw [hstack]; sep_focus)
    ?_
  clear hshim
  intro s1 hpc1 hrun1 hsp1 hsp1_align hF1' hsym1' hcs1
  dsimp only [session2ShimSpecX]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr1 => ?_
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, _, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, _⟩
  have hsp1_eq : s1.sp = sp' := by tryFromPost_sp [hsp1, hsp_eq]
  refine SepWPp.of_sepWP_frozen hF1' hsym1'
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% preKeyTryFromName)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun1, arm64_norm]) fun hF2 hsym2 => ?_
  have hlay54 : LayoutOk 54 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  refine SepWPp.call_noPanic_tryFromX (54, 1) halloc
    (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
    (by tryFromPost_sp_align hsp1_align) hF2 hsym2
    (ret_pc := entry + 2472#64) (by simp [arm64_norm])
    (T := A.pool ∗ stackAt sp' extHookStack)
    (φ := (54#64 : BitVec 64).toNat = 54 ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk 54 1)
    (by simp [rustAllocSpecWithStack, hsp1_eq, arm64_norm])
    ⟨rfl, rfl, hlay54⟩
    (by simp only [hsp_eq, arm64_norm]; sep_focus)
    ?_
  clear halloc
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2' hsym2' hcs2
  dsimp only [rustAllocSpecWithStack]
  rw [sepConj_rot3_kyber]
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, _, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, _⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp1_eq]
  by_cases hoom : s2.readReg64 .x0 = 0
  · simp only [hoom, ite_true]
    refine SepWPp.pure_pre fun htr2 => ?_
    refine SepWPp.of_sepWP_frozen hF2' hsym2'
      (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% preKeyTryFromName)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun _ _ => ?_
    refine SepWPp.panic (by simp [hrun2, arm64_norm])
      (by simpa [arm64_norm] using hpan)
      (tryFromQp_of_panicked (by simp [Rust.panicked, htr2, htr1, htr, arm64_norm]))
  · clear hpan
    simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨_, htr2⟩ => ?_
    have hbeq : (s2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    rw [memRegion54_unpack (s2.readReg64 .x0), memRegion248_split_err sret]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun s0_6 => SepWPp.exists_pre fun s0_5 =>
      SepWPp.exists_pre fun s0_4 => SepWPp.exists_pre fun s0_3 =>
      SepWPp.exists_pre fun s0_2 => SepWPp.exists_pre fun s0_1 =>
      SepWPp.exists_pre fun s0_0 =>
      SepWPp.exists_pre fun w5 => SepWPp.exists_pre fun w4 =>
      SepWPp.exists_pre fun w3 => SepWPp.exists_pre fun w2 =>
      SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w0 => ?_
    refine SepWPp.of_sepWP_frozen hF2' hsym2' (mid := entry + 2504#64) ?_
    refine SepWP.rodata64_intro (rodata_ro8_at himg (num% (ls_xref% (ls_off% preKeyTryFromName + 2476) (ls_off% preKeyTryFromName + 2480))) (by decide +kernel) hF2'.roData) rfl ?_
    refine SepWP.rodata64_intro (rodata_ro8_at himg (num% (ls_xref% (ls_off% preKeyTryFromName + 2476) (ls_off% preKeyTryFromName + 2480) + 8)) (by decide +kernel) hF2'.roData) rfl ?_
    refine SepWP.rodata64_intro (rodata_ro8_at himg (num% (ls_xref% (ls_off% preKeyTryFromName + 2476) (ls_off% preKeyTryFromName + 2480) + 16)) (by decide +kernel) hF2'.roData) rfl ?_
    refine SepWP.rodata64_intro (rodata_ro8_at himg (num% (ls_xref% (ls_off% preKeyTryFromName + 2476) (ls_off% preKeyTryFromName + 2480) + 24)) (by decide +kernel) hF2'.roData) rfl ?_
    refine SepWP.rodata64_intro (rodata_ro8_at himg (num% (ls_xref% (ls_off% preKeyTryFromName + 2476) (ls_off% preKeyTryFromName + 2480) + 32)) (by decide +kernel) hF2'.roData) rfl ?_
    refine SepWP.rodata64_intro (rodata_ro8_at himg (num% (ls_xref% (ls_off% preKeyTryFromName + 2476) (ls_off% preKeyTryFromName + 2480) + 40)) (by decide +kernel) hF2'.roData) rfl ?_
    refine SepWP.rodata64_intro (rodata_ro8_at himg (num% (ls_xref% (ls_off% preKeyTryFromName + 2476) (ls_off% preKeyTryFromName + 2480) + 46)) (by decide +kernel) hF2'.roData) rfl ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hF3 hsym3 => ?_
    have hshift := shift_window_40_to_46 (s2.readReg64 .x0)
      (s2.mem.read64 (img.base + BitVec.ofNat 64 (num% (ls_xref% (ls_off% preKeyTryFromName + 2476) (ls_off% preKeyTryFromName + 2480) + 40))))
    refine SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right
              (Entails.trans (by apply entails_of_eq; rw [← sepConj_assoc])
                (Entails.trans (sepConj_mono_left hshift)
                  (by apply entails_of_eq; rw [sepConj_assoc])))))))))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_pre fun w46 => ?_
    refine SepWPp.of_sepWP_end hF3 hsym3 ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hF4 hsym4 => ?_
    refine ⟨⟨⟨by tryFromPost_sp [hsp2_eq], by tryFromPost_sp_align hsp2_align, hF4, hsym4,
          by simp [htr2, htr1, htr, arm64_norm]⟩,
        by simp [hx29_2, hx29_1, hx29, arm64_norm],
        by simp [hx26_2, hx26_1, hx26, arm64_norm],
        by simp [hx23_2, hx23_1, hx23, arm64_norm],
        by simp [hx22_2, hx22_1, hx22, arm64_norm],
        by simp [hx21_2, hx21_1, hx21, arm64_norm],
        by simp [hx20_2, hx20_1, hx20, arm64_norm],
        by simp [hx19_2, hx19_1, hx19, arm64_norm]⟩, ?_⟩
    let rOff := num% (ls_xref% (ls_off% preKeyTryFromName + 2476) (ls_off% preKeyTryFromName + 2480))
    have hpack54 := memRegion54_pack (s2.readReg64 .x0)
      (s2.mem.read64 (img.base + BitVec.ofNat 64 rOff))
      (s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 8)))
      (s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 16)))
      (s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 24)))
      (s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 32)))
      (s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 46)))
    have herr := freshString_entails_pksmErrE A sret (s2.readReg64 .x0)
      (s0_5 &&& bv% (2 ^ 64 - 256) ||| 3#64) s0_6 54
      (((img.base + BitVec.ofNat 64 rOff) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 rOff)) ∗
        ((img.base + BitVec.ofNat 64 (rOff + 8)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 8))) ∗
        ((img.base + BitVec.ofNat 64 (rOff + 16)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 16))) ∗
        ((img.base + BitVec.ofNat 64 (rOff + 24)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 24))) ∗
        ((img.base + BitVec.ofNat 64 (rOff + 32)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 32))) ∗
        ((img.base + BitVec.ofNat 64 (rOff + 40)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 40))) ∗
        ((img.base + BitVec.ofNat 64 (rOff + 46)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 46))))
      (by decide) (by decide) hoom (bf_low8_eq_3 s0_5)
    have herr' :
        (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 24) ∗
          ((sret + 16#64) ↦₆₄ 54#64) ∗ ((sret + 24#64) ↦₆₄ s2.readReg64 .x0) ∗
          ((sret + 32#64) ↦₆₄ 54#64) ∗
          ((sret + 40#64) ↦₆₄ (s0_5 &&& bv% (2 ^ 64 - 256) ||| 3#64)) ∗
          ((sret + 48#64) ↦₆₄ s0_6) ∗ memRegion (sret + 56#64) 192 ∗
          A.live (s2.readReg64 .x0) 54 1 ∗
          (((s2.readReg64 .x0) ↦₆₄ s2.mem.read64 (img.base + BitVec.ofNat 64 rOff)) ∗
            ((s2.readReg64 .x0 + 8#64) ↦₆₄ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 8))) ∗
            ((s2.readReg64 .x0 + 16#64) ↦₆₄ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 16))) ∗
            ((s2.readReg64 .x0 + 24#64) ↦₆₄ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 24))) ∗
            ((s2.readReg64 .x0 + 32#64) ↦₆₄ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 32))) ∗
            memRegion (s2.readReg64 .x0 + 40#64) 6 ∗
            ((s2.readReg64 .x0 + 46#64) ↦₆₄ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 46)))) ∗
          (((img.base + BitVec.ofNat 64 rOff) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 rOff)) ∗
            ((img.base + BitVec.ofNat 64 (rOff + 8)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 8))) ∗
            ((img.base + BitVec.ofNat 64 (rOff + 16)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 16))) ∗
            ((img.base + BitVec.ofNat 64 (rOff + 24)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 24))) ∗
            ((img.base + BitVec.ofNat 64 (rOff + 32)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 32))) ∗
            ((img.base + BitVec.ofNat 64 (rOff + 40)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 40))) ∗
            ((img.base + BitVec.ofNat 64 (rOff + 46)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 46)))) ⊢
          pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap :=
      Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_left hpack54))))))))))
        herr
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono_left (Q := A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) herr')
        (by apply entails_of_eq; ac_rfl))
    dsimp only [rOff]
    simp only [hstack, hsp1_eq, errTag, speWord, arm64_norm]
    apply entails_of_eq; ac_rfl

/-! ## 3. ``w5b_kyber_ok_wp`, `w5b_kyber_err_wpE``: Full Kyber Dispatch (`+0x684 → +0x830` / `+0xa24`) -/

private theorem merge_err_anyHeap (E S : SepProp) :
    ((E ∗ anyHeap) ∗ S) ∗ anyHeap ⊢ E ∗ S ∗ anyHeap := by
  refine Entails.trans
    (Q := E ∗ S ∗ (anyHeap ∗ anyHeap))
    (by apply entails_of_eq; ac_rfl)
    (sepConj_mono_right (sepConj_mono_right (entails_anyHeap _)))

/-- (``+0x684 → +0x830`, dec `1668 → 2096``):
Composes `pk_scatter_head_wp`, `kyber_both_ok_wp`, and `kyber_neither_v3_ok_wp`
from `BaseKeyOkState` at `+0x684` (`1668`) to `KyberOkState` at `+0x830` (`2096`) with `kyberSpillsAtW`
and `kyberStageOut`. -/
theorem w5b_kyber_ok_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hIntoBox : IntoBoxedSliceOkX img A ext)
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen bkCap bkPtr bkLen
      ikCap ikPtr ikLen msgCap msgPtr msgLen : BitVec 64}
    {vb : BitVec 8}
    {regTag regVal opkTag opkVal spkVal kpkTag kpkVal : BitVec 32}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    {bk : List (BitVec 8)} {pk : PublicKey}
    (hkpk : match kpkOpt with | some id => kpkTag = 1#32 ∧ kpkVal = id | none => kpkTag = 0#32)
    (hok : (kpkOpt.isSome && kyberOpt.isSome) = true ∨
      (kpkOpt = none ∧ kyberOpt = none ∧ vb.toNat < 0x40))
    (hst : BaseKeyOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb bk pk s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1668#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 2096#64) s
      (memRegion (sp' + 12#64) 4 ∗
        seg1SpillsAtW sp' bkCap bkPtr bkLen kyberLen ikPtr ikLen msgPtr msgLen
          regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
        memRegion (sp' + 112#64) 32 ∗
        ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
        memRegion (sp' + 345#64) 15 ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        ∃ (kyberBoxPtr kyberBoxLen : BitVec 64)
          (b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8)
          (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64),
          (bk.take 33).drop 1 = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∧
          KyberOkState img s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb bk pk sf ∧
          (Pf ⊢ kyberSpillsAtW sp' bkCap bkPtr kyberLen ikPtr ikLen msgPtr msgLen
              regTag regVal opkTag opkVal spkVal kpkVal
              b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 w9 w13 w15 w23 ∗
            memRegion (sp' + 312#64) 48 ∗
            kyberStageOut A kpkVal vb kpkOpt kyberOpt kyberBoxPtr kyberBoxLen ∗
            A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hst_ep, hbk_ok, hpk_eq, hpk_bytes,
    hx29, hx28, hx27, hx26, hx25, _, hx23, hx22, hx21, hx20, hx19⟩
  have hlen32 : ((bk.take 33).drop 1).length = 32 := by
    rw [← hpk_bytes]; exact (pkOf bk).bytes.toList_length
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, w9, w13, w15, w23, b31, hpk_of⟩ :=
    exists_pkBytesOf ((bk.take 33).drop 1) hlen32
  have hpre_split :
      memRegion (sp' + 12#64) 4 ∗
        seg1SpillsAtW sp' bkCap bkPtr bkLen kyberLen ikPtr ikLen msgPtr msgLen
          regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
        memRegion (sp' + 112#64) 32 ∗
        ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
        memRegion (sp' + 345#64) 15 ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ⊢
      (((sp' + 68#64) ↦₃₂ kpkTag) ∗ memRegion (sp' + 112#64) 32 ∗
        ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
        memRegion (sp' + 345#64) 15) ∗
      (optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        memRegion (sp' + 12#64) 4 ∗
        ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkVal) ∗
        ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
        ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
        ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
        ((sp' + 72#64) ↦₆₄ bkLen) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) := by
    dsimp only [seg1SpillsAtW]
    apply entails_of_eq; ac_rfl
  refine SepWPp.mono_pre hpre_split ?_
  refine SepWPp.bind_frame_tryFrom
    (pk_scatter_head_wp hpk_of hst_ep hpc hrun hx29 hx28 hx27 hx26 hx25 hx23 hx22 hx21 hx20 hx19) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hst1, hpstate1, hx8_1, hx11_1, hx12_1,
    hx29_1, hx28_1, hx27_1, hx26_1, hx25_1, hx24_1, hx23_1, hx22_1, hx21_1, hx20_1, hx19_1, hent1⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_
  rcases hok with hboth | ⟨rfl, rfl, hvb_lt⟩
  · cases kpkOpt with
    | none => simp at hboth
    | some kpkId =>
      cases kyberOpt with
      | none => simp at hboth
      | some kyberCt =>
        rcases hkpk with ⟨rfl, rfl⟩
        have hvec_lt :
            optVecU8Buf A kyberCap kyberPtr kyberLen (some kyberCt) ⊢
              ⌜kyberLen = BitVec.ofNat 64 kyberCt.length ∧ kyberCap.toNat < 2 ^ 63⌝ ∗
                Wire.vecU8Buf A kyberCap kyberPtr kyberCt := by
          dsimp only [optVecU8Buf, Wire.vecU8Buf]
          refine Entails.pure_left fun hlen => Entails.pure_left fun ⟨hle, hlt, hne⟩ => ?_
          rw [pure_true_emp ⟨hlen, hlt⟩, emp_sepConj, pure_true_emp ⟨hle, hlt, hne⟩, emp_sepConj]
          exact Entails.refl _
        refine SepWPp.mono_pre (P' :=
            ⌜kyberLen = BitVec.ofNat 64 kyberCt.length ∧ kyberCap.toNat < 2 ^ 63⌝ ∗
            ((memRegion (sp' + 12#64) 4 ∗
              ((sp' + 40#64) ↦₆₄ kyberLen) ∗
              ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' + 72#64) ↦₆₄ bkLen) ∗
              memRegion (sp' + 312#64) 48 ∗
              Wire.vecU8Buf A kyberCap kyberPtr kyberCt ∗
              A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
             (((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
              ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkVal) ∗
              ((sp' + 32#64) ↦₆₄ msgLen) ∗
              ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
              ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
              ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
              ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
              spUnused112 sp' ∗
              ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
              ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
              sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6)))
          (by
            refine Entails.trans (sepConj_mono_right (sepConj_mono_left hvec_lt)) ?_
            apply entails_of_eq; ac_rfl) ?_
        refine SepWPp.pure_pre fun ⟨hky_len, hky_lt⟩ => ?_
        subst hky_len
        refine SepWPp.frame_tryFrom
          (kyber_both_ok_wp hIntoBox hbk_ok hpk_eq hpk_bytes hky_lt hst1 hpc1 hrun1 hpstate1
            hx8_1 hx11_1 hx12_1 hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx24_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1)
          fun sf Pf ⟨kyberBoxPtr, hstf, hptr_nz, hentf⟩ => ?_
        refine ⟨kyberBoxPtr, BitVec.ofNat 64 kyberCt.length,
          b0, b1, b2, b3, b4, b5, b6, b7, b8, b31, w9, w13, w15, w23,
          hpk_of, hstf, ?_⟩
        refine Entails.trans (sepConj_mono_left hentf) ?_
        dsimp only [kyberSpillsAtW, kyberStageOut]
        rw [pure_true_emp ⟨hptr_nz, rfl, rfl⟩, emp_sepConj]
        apply entails_of_eq; ac_rfl
  · subst hkpk
    refine SepWPp.mono_pre (P' :=
        optVecU8Buf A kyberCap kyberPtr kyberLen none ∗
        ((memRegion (sp' + 12#64) 4 ∗
          ((sp' + 68#64) ↦₃₂ 0#32) ∗ ((sp' + 72#64) ↦₆₄ bkLen)) ∗
         (((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
          ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkVal) ∗
          ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
          ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
          ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ spUnused112 sp' ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗ ((sp' + 128#64) ↦₃₂ w9) ∗
          ((sp' + 132#64) ↦₁₆ w13) ∗ sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          memRegion (sp' + 312#64) 48 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))))
      (by apply entails_of_eq; ac_rfl) ?_
    dsimp only [optVecU8Buf]
    refine SepWPp.pure_pre fun hcap => ?_
    subst hcap
    refine SepWPp.frame_tryFrom
      (kyber_neither_v3_ok_wp hbk_ok hpk_eq hpk_bytes hvb_lt hst1 hpc1 hrun1 hpstate1
        hx8_1 hx11_1 hx12_1 hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx24_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1)
      fun sf Pf ⟨hstf, hentf⟩ => ?_
    refine ⟨0#64, kyberPtr, b0, b1, b2, b3, b4, b5, b6, b7, b8, b31, w9, w13, w15, w23, hpk_of, hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_
    dsimp only [kyberSpillsAtW, kyberStageOut]
    rw [pure_true_emp ⟨rfl, hvb_lt⟩]; apply entails_of_eq; ac_rfl

/-- (``+0x684 → +0xa24`, dec `1668 → 2596``):
Composes `pk_scatter_head_wp`, `kyber_half_err_wpE`, and `kyber_neither_v4_err_wpE`
from `BaseKeyOkState` at `+0x684` (`1668`) to `KyberExitA24State` at `+0xa24` (`2596`) with
`pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext)` (keeping the 68- or 54-byte `String`
inside `speAt` as `vecU8`) and the remaining stack spills (`bkPtr`, `bkCap`, `msgPtr`, `ikPtr`) for the `+0xa24` cleanup tail. -/
theorem w5b_kyber_err_wpE {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext)
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen bkCap bkPtr bkLen
      ikCap ikPtr ikLen msgCap msgPtr msgLen : BitVec 64}
    {vb : BitVec 8}
    {regTag regVal opkTag opkVal spkVal kpkTag kpkVal : BitVec 32}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    {bk : List (BitVec 8)} {pk : PublicKey}
    (hkpk : match kpkOpt with | some id => kpkTag = 1#32 ∧ kpkVal = id | none => kpkTag = 0#32)
    (herr : (kpkOpt.isSome != kyberOpt.isSome) = true ∨
      (kpkOpt = none ∧ kyberOpt = none ∧ 0x40 ≤ vb.toNat))
    (hst : BaseKeyOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb bk pk s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1668#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 2596#64) s
      (seg1SpillsAtW sp' bkCap bkPtr bkLen kyberLen ikPtr ikLen msgPtr msgLen
          regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
        memRegion (sp' + 112#64) 32 ∗
        ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
        memRegion (sp' + 345#64) 15 ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        KyberExitA24State img s0 sp' sret len ptr0 ikCap msgCap vb sf ∧
        (Pf ⊢ pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ anyHeap))
      (tryFromQp s0) := by
  rcases hst with ⟨hst_ep, _, _, hpk_bytes,
    hx29, hx28, hx27, hx26, hx25, _, hx23, hx22, hx21, hx20, hx19⟩
  have hlen32 : ((bk.take 33).drop 1).length = 32 := by
    rw [← hpk_bytes]; exact (pkOf bk).bytes.toList_length
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, w9, w13, w15, w23, b31, hpk_of⟩ :=
    exists_pkBytesOf ((bk.take 33).drop 1) hlen32
  have hpre_split :
      seg1SpillsAtW sp' bkCap bkPtr bkLen kyberLen ikPtr ikLen msgPtr msgLen
          regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
        memRegion (sp' + 112#64) 32 ∗
        ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
        memRegion (sp' + 345#64) 15 ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ⊢
      (((sp' + 68#64) ↦₃₂ kpkTag) ∗ memRegion (sp' + 112#64) 32 ∗
        ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
        memRegion (sp' + 345#64) 15) ∗
      ((optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
       (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr)) ∗
       (((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkVal) ∗
        ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
        ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
        ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗ ((sp' + 72#64) ↦₆₄ bkLen))) := by
    dsimp only [seg1SpillsAtW]; apply entails_of_eq; ac_rfl
  refine SepWPp.mono_pre hpre_split ?_
  refine SepWPp.bind_frame_tryFrom
    (pk_scatter_head_wp hpk_of hst_ep hpc hrun hx29 hx28 hx27 hx26 hx25 hx23 hx22 hx21 hx20 hx19) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hst1, hpstate1, _, _, _,
    hx29_1, hx28_1, hx27_1, hx26_1, hx25_1, _, hx23_1, hx22_1, hx21_1, hx20_1, hx19_1, hent1⟩
  refine SepWPp.mono_pre (P' :=
      (optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
       ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ anyHeap))
    (by
      refine Entails.trans (sepConj_mono_left hent1) ?_
      refine Entails.trans (Q :=
        (optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
        (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
         ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr)) ∗
        (((sp' + 68#64) ↦₃₂ kpkTag) ∗ spUnused112 sp' ∗
         ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗ ((sp' + 128#64) ↦₃₂ w9) ∗
         ((sp' + 132#64) ↦₁₆ w13) ∗ sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
         memRegion (sp' + 312#64) 48 ∗
         ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
         ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkVal) ∗
         ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
         ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
         ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗ ((sp' + 72#64) ↦₆₄ bkLen)))
        (by apply entails_of_eq; ac_rfl) ?_
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (entails_anyHeap _)))
        (by apply entails_of_eq; ac_rfl)) ?_
  rcases herr with hhalf | ⟨rfl, rfl, hvb_ge⟩
  · have htag : kpkTag = if kpkOpt.isSome then 1#32 else 0#32 := by
      cases kpkOpt with
      | some _ => exact hkpk.1
      | none => exact hkpk
    refine SepWPp.frame_tryFrom
      (kyber_half_err_wpE himg hA htag hhalf hst1 hpc1 hrun1 hpstate1
        hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1)
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_
    refine Entails.trans
      (Q := ((pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap) ∗
          (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
           ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
           A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))) ∗ anyHeap)
      (by apply entails_of_eq; ac_rfl) ?_
    refine Entails.trans (merge_err_anyHeap _ _) ?_
    apply entails_of_eq; ac_rfl
  · subst hkpk
    refine SepWPp.frame_tryFrom
      (kyber_neither_v4_err_wpE himg hA hvb_ge hst1 hpc1 hrun1 hpstate1
        hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1)
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_
    refine Entails.trans
      (Q := ((pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap) ∗
          (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
           ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
           A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))) ∗ anyHeap)
      (by apply entails_of_eq; ac_rfl) ?_
    refine Entails.trans (merge_err_anyHeap _ _) ?_
    apply entails_of_eq; ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
