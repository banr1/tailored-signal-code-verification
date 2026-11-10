/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.OkBridge
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPost
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes

/-!
# `PreKeySignalMessage::try_from`: `PublicKey` Scatter and Kyber `Ok` Branches (`+0x684..+0x830`)

Defines the scattered-key spill layout `kyberSpillsAtW` (`sp' + 12..144`) and Kyber
error/panic exit states (`+0xa1c`, `+0xa24`, `+0xa74`, `+0xa80`), and proves
`pk_scatter_head_wp` (`+0x684..+0x6c8`), `kyber_both_ok_wp`, and `kyber_neither_v3_ok_wp`
(reaching `+0x830`).
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

private abbrev SepWPp := Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
private abbrev SepWPp.of_sepWP_frozen := @Wire.SepWPp.of_sepWP_frozen
private abbrev SepWPp.of_sepWP_end := @Wire.SepWPp.of_sepWP_end
private abbrev SepWPp.panic := @Wire.SepWPp.panic
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.bind_entails := @Wire.SepWPp.bind_entails
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.call_tryFromX := @Wire.SepWPp.call_tryFrom

open Lean Meta Elab Tactic in
local elab "pksm_fetches " b:term:max H:term:max hfn:ident
    k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat
    (← `(ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))
    "pksm_fetches"
  let offLit := Syntax.mkNumLit (toString off)
  evalTactic (← `(tactic|
    responder_wire_fetches_from $b $H $hfn $offLit $k0 $len))

/-! ## Local BitVec Normalizers -/

private theorem bv_sub_add_lit'X (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem bv_sub_sub_litX (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega
private theorem bv_add_neg_8X (x : BitVec 64) : x + bv% (2 ^ 64 - 8) = x - 8#64 := by bv_omega
private theorem bv_add_neg_16X (x : BitVec 64) : x + bv% (2 ^ 64 - 16) = x - 16#64 := by bv_omega
private theorem bv_add_neg_24X (x : BitVec 64) : x + bv% (2 ^ 64 - 24) = x - 24#64 := by bv_omega
private theorem bv_add_neg_32X (x : BitVec 64) : x + bv% (2 ^ 64 - 32) = x - 32#64 := by bv_omega
private theorem bv_add_neg_40X (x : BitVec 64) : x + bv% (2 ^ 64 - 40) = x - 40#64 := by bv_omega
private theorem bv_add_neg_48X (x : BitVec 64) : x + bv% (2 ^ 64 - 48) = x - 48#64 := by bv_omega
private theorem bv_add_neg_55X (x : BitVec 64) : x + bv% (2 ^ 64 - 55) = x - 55#64 := by bv_omega
private theorem bv_add_neg_56X (x : BitVec 64) : x + bv% (2 ^ 64 - 56) = x - 56#64 := by bv_omega
private theorem bv_add_neg_64X (x : BitVec 64) : x + bv% (2 ^ 64 - 64) = x - 64#64 := by bv_omega
private theorem bv_add_neg_72X (x : BitVec 64) : x + bv% (2 ^ 64 - 72) = x - 72#64 := by bv_omega
private theorem bv_add_neg_80X (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 := by bv_omega
private theorem bv_add_neg_87X (x : BitVec 64) : x + bv% (2 ^ 64 - 87) = x - 87#64 := by bv_omega
private theorem bv_add_neg_88X (x : BitVec 64) : x + bv% (2 ^ 64 - 88) = x - 88#64 := by bv_omega
private theorem bv_add_neg_96X (x : BitVec 64) : x + bv% (2 ^ 64 - 96) = x - 96#64 := by bv_omega
private theorem bv_add_neg_104X (x : BitVec 64) : x + bv% (2 ^ 64 - 104) = x - 104#64 := by bv_omega
private theorem bv_add_neg_112X (x : BitVec 64) : x + bv% (2 ^ 64 - 112) = x - 112#64 := by bv_omega
private theorem bv_add_neg_128X (x : BitVec 64) : x + bv% (2 ^ 64 - 128) = x - 128#64 := by bv_omega
private theorem bv_add_neg_136X (x : BitVec 64) : x + bv% (2 ^ 64 - 136) = x - 136#64 := by bv_omega
private theorem bv_add_neg_152X (x : BitVec 64) : x + bv% (2 ^ 64 - 152) = x - 152#64 := by bv_omega
private theorem bv_add_neg_160X (x : BitVec 64) : x + bv% (2 ^ 64 - 160) = x - 160#64 := by bv_omega
private theorem bv_add_neg_168X (x : BitVec 64) : x + bv% (2 ^ 64 - 168) = x - 168#64 := by bv_omega
private theorem bv_add_neg_176X (x : BitVec 64) : x + bv% (2 ^ 64 - 176) = x - 176#64 := by bv_omega
private theorem bv_add_neg_184X (x : BitVec 64) : x + bv% (2 ^ 64 - 184) = x - 184#64 := by bv_omega
private theorem bv_add_neg_186X (x : BitVec 64) : x + bv% (2 ^ 64 - 186) = x - 186#64 := by bv_omega
private theorem bv_add_neg_191X (x : BitVec 64) : x + bv% (2 ^ 64 - 191) = x - 191#64 := by bv_omega
private theorem bv_add_neg_192X (x : BitVec 64) : x + bv% (2 ^ 64 - 192) = x - 192#64 := by bv_omega
private theorem bv_add_neg_196X (x : BitVec 64) : x + bv% (2 ^ 64 - 196) = x - 196#64 := by bv_omega
private theorem bv_add_neg_200X (x : BitVec 64) : x + bv% (2 ^ 64 - 200) = x - 200#64 := by bv_omega
private theorem bv_add_neg_216X (x : BitVec 64) : x + bv% (2 ^ 64 - 216) = x - 216#64 := by bv_omega
private theorem bv_add_neg_512X (x : BitVec 64) : x + bv% (2 ^ 64 - 512) = x - 512#64 := by bv_omega

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit'X bv_sub_sub_litX BitVec.toNat_zero
  bv_add_neg_8X bv_add_neg_16X bv_add_neg_24X bv_add_neg_32X bv_add_neg_40X
  bv_add_neg_48X bv_add_neg_55X bv_add_neg_56X bv_add_neg_64X bv_add_neg_72X
  bv_add_neg_80X bv_add_neg_87X bv_add_neg_88X bv_add_neg_96X bv_add_neg_104X
  bv_add_neg_112X bv_add_neg_128X bv_add_neg_136X bv_add_neg_152X bv_add_neg_160X
  bv_add_neg_168X bv_add_neg_176X bv_add_neg_184X bv_add_neg_186X bv_add_neg_191X
  bv_add_neg_192X bv_add_neg_196X bv_add_neg_200X bv_add_neg_216X bv_add_neg_512X
  bv_reconstruct_low8 bv_reconstruct_low8_dec bv_zext8_mask truncate16_zext32
  append64_extract_lo append64_extract_hi append32_extract_lo append32_extract_hi
  append32_truncate zeroExtend32_truncate8_eq extractLsb0_8_append56
  zeroExtend32_lsr4_truncate8

theorem L1_PksmWire_W5bKyber : True := trivial

/-! ## 1. Frozen Exit States (`kyberSpillsAtW` and `section W5bExits`) -/

/-- Stack spill layout at `sp' + 12 .. sp' + 144` after `+0x684..+0x6c8` scatters the 32 bytes of `pk`
(`pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 = (bk.take 33).drop 1`).
Slots `sp' + 68` (`kpkTag`) and `sp' + 72` (`bkLen`) from `seg1SpillsAtW` are overwritten by
`b8.zeroExtend 32` and `w15`; all other `seg1SpillsAtW` slots (`sp' + 16..64`, `sp' + 80..104`)
are preserved. -/
def kyberSpillsAtW (sp' bkCap bkPtr kyberLen ikPtr ikLen msgPtr msgLen : BitVec 64)
    (regTag regVal opkTag opkVal spkVal kpkVal : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8)
    (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) : SepProp :=
  ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
  ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
  ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkVal) ∗
  ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
  ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
  ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
  ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
  ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
  ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
  spUnused112 sp' ∗
  ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
  ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
  sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6

section W5bExits

/-- Error-tail entry at `+0xa1c` (`2588`): reached on the `(none, some kyberCt)` error path
when `0 < kyberCap.toNat < 2 ^ 63` after `sret` has been populated with `pksmErrE`.
`x0 = kyberPtr` and `x1 = kyberCap` are set for `mov w2, #1; bl __rust_dealloc` at `+0xa1c..+0xa20`,
which then falls through to `+0xa24` (`2596`). -/
def KyberExitA1cState (img : Obj.Image) (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64) (vb : BitVec 8)
    (sf : State) : Prop :=
  PostEpilogueState img s0 sp' sf ∧
  0 < kyberCap.toNat ∧ kyberCap.toNat < 2 ^ 63 ∧ kyberPtr ≠ 0#64 ∧
  sf.readReg64 .x0 = kyberPtr ∧ sf.readReg64 .x1 = kyberCap ∧
  sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x26 = msgCap ∧
  sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = vb.zeroExtend 64 ∧
  sf.readReg64 .x21 = ptr0 ∧ sf.readReg64 .x20 = len ∧ sf.readReg64 .x19 = sret

/-- Error-tail entry at `+0xa24` (`2596`): reached on the `(some kpkId, none)` error path,
the `(none, some [])` error path with `kyberCap = 0#64`, or the `(none, none)` + `vb.toNat ≥ 0x40`
error path, after `sret` has been populated with `pksmErrE`. Frees `msgVec`, `ikVec`, `bkVec`. -/
def KyberExitA24State (img : Obj.Image) (s0 : State)
    (sp' sret len ptr0 ikCap msgCap : BitVec 64) (vb : BitVec 8)
    (sf : State) : Prop :=
  PostEpilogueState img s0 sp' sf ∧
  sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x26 = msgCap ∧
  sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = vb.zeroExtend 64 ∧
  sf.readReg64 .x21 = ptr0 ∧ sf.readReg64 .x20 = len ∧ sf.readReg64 .x19 = sret

/-- Allocation-failure panic entry at `+0xa74` (`2676`): reached when `__rust_alloc(68, 1)` at `+0x72c`
returns `x0 = 0#64` (`allocFailedIn s0 sf`). Executes `mov w0, #1; mov w1, #68; bl handle_error`. -/
def KyberExitA74State (img : Obj.Image) (s0 : State) (sp' : BitVec 64) (sf : State) : Prop :=
  sf.sp = sp' ∧ sf.spAligned = true ∧ img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
  allocFailedIn s0 sf ∧ s0.trace <+: sf.trace

/-- Allocation-failure panic entry at `+0xa80` (`2688`): reached when `__rust_alloc(54, 1)` at `+0x9a4`
returns `x0 = 0#64` (`allocFailedIn s0 sf`). Executes `mov w0, #1; mov w1, #54; bl handle_error`. -/
def KyberExitA80State (img : Obj.Image) (s0 : State) (sp' : BitVec 64) (sf : State) : Prop :=
  sf.sp = sp' ∧ sf.spAligned = true ∧ img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
  allocFailedIn s0 sf ∧ s0.trace <+: sf.trace

end W5bExits

/-! ## 2. ``pk_scatter_head_wp``, ``kyber_both_ok_wp``, ``kyber_neither_v3_ok_wp`` -/

theorem deser_ok_entails_memRegion48 (sp' : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8)
    (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    ((sp' + 312#64) ↦₈ 0#8) ∗ sevenBytesHeadAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗
      pkRestAt (sp' + 313#64) b7 b8 w9 w13 w15 w23 b31 ∗ memRegion (sp' + 345#64) 15 ⊢
      memRegion (sp' + 312#64) 48 := by
  have h1 : ((sp' + 312#64) ↦₈ 0#8) ∗ sevenBytesHeadAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗
      pkRestAt (sp' + 313#64) b7 b8 w9 w13 w15 w23 b31 ∗ memRegion (sp' + 345#64) 15 ⊢
      ((sp' + 312#64) ↦₆₄ (b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 ++ 0#8)) ∗
        memRegion (sp' + 320#64) 40 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      deser_ok_entails_spe_region (sp' + 312#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31
  refine Entails.trans h1 ?_
  rw [Prost.memRegion_split (sp' + 312#64) 8 40 (by decide),
    show sp' + 312#64 + BitVec.ofNat 64 8 = sp' + 320#64 by bv_omega]
  exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)

theorem memRegion48_312_split24 (sp' : BitVec 64) :
    memRegion (sp' + 312#64) 48 =
      (∃∗ w312 : BitVec 64, (sp' + 312#64) ↦₆₄ w312) ∗
      (∃∗ w320 : BitVec 64, (sp' + 320#64) ↦₆₄ w320) ∗
      (∃∗ w328 : BitVec 64, (sp' + 328#64) ↦₆₄ w328) ∗
      memRegion (sp' + 336#64) 24 := by
  rw [Prost.memRegion_split (sp' + 312#64) 8 40 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 8#64) 8 32 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 8#64 + 8#64) 8 24 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    ProofLib.memRegion_eight (sp' + 312#64),
    ProofLib.memRegion_eight (sp' + 320#64),
    ProofLib.memRegion_eight (sp' + 328#64)]

/-- (``+0x684 .. +0x6c8`, `+1668 .. +1736``):
Loads the 32-byte `PublicKey` from `sp' + 313..345`, scatters `w23, b31, w9, w13, b0..b6`
into `sp' + 112..144`, keeps `b8`, `w15`, `b7` in `x8`, `x11`, `x12`, sets `x24 = sp' + 312#64`,
and sets `pstate = subsPState32 kpkTag 1#32` at `+0x6c8` (`1736`, `b.ne +0x718`). -/
theorem pk_scatter_head_wp {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {kpkTag : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    {pkBytes : List (BitVec 8)}
    (hpk : pkBytes = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1668#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberPtr) (hx23 : s.readReg64 .x23 = ikCap)
    (hx22 : s.readReg64 .x22 = vb.zeroExtend 64) (hx21 : s.readReg64 .x21 = ptr0)
    (hx20 : s.readReg64 .x20 = len) (hx19 : s.readReg64 .x19 = sret) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1736#64) s
      (((sp' + 68#64) ↦₃₂ kpkTag) ∗ memRegion (sp' + 112#64) 32 ∗
        ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ pkBytes) ∗ memRegion (sp' + 345#64) 15)
      (fun sf Pf =>
        PostEpilogueState img s0 sp' sf ∧
        sf.pstate = subsPState32 kpkTag 1#32 ∧
        sf.readReg64 .x8 = (b8.zeroExtend 32).zeroExtend 64 ∧
        sf.readReg64 .x11 = w15 ∧
        sf.readReg64 .x12 = (b7.zeroExtend 32).zeroExtend 64 ∧
        sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 = kyberCap ∧
        sf.readReg64 .x27 = 0x8000000000000002#64 ∧ sf.readReg64 .x26 = msgCap ∧
        sf.readReg64 .x25 = kyberPtr ∧ sf.readReg64 .x24 = sp' + 312#64 ∧
        sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = vb.zeroExtend 64 ∧
        sf.readReg64 .x21 = ptr0 ∧ sf.readReg64 .x20 = len ∧ sf.readReg64 .x19 = sret ∧
        (Pf ⊢ ((sp' + 68#64) ↦₃₂ kpkTag) ∗ spUnused112 sp' ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          memRegion (sp' + 312#64) 48))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  let H := Rust.withPanics ext
  have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
      num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  pksm_fetches img.base H hfn 1668 68; clear hfn
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  rw [hpk, ← pkLayoutAt_eq_pointsToBytes]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (memRegion32_112_unpack sp'))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w112 => SepWPp.exists_pre fun b120 =>
    SepWPp.exists_pre fun w128 => SepWPp.exists_pre fun w132 =>
    SepWPp.exists_pre fun c0 => SepWPp.exists_pre fun c1 =>
    SepWPp.exists_pre fun c2 => SepWPp.exists_pre fun c3 =>
    SepWPp.exists_pre fun c4 => SepWPp.exists_pre fun c5 =>
    SepWPp.exists_pre fun c6 => ?_
  dsimp only [pkLayoutAt]
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 1680#64) ?_
  conv => arg 4; dsimp only [sevenBytesHeadAt, pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  have h313_tail := sevenBytesHeadAt_eq_tailAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6
  refine SepWPp.mono_pre (P' :=
      ((sp' + 68#64) ↦₃₂ kpkTag) ∗ spUnused112 sp' ∗
      ((sp' + 112#64) ↦₆₄ w112) ∗ ((sp' + 120#64) ↦₈ b120) ∗
      ((sp' + 128#64) ↦₃₂ w128) ∗ ((sp' + 132#64) ↦₁₆ w132) ∗
      sevenBytesHeadAt (sp' + 136#64) c0 c1 c2 c3 c4 c5 c6 ∗
      ((sp' + 312#64) ↦₈ 0#8) ∗
      sevenBytesTailAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗
      pkRestAt (sp' + 313#64) b7 b8 w9 w13 w15 w23 b31 ∗
      memRegion (sp' + 345#64) 15)
    (by
      rw [← h313_tail]
      dsimp only [sevenBytesHeadAt, pkRestAt]
      apply entails_of_eq; simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl) ?_
  refine SepWPp.of_sepWP_frozen hF1 hsym1 (mid := entry + 1704#64) ?_
  conv => arg 4; dsimp only [sevenBytesTailAt, pkRestAt, sevenBytesHeadAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF2 hsym2
  have h136_tail := sevenBytesHeadAt_eq_tailAt (sp' + 136#64) b0 b1 b2 b3 c4 c5 c6
  refine SepWPp.mono_pre (P' :=
      ((sp' + 68#64) ↦₃₂ kpkTag) ∗ spUnused112 sp' ∗
      ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b120) ∗
      ((sp' + 128#64) ↦₃₂ w128) ∗ ((sp' + 132#64) ↦₁₆ w132) ∗
      sevenBytesTailAt (sp' + 136#64) b0 b1 b2 b3 c4 c5 c6 ∗
      ((sp' + 312#64) ↦₈ 0#8) ∗
      sevenBytesHeadAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗
      pkRestAt (sp' + 313#64) b7 b8 w9 w13 w15 w23 b31 ∗
      memRegion (sp' + 345#64) 15)
    (by
      rw [sevenBytesHeadAt_eq_tailAt (sp' + 313#64), ← h136_tail]
      dsimp only [sevenBytesTailAt, pkRestAt, sevenBytesHeadAt]
      apply entails_of_eq; simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl) ?_
  refine SepWPp.of_sepWP_end hF2 hsym2 ?_
  conv => arg 4; dsimp only [sevenBytesTailAt, pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF3 hsym3 => ?_
  refine ⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hF3, hsym3,
      by simp [htr, arm64_norm]⟩,
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
    by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [arm64_norm],
    by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
    by simp [hx20, arm64_norm], by simp [hx19, arm64_norm], ?_⟩
  have h136_head := sevenBytesHeadAt_eq_tailAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6
  have hcollapse := deser_ok_entails_memRegion48 sp' b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31
  rw [h136_head]
  dsimp only [sevenBytesTailAt]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hcollapse)))))))
  dsimp only [sevenBytesHeadAt, pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply entails_of_eq; ac_rfl

/-- (``+0x6c8 .. +0x6fc → +0x830`, `1736 .. 1788 → 2096``):
When `kpkTag = 1#32` (`m.kyberPreKeyId = some kpkId`) and `m.kyberCiphertext = some kyberCt`
(`kyberCap.toNat < 2 ^ 63`), stores `b8`, `b7`, `w15` to stack slots `sp' + 68`, `sp' + 12`,
`sp' + 72`, converts `kyberCt` via `into_boxed_slice`, and branches to `+0x830` (`2096`). -/
theorem kyber_both_ok_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hIntoBox : IntoBoxedSliceOkX img A ext)
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr bkLen ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {b7 b8 : BitVec 8} {w15 : BitVec 64}
    {kyberCt : List (BitVec 8)}
    {bk : List (BitVec 8)} {pk : PublicKey}
    (hbk_ok : ecKeyParses bk = true) (hpk_eq : pkOf bk = pk)
    (hpk_bytes : (pkOf bk).bytes.toList = (bk.take 33).drop 1)
    (hky_lt : kyberCap.toNat < 2 ^ 63)
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1736#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState32 1#32 1#32)
    (hx8 : s.readReg64 .x8 = (b8.zeroExtend 32).zeroExtend 64)
    (hx11 : s.readReg64 .x11 = w15)
    (hx12 : s.readReg64 .x12 = (b7.zeroExtend 32).zeroExtend 64)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberPtr) (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx22 : s.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = ptr0) (hx20 : s.readReg64 .x20 = len)
    (hx19 : s.readReg64 .x19 = sret) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 2096#64) s
      (memRegion (sp' + 12#64) 4 ∗
        ((sp' + 40#64) ↦₆₄ BitVec.ofNat 64 kyberCt.length) ∗
        ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' + 72#64) ↦₆₄ bkLen) ∗
        memRegion (sp' + 312#64) 48 ∗
        Wire.vecU8Buf A kyberCap kyberPtr kyberCt ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        ∃ kyberBoxPtr : BitVec 64,
          KyberOkState img s0 sp' sret len ptr0 kyberBoxPtr (BitVec.ofNat 64 kyberCt.length)
            ikCap msgCap vb bk pk sf ∧
          kyberBoxPtr ≠ 0#64 ∧
          (Pf ⊢ ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
            ((sp' + 40#64) ↦₆₄ BitVec.ofNat 64 kyberCt.length) ∗
            ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
            memRegion (sp' + 312#64) 48 ∗
            boxU8Buf A kyberBoxPtr kyberCt ∗
            A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcallBox := intoBoxedSlice_ok_at_prekeyX hIntoBox; clear hIntoBox
  have hky_eq := cap_add1_eq_of_lt hky_lt
  let H := Rust.withPanics ext
  have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
      num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  pksm_fetches img.base H hfn 1736 56; clear hfn
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcallBox hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hstackBox := stackAt_sub_split sp' LibsignalTripleRatchet.intoBoxedSliceStackX
    (Prost.skipFieldStackX 100) (by decide)
  conv => arg 4; rw [memRegion48_312_split24 sp']
  refine SepWPp.mono_pre (sepConj_mono_left (memRegion_four_entails (sp' + 12#64))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w328 => SepWPp.exists_pre fun w320 =>
    SepWPp.exists_pre fun w312 => SepWPp.exists_pre fun w12 => ?_
  refine SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% ((2 ^ 64 + ls_off% intoBoxedSliceName - ls_off% preKeyTryFromName) % 2 ^ 64)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  have hvec_ky : vecU8At A (sp' + 312#64) kyberCap kyberPtr kyberCt =
      ((sp' + 312#64) ↦₆₄ kyberCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
      ((sp' + 328#64) ↦₆₄ BitVec.ofNat 64 kyberCt.length) ∗
      Wire.vecU8Buf A kyberCap kyberPtr kyberCt := by
    rw [vecU8At_eq_header_buf]
    dsimp only [vecHeader]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.call_tryFromX (⟨sp' + 312#64, kyberCap, kyberPtr, kyberCt⟩ : VecArg) hcallBox
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by tryFromPost_sp_align hsp) hF1 hsym1
    (ret_pc := entry + 1780#64) (by simp [arm64_norm])
    (by simp [htr, arm64_norm])
    (T := vecU8At A (sp' + 312#64) kyberCap kyberPtr kyberCt ∗ A.pool ∗
      stackAt s.sp LibsignalTripleRatchet.intoBoxedSliceStackX)
    (φ := sp' + 312#64 = sp' + 312#64)
    (by simp [LibsignalTripleRatchet.intoBoxedSliceSpecX, VecArg.at, hsp_eq, arm64_norm])
    rfl
    (by rw [hvec_ky, hstackBox, hsp_eq]; sep_focus)
    ?_
  clear hcallBox
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [LibsignalTripleRatchet.intoBoxedSliceSpecX]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun ⟨hx1_2, htr2⟩ => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, _, hx26_2, hx27_2, _, hx29_2, _⟩
  have hbox_nz : boxU8Buf A (s2.readReg64 .x0) kyberCt ⊢
      ⌜s2.readReg64 .x0 ≠ 0#64⌝ ∗ boxU8Buf A (s2.readReg64 .x0) kyberCt := by
    refine Entails.trans (by dsimp only [boxU8Buf]; exact Entails.refl _) ?_
    refine Entails.pure_left fun ⟨hptr, hlen⟩ => ?_
    have hptr' : s2.readReg64 .x0 ≠ 0#64 := hptr
    rw [pure_true_emp hptr', emp_sepConj]
    dsimp only [boxU8Buf]
    rw [pure_true_emp ⟨hptr, hlen⟩, emp_sepConj]
    exact Entails.refl _
  have h48 : vecHeader (sp' + 312#64) kyberCap kyberPtr (BitVec.ofNat 64 kyberCt.length) ∗
      memRegion (sp' + 336#64) 24 ⊢ memRegion (sp' + 312#64) 48 := by
    rw [show (48 : Nat) = 24 + 24 by decide, Prost.memRegion_split (sp' + 312#64) 24 24 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_left (vecHeader_entails_memRegion24 (sp' + 312#64) kyberCap kyberPtr _)
  refine SepWPp.mono_pre
    (P' := ⌜s2.readReg64 .x0 ≠ 0#64⌝ ∗
      (((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
        ((sp' + 40#64) ↦₆₄ BitVec.ofNat 64 kyberCt.length) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
        memRegion (sp' + 312#64) 48 ∗
        boxU8Buf A (s2.readReg64 .x0) kyberCt ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
    (by
      refine Entails.trans
        (Q := boxU8Buf A (s2.readReg64 .x0) kyberCt ∗
          ((vecHeader (sp' + 312#64) kyberCap kyberPtr (BitVec.ofNat 64 kyberCt.length) ∗
            memRegion (sp' + 336#64) 24) ∗
            ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
            ((sp' + 40#64) ↦₆₄ BitVec.ofNat 64 kyberCt.length) ∗
            ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
            A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
        (by simp only [hstackBox, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl) ?_
      refine Entails.trans (sepConj_mono hbox_nz (sepConj_mono_left h48)) ?_
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.pure_pre fun hptr_nz => ?_
  refine SepWPp.of_sepWP_end hF2 hsym2 ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hF3 hsym3 => ?_
  refine ⟨s2.readReg64 .x0,
    ⟨⟨by tryFromPost_sp [hsp2, hsp_eq], by tryFromPost_sp_align hsp2_align, hF3, hsym3,
        by simp [htr2, htr, arm64_norm]⟩,
      hbk_ok, hpk_eq, hpk_bytes,
      by simp [hx29_2, hx29, arm64_norm], by simp [arm64_norm],
      by simp [hx27_2, hx27, arm64_norm], by simp [hx26_2, hx26, arm64_norm],
      by simp [arm64_norm], by simp [hx24_2, hx24, arm64_norm],
      by simp [hx23_2, hx23, arm64_norm], by simp [hx22_2, hx22, arm64_norm],
      by simp [hx21_2, hx21, arm64_norm], by simp [hx20_2, hx20, arm64_norm],
      by simp [hx19_2, hx19, arm64_norm]⟩,
    hptr_nz, by apply entails_of_eq; ac_rfl⟩

private theorem ule_64_vb_eq_false {vb : BitVec 8} (hvb_lt : vb.toNat < 0x40) :
    (64#64).ule (vb.zeroExtend 64) = false := by
  rw [BitVec.ule_eq_decide]
  exact decide_eq_false (by rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth]; omega)

/-- (``+0x6c8 → +0x718 .. +0x71c → +0x818 .. +0x82c → +0x830`, `1736 → 1816 → 2072 → 2096``):
When `kpkTag = 0#32` (`m.kyberPreKeyId = none`), `kyberCap = noneCap` (`m.kyberCiphertext = none`),
and `vb.toNat < 0x40`, branches `1736 → 1816 → 2072`, checks `cmp w22, #64`, sets `x28 = 0#64`,
stores `b7`, `b8`, `w15` to stack slots `sp' + 12`, `sp' + 68`, `sp' + 72`, and falls through
to `+0x830` (`2096`). -/
theorem kyber_neither_v3_ok_wp {img : Obj.Image}
    {ext : String → Option (State → State)}
    {s0 s : State}
    {sp' sret len ptr0 kyberPtr bkLen ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {b7 b8 : BitVec 8} {w15 : BitVec 64}
    {bk : List (BitVec 8)} {pk : PublicKey}
    (hbk_ok : ecKeyParses bk = true) (hpk_eq : pkOf bk = pk)
    (hpk_bytes : (pkOf bk).bytes.toList = (bk.take 33).drop 1)
    (hvb_lt : vb.toNat < 0x40)
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1736#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState32 0#32 1#32)
    (hx8 : s.readReg64 .x8 = (b8.zeroExtend 32).zeroExtend 64)
    (hx11 : s.readReg64 .x11 = w15)
    (hx12 : s.readReg64 .x12 = (b7.zeroExtend 32).zeroExtend 64)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = noneCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberPtr) (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx22 : s.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = ptr0) (hx20 : s.readReg64 .x20 = len)
    (hx19 : s.readReg64 .x19 = sret) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 2096#64) s
      (memRegion (sp' + 12#64) 4 ∗
        ((sp' + 68#64) ↦₃₂ 0#32) ∗ ((sp' + 72#64) ↦₆₄ bkLen))
      (fun sf Pf =>
        KyberOkState img s0 sp' sret len ptr0 0#64 kyberPtr ikCap msgCap vb bk pk sf ∧
        (Pf ⊢ ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
          ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcs_vb := ule_64_vb_eq_false hvb_lt
  let H := Rust.withPanics ext
  have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
      num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  pksm_fetches img.base H hfn 1736 4
  pksm_fetches img.base H hfn 1816 8
  pksm_fetches img.base H hfn 2072 24; clear hfn
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.mono_pre (sepConj_mono_left (memRegion_four_entails (sp' + 12#64))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun w12 => ?_
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2080#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm])
    (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.of_sepWP_end hF1 hsym1 ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF2 hsym2 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hF2, hsym2,
        by simp [htr, arm64_norm]⟩,
      hbk_ok, hpk_eq, hpk_bytes,
      by simp [hx29, arm64_norm], by simp [arm64_norm],
      by simp [hx27, arm64_norm], by simp [hx26, arm64_norm],
      by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
      by simp [hx23, arm64_norm], by simp [hx22, arm64_norm],
      by simp [hx21, arm64_norm], by simp [hx20, arm64_norm],
      by simp [hx19, arm64_norm]⟩,
    by apply entails_of_eq; ac_rfl⟩

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
