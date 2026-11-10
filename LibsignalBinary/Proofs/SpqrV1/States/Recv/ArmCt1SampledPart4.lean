/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Sampled` Arm, Part 4 (`outMsg = none` Paths)

Verifies the two `outMsg = none` paths from `0x58ae4` (`+13968`):
- Path 4a (`ack = false`): `.stillReceivingStillSending` → `States.ct1Sampled`.
- Path 4b (`ack = true`): `.stillReceiving` → `States.ct1Acknowledged`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv")
  (ls_stub% "memcpy")

@[reducible] private def ct1s4MemcpySpec (Inv : State → Prop) (calleeStack : Nat) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun x s => ⌜Inv s⌝ ∗ sessionMemcpyRegionSpec.pre x s ∗ stackAt s.sp calleeStack
  post := fun x s0 sf => sessionMemcpyRegionSpec.post x s0 sf ∗ stackAt s0.sp calleeStack

private theorem ct1s4_memcpy_ok_zero {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      (ct1s4MemcpySpec (fun _ => True) 0) :=
  subroutine_ok_mono
    (subroutine_ok_withStack_of_subroutine_ok (memcpy_region_ok_at_statesRecv hmemcpy) 0)
    (fun _ _ _ hpre => by
      dsimp only [ct1s4MemcpySpec, withStack] at hpre ⊢
      rwa [pure_true_sepConj] at hpre)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h)

private theorem ct1s4_memcpy_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      (ct1s4MemcpySpec (ImgCallInv img) extHookStack) :=
  subroutine_ok_mono
    (hA.session_memcpy_region_ok_at statesRecvName
      (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")))
    (fun _ _ _ h => h)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h)

private theorem ct1s4_stackAt_zero_sep (fsp : BitVec 64) (Rest : SepProp) :
    stackAt fsp 0 ∗ Rest = Rest := by
  simp only [stackAt, memRegion_zero, emp_sepConj]

private theorem ct1s4_stackAt_statesRecvCallee_sep (fsp : BitVec 64) (Rest : SepProp) :
    stackAt fsp statesRecvCalleeStackX ∗ Rest =
      stackAt fsp extHookStack ∗ (memRegion (fsp - 19552#64) 3168 ∗ Rest) := by
  rw [stackAt_split_bottom_of_eq fsp statesRecvCalleeStackX extHookStack 3168]
  ac_rfl

private theorem ct1s4_seq_inv {prog : Program} {Inv : State → Prop}
    (hstep : ∀ {s s' : State}, Inv s → Steps prog s s' → Inv s')
    {mid target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hinv : Inv s)
    (h : SepWP prog mid s P (fun sm Pm => Inv sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold SepWP reaches_pc
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hf⟩⟩
  · rcases (hnext (hstep hinv hsteps)).elim hmm (hsteps.codeLoaded hL) with
      ⟨sf, hsteps', ⟨hpc, hrun, Pf, hmf, hpost⟩ | ⟨hoom, hf⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpc, hrun, Pf, hmf, hpost⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr ⟨hoom, hf⟩⟩
  · exact ⟨sm, hsteps, Or.inr ⟨hoom, hf⟩⟩

private theorem ct1s4_seq_inv_lr {prog : Program} {Inv : State → Prop}
    (hstep : ∀ {s s' : State}, Inv s → Steps prog s s' → Inv s')
    {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hinv : Inv s)
    (h : SepWP prog (s.readReg64 .x30) s P (fun sm Pm => Inv sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post :=
  ct1s4_seq_inv hstep (mid := s.readReg64 .x30) hinv h

private theorem ct1s4_imgCallInv_steps {img : Obj.Image} {prog : Program} {s s' : State}
    (h : ImgCallInv img s) (hs : Steps prog s s') : ImgCallInv img s' :=
  ⟨hs.frozenLoaded h.1, hs.symtab_eq.trans h.2⟩

local macro "ct1s4_steps_to_memcpy " hstep:term:max entry:term:max hinv:ident hcall:ident : tactic =>
  `(tactic| (
    apply ct1s4_seq_inv $hstep
      (mid := $entry + bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")) $hinv
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm]) fun $hcall => ?_))

local macro "ct1s4_call_memcpy " hstep:term:max hmemcpy:ident hinv:ident hnext_inv:ident g:term : tactic =>
  `(tactic| (
    apply ct1s4_seq_inv_lr $hstep $hinv
    wp_call $hmemcpy (x := $g)
    all_goals try exact $hinv
    refine SepWP.done (by simp only [arm64_norm]; assumption) (by assumption) fun $hnext_inv => ?_))

/-! ## 1. `mid376At` and `Split400` Byte/Word Decompositions -/

def mid376Bytes (w512 w520 w528 : BitVec 64) (bs352 : List (BitVec 8)) : List (BitVec 8) :=
  unpack64 w512 ++ (unpack64 w520 ++ (unpack64 w528 ++ bs352))

def mid376At (a : BitVec 64) (w512 w520 w528 : BitVec 64) (bs352 : List (BitVec 8)) : SepProp :=
  (a ↦₆₄ w512) ∗ ((a + 8#64) ↦₆₄ w520) ∗ ((a + 16#64) ↦₆₄ w528) ∗ ((a + 24#64) ↦ₛ bs352)

theorem mid376Bytes_length (w512 w520 w528 : BitVec 64) {bs352 : List (BitVec 8)}
    (h : bs352.length = 352) :
    (mid376Bytes w512 w520 w528 bs352).length = 376 := by
  dsimp only [mid376Bytes]
  simp only [List.length_append, unpack64_length, h]

theorem mid376At_eq_pointsToBytes (a : BitVec 64) (w512 w520 w528 : BitVec 64)
    (bs352 : List (BitVec 8)) :
    mid376At a w512 w520 w528 bs352 = (a ↦ₛ mid376Bytes w512 w520 w528 bs352) := by
  dsimp only [mid376At, mid376Bytes]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [unpack64_length, ← pointsTo64_eq_pointsToBytes]
  have ha1 : a + BitVec.ofNat 64 8 = a + 8#64 := rfl
  have ha2 : a + 8#64 + BitVec.ofNat 64 8 = a + 16#64 := by bv_omega
  have ha3 : a + 16#64 + BitVec.ofNat 64 8 = a + 24#64 := by bv_omega
  rw [ha1, ha2, ha3]

structure Split400 where
  w0 : BitVec 64
  mid352 : List (BitVec 8)
  tail : Words5

def Split400.tailBytes (d : Split400) : List (BitVec 8) :=
  d.mid352 ++ wordsBytes d.tail.toList

def Split400.toBytes (d : Split400) : List (BitVec 8) :=
  unpack64 d.w0 ++ d.tailBytes

def split400At (a : BitVec 64) (d : Split400) : SepProp :=
  (a ↦₆₄ d.w0) ∗ ((a + 8#64) ↦ₛ d.mid352) ∗ wordsAt (a + 360#64) d.tail.toList

theorem Split400.tailBytes_length (d : Split400) (hmid : d.mid352.length = 352) :
    d.tailBytes.length = 392 := by
  dsimp only [Split400.tailBytes]
  simp only [List.length_append, hmid, length_wordsBytes, Words5.toList_length]

theorem Split400.toBytes_length (d : Split400) (hmid : d.mid352.length = 352) :
    d.toBytes.length = 400 := by
  dsimp only [Split400.toBytes]
  rw [List.length_append, unpack64_length, d.tailBytes_length hmid]

theorem split400At_eq_w0_tailBytes (a : BitVec 64) (d : Split400) (hmid : d.mid352.length = 352) :
    split400At a d = ((a ↦₆₄ d.w0) ∗ ((a + 8#64) ↦ₛ d.tailBytes)) := by
  dsimp only [split400At, Split400.tailBytes]
  rw [pointsToBytes_append (a + 8#64) d.mid352 (wordsBytes d.tail.toList),
      hmid, ← wordsAt_eq_pointsToBytes]
  have ha : (a + 8#64) + BitVec.ofNat 64 352 = a + 360#64 := by bv_omega
  rw [ha]

theorem split400At_eq_pointsToBytes (a : BitVec 64) (d : Split400) (hmid : d.mid352.length = 352) :
    split400At a d = (a ↦ₛ d.toBytes) := by
  rw [split400At_eq_w0_tailBytes a d hmid]
  dsimp only [Split400.toBytes]
  rw [pointsToBytes_append a (unpack64 d.w0) d.tailBytes,
      unpack64_length, ← pointsTo64_eq_pointsToBytes a d.w0]

theorem exists_split400_of_length_400 {bs : List (BitVec 8)} (h : bs.length = 400) :
    ∃ d : Split400, d.mid352.length = 352 ∧ bs = d.toBytes := by
  have h0 : (bs.take 8).length = 8 * 1 := by simp [List.length_take]; omega
  have hmid : ((bs.drop 8).take 352).length = 352 := by
    simp [List.length_take, List.length_drop]; omega
  have htail : ((bs.drop 8).drop 352).length = 40 := by
    simp [List.length_drop]; omega
  obtain ⟨ws0, hlen0, hws0⟩ := exists_words_of_length 1 (bs.take 8) h0
  rcases ws0 with _ | ⟨w0, _ | _⟩ <;> try simp at hlen0
  obtain ⟨tail, htail_eq⟩ := exists_words5_of_length_40 htail
  refine ⟨⟨w0, (bs.drop 8).take 352, tail⟩, hmid, ?_⟩
  dsimp only [Split400.toBytes, Split400.tailBytes]
  have hw0 : bs.take 8 = unpack64 w0 := by
    simpa [wordsBytes, List.append_nil] using hws0
  rw [← hw0, ← htail_eq]
  simp only [List.take_append_drop]

theorem split400At_entails_memRegion (a : BitVec 64) (d : Split400) (hmid : d.mid352.length = 352) :
    split400At a d ⊢ memRegion a 400 := by
  rw [split400At_eq_pointsToBytes a d hmid]
  have h := ProofLib.pointsToBytes_entails_memRegion a d.toBytes
  rwa [d.toBytes_length hmid] at h

theorem Relocatable.extract_split400 {F : BitVec 64 → SepProp} (hrel : Relocatable 400 F) (a : BitVec 64) :
    F a ⊢ ∃∗ d : Split400, ⌜d.mid352.length = 352⌝ ∗ split400At a d ∗ relocatedHeap F d.toBytes := by
  refine Entails.trans (hrel a) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  obtain ⟨d, hmid, rfl⟩ := exists_split400_of_length_400 hlen
  refine Entails.sepExists_right d ?_
  refine Entails.pure_right hmid ?_
  rw [split400At_eq_pointsToBytes a d hmid]
  exact Entails.refl _

def copyFullScratch (sc : CopyScratchStack) (d : Split928) : CopyScratchStack where
  c0 := { sc.c0 with
    w1 := d.c3.w5
    w2 := d.c2.w4
    w3 := d.c2.w0
    w4 := d.c1.w14
    w5 := d.c2.w1
    w6 := d.c2.w10
    w7 := d.c2.w9
    w8 := d.c2.w7
    w9 := d.c2.w3
    w10 := d.c2.w2
    w11 := d.c3.w10
    w12 := d.c3.w8
    w13 := d.c2.w8
    w14 := d.c2.w5
    w15 := d.c3.w6
  }
  w80 := d.c2.w6
  w88 := d.c0.w1
  w90 := d.c3.w12
  w98 := d.c1.w0
  wa0 := d.c1.w1
  wa8 := d.c3.w0
  wb0 := d.c3.w4
  wb8 := d.c3.w2
  wc0 := d.c2.w12
  wc8 := d.c2.w14
  wd0 := d.c0.w2
  wd8 := d.c3.w1
  wf0 := d.c2.w11

def mkSplit928From528And400 (c0 c1 c2 c3 : Words16) (w512 w520 : BitVec 64) (d400 : Split400) : Split928 where
  c0 := c0
  c1 := c1
  c2 := c2
  c3 := c3
  mid := mid376Bytes w512 w520 d400.w0 d400.mid352
  tail := d400.tail

theorem mkSplit928From528And400_mid_length (c0 c1 c2 c3 : Words16) (w512 w520 : BitVec 64)
    {d400 : Split400} (hmid : d400.mid352.length = 352) :
    (mkSplit928From528And400 c0 c1 c2 c3 w512 w520 d400).mid.length = 376 :=
  mid376Bytes_length w512 w520 d400.w0 hmid

/-! ## 2. Branch on `w22` (`ack`) at `0x58ae4` (`+13968`) -/

/-- When `x22 = 0#64` (`ack = false`), `tbz w22, #0, 0x5938c` at `+13968` branches to `+16184`. -/
theorem ct1Sampled_none_branch_no_ack
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s_in : State) (Rest : SepProp)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 13968#64)
    (hrun : s_in.status = .Running)
    (hx22 : s_in.readReg64 .x22 = 0#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 16184#64) s_in
      Rest
      (fun sf Pf =>
        (Pf ⊢ Rest) ∧
        sf = s_in.setPC ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 16184#64)) := by
  states_recv_fetches_range b (Rust.withPanics ext) 13968 4
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- When `x22 = 1#64` (`ack = true`), `tbz w22, #0, 0x5938c` at `+13968` falls through to `+13972`. -/
theorem ct1Sampled_none_branch_ack
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s_in : State) (Rest : SepProp)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 13968#64)
    (hrun : s_in.status = .Running)
    (hx22 : s_in.readReg64 .x22 = 1#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 13972#64) s_in
      Rest
      (fun sf Pf =>
        (Pf ⊢ Rest) ∧
        sf = s_in.setPC ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 13972#64)) := by
  states_recv_fetches_range b (Rust.withPanics ext) 13968 4
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-! ## 3. Path 4a (`outMsg = none, ack = false`): `+16184 -> +16596 -> +18996` -/

set_option maxHeartbeats 1600000 in
private theorem ct1Sampled_copy_none_no_ack_part1_gen
    {b : BitVec 64} {ext : String → Option (State → State)} {Inv : State → Prop} {calleeStack : Nat}
    (hstep_inv : ∀ {s s' : State}, Inv s → Steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) s s' → Inv s')
    (hmemcpy_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      (ct1s4MemcpySpec Inv calleeStack))
    (s_in : State) (fsp stA : BitVec 64) (c0 c1 c2 c3 : Words16) (w512 w520 : BitVec 64) (d400 : Split400)
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (v976 v984 v992 vc90 vc98 v4096 v4104 v4112 : BitVec 64) (Rest : SepProp)
    (hmid352 : d400.mid352.length = 352) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 16184#64)
    (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64) (hinv : Inv s_in) :
    let d := mkSplit928From528And400 c0 c1 c2 c3 w512 w520 d400
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 16596#64) s_in
      (wordsAt stA c0.toList ∗ wordsAt (stA + 128#64) c1.toList ∗
        wordsAt (stA + 256#64) c2.toList ∗ wordsAt (stA + 384#64) c3.toList ∗
        ((stA + 512#64) ↦₆₄ w512) ∗ ((stA + 520#64) ↦₆₄ w520) ∗ ((fsp + 232#64) ↦₆₄ stA) ∗
        split400At (fsp + 2752#64) d400 ∗ memRegion (fsp + 1872#64) 400 ∗
        copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 976#64) ↦₆₄ v976) ∗ ((fsp + 984#64) ↦₆₄ v984) ∗ ((fsp + 992#64) ↦₆₄ v992) ∗
        memRegion (fsp + 1000#64) 392 ∗ ((fsp + 3216#64) ↦₆₄ vc90) ∗ ((fsp + 3224#64) ↦₆₄ vc98) ∗
        ((fsp + 4096#64) ↦₆₄ v4096) ∗ ((fsp + 4104#64) ↦₆₄ v4104) ∗ ((fsp + 4112#64) ↦₆₄ v4112) ∗
        stackAt fsp calleeStack ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          wordsAt stA c0.toList ∗ wordsAt (stA + 128#64) c1.toList ∗
          wordsAt (stA + 256#64) c2.toList ∗ wordsAt (stA + 384#64) c3.toList ∗
          ((stA + 512#64) ↦₆₄ w512) ∗ ((stA + 520#64) ↦₆₄ w520) ∗ ((fsp + 232#64) ↦₆₄ stA) ∗
          memRegion (fsp + 2752#64) 400 ∗ memRegion (fsp + 1872#64) 400 ∗
          copyScratchStackAt fsp (copyFullScratch sc d) ∗
          epilogueStoreStackPart1At fsp { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
          mid376At (fsp + 976#64) w512 w520 d400.w0 d400.mid352 ∗
          wordsAt (fsp + 1352#64) d400.tail.toList ∗
          ((fsp + 3216#64) ↦₆₄ c3.w13) ∗ ((fsp + 3224#64) ↦₆₄ c3.w14) ∗
          memRegion (fsp + 4096#64) 24 ∗ stackAt fsp calleeStack ∗ Rest) ∧
        sf.sp = fsp ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧ sf.readReg64 .x29 = fsp + 4144#64 ∧
        TraceCalleeSaved sf s_in) := by
  intro d; subst hsp
  have h400_len := d400.toBytes_length hmid352
  have h392_len := d400.tailBytes_length hmid352
  have h1872_split : ((s_in.sp + 1872#64) ↦ₛ d400.toBytes) =
      ((s_in.sp + 1872#64) ↦₆₄ d400.w0) ∗ ((s_in.sp + 1880#64) ↦ₛ d400.tailBytes) := by
    rw [← split400At_eq_pointsToBytes (s_in.sp + 1872#64) d400 hmid352,
        split400At_eq_w0_tailBytes (s_in.sp + 1872#64) d400 hmid352]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h2752_split : ((s_in.sp + 2752#64) ↦ₛ d400.toBytes) =
      ((s_in.sp + 2752#64) ↦₆₄ d400.w0) ∗ ((s_in.sp + 2760#64) ↦ₛ d400.tailBytes) := by
    rw [← split400At_eq_pointsToBytes (s_in.sp + 2752#64) d400 hmid352,
        split400At_eq_w0_tailBytes (s_in.sp + 2752#64) d400 hmid352]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h1000_split : ((s_in.sp + 1000#64) ↦ₛ d400.tailBytes) =
      ((s_in.sp + 1000#64) ↦ₛ d400.mid352) ∗ wordsAt (s_in.sp + 1352#64) d400.tail.toList := by
    dsimp only [Split400.tailBytes]
    rw [pointsToBytes_append (s_in.sp + 1000#64) d400.mid352 (wordsBytes d400.tail.toList),
        hmid352, ← wordsAt_eq_pointsToBytes]
    have ha : (s_in.sp + 1000#64) + BitVec.ofNat 64 352 = s_in.sp + 1352#64 := by bv_omega
    rw [ha]
  rw [split400At_eq_pointsToBytes (s_in.sp + 2752#64) d400 hmid352]
  refine SepWP.mono (post := fun sf Pf =>
      (Pf ⊢
        wordsAt stA c0.toList ∗ wordsAt (stA + 128#64) c1.toList ∗
        wordsAt (stA + 256#64) c2.toList ∗ wordsAt (stA + 384#64) c3.toList ∗
        ((stA + 512#64) ↦₆₄ w512) ∗ ((stA + 520#64) ↦₆₄ w520) ∗ ((s_in.sp + 232#64) ↦₆₄ stA) ∗
        (((s_in.sp + 2752#64) ↦₆₄ d400.w0) ∗ ((s_in.sp + 2760#64) ↦ₛ d400.tailBytes)) ∗
        (((s_in.sp + 1872#64) ↦₆₄ d400.w0) ∗ ((s_in.sp + 1880#64) ↦ₛ d400.tailBytes)) ∗
        copyScratchStackAt s_in.sp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At s_in.sp { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
          we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        mid376At (s_in.sp + 976#64) w512 w520 d400.w0 d400.mid352 ∗
        wordsAt (s_in.sp + 1352#64) d400.tail.toList ∗
        ((s_in.sp + 3216#64) ↦₆₄ c3.w13) ∗ ((s_in.sp + 3224#64) ↦₆₄ c3.w14) ∗
        (((s_in.sp + 4096#64) ↦₆₄ w512) ∗ ((s_in.sp + 4104#64) ↦₆₄ w520) ∗
          ((s_in.sp + 4112#64) ↦₆₄ d400.w0)) ∗
        stackAt s_in.sp calleeStack ∗ Rest) ∧
      sf.sp = s_in.sp ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
      sf.readReg64 .x23 = s_in.readReg64 .x23 ∧ sf.readReg64 .x29 = s_in.sp + 4144#64 ∧
      TraceCalleeSaved sf s_in) ?_ (fun sf Pf _ _ ⟨hPf, hrest⟩ => ⟨Entails.trans hPf ?_, hrest⟩)
  · states_recv_fetches_range b (Rust.withPanics ext) 16184 412
    dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::recv" = entry
    examples_hide_fetches
    dsimp only [d, mkSplit928From528And400, copyScratchStackAt, copyFullScratch,
      epilogueStoreStackPart1At, epilogueStackOfSplit928, mid376At, Words16.toList]
    simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd]
    ct1s4_steps_to_memcpy hstep_inv entry hinv hinv_call1
    ct1s4_call_memcpy hstep_inv hmemcpy_raw hinv_call1 hinv_sf1
      ⟨s_in.sp + 1872#64, s_in.sp + 2752#64, d400.toBytes⟩
    refine SepWP.focus_weaken (Entails.of_eq h1872_split) (by sep_focus) ?_
    refine SepWP.focus_weaken (Entails.of_eq h2752_split) (by sep_focus) ?_
    ct1s4_steps_to_memcpy hstep_inv entry hinv_sf1 hinv_call2
    ct1s4_call_memcpy hstep_inv hmemcpy_raw hinv_call2 _hinv_sf2
      ⟨s_in.sp + 1000#64, s_in.sp + 2760#64, d400.tailBytes⟩
    refine SepWP.focus_weaken (Entails.of_eq h1000_split) (by sep_focus) ?_
    wp_done
  · have h2752_mr : ((s_in.sp + 2752#64) ↦₆₄ d400.w0) ∗ ((s_in.sp + 2760#64) ↦ₛ d400.tailBytes) ⊢
        memRegion (s_in.sp + 2752#64) 400 := by
      rw [← h2752_split, ← h400_len]; exact ProofLib.pointsToBytes_entails_memRegion _ _
    have h1872_mr : ((s_in.sp + 1872#64) ↦₆₄ d400.w0) ∗ ((s_in.sp + 1880#64) ↦ₛ d400.tailBytes) ⊢
        memRegion (s_in.sp + 1872#64) 400 := by
      rw [← h1872_split, ← h400_len]; exact ProofLib.pointsToBytes_entails_memRegion _ _
    have h4096_mr : ((s_in.sp + 4096#64) ↦₆₄ w512) ∗ ((s_in.sp + 4104#64) ↦₆₄ w520) ∗
          ((s_in.sp + 4112#64) ↦₆₄ d400.w0) ⊢ memRegion (s_in.sp + 4096#64) 24 := by
      rw [ProofLib.memRegion_split' (b := s_in.sp + 4096#64) (n := 8) (k := 16)
            (b' := s_in.sp + 4104#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s_in.sp + 4104#64) (n := 8) (k := 8)
            (b' := s_in.sp + 4112#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (ProofLib.pointsTo64_entails_memRegion _ _))
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono h2752_mr (sepConj_mono h1872_mr (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h4096_mr)))))))))))))))

/-- Part 1 of Path 4a state assembly (`+16184 -> +16596`, `0x5938c..0x59528`):
    copies `d400` (`dec'`) and `stA + 8..528` (`sending_ct1` + `uc`) into the stack staging slots. -/
theorem ct1Sampled_copy_none_no_ack_part1
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s_in : State) (fsp stA : BitVec 64)
    (c0 c1 c2 c3 : Words16) (w512 w520 : BitVec 64) (d400 : Split400)
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (v976 v984 v992 vc90 vc98 v4096 v4104 v4112 : BitVec 64) (Rest : SepProp)
    (hmid352 : d400.mid352.length = 352) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 16184#64)
    (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64) :
    let d := mkSplit928From528And400 c0 c1 c2 c3 w512 w520 d400
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 16596#64) s_in
      (wordsAt stA c0.toList ∗ wordsAt (stA + 128#64) c1.toList ∗
        wordsAt (stA + 256#64) c2.toList ∗ wordsAt (stA + 384#64) c3.toList ∗
        ((stA + 512#64) ↦₆₄ w512) ∗ ((stA + 520#64) ↦₆₄ w520) ∗ ((fsp + 232#64) ↦₆₄ stA) ∗
        split400At (fsp + 2752#64) d400 ∗ memRegion (fsp + 1872#64) 400 ∗
        copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 976#64) ↦₆₄ v976) ∗ ((fsp + 984#64) ↦₆₄ v984) ∗ ((fsp + 992#64) ↦₆₄ v992) ∗
        memRegion (fsp + 1000#64) 392 ∗ ((fsp + 3216#64) ↦₆₄ vc90) ∗ ((fsp + 3224#64) ↦₆₄ vc98) ∗
        ((fsp + 4096#64) ↦₆₄ v4096) ∗ ((fsp + 4104#64) ↦₆₄ v4104) ∗ ((fsp + 4112#64) ↦₆₄ v4112) ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          wordsAt stA c0.toList ∗ wordsAt (stA + 128#64) c1.toList ∗
          wordsAt (stA + 256#64) c2.toList ∗ wordsAt (stA + 384#64) c3.toList ∗
          ((stA + 512#64) ↦₆₄ w512) ∗ ((stA + 520#64) ↦₆₄ w520) ∗ ((fsp + 232#64) ↦₆₄ stA) ∗
          memRegion (fsp + 2752#64) 400 ∗ memRegion (fsp + 1872#64) 400 ∗
          copyScratchStackAt fsp (copyFullScratch sc d) ∗
          epilogueStoreStackPart1At fsp { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
          mid376At (fsp + 976#64) w512 w520 d400.w0 d400.mid352 ∗
          wordsAt (fsp + 1352#64) d400.tail.toList ∗
          ((fsp + 3216#64) ↦₆₄ c3.w13) ∗ ((fsp + 3224#64) ↦₆₄ c3.w14) ∗
          memRegion (fsp + 4096#64) 24 ∗ Rest) ∧
        sf.sp = fsp ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧ sf.readReg64 .x29 = fsp + 4144#64 ∧
        TraceCalleeSaved sf s_in) := by
  intro d
  have h := ct1Sampled_copy_none_no_ack_part1_gen (fun _ _ => trivial)
    (ct1s4_memcpy_ok_zero hmemcpy) s_in fsp stA c0 c1 c2 c3 w512 w520 d400 sc k
    v976 v984 v992 vc90 vc98 v4096 v4104 v4112 Rest hmid352 hfsp_align hpc hrun hsp hx29 trivial
  dsimp only at h; rwa [ct1s4_stackAt_zero_sep fsp Rest] at h

/-- Part 1 of Path 4a state assembly (`+16184 -> +16596`, `0x5938c..0x59528`) under `AllocContractsX`. -/
theorem ct1Sampled_copy_none_no_ack_part1_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (s_in : State) (fsp stA : BitVec 64)
    (c0 c1 c2 c3 : Words16) (w512 w520 : BitVec 64) (d400 : Split400)
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (v976 v984 v992 vc90 vc98 v4096 v4104 v4112 : BitVec 64) (Rest : SepProp)
    (hmid352 : d400.mid352.length = 352) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 16184#64)
    (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64) (hinv : ImgCallInv img s_in) :
    let d := mkSplit928From528And400 c0 c1 c2 c3 w512 w520 d400
    SepWP (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 16596#64) s_in
      (wordsAt stA c0.toList ∗ wordsAt (stA + 128#64) c1.toList ∗
        wordsAt (stA + 256#64) c2.toList ∗ wordsAt (stA + 384#64) c3.toList ∗
        ((stA + 512#64) ↦₆₄ w512) ∗ ((stA + 520#64) ↦₆₄ w520) ∗ ((fsp + 232#64) ↦₆₄ stA) ∗
        split400At (fsp + 2752#64) d400 ∗ memRegion (fsp + 1872#64) 400 ∗
        copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 976#64) ↦₆₄ v976) ∗ ((fsp + 984#64) ↦₆₄ v984) ∗ ((fsp + 992#64) ↦₆₄ v992) ∗
        memRegion (fsp + 1000#64) 392 ∗ ((fsp + 3216#64) ↦₆₄ vc90) ∗ ((fsp + 3224#64) ↦₆₄ vc98) ∗
        ((fsp + 4096#64) ↦₆₄ v4096) ∗ ((fsp + 4104#64) ↦₆₄ v4104) ∗ ((fsp + 4112#64) ↦₆₄ v4112) ∗
        stackAt fsp statesRecvCalleeStackX ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          wordsAt stA c0.toList ∗ wordsAt (stA + 128#64) c1.toList ∗
          wordsAt (stA + 256#64) c2.toList ∗ wordsAt (stA + 384#64) c3.toList ∗
          ((stA + 512#64) ↦₆₄ w512) ∗ ((stA + 520#64) ↦₆₄ w520) ∗ ((fsp + 232#64) ↦₆₄ stA) ∗
          memRegion (fsp + 2752#64) 400 ∗ memRegion (fsp + 1872#64) 400 ∗
          copyScratchStackAt fsp (copyFullScratch sc d) ∗
          epilogueStoreStackPart1At fsp { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
          mid376At (fsp + 976#64) w512 w520 d400.w0 d400.mid352 ∗
          wordsAt (fsp + 1352#64) d400.tail.toList ∗
          ((fsp + 3216#64) ↦₆₄ c3.w13) ∗ ((fsp + 3224#64) ↦₆₄ c3.w14) ∗
          memRegion (fsp + 4096#64) 24 ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
        sf.sp = fsp ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧ sf.readReg64 .x29 = fsp + 4144#64 ∧
        TraceCalleeSaved sf s_in) := by
  intro d; rw [ct1s4_stackAt_statesRecvCallee_sep fsp Rest]
  exact ct1Sampled_copy_none_no_ack_part1_gen ct1s4_imgCallInv_steps
    (ct1s4_memcpy_ok_ext hA) s_in fsp stA c0 c1 c2 c3 w512 w520 d400 sc k
    v976 v984 v992 vc90 vc98 v4096 v4104 v4112 (memRegion (fsp - 19552#64) 3168 ∗ Rest)
    hmid352 hfsp_align hpc hrun hsp hx29 hinv

set_option maxHeartbeats 1600000 in
private theorem ct1Sampled_copy_none_no_ack_part2_gen
    {b : BitVec 64} {ext : String → Option (State → State)} {Inv : State → Prop} {calleeStack : Nat}
    (hstep_inv : ∀ {s s' : State}, Inv s → Steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) s s' → Inv s')
    (hmemcpy_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      (ct1s4MemcpySpec Inv calleeStack))
    (s_in : State) (fsp stA outA : BitVec 64)
    (c0 c1 c2 c3 : Words16) (w512 w520 : BitVec 64) (d400 : Split400)
    (sc : CopyScratchStack) (k : EpilogueStoreStack) (c_ca0 : Words5) (Rest : SepProp)
    (htag : c0.w0 = 0#64 ∨ c0.w0 = 1#64) (hmid352 : d400.mid352.length = 352)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 16596#64)
    (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA) (hx23 : s_in.readReg64 .x23 = c0.w0) (hinv : Inv s_in) :
    let d := mkSplit928From528And400 c0 c1 c2 c3 w512 w520 d400
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64) s_in
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At fsp { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
          we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        mid376At (fsp + 976#64) w512 w520 d400.w0 d400.mid352 ∗
        wordsAt (fsp + 1352#64) d400.tail.toList ∗
        ((fsp + 3216#64) ↦₆₄ c3.w13) ∗ ((fsp + 3224#64) ↦₆₄ c3.w14) ∗
        wordsAt (fsp + 3232#64) c_ca0.toList ∗ memRegion (fsp + 3272#64) 376 ∗
        stackAt fsp calleeStack ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          copyScratchStackAt fsp (copyFullScratch sc d) ∗
          epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          memRegion (fsp + 976#64) 376 ∗ memRegion (fsp + 1352#64) 40 ∗
          memRegion (fsp + 3216#64) 16 ∗ memRegion (fsp + 3232#64) 40 ∗
          memRegion (fsp + 3272#64) 376 ∗ stackAt fsp calleeStack ∗ Rest) ∧
        epilogueRegsEqSplit928 sf d ∧ sf.sp = fsp ∧ sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧ TraceCalleeSaved sf s_in) := by
  intro d; subst hsp hx19
  have hmid376_len : (mid376Bytes w512 w520 d400.w0 d400.mid352).length = 376 :=
    mid376Bytes_length w512 w520 d400.w0 hmid352
  rw [mid376At_eq_pointsToBytes (s_in.sp + 976#64) w512 w520 d400.w0 d400.mid352]
  change SepWP (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64) s_in
    (copyScratchStackAt s_in.sp (copyFullScratch sc d) ∗
      epilogueStoreStackPart1At s_in.sp { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
        we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
      ((s_in.sp + 232#64) ↦₆₄ stA) ∗ ((s_in.sp + 512#64) ↦₆₄ k.w200) ∗ ((s_in.sp + 520#64) ↦₆₄ k.w208) ∗
      wordsAt (s_in.sp + 528#64) k.tail.toList ∗ memRegion (s_in.sp + 576#64) 376 ∗
      ((s_in.sp + 976#64) ↦ₛ d.mid) ∗ wordsAt (s_in.sp + 1352#64) d.tail.toList ∗
      ((s_in.sp + 3216#64) ↦₆₄ c3.w13) ∗ ((s_in.sp + 3224#64) ↦₆₄ c3.w14) ∗
      wordsAt (s_in.sp + 3232#64) c_ca0.toList ∗ memRegion (s_in.sp + 3272#64) 376 ∗
      stackAt s_in.sp calleeStack ∗ Rest) _
  refine SepWP.mono (post := fun sf Pf =>
      (Pf ⊢
        copyScratchStackAt s_in.sp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At s_in.sp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
        epilogueStoreStackPart2At s_in.sp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
        ((s_in.sp + 976#64) ↦ₛ d.mid) ∗ wordsAt (s_in.sp + 1352#64) d.tail.toList ∗
        (((s_in.sp + 3216#64) ↦₆₄ c3.w13) ∗ ((s_in.sp + 3224#64) ↦₆₄ c3.w14)) ∗
        wordsAt (s_in.sp + 3232#64) d.tail.toList ∗ ((s_in.sp + 3272#64) ↦ₛ d.mid) ∗
        stackAt s_in.sp calleeStack ∗ Rest) ∧
      epilogueRegsEqSplit928 sf d ∧ sf.sp = s_in.sp ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
      sf.readReg64 .x29 = s_in.readReg64 .x29 ∧ TraceCalleeSaved sf s_in) ?_
    (fun sf Pf _ _ ⟨hPf, hrest⟩ => ⟨Entails.trans hPf ?_, hrest⟩)
  · states_recv_fetches_range b (Rust.withPanics ext) 16596 204
    states_recv_fetches_range b (Rust.withPanics ext) 11384 12
    dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::recv" = entry
    examples_hide_fetches
    dsimp only [d, mkSplit928From528And400, copyScratchStackAt, copyFullScratch,
      epilogueStoreStackPart1At, epilogueStoreStackPart2At, epilogueStackOfSplit928,
      epilogueRegsEqSplit928, EpilogueStoreStack.tail, noneCap, Words16.toList, Words5.toList]
    simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd]
    rcases htag with h0 | h0
    · have hx23_0 : s_in.readReg64 .x23 = 0#64 := hx23.trans h0
      rw [h0]
      ct1s4_steps_to_memcpy hstep_inv entry hinv hinv_call1
      ct1s4_call_memcpy hstep_inv hmemcpy_raw hinv_call1 hinv_sf1
        ⟨s_in.sp + 3272#64, s_in.sp + 976#64, mid376Bytes w512 w520 d400.w0 d400.mid352⟩
      ct1s4_steps_to_memcpy hstep_inv entry hinv_sf1 hinv_call2
      ct1s4_call_memcpy hstep_inv hmemcpy_raw hinv_call2 _hinv_sf2
        ⟨s_in.sp + 576#64, s_in.sp + 3272#64, mid376Bytes w512 w520 d400.w0 d400.mid352⟩
      wp_steps; wp_done
    · have hx23_0 : s_in.readReg64 .x23 = 1#64 := hx23.trans h0
      rw [h0]
      ct1s4_steps_to_memcpy hstep_inv entry hinv hinv_call1
      ct1s4_call_memcpy hstep_inv hmemcpy_raw hinv_call1 hinv_sf1
        ⟨s_in.sp + 3272#64, s_in.sp + 976#64, mid376Bytes w512 w520 d400.w0 d400.mid352⟩
      ct1s4_steps_to_memcpy hstep_inv entry hinv_sf1 hinv_call2
      ct1s4_call_memcpy hstep_inv hmemcpy_raw hinv_call2 _hinv_sf2
        ⟨s_in.sp + 576#64, s_in.sp + 3272#64, mid376Bytes w512 w520 d400.w0 d400.mid352⟩
      wp_steps; wp_done
  · have h976_mr := pointsToBytes_entails_memRegion_376 (s_in.sp + 976#64) d.mid hmid376_len
    have h1352_mr := wordsAt_entails_memRegion d.tail.toList (s_in.sp + 1352#64) 40 rfl
    have h3216_mr : ((s_in.sp + 3216#64) ↦₆₄ c3.w13) ∗ ((s_in.sp + 3224#64) ↦₆₄ c3.w14) ⊢
        memRegion (s_in.sp + 3216#64) 16 := by
      rw [ProofLib.memRegion_split' (b := s_in.sp + 3216#64) (n := 8) (k := 8)
            (b' := s_in.sp + 3224#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (ProofLib.pointsTo64_entails_memRegion _ _)
    have h3232_mr := wordsAt_entails_memRegion d.tail.toList (s_in.sp + 3232#64) 40 rfl
    have h3272_mr := pointsToBytes_entails_memRegion_376 (s_in.sp + 3272#64) d.mid hmid376_len
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono h976_mr (sepConj_mono h1352_mr (sepConj_mono h3216_mr
        (sepConj_mono h3232_mr (sepConj_mono_left h3272_mr)))))))

/-- Part 2 of Path 4a state assembly (`+16596 -> +18996`, `0x59528..0x595f4` and `0x580cc..0x580d8`):
    copies `mid` (`376`B) and `tail` (`40`B) to `fsp + 576` and `fsp + 528`, loads registers from
    `copyScratchStackAt`, and jumps to `+18996` (`ct1Sampled_epilogue_store`). -/
theorem ct1Sampled_copy_none_no_ack_part2
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s_in : State) (fsp stA outA : BitVec 64)
    (c0 c1 c2 c3 : Words16) (w512 w520 : BitVec 64) (d400 : Split400)
    (sc : CopyScratchStack) (k : EpilogueStoreStack) (c_ca0 : Words5) (Rest : SepProp)
    (htag : c0.w0 = 0#64 ∨ c0.w0 = 1#64) (hmid352 : d400.mid352.length = 352)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 16596#64)
    (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA) (hx23 : s_in.readReg64 .x23 = c0.w0) :
    let d := mkSplit928From528And400 c0 c1 c2 c3 w512 w520 d400
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64) s_in
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At fsp { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
          we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        mid376At (fsp + 976#64) w512 w520 d400.w0 d400.mid352 ∗
        wordsAt (fsp + 1352#64) d400.tail.toList ∗
        ((fsp + 3216#64) ↦₆₄ c3.w13) ∗ ((fsp + 3224#64) ↦₆₄ c3.w14) ∗
        wordsAt (fsp + 3232#64) c_ca0.toList ∗ memRegion (fsp + 3272#64) 376 ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          copyScratchStackAt fsp (copyFullScratch sc d) ∗
          epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          memRegion (fsp + 976#64) 376 ∗ memRegion (fsp + 1352#64) 40 ∗
          memRegion (fsp + 3216#64) 16 ∗ memRegion (fsp + 3232#64) 40 ∗
          memRegion (fsp + 3272#64) 376 ∗ Rest) ∧
        epilogueRegsEqSplit928 sf d ∧ sf.sp = fsp ∧ sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧ TraceCalleeSaved sf s_in) := by
  intro d
  have h := ct1Sampled_copy_none_no_ack_part2_gen (fun _ _ => trivial)
    (ct1s4_memcpy_ok_zero hmemcpy) s_in fsp stA outA c0 c1 c2 c3 w512 w520 d400 sc k c_ca0 Rest
    htag hmid352 hfsp_align hpc hrun hsp hx19 hx23 trivial
  dsimp only at h; rwa [ct1s4_stackAt_zero_sep fsp Rest] at h

/-- Part 2 of Path 4a state assembly (`+16596 -> +18996`) under `AllocContractsX`. -/
theorem ct1Sampled_copy_none_no_ack_part2_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (s_in : State) (fsp stA outA : BitVec 64)
    (c0 c1 c2 c3 : Words16) (w512 w520 : BitVec 64) (d400 : Split400)
    (sc : CopyScratchStack) (k : EpilogueStoreStack) (c_ca0 : Words5) (Rest : SepProp)
    (htag : c0.w0 = 0#64 ∨ c0.w0 = 1#64) (hmid352 : d400.mid352.length = 352)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 16596#64)
    (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA) (hx23 : s_in.readReg64 .x23 = c0.w0)
    (hinv : ImgCallInv img s_in) :
    let d := mkSplit928From528And400 c0 c1 c2 c3 w512 w520 d400
    SepWP (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 18996#64) s_in
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At fsp { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
          we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        mid376At (fsp + 976#64) w512 w520 d400.w0 d400.mid352 ∗
        wordsAt (fsp + 1352#64) d400.tail.toList ∗
        ((fsp + 3216#64) ↦₆₄ c3.w13) ∗ ((fsp + 3224#64) ↦₆₄ c3.w14) ∗
        wordsAt (fsp + 3232#64) c_ca0.toList ∗ memRegion (fsp + 3272#64) 376 ∗
        stackAt fsp statesRecvCalleeStackX ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          copyScratchStackAt fsp (copyFullScratch sc d) ∗
          epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          memRegion (fsp + 976#64) 376 ∗ memRegion (fsp + 1352#64) 40 ∗
          memRegion (fsp + 3216#64) 16 ∗ memRegion (fsp + 3232#64) 40 ∗
          memRegion (fsp + 3272#64) 376 ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
        epilogueRegsEqSplit928 sf d ∧ sf.sp = fsp ∧ sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧ TraceCalleeSaved sf s_in) := by
  intro d; rw [ct1s4_stackAt_statesRecvCallee_sep fsp Rest]
  exact ct1Sampled_copy_none_no_ack_part2_gen ct1s4_imgCallInv_steps
    (ct1s4_memcpy_ok_ext hA) s_in fsp stA outA c0 c1 c2 c3 w512 w520 d400 sc k c_ca0
    (memRegion (fsp - 19552#64) 3168 ∗ Rest) htag hmid352 hfsp_align hpc hrun hsp hx19 hx23 hinv

/-! ## 4. Path 4b (`outMsg = none, ack = true`): `+13972 -> +16596 -> +17192 -> +18996` -/

theorem polyEncoderBodyAt_entails_vecs_tail (A : RustAlloc) (stA : BitVec 64) (enc : PolyEncoder) :
    polyEncoderBodyAt A (stA + 8#64) enc ⊢
      ∃∗ vecs : List (List GF16),
        ⌜vecs.length = NUM_POLYS⌝ ∗
        vecGF16ListOf A (stA + 8#64) vecs ∗
        memRegion (stA + 392#64) 8 := by
  unfold polyEncoderBodyAt
  have htail := polyEncoderTail_entails_memRegion_8 stA enc.idx
  unfold polyEncoderIdxOff polyEncoderPadOff at htail
  have h392 : (stA + 8#64) + 384#64 = stA + 0x188#64 := by bv_omega
  have h396 : (stA + 8#64) + 388#64 = stA + 0x18c#64 := by bv_omega
  rw [h392, h396]
  cases hs : enc.s with
  | points pts =>
    dsimp only
    rw [pointListOf_eq_vecGF16ListOf]
    refine Entails.sepExists_right (pts.map Point.value) ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hlen => ?_
    have hlen' : (pts.map Point.value).length = NUM_POLYS := by simp [hlen]
    refine Entails.pure_right hlen' ?_
    exact sepConj_mono_right htail
  | polys ps =>
    dsimp only
    rw [polyListOf_eq_vecGF16ListOf]
    refine Entails.sepExists_right (ps.map LibsignalSpqrV1.Poly.coefficients) ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hlen => ?_
    have hlen' : (ps.map LibsignalSpqrV1.Poly.coefficients).length = NUM_POLYS := by simp [hlen]
    refine Entails.pure_right hlen' ?_
    exact sepConj_mono_right htail

def mkSplit928Ct1Acknowledged (c_uc : Words16) (c_dec : Words50)
    (bs352 : List (BitVec 8)) (tail5 : Words5) : Split928 where
  c0 := {
    w0 := 11#64
    w1 := c_uc.w0
    w2 := c_uc.w1
    w3 := c_uc.w2
    w4 := c_uc.w3
    w5 := c_uc.w4
    w6 := c_uc.w5
    w7 := c_uc.w6
    w8 := c_uc.w7
    w9 := c_uc.w8
    w10 := c_uc.w9
    w11 := c_uc.w10
    w12 := c_uc.w11
    w13 := c_uc.w12
    w14 := c_uc.w13
    w15 := c_uc.w14
  }
  c1 := {
    w0 := c_uc.w15
    w1 := c_dec.c0.w0
    w2 := c_dec.c0.w1
    w3 := c_dec.c0.w2
    w4 := c_dec.c0.w3
    w5 := c_dec.c0.w4
    w6 := c_dec.c0.w5
    w7 := c_dec.c0.w6
    w8 := c_dec.c0.w7
    w9 := c_dec.c0.w8
    w10 := c_dec.c0.w9
    w11 := c_dec.c0.w10
    w12 := c_dec.c0.w11
    w13 := c_dec.c0.w12
    w14 := c_dec.c0.w13
    w15 := c_dec.c0.w14
  }
  c2 := {
    w0 := c_dec.c0.w15
    w1 := c_dec.c1.w0
    w2 := c_dec.c1.w1
    w3 := c_dec.c1.w2
    w4 := c_dec.c1.w3
    w5 := c_dec.c1.w4
    w6 := c_dec.c1.w5
    w7 := c_dec.c1.w6
    w8 := c_dec.c1.w7
    w9 := c_dec.c1.w8
    w10 := c_dec.c1.w9
    w11 := c_dec.c1.w10
    w12 := c_dec.c1.w11
    w13 := c_dec.c1.w12
    w14 := c_dec.c1.w13
    w15 := c_dec.c1.w14
  }
  c3 := {
    w0 := c_dec.c1.w15
    w1 := c_dec.c2.w0
    w2 := c_dec.c2.w1
    w3 := c_dec.c2.w2
    w4 := c_dec.c2.w3
    w5 := c_dec.c2.w4
    w6 := c_dec.c2.w5
    w7 := c_dec.c2.w6
    w8 := c_dec.c2.w7
    w9 := c_dec.c2.w8
    w10 := c_dec.c2.w9
    w11 := c_dec.c2.w10
    w12 := c_dec.c2.w11
    w13 := c_dec.c2.w12
    w14 := c_dec.c2.w13
    w15 := c_dec.c2.w14
  }
  mid := mid376Bytes c_dec.c2.w15 c_dec.w48 c_dec.w49 bs352
  tail := tail5

theorem mkSplit928Ct1Acknowledged_mid_length (c_uc : Words16) (c_dec : Words50)
    {bs352 : List (BitVec 8)} (tail5 : Words5) (h : bs352.length = 352) :
    (mkSplit928Ct1Acknowledged c_uc c_dec bs352 tail5).mid.length = 376 :=
  mid376Bytes_length c_dec.c2.w15 c_dec.w48 c_dec.w49 h

set_option maxHeartbeats 1600000 in
/-- Part 1 of Path 4b (`+13972 -> +16596`, `0x58ae8..0x58ca8`):
    loads `c_dec` (`dec'` at `fsp + 2752`) and `c_uc` (`st.uc` at `stA + 400`) into the stack
    staging slots, calls `drop_glue::<[Poly; 16]>(stA + 8)` to drop `st.sending_ct1`, sets
    `x23 = 2#64`, and branches to `+16596` (`0x59528`). -/
theorem ct1Sampled_copy_none_ack_part1
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s_in : State) (fsp stA : BitVec 64)
    (vecs : List (List GF16)) (hvecs_len : vecs.length = NUM_POLYS)
    (c_uc : Words16) (c_dec : Words50)
    (bs352_mid : List (BitVec 8)) (tail5_mid : Words5)
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (v976 v984 v992 vc90 vc98 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 13972#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) :
    let d := mkSplit928Ct1Acknowledged c_uc c_dec bs352_mid tail5_mid
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 16596#64) s_in
      (vecGF16ListOf A (stA + 8#64) vecs ∗
        wordsAt (stA + 400#64) c_uc.toList ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗
        words50At (fsp + 2752#64) c_dec ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 976#64) ↦₆₄ v976) ∗
        ((fsp + 984#64) ↦₆₄ v984) ∗
        ((fsp + 992#64) ↦₆₄ v992) ∗
        ((fsp + 3216#64) ↦₆₄ vc90) ∗
        ((fsp + 3224#64) ↦₆₄ vc98) ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          memRegion (stA + 8#64) 384 ∗
          wordsAt (stA + 400#64) c_uc.toList ∗
          ((fsp + 232#64) ↦₆₄ stA) ∗
          memRegion (fsp + 2752#64) 400 ∗
          copyScratchStackAt fsp (copyFullScratch sc d) ∗
          epilogueStoreStackPart1At fsp
            { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
              we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
          ((fsp + 976#64) ↦₆₄ c_dec.c2.w15) ∗
          ((fsp + 984#64) ↦₆₄ c_dec.w48) ∗
          ((fsp + 992#64) ↦₆₄ c_dec.w49) ∗
          ((fsp + 3216#64) ↦₆₄ c_dec.c2.w12) ∗
          ((fsp + 3224#64) ↦₆₄ c_dec.c2.w13) ∗
          A.pool ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x23 = 2#64 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  intro d
  subst hsp
  have hdrop := dropPoly16_ok_at_statesRecv hdealloc
  have hsplit := stackAt_statesRecvCallee_eq_dropGluePoly16' s_in.sp
  refine SepWP.mono (post := fun sf Pf =>
      (Pf ⊢
        memRegion (stA + 8#64) 384 ∗
        wordsAt (stA + 400#64) c_uc.toList ∗
        ((s_in.sp + 232#64) ↦₆₄ stA) ∗
        words50At (s_in.sp + 2752#64) c_dec ∗
        copyScratchStackAt s_in.sp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At s_in.sp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((s_in.sp + 976#64) ↦₆₄ c_dec.c2.w15) ∗
        ((s_in.sp + 984#64) ↦₆₄ c_dec.w48) ∗
        ((s_in.sp + 992#64) ↦₆₄ c_dec.w49) ∗
        ((s_in.sp + 3216#64) ↦₆₄ c_dec.c2.w12) ∗
        ((s_in.sp + 3224#64) ↦₆₄ c_dec.c2.w13) ∗
        A.pool ∗
        stackAt s_in.sp statesRecvCalleeStackX ∗
        Rest) ∧
      sf.sp = s_in.sp ∧
      sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
      sf.readReg64 .x23 = 2#64 ∧
      sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
      sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
      sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
      TraceCalleeSaved sf s_in) ?_ (fun sf Pf _ _ ⟨hPf, hrest⟩ => ⟨Entails.trans hPf ?_, hrest⟩)
  · states_recv_fetches_range b (Rust.withPanics ext) 13972 452
    dsimp only [tripleRatchetProgAtExt, statesRecvName, polyArrayBytes, BitVec.ofNat_eq_ofNat]
      at hpc hdrop hsplit ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::recv" = entry
    examples_hide_fetches
    rw [hsplit]
    dsimp only [d, mkSplit928Ct1Acknowledged, copyScratchStackAt, copyFullScratch,
      epilogueStoreStackPart1At, epilogueStackOfSplit928, words50At, Words16.toList]
    simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    wp_call hdrop ⟨stA + 8#64, vecs⟩
    wp_steps
    wp_done
  · have h2752_mr := words50At_entails_memRegion (s_in.sp + 2752#64) c_dec
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h2752_mr)))

theorem fnAddr_adrp_59794 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr statesRecvName + 17216#64) &&&
      0xfffffffffffff000#64) = b + 0x54000#64 := by
  rw [Program.fnAddr_rebase, statesRecv_fnOff]
  revert hb; bv_bits

private theorem ct1Sampled_copy_none_ack_part2a_gen
    {b : BitVec 64} {ext : String → Option (State → State)}
    {Inv : State → Prop} {calleeStack : Nat}
    (hstep_inv : ∀ {s s' : State}, Inv s →
      Steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) s s' → Inv s')
    (hmemcpy_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      (ct1s4MemcpySpec Inv calleeStack))
    (s_in : State) (fsp : BitVec 64)
    (w0 w8 w16 : BitVec 64) (bs352_976 : List (BitVec 8))
    (c_1352 c_ca0 : Words5)
    (Rest : SepProp)
    (h976_len : bs352_976.length = 352)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 16596#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx23 : s_in.readReg64 .x23 = 2#64)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64)
    (hinv : Inv s_in) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 17192#64) s_in
      (mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗
        wordsAt (fsp + 1352#64) c_1352.toList ∗
        wordsAt (fsp + 3232#64) c_ca0.toList ∗
        memRegion (fsp + 3272#64) 376 ∗
        stackAt fsp calleeStack ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗
          wordsAt (fsp + 1352#64) c_1352.toList ∗
          wordsAt (fsp + 3232#64) c_1352.toList ∗
          mid376At (fsp + 3272#64) w0 w8 w16 bs352_976 ∗
          stackAt fsp calleeStack ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x28 = fsp + 3272#64 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  have hmid376_len : (mid376Bytes w0 w8 w16 bs352_976).length = 376 :=
    mid376Bytes_length w0 w8 w16 h976_len
  rw [mid376At_eq_pointsToBytes (s_in.sp + 976#64) w0 w8 w16 bs352_976,
      mid376At_eq_pointsToBytes (s_in.sp + 3272#64) w0 w8 w16 bs352_976]
  states_recv_fetches_range b (Rust.withPanics ext) 16596 68
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  dsimp only [Words5.toList]
  simp only [wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd, hx23, hx28]
  ct1s4_steps_to_memcpy hstep_inv entry hinv hinv_call1
  ct1s4_call_memcpy hstep_inv hmemcpy_raw hinv_call1 _hinv_sf
    ⟨s_in.sp + 3272#64, s_in.sp + 976#64, mid376Bytes w0 w8 w16 bs352_976⟩
  wp_steps
  wp_done

/-- Part 2a of Path 4b (`+16596 -> +17192`, `0x59528..0x59568`):
    copies `376`B from `fsp + 976` to `fsp + 3272` (`x28`), copies `fsp + 1352..1392` to `fsp + 3232..3272`,
    and branches on `x23 = 2#64` to `+17192` (`0x5977c`). -/
theorem ct1Sampled_copy_none_ack_part2a
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s_in : State) (fsp : BitVec 64)
    (w0 w8 w16 : BitVec 64) (bs352_976 : List (BitVec 8))
    (c_1352 c_ca0 : Words5)
    (Rest : SepProp)
    (h976_len : bs352_976.length = 352)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 16596#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx23 : s_in.readReg64 .x23 = 2#64)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 17192#64) s_in
      (mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗
        wordsAt (fsp + 1352#64) c_1352.toList ∗
        wordsAt (fsp + 3232#64) c_ca0.toList ∗
        memRegion (fsp + 3272#64) 376 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗
          wordsAt (fsp + 1352#64) c_1352.toList ∗
          wordsAt (fsp + 3232#64) c_1352.toList ∗
          mid376At (fsp + 3272#64) w0 w8 w16 bs352_976 ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x28 = fsp + 3272#64 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  have h := ct1Sampled_copy_none_ack_part2a_gen (fun _ _ => trivial)
    (ct1s4_memcpy_ok_zero hmemcpy) s_in fsp w0 w8 w16 bs352_976 c_1352 c_ca0 Rest
    h976_len hfsp_align hpc hrun hsp hx23 hx28 trivial
  rwa [ct1s4_stackAt_zero_sep fsp Rest] at h

/-- Part 2a of Path 4b (`+16596 -> +17192`, `0x59528..0x59568`) under `AllocContractsX`. -/
theorem ct1Sampled_copy_none_ack_part2a_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (s_in : State) (fsp : BitVec 64)
    (w0 w8 w16 : BitVec 64) (bs352_976 : List (BitVec 8))
    (c_1352 c_ca0 : Words5)
    (Rest : SepProp)
    (h976_len : bs352_976.length = 352)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 16596#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx23 : s_in.readReg64 .x23 = 2#64)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64)
    (hinv : ImgCallInv img s_in) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 17192#64) s_in
      (mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗
        wordsAt (fsp + 1352#64) c_1352.toList ∗
        wordsAt (fsp + 3232#64) c_ca0.toList ∗
        memRegion (fsp + 3272#64) 376 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗
          wordsAt (fsp + 1352#64) c_1352.toList ∗
          wordsAt (fsp + 3232#64) c_1352.toList ∗
          mid376At (fsp + 3272#64) w0 w8 w16 bs352_976 ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x28 = fsp + 3272#64 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  rw [ct1s4_stackAt_statesRecvCallee_sep fsp Rest]
  exact ct1Sampled_copy_none_ack_part2a_gen ct1s4_imgCallInv_steps
    (ct1s4_memcpy_ok_ext hA) s_in fsp w0 w8 w16 bs352_976 c_1352 c_ca0
    (memRegion (fsp - 19552#64) 3168 ∗ Rest) h976_len hfsp_align hpc hrun hsp hx23 hx28 hinv

set_option maxHeartbeats 1600000 in
/-- Part 2b of Path 4b (`+17192 -> +17360 -> +18996`, `0x5977c..0x597b8` and `0x59824..0x59888`):
    checks `MAX_LOG_LEVEL_FILTER` (`0 <= 2`), writes `w512, w520, w528` to `fsp + 576..600`,
    writes `we0 = 11#64` and `we8 = noneCap`, loads registers from `copyScratchStackAt`,
    and jumps to `+18996`. -/
theorem ct1Sampled_copy_none_ack_part2b
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (s_in : State) (fsp stA outA : BitVec 64)
    (c_uc : Words16) (c_dec : Words50)
    (bs352_976 bs352_576 : List (BitVec 8))
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (v576 v584 v592 vf10 vf18 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 17192#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64) :
    let d := mkSplit928Ct1Acknowledged c_uc c_dec bs352_576 k.tail
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64) s_in
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
        mid376At (fsp + 976#64) c_dec.c2.w15 c_dec.w48 c_dec.w49 bs352_976 ∗
        ((fsp + 3216#64) ↦₆₄ c_dec.c2.w12) ∗
        ((fsp + 3224#64) ↦₆₄ c_dec.c2.w13) ∗
        mid376At (fsp + 3272#64) c_dec.c2.w15 c_dec.w48 c_dec.w49 bs352_976 ∗
        ((fsp + 3856#64) ↦₆₄ vf10) ∗
        ((fsp + 3864#64) ↦₆₄ vf18) ∗
        statesRecvRoAt b ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          copyScratchStackAt fsp (copyFullScratch sc d) ∗
          epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          mid376At (fsp + 976#64) c_dec.c2.w15 c_dec.w48 c_dec.w49 bs352_976 ∗
          ((fsp + 3216#64) ↦₆₄ c_dec.c2.w12) ∗
          ((fsp + 3224#64) ↦₆₄ c_dec.c2.w13) ∗
          mid376At (fsp + 3272#64) c_dec.c2.w15 c_dec.w48 c_dec.w49 bs352_976 ∗
          ((fsp + 3856#64) ↦₆₄ c_dec.c2.w12) ∗
          ((fsp + 3864#64) ↦₆₄ c_dec.c2.w13) ∗
          statesRecvRoAt b ∗
          Rest) ∧
        epilogueRegsEqSplit928 sf d ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  intro d
  subst hsp hx19
  have hadrp := fnAddr_adrp_59794 (b := b) (H := Rust.withPanics ext) hb
  states_recv_fetches_range b (Rust.withPanics ext) 17192 68
  states_recv_fetches_range b (Rust.withPanics ext) 17360 104
  dsimp only [tripleRatchetProgAtExt, statesRecvName, statesRecvRoAt, unchunkedSendCt2RoAt,
    logOff, BitVec.ofNat_eq_ofNat] at hpc hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  dsimp only [epilogueStoreStackPart2At]
  rw [show (epilogueStackOfSplit928 d noneCap k.w200 k.w208).mid =
      mid376Bytes c_dec.c2.w15 c_dec.w48 c_dec.w49 bs352_576 from rfl,
      ← mid376At_eq_pointsToBytes (s_in.sp + 576#64) c_dec.c2.w15 c_dec.w48 c_dec.w49 bs352_576]
  dsimp only [d, mkSplit928Ct1Acknowledged, copyScratchStackAt, copyFullScratch,
    epilogueStoreStackPart1At, epilogueStackOfSplit928, epilogueRegsEqSplit928,
    EpilogueStoreStack.tail, mid376At, noneCap, Words16.toList, Words5.toList]
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd, hx28]
  wp_steps
  wp_done

end CryptoVerification.SpqrV1.States.Recv
