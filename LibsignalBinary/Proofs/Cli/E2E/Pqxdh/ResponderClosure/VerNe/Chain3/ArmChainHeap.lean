/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.DecInterface
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeSenderChainAux.Fetch

/-!
# Tag-6 (`sender_chain`) Heap Framing Lemmas

Separation-logic splitting and framing identities for `prostSSGQAt` (`overDecChainRest`,
`overDecChainFrameExt`) around the tag-6 `message::merge<Chain> [local#5]` call at `ss + 0x90`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record (A0)
open CryptoVerification.E2E.Record.DeserializeGeneral (ChainG prostChainGAt GenField SSG)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt ExtraGQ)

/-! ## 1. `prostSSGQAt` without `sender_chain` -/


/-- `prostSSGQAt A ss v` without the `sender_chain` match (`ss + 0x90`), the other fields in the
same order. -/
def overDecChainRest (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗ vecU8 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         CryptoVerification.E2E.Record.L1GX.pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    CryptoVerification.E2E.Record.L1GX.kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

/-- With no sender chain, `prostSSGQAt` is the `None` niche, the 96 spare bytes, and the rest. -/
theorem overDecChain_split_none (A : RustAlloc) (ss : BitVec 64) (v : SSGQ)
    (hnone : v.base.sender = none) :
    prostSSGQAt A ss v =
      ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96 ∗ overDecChainRest A ss v := by
  unfold prostSSGQAt overDecChainRest
  rw [hnone]
  cases v.base.pending <;> (dsimp only; ac_rfl)

/-- After `apply (.sender c)`, `prostSSGQAt` is the chain at `ss + 0x90` and the rest of `v`
(the rest does not mention `sender`). -/
theorem overDecChain_split_some (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) (c : ChainG) :
    prostSSGQAt A ss ⟨v.base.apply (.sender c), v.ext⟩ =
      prostChainGAt A (ss + 0x90#64) c ∗ overDecChainRest A ss v := by
  rcases v with ⟨⟨ver, lik, rik, root, prevCounter, recv, sender, pending⟩, ext⟩
  unfold prostSSGQAt overDecChainRest SSG.apply
  cases pending <;> (dsimp only; ac_rfl)

/-! ## 2. The frame and the pre / post heaps -/

/-- Everything the tag-6 `merge<Chain>` call does not touch at allocator `A` (note `A.pool` is
passed into `chainMerge3SpecAtWExt A` rather than framed out). -/
def overDecChainFrameExt (A : RustAlloc) (g : OverDecG) (pfx : List (BitVec 8))
    (v : SSGQ) : SepProp :=
  overPrevElemRestExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗ (g.encPtr ↦ₛ pfx) ∗
    overDecChainRest A (g.q + 0x930#64) v ∗ memRegion (g.q + 0xa88#64) 8 ∗
    memRegion (g.q + 0xa90#64) 344 ∗ memRegion (g.q + 0xbf0#64) 128 ∗
    memRegion (g.q - 65536#64) (65536 - chainMerge3StackX)

def overDecChainFrame (g : OverDecG) (pfx : List (BitVec 8)) (v : SSGQ) : SepProp :=
  overPrevElemRest g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗ (g.encPtr ↦ₛ pfx) ∗
    overDecChainRest A0 (g.q + 0x930#64) v ∗ memRegion (g.q + 0xa88#64) 8 ∗
    memRegion (g.q + 0xa90#64) 344 ∗ memRegion (g.q + 0xbf0#64) 128 ∗
    memRegion (g.q - 65536#64) (65536 - chainMerge3StackX) ∗ A0.pool

/-- Split the 64 KiB `overDecStackX` into the bottom region and `chainMerge3StackX`. -/
theorem overDecChain_stack_split (sp : BitVec 64) :
    stackAt sp overDecStackX =
      memRegion (sp - 65536#64) (65536 - chainMerge3StackX) ∗ stackAt sp chainMerge3StackX := by
  have h := ProofLib.stackAt_split_bottom sp chainMerge3StackX (65536 - chainMerge3StackX)
    (by rw [chainMerge3StackX_eq]; omega)
  rw [show chainMerge3StackX + (65536 - chainMerge3StackX) = overDecStackX by
    rw [chainMerge3StackX_eq]] at h
  rw [h]

/-- `(ptr ↦ₛ pfx)` and the cursor past `pfx` at the suffix `payload ++ rest`, advanced to `rest`,
recombine into the cursor over `pfx ++ (payload ++ rest)` advanced to `rest`. -/
theorem overDecChain_cursor_unsplit (slot ptr : BitVec 64) (pfx payload rest : List (BitVec 8)) :
    (ptr ↦ₛ pfx) ∗
        Prost.sliceCursorAfter slot (ptr + BitVec.ofNat 64 pfx.length) (payload ++ rest) rest =
      Prost.sliceCursorAfter slot ptr (pfx ++ (payload ++ rest)) rest := by
  unfold Prost.sliceCursorAfter
  have hlen : (pfx ++ (payload ++ rest)).length - rest.length = pfx.length + payload.length := by
    simp only [List.length_append]; omega
  have hlen2 : (payload ++ rest).length - rest.length = payload.length := by
    simp only [List.length_append]; omega
  rw [hlen, hlen2, BitVec.ofNat_add, ← BitVec.add_assoc,
    pointsToBytes_append ptr pfx (payload ++ rest)]
  ac_rfl

/-- Pre-call heap decomposition parameterized over `A : RustAlloc` (with `A.pool` in the active call heap). -/
theorem overDecChain_heap_pre_ext (A : RustAlloc) (g : OverDecG) (v : SSGQ)
    (pfx pay rest : List (BitVec 8))
    (hpfx : g.enc = pfx ++ (pay ++ rest)) (hnone : v.base.sender = none) :
    overDecHeapExt A g (pay ++ rest) v =
      ((g.q + 0x9c0#64) ↦₆₄ noneCap) ∗ memRegion (g.q + 0x9c8#64) 96 ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      Prost.sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length) (pay ++ rest) ∗
      A.pool ∗ stackAt g.q chainMerge3StackX ∗ overDecChainFrameExt A g pfx v := by
  have h90 : g.q + 0x930#64 + 0x90#64 = g.q + 0x9c0#64 := by rw [BitVec.add_assoc]; rfl
  have h98 : g.q + 0x930#64 + 0x98#64 = g.q + 0x9c8#64 := by rw [BitVec.add_assoc]; rfl
  unfold overDecHeapExt overDecChainFrameExt
  rw [overDecChain_split_none A (g.q + 0x930#64) v hnone, h90, h98, overDecChain_stack_split]
  have hcur := CryptoVerification.E2E.Record.DeserializeSeed.sliceCursorAfter_append_eq_seedChain
    (g.q + 0x920#64) g.encPtr pfx (pay ++ rest)
  rw [← hpfx] at hcur
  rw [hcur]
  ac_rfl

theorem overDecChain_heap_pre (g : OverDecG) (v : SSGQ) (pfx pay rest : List (BitVec 8))
    (hpfx : g.enc = pfx ++ (pay ++ rest)) (hnone : v.base.sender = none) :
    overDecHeap g (pay ++ rest) v =
      ((g.q + 0x9c0#64) ↦₆₄ noneCap) ∗ memRegion (g.q + 0x9c8#64) 96 ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      Prost.sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length) (pay ++ rest) ∗
      stackAt g.q chainMerge3StackX ∗ overDecChainFrame g pfx v := by
  have h90 : g.q + 0x930#64 + 0x90#64 = g.q + 0x9c0#64 := by rw [BitVec.add_assoc]; rfl
  have h98 : g.q + 0x930#64 + 0x98#64 = g.q + 0x9c8#64 := by rw [BitVec.add_assoc]; rfl
  unfold overDecHeap overDecHeapExt overDecChainFrame overPrevElemRest
  rw [overDecChain_split_none A0 (g.q + 0x930#64) v hnone, h90, h98, overDecChain_stack_split]
  have hcur := CryptoVerification.E2E.Record.DeserializeSeed.sliceCursorAfter_append_eq_seedChain
    (g.q + 0x920#64) g.encPtr pfx (pay ++ rest)
  rw [← hpfx] at hcur
  rw [hcur]
  ac_rfl

/-- Post-call heap recombination parameterized over `A : RustAlloc` (with `A.pool` in the active call heap). -/
theorem overDecChain_heap_post_ext (A : RustAlloc) (g : OverDecG) (v : SSGQ) (c : ChainG)
    (pfx pay rest : List (BitVec 8))
    (hpfx : g.enc = pfx ++ (pay ++ rest)) :
    prostChainGAt A (g.q + 0x9c0#64) c ∗ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      Prost.sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
        (pay ++ rest) rest ∗
      A.pool ∗ stackAt g.q chainMerge3StackX ∗ overDecChainFrameExt A g pfx v =
    overDecHeapExt A g rest ⟨v.base.apply (.sender c), v.ext⟩ := by
  have h90 : g.q + 0x930#64 + 0x90#64 = g.q + 0x9c0#64 := by rw [BitVec.add_assoc]; rfl
  unfold overDecHeapExt overDecChainFrameExt
  rw [overDecChain_split_some A (g.q + 0x930#64) v c, h90, overDecChain_stack_split]
  have hcur := overDecChain_cursor_unsplit (g.q + 0x920#64) g.encPtr pfx pay rest
  rw [← hpfx] at hcur
  rw [← hcur]
  ac_rfl

theorem overDecChain_heap_post (g : OverDecG) (v : SSGQ) (c : ChainG) (pfx pay rest : List (BitVec 8))
    (hpfx : g.enc = pfx ++ (pay ++ rest)) :
    prostChainGAt A0 (g.q + 0x9c0#64) c ∗ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      Prost.sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
        (pay ++ rest) rest ∗
      stackAt g.q chainMerge3StackX ∗ overDecChainFrame g pfx v =
    overDecHeap g rest ⟨v.base.apply (.sender c), v.ext⟩ := by
  have h90 : g.q + 0x930#64 + 0x90#64 = g.q + 0x9c0#64 := by rw [BitVec.add_assoc]; rfl
  unfold overDecHeap overDecHeapExt overDecChainFrame overPrevElemRest
  rw [overDecChain_split_some A0 (g.q + 0x930#64) v c, h90, overDecChain_stack_split]
  have hcur := overDecChain_cursor_unsplit (g.q + 0x920#64) g.encPtr pfx pay rest
  rw [← hpfx] at hcur
  rw [← hcur]
  ac_rfl

theorem overDecChain_mem96 (q : BitVec 64) :
    memRegion (q + 0x9c8#64) 96 =
      ∃∗ u9 : BitVec 64, ∃∗ u8 : BitVec 64, ∃∗ u7 : BitVec 64, ∃∗ u6 : BitVec 64,
        ∃∗ u5 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u3 : BitVec 64, ∃∗ u2 : BitVec 64,
        ∃∗ u1 : BitVec 64,
        ((q + 0x9c8#64) ↦₆₄ u1) ∗ ((q + 0x9d0#64) ↦₆₄ u2) ∗ ((q + 0x9d8#64) ↦₆₄ u3) ∗
        ((q + 0x9e0#64) ↦₆₄ u4) ∗ ((q + 0x9e8#64) ↦₆₄ u5) ∗ ((q + 0x9f0#64) ↦₆₄ u6) ∗
        ((q + 0x9f8#64) ↦₆₄ u7) ∗ ((q + 0xa00#64) ↦₆₄ u8) ∗ ((q + 0xa08#64) ↦₆₄ u9) ∗
        memRegion (q + 0xa10#64) 24 := by
  have h := CryptoVerification.E2E.Record.DeserializeSeed.memRegion96_sender_split_senderChain
    (q + 0x930#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  rw [h]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem overDecChain_bridge_ext (A : RustAlloc) (q : BitVec 64) :
    ((q + 0x9c0#64) ↦₆₄ 0#64) ∗ ((q + 0x9c8#64) ↦₆₄ 1#64) ∗ ((q + 0x9d0#64) ↦₆₄ 0#64) ∗
    ((q + 0x9d8#64) ↦₆₄ 0#64) ∗ ((q + 0x9e0#64) ↦₆₄ 1#64) ∗ ((q + 0x9e8#64) ↦₆₄ 0#64) ∗
    ((q + 0x9f0#64) ↦₆₄ 0#64) ∗ ((q + 0x9f8#64) ↦₆₄ 8#64) ∗ ((q + 0xa00#64) ↦₆₄ 0#64) ∗
    ((q + 0xa08#64) ↦₆₄ noneCap) ∗ memRegion (q + 0xa10#64) 24 ⊢
      chain3GAt A (q + 0x9c0#64) ChainG.empty := by
  have h := default_cells_entail_chain3GAt A
    (q + 0x9c0#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  exact h

theorem overDecChain_bridge (q : BitVec 64) :
    ((q + 0x9c0#64) ↦₆₄ 0#64) ∗ ((q + 0x9c8#64) ↦₆₄ 1#64) ∗ ((q + 0x9d0#64) ↦₆₄ 0#64) ∗
    ((q + 0x9d8#64) ↦₆₄ 0#64) ∗ ((q + 0x9e0#64) ↦₆₄ 1#64) ∗ ((q + 0x9e8#64) ↦₆₄ 0#64) ∗
    ((q + 0x9f0#64) ↦₆₄ 0#64) ∗ ((q + 0x9f8#64) ↦₆₄ 8#64) ∗ ((q + 0xa00#64) ↦₆₄ 0#64) ∗
    ((q + 0xa08#64) ↦₆₄ noneCap) ∗ memRegion (q + 0xa10#64) 24 ⊢
      chain3GAt A0 (q + 0x9c0#64) ChainG.empty :=
  overDecChain_bridge_ext A0 q

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
