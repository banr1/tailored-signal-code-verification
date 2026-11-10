/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsShaRows
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Synthetic.Witnesses.EvictedChainSkippedKeyCli

/-!
# Concrete Witness Interpretation `evictedI0` and Pinned `fits` Predicate

Defines the table-driven `ExternInterpretation` `evictedI0`, matching CLI hooks `evictedHooks0`,
setup records `evictedRecordsI0`, concrete opaque semantics `evictedSem0`, and
`evictedCompFitsPinned` for `EvictedChainSkippedKeyCli`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0

open CryptoProofLib.Refinement (ExternInterpretation ByteString)
open DY.X25519 (isLowOrderKey uCoord)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement
  (StubSymbol x25519PublicKeySymbol x25519AgreementSymbol x25519TorsionSymbol
   aesCbcEncryptSymbol aesCbcDecryptSymbol sha256CompressSymbol sha256CompressFunction)
open DY.Libsignal.PQXDH.Refinement
  (kyberEncapsSymbol kyberDecapsSymbol toEdwardsSymbol torsionFreeSymbol
   mlkem768Encaps1Symbol libcruxHmacSymbol X25519TorsionShiftsRejected)
open DY.Libsignal.Composed.Refinement (ProtocolSetup OpaqueSymbolSemantics gamma leBytes secretBytes)
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli HooksMatchInterpretation)
open CryptoVerification.SignalSession (CliHooks)
open Symbolic.BugInjection (PQXDHSpqrSetup TorsionShiftsRecorded compFits cliCompShape fillFresh)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
  (bytesToNat compTag4 compDefaultPub compDefaultDh compDefaultSha256 compDefaultHmac
   compDefaultKyberCt compDefaultKyberSs compKyberEncaps compKyberDecaps
   compToEdwards compTorsionFree compHmac compOtherExtern compMlkem768FromSeed
   compSha512 compEdwardsCompress compEdwardsNeg compDoubleScalarMul
   compScalarModOrder compScalarModOrderWide)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (bytesToSha512StateLE)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws
  (compMlKem0 compBcmp0 compBcmp0_ok compKyberEncaps_length compKyberDecaps_length compToEdwards_length)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsShaRows (evictedSha256)
open Symbolic.Swarm.CREF (compSemOf)

/-- The 16 recorded X25519 public keys indexed by `Fin 16`. -/
def evictedPubOfIdx (i : Fin 16) : HwBytes :=
  match i.val with
  | 0 => leBytes 32 0x3c01432d659f6956d79efdb84cf363bd3effef89cb39f4513184d598b479f75a
  | 1 => leBytes 32 0x627fac8bff0348b0c032b515e585e882aa28244c58ceadfb6f2c8876f3506df7
  | 2 => leBytes 32 0x1814e39f6c4912ea4cff03837272d451a1ac17771cbf3a0572c2e6bc9688b8b6
  | 3 => leBytes 32 0x4dc349100e5b5e487b92852d337badcba1b1139305b83213f7868f2c4f90bbab
  | 4 => leBytes 32 0x3fd3bf370a6f0d82bce23a6bc81073a3968030a12fd4407213598fb0a385fc5b
  | 5 => leBytes 32 0x4a0f460fe301182fc1f6649d265293f6015b9d019228dea3dd6c6dab69c19b00
  | 6 => leBytes 32 0x31a193d2d1dc63dd261d38fbf84e92cb27fedda510a9f301e2e9f33292755d8b
  | 7 => leBytes 32 0x2d1ef979d09ad8d12aaf718716a3749d3f803d4692788d23f063c6eac5c77d9b
  | 8 => leBytes 32 0x5c65bf5107c81941152795f6dd56dfb6209c462f5b5f1d21a44e96e24cece8f4
  | 9 => leBytes 32 0x7c0e10b00809707b115a4c64e94f790efbe4807883c50d7ef7e577808154bbea
  | 10 => leBytes 32 0x18afcd3b2c45a6e31513c147125cebd8d36c51224a16162a08e1133ddb4adde7
  | 11 => leBytes 32 0x749b1fbb508f1add1ef2300ed875e28b197eed8a81275c1e88eaf963c2e6c0ae
  | 12 => leBytes 32 0x775b26c0639d006eeee088cf6ce8a4c11e608beea345328b0e3018913401068b
  | 13 => leBytes 32 0x1dfa6a8312923fc0a5dea23acd80e95ab1ab9034286f199aba42da1f4d4b0c93
  | 14 => leBytes 32 0x4b52caeff9817db663605252f70d8c479b7c027de60916a16d63da853be8e423
  | _ => leBytes 32 0x4cac1f601c3e378f9354e009959e2521abb842c84b16e2865c5234d3a4dc5ccc

def evictedPubOfOpt : Option (Fin 16) → HwBytes
  | some idx => evictedPubOfIdx idx
  | none => compDefaultPub

/-- Normalize a 32-byte clamped secret `s` to its `Fin 16` table index. -/
def evictedSecretIdx (s : HwBytes) : Option (Fin 16) :=
  if s.length == 32 then
    let n := bytesToNat s
    if n == 0x65385b1d0d73750ca8125bca3c7e3bf70682a12a5e17055929b1566240215318 then some ⟨0, by decide⟩
    else if n == 0x5e9c4282ed6763a8c28ebb7233e51d1950937b3041d5d4ac13ac2650f5f8df00 then some ⟨1, by decide⟩
    else if n == 0x6385622579df091d9039fcd19c5dd34f7a2af4f99132c5932ff0a06b4bd52080 then some ⟨2, by decide⟩
    else if n == 0x5ebeb27d522a4e8b1b9ec6ebbda97281992ffac69a7acd4c118e846ea93bc948 then some ⟨3, by decide⟩
    else if n == 0x66964f30e299608354c3ce2401e61e48206f8f36b8468efae8fb77c019042648 then some ⟨4, by decide⟩
    else if n == 0x57904732f1bc41dd3191d85cef29f61ab333f1de246c0abcddcea107072d8550 then some ⟨5, by decide⟩
    else if n == 0x58baa6d6b82ec49a37fe1082ccf397e5d48f29e208dffc4beb01bffe1aa79950 then some ⟨6, by decide⟩
    else if n == 0x7599def579678f793d17bfa4d0db9d626035fccdadd3d8e4759b35eaf6c2da08 then some ⟨7, by decide⟩
    else if n == 0x6ca66941f779b6dfd783e5be92f36f357a2c0df73dba180da59759d7ac7ee8a8 then some ⟨8, by decide⟩
    else if n == 0x7ab96faeb8bb35f4df5632246358c5e535a3cd3e82f2d20485fd23477fd7a348 then some ⟨9, by decide⟩
    else if n == 0x44fee0c5fe38fe45d19634e04d985437210dddca13203719935c91bf9f1e4698 then some ⟨10, by decide⟩
    else if n == 0x7158c9d0ee929e19955f3885cbc39b16521866c8710ca1293668f94ac25d1ef8 then some ⟨11, by decide⟩
    else if n == 0x64f3d1f254b205c98b0f68af93eb3bab2c0cea6681f44bd72d39ecee087f99e8 then some ⟨12, by decide⟩
    else if n == 0x5091e46c8a462fafa36f7cd4701d28a9af37bdd2ec8556c2efaeba78adf3fe10 then some ⟨13, by decide⟩
    else if n == 0x51f6004c25efd78deca62602331a243772cbd56f6f37b952d8721c97b87fefe8 then some ⟨14, by decide⟩
    else if n == 0x66e22059750f93dd3088c0266cc3be301c13adb2a7842c190c7fc19c19164668 then some ⟨15, by decide⟩
    else none
  else none

/-- Map a 255-bit Montgomery `uCoord` to its `Fin 16` key index. -/
def evictedPointIdxOfU (u : Nat) : Option (Fin 16) :=
  if u == 0x3c01432d659f6956d79efdb84cf363bd3effef89cb39f4513184d598b479f75a then some ⟨0, by decide⟩
  else if u == 0x627fac8bff0348b0c032b515e585e882aa28244c58ceadfb6f2c8876f3506df7 then some ⟨1, by decide⟩
  else if u == 0x1814e39f6c4912ea4cff03837272d451a1ac17771cbf3a0572c2e6bc9688b8b6 then some ⟨2, by decide⟩
  else if u == 0x4dc349100e5b5e487b92852d337badcba1b1139305b83213f7868f2c4f90bbab then some ⟨3, by decide⟩
  else if u == 0x3fd3bf370a6f0d82bce23a6bc81073a3968030a12fd4407213598fb0a385fc5b then some ⟨4, by decide⟩
  else if u == 0x4a0f460fe301182fc1f6649d265293f6015b9d019228dea3dd6c6dab69c19b00 then some ⟨5, by decide⟩
  else if u == 0x31a193d2d1dc63dd261d38fbf84e92cb27fedda510a9f301e2e9f33292755d8b then some ⟨6, by decide⟩
  else if u == 0x2d1ef979d09ad8d12aaf718716a3749d3f803d4692788d23f063c6eac5c77d9b then some ⟨7, by decide⟩
  else if u == 0x5c65bf5107c81941152795f6dd56dfb6209c462f5b5f1d21a44e96e24cece8f4 then some ⟨8, by decide⟩
  else if u == 0x7c0e10b00809707b115a4c64e94f790efbe4807883c50d7ef7e577808154bbea then some ⟨9, by decide⟩
  else if u == 0x18afcd3b2c45a6e31513c147125cebd8d36c51224a16162a08e1133ddb4adde7 then some ⟨10, by decide⟩
  else if u == 0x749b1fbb508f1add1ef2300ed875e28b197eed8a81275c1e88eaf963c2e6c0ae then some ⟨11, by decide⟩
  else if u == 0x775b26c0639d006eeee088cf6ce8a4c11e608beea345328b0e3018913401068b then some ⟨12, by decide⟩
  else if u == 0x1dfa6a8312923fc0a5dea23acd80e95ab1ab9034286f199aba42da1f4d4b0c93 then some ⟨13, by decide⟩
  else if u == 0x4b52caeff9817db663605252f70d8c479b7c027de60916a16d63da853be8e423 then some ⟨14, by decide⟩
  else if u == 0x4cac1f601c3e378f9354e009959e2521abb842c84b16e2865c5234d3a4dc5ccc then some ⟨15, by decide⟩
  else none

/-- Normalize a 32-byte public key point `p` to its `Fin 16` index via `uCoord`. -/
def evictedPointIdx (p : HwBytes) : Option (Fin 16) :=
  if p.length == 32 then evictedPointIdxOfU (uCoord (p.map BitVec.toNat))
  else none

/-- Symmetric X25519 agreement table on `Fin 16 × Fin 16` (15 recorded pairs). -/
def evictedDhByIdx (i j : Fin 16) : HwBytes :=
  let lo := min i.val j.val
  let hi := max i.val j.val
  if lo == 0 && hi == 2 then leBytes 32 0x2b1507edf1e8d4f38a3da9d3571b67ea7ee5b0606ab27e0c41dfd01e683e373b
  else if lo == 1 && hi == 3 then leBytes 32 0x54151271fa3dd6f78b354f259b6c06bad17e64fc6967b26f10367cff0436cdf3
  else if lo == 2 && hi == 3 then leBytes 32 0x6b77c765b6556603b9ce3789d8135f9f017ce167088d37af655befa4f2f390e3
  else if lo == 2 && hi == 4 then leBytes 32 0x863177d59a538caa707d477ef3bc0bcd29ddbc0055aeeedb3b5795a24d424bf
  else if lo == 4 && hi == 5 then leBytes 32 0x41390a6cf70bb8d460044b93018074710b15249a39767762e2b75f3dd3ab9568
  else if lo == 5 && hi == 6 then leBytes 32 0x7f6433f90c337ddbdacc5bc54e3c34e5da67180473c9b79250e4edeb2a3458b2
  else if lo == 6 && hi == 7 then leBytes 32 0x5811d89c4ad6e354fcab640b7bc8fe5d68931588be9ae51875dc61c36042a626
  else if lo == 7 && hi == 8 then leBytes 32 0x43b238732f882e899e4b738c21319ad8e60d9f444db1e8e876927316d877710a
  else if lo == 8 && hi == 9 then leBytes 32 0x52d995fb26385523e560f835d70e2f7b0e66690b1a6f9f8b79c34dc6c47752fc
  else if lo == 9 && hi == 10 then leBytes 32 0x696a7eac3b5a47a4be92146ef5f0d9e47eb4b687b13780d6036e5a276378d071
  else if lo == 10 && hi == 11 then leBytes 32 0x7180fd6dc0c33559ce6a7316793f5db8e095857a94efcf7e58bb293e90e650c3
  else if lo == 11 && hi == 12 then leBytes 32 0x5e27ce73f659e204e82e81a0aed70d846c9181f13769c300c223cebf7ba13e9d
  else if lo == 12 && hi == 13 then leBytes 32 0x568ec81f3c0d5fcc7d973ae3ad34b34f68228b8191412bb078257ad99522ae5d
  else if lo == 13 && hi == 14 then leBytes 32 0x2826019da073fd6342c5c9bfda08c7434190fa81fa858028e3920527ce29660
  else if lo == 14 && hi == 15 then leBytes 32 0x64ef8950d8cfad47b4f8a251f571586501657ae3326021448f4508a0bafceb81
  else compTag4 ++ [BitVec.ofNat 8 lo, BitVec.ofNat 8 hi] ++ List.replicate 26 0x42#8

def evictedLookupPub (s : HwBytes) : HwBytes :=
  evictedPubOfOpt (evictedSecretIdx s)

def evictedLookupDh (s p : HwBytes) : HwBytes :=
  if isLowOrderKey (p.map BitVec.toNat) then
    List.replicate 32 0#8
  else
    match evictedSecretIdx s, evictedPointIdx p with
    | some i, some j => evictedDhByIdx i j
    | _, _ => compDefaultDh

def evictedAesPt0 : HwBytes := leBytes 6 0x302d70696b73
def evictedAesK0 : HwBytes := leBytes 32 0x675cd8931fad91165aab9f19384fad036b91292bc99dd88b42fda26566aeaa51
def evictedAesIv0 : HwBytes := leBytes 16 0xb7ca7a35cbdbee763f0a1a89736fc326
def evictedAesCt0 : HwBytes := leBytes 16 0x9e7a06d29250e3a2674e9f20473de0bc
def evictedAesA0 : CryptoGames.CBC.Block := ByteSpecs.bytesToBlock (ByteSpecs.pkcs7Bytes (⟨evictedAesPt0, by decide⟩ : List.Vector (BitVec 8) 6)) ^^^ CryptoGames.CBC.bytesToBlock evictedAesIv0
def evictedAesB0 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock evictedAesCt0
def evictedAesPt1 : HwBytes := leBytes 6 0x312d74696e69
def evictedAesK1 : HwBytes := leBytes 32 0x5527185c0cd38c6eff3cc60e8b4d0acd619093627075c02d0b78932a5966e1c2
def evictedAesIv1 : HwBytes := leBytes 16 0x3b0f6fbbdc1ef4ed636649f26f973f5d
def evictedAesCt1 : HwBytes := leBytes 16 0xf9feb1107ca28e6604d0154a873bcc7b
def evictedAesA1 : CryptoGames.CBC.Block := ByteSpecs.bytesToBlock (ByteSpecs.pkcs7Bytes (⟨evictedAesPt1, by decide⟩ : List.Vector (BitVec 8) 6)) ^^^ CryptoGames.CBC.bytesToBlock evictedAesIv1
def evictedAesB1 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock evictedAesCt1
def evictedAesPt2 : HwBytes := leBytes 2 0x3062
def evictedAesK2 : HwBytes := leBytes 32 0xf25641a450e83c4cc140f5384578aa611572918e45dd0f1bdddd9b3fc1b724f1
def evictedAesIv2 : HwBytes := leBytes 16 0x664e21c6c9a89e094b77f8a65e996721
def evictedAesCt2 : HwBytes := leBytes 16 0xfdcc0bbccbdec4ddc06c5a664b77a806
def evictedAesA2 : CryptoGames.CBC.Block := ByteSpecs.bytesToBlock (ByteSpecs.pkcs7Bytes (⟨evictedAesPt2, by decide⟩ : List.Vector (BitVec 8) 2)) ^^^ CryptoGames.CBC.bytesToBlock evictedAesIv2
def evictedAesB2 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock evictedAesCt2
def evictedAesPt3 : HwBytes := leBytes 2 0x3161
def evictedAesK3 : HwBytes := leBytes 32 0x2d1621327e6adcbd5aa11ab84f6a517f46a819c7da99bff0cb99f95d96170b11
def evictedAesIv3 : HwBytes := leBytes 16 0x68be5dc8abe5e8f2ce34744a90863561
def evictedAesCt3 : HwBytes := leBytes 16 0x4b973d32db9f7ab99d68a15504d96361
def evictedAesA3 : CryptoGames.CBC.Block := ByteSpecs.bytesToBlock (ByteSpecs.pkcs7Bytes (⟨evictedAesPt3, by decide⟩ : List.Vector (BitVec 8) 2)) ^^^ CryptoGames.CBC.bytesToBlock evictedAesIv3
def evictedAesB3 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock evictedAesCt3
def evictedAesPt4 : HwBytes := leBytes 2 0x3162
def evictedAesK4 : HwBytes := leBytes 32 0x6f82a608a62ac14f40ef03f6fe445232cecc1e3e18a8b4fa92b809dcac11271e
def evictedAesIv4 : HwBytes := leBytes 16 0xa09e580519e20d1c374d3df0e40375d2
def evictedAesCt4 : HwBytes := leBytes 16 0x9e7737646ce8c7f18168443ed8470ba8
def evictedAesA4 : CryptoGames.CBC.Block := ByteSpecs.bytesToBlock (ByteSpecs.pkcs7Bytes (⟨evictedAesPt4, by decide⟩ : List.Vector (BitVec 8) 2)) ^^^ CryptoGames.CBC.bytesToBlock evictedAesIv4
def evictedAesB4 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock evictedAesCt4
def evictedAesPt5 : HwBytes := leBytes 2 0x3261
def evictedAesK5 : HwBytes := leBytes 32 0x59b1820b508235dba97b7aa09ac7c55f6c30c429d1270e85a4b6b3a7b7acc782
def evictedAesIv5 : HwBytes := leBytes 16 0xb84e2ddc47670f9cfa4d7849dadd7c97
def evictedAesCt5 : HwBytes := leBytes 16 0xf57d7fe0b54c4f64d06176c8f6922418
def evictedAesA5 : CryptoGames.CBC.Block := ByteSpecs.bytesToBlock (ByteSpecs.pkcs7Bytes (⟨evictedAesPt5, by decide⟩ : List.Vector (BitVec 8) 2)) ^^^ CryptoGames.CBC.bytesToBlock evictedAesIv5
def evictedAesB5 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock evictedAesCt5
def evictedAesPt6 : HwBytes := leBytes 2 0x3262
def evictedAesK6 : HwBytes := leBytes 32 0x10b487d19b2e5d4c2650ee3944536795c588cb2e454eabbd15fa82683906598e
def evictedAesIv6 : HwBytes := leBytes 16 0xbab0d3aeaf61fe7cf0d65ef7b21a1284
def evictedAesCt6 : HwBytes := leBytes 16 0x2628fa4ead2772a031ee2c12827c470b
def evictedAesA6 : CryptoGames.CBC.Block := ByteSpecs.bytesToBlock (ByteSpecs.pkcs7Bytes (⟨evictedAesPt6, by decide⟩ : List.Vector (BitVec 8) 2)) ^^^ CryptoGames.CBC.bytesToBlock evictedAesIv6
def evictedAesB6 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock evictedAesCt6
def evictedAesPt7 : HwBytes := leBytes 2 0x3361
def evictedAesK7 : HwBytes := leBytes 32 0xc08dc18a8ada3705d5da0ce13827c4bcffdef94b482d17bb1da69d5a8d6c5cb4
def evictedAesIv7 : HwBytes := leBytes 16 0x5eb7316e74190a0a3e396f599d58e60f
def evictedAesCt7 : HwBytes := leBytes 16 0xe70d92781494b24f411dea4940f4eae
def evictedAesA7 : CryptoGames.CBC.Block := ByteSpecs.bytesToBlock (ByteSpecs.pkcs7Bytes (⟨evictedAesPt7, by decide⟩ : List.Vector (BitVec 8) 2)) ^^^ CryptoGames.CBC.bytesToBlock evictedAesIv7
def evictedAesB7 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock evictedAesCt7
def evictedAesPt8 : HwBytes := leBytes 2 0x3362
def evictedAesK8 : HwBytes := leBytes 32 0xe217355f6736d5f1b780309a43cf152e30256badb012c8a7c9f08ae2048efb6d
def evictedAesIv8 : HwBytes := leBytes 16 0x99771ac0efe2695b55dcbda6f9dfb3dc
def evictedAesCt8 : HwBytes := leBytes 16 0xa7f77227b21364bb198d1edfdbe9a650
def evictedAesA8 : CryptoGames.CBC.Block := ByteSpecs.bytesToBlock (ByteSpecs.pkcs7Bytes (⟨evictedAesPt8, by decide⟩ : List.Vector (BitVec 8) 2)) ^^^ CryptoGames.CBC.bytesToBlock evictedAesIv8
def evictedAesB8 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock evictedAesCt8
def evictedAesPt9 : HwBytes := leBytes 2 0x3461
def evictedAesK9 : HwBytes := leBytes 32 0x33b683f4b990ea9e075442d0a31b3caf180800193b9b125f02ca196645e5a964
def evictedAesIv9 : HwBytes := leBytes 16 0xf7e8f17e3f50fa4ba5a7216149c73761
def evictedAesCt9 : HwBytes := leBytes 16 0xbff3bca9a5306b51806be1bd6aebba95
def evictedAesA9 : CryptoGames.CBC.Block := ByteSpecs.bytesToBlock (ByteSpecs.pkcs7Bytes (⟨evictedAesPt9, by decide⟩ : List.Vector (BitVec 8) 2)) ^^^ CryptoGames.CBC.bytesToBlock evictedAesIv9
def evictedAesB9 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock evictedAesCt9
def evictedAesPt10 : HwBytes := leBytes 2 0x3462
def evictedAesK10 : HwBytes := leBytes 32 0xf96ea79dc5e7f4fc6d7f9f77aa3e9988a614b0b86d03e256c9c23cedf94fcd46
def evictedAesIv10 : HwBytes := leBytes 16 0xef1f0cb409787cd9a73692d96b698b28
def evictedAesCt10 : HwBytes := leBytes 16 0x5c745640e7705f59a9d0c29d3c20dc14
def evictedAesA10 : CryptoGames.CBC.Block := ByteSpecs.bytesToBlock (ByteSpecs.pkcs7Bytes (⟨evictedAesPt10, by decide⟩ : List.Vector (BitVec 8) 2)) ^^^ CryptoGames.CBC.bytesToBlock evictedAesIv10
def evictedAesB10 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock evictedAesCt10
def evictedAesPt11 : HwBytes := leBytes 2 0x3561
def evictedAesK11 : HwBytes := leBytes 32 0x6a705bc9080d34468cdcc972167519bf8f7b327be599a7e4283a9b09aa7b71f2
def evictedAesIv11 : HwBytes := leBytes 16 0xa9f0fdac924b8fac4f50df4d4cef770e
def evictedAesCt11 : HwBytes := leBytes 16 0xfb9c9e92acaab885fdeb9de32cf6f207
def evictedAesA11 : CryptoGames.CBC.Block := ByteSpecs.bytesToBlock (ByteSpecs.pkcs7Bytes (⟨evictedAesPt11, by decide⟩ : List.Vector (BitVec 8) 2)) ^^^ CryptoGames.CBC.bytesToBlock evictedAesIv11
def evictedAesB11 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock evictedAesCt11

/-- Involutive AES-256 block cipher swapping `(evictedAesA_m, evictedAesB_m)` on `evictedAesK_m`. -/
def evictedAesBlock (k : CryptoGames.CBC.AesKey) (b : CryptoGames.CBC.Block) : CryptoGames.CBC.Block :=
  if k == CryptoGames.HKDF.bytesToKey32 evictedAesK0 then
    if b == evictedAesA0 then evictedAesB0 else if b == evictedAesB0 then evictedAesA0 else b
  else if k == CryptoGames.HKDF.bytesToKey32 evictedAesK1 then
    if b == evictedAesA1 then evictedAesB1 else if b == evictedAesB1 then evictedAesA1 else b
  else if k == CryptoGames.HKDF.bytesToKey32 evictedAesK2 then
    if b == evictedAesA2 then evictedAesB2 else if b == evictedAesB2 then evictedAesA2 else b
  else if k == CryptoGames.HKDF.bytesToKey32 evictedAesK3 then
    if b == evictedAesA3 then evictedAesB3 else if b == evictedAesB3 then evictedAesA3 else b
  else if k == CryptoGames.HKDF.bytesToKey32 evictedAesK4 then
    if b == evictedAesA4 then evictedAesB4 else if b == evictedAesB4 then evictedAesA4 else b
  else if k == CryptoGames.HKDF.bytesToKey32 evictedAesK5 then
    if b == evictedAesA5 then evictedAesB5 else if b == evictedAesB5 then evictedAesA5 else b
  else if k == CryptoGames.HKDF.bytesToKey32 evictedAesK6 then
    if b == evictedAesA6 then evictedAesB6 else if b == evictedAesB6 then evictedAesA6 else b
  else if k == CryptoGames.HKDF.bytesToKey32 evictedAesK7 then
    if b == evictedAesA7 then evictedAesB7 else if b == evictedAesB7 then evictedAesA7 else b
  else if k == CryptoGames.HKDF.bytesToKey32 evictedAesK8 then
    if b == evictedAesA8 then evictedAesB8 else if b == evictedAesB8 then evictedAesA8 else b
  else if k == CryptoGames.HKDF.bytesToKey32 evictedAesK9 then
    if b == evictedAesA9 then evictedAesB9 else if b == evictedAesB9 then evictedAesA9 else b
  else if k == CryptoGames.HKDF.bytesToKey32 evictedAesK10 then
    if b == evictedAesA10 then evictedAesB10 else if b == evictedAesB10 then evictedAesA10 else b
  else if k == CryptoGames.HKDF.bytesToKey32 evictedAesK11 then
    if b == evictedAesA11 then evictedAesB11 else if b == evictedAesB11 then evictedAesA11 else b
  else b

def evictedAesPerm (k iv text : HwBytes) : HwBytes :=
  CryptoGames.LibsignalSession.aesCbcEncrypt evictedAesBlock (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) text

def evictedAesDec (k iv ct : HwBytes) : Option HwBytes :=
  CryptoGames.LibsignalSession.aesCbcDecrypt evictedAesBlock (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) ct

/-- Recorded `mlkem768Encaps1` output for call 5 (`bob send`). -/
def evictedMlkemEnc1Out : HwBytes := leBytes 960 0x2567a3ac96fb37e3f7e4abd8d76606e0d70f8a28ea52d211faffe89af954662c0d9bc7bad5950aff8ec97c9ef6044402ecab2d868a501c770af2d4e03acb418c6c27b48ffbaf14ec6a1131266970fac4eaa9ad7a9331ed7d214dc5a96ec79cbcaf379ba45d4a736561d9abafcc754698670954f1af1db97af1063e3ea730408554fc76fb06a6d94e219d5bdc2cae60121195a1fefb4346d5a534ee42827862bb1c111d6631250903395ed675d52b97eb1bcc12f4d6ffa62b53b4428f28f4a4cca60b0a5fd7a80a3d6da4f9decd811a4cbccc362581071bc156dabd75f548c5e901b0dc76a7aa54848c63c4bf28306f75243ac60848c497e456c2bdc3a9a4a500d64e851d3c4b3dfa5e565e0735e845d5ffbd4466e0bd50b5651ed3fc70020a5dec56b84e83c4db81bc59d5641735d88dcad97349d0d4859a6dfd408d73bfff12db5dab078766f94a2bf0decbbd0dec7c9ef37002b3861f1dcfc026076bc903401b3df13e1f7612f7fe5550db64d93d9567a7d8c6f7a60b843be25c2c2f6c44a286245d87d1586b3353593f4d46c4015365306654b061c4ac8b712ac9f7eeb7a881ab0f2f20500dbe8ea2ed3e3b99166856ad5eb0861732e787b3f458e46542a0e02e90dff8c1e7ac3922a1a052cf99b0af98872d4f31e350d94cd9cd1cd65682e187a2bca63516a263c18bb5cc5cd96e0fc693652445f076879a1fca2cd03ff37c95f3747c3c8d5c90c9a77e1b642e7f2424df6df64042a53ef3b4275a563b5dbb74ef48d826ca575e76fde5d93f584e557c746583450b2a9c1fe38c0de20fb1882238475380201a6b8f4caf1be5156e9dbd5348a5d9cf0198b0d7a6763d89fa7b605102486ca9cb075a22a7089d07d7ca8844e9f139bca09ed0880cce44b631c65baf37b137448d4c216fbd961ba1a70bafd4fcecb2bf098ccbf1addcc6f4f220a0f74c4746479381fa988cab717cd5c6384c6cdef9ec74a9f23b19c98c94e7817102f7a0a7799e20fa27981f29d3bf7cd0cbd6cc45125ee49eb6acc238beee88e6bed96c4b9b5f1178f4cd3f4ff2424f4e5d9d37c4ead305e0fc0b3700fdf2df142b6002a63da917756a0196e7b4fffdac50cdb81617962c76a533e59da8fa5071f5ea060d9d8ca4f81c2b85d68d9354e4fe4e01b0194a44ee8f8bab878a8e5e20c787c364ef1446965937b9048e2353a8351cf5501cf08ed7605448aad5526d80397be9e5f5cdc86dd98705d2df571d741d5bd2dcfdbcac4ceaecbe00229c2cfb2ff7515829ba7499224eb40a86f06cf8849edc9e2bd774b4fd36deb765cf93ee525d1fcb1bbca1f02e6b6a038245b0adf6dd7f99d3c10d49b7479be4f5b6 ++ leBytes 2080 0x199c171ed842fe6110a0964c66c7b8937371c59c4621db0fb7c79d64651732bfffffffe0000ffffffff00000001fffe00020000ffffffffffff00000000000000010000000000010000ffff00000002000000000000000100010001ffff0000ffff00000001fffffffeffff00000001ffff00000002ffff000000010001ffff0000000000000001000000010000fffe00010001000100000000ffff000100020001ffff00000000000100000001ffff00000000ffff000200010001ffff00000000ffff00010000000100000000fffe0001ffff0000ffff00010000000200010001ffff000100020000000200010001ffffffff00010000ffff000000000000000100000001000100010001ffff00000000fffe0000000000010001000100010001ffff0000ffff0000000000000000ffff0000ffff000100010000fffffffffffe0000ffffffffffffffff0000ffff00020002ffffffff0000ffffffff00010001fffffffefffffffe000000000002000000000000000000010002000100000000ffff0000fffe000000010001ffffffff0002ffff0001000000020000fffffffffffe00010000ffff0000000000000001000100020000fffffffeffff000000000000ffff00000000fffe000100000001000100010001ffff0000000200000000000000010000ffff000000010001000000000001000200000000ffff0002ffff00010000ffffffff000100000000fffffffe000000010001fffefffe0000fce4048305b504feff9104faff3efb1505c3fe6ffd34fdedfc99fff703fffff5030ffa21010b03f3fe0afd21fb7afdfcffa8fbb8faadff7604160044fded0485fa3f03adfb93014504c704ff058404c204cd04100426fdeefc4a02b0022d064404d7fd0304a2ffa0ff93fab8047c0030062e01a3036906320306ff860389fd2006620672fa3dfc4df99c03bd0348037afc54fc99014102fb05340152ffd5fffd002d0635fc1300ad03da00ce05b6ff0ffeb1050dfff3000505f60073fb450314f9dc0673fbaf0321ff54fa6cfcce00ecfe8ffb7605b3fc5b060c05fbfce7fc30006e04a4f988fc9f03c6ff3ffc7403fc0192fafd0584fd3a035002b3ffd903f900a1ffcffdcefafd00cfffcf00be0075052304f90360018705e3fc68ff8402620466044d0253fd630531ffb4feff0011fcb80393fcf9fe06fee105bcfadefc67fa30fbe905870397fe67fe4a04a5fe42fbe0ff4afb9cfe28060004d404b4fd37ffb903f1007d0220fd40fd2f0677fa0b0472fd8c011ffe99fe32fe3a0672fa70fe3a04aafd5302f9fd39041904cafbd5fb1bfe14fae4fbbd03cdfa3103d8ff1bfec7023ffbd9ff99fedd04b0ff2cfbe9fd38032f01540225053905f7fac9015affddfbe8003f06030593ff4d006affc6006c0580036904a6fc40feda02d0fe13fda30061fb3cf9a10383fbf00470fb39fe12fee1fcc0fe36fdec02ca05f5004ffee10615fbbafbb3fd4b00d40331059001450075fccdf9dc04adfd6dfdc8fae701c50492020c03bd0640039000aefc26016ffc96fc9502aeff4800f6fc450239fcfa01a0013804d10326ff43ff22040d05f1062a01d3fe38f9d004a50308033701040597034903c0fc78006bfd710369ffb40437fe7702f4032c02400051029dfca3ff12fb5d00ae01e20165fffcfa75fe92fc4f0329ff2efdbffdd8fa48fd9d0601011f04f501aa067005a5064efe5601e000f5fd75047f065604ba02e8feef015e01e4ff5bfcd7ffcbffe705ab0174fa0800aefd47035afa3cfc89fa55fdbf03830455fffff9e4fa3a062afe91fd4efa6401f8faab0256fff30496fd9b04410284049f002a014000b1fbd4050c04e10127fbeffe570055061d060afb7b017d0380fc1a023301e7fe3503a4038c00330187ff80fe85fecd02b801da0242062c03a804100356fb7bff340142006afb05fc9c023bfd1bfbb8039ffbdb042f00e504ad029dfc0b05bcfa75fcddfdec02def9f0059eff0c0325fbb2fa0101a403730568f9c300fa0612faa1fa06f9c6fd82fd570421f9faff54fa780477049fff4bfff005b4ff0efc2c052c00050139ff14fb010435fca6046301b6012ffc79ffd702750159008e007effad05b7fad2fc4801e3fa2dfa35067bff0a0545fa3d053903b0fcbcfaeffeb604da0416fcd40461027afd4c064ffa78fe15fcbd0540fbf9fa97fa67035705fffd1aff06006afaaffe76f9d6f98afd1001f1fb4cfcc1ffb40186fe2f003e04befc2bfcd8063205cfffd80038004101a300a70665ff330425fa93ffd2fcc603affb09002301a4030600690261fad6007201bf01cefa34fa2c044602ad044705b400b8ffa8ffd1030ffb64fcf8fbc4007ffa18043c04befd05fc60fa00fd7a02e9ffb200b6008cfe6dfc16f9e9fb6d0462015f05dffaeeff8900f8010bfb97fd13fb17fad8feecffe1039300ab063a04b4fe900367055a02260166ffbafab6fdf2f994ff20fc31fed201e5ffddff21fb77fd8afc2e0436fc5a0165fab7fc450266026effac03450426fb6a0617ffaf04cefd6cfa27fbfdfa480264fab3fed1009dfc47036c016efcbd02a6fbbffd1dfd92fa1eff57ff05046afdfd058c0374fbb5fc81fdd7ff5dfb650439fb3a042704c4fd64faa9ff47002a02aefc37fd69fc8df9d9ffe6024703350217fb76ff550552fe12fcf6fd8afb7bfd970238fbd7035cf998fbbafd00064ffff704a9049f02b60655fe7404f702defb3302d80084006d045d050dfda3fd68fce4017902170164063d035f00a2022bfaacfab1fdabfa1905f20071fe3bff69ffcb065c032d00e80622006cffedfac2fd5c018301f4fae7052bfbe6ff6202c6ffddfb33fda0067ffbf2008f02bf05d402eefd3e028805c002cb01f2ffd80525ff3001e9fb79fdcb02ad003efe59fad8 ++ leBytes 32 0x2fc9f1af03668a722ef219bfe5ee865647dcf1f0f9626bde082a3c6ab0858b19

def evictedMlkem768Encaps1 (hdr rnd : HwBytes) : HwBytes :=
  if hdr.length == 64 && rnd.length == 32 && bytesToNat hdr == 0x5ac2f4ce6d5b71c22b23d97cc15fd3dfd708a3bd1e6fbddc7d7cbb0b08bac6000b8cdd0fe997174ce780528bf9ecc13020f000fc44144b1638e063bc8c1218a5 && bytesToNat rnd == 0x199c171ed842fe6110a0964c66c7b8937371c59c4621db0fb7c79d64651732b then
    evictedMlkemEnc1Out
  else
    List.replicate 3072 0#8

def evictedI0 : ExternInterpretation :=
  fun s args =>
    if s = x25519PublicKeySymbol then
      match args with | [sk] => some (evictedLookupPub sk) | _ => none
    else if s = x25519AgreementSymbol then
      match args with | [sk, pk] => some (evictedLookupDh sk pk) | _ => none
    else if s = x25519TorsionSymbol then
      none
    else if s = aesCbcEncryptSymbol then
      match args with | [text, k, iv] => some (evictedAesPerm k iv text) | _ => none
    else if s = aesCbcDecryptSymbol then
      match args with | [ct, k, iv] => evictedAesDec k iv ct | _ => none
    else if s = kyberEncapsSymbol then
      match args with | [_, rand] => some (compKyberEncaps rand) | _ => some (compDefaultKyberCt ++ compDefaultKyberSs)
    else if s = kyberDecapsSymbol then
      match args with | [_, ct] => some (compKyberDecaps ct) | _ => some compDefaultKyberSs
    else if s = toEdwardsSymbol then
      match args with | [u, [sign]] => some (compToEdwards u sign) | _ => some (List.replicate 160 0#8)
    else if s = torsionFreeSymbol then
      match args with | [pt] => some (compTorsionFree pt) | _ => some [0#8]
    else if s = libcruxHmacSymbol then
      match args with | [k, d] => some (compHmac k d) | _ => some (compDefaultHmac [] [])
    else if s = sha256CompressSymbol then
      match args with | [st, blk] => some (evictedSha256 st blk) | _ => some (compDefaultSha256 [] [])
    else if s = mlkem768Encaps1Symbol then
      match args with | [hdr, rnd] => some (evictedMlkem768Encaps1 hdr rnd) | _ => some (List.replicate 3072 0#8)
    else
      compOtherExtern s args

theorem evictedPubOfIdx_length (i : Fin 16) : (evictedPubOfIdx i).length = 32 := by
  revert i; decide

theorem evictedLookupPub_length (s : HwBytes) : (evictedLookupPub s).length = 32 := by
  unfold evictedLookupPub evictedPubOfOpt
  cases evictedSecretIdx s with
  | none => decide
  | some idx => exact evictedPubOfIdx_length idx

theorem evictedDhByIdx_length (i j : Fin 16) : (evictedDhByIdx i j).length = 32 := by
  revert i j; decide

theorem evictedLookupDh_length (s p : HwBytes) : (evictedLookupDh s p).length = 32 := by
  unfold evictedLookupDh
  split
  · rfl
  · cases evictedSecretIdx s <;> cases evictedPointIdx p <;> dsimp only <;>
      first | exact evictedDhByIdx_length _ _ | decide

def evictedExecMlKem0 : CryptoVerification.LibsignalSpqrV1.MlKem :=
  { compMlKem0 with
    keyPair := fun seed => CryptoVerification.E2E.fitVec 2400 (compMlkem768FromSeed seed.toList)
    encaps1 := fun hdr rnd =>
      let out := evictedMlkem768Encaps1 hdr rnd.toList
      some (CryptoVerification.E2E.fitVec 960 (out.take 960),
            CryptoVerification.E2E.fitVec 2080 ((out.drop 960).take 2080),
            CryptoVerification.E2E.fitVec 32 (out.drop 3040)) }

def evictedHooks0 : CliHooks where
  C :=
    { F := sha256CompressFunction evictedI0
      E := evictedAesBlock
      D := evictedAesBlock
      X := fun a b => ⟨evictedLookupDh a.toList b.toList, evictedLookupDh_length a.toList b.toList⟩
      pubKey := fun a => ⟨evictedLookupPub a.toList, evictedLookupPub_length a.toList⟩ }
  Q :=
    { F512 := fun st blk =>
        bytesToSha512StateLE (compSha512 (CryptoVerification.E2E.sha512StateBytesLE st) blk)
      montToEd := fun u sign =>
        some ⟨compToEdwards u.toList sign, compToEdwards_length u.toList sign⟩
      compress := fun pt => CryptoVerification.E2E.fitVec 32 (compEdwardsCompress pt.toList)
      edNeg := fun pt => CryptoVerification.E2E.fitVec 160 (compEdwardsNeg pt.toList)
      isTorsionFree := fun pt => decide (compTorsionFree pt.toList = [1#8])
      dsmb := fun a pt b =>
        CryptoVerification.E2E.fitVec 160 (compDoubleScalarMul a.toList pt.toList b.toList)
      scalarMod := fun s => CryptoVerification.E2E.fitVec 32 (compScalarModOrder s.toList)
      scalarWide := fun w => CryptoVerification.E2E.fitVec 32 (compScalarModOrderWide w.toList)
      encaps := fun _ rand =>
        (⟨(compKyberEncaps rand.toList).take 1568, by
            rw [List.length_take, compKyberEncaps_length]; rfl⟩,
         ⟨(compKyberEncaps rand.toList).drop 1568, by
            rw [List.length_drop, compKyberEncaps_length]⟩)
      decaps := fun _ ct => ⟨compKyberDecaps ct.toList, compKyberDecaps_length ct.toList⟩
      K := evictedExecMlKem0 }
  bcmp := compBcmp0
  bcmp_ok := compBcmp0_ok
  utf8Err := fun _ => (0#64, 0#16)

def evictedRecordsI0 (w : PQXDHSpqrSetup) : ProtocolSetup :=
  { alice := "alice", bob := "bob", withOpk := false, regIdA := w.regIdA, regIdB := w.regIdB,
    spkId := w.spkId, kpkId := w.kpkId, opkId := 0, kyberSecB := w.kyberSec, fresh := w.fresh,
    opaqueBytes := gamma evictedI0 w.compSem w.compGhost }

def evictedSem0 : OpaqueSymbolSemantics :=
  compSemOf evictedI0 (evictedRecordsI0 Symbolic.BugInjection.Synthetic.Witnesses.EvictedChainSkippedKeyCli.setup)

/-- Strengthens `compFits` with `iw.1 = evictedI0`, fresh signing/KEM randomness, torsion-shift
laws, and CLI hook agreement. -/
def evictedCompFitsPinned (iw : cliCompShape.Interp) (r : ProtocolSetup) : Prop :=
  (compFits Symbolic.BugInjection.Synthetic.Witnesses.EvictedChainSkippedKeyCli.setup iw.1 r ∧
    iw.1 = evictedI0 ∧
    (secretBytes r 3 = fillFresh 11 64 ∧ secretBytes r 4 = fillFresh 16 64 ∧
      secretBytes r 5 = fillFresh 17 64) ∧
    (r.alice = "alice" ∧ r.bob = "bob") ∧
    X25519TorsionShiftsRejected iw.1 ∧
    TorsionShiftsRecorded iw.1
      Symbolic.BugInjection.Synthetic.Witnesses.EvictedChainSkippedKeyCli.setup.torsionShifts) ∧
  ExternContractsHoldCli iw.1 ∧
  HooksMatchInterpretation iw.1 iw.2

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
