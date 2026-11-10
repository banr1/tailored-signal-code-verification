/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement
public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Proofs.SpecLemmas.ByteSpecs
public import Symbolic.Proofs.SpecLemmas.ImageSymbolsProofDefs
public import Symbolic.Proofs.SpecLemmas.ExternInterpretationProofDefs
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatement
public import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
public import Symbolic.Proofs.Swarm.CREF.TRView

/-!
# Frozen Table-Driven Interpretation for Composed Witnesses

Defines the self-contained table-driven `ExternInterpretation` `compI0` under
`Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0`, covering X25519, AES-CBC, Kyber-1024,
Edwards/XEdDSA, ML-KEM-768, HMAC, SHA-256, and SHA-512 lookup tables with tagged off-table
defaults, together with refinement compatibility abbreviations.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0

open Symbolic.BugInjection
open CryptoProofLib.Refinement (ExternInterpretation ByteString)
open DY.X25519 (isLowOrderKey lowOrderUs uCoord leValue p25519)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (StubSymbol x25519PublicKeySymbol x25519AgreementSymbol x25519TorsionSymbol aesCbcEncryptSymbol aesCbcDecryptSymbol sha256CompressSymbol)
open DY.Libsignal.Composed.Refinement (leBytes)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol kyberDecapsSymbol sha512CompressSymbol toEdwardsSymbol edwardsCompressSymbol edwardsNegSymbol torsionFreeSymbol doubleScalarMulSymbol scalarModOrderSymbol scalarModOrderWideSymbol mlkem768FromSeedSymbol mlkem768Encaps1Symbol mlkem768Encaps2Symbol mlkem768DecapsSymbol mlkem768ValidatePkSymbol libcruxHmacSymbol)

/-- Little-endian `Nat` value of a byte string (inverse of `leBytes bs.length` on `bs`). -/
def bytesToNat : HwBytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * bytesToNat bs

/-- The 4-byte byte-symmetric tag `0xd7d7d7d7` (`reverse compTag4 = compTag4`). -/
def compTag4 : HwBytes := [0xd7#8, 0xd7#8, 0xd7#8, 0xd7#8]
def compTag4Ipad : HwBytes := [0xe1#8, 0xe1#8, 0xe1#8, 0xe1#8]
def compTag4Opad : HwBytes := [0x8b#8, 0x8b#8, 0x8b#8, 0x8b#8]

/-- 28-byte state-and-block XOR mix:
`(st.drop 4)[0..28) ⊕ blk[0..28) ⊕ blk[28..56) ⊕ (blk[56..64) ‖ 0²⁰)`. -/
def compShaMix28 (st blk : HwBytes) : HwBytes :=
  List.ofFn fun i : Fin 28 =>
    st.getD (i.val + 4) 0#8 ^^^ blk.getD i.val 0#8 ^^^ blk.getD (i.val + 28) 0#8 ^^^
    (if i.val < 8 then blk.getD (i.val + 56) 0#8 else 0#8)

def compDefaultSha256 (st blk : HwBytes) : HwBytes := compTag4 ++ compShaMix28 st blk

/-- 28-byte key-and-data XOR mix for `libcruxHmacSymbol`. -/
def compHmacMix28 (k d : HwBytes) : HwBytes :=
  List.ofFn fun i : Fin 28 =>
    k.getD i.val 0#8 ^^^
    (if i.val < 4 then k.getD (i.val + 28) 0#8 else 0#8) ^^^
    d.getD i.val 0#8 ^^^
    d.getD (i.val + 28) 0#8 ^^^
    d.getD (i.val + 56) 0#8 ^^^
    d.getD (i.val + 84) 0#8

/-- Off-table default for `libcruxHmacSymbol`: `compTag4 ‖ compHmacMix28 k d` (32 bytes). -/
def compDefaultHmac (k d : HwBytes) : HwBytes :=
  compTag4 ++ compHmacMix28 k d

/-- Default X25519 public key `Pd` (`u = 9`, canonical, not low-order, u-coordinate outside the 12
recorded keys and the torsion shift). -/
def compDefaultPub : HwBytes := leBytes 32 9

/-- Default X25519 shared secret `Gd` on off-table non-low-order pairs (32 bytes, nonzero,
tagged with `0xd7` in byte 0). -/
def compDefaultDh : HwBytes :=
  leBytes 32 0x715a9e3c4b2d8f1065c3a894e21b7d049a6f3c812e5d0b74c91a8e3f526b4cd7

/-- Alice's ephemeral public key `ekA_pub` (index 1 in the pub table). -/
def compEkAPub : HwBytes :=
  leBytes 32 0x4dc349100e5b5e487b92852d337badcba1b1139305b83213f7868f2c4f90bbab

/-- The 8-torsion-shifted ephemeral public key `ekA_torsion` in `Cheval26SmallSubgroupTorsionComp`. -/
def compEkATorsion : HwBytes :=
  leBytes 32 0x7a88b2f8abf8cf55bbf89780412fb7004b64bde0e16095c1234eddde08497135

/-- The 12 recorded X25519 public keys indexed by `Fin 12`. -/
def compPubOfIdx (i : Fin 12) : HwBytes :=
  match i.val with
  | 0 => leBytes 32 0x3c01432d659f6956d79efdb84cf363bd3effef89cb39f4513184d598b479f75a
  | 1 => leBytes 32 0x4dc349100e5b5e487b92852d337badcba1b1139305b83213f7868f2c4f90bbab
  | 2 => leBytes 32 0x3fd3bf370a6f0d82bce23a6bc81073a3968030a12fd4407213598fb0a385fc5b
  | 3 => leBytes 32 0x1814e39f6c4912ea4cff03837272d451a1ac17771cbf3a0572c2e6bc9688b8b6
  | 4 => leBytes 32 0x627fac8bff0348b0c032b515e585e882aa28244c58ceadfb6f2c8876f3506df7
  | 5 => leBytes 32 0xdf1b9cfdb6f1beecfab864aec3b00d301fabcf8efbdadae64b8f3ce0a70062a
  | 6 => leBytes 32 0x3876d0f225aa2d85682498e61e2fe97bc189e4815c96aee21e8218cf997b078f
  | 7 => leBytes 32 0x4ae020f0133ecd4a8abe6ff58f162cef8c18ef9d7411918dad639572eb5d1627
  | 8 => leBytes 32 0x72286eeb9c357cfe8e987def6eb01547ab213f371009d6008d514824f77f6845
  | 9 => leBytes 32 0x191933f5352eccec96182dee25cb6fc49f24128081a4b0215fcc626dfb5fa897
  | 10 => leBytes 32 0x403fe1f44d61222fa5fa45d5d75c73b9cf3bb9613445fbf0ec18d035609a9783
  | _ => leBytes 32 0x2d6b8af9c5741253c312f5863e6816d644b74e4125980fb1d878a17e71049637

def compPubOfOpt : Option (Fin 12) → HwBytes
  | some idx => compPubOfIdx idx
  | none => compDefaultPub

/-- Map a 32-byte secret key `s` to its `Fin 12` table index, or `none` if unrecorded. -/
def compSecretIdx (s : HwBytes) : Option (Fin 12) :=
  if s.length == 32 then
    let n := bytesToNat s
    if n == 0x65385b1d0d73750ca8125bca3c7e3bf70682a12a5e17055929b1566240215318 then some ⟨0, by decide⟩
    else if n == 0x5ebeb27d522a4e8b1b9ec6ebbda97281992ffac69a7acd4c118e846ea93bc948 then some ⟨1, by decide⟩
    else if n == 0x66964f30e299608354c3ce2401e61e48206f8f36b8468efae8fb77c019042648 then some ⟨2, by decide⟩
    else if n == 0x6385622579df091d9039fcd19c5dd34f7a2af4f99132c5932ff0a06b4bd52080 then some ⟨3, by decide⟩
    else if n == 0x5e9c4282ed6763a8c28ebb7233e51d1950937b3041d5d4ac13ac2650f5f8df00 then some ⟨4, by decide⟩
    else if n == 0x5c7f85979eaf14f7fb49936bd882f71348114868c9e6902973986d357f2a7e20 then some ⟨5, by decide⟩
    else if n == 0x549ffe504bfdab7f6ec624aa856858679cde98852e60034bba69ec90eb4fef88 then some ⟨6, by decide⟩
    else if n == 0x52461536c4ec47f2f627d8acad21a894997606a9f69e103e2b90d87b87062920 then some ⟨7, by decide⟩
    else if n == 0x6264601f3e57cc7b01d4d961486f4f76c69227f456ddcf04d2fe0ce30504f8b0 then some ⟨8, by decide⟩
    else if n == 0x7f62e60296fdfd995c0ef0e79e17027f62ee6dbfe35320b65c29f2075b719610 then some ⟨9, by decide⟩
    else if n == 0x640de9c22005555e9f5bc5f1de78c1a837ccef0b2752c025b10c76f4432be218 then some ⟨10, by decide⟩
    else if n == 0x73a8337d2e8afab34f706c15ac4bb27e43eefd6e2178cb07b9d9f3a798205660 then some ⟨11, by decide⟩
    else none
  else none

/-- Map a 255-bit Montgomery `uCoord` to its `Fin 12` key index (`uCoord compEkATorsion` maps to index 1). -/
def compPointIdxOfU (u : Nat) : Option (Fin 12) :=
  if u == 0x7a88b2f8abf8cf55bbf89780412fb7004b64bde0e16095c1234eddde08497135 then some ⟨1, by decide⟩
  else if u == 0x3c01432d659f6956d79efdb84cf363bd3effef89cb39f4513184d598b479f75a then some ⟨0, by decide⟩
  else if u == 0x4dc349100e5b5e487b92852d337badcba1b1139305b83213f7868f2c4f90bbab then some ⟨1, by decide⟩
  else if u == 0x3fd3bf370a6f0d82bce23a6bc81073a3968030a12fd4407213598fb0a385fc5b then some ⟨2, by decide⟩
  else if u == 0x1814e39f6c4912ea4cff03837272d451a1ac17771cbf3a0572c2e6bc9688b8b6 then some ⟨3, by decide⟩
  else if u == 0x627fac8bff0348b0c032b515e585e882aa28244c58ceadfb6f2c8876f3506df7 then some ⟨4, by decide⟩
  else if u == 0xdf1b9cfdb6f1beecfab864aec3b00d301fabcf8efbdadae64b8f3ce0a70062a then some ⟨5, by decide⟩
  else if u == 0x3876d0f225aa2d85682498e61e2fe97bc189e4815c96aee21e8218cf997b078f then some ⟨6, by decide⟩
  else if u == 0x4ae020f0133ecd4a8abe6ff58f162cef8c18ef9d7411918dad639572eb5d1627 then some ⟨7, by decide⟩
  else if u == 0x72286eeb9c357cfe8e987def6eb01547ab213f371009d6008d514824f77f6845 then some ⟨8, by decide⟩
  else if u == 0x191933f5352eccec96182dee25cb6fc49f24128081a4b0215fcc626dfb5fa897 then some ⟨9, by decide⟩
  else if u == 0x403fe1f44d61222fa5fa45d5d75c73b9cf3bb9613445fbf0ec18d035609a9783 then some ⟨10, by decide⟩
  else if u == 0x2d6b8af9c5741253c312f5863e6816d644b74e4125980fb1d878a17e71049637 then some ⟨11, by decide⟩
  else none

/-- Normalize a 32-byte public key point `p` to its `Fin 12` index via `uCoord` only. -/
def compPointIdx (p : HwBytes) : Option (Fin 12) :=
  if p.length == 32 then compPointIdxOfU (uCoord (p.map BitVec.toNat))
  else none

/-- Symmetric DH lookup on `Fin 12 × Fin 12` via `(min i.val j.val, max i.val j.val)`. -/
def compDhByIdx (i j : Fin 12) : HwBytes :=
  let lo := min i.val j.val
  let hi := max i.val j.val
  if lo == 0 && hi == 3 then leBytes 32 0x2b1507edf1e8d4f38a3da9d3571b67ea7ee5b0606ab27e0c41dfd01e683e373b
  else if lo == 1 && hi == 3 then leBytes 32 0x6b77c765b6556603b9ce3789d8135f9f017ce167088d37af655befa4f2f390e3
  else if lo == 1 && hi == 4 then leBytes 32 0x54151271fa3dd6f78b354f259b6c06bad17e64fc6967b26f10367cff0436cdf3
  else if lo == 2 && hi == 3 then leBytes 32 0x863177d59a538caa707d477ef3bc0bcd29ddbc0055aeeedb3b5795a24d424bf
  else if lo == 2 && hi == 5 then leBytes 32 0x1edc8f428b3201dcd6286cac92f8611914a3a83f06e9834a6b2a62b6889fc766
  else if lo == 3 && hi == 6 then leBytes 32 0x7707b1a8208d0492fce5307d23fe5b81e8943766928eb6d041f35cad4df47188
  else if lo == 3 && hi == 7 then leBytes 32 0x5188500b822d529fe65cfbc87e52c5607f92b09f3dc64254c47aed0d73c65ebc
  else if lo == 3 && hi == 9 then leBytes 32 0xd09069e4d2b6c6b8d7b7bb54701ce5b5394e941e2b5ee55f4e1aa70a3ccabc1
  else if lo == 3 && hi == 10 then leBytes 32 0x4f0afd7d659b52fae025b55d505736adc89928285fecd3039bbb03d943130441
  else if lo == 4 && hi == 6 then leBytes 32 0xa2243eb8bcdb7e8ea5b789c1e176f460f7589421241238bef591bd268baa0d8
  else if lo == 4 && hi == 9 then leBytes 32 0x32cd5b7e65b83b22788fc146ea032ea99a2d368cf12ef60abe24a50e429e4553
  else if lo == 7 && hi == 8 then leBytes 32 0x6405a2df8adffc0ad3751f0557dddbbecf6918b6de21da8a256c5def3434b187
  else if lo == 7 && hi == 11 then leBytes 32 0x71c9603a3a852133054ddc8f21ef2c9257ffd88c50067a9f45d18af019b3e30e
  else compDefaultDh

def compLookupPub (s : HwBytes) : HwBytes :=
  compPubOfOpt (compSecretIdx s)

/-- X25519 agreement lookup: returns 32 zero bytes on low-order public keys, otherwise dispatches
symmetrically on `(compSecretIdx s, compPointIdx p)`. -/
def compLookupDh (s p : HwBytes) : HwBytes :=
  if isLowOrderKey (p.map BitVec.toNat) then
    List.replicate 32 0#8
  else
    match compSecretIdx s, compPointIdx p with
    | some i, some j => compDhByIdx i j
    | _, _ => compDefaultDh

/-- X25519 8-torsion shift lookup: maps `(compEkAPub, 1#8)` to `some compEkATorsion` and all other
inputs to `none`. -/
def compLookupTorsion (point : HwBytes) (b : BitVec 8) : Option HwBytes :=
  if b = 1#8 then
    if point == compEkAPub then some compEkATorsion else none
  else none

def aesSwapPair (pt ct text : HwBytes) : HwBytes :=
  if text == pt then ct
  else if text == ct then pt
  else text

/-- Involutive byte-string map that XORs byte 0 with `0xd7#8` when non-empty. -/
def xorHeadD7 : HwBytes → HwBytes
  | [] => []
  | b :: bs => (b ^^^ 0xd7#8) :: bs

def compAesPt0 : HwBytes := leBytes 9 0x626f62206f6c6c6568
def compAesK0 : HwBytes := leBytes 32 0x675cd8931fad91165aab9f19384fad036b91292bc99dd88b42fda26566aeaa51
def compAesIv0 : HwBytes := leBytes 16 0xb7ca7a35cbdbee763f0a1a89736fc326
def compAesCt0 : HwBytes := leBytes 16 0x7c6c2aec8510f4291f9dd3397ce8a4fc
def compAesPt1 : HwBytes := leBytes 5 0x7473726966
def compAesK1 : HwBytes := leBytes 32 0xe69af03427530a580cc1538c3b3109974a21cbfb15fbee9290dd8ed3972a021a
def compAesIv1 : HwBytes := leBytes 16 0x8dcedd678ff7bac2d9aa71ff7de710a6
def compAesCt1 : HwBytes := leBytes 16 0xd153ffaca7b73d3f808747a77c58d1f6
def compAesPt2 : HwBytes := leBytes 6 0x646e6f636573
def compAesK2 : HwBytes := leBytes 32 0xefea580d415e61f45893902a1353934cd9cadd8208a53de83d8c98c530663bf1
def compAesIv2 : HwBytes := leBytes 16 0xc9fc50b91e8360214abf37e35caba679
def compAesCt2 : HwBytes := leBytes 16 0x884f40bdd047e18767282d49485b5ca0
def compAesPt3 : HwBytes := leBytes 5 0x726568746f
def compAesK3 : HwBytes := leBytes 32 0xdc524f6fed7b13b4898be28676ae1ee972cb7bfc2b16ba3f9e23867a771473f5
def compAesIv3 : HwBytes := leBytes 16 0xeb9176164f25d57578dc7fe7d02be9e1
def compAesCt3 : HwBytes := leBytes 16 0x2bd957f3dde6eae35954587a0a9333cf

def compAesA0 : CryptoGames.CBC.Block := ByteSpecs.bytesToBlock (ByteSpecs.pkcs7Bytes (⟨compAesPt0, by decide⟩ : List.Vector (BitVec 8) 9)) ^^^ CryptoGames.CBC.bytesToBlock compAesIv0
def compAesB0 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock compAesCt0
def compAesA1 : CryptoGames.CBC.Block := ByteSpecs.bytesToBlock (ByteSpecs.pkcs7Bytes (⟨compAesPt1, by decide⟩ : List.Vector (BitVec 8) 5)) ^^^ CryptoGames.CBC.bytesToBlock compAesIv1
def compAesB1 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock compAesCt1
def compAesA2 : CryptoGames.CBC.Block := ByteSpecs.bytesToBlock (ByteSpecs.pkcs7Bytes (⟨compAesPt2, by decide⟩ : List.Vector (BitVec 8) 6)) ^^^ CryptoGames.CBC.bytesToBlock compAesIv2
def compAesB2 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock compAesCt2
def compAesA3 : CryptoGames.CBC.Block := ByteSpecs.bytesToBlock (ByteSpecs.pkcs7Bytes (⟨compAesPt3, by decide⟩ : List.Vector (BitVec 8) 5)) ^^^ CryptoGames.CBC.bytesToBlock compAesIv3
def compAesB3 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock compAesCt3

def compAesBlock (k : CryptoGames.CBC.AesKey) (b : CryptoGames.CBC.Block) : CryptoGames.CBC.Block :=
  if k == CryptoGames.HKDF.bytesToKey32 compAesK0 then
    if b == compAesA0 then compAesB0 else if b == compAesB0 then compAesA0 else b
  else if k == CryptoGames.HKDF.bytesToKey32 compAesK1 then
    if b == compAesA1 then compAesB1 else if b == compAesB1 then compAesA1 else b
  else if k == CryptoGames.HKDF.bytesToKey32 compAesK2 then
    if b == compAesA2 then compAesB2 else if b == compAesB2 then compAesA2 else b
  else if k == CryptoGames.HKDF.bytesToKey32 compAesK3 then
    if b == compAesA3 then compAesB3 else if b == compAesB3 then compAesA3 else b
  else b

def compAesPerm (k iv text : HwBytes) : HwBytes :=
  CryptoGames.LibsignalSession.aesCbcEncrypt compAesBlock (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) text

def compAesDec (k iv ct : HwBytes) : Option HwBytes :=
  CryptoGames.LibsignalSession.aesCbcDecrypt compAesBlock (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) ct

/-- Default 1568-byte Kyber ciphertext off-table (starts with `0xd7#8`, distinct from all recorded cts). -/
def compDefaultKyberCt : HwBytes := List.replicate 1568 0xd7#8

/-- Default 32-byte Kyber shared secret off-table (starts with `0xd7#8`, distinct from all recorded sses). -/
def compDefaultKyberSs : HwBytes := List.replicate 32 0xd7#8

def compKyberE0 : HwBytes := leBytes 32 0x26dbbcc03fd18c061cfc083f071e14d5baf49d84843ffc43a4383b3212e60505
def compKyberCt0 : HwBytes := leBytes 1568 0xb42a96dfc7a8a6d25abee582e4b78cea7fadac372a1824a1e626760fe6ff6c9e34b2c6f03cb0501a903a303f516d73b2db2a00072963704437743abdce9db0dc84fd0ba040ec002e7baf168e128381ea90c450e953c86ccb291155d636cbd1b560de601ba52819dc2272f5e82e1fa3962fb32205351bc1ffdc5466b3db95ac329db4a737713a2b490456ae8fada2e9ba4550f9153fa011cc5d9cd2f0a3bf536fedf72c797f8f0582d2a1dd5cec9691a837e7d5f74e8993b8126331de8288bb54d6f29b2bd3ac0fc96ce62e013b07ea8cf6796c7b526ed61f4eadc6d9672a5c71b5b4d1e69d374456f3b914a23a0c58ddc2e0cfdb434ca164fa8928d637d9434e9f4a19a7d57785ee084ca2d9350115ec2a56fdfe5e6e4d36c992a9ff42598279e32cda1c5b345c77f6fcace6d3c05989c16443b0198a4430dd5f2201b6bc024ce4abf131369ed8e983942e19e39930ed26ed7c7461c962453cfa647e37c58b7a72730db8a5d60dd8a2a9afb3beb9bacf4657b7926aac6e524367ebee8716bcb68cace7e857b472fa59325e7df90a65f75ed132b5c410b80565daf1cbd26ef53ef459de28227ec0500ff994facb3e97925f187e902475c8b0b4deac39a887024e09c951dd07b1c8ec6f88b457144b6711f37789a0800cd689d2bbf117ca9302a01824d436c19bf7ca05c27d5ecb8d535098fcb6bcd1ec09d1fa58c0dc810cc9b53238d8d89ad152c4059e12095b07977a07b68006c97255d442475b5491d0497885d69dbcf3b1b4545c8e767e26e87f270d0aed90e54e267d0b4c48ca1090e437135bdaddea439d7d0fa04c446d4d45b5f11cae388f7956e01edc102b0766384ebd775eb816a5a9ac26143ec6c849ef7931ab44c83ea3d47dc0f0f06893f8e344aec2387347f66b1a7a2887f6c608721283f1778bc2bebc1a2347ddb961ec2c4d198f4c9516f05b7b570a4bce3fd8a2ddf5e5fecca255f209c0e5bea962fdceff96dbb7a8e8fad916f9058e4ce958339f95ed69432f6e4a3a9d33bf35b03b59cb896782b88bff16e27c11311ec4c006a58b8c1532bb525a72a3b7dc90e757c1b01647ac36b866bad55fa2f0da38a0139d21f079be85160334fdac98bdfeb68871e35213db43035f7ba38a456b0e29841ac3d4ced36c5f0b184b1fb44c3dd2993bb179ed6108d317bcf62d556c1366f797a44bd7d1b2585dd9fce77b25f32fc4ab1b1fa46b7ff2bc5adb73a0fbef2a60c09d3fdea2b1a5ed88b6da60c3bd3b2be0c331e6ce080835561884cf82745d1265b3d8a0d5726292c1d4191ae51ed8bf94125accd3aaf8fdde3a34218457bc05916295707c07e299a86856ec3fd6d30c73d709e4c5dd70dda07c29998c03f726117b5ec13279b904e3b715faf9761744f292833392fd0950fc7b2e6308e08fcabe7d852440067aa9dc4da1e2c3e5342580fd96a8a9c7b30bac80c5a4902989a7399a01da490bbc70b48f02fc3d11d9416c4e46eb691e2c663138cd576cc79ac8d5adf247b36b6cd9e5e8a04c374ca8cecb14159a294b149a6401eb19a4def3c4a0f66c4ac306b91292c477fabb4e282cdf2edb540ce09c61bf7f134f2ceaf617bc03fe047b4d5fe42bc7486bc2dd43e98e0d4baea36a4cbc16ff724df76ef4adaec83fde1d7001aad07b7ce3ce98a5829dc13f22f44c152cd6cb6245aefc3d7e2764bf795c64a1959fb6445c00293fd380ea76a052840184a2bb786a83f260b3ae9a4a32bda75fa24bdb4130d8c1ddd36f948b548557852eb7890f1194eb5d1e929a57c0d304666e3909429b4d2eb1eb5040febd7e88c7d16695fa45af26587a82e36f7655a39190bdde536d501169a29df89e38ad467374b25201a1057d2dfb2ff41261c1c039138ec8a41b1b80d7dcfd525bb84e94a1f126a5010f04414c22c107f7de161d2e7390cb291c163285dd4d816fb137d8c1887007fb458eee73beecd9289453829e6869b6e4240a18c5334ba3f64144ed7b58ac1cdbf6ddef93aa64ce716c130cb6419e10a0a1b38b07cb4ab66348a7f03624ee33ebcb3cb81b4cbf9204b7f6ac5edb9a2bfd8b27f8d037534f41a994293a1aa2a1fe72c59e9f45af08afcb7f995a36e1ea386abd57873249e8a85374526a9ddd5bf2b94d5813d9792c1fac610337404fe8b49af34604b0c177ad64ea0b19c5cf3f96a292dce6860e598e3a06d184059f6ef89cb80872c8e4
def compKyberSs0 : HwBytes := leBytes 32 0x86e81a17be5801293d514fe3c93d60943e523b05dc2096ee371824900b0cace4
def compKyberE1 : HwBytes := leBytes 32 0xa17c64c821d75c2d6768b06bdd0d8cd2bad1b16034d2bf96d03add8809fe1bff
def compKyberCt1 : HwBytes := leBytes 1568 0xc42e541922e8a39abf22c68aa63f74447fa1f625ee7c866f16053738f3c8c9362d5bdd5c5a576634f4c25d460ba49396faf3b52e827e37a38d8b05d2945e0758babd1732645b2726ea0b47abe94e9caa39ea58826c56ba8925c24498d5a07aaed8905a8a616c41f5617cfed5c8cbedc59b100320d7898a04c504b895d1a2db279630c467f3efcbdde15d9bf59f04a88ca623943d272ab09c31370a2bc7401d7396fd700cdb1109e9af06a61fb2829ae11615aec9e3705e7ec5e9262d190c8fd76d6301f219cb86d440b07db73ef14535322bc5662cc423e4d2671c24ed8d226ead09ed38f1cdaa0b6cba7cc4e8b65dcbd3c78ab45cafa13cd867f6b68d9f89dd397b5a5482a29b4bb977bd6d69b292aced14d1616661de2e32dfbc80565d74774b6def3177edcc0761a5102ec0a3fd3bdd8c699719661c5d1e01c0658506668c211586aa1a7f593e6cacd6142e1372ea3a55ae20b0b772235fae44270da4f016ace974738ca9acc86f009806ba993b87edc1cbe8a80b782882a11c7232bc0b50dc1e06a884a30a7ed86ba33d479a00a2309149aadac61704eb1e056e113c51da935b01cdbd53379c5c11f55c3a8ea6f8f96730ce16533a7e1371f3aa35c3804f381b84990ccb664ec20337aa2d390d11db0bc30377b7f0339121b41ddd61bb01adff92493f81b7fb3499bcd04c675bb3bef6a7edd8dd88224d7cf3614233f84fbdd922a91711bb0dadc9a8f33f870820fd2f8ee5eeabeb9db9a94ae86c3b99e102055ad188abe4bb32fa6cd9085fbb3b1297ea22d659cfc10a193e764dea4e2ba5551ffc68a5ff98a223e7b7ca7b6dab6279ace199c4d8a25d5d9ae9316a71609392275bed36a441e5aaeec7a0784601f854e4b78d0689ececc31c53b3bc5c5c7c08c851772f2992c7ee4a68af9365991af6cf6f8df98d8a8b3d01cdc38a5e2c2919ba7372b4e018e71c56946bd996724393a909d048bd434f1311889f4309ce1ae6246f8eef0d7809bdac04209d1e70289d448345b6e294c29bd4ae442b7528aca3107a9df0a2b7e2d3345b8213fe687f1186ad20b4736e424e034e367f675abdf35688585ef5cec91e9372573691c30a9320545ad88a083a5383cca3b6a41b9edf6a65c615d73c3bec360679315d9235414dc7f6a71ddde06a84b21be59e9a796e11e5b52e4d9665139d1333eb9799499c02c1c40bbfea2c356f8f522a5bb2b99e0887ab254657de053163599c8fa4efb01b0cd0369d9bd0346fcf8544407dfe3e08f81b6ba255f69255c8683055b2917e43c32572488b1c435cf7f705adf1ca927ae43544f92b965704aed934418fb8eb66d101523a978f0eecaa8f1b690df0d24900eb76c259041071c36037304f831a133cdbf273988ad7005b4638d2e379b04861332bec53afa1cc8d2159f563a7f1686d17b3776bded1d01b6452c46e9021304feca426c41b88d37acb4f651b2652c16eaeffd034a7f037979436408e2748c0160497be9cbb273b62d3fa862600676c5cbce90abb176a339e7f98b0d03cd4a8d138e36336853375f23533da7a1569cc6e4b09e539ae62ee2bae273292d00ec3c1c9b066c1176fa768e51c91b0af5db8b4d1f8e90fdba3dff867086feaeda6f0904ecc37c963cfa484665e3f75699d8cbc06f77115d10667dd1dd4ed9900cc4d6be5d78b18928f371711fbf01f76c9e2684ad3362ee37debc5cdb5b6bcef772222970bfa11ad056af9dda81e5acbc6885e626d347764a555b5ee1d29fb838644071293e9719c82545ccf87de02789d313b26b1c8798771cd570d8a330a4cb3a9c962e05ae6be74114c5168101456a617c5af83e3ad2552fb400825a7d067821791b303e55a31b90d5aaec46c47b266967de7befb8598e2745d4c9c0a11e2b40d43fbce4e7dbabbb72d63e80bb0982c2e30b00b8c0615e3c048193c5ce4885bddb113860ebbb390cb0052afd94cdd22e5d04f2a63830c14c8118a9609be2e6e0473b10f1a518879dca5c450b01c90e7f4b8dfdb01e3a8e236136bb8d054c753db37a5f7c63c1dba376e30d3d25f35ac50f81a9a200dc4429972af25aedae2eb1a4368615d291fb670caedcb9ebffe30167e2dc4657524168716d277ff0bd3824804f19be5b71191d446cb3d696a1039cfce61ef10701d5e0ef6e622591d57c0ae9e0b83d193eddb38a56cc2408fe898c2ee5b191a0ca8f6623ffdd6a70b
def compKyberSs1 : HwBytes := leBytes 32 0xb19965264efb6794bbdaed8cc7eaa4c2b2e958dfced7345859e40a0e80308b9a
def compKyberE2 : HwBytes := leBytes 32 0x675e2cdfd3d2e52d09ae220530ca23728be4bfe4256fdbbfc9024694cc039787
def compKyberCt2 : HwBytes := leBytes 1568 0xecddaae88653150d90eb626a773655ad8fc5964c8d8e165ce7a03b6039dd8e9b42847f92407aff12c6a100db66e79e66af22c3b97977bd895582392ee9e0d87e4d183d22cedc03ce196ff2ccf6eaed52703dba7610a9070944212aa822170c2dc1e5a2c7b1755f8d22bab6b9e25d983643fc4e98d29e032decaa033a7df9a989795bc2104b9914e46ac5223cfa16974595856a8d117e21bf9b0e38ca8fdf8514876d4d7cab81c36cb5a7d75b2333c78ace71c75b6d2948cfea7c8d8d8b2162607f08ca02fdfb4636ca3b206bad5661851d5ee976f41041328c7870b38e3e3f7f4ab03934ae3e52fbaed1fa0e9625dc90bacf94058a72ab133baab759d28037cad1d2b891114d006bf81fdf1954b10b57fd17b7ad9e22f0ab761b2f4b29526b50bbd6c1d2a345dd3c74c75ed242d59349e45ca4a8d97a6506cc28fc2681310a579b3a7ae057e842d0f75d124bdd393b5ba38c167cf2e64f162b72bd0db46e61fd8b23d271bfd3ded70161911978e8cc1059c175079d353509035b43cbe625a89a6a5feaae81be60a5bdfe585253d1842c34694c930bbed780f2388b093607b50f5c3cb23b5c5b93520a42fde48d2a5737f774ad09f1b66aaaace4fec23ff2d9d7970f8cf3399d74001caa7fd47a4aa15bbcbde8236eb941341f48b784f21a781961d9ca9e243a601900956b06d10df9520a6dc7781e715baebc770661f247fcb5625f87fb60670607e3d5f894b13bab380a54780b2bbd15e6ae102a0ca27cb81af7c96e4e225f064cddf23eaebb00d56f2348c501077f2f2d84fee4e84eee3beb32cd69bb44f7de26da705d38cae13f49c55e090d2b52d5fb58beb2a61961d2304357b2f06004b4fc4aa21ac38ed3305bb2e7dac49fb8d8bdc536ffbbbb8fd4f7ee5b4563f2ec98e8671d2f386b969b512445505bbac5942046069ca3dea1ba470a7fc912500f315aaf42336324bbd4d8cf85de8813ae2dbd0692a80a24868c14504e9c14fa78766c1e4c4084048dde81d2bf1daf533088ae29b0b3dcec907704c016afa75082459fc891576b41ef4005d0a15ce5fd043720480874775645f11bed44ecb6ae3c197b79b8d7e8b8b772cd718b5bbd795645245ab4fd0ce5e4a66dcb0c72a1d13a60955d46bcf94134ea00c690d0941c3e251f5c31ce6c1f5d5911ea2aa789cda81b0be259ae01cce310e309e905bedb7d55cdf5d023fa7ada4666cdd3a11a9d97effe3c126f6a4dd02ca2a51786001ac2c963017ab8fe1f910bd10c4b95bb77d6555caef6b50bdddbae008c110ebf3e70e7bf702e66d6c21f075f0e4d38aeb4eff99b2d6d3a1364fdd8a6656369b65a5471189ccf215c983c5a89105e7bc0306158bcece2a892021d37077691822e7f8a6731c2eac2f4043e9ce158dd5b9e7b0ed12768c4c2158b8bf766b5e4509cfd620533c8e1cbd38d4854bb4328ddd53a8ccf76f73797559b7968c2370c29e537cd3d1ce2a3e9d85f5a7573992a5a494330257e93d8ea5cd7903ff50de289c0030391c343533cd9af6fd46ba092cbf78f9f94a25536f020d79ddaa2a9d295b9f4b6c394248b2d4063d39ae1eb8293a14fd96e6b1166630b83d704975425447ee4574f20a6321778f1f8871a4f028c05d3921a176b7c0960dd4338fe5161b60b25e097a9cea69f40591dacc3d7c4f6d9eb228b1c8bee6a4f22d8cc5cdc64001040def25a88806f9f87fe21d450153f38fc629fd99218c2e182a6ddcf6a91fb5ed273f60ef38bd8f5419070672112379b9e388a34a89c70c72ba112b73e21d3544231d431335bdc43f1f2193beffec03070a45a086d3e2c72342cee1377e01726104f6a29c89177465ee98b92a075c11fa19bc34ab6a7804b61e5f9c0dbb6077bd9eaa6e7b97f7083ff13fb80bd438d084898d468b7e1691c54135dcc08ffb6584d82c22120a42671ad9aea3d687cf94ad2fbe1b24e964deb0efc3265a5f497d307fde33b4a042970050bb185ae6df792554afb84683835d9c0ab6904c92319e2185d4f87257785960e7be46b8fba5344c857b9e8b8f1ad4eeac1b7faf445a62972fe452ec272b104a2a0c1b3251ab9346ff7d94daad7735f0347e9396230ee5666eb3266d22cae8cfe40eee1319b69d3346108faa6e88ae14627f2130bd807cec468254d1bff67279fa2642026042825ac9ed7ef6076ff0b56098852c92426df0bc26e78f15437d6b6c7b8f8
def compKyberSs2 : HwBytes := leBytes 32 0x32c88db1104654ede99cb46c61acb5170a8b2b78b76649d64f3b77acebf05deb

/-- Kyber-1024 encapsulate output (`1600 = 1568 + 32` bytes) for randomness `e`. -/
def compKyberEncaps (e : HwBytes) : HwBytes :=
  if e == compKyberE0 then compKyberCt0 ++ compKyberSs0
  else if e == compKyberE1 then compKyberCt1 ++ compKyberSs1
  else if e == compKyberE2 then compKyberCt2 ++ compKyberSs2
  else compDefaultKyberCt ++ compDefaultKyberSs

/-- Kyber-1024 decapsulate output (32 bytes) for ciphertext `ct`. -/
def compKyberDecaps (ct : HwBytes) : HwBytes :=
  if ct == compKyberCt0 then compKyberSs0
  else if ct == compKyberCt1 then compKyberSs1
  else if ct == compKyberCt2 then compKyberSs2
  else compDefaultKyberSs

def compToEdIn0 : HwBytes := leBytes 32 0x627fac8bff0348b0c032b515e585e882aa28244c58ceadfb6f2c8876f3506df7
def compToEdOut0 : HwBytes := leBytes 160 0x5878c9144a7c80004cd453acee0a90001fcd8fa76af040002583687913b060006e7568ae2d4f3000000000000000000000000000000000000000000000000000000000000000000000000000000010007ef254c93b079000228b5e52f00dd00001f12091a5b9e000084955b96165200038fb47820a1bb000392e984646ec300055da88bdda09d00028c51926f4eab0001808d2d4fc2fa0007196f4b6dc9ba
def compToEdIn1 : HwBytes := leBytes 32 0x3876d0f225aa2d85682498e61e2fe97bc189e4815c96aee21e8218cf997b078f
def compToEdOut1 : HwBytes := leBytes 160 0x2a149ae202693000203c866ecd7c400017ca9eb1346aa00046bd475be61f400073071d567eabb0000000000000000000000000000000000000000000000000000000000000000000000000000000100047a30b25a468200010adb79e55f040000236395f378f50001f0f363772bdf00078dbefecf5ddf0006bcf8f1ad64e30006cbde347ead7200048708cf90dc740005a6d6a8d9815500067d22beee5436
def compToEdIn2 : HwBytes := leBytes 32 0x191933f5352eccec96182dee25cb6fc49f24128081a4b0215fcc626dfb5fa897
def compToEdOut2 : HwBytes := leBytes 160 0x485855e370e5f00023a74cbf807610001b083b066c7cd0005ce1e098035f600055f98b71fc6340000000000000000000000000000000000000000000000000000000000000000000000000000000100033e156af78bbc00009db993c58c840000664f0e0f4f0800041e92664d928f00050ce0879dea270005be2c37e8251d0004d7cc91618eb800075d43278f7b7a000218cd445c7617000496286d2cfd72

def compToEdwards (u : HwBytes) (sign : BitVec 8) : HwBytes :=
  if sign == 0#8 then
    if u == compToEdIn0 then compToEdOut0
    else if u == compToEdIn1 then compToEdOut1
    else if u == compToEdIn2 then compToEdOut2
    else List.replicate 160 0#8
  else List.replicate 160 0#8

def compTorsionFree (pt : HwBytes) : HwBytes :=
  if pt.length == 160 then
    let k := bytesToNat pt
    if k == 0x2a149ae202693000203c866ecd7c400017ca9eb1346aa00046bd475be61f400073071d567eabb0000000000000000000000000000000000000000000000000000000000000000000000000000000100047a30b25a468200010adb79e55f040000236395f378f50001f0f363772bdf00078dbefecf5ddf0006bcf8f1ad64e30006cbde347ead7200048708cf90dc740005a6d6a8d9815500067d22beee5436 then [1#8]
    else if k == 0x485855e370e5f00023a74cbf807610001b083b066c7cd0005ce1e098035f600055f98b71fc6340000000000000000000000000000000000000000000000000000000000000000000000000000000100033e156af78bbc00009db993c58c840000664f0e0f4f0800041e92664d928f00050ce0879dea270005be2c37e8251d0004d7cc91618eb800075d43278f7b7a000218cd445c7617000496286d2cfd72 then [1#8]
    else [0#8]
  else [0#8]

def compEdwardsCompress (pt : HwBytes) : HwBytes :=
  if pt.length == 160 then
    let k := bytesToNat pt
    if k == 0x5878c9144a7c80004cd453acee0a90001fcd8fa76af040002583687913b060006e7568ae2d4f3000000000000000000000000000000000000000000000000000000000000000000000000000000010007ef254c93b079000228b5e52f00dd00001f12091a5b9e000084955b96165200038fb47820a1bb000392e984646ec300055da88bdda09d00028c51926f4eab0001808d2d4fc2fa0007196f4b6dc9ba then leBytes 32 0x7ef254c93b0794516bca5e01ba07c4824696e78424aadcb0b2938fb47820a1bb
    else if k == 0x4d3d7e70c88e900027bea208f38b6000584af592c54c200010fe0844ee26c000015a32eb7d22f000350b0c0ecaa4e0007a37a2e47f32f00038ddb606306bc00017341a5b3e67b00059b4d2b2555790002f26eb8ef19da0006d899f04e8db50007d0a4d50da5e80006d48b89a3193c00056801940b805a000480748b2dbbeb0002687e3b4cd34d0000024e7758cd02000093f30e236ece0004ff181bbc3a23 then leBytes 32 0x689653e280aa7564f9a4f48fd1437cb87e75435627bb9c96abc674fb9158bd69
    else if k == 0x2f0cac43108d50000eb80cc4a344a000685f2aa1958d00003fda9017bffc80002c6db4798e4c90000a05dff353f180004e8a5ab1a54a80004e1e765adf52e0003e15fe858a4dc0006185ac953c28400030a1da4393edb000319e84a20cd1e0003b2ca5becd9e200038ff42a8462cd000292080d06dbd30001fc24610153bd0002711f0c82ff5300063a51b10d5cfa00046e210dc1306b00007e4f141bb4c9 then leBytes 32 0x5df9a41280bb4aba6ad40bf0575cb612f816e75b9f8efe23a88f6b6bb02019c7
    else List.replicate 32 0#8
  else List.replicate 32 0#8

def compEdwardsNeg (pt : HwBytes) : HwBytes :=
  if pt.length == 160 && bytesToNat pt == 0x5878c9144a7c80004cd453acee0a90001fcd8fa76af040002583687913b060006e7568ae2d4f3000000000000000000000000000000000000000000000000000000000000000000000000000000010007ef254c93b079000228b5e52f00dd00001f12091a5b9e000084955b96165200038fb47820a1bb000392e984646ec300055da88bdda09d00028c51926f4eab0001808d2d4fc2fa0007196f4b6dc9ba then
    leBytes 160 0x278736ebb5837000332bac5311f5600060327058950fb0005a7c9786ec4f9000118a9751d2afa000000000000000000000000000000000000000000000000000000000000000000000000000000010007ef254c93b079000228b5e52f00dd00001f12091a5b9e000084955b96165200038fb47820a1bb00046d167b9b913c0002a25774225f62000573ae6d90b15400067f72d2b03d050000e690b4923633
  else List.replicate 160 0#8

def compDoubleScalarMul (a pt b : HwBytes) : HwBytes :=
  if a.length == 32 && pt.length == 160 && b.length == 32 then
    let ka := bytesToNat a
    let kpt := bytesToNat pt
    let kb := bytesToNat b
    if ka == 0x99f0f157619bfb8b1b8267af1c2e58e35b2598910b89ef29ae52cf13320743b && kpt == 0x278736ebb5837000332bac5311f5600060327058950fb0005a7c9786ec4f9000118a9751d2afa000000000000000000000000000000000000000000000000000000000000000000000000000000010007ef254c93b079000228b5e52f00dd00001f12091a5b9e000084955b96165200038fb47820a1bb00046d167b9b913c0002a25774225f62000573ae6d90b15400067f72d2b03d050000e690b4923633 && kb == 0xac1aa990a4cbd3b772e51b1e8e2656d9df2297ff1af29c98244a78c3fcfea64 then
      leBytes 160 0x4d3d7e70c88e900027bea208f38b6000584af592c54c200010fe0844ee26c000015a32eb7d22f000350b0c0ecaa4e0007a37a2e47f32f00038ddb606306bc00017341a5b3e67b00059b4d2b2555790002f26eb8ef19da0006d899f04e8db50007d0a4d50da5e80006d48b89a3193c00056801940b805a000480748b2dbbeb0002687e3b4cd34d0000024e7758cd02000093f30e236ece0004ff181bbc3a23
    else if ka == 0x3fcd9a24468a92ebcacb6dac5b2a92bce715fc8f20b793c97604fb33eeb9465 && kpt == 0x278736ebb5837000332bac5311f5600060327058950fb0005a7c9786ec4f9000118a9751d2afa000000000000000000000000000000000000000000000000000000000000000000000000000000010007ef254c93b079000228b5e52f00dd00001f12091a5b9e000084955b96165200038fb47820a1bb00046d167b9b913c0002a25774225f62000573ae6d90b15400067f72d2b03d050000e690b4923633 && kb == 0x575a2a18d250abc139a223a67c035f2662ca6f6beb211de1200671c8323fe32 then
      leBytes 160 0x2f0cac43108d50000eb80cc4a344a000685f2aa1958d00003fda9017bffc80002c6db4798e4c90000a05dff353f180004e8a5ab1a54a80004e1e765adf52e0003e15fe858a4dc0006185ac953c28400030a1da4393edb000319e84a20cd1e0003b2ca5becd9e200038ff42a8462cd000292080d06dbd30001fc24610153bd0002711f0c82ff5300063a51b10d5cfa00046e210dc1306b00007e4f141bb4c9
    else List.replicate 160 0#8
  else List.replicate 160 0#8

def compScalarModOrder (b : HwBytes) : HwBytes :=
  if b.length == 32 then
    let k := bytesToNat b
    if k == 0xac1aa990a4cbd3b772e51b1e8e2656d9df2297ff1af29c98244a78c3fcfea64 then leBytes 32 0xac1aa990a4cbd3b772e51b1e8e2656d9df2297ff1af29c98244a78c3fcfea64
    else if k == 0x575a2a18d250abc139a223a67c035f2662ca6f6beb211de1200671c8323fe32 then leBytes 32 0x575a2a18d250abc139a223a67c035f2662ca6f6beb211de1200671c8323fe32
    else List.replicate 32 0#8
  else List.replicate 32 0#8

def compScalarModOrderWide (b : HwBytes) : HwBytes :=
  if b.length == 64 then
    let k := bytesToNat b
    if k == 0x233338e7f358192a56f43285df78ddc2fba98a7280dd4cec7d70cc5ad6028556bed600c27bfee2d189c32d0b77021b445298db845dfdadfa0cbcc6062e5cb320 then leBytes 32 0x99f0f157619bfb8b1b8267af1c2e58e35b2598910b89ef29ae52cf13320743b
    else if k == 0x5912023c7223bb91b41d247cb25b026e09565ce04cd8787aede080da8651d774cb20f725ebae08b0e09c1dcf60510165a52c57ddb7a251e3495d01694831f46d then leBytes 32 0x3fcd9a24468a92ebcacb6dac5b2a92bce715fc8f20b793c97604fb33eeb9465
    else List.replicate 32 0#8
  else List.replicate 32 0#8

def compMlkem768FromSeed (seed : HwBytes) : HwBytes :=
  if seed.length == 64 then
    let k := bytesToNat seed
    if k == 0xd29f4b1ebb34c5fb9a88a065d0c64af252f6b36390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523 then leBytes 2400 0xd29f4b1ebb34c5fb9a88a065d0c64af252f6b36390ab32da16b3db3cf2c0f2e15ac2f4ce6d5b71c22b23d97cc15fd3dfd708a3bd1e6fbddc7d7cbb0b08bac6000b8cdd0fe997174ce780528bf9ecc13020f000fc44144b1638e063bc8c1218a54669b94d499916b04ec8b2539b63e4a0e87d9e04077bacc6c5aba21579703142bb10b73c96f63e68411d16c1241f039aa760790fd80a9d3a35b9a0c7adc6eea9e09a713a7026929b1c701c5f9c9b9434915df3a1beecdb8e29c97419c1c9678bbb48d7672b62cd33798d258a0e26acbbe7252b03c79a388c1b05bfa8ac9bc141bfa2d7fe22584f99baaa1dc8c56619a822d5a6135080c2d8409d4c275591e219d1787eba6cba3be6b0049599e2d0cbc2c43435ab48768b898636b028f09ae28f1c52c355981189e8e5a6a1659329c277b941a34a4769dabfc21b3539e3e5b747289fc7a263109934ab8545d48c7217d26ef872435cb59d16a17ca026c9993588e7273a32528c96ed2ef0bb3eb4aa2171ff35c8526682ea9bc02c6d92971d956bb75a1345c4070445253e814fa432c033e1ee56d4a233c43f73d71bcdc0d24f2b02109199763bd5af89da0548ce7c9c03c9f1fa1f62b1801a7fb9fb5b7e002d12e9242c1a0d968c5d005ce446d05b3e6bf48131be3352775965e379d0af59e1ba0198d43e1adb9414d81335d6b8cb7e4686b0c808f5be53229779fd2906766ce77011d5b447c6ef2e41bd85c6155bd2c67e44ee3fb187a91539acac4ba619102c9c8e7161b23b7c46a583327d97a2c1dc0d76f37cb6326942491e20c7e856d5ec47c0f335d405265c064b40470d97649a180c0efaf993f9723515117a5ba6070acb05839021c9165c76f5c1d57a4783eec4c05b0353c0a048b36633ac8d66bf48052e69580c2236b15a93a11bf97a68e412a91c418239115681e93eb45375923e7e64bd4545508aa4771cb40976ec1ec4b228a808d9205a773dc26d9a7bbf3a9abb875a9d84dbba81a3a0bab2c128067cc38965bfd9207f2add5f2691282086b7237b84eb358e17904d357a66e82946c6d68d2b619e4b38996a178c0be2c0147b51803d45f024cb8099c5a3d36537ea4807859c9218bad72773f6583a40971a7cc8a09694aa45da348c1047b624af768aae699617f79ac097d448d6f9282926bb943bc58b0435a4af7e726f84094f5d065d7df6b8c414051ea1580a994366fc5a80aa526014604543d0cde9c78442294b0c7b6b00bb2ed0643719bb8b81b716c7df7c591776f199cf08b6133aceaa39ad4ae0298753034e40607fd6aa2b47d7ac58bdc5b30618d3427f40365b12e686d6112bc2c81ad8918e14bab8ac4589978ec9b5804a015b74b7919a79049af14c83fac823fa4e36277b29583a5cd3de82e65d98bb3c1482c65adcb9c298b298292aae02e942b18b1303930a45b00be39fa5f8836f6c2b543661a9220b2663d226c5f86cda7d34f26028aa6991fcb467c54e727719cd1adf8b03d105466d86943496ea681bfc237e17d59784cd8e64fb81e86e48fc9fa441ccb5c42b5d5aa089382b32d9e56ea0347959e466d3ba05f5ecce61d01ab2a98a97ff2200b119745ba1e92f8f13b68b02bda5217f4084004a59026df83f4ac22a65b224bfc5b52a8b53a98345c4496076430f8c730058fb773ff90dcc157209618639f0a994e94705a4d55a564959b74a6526b96565ab88333028e116ad60c1a3611baabc7a4c8bbc674b70a0300f96d7d097d3c80aac330c59c3021a55a41cc31911f52075d253f9e63b340f8f6cc450179a3c826fa9978884919f1ffbddce05304119ec652b5b6bf2d23bf5669e12c288fa6d649ac155ab56656ae723e013718a20bfab0185f73d00d6e78263de3d2ba6c2d0abb0c48163e088bd00483b34d73a428a64a97c707bc02502d30eba565d857a6b00b4974ab88a095b98a4106a689d0e9590c010e27611f818c5e43985e901658dac512d515a9fb2ecd48277338771ba187276abc07e824cc11b77d7b704e99f802306f1df14064a3b6298c3dce9c1950b09ea8603cabd4b30bfb9f548c7a0aaa1eb0b7f546791aa2bc5804b75e9e15f20ea2ba1e6a3ea05b06893a435401b52b832ea6b50468fcee7cc30024d28504bbed5aaa7d76e7ed674186a8e406c4240564eba614bc206ac37039f8473bc95a76d4d0a67bedb4c5527032f722f1c2035529709a41751938192c3c581ceb2723d269b4dea7898d5c7305145727c5260d42743e7774093c50ee9497bcae152578e3fc7125ecc2a09f27ac7756ca3d453435812048a9a34a609ca634d0c71c18784dd2b02facfb90770f86123f758839218c156d70f11b5a9196ea18bf0144778705cf02ab9d3337ae25443071f045702e6c523e81f1b528188050fb256ee7fac6b50a35a88f8f43e7155012a533ce8114df5554c442844671441091131435b1b89173858c3b23c09542bcc2637a0866c3b6e148845b89e33aa50bb417b109989a57ad49c8bf7c2a0231ef0b851452bb4273415818956f1d8a209746d27ac74747479c965c9b5df51102cc2a32941052427c5815de51c2036f4a0e91e1ca70613056b5766ef7d7345b342b90e36d85901784541de6a889593b01fc20a80b7d0bf2bc957bfb77562684a95e1837a2aaa5ab9de7eabc46c46988feb4165bc3469112f556b58b190ee30c5026eb24555177c621556cdc86bcf59e057361495235d62943535600a787bf3a139751c5ca2b699ae73f344c9b8c507ec7a8288d09ad32787e1ebaa8ae4a2139c389456c7aa863c7a046f81923cfb9f511c048a5051a1605208d8b0b4f20db447d17afc3fa198124221e80be59e12502f8235c701313d0ca4838a90c63cab8592e5ad070c5eb162c3c1b22209204b56aa49b5f90a0505c69f6367b98579ae72d44153d581b494a2e18189ab0d2c0c6c335bb63887097cdcff6954308f17857f56c758813499a1556472ecbb252391e888ad73b68ed601ccd48a519a836cb104377b95847aa9375847c06476457c49884a6231257b0a77b4b6b31c7744357d7b2b9cc12623c36e834701033240a5e90791437e53589ecd0281a2e21284d9dd4779509e1cf6c764e83ef91058061c8f568e72d36bcb1ca8a6637a153b47bb1bf650139e73c5fa22879e5b11d33b7ac72ba5f243d8669ce2a47db9427cc347aeecee07e33e1ef37f10796325cba5cf4b9861da023cb77a7f02da03054454f6d786d6d384fa8750c98091c4a82636ca41e12b8827798308c651677210a22bc62557cbe18548a9de7b5549bad9314fe8a31ff91f0cecef69f6e968aace524c5581183b5b0cab0794332f35a821831cc8a4498eb5332ff398bbf6747bb9bdabf2baa6718758253555c64d6ef49a0c0a36c1476d
    else if k == 0xe433633e690c580d48a845f432baed2d9d4eacd4dd31530387efc357272635b4886bf03de19054c2320a13e03f67b0a3ea550f16370a2a9ba446ea8eb1ecad6e then leBytes 2400 0xe433633e690c580d48a845f432baed2d9d4eacd4dd31530387efc357272635b4c5dfa53708ac5adfa9c2afd695fb8d5722060dfb58d3c7074b5508b4c4e50286b03846914a49bb4426876200e8a712484bb2386963aab9bcd113547372b8d671a6eb7801c1f0c7c687bf187a95857d786bc56e330c570063a485782956261a6b93863061675562a483fd49d5eecf507f5d28b82cfa9924a6ee93997b25009f7ce4d2bbbbd27b26cf19cb9058b563bb11d525d11189ba4e4449c21d478d549bd04e35f96e26f26fdbffa4483f7d67a02cfa04608a7f60c25b5dbb8439c8ea4127888865dabf4be5a164ff4f8b4f1716f976c4d428700b16d48b8898b16c586bcc55884adaac4e11e8a924f8b167c757d4809fca52bb54c7b37353b235161477829d52e99a3a5da1c382b434bd48c8c593db7392f86017e10a72a7ffa1c3adbd62173afbaa52a8766a747291364971f1ce5f3629a319df25d1d1876c4dbdca154012d592d8b999bcd964d73127eb98852928025b2781fb9353049625dc748798f972c731375aec52675715e8175f722a1cfc720804e796ba8e0762ed43a73cc4d3405febdb6524bb02125aab19013d03ff48d79986f3882851b52291c327058b4ee3696edbeeaaa9fba7a366ccf19e8fc4ac7cfaa56304e46166ec1b449b8408571debb928f740790665791057b59783bb314d08f514232a7d3352b28e591899811b4115433ce7e0114bc692648b1764a86a310c81e73190e5e0877c8799b80413a56fb019bccb955355b933663454285b8e23c66700e051bb1a1632616041f439bdd4990ac3cbc0a29640142435b9cc52a27a74001926a307b628931cf4909670330b02c73ba3599c9a103af21692a651210325bfe27b3228f95e470d5612130ff2a03f3bccac1845c25bea4bfbbc38e7987a70258868ae80e1fb73865ccc5a55ac2c08779aaa7cc9a39807c92c97da6d0c4d9b0bc998045a1e02946766b74a09fa6b5c743e014b70c89223795710110327e3684ef683753558081cb25706dc19c1fe9c393e0ecab8a377d496e8895558522ab42f95b336b566602899acbf8a951adba32c109a3a532cc5c916a4d9b82c58966a438002829b3a58d62eb063b0ba2f87ac9acf0541b3f2526cd4dc81201c1d8c66589b6bcc38449be0be1740996bb7458d0a166e797e43655334e1eace42f39f85fbc910f21de025642c7c233c622eb9018173129da1975fa2b8b268c032c9b2c7b662cc407dc0a09a60e9385621f3c44cbd44993a1d0b178fd49498056064743a29d666208b18beb2232c50f075371c87954cccc5ab2a90284e34af5b5c544023a846b0b774f2e572c3f5056051bd151a3665361318c12c365692550e07c3db7c75dd7e2856b91a8572c0c46f58cd6eb1811babb8b69bfd33e66c14acc81819d6229872a1ec797b03a2c07983c4e1965b126538646e5e323ecaf8f99f76be8c057b2096f1c8773ac033642d537e2a568d8443a2b74c67a303fe6e5c85b216f41a17d370d25245668e15e5aa44511c5f67aeb509d0353793a4c47cae532c5a03bf385b5f8502715378982d015aba7760a5200fb3736c61c19d51cb9761bada981af31476035ba91ac9794f362a998adb4c124cb13f5b4b4c0347ba79b95d7ce32fa8f194975025b889b6f1713592d4708c2bbbd7dc46e3e95916438566e1b06455cb5cc108a5f45b4c9e107b768d38d00d64c4c82b7e45151ba08246c69b1102e75016c4c700d789935cf27043f519f61a123c8357587797e67f9774be95b328cf787871b87ac1b2b61fd83c3374a3c751e79c19266f406983d06a27a92f0cd444a261c0aafa6c999b87079c32a111ce0d092500a20d07967c674269c4f20fa1e9b04966dda14ae0571ac51f35c1525ab95ab409ab3a2c0bb54cc5e66bbae6b7106c7a0ad6bb4a3c1c387835ce560c0cc7b554573546f4790d8bcf20a0f126d7c9430c8607d64c0732f5a30a7232472c44c4229196824ca7602099156b8294cc58b867ca607536cb40a7db7f0a78ce8aa97c2282593b9253065a0ad16d74554a52111322b1e8adab9598085483ab6531eb3d6d0abbb8176f581b8d925cf78866d041d410171bb81623490b8a7a2024fb9aa2189a821aa0572601b62e606ba6a0471eb317f782192e720b4965e6f39fb677ac4b737aa12e00a9fc1c5061434c960e507e355698a33b45aafbb488306e20568e55ba31c436eb8c44f75c1bd8736cef163b50ac04d93e0bb08b70ac1562f0098653bea3ac401c33ad5a2333a3ec4ae9fd870480b7ab7139bc46091729b4baa31b24cf3e08cd9bd3c814021465bc14933c0e29f6ac02024c3c75d469e2e21f833d98c8c942c4ca8593b98d434e301bb0cd522d694b3aa618c2c0113b79f94155b209bb818165bb0c0700cb5c49986ad37105e5a3346a466e343d88e97865969100bbbb8a73c6412a1583e6bb6983633e193a1f6607cdb8eb00d5a7643a8ebf43e39b0acfa97c2ac08219b443bf2152ca7d257f9576cc53a5951e57f53c38fc2b67e70d4bf72e0cc5ce033b84586878cb77a7c5cf99f9cf9e88072b01caa4c0dea1923238bc416623fd335598c8eb3d4548301a39a12e783183dcdbc7855f58f06bafc69c06706c504a467ca78db5c0e72225f9894bda22682fc695391d12d1996beb7c80153e67ae8cf9cd0b462820e8215f0658c5c7fc9cccbbbb0bfe52b1a61f7b1cc35028a8e211bbc6a51ff54c915a573c76fd1dfbda306c406897a9341a0487123da53b175a50ac51d3bc13d23600db2a002cb20043011589dc6c95de5f94ff631c463a06f123ccc9b9eb287ee9aab76cb234d093902c0582c9f16d2579c074a8186c2ab54abc9e0a7bb436748d3b39be4a4f5cebca8846efc8e57d520372c679a41a5cd04f50e87ac0d781487293e0788732fdccc1c32db1af895a027fe3b10870a2a5d7aa9bea043f70e57cec389c80f71f95136499073883c545786f2f2b4708713678da7439cca112209b30bbc8b5b43a0d4ab45869f36f4c847df6e7a821eb8821c528f38a45e630551a9f256643cdc44e8429af27f2c750469ec543c5be4c7e09dcb92f712684b57e2d7b004117d868a28c29511122910564abfc57f4bc2c04f13a779c7db1b5096bd2b32a0371ab050036a85c9c8c6a31f0290b60a217b18247f96574595dacd664389fb66b9f12ba73c6e2ad92e30e83d462b7d62277067661701b35b1b246f9e74b701d17d130803a176430e980a911a808184da637c623d2b091930e7a244452afbdfcea5fa05cc73836cfdbdc83294eb394342254f7b495f3a67c75c110da07d2114ed5f747d5bb62445cb6ec07483cdf51e213277727cdac7d71571c1763dfb193515ec2da2555daced691639290
    else if k == 0xa5d53e09b850b7f2c85b3e77c1caf4c396dcd9e8980b522502349fc21e8a359470c1bec90f220fad709ccc50858c8ce0d98f104a4f0c16e18ec8c1dee3e29252 then leBytes 2400 0xa5d53e09b850b7f2c85b3e77c1caf4c396dcd9e8980b522502349fc21e8a359405d952d6c5c74f7fa94764b75b8bc7ebc2ad258ae290f6e347e27860eaf2f555c0396c4d0c20a2783f686eb9f1a0d3d9862de2de4453d804b01c6fc502bcb3ccc26a389654cf487b04cd882fbdb8492eb0ca5c43961adacca871fab6536078844a18c52d1fc0f4b133962dd8ec5f93ed1648785e033f66f4710ba61169b23bb7e90e0b4bd79e294faf4a5c37cb772ed58d8379cd7e356aad38b6091b999aa1769b98d400e02372c79073cb955d006936745337a47629597565f1860c88aa7ff7a40657c9555763257632c333e91c4cf0cb5be78e606e9377513a9b3200760982476b42705275376a2987cd51d3ee657b0a4674ee4dfb6277656c4de9016f320778a0d579e37708124c560856b85acac0e6ec3890da2697694bd925ba859b3e7b0e696c320cb8d138f0e91128f69233cb4cc3ca8bf02d3b3a1d7a1157ca61b5c6f8e2b575b4627121ad979953642343d8d93f13c8778ce18e17338ebb0c3435af7582168f3bc07ec9210e2a5e18e937907cfb8ff436c6240d9ca7326e86e9a3eba740c77d7ce8a18892916dd82651c7443b364c2fe9213bc2b50d77667c36640127758536802d03e40d01b48bb55e1839178f9c0823520a31f7a21615c9a76b3a7f9039cc23ac0275062a0c390016b1ca0cbc4893dba6d2d48f152821d278a8c823c6681423f64b93e9aa4d086dc0222d20a42405d2d27cc610493ac2bc9955069c37bf26ef00f8c9565a7f535c6326e8735881f44120b485b12252ec8ac3c9eb7c16235b13b277733dc549ea81c213ccc581b237049f38898394a499a95c21e6376d615a0507f7229ba34cb437126259abd6083954e0be20ddcae8c26c2cf3585b3d8f94b779aa3f3f74c86bb9e46fb876cc29741c499a96c1dc218a840336bbc642547402e0948c971f4a650e76845f82b8b64bef54d454357bdc3a3c7f9ab739525bf04323529823f58331c65467de7437d77049bb43c30b7f3862739cb16f2a7991e36ac4834c8ab036cd08d538d13f39804776e6ad14e7d90ad172bcc72a3aa6e232cc3234478a5622927ebb465036005390f949d18b3443863890256fa7eb7955639a70c614b2401c82bc78b27cbca50cc9fcbb9861cd84bafccec6f550e35499109b9f920c83e1ac2f454800a5813fb78851544c9964eb4449e91006508dcbb50908bcaa32cf04f9beb9d843af28a7a4b44ac0c26132c595254ae724fb01223a761bc1be8aac75c48b267939a04fda8854f9da52e263c1d18ea90c5f72e944ccf6777ac0d97b957f034b91cd4acf2983280cc3392034916fd859cc55523aaa3c0c679b056800c862509f942791e944cb86d567b5fa9e065a354b6153059ec88aa09d707a0c588d655538ab16df34eb415314d8833b881e205727d7dbbc532325823383d786566bf3cb83cd1711457ea93f68610ebf4c2455090b0ef18754e6b2c991aa4a9cb8b3a83bcae5ff5bf4487ca672533a2d9b51962600a6b627f6651a05bcb4b6ac400581eb50c531a5c8d7ac741cd6b171da8530415370e49bfa9fb3f0f77d704d04163297160c1d5296341b63cbab001f331989289291f197bbbc1e288aeb0368e86aa8ce0406eb2a61167452b751b34603a975365b6f404a714be272570763424af8278b980c6996b30759cce2fd675a2018400a5668360a28a16077acc62ba231f2579af948bb73e030741a87daa1b2f315a3a051788c321960217590ea6d0370a054c82886f708d46ba8b8183997a1323425456a1504028340ca9660056f0c3c2532c90d7d4231a56314c6d1309e0cc5847bda0bb9a27d295b57416e7eab235bb69c7b686cc3b68170a58c00b65f5af301c26930bd843781d1a6744b2a02a2144e97dd9cd4f83cfbe40c0be084712222779d6523cbafc01985da9e31f469410bddab3240393a2365b562caa919802c88b07bb604c98c8f03396327b70d485c4afaaf4877f5939bc83ab949b7006b4a5be8ba74ee913ae45748359e7c447268e857bb7465b9846d09464591fd0e594e10aa37838a7a273833ad3423a266cc54eb0b3229e47109645660e3c69c95c188895028de7579d07b75f9a4c2a15721133f37ccbc407f520aa379290a66ac7d7a366dcfe5dba75011a3889f403c38ceb630c5000f163a89b012d0ad741d5ad85107dc2d97c5d164d1ccb60582120829556ced58a56c50e4d216cb3d655996c5b74452c6011210e56026601b4aaea7933c35c8b8c0a1605716819649b56f48820b0c6f147265660902c7435e8c208d954352564a3d4379b05f38674c399541377d68bca9aac4c52e718425650e9333d198d955bd007620619d09c0873dd27e6bf0f8734b9062e6bf4af43eb7b120a59ab80056e1c5eabe317bcf9aebca6a06e2c2f9c226d427887cae65ab2ba2cb4b4088163b998d8ba3548e9ca2c283a619cce5b787a79f06876c5bd839f3e1534839a4daa21ca36164970a507b8f7bf1b5cd20f66cd322c680d03e19537d399e9769f829643c513c37615bbc179bd307b040cbf073ca865eae3b042238579c1241605c1d9d67838df7bf74455f27d6fd606cce1c0ba54d22642fdb139bf58d0d48a16e6787ca3af789a8a573c7ce02a6cfc170c6b46a1c94f9123a91e781ec149e913e11d713ba2af9bb25f77892dc2962cd9d777fcf512761a8791206d1c35534b42015668be5c7e98b017b83a4eb5fb8133d8bf11586335f34109c081c2d52c4335a7ae839da73460a2539a48f4147fcc76c4fbf893eb3d100a9812535fa8c94c1af6d9b2b3b32c095f74f68652da5ec7f02cb1acf6a1b43e794b3aa96a452a4512555afe4d348673f90e02125ecbe86e2cacfd38c5711daaa779c4946555044aab0d32eb2a2d8744373b5c75d685722026af26a56699d1cb4844cc1bebb4c9680ecaae7004de8c0bd34a88642b7b8e8227ff9403771711da88cb5638e4730145109ae54006bb565e31e8954310c91b65507ce55da5636d695544d91d05f3316f702c74d80d1ffbf8808ac288eb2300b95644c64db866422736a1a6b3fe40e39e56015b25ba7e8ed275bac311b005cd210b4b550af141b94244025160fc3a8ed6d7b5642a784baa9193ea0c297a4f7b4751f5f9300bb538d7a158764e2d574c1a457f1ba9391f77b982494e7490537665ed0080afb5883fcbd54dce989b53e522bfa203c5967115b7e83dfa0e6fa17776a7c682658966f7d886522a6570631fbbcf28b3e702f7117f4a0462113049011e60c3d5ac8c5531746a995aa0b345569682845ed0de77326b131cbc7ee684105708854a774a8cf25501499418cc9d98d0999bd47032827427acba047d91b2ca2f86b45386a9be895eb6f
    else List.replicate 2400 0#8
  else List.replicate 2400 0#8

def compHmac (k d : HwBytes) : HwBytes :=
  if k.length == 32 && d.length == 105 then
    let kk := bytesToNat k
    let kd := bytesToNat d
    if kk == 0x5ecb152e05ff5834fe3b23b9a714982f10c6d29af74f8ebc65dc41e85248b1cd && kd == 0x5ac2f4ce6d5b71c22b23d97cc15fd3dfd708a3bd1e6fbddc7d7cbb0b08bac6000b8cdd0fe997174ce780528bf9ecc13020f000fc44144b1638e063bc8c1218a501000000000000007265646165686b653a3836374d454b4c4d5f31565f414b4351505f6c616e676953 then leBytes 32 0xce849e0a450f61afb64592dc66986e1aee6c76148888a8a1efd5398f9e8f1d38
    else if kk == 0xda9531f9cc78d8bc2f2247d73934950c0d3727a14e4b233b5f3a312711b33bfb && kd == 0xc5dfa53708ac5adfa9c2afd695fb8d5722060dfb58d3c7074b5508b4c4e50286b03846914a49bb4426876200e8a712484bb2386963aab9bcd113547372b8d67101000000000000007265646165686b653a3836374d454b4c4d5f31565f414b4351505f6c616e676953 then leBytes 32 0xe710caefe1d8e3f9dd028ee97e6d5b484c1ad09e476591d0b9830a0fe42f1197
    else if kk == 0x1c11bc1255efa80b7baa56324c0b24c2cdf45fc045e2afd9849df2e2b920e4c7 && kd == 0x5d952d6c5c74f7fa94764b75b8bc7ebc2ad258ae290f6e347e27860eaf2f555c0396c4d0c20a2783f686eb9f1a0d3d9862de2de4453d804b01c6fc502bcb3cc01000000000000007265646165686b653a3836374d454b4c4d5f31565f414b4351505f6c616e676953 then leBytes 32 0x1f49fbfdc0472992d571a461caeb6d40b15f7180304197c65a19725197c88df3
    else compDefaultHmac k d
  else compDefaultHmac k d

def compSha512Rows : List (Nat × Nat × Nat) := [
  (0x5be0cd19137e21791f83d9abfb41bd6b9b05688c2b3e6c1f510e527fade682d1a54ff53a5f1d36f13c6ef372fe94f82bbb67ae8584caa73b6a09e667f3bcc908, 0x80300000000000000000000000000000000000000000000000000000000801814e39f6c4912ea4cff03837272d451a1ac17771cbf3a0572c2e6bc9688b8b6057ef254c93b0794516bca5e01ba07c4824696e78424aadcb0b2938fb47820a1bb689653e280aa7564f9a4f48fd1437cb87e75435627bb9c96abc674fb9158bd69, 0x2a1958f3e7383323c2dd78df8532f456ec4cdd80728aa9fb568502d65acc707dd1e2fe7bc200d6be441b02770b2dc389faadfd5d84db985220b35c2e06c6bc0c),
  (0x5be0cd19137e21791f83d9abfb41bd6b9b05688c2b3e6c1f510e527fade682d1a54ff53a5f1d36f13c6ef372fe94f82bbb67ae8584caa73b6a09e667f3bcc908, 0xb4a83442745374f7a1a1e69d8238969dc46267f23b7cf184cde0e9a5e6e9b6379399711f1b102ac3fab372a617bc50b981a8d760c988bc0c015864930e73a8087ef254c93b0794516bca5e01ba07c4824696e78424aadcb0b2938fb47820a1bb5df9a41280bb4aba6ad40bf0575cb612f816e75b9f8efe23a88f6b6bb02019c7, 0x19f12216f368adb188cc3bc3c247c7c567f408b53f4706cb61bbe44b8fd70616166f2aaf2d0a067ddb43a56835a812769ee04b4d2e0395bab39545e6dc99891b),
  (0x19f12216f368adb188cc3bc3c247c7c567f408b53f4706cb61bbe44b8fd70616166f2aaf2d0a067ddb43a56835a812769ee04b4d2e0395bab39545e6dc99891b, 0x22aeb4d743b5f04711171f1e02d666665d7c67985518fe27475a1725cb2194e7856aef7236acb84cb6668960a5dc9a5d7a5ea2118da6c0bc1493522078fb7431206e116f78072d436c174ddcd75acafe7df6a53bf915786a4eb371a13bfba99f505c7ac2a7458303919715aa6432c259a4235c3476c9ed682ad40790646b72af, 0xa62178ed4d06a1af4f5fc947653e071b191778464d85e2c7cc859b26e50333d786d9be0a715f35038fe8d19e1c6523e1a96ab9a2fd1230bc11aba02415375c3b),
  (0xa62178ed4d06a1af4f5fc947653e071b191778464d85e2c7cc859b26e50333d786d9be0a715f35038fe8d19e1c6523e1a96ab9a2fd1230bc11aba02415375c3b, 0xf5e55c2a4167358f5327d02f1260b27113b0abc5922b1e4718736dcb4845f56e44b2bf58c35198d74819e40785223f0352ed8dc2bb2061224864f9b2833ac09ca25ac09c7b31a7c9b9f28a87c9367bf96e5117bd96d8a748db2ed84c0eda8768c3de01670c1879d215cbb5c710dea5c6efc78a143476465e614597d37e77446, 0x5affdd891dbd4e2e34ea7040efc7e4c1e9d4b1a79b39a1c2d5f8c67f61c93f96b05b1cdcf9f62984c5f0e7f57616d7956b169a844a30db509221708cb4735c72),
  (0x5affdd891dbd4e2e34ea7040efc7e4c1e9d4b1a79b39a1c2d5f8c67f61c93f96b05b1cdcf9f62984c5f0e7f57616d7956b169a844a30db509221708cb4735c72, 0x81641e7430986e12969e746159539ca0b68a53ab460952ef9423ad05e77a74e9cf52582d3b07837566be4fc8527e3b2414e41b84857148416e974962c7864db3116a3a52b21e5c7e227ae749f09bb981aca30aa58716c30061d0620904b5618c7991f0c025ec2f31d8b8576c072172295c6d20a4d290e5586cfca61508af3745, 0xdcb2cd3d1545782e4b98a2ede3b7f4200a466bb32a46b52c4ff87d8a74ea36313ea283b5e5bb0fd9fed8f6f4fac31a8ef76fa1a5d5c6db7b7446f1218555fe5b),
  (0xdcb2cd3d1545782e4b98a2ede3b7f4200a466bb32a46b52c4ff87d8a74ea36313ea283b5e5bb0fd9fed8f6f4fac31a8ef76fa1a5d5c6db7b7446f1218555fe5b, 0x5c7e29c3e91f346534f1e3387688520100ab94e333f06c7468707be0bc32d783579018ce60c03346052b86523b19becd6a0cba09f14381d235217045a448b637e501b48872f3c5625c3e644282b430b18198c130e1a22cec8e7a9c6133605649550532b33111e34ec8dbd550c8611b7c9816da026ac53e856772b789b80828a2, 0x31ec8438efc4bf918d7e15c70e14d299044df050e9977dca1428ee00db0cbf76ad2b118fda1462e4a28259f8e38d2854d878e4eaae81bb94d6c15754df8d13c9),
  (0x31ec8438efc4bf918d7e15c70e14d299044df050e9977dca1428ee00db0cbf76ad2b118fda1462e4a28259f8e38d2854d878e4eaae81bb94d6c15754df8d13c9, 0xca954009ac0b931626283a69834ae15542267744f4e85ecad5ad695f90f23a0016474f6561892125982c6021f7857c60ae534cb79e2941c80642aeb2fe257a69c6126326a5a58fa58d1157f2cf7a8a5d1cb98cc7e55c1637b33b917d8b7774b367cae5f54a645e260327adb5bc3155a00c555174b68005256b52263bb6a7dc2c, 0xe6c11d444a2cf63549e797b37803f4d9f3a863b6fa53b741da251ffecbb53b70166ae890968f178b073236a03bc963317af4e5eea704fd04fb652d58da262497),
  (0xe6c11d444a2cf63549e797b37803f4d9f3a863b6fa53b741da251ffecbb53b70166ae890968f178b073236a03bc963317af4e5eea704fd04fb652d58da262497, 0x9ffca5cb3bdb02ac9b9292ec6fb24c42922216bca5a8865d77bbc05f09486459929897b3bf3ac17070d697807e7915582289de265787ad287a2828329e21bda629ad15d7922879a68c88ccbb69a9107a5fcdb27119170540e469aae1f64149f08f86c14b666294941578b8a6674bdd5926b996d7410df6bea443c2a4c10ec161, 0x9fa11cfc00b504377e0cd5fdf96dd1cf7fdd5a3fb99bdcae5af788438f0a27398e08520b60cc09c0c99c7c48d588413d56d1b2781669d6674490c2c26155ad67),
  (0x9fa11cfc00b504377e0cd5fdf96dd1cf7fdd5a3fb99bdcae5af788438f0a27398e08520b60cc09c0c99c7c48d588413d56d1b2781669d6674490c2c26155ad67, 0xec860d0b4250316d723bc84b2693183bb53a3ca2ce378b79813c3588b2b74344660a1a6b9c5c3d27f77c03a41615c686c99b2e78070f841650624110b688318c561cc03ac65ba3a1419a60bb58b451997c50ea1b2ab32899d86a80b510632f64191316134c2ac46f8fe4fc61141baf92864942356a358f7002b27a96f92a14e5, 0x30df0d1319e89a700f64af746f156ed429cb2d6638acdd562d49db414193c5c568566165b64235ac09c66124df500b9e87a61ade16447818047ab5ffb0aef79d),
  (0x30df0d1319e89a700f64af746f156ed429cb2d6638acdd562d49db414193c5c568566165b64235ac09c66124df500b9e87a61ade16447818047ab5ffb0aef79d, 0x387eeaac3402acc1fc2f58325a3f50ff1e173686511712e3db626631bbb1fbb58cb3929287cada9d4773d155344a15c4ed60990e5a9a326ff17952265ba293a88646d922998fb7baf8b868dd24f850118bffca0c889d56de0751538c665fac0688282bd6ae80051e59ed5a1b4da525994561f9632c0b02468db5ab480cf3fabf, 0xf41dea023ee3e79ced637581c45cacf1af89f4dd2f9f28671780d2162a6168238a1b6e607becbd1b830d81542a95fa929c768ecdc62c840d7642dbd52ae31918),
  (0xf41dea023ee3e79ced637581c45cacf1af89f4dd2f9f28671780d2162a6168238a1b6e607becbd1b830d81542a95fa929c768ecdc62c840d7642dbd52ae31918, 0x3f1e61287d43ee913ab868c38738a3b08c15ebc9141fba83f78f3a64451626adfc966c7af03b1bddbaa77d4a4cb252a06c8eba6e8734a2c0bcdaa2c2782d959e236a396b93e2ba14769485b3bd1bf623725870fc3f6a886933d0e43105f87478db30f31dce0af1541a764100ce5b292303e74766957a28e4bd4a45140844254, 0xc87d166b3e836248f2be663b0bbd73b489124e61fa3a2d52522af435dfebd631bc8df37985e03c1dfd6871aa00009eb065de2a291b77aacacc7bc26790b963a7),
  (0xc87d166b3e836248f2be663b0bbd73b489124e61fa3a2d52522af435dfebd631bc8df37985e03c1dfd6871aa00009eb065de2a291b77aacacc7bc26790b963a7, 0x397236f9f13462c5cf26bf8d90f7c6407062aaa082527cc4e2031758b92765d2a57551892968adfa5d113c72955a02c9333955072fcd8bb835e2e814d4161349cb6c92475de6b980874e796a339ff66058e32cbca8f390b76f3be9cb637c8622ac2a8ed8a18f5386c95133c3b9206bd64e5913464220f1410af120141c429073, 0x3ce0a567868726bb5d5c1e1d81d59ca423e92389f789c2bca1426eb54969e03ef4ae34a8f15b11d6cc5647b0696b9087e0a4aa498711ecac36a635b8b009ed2b),
  (0x3ce0a567868726bb5d5c1e1d81d59ca423e92389f789c2bca1426eb54969e03ef4ae34a8f15b11d6cc5647b0696b9087e0a4aa498711ecac36a635b8b009ed2b, 0x5e722bb9454a7b8759136f0ba9ac38fca225ed0ea618a542e67c35e81a5b8776129d5867eaca617f82831c8509b6b48b5d013b90b2d4526ad80faa8b4c32c79c6ab01db989b7706bc215a6e4cc84ed2339dc481a861d83cb1beb82cf21bf7ba1cf422cd8b829089cc54b9a34028b04df24c90fbf6a96506c8d03925e55ab4f99, 0x1aed1bf02bedf8352d898e0468d8bca7a2184e29434657ca72d99b4ea35a70418203bb0ba004c2a1d8eefa0ebceaab20d9c8778ae458a8e149fd73bb2d15efbc),
  (0x1aed1bf02bedf8352d898e0468d8bca7a2184e29434657ca72d99b4ea35a70418203bb0ba004c2a1d8eefa0ebceaab20d9c8778ae458a8e149fd73bb2d15efbc, 0x8330000000000000000000000000000000000000000000000000000000080089f6a44a4192619751ad2bfbd97786f69f870782bc1437a1c5432910070899f9861bf6442bfc650aa3795797e2ae2460699a71a2d491830adf1bfc435559d0a393bdae80abce052688e0c0a6c59369137d6287b5c4c6a89e40905fcafa29b8775, 0x91bb23723c0212596e025bb27c241db47a78d84ce05c560974d75186da80e0edb008aeeb25f720cb65015160cf1d9ce0e351a2b7dd572ca56df4314869015d49)
]

def compSha512 (st blk : HwBytes) : HwBytes :=
  if st.length == 64 && blk.length == 128 then
    let kSt := bytesToNat st
    let kBlk := bytesToNat blk
    match compSha512Rows.find? (fun r => r.1 == kSt && r.2.1 == kBlk) with
    | some (_, _, outNat) => leBytes 64 outNat
    | none => List.replicate 64 0#8
  else List.replicate 64 0#8

def compSha256Rows : List (Nat × Nat × Nat) := [
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x36363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636, 0xf8e04e32824a932ba392418164e5750fdf1228ea90daf2a09725214ff454dead),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c, 0x361d45a6deb82818753434b08e043a725dd8246737c9c5387abb6477d385480f),
  (0xf8e04e32824a932ba392418164e5750fdf1228ea90daf2a09725214ff454dead, 0x2b1507edf1e8d4f38a3da9d3571b67ea7ee5b0606ab27e0c41dfd01e683e373bffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0xc87493f4418f30a35731c97400f76c573c634ddb3f392a266ef10d36f057716e),
  (0xc87493f4418f30a35731c97400f76c573c634ddb3f392a266ef10d36f057716e, 0x6b77c765b6556603b9ce3789d8135f9f017ce167088d37af655befa4f2f390e354151271fa3dd6f78b354f259b6c06bad17e64fc6967b26f10367cff0436cdf3, 0x56c78a787c1827d8b2fcd49199c368904f7bed8a33e0a607fbb7a3bc5ef17819),
  (0x56c78a787c1827d8b2fcd49199c368904f7bed8a33e0a607fbb7a3bc5ef17819, 0x700000000000000000000000000000000000000000000000000000000008086e81a17be5801293d514fe3c93d60943e523b05dc2096ee371824900b0cace4, 0x3ad8cda4837097c45eab082fecbaf978c4b99e3cde578caafd9d2bc7ce313f93),
  (0x361d45a6deb82818753434b08e043a725dd8246737c9c5387abb6477d385480f, 0x3000000000000000000000000000000000000000000000000000000000080a4cdd83ac49770832f08ab5e78f9baec3c9eb9c4aa8c57dec72b9dfd933f31ce, 0x735919ec8086b0842db228a015f4c77c2e9b97e6f64356e90579e0b6df22c6d9),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636da2f6f45b286b0b6961e841b4af1c223d0a1ad18df6075c080d64f33eff014e9, 0x408217d3733212ba6a026aaad57ea749876bb033a693e7a0ccc3657b1ca0046f),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5cb045052fd8ecdadcfc74ee71209ba849bacbc772b50a1faaeabc2559859a7e83, 0xd5d8774008ad0a31b7e137d1d9efe989155cafe509c6c883ee9074970f284a3b),
  (0x408217d3733212ba6a026aaad57ea749876bb033a693e7a0ccc3657b1ca0046f, 0x780300000000000000000000000000008001343230312d524542594b2d534c4154535952435f3635322d4148535f3931353532585f7478655472657073696857, 0x56d2843745597d28215dea6829baf9bb38a501fd24fabf1b79a650bb87c92bdb),
  (0xd5d8774008ad0a31b7e137d1d9efe989155cafe509c6c883ee9074970f284a3b, 0x30000000000000000000000000000000000000000000000000000000000803784d256287d594568ea5d21bbf9ba29fd01a5381bbffa24bb50a679db2bc987, 0x4c11ee612318627c98c85d1d313e499ca37c459e7faa250a3508b431c9867e50),
  (0x408217d3733212ba6a026aaad57ea749876bb033a693e7a0ccc3657b1ca0046f, 0x54535952435f3635322d4148535f3931353532585f747865547265707369685761ee114c7c6218231d5dc8989c493e319e457ca30a25aa7f31b40835507e86c9, 0x7d98713ce929e25f72bc96e31ab42a99a1ac8cf4869112b28be58505465142d5),
  (0x7d98713ce929e25f72bc96e31ab42a99a1ac8cf4869112b28be58505465142d5, 0x7804000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008002343230312d524542594b2d534c41, 0x7899a72c049d6b0338c2afc67e2b7bca9970107ace192ccf0024a198e3fe10b9),
  (0xd5d8774008ad0a31b7e137d1d9efe989155cafe509c6c883ee9074970f284a3b, 0x30000000000000000000000000000000000000000000000000000000000802ca79978036b9d04c6afc238ca7b2b7e7a107099cf2c19ce98a12400b910fee3, 0x86734de4b6588902755fbb4ee6b02413121f627d32a6ee0e2c7be763afe3ec71),
  (0x408217d3733212ba6a026aaad57ea749876bb033a693e7a0ccc3657b1ca0046f, 0x54535952435f3635322d4148535f3931353532585f7478655472657073696857e44d7386028958b64ebb5f751324b0e67d621f120eeea63263e77b2c71ece3af, 0x3eb96befd438fb5b8aaadff31754e6b48098814f723b41f0a9d81f77c7e5268e),
  (0x3eb96befd438fb5b8aaadff31754e6b48098814f723b41f0a9d81f77c7e5268e, 0x7804000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008003343230312d524542594b2d534c41, 0xad75ae2967a3d96b2d37e2d5abad8da4e8e2f1c18d570145bbf6756c203a523b),
  (0xd5d8774008ad0a31b7e137d1d9efe989155cafe509c6c883ee9074970f284a3b, 0x300000000000000000000000000000000000000000000000000000000008029ae75ad6bd9a367d5e2372da48dadabc1f1e2e84501578d6c75f6bb3b523a20, 0xd7c7b14df20e3fcb714f4cddd439dab31730668aa0aa4292121d346c11fbe377),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x363636363636363636363636363636363636363636363636363636363636363657d8277a4a542e152b6bfeaeaa7f0807a8734a953c139c4907823e036648b0ff, 0x7403d2055fc7a3971c4b1ebcfb9b7da0b6689c63d3e2ea3428ef92d23a67a968),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c3db24d10203e447f410194c4c015626dc21920ff5679f6236de854690c22da95, 0x12031960409d0dba6d13f4a5bdaefd9cbada8d05f7cd3c89b388a7cfadfb628f),
  (0x7403d2055fc7a3971c4b1ebcfb9b7da0b6689c63d3e2ea3428ef92d23a67a968, 0x30000000000000000000000000000000000000000000000000000000000800863177d59a538caa707d477ef3bc0bcd29ddbc0055aeeedb3b5795a24d424bf, 0xa2987af212be2f2a2f829a29a97f8e36a0da5b2c00a43b721decf2b16101f51b),
  (0x12031960409d0dba6d13f4a5bdaefd9cbada8d05f7cd3c89b388a7cfadfb628f, 0x3000000000000000000000000000000000000000000000000000000000080f27a98a22a2fbe12299a822f368e7fa92c5bdaa0723ba400b1f2ec1d1bf50161, 0x13542924829c7996de78c7db81e505b1981809bafb9541f752a485db6a39c683),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636121f6225a04faab4edf14ee88733d3b78c3f2eaec177a3cdedb39264b5f00f5c, 0xe78b6185da1845e2e76ea3eaed7a9171eb3c60b162364ee62f5e2e82dcb57921),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c7875084fca25c0de879b2482ed59b9dde65544c4ab1dc9a787d9f80edf9a6536, 0xc733d33e5167995b106ead1389c99d55f5040e8ce68df25a889a4191d42a07f3),
  (0xe78b6185da1845e2e76ea3eaed7a9171eb3c60b162364ee62f5e2e82dcb57921, 0x78020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080017465686374615272657073696857, 0x50a3a39aa8381ed9c21516d039214c21f6fed218897067d378d1d349927635f2),
  (0xc733d33e5167995b106ead1389c99d55f5040e8ce68df25a889a4191d42a07f3, 0x30000000000000000000000000000000000000000000000000000000000809aa3a350d91e38a8d01615c2214c213918d2fef6d367708949d3d178f2357692, 0x489b1e189583d65bd5eafc0eabd97ad6ab027081a3cdf07b4d9aaf42caae2ddc),
  (0xe78b6185da1845e2e76ea3eaed7a9171eb3c60b162364ee62f5e2e82dcb57921, 0x7803000000000000000000000000000080027465686374615272657073696857181e9b485bd683950efcead5d67ad9ab817002ab7bf0cda342af9a4ddc2daeca, 0xa59d63e7803203c25003acc7f538b886fc026430983b49a8138691506ed5d154),
  (0xc733d33e5167995b106ead1389c99d55f5040e8ce68df25a889a4191d42a07f3, 0x3000000000000000000000000000000000000000000000000000000000080e7639da5c2033280c7ac035086b838f5306402fca8493b985091861354d1d56e, 0x3b06b7dc598d52a70985aa1e2191cb06a0bf81320d42c4c4d0f4bb309520ca1e),
  (0xf8e04e32824a932ba392418164e5750fdf1228ea90daf2a09725214ff454dead, 0x4db1c7d7cb3f0ef2dd4c4f71b3da39d48a6630179242aaa06c341d1277e3fb110000000000000000000000000000000000000000000000000000000000000000, 0x429d66cc67efe7b77c38f5df66c30b4ea8f080c7ee0100082756049b27d81eeb),
  (0x429d66cc67efe7b77c38f5df66c30b4ea8f080c7ee0100082756049b27d81eeb, 0x40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080, 0x4afa365c96d6c0551e0c29886c50aeeed0daea317fa4f90bad58b7fa7294679b),
  (0x361d45a6deb82818753434b08e043a725dd8246737c9c5387abb6477d385480f, 0x30000000000000000000000000000000000000000000000000000000000805c36fa4a55c0d69688290c1eeeae506c31eadad00bf9a47ffab758ad9b679472, 0x9678c5dd76ee11dba811bda2a68d76a21029823a67c31888ec8127dc955c4d26),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636ebf34ea0ed27d840948b279e9440bb900cb41f26be2ef551ea11b7da107b6aa3, 0xd57f0f8d9c060782ec25355149a146d065d5ca4c94b9fb868f7508964560e0f5),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c819924ca874db22afee14df4fe2ad1fa66de754cd4449f3b807bddb07a1100c9, 0x94e1e63c71c9ddaa3b4e67ccbeb88dcb17ba8ed5a89a82791c529e6abb37748f),
  (0xd57f0f8d9c060782ec25355149a146d065d5ca4c94b9fb868f7508964560e0f5, 0xb003000000000000008001010000000000000065746164705520726f74616369746e65687475413a3836374d454b4c4d5f31565f414b4351505f6c616e676953, 0xf6b0717d4dc7e464a1e1ec2c2277f948b346bf501c815366d2bfbc7723dd6d27),
  (0x94e1e63c71c9ddaa3b4e67ccbeb88dcb17ba8ed5a89a82791c529e6abb37748f, 0x30000000000000000000000000000000000000000000000000000000000807d71b0f664e4c74d2cece1a148f9772250bf46b36653811c77bcbfd2276ddd23, 0x6db7dba57ed5a661b0525b17c1ae5bdb40de8ce52787edc7f91f7024ce261044),
  (0xd57f0f8d9c060782ec25355149a146d065d5ca4c94b9fb868f7508964560e0f5, 0x746e65687475413a3836374d454b4c4d5f31565f414b4351505f6c616e676953a5dbb76d61a6d57e175b52b0db5baec1e58cde40c7ed872724701ff9441026ce, 0x47a304c6d474f502b01211b5beab1ca4fb24a270f2deaaff002d65a4f290f18b),
  (0x47a304c6d474f502b01211b5beab1ca4fb24a270f2deaaff002d65a4f290f18b, 0xb0040000000000000000000000000000000000000000000000000000000000000000000000000000008002010000000000000065746164705520726f74616369, 0x2e63bef214c17a492d5fdbf8807e3b4efe5488f6289258ed736e6888a9aba4a8),
  (0x94e1e63c71c9ddaa3b4e67ccbeb88dcb17ba8ed5a89a82791c529e6abb37748f, 0x3000000000000000000000000000000000000000000000000000000000080f2be632e497ac114f8db5f2d4e3b7e80f68854feed58922888686e73a8a4aba9, 0x2e15cb5e3458ff05b9233bfe2f9814a79ad2c610bc8e4ff7e841dc65cdb14852),
  (0xf8e04e32824a932ba392418164e5750fdf1228ea90daf2a09725214ff454dead, 0x30000000000000000000000000000000000000000000000000000000000804db1c7d7cb3f0ef2dd4c4f71b3da39d48a6630179242aaa06c341d1277e3fb11, 0x8e2c20b810ed67c32b55b0edc814a96f30dc713d524b29c4b5dc88312adb7371),
  (0x361d45a6deb82818753434b08e043a725dd8246737c9c5387abb6477d385480f, 0x3000000000000000000000000000000000000000000000000000000000080b8202c8ec367ed10edb0552b6fa914c83d71dc30c4294b523188dcb57173db2a, 0x9ea146e103f1b3704acdf05cb7361afd659aa51d1160722e5324ed341bad6ae9),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636d77097a84685c7356ac6fb7ccb2c00812b93ac531844562702db1265df5c9b2d, 0x2e4138db1d47af2c1856fb2e20f485606b8e5e03f7f2dc7c4e9ce700583a7cff),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5cbd1afdc22cefad5f00ac9116a1466aeb41f9c639722e3c4d68b1780fb536f147, 0x17b06a0361ed65c186664489d6df348b93db4db7714061c84a41727e6aedd983),
  (0x2e4138db1d47af2c1856fb2e20f485606b8e5e03f7f2dc7c4e9ce700583a7cff, 0x10030000000000000000000000000000000000000000000000000000008001747261745320206e696168432031562074656863746152205150206c616e676953, 0x5006fe74f9f3fba13d50dfd3a7a0e8fb3cc1f701d8cf5a1a57336585c7da5425),
  (0x17b06a0361ed65c186664489d6df348b93db4db7714061c84a41727e6aedd983, 0x300000000000000000000000000000000000000000000000000000000008074fe0650a1fbf3f9d3df503dfbe8a0a701f7c13c1a5acfd8856533572554dac7, 0x6db08b3c3673f474f7a9a7778aea54fe2d5b9bcc5527d62e44d16703f27226f0),
  (0x2e4138db1d47af2c1856fb2e20f485606b8e5e03f7f2dc7c4e9ce700583a7cff, 0x7261745320206e696168432031562074656863746152205150206c616e6769533c8bb06d74f4733677a7a9f7fe54ea8acc9b5b2d2ed627550367d144f02672f2, 0x26ffc6ad10bc6800b5cfa45f30ff16f081322f633fd153bdebfb973cd1a7263a),
  (0x26ffc6ad10bc6800b5cfa45f30ff16f081322f633fd153bdebfb973cd1a7263a, 0x10040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800274, 0xdbd1146937cd670f1f40eb2b06dfd55d6edda8531a5d01accd6a542ef68f0f9d),
  (0x17b06a0361ed65c186664489d6df348b93db4db7714061c84a41727e6aedd983, 0x30000000000000000000000000000000000000000000000000000000000806914d1db0f67cd372beb401f5dd5df0653a8dd6eac015d1a2e546acd9d0f8ff6, 0x8de967f319204ca999e05d477df232b249fc410baf56b3f290b3557307a98ee2),
  (0x2e4138db1d47af2c1856fb2e20f485606b8e5e03f7f2dc7c4e9ce700583a7cff, 0x7261745320206e696168432031562074656863746152205150206c616e676953f367e98da94c2019475de099b232f27d0b41fc49f2b356af7355b390e28ea907, 0xd0b63dd20ee01c6ef31992a5b4c54c7c119c390a58fdb94879d2a3b989e50c34),
  (0xd0b63dd20ee01c6ef31992a5b4c54c7c119c390a58fdb94879d2a3b989e50c34, 0x10040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800374, 0x81523836011dbe872ea2e4bb708bd1594cc43018c565514399c15bbc72977bb0),
  (0x17b06a0361ed65c186664489d6df348b93db4db7714061c84a41727e6aedd983, 0x30000000000000000000000000000000000000000000000000000000000803638528187be1d01bbe4a22e59d18b701830c44c435165c5bc5bc199b07b9772, 0x357fe107b17d33799e0b9b942c4799e0a4bb099bae75fcc4180b9ca6b78527c1),
  (0xf8e04e32824a932ba392418164e5750fdf1228ea90daf2a09725214ff454dead, 0x3000000000000000000000000000000000000000000000000000000000080f367e98da94c2019475de099b232f27d0b41fc49f2b356af7355b390e28ea907, 0xeea464694b75e23391127d9db415626cf19422e9a3f74b496567fe187e9162b5),
  (0x361d45a6deb82818753434b08e043a725dd8246737c9c5387abb6477d385480f, 0x30000000000000000000000000000000000000000000000000000000000806964a4ee33e2754b9d7d12916c6215b4e92294f1494bf7a318fe6765b562917e, 0x6e8c4d60ba5accd614d992cdfc132c1fd991caf37b269316765dadb6f53c9a6),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636e0f2de30fb9a933d1aaf7b57f704f7e9992aafcb075f8401edec535190ff6559, 0x7b582ac1b468af32e9d61dfdedf420f47215035f9906ee5055d2e734f937d7cc),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c8a98b45a91f0f95770c5113d9d6e9d83f340c5a16d35ee6b8786393bfa950f33, 0x38412ccf48d211e4860e3dac7fd2db4917841b4c2f77d0b034b2f17f8a4b949b),
  (0x7b582ac1b468af32e9d61dfdedf420f47215035f9906ee5055d2e734f937d7cc, 0x20030000000000000000000000000000000000000000000000000080017478654e206e696168432031562074656863746152205150206c616e67695301000000, 0x56c52092d6ef078b768650255b1ec8ee234afc9b805e28f886cd80a58dec9127),
  (0x38412ccf48d211e4860e3dac7fd2db4917841b4c2f77d0b034b2f17f8a4b949b, 0x30000000000000000000000000000000000000000000000000000000000809220c5568b07efd625508676eec81e5b9bfc4a23f8285e80a580cd862791ec8d, 0x37dee381ee2a1f8bff243349472f10dc3d9cb129c517254cd29cadf1e3db7307),
  (0x7b582ac1b468af32e9d61dfdedf420f47215035f9906ee5055d2e734f937d7cc, 0x4e206e696168432031562074656863746152205150206c616e6769530100000081e3de378b1f2aee493324ffdc102f4729b19c3d4c2517c5f1ad9cd20773dbe3, 0x7d4a3e6d7172f545f20370ca240b3f97c8f363ade0172b64c730e3c50a38f020),
  (0x7d4a3e6d7172f545f20370ca240b3f97c8f363ade0172b64c730e3c50a38f020, 0x20040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008002747865, 0x5174e0b8c7746991a27e3e060f7a1081e7bc7dad40f6af6cf4c40a5fa51e2753),
  (0x38412ccf48d211e4860e3dac7fd2db4917841b4c2f77d0b034b2f17f8a4b949b, 0x3000000000000000000000000000000000000000000000000000000000080b8e07451916974c7063e7ea281107a0fad7dbce76caff6405f0ac4f453271ea5, 0x1ac6a7dce187a9a79a4182835aaff12935e076777f0fc5853211f188b5399b21),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636ea81300d9164bb6f289cb33f30fda71704b78996f2f2743b068dc2e628fc16a3, 0x2d59d926e2d1ac85cbaa7aa8e6d89ff323b4aa90099e74701d8f28e490f2986),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c80eb5a67fb0ed10542f6d9555a97cd7d6edde3fc98981e516ce7a88c42967cc9, 0xbb12db4d967171b4b383dfd99c2be8dfd6b0b1677d239cf8afd7af9b915f9f89),
  (0x2d59d926e2d1ac85cbaa7aa8e6d89ff323b4aa90099e74701d8f28e490f2986, 0x8020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008001, 0xce691812fe32dd19c1f998d3d70249fac22675164b4876157a127324252ab93d),
  (0xbb12db4d967171b4b383dfd99c2be8dfd6b0b1677d239cf8afd7af9b915f9f89, 0x3000000000000000000000000000000000000000000000000000000000080121869ce19dd32fed398f9c1fa4902d7167526c21576484b2473127a3db92a25, 0x784f068fc56a3ead8f5bd2830a8706b24476be41f2318fb5b1c88e32647cea47),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636ea91f02c919fb1d7b5b477ac1fc7996c4140d603b3f33949bec7270417ad0f83, 0x8e40a069b9262690cbf2df7d725ed5f7a8bf0d94404ffe00c78fb1444e3847fd),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c80fb9a46fbf5dbbddfde1dc675adf3062b2abc69d9995323d4ad4d6e7dc765e9, 0x92b5c02b3371dd4961f2c206bacb7704db117a33aa50f4acdce27fd100ecb0c8),
  (0x8e40a069b9262690cbf2df7d725ed5f7a8bf0d94404ffe00c78fb1444e3847fd, 0x30000000000000000000000000000000000000000000000000000000000808f064f78ad3e6ac583d25b8fb206870a41be7644b58f31f2328ec8b147ea7c64, 0x26a7ab8d82cbe5475e7af08e3d320ef4bbeaec0b516b22802b0d59bc2962de4d),
  (0x92b5c02b3371dd4961f2c206bacb7704db117a33aa50f4acdce27fd100ecb0c8, 0x30000000000000000000000000000000000000000000000000000000000808daba72647e5cb828ef07a5ef40e323d0beceabb80226b51bc590d2b4dde6229, 0x45287bfdb9834ec13bccb85f16817b4fd33f6fcf2346d9bd69c7c680ec28fc96),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636cb4d1e73f778b58f698efa0d794db720f95909e58bef7015b6f0f15fa0ca1eda, 0x5a74cdaf3161e0d6a3c268dccc0b32b921051535d277ae1051407bcf5c5bead5),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5ca12774199d12dfe503e490671327dd4a9333638fe1851a7fdc9a9b35caa074b0, 0x43f6d3c24f699df9d0430b20f00938bd5e52cf194985f6738b91267549c655a2),
  (0x5a74cdaf3161e0d6a3c268dccc0b32b921051535d277ae1051407bcf5c5bead5, 0x980200000000000000000000000000000000000000000000000000000000000000000000000000000000000080017379654b6567617373654d72657073696857, 0xd7269f544fef277c517b17d1d220fff142fa9c57039500c190feeccb04b7c2c8),
  (0x43f6d3c24f699df9d0430b20f00938bd5e52cf194985f6738b91267549c655a2, 0x3000000000000000000000000000000000000000000000000000000000080549f26d77c27ef4fd1177b51f1ff20d2579cfa42c1009503cbecfe90c8c2b704, 0x93d85c671691ad1f199fab5a03ad4f382b29916b8bd89dc965a2fd4251aaae66),
  (0x5a74cdaf3161e0d6a3c268dccc0b32b921051535d277ae1051407bcf5c5bead5, 0x98030000000000000000000080027379654b6567617373654d72657073696857675cd8931fad91165aab9f19384fad036b91292bc99dd88b42fda26566aeaa51, 0xe94eecebbd75f3c78fb52d41d276de373bb8673c30fb691b1384b3fbd856a825),
  (0x43f6d3c24f699df9d0430b20f00938bd5e52cf194985f6738b91267549c655a2, 0x3000000000000000000000000000000000000000000000000000000000080ebec4ee9c7f375bd412db58f37de76d23c67b83b1b69fb30fbb3841325a856d8, 0xeb8606fa4763c89799687b021ebab713b2b2a42e9def4369778fd9481403bc82),
  (0x5a74cdaf3161e0d6a3c268dccc0b32b921051535d277ae1051407bcf5c5bead5, 0x98030000000000000000000080037379654b6567617373654d72657073696857fa0686eb97c86347027b689913b7ba1e2ea4b2b26943ef9d48d98f7782bc0314, 0x9e43e855ab4514d66d6236e140b53e9fee7b1da99ba3efa14ded54fbf3d7254),
  (0x43f6d3c24f699df9d0430b20f00938bd5e52cf194985f6738b91267549c655a2, 0x3000000000000000000000000000000000000000000000000000000000080853ee4094d51b45a6e23d666e9530b14dab1e7fefa3eba994fd5de1454723dbf, 0x6567b87a3b29bf0d9ba94ca6cc068a02357acab776eedbcb891a0a3f26c36f73),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636cc30b0dda1fe5571344d5eaf25818c28189284845f75d9ab7eefb941b48a3522, 0xc3e4234331a1a7ae6602dd99556f73ae0ab8e6d3eb31e440e4345ca870af4bc0),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5ca65adab7cb943f1b5e2734c54febe64272f8eeee351fb3c11485d32bdee05f48, 0x96806b9391c992f94ed4516c60e1dfd8194914c8ffdd5d83b9b63c7896e1367b),
  (0xc3e4234331a1a7ae6602dd99556f73ae0ab8e6d3eb31e440e4345ca870af4bc0, 0xac8bff0348b0c032b515e585e882aa28244c58ceadfb6f2c8876f3506df7053c01432d659f6956d79efdb84cf363bd3effef89cb39f4513184d598b479f75a05, 0x2d02bfa2e84dcf789bdae2690a26eafa91965824a75ba32bf009c211b464f5b0),
  (0x2d02bfa2e84dcf789bdae2690a26eafa91965824a75ba32bf009c211b464f5b0, 0x101252a7c6c2aec8510f4291f9dd3397ce8a4fc1022001800103fd3bf370a6f0d82bce23a6bc81073a3968030a12fd4407213598fb0a385fc5b05210a44627f, 0xbb44e90a5aa47f3119ad580ba750f6ecb3d9a535e82619aa3e16cd78083fc78d),
  (0xbb44e90a5aa47f3119ad580ba750f6ecb3d9a535e82619aa3e16cd78083fc78d, 0x9d4c8b7a102f3e5d00016b5a4f3e2d1c0b9a5f4e4d3b2e1c6f8a0024320b8cdd0fe997174ce780528bf9ecc13020f000fc44144b1638e063bc8c1218a5000101, 0x4bebb9ff03f6f987db7d934b1c4f3f0a4b9ee781343af2308ec055e870602896),
  (0x4bebb9ff03f6f987db7d934b1c4f3f0a4b9ee781343af2308ec055e870602896, 0x4808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008001f6e5d4c3b2a10f8e, 0xb9e96600149a17975dda5703dc10e51946019fec97c0687c1d06f8910ef559d6),
  (0x96806b9391c992f94ed4516c60e1dfd8194914c8ffdd5d83b9b63c7896e1367b, 0x30000000000000000000000000000000000000000000000000000000000800066e9b997179a140357da5d19e510dcec9f01467c68c09791f8061dd659f50e, 0xc328197003979973f8d1aa90dcc5d9bb24fc8f6e08dab8c1c7cfaa39e92926fb),
  (0x2d59d926e2d1ac85cbaa7aa8e6d89ff323b4aa90099e74701d8f28e490f2986, 0x8020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008002, 0xd771bf584366f9a9e8a2c7f0b011a7ace667c426337888c675d53f2e5bd7e91d),
  (0xbb12db4d967171b4b383dfd99c2be8dfd6b0b1677d239cf8afd7af9b915f9f89, 0x300000000000000000000000000000000000000000000000000000000008058bf71d7a9f96643f0c7a2e8aca711b026c467e6c68878332e3fd5751de9d75b, 0x241f6e2a0c683d2cf5090ddab94d83bd838fb9c13c938adbf90874f683c22513),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x36363636363636363636363636363636363636363636363636363636363636362e28ad7e6de0b5a338cadce3e04cef9db746349d4dc6fb957499ac7bea1b98fc, 0x3ff95ca5a0dc185c87209cdd205c156903d92b5e4397dce61e374992f0f695bc),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c4442c714078adfc952a0b6898a2685f7dd2c5ef727ac91ff1ef3c6118071f296, 0x6ab57a3f1c0bd72e9c58972e3df65b75e73b080412b315902b90bc5028b4fad),
  (0x3ff95ca5a0dc185c87209cdd205c156903d92b5e4397dce61e374992f0f695bc, 0x30000000000000000000000000000000000000000000000000000000000801edc8f428b3201dcd6286cac92f8611914a3a83f06e9834a6b2a62b6889fc766, 0x9857aded25958198d43268dc21feea8acaa6c014a0afac3d2be0c4731efd02c5),
  (0x6ab57a3f1c0bd72e9c58972e3df65b75e73b080412b315902b90bc5028b4fad, 0x3000000000000000000000000000000000000000000000000000000000080edad579898819525dc6832d48aeafe2114c0a6ca3dacafa073c4e02bc502fd1e, 0x1d97b462c9baa931d8c548ac65365edb2d25168a45ee1f510a2012b2de7f64c0),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x36363636363636363636363636363636363636363636363636363636363636365482a12b079f8cff9a7ef3eeed680053bc20131b6729d8738424163cf65249e8, 0xec2fddaabb722762fd730368e6732e96dd7d1dab03a5a1dc794d75409dad4644),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c3ee8cb416df5e695f014998487026a39d64a79710d43b219ee4e7c569c382382, 0xe44b18e6f2d3c62c882ecc91507dbdd415c5ecd7ca5618203b3a595c44699fe5),
  (0xec2fddaabb722762fd730368e6732e96dd7d1dab03a5a1dc794d75409dad4644, 0x78020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080017465686374615272657073696857, 0xf44aa5a83a19a0ea7f334e397e9058f7ab16de0f93274794a851b73e2a2bd615),
  (0xe44b18e6f2d3c62c882ecc91507dbdd415c5ecd7ca5618203b3a595c44699fe5, 0x3000000000000000000000000000000000000000000000000000000000080a8a54af4eaa0193a394e337ff758907e0fde16ab944727933eb751a815d62b2a, 0xbb2f5ea848356fdaa38c4ced7828dc7e8fc249678dad40d11ee499ad5e959002),
  (0xec2fddaabb722762fd730368e6732e96dd7d1dab03a5a1dc794d75409dad4644, 0x7803000000000000000000000000000080027465686374615272657073696857a85e2fbbda6f3548ed4c8ca37edc28786749c28fd140ad8dad99e41e0290955e, 0x1b2d4587f0c92e31c2fc691fa31eb2d63c794450d09780cad6282eb9880be754),
  (0xe44b18e6f2d3c62c882ecc91507dbdd415c5ecd7ca5618203b3a595c44699fe5, 0x300000000000000000000000000000000000000000000000000000000008087452d1b312ec9f01f69fcc2d6b21ea35044793cca8097d0b92e28d654e70b88, 0xda88542333e21c90476f13fe1e8f456d0148045e0d194e28945368ee7a945503),
  (0xc87493f4418f30a35731c97400f76c573c634ddb3f392a266ef10d36f057716e, 0x7707b1a8208d0492fce5307d23fe5b81e8943766928eb6d041f35cad4df471880a2243eb8bcdb7e8ea5b789c1e176f460f7589421241238bef591bd268baa0d8, 0x54c3280af336c64a4780f47a7b6ace23a11b0b119c88469ad6d2ed88da12b8de),
  (0x54c3280af336c64a4780f47a7b6ace23a11b0b119c88469ad6d2ed88da12b8de, 0x7000000000000000000000000000000000000000000000000000000000080b19965264efb6794bbdaed8cc7eaa4c2b2e958dfced7345859e40a0e80308b9a, 0x9d35ebc5d9281ce999b1f5da52af831e480bf7f275c4f25e220929198cad4e6b),
  (0x361d45a6deb82818753434b08e043a725dd8246737c9c5387abb6477d385480f, 0x3000000000000000000000000000000000000000000000000000000000080c5eb359de91c28d9daf5b1991e83af52f2f70b485ef2c475192909226b4ead8c, 0x52d96937057e7c3594ac117afec372cde6853fcda87dfafd234525e1aa6c42bf),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636015fef64034a48334c279aa2fb44f5c8fb09b3d0cbcc4b9ed713731589745a9c, 0xd1e60d9c601bba16f8689a2b6dcf54459d877a5c8b603f079fd3e94740fedd2f),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c6b35850e69202259264df0c8912e9fa29163d9baa1a621f4bd79197fe31e30f6, 0x61bf52fd96a546fe85c50e48c281b3248dc2bb536fb86a99028686d234e3893c),
  (0xd1e60d9c601bba16f8689a2b6dcf54459d877a5c8b603f079fd3e94740fedd2f, 0x780300000000000000000000000000008001343230312d524542594b2d534c4154535952435f3635322d4148535f3931353532585f7478655472657073696857, 0xb6643310f5925d3b8965c44dd18d859d061dd9f6a6bccf54a3c6e2bffecd7aee),
  (0x61bf52fd96a546fe85c50e48c281b3248dc2bb536fb86a99028686d234e3893c, 0x3000000000000000000000000000000000000000000000000000000000080103364b63b5d92f54dc465899d858dd1f6d91d0654cfbca6bfe2c6a3ee7acdfe, 0x323099ff6cd65a66ba572b696e3db41d51787234b57794be5809700574e9af1a),
  (0xd1e60d9c601bba16f8689a2b6dcf54459d877a5c8b603f079fd3e94740fedd2f, 0x54535952435f3635322d4148535f3931353532585f7478655472657073696857ff993032665ad66c692b57ba1db43d6e34727851be9477b5057009581aafe974, 0x851f499d0d1c5be464df166df59c09963d141c457fef2d4c4aba78fcb2ea98b2),
  (0x851f499d0d1c5be464df166df59c09963d141c457fef2d4c4aba78fcb2ea98b2, 0x7804000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008002343230312d524542594b2d534c41, 0x37eca9479e0e04ff7ea3a70658c5db4b4af8b094ba715f65abf44d6519479357),
  (0x61bf52fd96a546fe85c50e48c281b3248dc2bb536fb86a99028686d234e3893c, 0x300000000000000000000000000000000000000000000000000000000008047a9ec37ff040e9e06a7a37e4bdbc55894b0f84a655f71ba654df4ab57934719, 0xe62fb2057b34543c308e34e80aa3f0fcad26166bf82b8053c7f73c10f6f89823),
  (0xd1e60d9c601bba16f8689a2b6dcf54459d877a5c8b603f079fd3e94740fedd2f, 0x54535952435f3635322d4148535f3931353532585f747865547265707369685705b22fe63c54347be8348e30fcf0a30a6b1626ad53802bf8103cf7c72398f8f6, 0x11277c05183dd18a67180fdcdb4d9a2e4c0857e3ace287e3e0983c5f05ad61eb),
  (0x11277c05183dd18a67180fdcdb4d9a2e4c0857e3ace287e3e0983c5f05ad61eb, 0x7804000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008003343230312d524542594b2d534c41, 0x27cd0f39007397f2d59bef673b9e78840192f22cc64450b60ba1563dbeb3370c),
  (0x61bf52fd96a546fe85c50e48c281b3248dc2bb536fb86a99028686d234e3893c, 0x3000000000000000000000000000000000000000000000000000000000080390fcd27f297730067ef9bd584789e3b2cf29201b65044c63d56a10b0c37b3be, 0x1b539b57e4d4e937e7bb1ba3b8a1de4abc8e5b83e711ce8ec3ed2ae8c39436e6),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636c9af0604506ce05a5f1d618c2b820b5802444e6788a2418333463f6e2c99df42, 0xb487e3165bfd4b505e97f695401575e725899bf52cd55a05b560696262fd284b),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5ca3c56c6e3a068a3035770be641e86132682e240de2c82be9592c550446f3b528, 0xba39f493b0151cb7071788c34f15564d61c37c6604664975b0f1a4de61e2d343),
  (0xb487e3165bfd4b505e97f695401575e725899bf52cd55a05b560696262fd284b, 0x30000000000000000000000000000000000000000000000000000000000805188500b822d529fe65cfbc87e52c5607f92b09f3dc64254c47aed0d73c65ebc, 0xa89aea3b033dd0705c4500ff1eda1d90a40c2b95f0d3a3c041cb9472777067c7),
  (0xba39f493b0151cb7071788c34f15564d61c37c6604664975b0f1a4de61e2d343, 0x30000000000000000000000000000000000000000000000000000000000803bea9aa870d03d03ff00455c901dda1e952b0ca4c0a3d3f07294cb41c7677077, 0xc08d9c6a290836050f12c6683743d2743f646d63a4bb98ad11d40a5ab2507c15),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x36363636363636363636363636363636363636363636363636363636363636365caabbf633003e1f5ef0243942e47501555b52099bae8d926c3ce227234a6684, 0x5a3245af79453650000c85d3047d153c62bdfb290e9867936be231f9c644c38e),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c36c0d19c596a5475349a4e53288e1f6b3f313863f1c4e7f80656884d49200cee, 0x9e3ca6cff0d5035c8b672d4fa24b725f1f2489f39eaf3d286a99405d0f9ab463),
  (0x5a3245af79453650000c85d3047d153c62bdfb290e9867936be231f9c644c38e, 0x78020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080017465686374615272657073696857, 0x3dd2926b16d0216f26df71844cfdb3febba76cbb9a74ce6d04af5c799d7a90f0),
  (0x9e3ca6cff0d5035c8b672d4fa24b725f1f2489f39eaf3d286a99405d0f9ab463, 0x30000000000000000000000000000000000000000000000000000000000806b92d23d6f21d0168471df26feb3fd4cbb6ca7bb6dce749a795caf04f0907a9d, 0xa450c884e600185935a9514d73cfa30b9ffb7d4c9f9da7fe77da48a2e9e2c8ce),
  (0x5a3245af79453650000c85d3047d153c62bdfb290e9867936be231f9c644c38e, 0x780300000000000000000000000000008002746568637461527265707369685784c850a4591800e64d51a9350ba3cf734c7dfb9ffea79d9fa248da77cec8e2e9, 0xdc4eef35ba7d001fa41166f49d37dc6b38a51a3de5590bc4b4729ffb95a39ffc),
  (0x9e3ca6cff0d5035c8b672d4fa24b725f1f2489f39eaf3d286a99405d0f9ab463, 0x300000000000000000000000000000000000000000000000000000000008035ef4edc1f007dbaf46611a46bdc379d3d1aa538c40b59e5fb9f72b4fc9fa395, 0xee83bd556a497074b40a8e058c606198b8076ae9d8c497884c1bf84bffd1d6b7),
  (0xf8e04e32824a932ba392418164e5750fdf1228ea90daf2a09725214ff454dead, 0x579b531b37e9d4e4a31bbbe74adea1b8835b8ebc8ece11e7e82aedc3e63694c30000000000000000000000000000000000000000000000000000000000000000, 0x9b0abe49d472662f37bcf9f5d5753e4567a15f4da33ba3fb828458152a029d6f),
  (0x9b0abe49d472662f37bcf9f5d5753e4567a15f4da33ba3fb828458152a029d6f, 0x40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080, 0xb14d0acb6b3dd3d190795b212f913cb75842ece5f9d4c1cbe67f13ad3ec1b721),
  (0x361d45a6deb82818753434b08e043a725dd8246737c9c5387abb6477d385480f, 0x3000000000000000000000000000000000000000000000000000000000080cb0a4db1d1d33d6b215b7990b73c912fe5ec4258cbc1d4f9ad137fe621b7c13e, 0x33a258b3738c43d7cbbc9544b29a2be61ab8c45041bfda6e173ac6cec5497b8a),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636856e9405e175ba4572a38afdd01dac8466f28e2c58ec8977f8f00c21bc4d7ff3, 0x3ed821c47301e0e24304099da4a619d72edb77dfbebfe1bf4c76616932c63d7e),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5cef04fe6f8b1fd02f18c9e097ba77c6ee0c98e4463286e31d929a664bd6271599, 0x2d65ee5929f3b06a4fef431edcea2c2662e8f99caa8d2781143a42dfac954891),
  (0x3ed821c47301e0e24304099da4a619d72edb77dfbebfe1bf4c76616932c63d7e, 0xb003000000000000008001010000000000000065746164705520726f74616369746e65687475413a3836374d454b4c4d5f31565f414b4351505f6c616e676953, 0x13f1391597a7560ba111fd5ab40b182eed720538a1081e41a0f0040bee03f98c),
  (0x2d65ee5929f3b06a4fef431edcea2c2662e8f99caa8d2781143a42dfac954891, 0x30000000000000000000000000000000000000000000000000000000000801539f1130b56a7975afd11a12e180bb4380572ed411e08a10b04f0a08cf903ee, 0x665dcab41e50ccc6c7d60378ce596241016a938f41bb0dd212dbe1498df9a6c6),
  (0x3ed821c47301e0e24304099da4a619d72edb77dfbebfe1bf4c76616932c63d7e, 0x746e65687475413a3836374d454b4c4d5f31565f414b4351505f6c616e676953b4ca5d66c6cc501e7803d6c7416259ce8f936a01d20dbb4149e1db12c6a6f98d, 0xc2e0653727e38f48cff282ec3e1af00d05903e89c2c1acc6dc70067ba39ba180),
  (0xc2e0653727e38f48cff282ec3e1af00d05903e89c2c1acc6dc70067ba39ba180, 0xb0040000000000000000000000000000000000000000000000000000000000000000000000000000008002010000000000000065746164705520726f74616369, 0xaa56eef843c34d6bc1b18228f8bc7b8667762f53b604270f9196065558a3dd62),
  (0x2d65ee5929f3b06a4fef431edcea2c2662e8f99caa8d2781143a42dfac954891, 0x3000000000000000000000000000000000000000000000000000000000080f8ee56aa6b4dc3432882b1c1867bbcf8532f76670f2704b65506969162dda358, 0xf93195dabcd878ccd747222f0c953439a127370d3b234b4e27313a5ffb3bb311),
  (0xf8e04e32824a932ba392418164e5750fdf1228ea90daf2a09725214ff454dead, 0x3000000000000000000000000000000000000000000000000000000000080579b531b37e9d4e4a31bbbe74adea1b8835b8ebc8ece11e7e82aedc3e63694c3, 0x49e027903103c7270ded63a258b4bfcdaf4092f99265a54f79ee33496c988927),
  (0x361d45a6deb82818753434b08e043a725dd8246737c9c5387abb6477d385480f, 0x30000000000000000000000000000000000000000000000000000000000809027e04927c70331a263ed0dcdbfb458f99240af4fa565924933ee792789986c, 0x6567835f0f443671b41a37f06a4a5f30b6b96ccea9ff0be6c1433fb0c3ef53d9),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x363636363636363636363636363636363636363636363636363636363636363669b5515347007239c6012c8206697c5cf85a8f80d03dc99f860975f7ef65d9f5, 0xa42a953c6804a417d14c0337e4ba91942134f97a923d3ec027c3efdd08d27c50),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c03df3b392d6a1853ac6b46e86c0316369230e5eaba57a3f5ec631f9d850fb39f, 0xabde521684408febd353ce04c39cfc7308f3023d4ebe57df32ac9239923d0302),
  (0xa42a953c6804a417d14c0337e4ba91942134f97a923d3ec027c3efdd08d27c50, 0x10030000000000000000000000000000000000000000000000000000008001747261745320206e696168432031562074656863746152205150206c616e676953, 0xb3fbcd82c0ef1b86d2025e920819d5234287154af3e63afe2496d19486c181f),
  (0xabde521684408febd353ce04c39cfc7308f3023d4ebe57df32ac9239923d0302, 0x3000000000000000000000000000000000000000000000000000000000080d8bc3f0bb8f10e2ce925206d529d812054712834af633eaf196d49e21f186c48, 0xc97b57beceadb659ec9f8e4895dbae70cfc565850a5fe3beb598c5701392ab06),
  (0xa42a953c6804a417d14c0337e4ba91942134f97a923d3ec027c3efdd08d27c50, 0x7261745320206e696168432031562074656863746152205150206c616e676953be577bc959b6adce488e9fec70aedb958565c5cfbee35f0a70c598b506ab9213, 0xdd280afe1a5607fef854ea7d0cde62661d346e12bf52812dfdd6d171c7897081),
  (0xdd280afe1a5607fef854ea7d0cde62661d346e12bf52812dfdd6d171c7897081, 0x10040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800274, 0xa28f827db4b3623d2c0166d0ba1c0ce25ed26dc8534f98b8cf04e0ccfa13fbd6),
  (0xabde521684408febd353ce04c39cfc7308f3023d4ebe57df32ac9239923d0302, 0x30000000000000000000000000000000000000000000000000000000000807d828fa23d62b3b4d066012ce20c1cbac86dd25eb8984f53cce004cfd6fb13fa, 0xb5c6768d3c623d9694a5a990b457421c9f7c7a2137fbdaeb4c842762cf5e3792),
  (0xa42a953c6804a417d14c0337e4ba91942134f97a923d3ec027c3efdd08d27c50, 0x7261745320206e696168432031562074656863746152205150206c616e6769538d76c6b5963d623c90a9a5941c4257b4217a7c9febdafb376227844c92375ecf, 0x5ff32fbbf380b52e55602436f0f72b8063c5e4606a563bb22ad0d60499cf665a),
  (0x5ff32fbbf380b52e55602436f0f72b8063c5e4606a563bb22ad0d60499cf665a, 0x10040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800374, 0x8a99fb99899f5b530767a659c666e07307f3e1a9f77e24a71ddec0ee48b042fd),
  (0xabde521684408febd353ce04c39cfc7308f3023d4ebe57df32ac9239923d0302, 0x300000000000000000000000000000000000000000000000000000000008099fb998a535b9f8959a6670773e066c6a9e1f307a7247ef7eec0de1dfd42b048, 0x19d0c69b64973a8a8812527c7156a9e0e1d0b63a1ac44a45bb5ced756f583be3),
  (0xf8e04e32824a932ba392418164e5750fdf1228ea90daf2a09725214ff454dead, 0x30000000000000000000000000000000000000000000000000000000000808d76c6b5963d623c90a9a5941c4257b4217a7c9febdafb376227844c92375ecf, 0x56b7e9fa8ceed1a46b7173b2f2d2a50ea932e5a05aeac3b26a2ef6d0b4dadc7b),
  (0x361d45a6deb82818753434b08e043a725dd8246737c9c5387abb6477d385480f, 0x3000000000000000000000000000000000000000000000000000000000080fae9b756a4d1ee8cb273716b0ea5d2f2a0e532a9b2c3ea5ad0f62e6a7bdcdab4, 0x40f05d57780a98fea3334e19bbb200fdf751abaf3ea10b5efb1c521cfaffa783),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636616bc676c8ae3c4e2f780595cb36848d999d67c1683d97082a642acdb591c9cc, 0xa770a3d1e407f484f891ed4b86811d61592d56f802f4b569e6d6f39acbe607a8),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c0b01ac1ca2c4562445126fffa15ceee7f3f70dab0257fd62400e40a7dffba3a6, 0x9dde90062bcfa16314b4f86e434c86f4fe0d458b7b8077c7d0ea8420799a16fc),
  (0xa770a3d1e407f484f891ed4b86811d61592d56f802f4b569e6d6f39acbe607a8, 0x20030000000000000000000000000000000000000000000000000080017478654e206e696168432031562074656863746152205150206c616e67695301000000, 0x5ea7bec1c2300a7d90dee7869f08d0ac9f2fea77a271db31c737903aa3fa6da4),
  (0x9dde90062bcfa16314b4f86e434c86f4fe0d458b7b8077c7d0ea8420799a16fc, 0x3000000000000000000000000000000000000000000000000000000000080c1bea75e7d0a30c286e7de90acd0089f77ea2f9f31db71a23a9037c7a46dfaa3, 0xdb988f4aaca7494fe6d43978fdf7ef4fd08c34a34c2655baffd3389a379b48f8),
  (0xa770a3d1e407f484f891ed4b86811d61592d56f802f4b569e6d6f39acbe607a8, 0x4e206e696168432031562074656863746152205150206c616e676953010000004a8f98db4f49a7ac7839d4e64feff7fda3348cd0ba55264c9a38d3fff8489b37, 0xd08100fbb931aa95bc6195720dd7a3d973e0af761225e2f6989387157c77049c),
  (0xd08100fbb931aa95bc6195720dd7a3d973e0af761225e2f6989387157c77049c, 0x20040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008002747865, 0xdd3324d3fadfc9743457ab118c256f4f9ad7d71b3d8ce8686f53bb6d2587faa),
  (0x9dde90062bcfa16314b4f86e434c86f4fe0d458b7b8077c7d0ea8420799a16fc, 0x30000000000000000000000000000000000000000000000000000000000804d32d30d97fcad3fb17a4543f456c218717dadf986ced8b3b63bf586aa7f58d2, 0x443a0b8af7f6f7c6b3c62e1eac60619c54fe14425e7ef3b6ac5807147565cfed),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636638bb5d842467f5c33b83c82ae5756badf5c318ebea1f2ee7dce2d7a81e0e7c9, 0x702115cc24638a72116426be40d273adc908568bb67db452d75e33cf92765516),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c09e1dfb2282c153659d256e8c43d3cd0b5365be4d4cb988417a44710eb8a8da3, 0x15824443390a77322e72faa4f6ed2547e01fd8ff3e57ee9fcc52a71f6ec21cb9),
  (0x702115cc24638a72116426be40d273adc908568bb67db452d75e33cf92765516, 0x8020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008001, 0x478551e1b392d7efc2c7806731a1f6d01c802faea0df414fdb49981a39ea23a9),
  (0x15824443390a77322e72faa4f6ed2547e01fd8ff3e57ee9fcc52a71f6ec21cb9, 0x3000000000000000000000000000000000000000000000000000000000080e1518547efd792b36780c7c2d0f6a131ae2f801c4f41dfa01a9849dba923ea39, 0x3846661b585f32d7926e3ade11c6194e9c355b4f9291fc9349d99fc104cbfe36),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636bc3d0c72f0c1c0c12818f085aa57569a7422c86280c5486822316e9adbf95343, 0x3d984a6f6b976a7a379308a9a2d919db16b426d25c2706185b959911190b242e),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5cd65766189aabaaab42729aefc03d3cf01e48a208eaaf2202485b04f0b1933929, 0xb339a4d83f93a25badbf1a11df8a944a9a0161745eb8ddee590ffc327e31527b),
  (0x3d984a6f6b976a7a379308a9a2d919db16b426d25c2706185b959911190b242e, 0x30000000000000000000000000000000000000000000000000000000000801b664638d7325f58de3a6e924e19c6114f5b359c93fc9192c19fd94936fecb04, 0x48b4b9608f4230d44fe9cfc00fbbd515a666b09d8721a9c3b0ab59e040f616e4),
  (0xb339a4d83f93a25badbf1a11df8a944a9a0161745eb8ddee590ffc327e31527b, 0x300000000000000000000000000000000000000000000000000000000008060b9b448d430428fc0cfe94f15d5bb0f9db066a6c3a92187e059abb0e416f640, 0xdc3919f076005aba5c96ef9c16aee9ec3adb9b4b30fd45aaae0a1311bb36e204),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636c62f0fea8c6c3640aad9a06adadf98207daded0c9c73cb0627253c9832d4008d, 0xc3b76d39c08e5a5a0b85d07f9f736f3415a4c82b77cd2be18421f19a8b695cd7),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5cac456580e6065c2ac0b3ca00b0b5f24a17c78766f619a16c4d4f56f258be6ae7, 0x989c2c9ab50564143d4cdd652db743ac37f9017806d1229d114f0aaa2f865c11),
  (0xc3b76d39c08e5a5a0b85d07f9f736f3415a4c82b77cd2be18421f19a8b695cd7, 0x980200000000000000000000000000000000000000000000000000000000000000000000000000000000000080017379654b6567617373654d72657073696857, 0x10780c1c2e53a8c8bb3f9be399835ab8c2144895fdbdbd170b9a72ccb948b915),
  (0x989c2c9ab50564143d4cdd652db743ac37f9017806d1229d114f0aaa2f865c11, 0x30000000000000000000000000000000000000000000000000000000000801c0c7810c8a8532ee39b3fbbb85a8399954814c217bdbdfdcc729a0b15b948b9, 0x34f09ae6580a53278c53c10c9709313bfbcb214a92eefb15d38edd901a022a97),
  (0xc3b76d39c08e5a5a0b85d07f9f736f3415a4c82b77cd2be18421f19a8b695cd7, 0x98030000000000000000000080027379654b6567617373654d72657073696857e69af03427530a580cc1538c3b3109974a21cbfb15fbee9290dd8ed3972a021a, 0xcd54d2cb6e1c0a696a9117493a0a1ef4e7ee37454700bfc8d11e9e7c44da4221),
  (0x989c2c9ab50564143d4cdd652db743ac37f9017806d1229d114f0aaa2f865c11, 0x3000000000000000000000000000000000000000000000000000000000080cbd254cd690a1c6e4917916af41e0a3a4537eee7c8bf00477c9e1ed12142da44, 0xf255611deeda733d820b489ecbcb81241c27f427c5f7fda45c1e8d43900d0a3),
  (0xc3b76d39c08e5a5a0b85d07f9f736f3415a4c82b77cd2be18421f19a8b695cd7, 0x98030000000000000000000080037379654b6567617373654d726570736968571156250f33a7edde89b420d812b8bcec427fc241da7f5f7cd4e8c145a3d00039, 0xa9ec944da3cacaceacbd5021a5a3a0d92571aec8ca727e69810c0b4660bd7e09),
  (0x989c2c9ab50564143d4cdd652db743ac37f9017806d1229d114f0aaa2f865c11, 0x30000000000000000000000000000000000000000000000000000000000804d94eca9cecacaa32150bdacd9a0a3a5c8ae7125697e72ca460b0c81097ebd60, 0x1be1e0a963bafb0b38dec142d0d1a9f67ddce8dc2baf78fff71aad9a610e77d),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636276013390591dbe8bf8216ee248e8ada7449f477ec49694ae2def77395e6360f, 0x37f11f3950ce3741a99cad370db778b6ab004eeffca77a8578a35fc835b5209b),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c4d0a79536ffbb182d5e87c844ee4e0b01e239e1d8623032088b49d19ff8c5c65, 0x731d5337e25305f231ae7ceb776dd6afd0f07efce35b06b1ba200f9550e05fc1),
  (0x37f11f3950ce3741a99cad370db778b6ab004eeffca77a8578a35fc835b5209b, 0xac8bff0348b0c032b515e585e882aa28244c58ceadfb6f2c8876f3506df7053c01432d659f6956d79efdb84cf363bd3effef89cb39f4513184d598b479f75a05, 0xc62dac27eff0a60c967c0ab8d3cf7365abe3db5a91caf1f56635a84abe4ec04e),
  (0xc62dac27eff0a60c967c0ab8d3cf7365abe3db5a91caf1f56635a84abe4ec04e, 0x101252ad153ffaca7b73d3f808747a77c58d1f61022001800104ae020f0133ecd4a8abe6ff58f162cef8c18ef9d7411918dad639572eb5d162705210a44627f, 0xa917d23d9543860f32db814f49206b564757f44c8513878f81f3c071a9d50cbb),
  (0xa917d23d9543860f32db814f49206b564757f44c8513878f81f3c071a9d50cbb, 0x9d4c8b7a102f3e5d00016b5a4f3e2d1c0b9a5f4e4d3b2e1c6f8a002432b03846914a49bb4426876200e8a712484bb2386963aab9bcd113547372b8d671000101, 0x9a2bf185171f11e6f46b38427211bdd44f8ecb39ee1a2d0870f41d0cfb492b74),
  (0x9a2bf185171f11e6f46b38427211bdd44f8ecb39ee1a2d0870f41d0cfb492b74, 0x4808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008001f6e5d4c3b2a10f8e, 0xc9cddc5dcd533fae30d0f348bfe3edbbce01bd01205e7b214254db4bb4ebd063),
  (0x731d5337e25305f231ae7ceb776dd6afd0f07efce35b06b1ba200f9550e05fc1, 0x30000000000000000000000000000000000000000000000000000000000805ddccdc9ae3f53cd48f3d030bbede3bf01bd01ce217b5e204bdb544263d0ebb4, 0xd7694fc52c8f26d0b02b1162ca935d28522cff585ab179982712bcb719bd0c2d),
  (0x702115cc24638a72116426be40d273adc908568bb67db452d75e33cf92765516, 0x8020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008002, 0x65e6a19dc75431ccad7b2486fa481c7aa95ad3bd34d48fe927f985ae75082444),
  (0x15824443390a77322e72faa4f6ed2547e01fd8ff3e57ee9fcc52a71f6ec21cb9, 0x30000000000000000000000000000000000000000000000000000000000809da1e665cc3154c786247bad7a1c48fabdd35aa9e98fd434ae85f92744240875, 0x34420e81858fb2e29959a75f3e705598d67f1aa5a6c878ebaa289d978ace84d7),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636b2fe66926f2e36d07b679f033d95f9457a4bcda9c891aba9947eec41f8fed4df, 0xd9eb6e0c91a19d2cda72bbea13e711d4a2f0e5e25750c30e7bdefa5a939b3a9),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5cd8940cf805445cba110df56957ff932f1021a7c3a2fbc1c3fe14862b9294beb5, 0x5fd816bcd0abc42bf22c0423429897d83d0cad64922b59a59eca385d2b866451),
  (0xd9eb6e0c91a19d2cda72bbea13e711d4a2f0e5e25750c30e7bdefa5a939b3a9, 0x30000000000000000000000000000000000000000000000000000000000806405a2df8adffc0ad3751f0557dddbbecf6918b6de21da8a256c5def3434b187, 0x7dcbcd764a956dca5b78c7464d26fe2913364d4c5ca46bb067b7b06b35e5ee48),
  (0x5fd816bcd0abc42bf22c0423429897d83d0cad64922b59a59eca385d2b866451, 0x300000000000000000000000000000000000000000000000000000000008076cdcb7dca6d954a46c7785b29fe264d4c4d3613b06ba45c6bb0b76748eee535, 0xe0b4f2adf162a7c02c87a837639410f6cc92120957c75b4aaea400783afdb80e),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x36363636363636363636363636363636363636363636363636363636363636369bc482d6f69154c7019eb11ac026a2553f24a4fa7c6df1614e369298388ecb0c, 0x8c912ca7b176a08a3cefd82ae47ee2373f76c2bc1e1800383aa27e5041daaaee),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5cf1aee8bc9cfb3ead6bf4db70aa4cc83f554ece9016079b0b245cf8f252e4a166, 0xce0f3bd2042798c6f726271b56cebd4ccadc31b217ed1eb9b5bc9cce2912118),
  (0x8c912ca7b176a08a3cefd82ae47ee2373f76c2bc1e1800383aa27e5041daaaee, 0x78020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080017465686374615272657073696857, 0x2f6a37e192bd97e77deb0dbb72580d7034cad4b2dc5a06b305d6f93a50dba75f),
  (0xce0f3bd2042798c6f726271b56cebd4ccadc31b217ed1eb9b5bc9cce2912118, 0x3000000000000000000000000000000000000000000000000000000000080e1376a2fe797bd92bb0deb7d700d5872b2d4ca34b3065adc3af9d6055fa7db50, 0x6a6e90c728cc2499751aa0cda54d36805c4b16b7970f2e956dafde09b0a675dd),
  (0x8c912ca7b176a08a3cefd82ae47ee2373f76c2bc1e1800383aa27e5041daaaee, 0x7803000000000000000000000000000080027465686374615272657073696857c7906e6a9924cc28cda01a7580364da5b7164b5c952e0f9709deaf6ddd75a6b0, 0xa9fde16227d33b7b3f69832f3f833ffdd67bb5f54e4f8d8abfa538424348090),
  (0xce0f3bd2042798c6f726271b56cebd4ccadc31b217ed1eb9b5bc9cce2912118, 0x300000000000000000000000000000000000000000000000000000000008016de9f0ab7337d223298f6b3ff33f8f35fbb67ddd8f8e4548453faab90803424, 0x46555b7931e15a93b3ab6eba30a4e600371012578b78d58437d475469dc13274),
  (0xf8e04e32824a932ba392418164e5750fdf1228ea90daf2a09725214ff454dead, 0x30000000000000000000000000000000000000000000000000000000000804a8f98db4f49a7ac7839d4e64feff7fda3348cd0ba55264c9a38d3fff8489b37, 0x10729b796448835538bae247162b5537206a5e5b8e649aca87471f3421a243cf),
  (0x361d45a6deb82818753434b08e043a725dd8246737c9c5387abb6477d385480f, 0x3000000000000000000000000000000000000000000000000000000000080799b72105583486447e2ba3837552b165b5e6a20ca9a648e341f4787cf43a221, 0xf7bcfe792659dd2a9a39381bbcd2c46b9983383b06e4a358387beacefbc4553a),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x36363636363636363636363636363636363636363636363636363636363636364fc88ac11ceb6f102d0e0fac5df2e48a0d0eb5af6e95d230f8dc4d0e0c63f2cd, 0x32ac4be82e6eb1f2ba3a1917500afa83d9c03fc7a4985d190b8a9b50df49a347),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c25a2e0ab7681057a476465c637988ee06764dfc504ffb85a92b62764660998a7, 0x8a17f841b8125e15d59098a1cfdd0e851ad952f09b402c1614f93e53e5ec1fc2),
  (0x32ac4be82e6eb1f2ba3a1917500afa83d9c03fc7a4985d190b8a9b50df49a347, 0x20030000000000000000000000000000000000000000000000000080017478654e206e696168432031562074656863746152205150206c616e67695302000000, 0x95b0a062141b06cb9ba0f43f60e5d04130ea61db696827974203d17662a61cd9),
  (0x8a17f841b8125e15d59098a1cfdd0e851ad952f09b402c1614f93e53e5ec1fc2, 0x300000000000000000000000000000000000000000000000000000000008062a0b095cb061b143ff4a09b41d0e560db61ea309727686976d10342d91ca662, 0x84fd44b6b8900b2c6e5154ecc6b892c6fe0e0b350b8d2a0166be55f6462cdee4),
  (0x32ac4be82e6eb1f2ba3a1917500afa83d9c03fc7a4985d190b8a9b50df49a347, 0x4e206e696168432031562074656863746152205150206c616e67695302000000b644fd842c0b90b8ec54516ec692b8c6350b0efe012a8d0bf655be66e4de2c46, 0x52af7d22876c8d8105b6c1e5b63709bf642ea1209a5ecd98962cf1180e9b7139),
  (0x52af7d22876c8d8105b6c1e5b63709bf642ea1209a5ecd98962cf1180e9b7139, 0x20040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008002747865, 0x1fbcf5f8d9c164d4b584b3f622e9d739a159ece42c3ded7615944917f7683f15),
  (0x8a17f841b8125e15d59098a1cfdd0e851ad952f09b402c1614f93e53e5ec1fc2, 0x3000000000000000000000000000000000000000000000000000000000080f8f5bc1fd464c1d9f6b384b539d7e922e4ec59a176ed3d2c17499415153f68f7, 0x57144c7ab7a6f7232e616efe16ee731009f1614c172b5de441efd74903874fd6),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636b7387402d484b9b369916fafae634608932c49e0dd4efe90a1ab1e9ce1b2f8bc, 0x7125378287589edacb716bac6b03cfacff8b4c15ab682b60195270f22a906c75),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5cdd521e68beeed3d903fb05c5c4092c62f946238ab72494facbc174f68bd892d6, 0xa482af286e7e5c6161d578fac0c5b843bb77eb0f523c4cf16606f406db66d66),
  (0x7125378287589edacb716bac6b03cfacff8b4c15ab682b60195270f22a906c75, 0x8020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008001, 0x71f0467508c62581f28fb1f9b49e1f7abc955939c6ae0de9c889f5e584c23823),
  (0xa482af286e7e5c6161d578fac0c5b843bb77eb0f523c4cf16606f406db66d66, 0x30000000000000000000000000000000000000000000000000000000000807546f0718125c608f9b18ff27a1f9eb4395995bce90daec6e5f589c82338c284, 0x15ec974f17b12c5f0f0ab3757c5b4ad85b77965e8220f913ba15c97a62562015),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x36363636363636363636363636363636363636363636363636363636363636364c7a226115c19081c85857182645d8207a57c73fd26b1d217fe1d977e079b135, 0xa5b7ab9910b74d6b34e9d3638ac5e8cbcb89c557ee0d87f1f35ac2f329dd2872),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c2610480b7fabfaeba2323d724c2fb24a103dad55b801774b158bb31d8a13db5f, 0x4faf2317a5ff83e28b5125de492d6e684e87719403257963dd0606cd211bccba),
  (0xa5b7ab9910b74d6b34e9d3638ac5e8cbcb89c557ee0d87f1f35ac2f329dd2872, 0x30000000000000000000000000000000000000000000000000000000000804f97ec155f2cb11775b30a0fd84a5b7c5e96775b13f920827ac915ba15205662, 0x54bc56b1fe8874a2cdaa3d6f3e7a9595d967c55876430d766844d3138127e3c1),
  (0x4faf2317a5ff83e28b5125de492d6e684e87719403257963dd0606cd211bccba, 0x3000000000000000000000000000000000000000000000000000000000080b156bc54a27488fe6f3daacd95957a3e58c567d9760d437613d34468c1e32781, 0xd2a66c0f5af26b7eb9661f910a7513edfa6a5663004344f8a805c658da3c7055),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636395a90e4485dc46ca729508fdb25433c55605cccce7275366ef0339e63460aec, 0xd720fb960c35ba08c50ad1097e8a62888f0115e952ac667b326f609c168dc25a),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5330fa8e2237ae06cd433ae5b14f29563f0a36a6a4181f5c049a59f4092c6086, 0x58e3c32da9eca4f651674e0a91bb3ab4ddc75989e7dd9700d98f5934a3c7a22c),
  (0xd720fb960c35ba08c50ad1097e8a62888f0115e952ac667b326f609c168dc25a, 0x980200000000000000000000000000000000000000000000000000000000000000000000000000000000000080017379654b6567617373654d72657073696857, 0xe9a8b5b718145e4bf7dc5542e61e1da16aa1979774e25f16f41f2f35b22f81a),
  (0x58e3c32da9eca4f651674e0a91bb3ab4ddc75989e7dd9700d98f5934a3c7a22c, 0x30000000000000000000000000000000000000000000000000000000000805b8b9a0ee445817154c57dbfdae1612e7919aa16f1254e77f3f2416f1af8225b, 0xd58eaeff4615e412a9093584c93531382ddcad9e83da508c5988c3df13b6630),
  (0xd720fb960c35ba08c50ad1097e8a62888f0115e952ac667b326f609c168dc25a, 0x98030000000000000000000080027379654b6567617373654d72657073696857efea580d415e61f45893902a1353934cd9cadd8208a53de83d8c98c530663bf1, 0xc806a11f3fe711baf71816032888500d29090c08c0c552cb8a296888b4bc2406),
  (0x58e3c32da9eca4f651674e0a91bb3ab4ddc75989e7dd9700d98f5934a3c7a22c, 0x30000000000000000000000000000000000000000000000000000000000801fa106c8ba11e73f031618f70d508828080c0929cb52c5c08868298a0624bcb4, 0xa6e57c03129f2e0150c3083d72f1effa3869073465c003865b34c750727fa93c),
  (0xd720fb960c35ba08c50ad1097e8a62888f0115e952ac667b326f609c168dc25a, 0x98030000000000000000000080037379654b6567617373654d72657073696857037ce5a6012e9f123d08c350faeff172340769388603c06550c7345b3ca97f72, 0x437c600e10f67b0258c4b13b0e505b5bf4cab6b180e65bb698a0d848e659d9f3),
  (0x58e3c32da9eca4f651674e0a91bb3ab4ddc75989e7dd9700d98f5934a3c7a22c, 0x30000000000000000000000000000000000000000000000000000000000800e607c43027bf6103bb1c4585b5b500eb1b6caf4b65be68048d8a098f3d959e6, 0x43b65222d408065e4d2f9d6e6c5a882eb950fcc92160831ee337bf4a79a6ab5c),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636354ad3903718a9240b3ef566ccd9c74402315f0eb035f65366f1026d0a9f4944, 0xa7a9bcdcc8e43643036fda52e644dcb14b5a6fd33533e9c56fda6ad919bed1e9),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5f20b9fa5d72c34e61549f0ca6b3ad2e685b3564da5f9c390c9b680760f5232e, 0x4a814b7ff0e8e8f28025d30c6936f9f87673521efe3bd77bed14e5f3e25c4366),
  (0xa7a9bcdcc8e43643036fda52e644dcb14b5a6fd33533e9c56fda6ad919bed1e9, 0xac8bff0348b0c032b515e585e882aa28244c58ceadfb6f2c8876f3506df7053c01432d659f6956d79efdb84cf363bd3effef89cb39f4513184d598b479f75a05, 0x992ff5f61c1b7e09df99d8d2afa0bfabdbfa4cfbdb39d03c71d50897564e19ae),
  (0x992ff5f61c1b7e09df99d8d2afa0bfabdbfa4cfbdb39d03c71d50897564e19ae, 0x101252a884f40bdd047e18767282d49485b5ca01022001801104ae020f0133ecd4a8abe6ff58f162cef8c18ef9d7411918dad639572eb5d162705210a44627f, 0x64a738b763ee71034670c2b2907019316d9630ea98a16ca0e2992e4ebaa2c8b4),
  (0x64a738b763ee71034670c2b2907019316d9630ea98a16ca0e2992e4ebaa2c8b4, 0x9d4c8b7a102f3e5d00016b5a4f3e2d1c0b9a5f4e4d3b2e1c6f8a002432c5dfa53708ac5adfa9c2afd695fb8d5722060dfb58d3c7074b5508b4c4e50286010102, 0xb9c658be240ced3507023885660a5240d154ecfabe53ef168f6cefbbf73a5b9f),
  (0xb9c658be240ced3507023885660a5240d154ecfabe53ef168f6cefbbf73a5b9f, 0x4808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008001f6e5d4c3b2a10f8e, 0xff9a39e6eb476d463eeaa47468213567db9c9540ee722b62dde685fb0b601548),
  (0x4a814b7ff0e8e8f28025d30c6936f9f87673521efe3bd77bed14e5f3e25c4366, 0x3000000000000000000000000000000000000000000000000000000000080e6399aff466d47eb74a4ea3e6735216840959cdb622b72eefb85e6dd4815600b, 0xd264df00c2f4ed37981aec6bad3fdc5d9070ade375549cbe19b301591ba3bf46),
  (0x7125378287589edacb716bac6b03cfacff8b4c15ab682b60195270f22a906c75, 0x8020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008002, 0x645aadaf08f1c7750441162fdae90fb2edd481e5068314234336d7d108635225),
  (0xa482af286e7e5c6161d578fac0c5b843bb77eb0f523c4cf16606f406db66d66, 0x3000000000000000000000000000000000000000000000000000000000080afad5a6475c7f1082f164104b20fe9dae581d4ed23148306d1d7364325526308, 0x5bbfd192d3f8a0b2a646f768d5808a8d1858ed339f72d2c4c15d6f53d0f2184),
  (0xc87493f4418f30a35731c97400f76c573c634ddb3f392a266ef10d36f057716e, 0xd09069e4d2b6c6b8d7b7bb54701ce5b5394e941e2b5ee55f4e1aa70a3ccabc132cd5b7e65b83b22788fc146ea032ea99a2d368cf12ef60abe24a50e429e4553, 0xdce26f1b828cbd2f9450919a6616b969b1d36d18033f4d1e72c683dc49b4165e),
  (0xdce26f1b828cbd2f9450919a6616b969b1d36d18033f4d1e72c683dc49b4165e, 0x700000000000000000000000000000000000000000000000000000000008032c88db1104654ede99cb46c61acb5170a8b2b78b76649d64f3b77acebf05deb, 0x7b62b4d069a7ee5ad1cdb913e40a56c8a7e1796d6f83699d929c4b548c2821be),
  (0x361d45a6deb82818753434b08e043a725dd8246737c9c5387abb6477d385480f, 0x3000000000000000000000000000000000000000000000000000000000080d0b4627b5aeea76913b9cdd1c8560ae46d79e1a79d69836f544b9c92be21288c, 0xd92d95c216387d6cacfbcb4c8090ccd5bee2b8deb6007442dc27ea648577824e),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636f4a31bef5a4b0e207afdcd9ae3faa6b6e88ed4887442368052dc11ea78b441b3, 0x75c8776b8387705fe090db00d4f446035e1bb2396602de38748a52826e189bbe),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c9ec971853021644a1097a7f08990ccdc82e4bee21e285cea38b67b8012de2bd9, 0xbe66d6018666cefb7c1ac9ff82dd8841c604d4cdacca1d70fe3622903bfbecbf),
  (0x75c8776b8387705fe090db00d4f446035e1bb2396602de38748a52826e189bbe, 0x780300000000000000000000000000008001343230312d524542594b2d534c4154535952435f3635322d4148535f3931353532585f7478655472657073696857, 0xae35e819b7d688398eef128ec5809757f4afe26c59dfe655dbdce3f868cf9d7e),
  (0xbe66d6018666cefb7c1ac9ff82dd8841c604d4cdacca1d70fe3622903bfbecbf, 0x300000000000000000000000000000000000000000000000000000000008019e835ae3988d6b78e12ef8e579780c56ce2aff455e6df59f8e3dcdb7e9dcf68, 0xa0e4b941eee905643ae23fcff4659b0c85a7f23ebde11134b8153d77b1ec4fe8),
  (0x75c8776b8387705fe090db00d4f446035e1bb2396602de38748a52826e189bbe, 0x54535952435f3635322d4148535f3931353532585f747865547265707369685741b9e4a06405e9eecf3fe23a0c9b65f43ef2a7853411e1bd773d15b8e84fecb1, 0x380768761567365901d4def7c5d60f403fc045515692e406ccb67e51bde3ba00),
  (0x380768761567365901d4def7c5d60f403fc045515692e406ccb67e51bde3ba00, 0x7804000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008002343230312d524542594b2d534c41, 0xf2387d77269f85516af77795219a67327c8f593f4767eb234d75061da7923da2),
  (0xbe66d6018666cefb7c1ac9ff82dd8841c604d4cdacca1d70fe3622903bfbecbf, 0x3000000000000000000000000000000000000000000000000000000000080777d38f251859f269577f76a32679a213f598f7c23eb67471d06754da23d92a7, 0x3e78f157ce9e2e555a26b01e73782b6ae99ea32bb5cf09c0274cdae263992812),
  (0x75c8776b8387705fe090db00d4f446035e1bb2396602de38748a52826e189bbe, 0x54535952435f3635322d4148535f3931353532585f747865547265707369685757f1783e552e9ece1eb0265a6a2b78732ba39ee9c009cfb5e2da4c2712289963, 0x431dee2e0f8196c1eebda95bdb2d4eb9967a2b0dcabfbd19cd02ab893cac733f),
  (0x431dee2e0f8196c1eebda95bdb2d4eb9967a2b0dcabfbd19cd02ab893cac733f, 0x7804000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008003343230312d524542594b2d534c41, 0xca0e492a0ddc18dca80b50c0feabd829e2c321f23c007827c599fb2711814968),
  (0xbe66d6018666cefb7c1ac9ff82dd8841c604d4cdacca1d70fe3622903bfbecbf, 0x30000000000000000000000000000000000000000000000000000000000802a490ecadc18dc0dc0500ba829d8abfef221c3e22778003c27fb99c568498111, 0x1fbddc11374a5dbf69484c29d9e9950614e418c813211cf1c4561ef4e054cb8a),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636778fd2965233dfd8f909d40c3aad53c208c491b30227d78b410b238ede79da87, 0x88b511b97965082412aae2b638dd9ad6a4dbafe7849285101e47c82833102684),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c1de5b8fc3859b5b29363be6650c739a862aefbd9684dbde12b6149e4b413b0ed, 0x9ba3eddee247652475be2926f3e95b9f8fceaa372bede3d222206e0b0b9c99dd),
  (0x88b511b97965082412aae2b638dd9ad6a4dbafe7849285101e47c82833102684, 0x30000000000000000000000000000000000000000000000000000000000804f0afd7d659b52fae025b55d505736adc89928285fecd3039bbb03d943130441, 0x4c82ba63b0de8d3e3b9042e06d3d499669389baf50120c9585c623c531bcc348),
  (0x9ba3eddee247652475be2926f3e95b9f8fceaa372bede3d222206e0b0b9c99dd, 0x300000000000000000000000000000000000000000000000000000000008063ba824c3e8ddeb0e042903b96493d6daf9b3869950c1250c523c68548c3bc31, 0x6f7b1d3a8f4d2ba2de1bd4eb1ad0048a548e647a3435e31d5658535a2a76837b),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x36363636363636363636363636363636363636363636363636363636363636360c2b4d59941d7bb9dde22de8bc32e62c4c52b8622bd503026c656e604db5401c, 0xf05787342cb15a778198f2af727c5fbbd779ce862a2072a1880411ce299dcca5),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c66412733fe7711d3b7884782d6588c462638d20841bf6968060f040a27df2a76, 0xa02006f5204e03d21055bc8f993e77cd457669c8a4fc7562498fac84da51525f),
  (0xf05787342cb15a778198f2af727c5fbbd779ce862a2072a1880411ce299dcca5, 0x78020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080017465686374615272657073696857, 0x9cdfd8ff20a7eee599e98ab7a40ad38ccd39590b07892e5f941a8aeeaa645e30),
  (0xa02006f5204e03d21055bc8f993e77cd457669c8a4fc7562498fac84da51525f, 0x3000000000000000000000000000000000000000000000000000000000080ffd8df9ce5eea720b78ae9998cd30aa40b5939cd5f2e8907ee8a1a94305e64aa, 0x4eb5125e19e0c5ebd6468de8c3260bbc52929beddef7007f274770dca11d67cd),
  (0xf05787342cb15a778198f2af727c5fbbd779ce862a2072a1880411ce299dcca5, 0x78030000000000000000000000000000800274656863746152726570736968575e12b54eebc5e019e88d46d6bc0b26c3ed9b92527f00f7dedc704727cd671da1, 0x9af270a82d7ea6873827d59347c7dc8cc70c73fcfda2cc8a3e93e7d4cca2e515),
  (0xa02006f5204e03d21055bc8f993e77cd457669c8a4fc7562498fac84da51525f, 0x3000000000000000000000000000000000000000000000000000000000080a870f29a87a67e2d93d527388cdcc747fc730cc78acca2fdd4e7933e15e5a2cc, 0x184b9ec35c44915a12f33d5ce9b0dd8f96c703b1e2d1ec840333428884c20e6f),
  (0xf8e04e32824a932ba392418164e5750fdf1228ea90daf2a09725214ff454dead, 0x11dcbd1fbf5d4a37294c48690695e9d9c818e414f11c2113f41e56c48acb54e00000000000000000000000000000000000000000000000000000000000000000, 0x524e3faf6289a9e0b744acc5efc13718a451bf308af0039c7cb5c688553e99ae),
  (0x524e3faf6289a9e0b744acc5efc13718a451bf308af0039c7cb5c688553e99ae, 0x40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080, 0x8ecbef23fd5a09294b364ae6717a5dba3c368f2bf475f2a93c3cec6677d3d705),
  (0x361d45a6deb82818753434b08e043a725dd8246737c9c5387abb6477d385480f, 0x300000000000000000000000000000000000000000000000000000000008023efcb8e29095afde64a364bba5d7a712b8f363ca9f275f466ec3c3c05d7d377, 0xce872b4ca6154b5f3f6d87a66c093830113a5279fdcf1937e4de27896956b77f),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x36363636363636363636363636363636363636363636363636363636363636367a1db1f8697d239090b15b09060e3f5a4f640c27012ff9cbbf11e8d24981605f, 0x2c2ba409d62f61eecd678467e20ec03cad4199823b132dc10aeb0858e2394924),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c1077db92031749fafadb31636c645530250e664d6b4593a1d57b82b823eb0a35, 0x3fbd5d0ae3134e33c9405fe259a243e3824782e13b55cfe4ae49f2a833df9941),
  (0x2c2ba409d62f61eecd678467e20ec03cad4199823b132dc10aeb0858e2394924, 0xb003000000000000008001010000000000000065746164705520726f74616369746e65687475413a3836374d454b4c4d5f31565f414b4351505f6c616e676953, 0x72319f81d4774ec3754498bcfecb05e1f4fbbb71a1ff097eedf39e953adb64ca),
  (0x3fbd5d0ae3134e33c9405fe259a243e3824782e13b55cfe4ae49f2a833df9941, 0x3000000000000000000000000000000000000000000000000000000000080819f3172c34e77d4bc984475e105cbfe71bbfbf47e09ffa1959ef3edca64db3a, 0xd2e99518cbe5913434c46135db4849144faf6342e86743acbe39841a786fed3a),
  (0x2c2ba409d62f61eecd678467e20ec03cad4199823b132dc10aeb0858e2394924, 0x746e65687475413a3836374d454b4c4d5f31565f414b4351505f6c616e6769531895e9d23491e5cb3561c434144948db4263af4fac4367e81a8439be3aed6f78, 0x76718622b755d9434b1f7522b908475e75aeb54c0613f87147857cbf52a52d3e),
  (0x76718622b755d9434b1f7522b908475e75aeb54c0613f87147857cbf52a52d3e, 0xb0040000000000000000000000000000000000000000000000000000000000000000000000000000008002010000000000000065746164705520726f74616369, 0xc95d13819ef03c739d59bc599a68f076cc4671fba7e0593b55599a2f541e30c5),
  (0x3fbd5d0ae3134e33c9405fe259a243e3824782e13b55cfe4ae49f2a833df9941, 0x300000000000000000000000000000000000000000000000000000000008081135dc9733cf09e59bc599d76f0689afb7146cc3b59e0a72f9a5955c5301e54, 0x12bc111c0ba8ef553256aa7bc2240b4cc05ff4cdd9afe245e2f29d84c7e420b9),
  (0xf8e04e32824a932ba392418164e5750fdf1228ea90daf2a09725214ff454dead, 0x300000000000000000000000000000000000000000000000000000000008011dcbd1fbf5d4a37294c48690695e9d9c818e414f11c2113f41e56c48acb54e0, 0x4f6dc6e3f5bfd0291d0d19225f3d5bc70f3fb980dcecbed183ab7a9f1a8b5e11),
  (0x361d45a6deb82818753434b08e043a725dd8246737c9c5387abb6477d385480f, 0x3000000000000000000000000000000000000000000000000000000000080e3c66d4f29d0bff522190d1dc75b3d5f80b93f0fd1beecdc9f7aab83115e8b1a, 0xc198bd628714860396b5c39e60e9322e5b80e95b61b964b601c7e6b02189f7fd),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636548baef735b022b1a8f583a01804df566ddfb66d80528f5786d0f137cbc1bf17, 0x7c312127208be90577c1bb2330e2b5ceb73e90115cfdc3d839b2243995486a47),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c3ee1c49d5fda48dbc29fe9ca726eb53c07b5dc07ea38e53decba9b5da1abd57d, 0xa4fc6f7cd755e556686c4f81b2af6ba61cbf67d16de10378ec733335b119e574),
  (0x7c312127208be90577c1bb2330e2b5ceb73e90115cfdc3d839b2243995486a47, 0x10030000000000000000000000000000000000000000000000000000008001747261745320206e696168432031562074656863746152205150206c616e676953, 0x352ba33cb7933102acbb974815f4e95067c4be90a226cfafa9e4ddafc212d48d),
  (0xa4fc6f7cd755e556686c4f81b2af6ba61cbf67d16de10378ec733335b119e574, 0x30000000000000000000000000000000000000000000000000000000000803ca32b35023193b74897bbac50e9f41590bec467afcf26a2afdde4a98dd412c2, 0x382b2bfb44df3eecd12520d22cdb2e31b985044108727cd25de064fe39ce6a73),
  (0x7c312127208be90577c1bb2330e2b5ceb73e90115cfdc3d839b2243995486a47, 0x7261745320206e696168432031562074656863746152205150206c616e676953fb2b2b38ec3edf44d22025d1312edb2c410485b9d27c7208fe64e05d736ace39, 0x5f6198713198d2d32fd9ab658bdac8d031cdff7f2ffd7b3784d5ebe5c539f5bd),
  (0x5f6198713198d2d32fd9ab658bdac8d031cdff7f2ffd7b3784d5ebe5c539f5bd, 0x10040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800274, 0xdf31a4a7a51b2cd774357dbd25f8c0ae5285dccd7b301fe404e11a74059442f7),
  (0xa4fc6f7cd755e556686c4f81b2af6ba61cbf67d16de10378ec733335b119e574, 0x3000000000000000000000000000000000000000000000000000000000080a7a431dfd72c1ba5bd7d3574aec0f825cddc8552e41f307b741ae104f7429405, 0xafc09c73bf3aabb718a4813bc65d3f6e3fc83b61a4d8c3392a6f47a6773e1077),
  (0x7c312127208be90577c1bb2330e2b5ceb73e90115cfdc3d839b2243995486a47, 0x7261745320206e696168432031562074656863746152205150206c616e676953739cc0afb7ab3abf3b81a4186e3f5dc6613bc83f39c3d8a4a6476f2a77103e77, 0xbb13b9629b3ae3b0ef403ab407af6d5faaea32b1e92be43ba71f00bdbd4b2142),
  (0xbb13b9629b3ae3b0ef403ab407af6d5faaea32b1e92be43ba71f00bdbd4b2142, 0x10040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800374, 0xe65090b561d11326ae6fc6df03daa062f8283b28ab50b1007f891cba9487a06b),
  (0xa4fc6f7cd755e556686c4f81b2af6ba61cbf67d16de10378ec733335b119e574, 0x3000000000000000000000000000000000000000000000000000000000080b59050e62613d161dfc66fae62a0da03283b28f800b150abba1c897f6ba08794, 0x405284ffcf311bfbd6752d19a1fdc6c1326e3dddc26e2ef308311093827479ae),
  (0xf8e04e32824a932ba392418164e5750fdf1228ea90daf2a09725214ff454dead, 0x3000000000000000000000000000000000000000000000000000000000080739cc0afb7ab3abf3b81a4186e3f5dc6613bc83f39c3d8a4a6476f2a77103e77, 0x6bcb350ccaa8fd7b20be980711d94588c3cef3ae4f12116f2cda341e37679176),
  (0x361d45a6deb82818753434b08e043a725dd8246737c9c5387abb6477d385480f, 0x30000000000000000000000000000000000000000000000000000000000800c35cb6b7bfda8ca0798be208845d911aef3cec36f11124f1e34da2c76916737, 0xcf044cff2cd306ed1d1a6603461bd298aaec65fcab7939966a366430f156f41d),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636c97a32f9db30e51a35502c2baee42d70ca53da9ca00f4f9d0652005c2bc260c7, 0x8ebcef4dce178687fb1cb512c7226ccf7da5e9c431aa8c2300dfe831f26405e9),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5ca3105893b15a8f705f3a4641c48e471aa039b0f6ca6525f76c386a3641a80aad, 0xb8564fc0cdd2a0d02d8cc751b2535ae8d9a9b0faedbeea50e69eec0c5cefa8fd),
  (0x8ebcef4dce178687fb1cb512c7226ccf7da5e9c431aa8c2300dfe831f26405e9, 0x20030000000000000000000000000000000000000000000000000080017478654e206e696168432031562074656863746152205150206c616e67695301000000, 0xd7d221323b0777a36b7cac3e600ec1cfca5b13f98c71e67c08fd77e7dce9c084),
  (0xb8564fc0cdd2a0d02d8cc751b2535ae8d9a9b0faedbeea50e69eec0c5cefa8fd, 0x30000000000000000000000000000000000000000000000000000000000803221d2d7a377073b3eac7c6bcfc10e60f9135bca7ce6718ce777fd0884c0e9dc, 0x5cfadecad50f906f35baf74d11b02589bc13c773426cbbf85455522240ac7927),
  (0x8ebcef4dce178687fb1cb512c7226ccf7da5e9c431aa8c2300dfe831f26405e9, 0x4e206e696168432031562074656863746152205150206c616e67695301000000cadefa5c6f900fd54df7ba358925b01173c713bcf8bb6c42225255542779ac40, 0xeee895a7bda942b689819d007094c08fb85532c22cb30b718d34feddd930cdd5),
  (0xeee895a7bda942b689819d007094c08fb85532c22cb30b718d34feddd930cdd5, 0x20040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008002747865, 0x38b9f30471e533d164d3501254cdafa42443aa368b8941946bf06590b2a4c7b3),
  (0xb8564fc0cdd2a0d02d8cc751b2535ae8d9a9b0faedbeea50e69eec0c5cefa8fd, 0x300000000000000000000000000000000000000000000000000000000008004f3b938d133e5711250d364a4afcd5436aa43249441898b9065f06bb3c7a4b2, 0x47a416af4853c12299f1afae40f3cf853e937a773a47ea4de030382620eb3dd8),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636f5a87d2e6ca7726a6a0bc524b9eb86df8735f1a0b2dae7d4be7405355938f4b2, 0x946a12897caee06b0feff1ef7bb1a5ad2dd870653d79968a1eabd0b9c075f6cf),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c9fc2174406cd18000061af4ed381ecb5ed5f9bcad8b08dbed41e6f5f33529ed8, 0x2f0b0526e56b55544220d911e63c86808ce1078738c1c8c458b8d122ca4d8ca0),
  (0x946a12897caee06b0feff1ef7bb1a5ad2dd870653d79968a1eabd0b9c075f6cf, 0x8020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008001, 0x8abc00fb117ea2a0d0bc78d7ebfdcec5586e5d187d4a8136d36e32ed208f7aa2),
  (0x2f0b0526e56b55544220d911e63c86808ce1078738c1c8c458b8d122ca4d8ca0, 0x3000000000000000000000000000000000000000000000000000000000080fb00bc8aa0a27e11d778bcd0c5cefdeb185d6e5836814a7ded326ed3a27a8f20, 0xd135becfa0f234f0d03ee8002892272713231a79ff6e013cd3410197332c1abd),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x36363636363636363636363636363636363636363636363636363636363636369920927114f7657e9899c7afb3f9c576414ca5087bdc710c100e06d6ee0bdd16, 0x6b1a716a2f096c3cc6f652bc191c0b90da69ff82280a856fd9aad65c41792b8e),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5cf34af81b7e9d0f14f2f3adc5d993af1c2b26cf6211b61b667a646cbc8461b77c, 0x7d38e60c909e59a9de1e70f52cd4ee9277ccfd2563a3f7bebd8def9a37409c91),
  (0x6b1a716a2f096c3cc6f652bc191c0b90da69ff82280a856fd9aad65c41792b8e, 0x3000000000000000000000000000000000000000000000000000000000080cfbe35d1f034f2a000e83ed027279228791a23133c016eff970141d3bd1a2c33, 0x1f20c3fb9ce7476047e506f67a4b5b85202e456dcb8aeda5105fa5261536eb89),
  (0x7d38e60c909e59a9de1e70f52cd4ee9277ccfd2563a3f7bebd8def9a37409c91, 0x3000000000000000000000000000000000000000000000000000000000080fbc3201f6047e79cf606e547855b4b7a6d452e20a5ed8acb26a55f1089eb3615, 0x8d457b0fddfd160a57ac898d50bfa1dd7c367fa84fb866d4f28c43b9aaba5cf2),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636394d73bb3c20cbebbbbf9a61eb9789669e49004ae2508e798f75bac4c46a8c9c, 0x391d8e7afe67e4df92769d240912439b35d303b50a904e898082bd017316f099),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c532719d1564aa181d1d5f00b81fde30cf4236a20883ae413e51fd0aeae00e6f6, 0xdd1ed0a41c11328f561b0613055540dbef805b013ea30986c41b2ccd7ffbd4d),
  (0x391d8e7afe67e4df92769d240912439b35d303b50a904e898082bd017316f099, 0x980200000000000000000000000000000000000000000000000000000000000000000000000000000000000080017379654b6567617373654d72657073696857, 0xdd9f8f88f1bff826dadb63341b654b38003943e7cd52373007899fd6da8884a9),
  (0xdd1ed0a41c11328f561b0613055540dbef805b013ea30986c41b2ccd7ffbd4d, 0x3000000000000000000000000000000000000000000000000000000000080888f9fdd26f8bff13463dbda384b651be7433900303752cdd69f8907a98488da, 0x6f4f52dcb4137bed86e28b89e91eae76fc7bcb723fba162b7a86239ef5731477),
  (0x391d8e7afe67e4df92769d240912439b35d303b50a904e898082bd017316f099, 0x98030000000000000000000080027379654b6567617373654d72657073696857dc524f6fed7b13b4898be28676ae1ee972cb7bfc2b16ba3f9e23867a771473f5, 0x1e3c531cacadce238ad46a8477afd5dfe50e67bb30742c4d0e6bd793a9362961),
  (0xdd1ed0a41c11328f561b0613055540dbef805b013ea30986c41b2ccd7ffbd4d, 0x30000000000000000000000000000000000000000000000000000000000801c533c1e23ceadac846ad48adfd5af77bb670ee54d2c743093d76b0e612936a9, 0xfbe94e42f73b24198616cf6bb1319c65f2d654ebbe37367271d8c9733cee22bf),
  (0x391d8e7afe67e4df92769d240912439b35d303b50a904e898082bd017316f099, 0x98030000000000000000000080037379654b6567617373654d72657073696857424ee9fb19243bf76bcf1686659c31b1eb54d6f2723637be73c9d871bf22ee3c, 0xf4e54ff19e7367717f148786bba4baa0456816970803857b8a2cff417a7a4e4c),
  (0xdd1ed0a41c11328f561b0613055540dbef805b013ea30986c41b2ccd7ffbd4d, 0x3000000000000000000000000000000000000000000000000000000000080f14fe5f47167739e8687147fa0baa4bb971668457b85030841ff2c8a4c4e7a7a, 0x7406347327be17e24ade881973e0d4a167691eb75d5254fe77fdc78e1e92bd0),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x36363636363636363636363636363636363636363636363636363636363636367478dfcd2f120dc15df920b053aa0787dd62e0c44400018845ffee478914d80a, 0x8eae849b5f46f42a284c2005864f9850342efab10199318a659bab1a3ff36e38),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c1e12b5a7457867ab37934ada39c06dedb7088aae2e6a6be22f95842de37eb260, 0xc32f154a9f61e5f342f75ff343feebf63c595217a6872db8ddf50f4bf9f57b31),
  (0x8eae849b5f46f42a284c2005864f9850342efab10199318a659bab1a3ff36e38, 0xac8bff0348b0c032b515e585e882aa28244c58ceadfb6f2c8876f3506df7053c01432d659f6956d79efdb84cf363bd3effef89cb39f4513184d598b479f75a05, 0xbbbde35f5805075e2f7e75f4898eb5275404eef0423f9aefb8efdc1a640de00e),
  (0xbbbde35f5805075e2f7e75f4898eb5275404eef0423f9aefb8efdc1a640de00e, 0x101252a2bd957f3dde6eae35954587a0a9333cf102200180010403fe1f44d61222fa5fa45d5d75c73b9cf3bb9613445fbf0ec18d035609a978305210a44627f, 0x6a6cb3e1bb39b12ab3a595ef3c96f5e3fb952c466c9701f0c39c7230a74d3f7),
  (0x6a6cb3e1bb39b12ab3a595ef3c96f5e3fb952c466c9701f0c39c7230a74d3f7, 0x9d4c8b7a102f3e5d00016b5a4f3e2d1c0b9a5f4e4d3b2e1c6f8a002432c0396c4d0c20a2783f686eb9f1a0d3d9862de2de4453d804b01c6fc502bcb3cc000101, 0x44961558b26dfd4d928e0ba312ceb087d4be12734d54d16a255a04d6f2833a54),
  (0x44961558b26dfd4d928e0ba312ceb087d4be12734d54d16a255a04d6f2833a54, 0x4808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008001f6e5d4c3b2a10f8e, 0xb71c0407ed07038e70ca9beed8d423c021afa436c31dadd5502545f10e63960d),
  (0xc32f154a9f61e5f342f75ff343feebf63c595217a6872db8ddf50f4bf9f57b31, 0x300000000000000000000000000000000000000000000000000000000008007041cb78e0307edee9bca70c023d4d836a4af21d5ad1dc3f14525500d96630e, 0xa758fa2fcb6562ed321b415b69324bcb6c3777751a45cc8bf21c71ff830b0f13),
  (0x946a12897caee06b0feff1ef7bb1a5ad2dd870653d79968a1eabd0b9c075f6cf, 0x8020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008002, 0x43f8eeeb30f5b538e2607b5df6056534117fda317ad92ad2cbedf3eacaa81a11),
  (0x2f0b0526e56b55544220d911e63c86808ce1078738c1c8c458b8d122ca4d8ca0, 0x3000000000000000000000000000000000000000000000000000000000080ebeef84338b5f5305d7b60e2346505f631da7f11d22ad97aeaf3edcb111aa8ca, 0xb656dd017600757650f6965abfb4cfb973b615cf880f647b4277c41da44e5140),
  (0x88b511b97965082412aae2b638dd9ad6a4dbafe7849285101e47c82833102684, 0x30000000000000000000000000000000000000000000000000000000000805188500b822d529fe65cfbc87e52c5607f92b09f3dc64254c47aed0d73c65ebc, 0x5c2d8cbd439bebca8d289631455c2242f899006088d12a95e38ccbc9bfcd059),
  (0x9ba3eddee247652475be2926f3e95b9f8fceaa372bede3d222206e0b0b9c99dd, 0x3000000000000000000000000000000000000000000000000000000000080cbd8c205bcbe39d46389d2a824c255140690892fa9128d08bccc385e59d0fc9b, 0x7e3f98dc7cc2ef929cd023f6459de322c9352437e66371e7818067b884128e91),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636eaae0948a4d9f44ac015e6aa14d5ab73011203ffd14755d08e51b6b7a7b824b2, 0x8c3f9c2e79b4656e4ca2d29cbd30e5d39e4505cca868b38ed1dfbe2f796f7d4c),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c80c46322ceb39e20aa7f8cc07ebfc1196b786995bb2d3fbae43bdcddcdd24ed8, 0x3ac79ca5f5881c90a46fe7a3f3f40723d7a2223a555471d2f5fe8ca9dfb99307),
  (0x8c3f9c2e79b4656e4ca2d29cbd30e5d39e4505cca868b38ed1dfbe2f796f7d4c, 0x78020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080017465686374615272657073696857, 0xfab12e511cba59440a362035675f3ae878d56275ad167d00d8abc792e9852f89),
  (0x3ac79ca5f5881c90a46fe7a3f3f40723d7a2223a555471d2f5fe8ca9dfb99307, 0x3000000000000000000000000000000000000000000000000000000000080512eb1fa4459ba1c3520360ae83a5f677562d578007d16ad92c7abd8892f85e9, 0x50edeaa4684643cd3e77748cb816c6f79290994d8a9c68ab5ffb94b95c5ac141),
  (0x8c3f9c2e79b4656e4ca2d29cbd30e5d39e4505cca868b38ed1dfbe2f796f7d4c, 0x7803000000000000000000000000000080027465686374615272657073696857a4eaed50cd4346688c74773ef7c616b84d999092ab689c8ab994fb5f41c15a5c, 0xfbe259238090ae8d0da1f0299e5b12d5e87f7c32bcf5dd3733510c9afd9ea9b0),
  (0x3ac79ca5f5881c90a46fe7a3f3f40723d7a2223a555471d2f5fe8ca9dfb99307, 0x30000000000000000000000000000000000000000000000000000000000802359e2fb8dae908029f0a10dd5125b9e327c7fe837ddf5bc9a0c5133b0a99efd, 0x95657e3a03583453900af4247684b0d730da197e9cb5dde583cd7356c78647e0),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x363636363636363636363636363636363636363636363636363636363636363692dcdb66fb75705eba424108c1f0208e7bafa6a49d5eaabc8fa2cd6977f76c6a, 0x76b22d6898b2dcde6d6c5a465d575daf37e1f828674e0243ac08133b776928ad),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5cf8b6b10c911f1a34d0282b62ab9a4ae411c5cccef734c0d6e5c8a7031d9d0600, 0x2edaf4d9f58bf9bfba8073ab96b45924ef0a0519d01910e96b42e046839ac583),
  (0x76b22d6898b2dcde6d6c5a465d575daf37e1f828674e0243ac08133b776928ad, 0x300000000000000000000000000000000000000000000000000000000008071c9603a3a852133054ddc8f21ef2c9257ffd88c50067a9f45d18af019b3e30e, 0x51ab2df8b81f24aa84e357957302eb19f409fe2496085e3a28e12c82bbfd8e39),
  (0x2edaf4d9f58bf9bfba8073ab96b45924ef0a0519d01910e96b42e046839ac583, 0x3000000000000000000000000000000000000000000000000000000000080f82dab51aa241fb89557e38419eb027324fe09f43a5e0896822ce128398efdbb, 0xf04e0f2ebe269d0e3a40f6495bcbb41dc25c9ab5c175c58a8ebd2d66c594d1aa),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636183978c638ab10887fc0760c2b82fd6d83ac6af4bcf343f7501b8bb89ce7a2f3, 0x96227ba15e113f7c131c606be91f5a105ba1d2b4abc3a557003952811c3f657b),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c725312ac52c17ae215aa1c6641e89707e9c6009ed699299d3a71e1d2f68dc899, 0xdcc4ae89e4190a34656638ada3027746fbf32834338a1732e90fd41778b51eed),
  (0x96227ba15e113f7c131c606be91f5a105ba1d2b4abc3a557003952811c3f657b, 0x78020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080017465686374615272657073696857, 0x309e44abef3da421d5b65e89474f2474de7e8b60fe3333bd5010df1e0c1cf841),
  (0xdcc4ae89e4190a34656638ada3027746fbf32834338a1732e90fd41778b51eed, 0x3000000000000000000000000000000000000000000000000000000000080ab449e3021a43def895eb6d574244f47608b7edebd3333fe1edf105041f81c0c, 0x24adf9428b34f4083bf3f5e74554c3b5a744eecc68ea72b6889845ee31138b35),
  (0x96227ba15e113f7c131c606be91f5a105ba1d2b4abc3a557003952811c3f657b, 0x780300000000000000000000000000008002746568637461527265707369685742f9ad2408f4348be7f5f33bb5c35445ccee44a7b672ea68ee459888358b1331, 0x5c1c0c64049c2783110ae1c234a9379d7d38eaa0acb99bd0f3b9acc2d1c5b36d),
  (0xdcc4ae89e4190a34656638ada3027746fbf32834338a1732e90fd41778b51eed, 0x3000000000000000000000000000000000000000000000000000000000080640c1c5c83279c04c2e10a119d37a934a0ea387dd09bb9acc2acb9f36db3c5d1, 0xc7d1f5662e51b40ee0c1f936e039d8a6328b7ecb8f10e047b59e9d63bd191452),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x36363636363636363636363636363636363636363636363636363636363636360c4853a365026e3512c23ca6e186b240482fec06d3eb83aa6045fbb5d671b0f1, 0x9e3e684ca44c91c6f0e012ecd4ea9e19160c5df10baa36eae4ed32645f3c02b3),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c662239c90f68045f78a856cc8becd82a2245866cb981e9c00a2f91dfbc1bda9b, 0x533bc28327c41ceae5ec7cf83cea25890ad5e01f60e227d468fe8975fcb390ed),
  (0x9e3e684ca44c91c6f0e012ecd4ea9e19160c5df10baa36eae4ed32645f3c02b3, 0x8020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008001, 0x64db72320d96e943eece927b8bd24e114df368a79d93c7b16ad9b0bbbafd278f),
  (0x533bc28327c41ceae5ec7cf83cea25890ad5e01f60e227d468fe8975fcb390ed, 0x30000000000000000000000000000000000000000000000000000000000803272db6443e9960d7b92ceee114ed28ba768f34db1c7939dbbb0d96a8f27fdba, 0xcbd75b4faf2ec43d66b76e505c95c64adc2109f26aecccac5a68a74b89f1fa25),
  (0x9e3e684ca44c91c6f0e012ecd4ea9e19160c5df10baa36eae4ed32645f3c02b3, 0x8020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008002, 0x84c1fa5740170bc5a00b5819aec8cf128cf7338578e72a4b53a92bbe648bfd3c),
  (0x533bc28327c41ceae5ec7cf83cea25890ad5e01f60e227d468fe8975fcb390ed, 0x300000000000000000000000000000000000000000000000000000000008057fac184c50b174019580ba012cfc8ae8533f78c4b2ae778be2ba9533cfd8b64, 0x5263a46df065833e5d9800ba407381a7d9884b210b0543bd4cf67f848b5cf9fe),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x36363636363636363636363636363636363636363636363636363636363636365b92556408b553c68c36ae6b91b74576177dbeef8b75333db249c07ac8cf6abd, 0xd6b06bd38fc362a723946af0c9fe7f5d1270915847fa8e5c856f0d8cf7e90379),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c31f83f0e62df39ace65cc401fbdd2f1c7d17d485e11f5957d823aa10a2a500d7, 0xcba87472c52bcf72096cb5eb12adfcf1df51657d2e32f3f27ac92cc625427912),
  (0xd6b06bd38fc362a723946af0c9fe7f5d1270915847fa8e5c856f0d8cf7e90379, 0x8020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008002, 0x9f68112426fbf8fa21707ab7083905eb53b5f5158ddcdcc45bca198354752858),
  (0xcba87472c52bcf72096cb5eb12adfcf1df51657d2e32f3f27ac92cc625427912, 0x30000000000000000000000000000000000000000000000000000000000802411689ffaf8fb26b77a7021eb05390815f5b553c4dcdc8d8319ca5b58287554, 0x62b9d0eff189a011eaea9d1103e42b8b464400c962789453ac6b7661ac5a542c),
  (0xd6b06bd38fc362a723946af0c9fe7f5d1270915847fa8e5c856f0d8cf7e90379, 0x8020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008001, 0x2b4f516553a3fe85bb9e3c8a6c178585817e4b3a82f6ee43665d817de8f5592b),
  (0xcba87472c52bcf72096cb5eb12adfcf1df51657d2e32f3f27ac92cc625427912, 0x300000000000000000000000000000000000000000000000000000000008065514f2b85fea3538a3c9ebb8585176c3a4b7e8143eef6827d815d662b59f5e8, 0xc6adc16de8925e36722a8eda3064ed49aab29965e9a2bf851768703a5d267efb),
  (0xf8e04e32824a932ba392418164e5750fdf1228ea90daf2a09725214ff454dead, 0x3000000000000000000000000000000000000000000000000000000000080cadefa5c6f900fd54df7ba358925b01173c713bcf8bb6c42225255542779ac40, 0xe5318bfc37e7d1b45e412de6eed72f79f65b5da1790e135e7a77373c7a511e4b),
  (0x361d45a6deb82818753434b08e043a725dd8246737c9c5387abb6477d385480f, 0x3000000000000000000000000000000000000000000000000000000000080fc8b31e5b4d1e737e62d415e792fd7eea15d5bf65e130e793c37777a4b1e517a, 0x39063329fc5ccd99cd67bcec45626dcb5da2461371723a13f587221904086de8),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x36363636363636363636363636363636363636363636363636363636363636361f05300faffb6acada8a51fbfd5b54732570946b250c44472f14b1c3de5b3e32, 0xf34a896a2ce6ea4fd2af850b6faf2a5a4a0917084586f08e821fbfc954a64fd),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c756f5a65c59100a0b0e03b9197313e194f1afe014f662e2d457edba9b4315458, 0xb4b8069ab8e74118965c2dc5380dfb9824bf9049d11063f391f268d847811b3),
  (0xf34a896a2ce6ea4fd2af850b6faf2a5a4a0917084586f08e821fbfc954a64fd, 0x20030000000000000000000000000000000000000000000000000080017478654e206e696168432031562074656863746152205150206c616e67695302000000, 0x6546dcdfdf80f5ba1e7619ba6b08ae65ff5dba415f729b82257c7b73d6dd1e6f),
  (0xb4b8069ab8e74118965c2dc5380dfb9824bf9049d11063f391f268d847811b3, 0x3000000000000000000000000000000000000000000000000000000000080dfdc4665baf580dfba19761e65ae086b41ba5dff829b725f737b7c256f1eddd6, 0x7d3faf47d64966a4ca06c4145ff88496c578aefd23ebe3c3592bee538dd8c2e7),
  (0xf34a896a2ce6ea4fd2af850b6faf2a5a4a0917084586f08e821fbfc954a64fd, 0x4e206e696168432031562074656863746152205150206c616e6769530200000047af3f7da46649d614c406ca9684f85ffdae78c5c3e3eb2353ee2b59e7c2d88d, 0x560b505fae731224ca3a1230b60180caec369e8329638bc99033be7683d5a342),
  (0x560b505fae731224ca3a1230b60180caec369e8329638bc99033be7683d5a342, 0x20040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008002747865, 0x823d6521fd1327083839d134dff02aeb0a040f4ac2c1e87d97d462f428406920),
  (0xb4b8069ab8e74118965c2dc5380dfb9824bf9049d11063f391f268d847811b3, 0x300000000000000000000000000000000000000000000000000000000008021653d82082713fd34d13938eb2af0df4a0f040a7de8c1c2f462d49720694028, 0xdeb31915df78842d35f87a615c44b4f591d33f69cc1d995712a29e942011abea),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636232f85e81bb24ee9574cce03c382726a5f09e5a761af2bfaa2a89424dc9d2716, 0xdf0241cd5242224bd3a98855b88fbd8255a8e5b42e7c6fa0c1b144439a675639),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c4945ef8271d824833d26a469a9e8180035638fcd0bc54190c8c2fe4eb6f74d7c, 0xacc376ed50e7aeea66a84daeb72b3d8fa04312a67a81ab7fa6e70631dbce218c),
  (0xdf0241cd5242224bd3a98855b88fbd8255a8e5b42e7c6fa0c1b144439a675639, 0x30000000000000000000000000000000000000000000000000000000000806dc1adc6365e92e8da8e2a7249ed64306599b2aa85bfa2e93a706817fb7e265d, 0x1348bac97cb7a64a217bfb174aa295845e76de82e3c3bc65c1c2545ffa71e1c6),
  (0xacc376ed50e7aeea66a84daeb72b3d8fa04312a67a81ab7fa6e70631dbce218c, 0x3000000000000000000000000000000000000000000000000000000000080c9ba48134aa6b77c17fb7b218495a24a82de765e65bcc3e35f54c2c1c6e171fa, 0x2f99cfe617c749b5040fc50f0831baceae84661661803a025da260dfa7485115),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636d0f9af19837ff12139f33932f88c073e2050b298340cb657e956946b23677e91, 0xdce4317fca5ab2cfaf3b64f0b2c23651d9585515fbae984d219c93737a58bbdf),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5cba93c573e9159b4b5399535892e66d544a3ad8f25e66dc3d833cfe01490d14fb, 0xe6c2d6b36b4ecf427298035f646c029f76bc84795d56c1ba64fcf9358f622324),
  (0xdce4317fca5ab2cfaf3b64f0b2c23651d9585515fbae984d219c93737a58bbdf, 0x980200000000000000000000000000000000000000000000000000000000000000000000000000000000000080017379654b6567617373654d72657073696857, 0xaa1d06099faf2ed770445a0cc89cbd3421248d66a25c3a9031d09f804a68c4e7),
  (0xe6c2d6b36b4ecf427298035f646c029f76bc84795d56c1ba64fcf9358f622324, 0x300000000000000000000000000000000000000000000000000000000008009061daad72eaf9f0c5a447034bd9cc8668d2421903a5ca2809fd031e7c4684a, 0x6cb5586735178d53cf58521e843fbe995131d8de8c1e9c867a9a29d893a513bd),
  (0xdce4317fca5ab2cfaf3b64f0b2c23651d9585515fbae984d219c93737a58bbdf, 0x98030000000000000000000080027379654b6567617373654d726570736968576758b56c538d17351e5258cf99be3f84ded83151869c1e8cd8299a7abd13a593, 0x365dc4b47547891719795e9511bd816b88ce0535fcb0bd6ed13bee3b2709a4da),
  (0xe6c2d6b36b4ecf427298035f646c029f76bc84795d56c1ba64fcf9358f622324, 0x3000000000000000000000000000000000000000000000000000000000080b4c45d3617894775955e79196b81bd113505ce886ebdb0fc3bee3bd1daa40927, 0xf6a7a9131f3b94636a4391555f622e5627b3a8a88ecda80819418b2457e776fe),
  (0xdce4317fca5ab2cfaf3b64f0b2c23651d9585515fbae984d219c93737a58bbdf, 0x98030000000000000000000080037379654b6567617373654d7265707369685713a9a7f663943b1f5591436a562e625fa8a8b32708a8cd8e248b4119fe76e757, 0xb7f97a650ef70a182ba40cfebf171339353dd752d902d9a60bcdd875c2b1ae52),
  (0xe6c2d6b36b4ecf427298035f646c029f76bc84795d56c1ba64fcf9358f622324, 0x3000000000000000000000000000000000000000000000000000000000080657af9b7180af70efe0ca42b391317bf52d73d35a6d902d975d8cd0b52aeb1c2, 0x67e07d1d7e789f063ac94c59956abed4c0bbc3b5d175160733eba28cdb0ffaf),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636259f91c055a20d2963a7755c601854699e9e85113e9efbb812bd772fc840d161, 0x6629cc472d8d75e9ad0665c114fdaba51ec5fe0d1421ac5c3f2921004fd1ceef),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c4ff5fbaa3fc8674309cd1f360a723e03f4f4ef7b54f491d278d71d45a22abb0b, 0x7bfd706572848763585a8436cd6fd5b023a04d86c20a495dd2160d5850f6af41),
  (0x6629cc472d8d75e9ad0665c114fdaba51ec5fe0d1421ac5c3f2921004fd1ceef, 0xac8bff0348b0c032b515e585e882aa28244c58ceadfb6f2c8876f3506df7053c01432d659f6956d79efdb84cf363bd3effef89cb39f4513184d598b479f75a05, 0xc9fc3973f515b81036437a5d3b82ee4f486274a93baff9b1913b74ebeba57825),
  (0xc9fc3973f515b81036437a5d3b82ee4f486274a93baff9b1913b74ebeba57825, 0x101252a884f40bdd047e18767282d49485b5ca01022001801104ae020f0133ecd4a8abe6ff58f162cef8c18ef9d7411918dad639572eb5d162705210a44627f, 0xc2ca1f1ff8505d5ceb8fb6b5dff0fb3af767d26124f21bdfeecd2e81ddc0f6c6),
  (0xc2ca1f1ff8505d5ceb8fb6b5dff0fb3af767d26124f21bdfeecd2e81ddc0f6c6, 0x9d4c8b7a102f3e5d00016b5a4f3e2d1c0b9a5f4e4d3b2e1c6f8a002432c5dfa53708ac5adfa9c2afd695fb8d5722060dfb58d3c7074b5508b4c4e50286010102, 0xbf12e260efae36a5dccca7336af247a6b7148d99c9c389354478b3a581c77474),
  (0xbf12e260efae36a5dccca7336af247a6b7148d99c9c389354478b3a581c77474, 0x4808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008001f6e5d4c3b2a10f8e, 0x4f2f90b7d1dfc5c96e668f5e15da5cccf51ec92f7a1e742c6cd0303523033223),
  (0x7bfd706572848763585a8436cd6fd5b023a04d86c20a495dd2160d5850f6af41, 0x3000000000000000000000000000000000000000000000000000000000080b7902f4fc9c5dfd15e8f666ecc5cda152fc91ef52c741e7a3530d06c23320323, 0x4e8febb4cea7246e008e90a86da5f10d299749d15654d783e5ad80f4166e917b)
]

/-- SHA-256 compression for `compI0`: returns `compDefaultSha256 st blk` whenever `st` starts with
`compTag4` or `blk` starts with `compTag4`, `compTag4Ipad`, or `compTag4Opad`, and otherwise looks
up `(st, blk)` in `compSha256Rows` with fallback `compDefaultSha256 st blk`. -/
def compSha256 (st blk : HwBytes) : HwBytes :=
  if st.take 4 == compTag4 || blk.take 4 == compTag4 ||
     blk.take 4 == compTag4Ipad || blk.take 4 == compTag4Opad then
    compDefaultSha256 st blk
  else if st.length == 32 && blk.length == 64 then
    let kSt := bytesToNat st
    let kBlk := bytesToNat blk
    match compSha256Rows.find? (fun r => r.1 == kSt && r.2.1 == kBlk) with
    | some (_, _, outNat) => leBytes 32 outNat
    | none => compDefaultSha256 st blk
  else
    compDefaultSha256 st blk

def compOtherExtern (s : StubSymbol) (args : List ByteString) : Option ByteString :=
  if s = sha512CompressSymbol then
    match args with | [st, blk] => some (compSha512 st blk) | _ => some (List.replicate 64 0#8)
  else if s = edwardsCompressSymbol then
    match args with | [pt] => some (compEdwardsCompress pt) | _ => some (List.replicate 32 0#8)
  else if s = edwardsNegSymbol then
    match args with | [pt] => some (compEdwardsNeg pt) | _ => some (List.replicate 160 0#8)
  else if s = doubleScalarMulSymbol then
    match args with | [a, pt, b] => some (compDoubleScalarMul a pt b) | _ => some (List.replicate 160 0#8)
  else if s = scalarModOrderSymbol then
    match args with | [b] => some (compScalarModOrder b) | _ => some (List.replicate 32 0#8)
  else if s = scalarModOrderWideSymbol then
    match args with | [b] => some (compScalarModOrderWide b) | _ => some (List.replicate 32 0#8)
  else if s = mlkem768FromSeedSymbol then
    match args with | [seed] => some (compMlkem768FromSeed seed) | _ => some (List.replicate 2400 0#8)
  else if s = mlkem768Encaps1Symbol then some (List.replicate (960 + 2080 + 32) 0#8)
  else if s = mlkem768Encaps2Symbol then some (List.replicate 128 0#8)
  else if s = mlkem768DecapsSymbol then some (List.replicate 32 0#8)
  else if s = mlkem768ValidatePkSymbol then some []
  else none

/-- Table-driven `ExternInterpretation` shared across the composed bug-injection witnesses. -/
def compI0 : ExternInterpretation :=
  fun s args =>
    if s = x25519PublicKeySymbol then
      match args with | [sk] => some (compLookupPub sk) | _ => none
    else if s = x25519AgreementSymbol then
      match args with | [sk, pk] => some (compLookupDh sk pk) | _ => none
    else if s = x25519TorsionSymbol then
      match args with | [point, [b]] => compLookupTorsion point b | _ => none
    else if s = aesCbcEncryptSymbol then
      match args with | [text, k, iv] => some (compAesPerm k iv text) | _ => none
    else if s = aesCbcDecryptSymbol then
      match args with | [ct, k, iv] => compAesDec k iv ct | _ => none
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
      match args with | [st, blk] => some (compSha256 st blk) | _ => some (compDefaultSha256 [] [])
    else
      compOtherExtern s args

end Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0

abbrev DY.Libsignal.Refinement.CryptoEquationsHold := DY.Libsignal.Refinement.ExternCryptoLawsHold
abbrev DY.Libsignal.PQXDH.Refinement.X25519PubTorsionShiftsRejected := DY.Libsignal.PQXDH.Refinement.X25519TorsionShiftsRejected
abbrev DY.Libsignal.Composed.Refinement.CompInterpretationTotal := DY.Libsignal.Composed.Refinement.ExternInterpretationTotalOnUsedSymbols
abbrev DY.Libsignal.Composed.Refinement.Records := DY.Libsignal.Composed.Refinement.ProtocolSetup
abbrev DY.Libsignal.Composed.Refinement.RecordsWF := DY.Libsignal.Composed.Refinement.ProtocolSetupWF
abbrev DY.Libsignal.Composed.Refinement.Sem := DY.Libsignal.Composed.Refinement.OpaqueSymbolSemantics
abbrev DY.Libsignal.Composed.Refinement.BobStartCollision := DY.Libsignal.Composed.Refinement.BobSessionStartCollidesOrImplicitRejects
abbrev DY.Libsignal.Composed.CEvent := DY.Libsignal.Composed.ComposedEvent
abbrev Symbolic.BugInjection.Records := DY.Libsignal.Composed.Refinement.ProtocolSetup
abbrev DY.X25519.x25519Key := DY.X25519.normalizeX25519Key
abbrev DY.Spqr.spqrIdx := DY.Spqr.encodeSpqrIndexTerm
abbrev DY.Spqr.spqrParams := DY.Spqr.encodeSpqrDirectionParams
abbrev DY.Libsignal.TripleRatchet.TRState.sinfo (st : DY.Libsignal.TripleRatchet.TRState) (me : DY.Participant) := st.sessionInfo me
namespace DY.Libsignal.Composed.Refinement
abbrev Compat := GhostAndSemMatchSetup
abbrev OwnSaltMacCollision := MacTagForgeryOrCollision
abbrev Kind := VisEventKind
abbrev Kind.rng := VisEventKind.rng
abbrev Kind.send := VisEventKind.send
abbrev Kind.recv := VisEventKind.recv
abbrev Kind.pt := VisEventKind.pt
abbrev Kind.accept := VisEventKind.accept
abbrev Kind.leak := VisEventKind.leak
abbrev G := ConcretizedTerm
abbrev ConcretizedTerm.val := ConcretizedTerm.bytes
abbrev uOf := x25519UCoord
abbrev gRandom := concretizeRandom
abbrev gLit0 := concretizeLit
abbrev gConcat0 := concretizeConcat
abbrev gDhPk := concretizeDhPk
abbrev gDh := concretizeDh
abbrev gKdf0 := concretizeKdf
abbrev gSym0 := concretizeSym
abbrev gTrunc0 := concretizeTrunc
abbrev gVariant0 := concretizeVariant
abbrev gTrWire0 := concretizeTrWire
abbrev gKemPk := concretizeKemPk
abbrev gKemEncap := concretizeKemEncap
abbrev gKemSS := concretizeKemSS
abbrev gKemRej := concretizeKemRej
abbrev gVk := concretizeVk
abbrev gSign := concretizeSign
abbrev gSpqrInit := concretizeSpqrInit
abbrev gSpqrSendState := concretizeSpqrSendState
abbrev gSpqrSendKey := concretizeSpqrSendKey
abbrev gSpqrSendMsg := concretizeSpqrSendMsg
abbrev gSpqrRecvState := concretizeSpqrRecvState
abbrev gSpqrRecvKey := concretizeSpqrRecvKey
abbrev gSpqrChainKey := concretizeSpqrChainKey
abbrev gAll := concretizeAll
end DY.Libsignal.Composed.Refinement
