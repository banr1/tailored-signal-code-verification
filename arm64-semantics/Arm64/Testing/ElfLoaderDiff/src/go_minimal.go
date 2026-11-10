// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// Minimal static Go program (`GOOS=linux GOARCH=arm64 CGO_ENABLED=0`) for testing
// Go's unusual ELF64 segment layout (0x10000 text with embedded section headers,
// PT_NOTE `.note.go.buildid`, and large rwnoptrdata/bss segment) against `ElfImage.loadState`.
package main

import "os"

var (
	roSlice  = [4]uint64{0x1122334455667788, 0x99aabbccddeeff00, 0xdeadbeefcafebabe, 0x0102030405060708}
	bssTable [16384]byte
)

func main() {
	if len(os.Args) > 0 {
		bssTable[0] = byte(len(os.Args))
		bssTable[len(bssTable)-1] = byte(roSlice[0] & 0xff)
	}
}
