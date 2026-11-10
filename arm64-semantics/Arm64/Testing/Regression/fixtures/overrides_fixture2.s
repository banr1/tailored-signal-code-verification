// Second translation unit of `overrides_fixture.elf`: a second local `STT_FUNC` named `dummy`
// (the first is in `overrides_fixture.s`), so `.symtab` holds two entries with that name.
.section .text.aux,"ax",@progbits
.type dummy, @function
dummy:
  ret
.size dummy, .-dummy
