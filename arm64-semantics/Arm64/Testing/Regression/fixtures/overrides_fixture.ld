/* Linker script of `overrides_fixture.elf`: two executable segments (`.text.aux` at `0x400000`,
   `.text.main` with `_start` at `0x40e000`) and one data segment at `0x410000`. */
ENTRY(_start)
PHDRS { aux PT_LOAD; main PT_LOAD; data PT_LOAD; }
SECTIONS {
  . = 0x400000;
  .text.aux : { *(.text.aux) } :aux
  . = 0x40e000;
  .text.main : { *(.text.main) } :main
  .text : { *(.text) } :main
  . = 0x410000;
  .data : { *(.data) } :data
  /DISCARD/ : { *(.comment) }
}
