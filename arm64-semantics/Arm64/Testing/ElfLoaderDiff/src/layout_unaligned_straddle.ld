ENTRY(_start)

PHDRS {
    rx  PT_LOAD FLAGS(5);
    ro  PT_LOAD FLAGS(4);
    rw  PT_LOAD FLAGS(6);
    stk PT_GNU_STACK FLAGS(6);
}

SECTIONS {
    /* `.text` (0x1e0 B) starts 0x100 B before a page boundary (file offset 0xf00). */
    . = 0x900f00;
    .text : { *(.text*) } :rx

    /* `.rodata` (0xc0 B) starts 0x40 B before a page boundary. */
    . = 0x903fc0;
    .rodata : { *(.rodata*) } :ro

    /* `.data` (0x180 B) starts 0x80 B before a page boundary; `.bss` crosses the next one. */
    . = 0x906f80;
    .data : { *(.data) } :rw
    .bss (NOLOAD) : { *(.bss) } :rw

    /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) }
}
