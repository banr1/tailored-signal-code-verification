ENTRY(_start)

PHDRS {
    ro  PT_LOAD FILEHDR PHDRS FLAGS(4);
    rx  PT_LOAD FLAGS(5);
    rw  PT_LOAD FLAGS(6);
    stk PT_GNU_STACK FLAGS(6);
}

SECTIONS {
    . = 0x800000 + SIZEOF_HEADERS;
    .rodata : { *(.rodata*) } :ro

    . = ALIGN(0x1000) + (. & 0xfff);
    .text : { *(.text*) } :rx

    . = ALIGN(0x1000) + (. & 0xfff);
    .data : { *(.data) } :rw
    .bss (NOLOAD) : { *(.bss) } :rw

    /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) }
}
