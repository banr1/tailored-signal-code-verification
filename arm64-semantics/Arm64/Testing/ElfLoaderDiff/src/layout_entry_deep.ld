ENTRY(_start)

PHDRS {
    hdr PT_LOAD FILEHDR PHDRS FLAGS(4);
    rx  PT_LOAD FLAGS(5);
    rw  PT_LOAD FLAGS(6);
    stk PT_GNU_STACK FLAGS(6);
}

SECTIONS {
    . = 0x600000 + SIZEOF_HEADERS;
    .rodata : { *(.rodata*) } :hdr

    . = ALIGN(0x1000) + (. & 0xfff);
    .text : { *(.text.cold) *(.text.entry) } :rx

    . = ALIGN(0x1000) + (. & 0xfff);
    .data : { *(.data) } :rw
    .bss (NOLOAD) : { *(.bss) } :rw

    /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) }
}
