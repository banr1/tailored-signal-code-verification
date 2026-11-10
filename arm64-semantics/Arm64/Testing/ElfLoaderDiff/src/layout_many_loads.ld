ENTRY(_start)

PHDRS {
    ro1  PT_LOAD FILEHDR PHDRS FLAGS(4);
    rx1  PT_LOAD FLAGS(5);
    ro2  PT_LOAD FLAGS(4);
    rw1  PT_LOAD FLAGS(6);
    ro3  PT_LOAD FLAGS(4);
    rx2  PT_LOAD FLAGS(5);
    rw2  PT_LOAD FLAGS(6);
    rw3  PT_LOAD FLAGS(6);
    stk  PT_GNU_STACK FLAGS(6);
}

/* Each segment starts on a new 4 KiB virtual page at the same page offset as its file offset,
   so consecutive segments share file pages without sharing virtual pages. */
SECTIONS {
    . = 0xc00000 + SIZEOF_HEADERS;
    .ro1 : { *(.ro1) } :ro1
    . = 0xc01000 + (. & 0xfff);
    .text1 : { *(.text1) } :rx1
    . = 0xc03000 + (. & 0xfff);
    .ro2 : { *(.ro2) } :ro2
    . = 0xc04000 + (. & 0xfff);
    .rw1 : { *(.rw1) } :rw1
    . = 0xc05000 + (. & 0xfff);
    .ro3 : { *(.ro3) } :ro3
    . = 0xc08000 + (. & 0xfff);
    .text2 : { *(.text2) } :rx2
    . = 0xc09000 + (. & 0xfff);
    .rw2 : { *(.rw2) } :rw2
    .bss2 (NOLOAD) : { *(.bss2) } :rw2
    . = 0xc0b000;
    .bss3 (NOLOAD) : { *(.bss3) } :rw3

    /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) }
}
