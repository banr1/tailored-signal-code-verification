ENTRY(_start)

PHDRS {
    phdr PT_PHDR PHDRS;
    ro   PT_LOAD FILEHDR PHDRS FLAGS(4);
    rx   PT_LOAD FLAGS(5);
    rw1  PT_LOAD FLAGS(6);
    rw2  PT_LOAD FLAGS(6);
    rw3  PT_LOAD FLAGS(6);
    stk  PT_GNU_STACK FLAGS(6);
}

SECTIONS {
    . = 0x400000 + SIZEOF_HEADERS;
    .rodata : { *(.rodata*) } :ro

    . = 0x410000;
    .text : { *(.text*) } :rx

    . = 0x420000;
    .rw1 : { *(.rw1_data) } :rw1

    . = 0x430000;
    .rw2_data : { *(.rw2_data) } :rw2
    .rw2_bss (NOLOAD) : { *(.rw2_bss) } :rw2

    . = 0x445000;
    .rw3_bss (NOLOAD) : { *(.rw3_bss) } :rw3

    /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) }
}
