ENTRY(_start)

PHDRS {
    phdr  PT_PHDR PHDRS;
    ro    PT_LOAD FILEHDR PHDRS FLAGS(4);
    rx    PT_LOAD FLAGS(5);
    rw    PT_LOAD FLAGS(6);
    tls   PT_TLS FLAGS(4);
    relro PT_GNU_RELRO FLAGS(4);
    note  PT_NOTE FLAGS(4);
    stk   PT_GNU_STACK FLAGS(6);
}

SECTIONS {
    . = 0x400000 + SIZEOF_HEADERS;
    .note.ABI-tag : { KEEP(*(.note.ABI-tag)) } :ro :note
    .rodata : { *(.rodata*) } :ro

    . = 0x410000;
    .text : { *(.text*) } :rx

    . = 0x420000;
    .tdata : { *(.tdata) } :rw :tls :relro
    .tbss (NOLOAD) : { *(.tbss) } :tls
    .data.rel.ro : { *(.data.rel.ro) } :rw :relro
    . = ALIGN(0x1000);
    .data : { *(.data) } :rw
    .bss (NOLOAD) : { *(.bss) } :rw

    /DISCARD/ : { *(.comment) *(.eh_frame*) }
}
