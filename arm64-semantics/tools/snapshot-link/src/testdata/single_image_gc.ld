PHDRS {
  phdr PT_PHDR PHDRS;
  hdr PT_LOAD FILEHDR PHDRS;
  imgtext PT_LOAD;
  imgdata PT_LOAD;
  text PT_LOAD;
  ro PT_LOAD;
  data PT_LOAD;
  tls PT_TLS;
  stack PT_GNU_STACK FLAGS(6);
}
SECTIONS {
  . = 0x3ff000 + SIZEOF_HEADERS;
  . = 0x400000;
  .img.text : {
    . = 0x400000;
    KEEP(*img0.o(".text"))
    . = 0x400040;
    KEEP(*img0.o(".text.f"))
    . = 0x400080;
    KEEP(*(.text.__snapstub_0))
  } :imgtext =0
  . = 0x401000;
  .img.data : {
    . = 0x401000;
    KEEP(*img0.o(".rodata"))
  } :imgdata
  .img.bss (NOLOAD) : {
    . = 0x401080;
    KEEP(*img0.o(".bss"))
  } :imgdata
  .img.extdata : {
    . = 0x401100;
    KEEP(*(.rodata.__snapextdata_0))
  } :imgdata
  . = 0x401110;
  .img.got : {
    . = 0x401110;
    KEEP(*(.rodata.__snapgot))
  } :imgdata
  . = ALIGN(0x1000);
  .text : { *(.text .text.*) } :text
  . = ALIGN(0x1000);
  .rodata : { *(.rodata .rodata.*) } :ro
  . = ALIGN(0x1000);
  .tdata : { *(.tdata .tdata.*) } :data :tls
  .tbss : { *(.tbss .tbss.*) } :data :tls
  .init_array : { KEEP(*(.init_array*)) } :data
  .fini_array : { KEEP(*(.fini_array*)) }
  .data : { *(.data .data.*) }
  .bss : { *(.bss .bss.* COMMON) }
  /DISCARD/ : { *(.eh_frame) *(.gcc_except_table*) *(.comment) *(.note*) *(.llvm_addrsig) }
}
