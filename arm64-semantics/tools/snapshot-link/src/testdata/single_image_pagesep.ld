PHDRS {
  phdr PT_PHDR PHDRS;
  hdr PT_LOAD FILEHDR PHDRS FLAGS(4);
  imgtext PT_LOAD FLAGS(5);
  imgro PT_LOAD FLAGS(4);
  imgdata PT_LOAD FLAGS(6);
  imggot PT_LOAD FLAGS(4);
  text PT_LOAD FLAGS(5);
  ro PT_LOAD FLAGS(4);
  data PT_LOAD FLAGS(6);
  tls PT_TLS;
  stack PT_GNU_STACK FLAGS(6);
}
SECTIONS {
  . = 0x3ff000 + SIZEOF_HEADERS;
  . = 0x400000;
  .img.text : {
    . = 0x400000;
    *img0.o(".text")
    . = 0x400040;
    *img0.o(".text.f")
    . = 0x400080;
    *(.text.__snapstub_0)
  } :imgtext =0
  . = 0x401000;
  .img.rodata : {
    . = 0x401000;
    *img0.o(".rodata")
    . = 0x401fff;
    BYTE(0);
  } :imgro =0
  . = 0x402000;
  .img.data : {
    . = 0x402000;
    *img0.o(".data")
  } :imgdata =0
  . = 0x402010;
  .img.bss (NOLOAD) : {
    . = 0x402010;
    *img0.o(".bss")
  } :imgdata
  .img.extdata : {
    . = 0x402020;
    *(.data.__snapextdata_0)
  } :imgdata =0
  . = 0x403000;
  .img.got : {
    . = 0x403000;
    *(.rodata.__snapgot)
  } :imggot =0
  . = 0x403010;
  .img.got.pad : {
    . = 0x403010;
    BYTE(0);
    . = 0x403fff;
    BYTE(0);
  } :imggot =0
  . = ALIGN(0x1000);
  .text : { *(.text .text.*) } :text
  . = ALIGN(0x1000);
  .rodata : { *(.rodata .rodata.*) } :ro
  . = ALIGN(0x1000);
  .tdata : { *(.tdata .tdata.*) } :data :tls
  .tbss : { *(.tbss .tbss.*) } :data :tls
  .init_array : { KEEP(*(.init_array*)) } :data
  .fini_array : { KEEP(*(.fini_array*)) } :data
  .data : { *(.data .data.*) } :data
  .bss : { *(.bss .bss.* COMMON) } :data
  /DISCARD/ : { *(.eh_frame) *(.comment) *(.note*) *(.llvm_addrsig) }
}
