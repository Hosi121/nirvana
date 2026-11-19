#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <setjmp.h>

#ifndef NV_INSTRUCTION_LIMIT
#define NV_INSTRUCTION_LIMIT UINT64_C(10000000)
#endif
#ifndef NV_IMPORT_LIMIT
#define NV_IMPORT_LIMIT UINT64_C(10000)
#endif

struct nv_module {
    uint64_t r[80];
    uint8_t *memory;
    uint64_t base,size,pc,errno_address,instructions_left,imports_left,started;
    unsigned status;
    uint64_t fault_address,fault_width;
    unsigned fault_access;
    jmp_buf jump;
};

static inline uint64_t nv_check(struct nv_module *s,uint64_t address,uint64_t width,unsigned access) {
    /* Subtract only after establishing the lower bound. This permits an empty
       range at the one-past address while rejecting all wrapping ranges. */
    if(address<s->base || width>s->size || address-s->base>s->size-width ||
       (width!=0 && address>UINT64_MAX-(width-1))) {
        s->status=1; s->fault_address=address; s->fault_width=width; s->fault_access=access;
        longjmp(s->jump,1);
    }
    return address-s->base;
}
static inline uint64_t nv_read(struct nv_module *s,uint64_t address,unsigned width) {
    if(width!=1 && width!=2 && width!=4 && width!=8) {
        s->status=1; s->fault_address=address; s->fault_width=width; s->fault_access=1;
        longjmp(s->jump,1);
    }
    uint64_t offset=nv_check(s,address,width,1), value=0;
    for(unsigned i=0;i<width;++i) value|=(uint64_t)s->memory[offset+i]<<(i*8);
    return value;
}
static inline void nv_write(struct nv_module *s,uint64_t address,unsigned width,uint64_t value) {
    if(width!=1 && width!=2 && width!=4 && width!=8) {
        s->status=1; s->fault_address=address; s->fault_width=width; s->fault_access=2;
        longjmp(s->jump,1);
    }
    uint64_t offset=nv_check(s,address,width,2);
    for(unsigned i=0;i<width;++i) s->memory[offset+i]=(uint8_t)(value>>(i*8));
}
struct nirvana_memory { struct nv_module *state; };
static inline uint64_t nirvana_offset(struct nirvana_memory *m,uint64_t address,uint64_t width) {
    return nv_check(m->state,address,width,2);
}
static inline uint64_t nirvana_load(struct nirvana_memory *m,uint64_t address,unsigned width) {
    return nv_read(m->state,address,width);
}
static inline void nirvana_store(struct nirvana_memory *m,uint64_t address,unsigned width,uint64_t value) {
    nv_write(m->state,address,width,value);
}
static inline unsigned nv_step(struct nv_module *s) {
    if(s->instructions_left==0) { s->status=4; return 0; }
    --s->instructions_left; ++s->started;
    return 1;
}
