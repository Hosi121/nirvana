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

#ifndef NV_SPARSE_REGION_COUNT
#define NV_SPARSE_REGION_COUNT 0
#endif
#if NV_SPARSE_REGION_COUNT
struct nv_memory_region { uint64_t address,size,offset; unsigned permissions; };
static const struct nv_memory_region nv_regions[NV_SPARSE_REGION_COUNT] = NV_SPARSE_REGIONS;
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
#if NV_SPARSE_REGION_COUNT
    const unsigned permissions=access==0 ? 0 : access==1 ? 4 : 2;
    if(width && address>UINT64_MAX-width) goto nv_bad;
    for(unsigned i=0;i<NV_SPARSE_REGION_COUNT;++i) {
        const struct nv_memory_region *r=&nv_regions[i];
        const uint64_t end=r->address+r->size;
        uint64_t offset,covered;
        if(address<r->address) break;
        if(width==0 && address<=end) {
            offset=r->offset+(address-r->address);
            if(offset<=s->size) return offset;
            break;
        }
        if(address>=end) continue;
        offset=r->offset+(address-r->address); covered=address;
        if(offset>s->size || width>s->size-offset) break;
        for(unsigned j=i;j<NV_SPARSE_REGION_COUNT;++j) {
            r=&nv_regions[j];
            if(r->address>covered || (r->permissions&permissions)!=permissions) break;
            covered=r->address+r->size;
            if(address+width<=covered) return offset;
        }
        break;
    }
nv_bad:
    s->status=1; s->fault_address=address; s->fault_width=width; s->fault_access=access;
    longjmp(s->jump,1);
#else
    /* Subtract only after establishing the lower bound. This permits an empty
       range at the one-past address while rejecting all wrapping ranges. */
    if(address<s->base || width>s->size || address-s->base>s->size-width ||
       (width!=0 && address>UINT64_MAX-(width-1))) {
        s->status=1; s->fault_address=address; s->fault_width=width; s->fault_access=access;
        longjmp(s->jump,1);
    }
    return address-s->base;
#endif
}

static inline uint64_t nv_available(struct nv_module *s,uint64_t address,unsigned access) {
    uint64_t offset=nv_check(s,address,1,access);
#if NV_SPARSE_REGION_COUNT
    const unsigned permissions=access==1 ? 4 : 2;
    (void)offset;
    for(unsigned i=0;i<NV_SPARSE_REGION_COUNT;++i) {
        const struct nv_memory_region *r=&nv_regions[i];
        if(address>=r->address && address<r->address+r->size) {
            uint64_t end=r->address+r->size;
            for(unsigned j=i+1;j<NV_SPARSE_REGION_COUNT;++j) {
                r=&nv_regions[j];
                if(r->address!=end || (r->permissions&permissions)!=permissions) break;
                end=r->address+r->size;
            }
            return end-address;
        }
    }
    return 0; /* nv_check established a containing accessible region. */
#else
    return s->size-offset;
#endif
}
#define NV_GUEST_REMAINING(s,a) nv_available((s),(a),1)
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
static inline void nv_string_transfer(struct nv_module *s,unsigned width,unsigned repeat,unsigned copy) {
    while(!repeat || s->r[1]!=0) {
        uint64_t value=copy?nv_read(s,s->r[6],width):s->r[0];
        nv_write(s,s->r[7],width,value);
        uint64_t delta=(s->r[29]&1)?UINT64_C(0)-width:width;
        s->r[7]+=delta;
        if(copy) s->r[6]+=delta;
        if(repeat) --s->r[1]; else break;
    }
}
static inline void nv_stos(struct nv_module *s,unsigned width,unsigned repeat) {
    nv_string_transfer(s,width,repeat,0);
}
static inline void nv_movs(struct nv_module *s,unsigned width,unsigned repeat) {
    nv_string_transfer(s,width,repeat,1);
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
