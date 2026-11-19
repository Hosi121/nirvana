pub(super) const HEADER: &str = r#"
/* Status: returned, memory fault, unknown target, missing outcome, invalid
   outcome, instruction/read/output/call budget. Output is modeled byte data. */
enum nirvana_effect_status {
    NIRVANA_RETURNED=0,NIRVANA_MEMORY_FAULT=1,NIRVANA_UNKNOWN_TARGET=2,
    NIRVANA_MISSING_OUTCOME=3,NIRVANA_INVALID_OUTCOME=4,
    NIRVANA_INSTRUCTION_LIMIT=5,NIRVANA_READ_LIMIT=6,
    NIRVANA_OUTPUT_LIMIT=7,NIRVANA_CALL_LIMIT=8
};
struct nirvana_puts_outcome {
    uint64_t registers[14];
    unsigned all;
    uint64_t prefix;
};
struct nirvana_effects {
    const struct nirvana_puts_outcome *outcomes;
    uint64_t outcome_count;
    uint8_t *output;
    uint64_t output_capacity;
    uint64_t instructions_left, external_reads_left, calls_left;
    unsigned status;
    uint64_t result, output_size, consumed, started, instruction;
    uint64_t fault_address, fault_width, unknown_target;
    unsigned fault_access;
};
struct nirvana_memory {
    uint8_t *bytes;
    uint64_t base,size;
    struct nirvana_effects *effects;
    jmp_buf *jump;
};
static inline uint64_t nirvana_checked_offset(struct nirvana_memory *m,uint64_t address,uint64_t width,unsigned access) {
    if(width==0 || address>UINT64_MAX-(width-1) || address<m->base || width>m->size || address-m->base>m->size-width) {
        m->effects->status=1; m->effects->fault_address=address; m->effects->fault_width=width; m->effects->fault_access=access;
        longjmp(*m->jump,1);
    }
    return address-m->base;
}
static inline uint64_t nirvana_offset(struct nirvana_memory *m,uint64_t address,uint64_t width) {
    return nirvana_checked_offset(m,address,width,2);
}
static inline uint64_t nirvana_load(struct nirvana_memory *m,uint64_t address,unsigned width) {
    uint64_t offset=nirvana_checked_offset(m,address,width,1), value=0;
    for(unsigned i=0;i<width;++i) value|=(uint64_t)m->bytes[offset+i]<<(i*8);
    return value;
}
static inline void nirvana_store(struct nirvana_memory *m,uint64_t address,unsigned width,uint64_t value) {
    uint64_t offset=nirvana_offset(m,address,width);
    for(unsigned i=0;i<width;++i) m->bytes[offset+i]=(uint8_t)(value>>(i*8));
}
static inline unsigned nirvana_puts(struct nirvana_memory *m,uint64_t *r,uint64_t address) {
    static const unsigned volatile_registers[14]={0,1,2,6,7,8,9,10,11,16,17,18,19,20};
    struct nirvana_effects *e=m->effects;
    if(e->calls_left==0) {e->status=8;return 0;}
    uint64_t length=0, cursor=address;
    for(;;) {
        if(e->external_reads_left==0) {e->status=6;return 0;}
        --e->external_reads_left;
        uint64_t byte=nirvana_load(m,cursor,1);
        if(byte==0) break;
        ++length; ++cursor;
    }
    if(e->consumed>=e->outcome_count) {e->status=3;return 0;}
    const struct nirvana_puts_outcome *outcome=&e->outcomes[e->consumed];
    uint64_t full=length+1, written=outcome->all?full:outcome->prefix;
    if(outcome->all>1 || written>full || (!(outcome->registers[0]&UINT64_C(0x80000000)) && written!=full)) {
        e->status=4;return 0;
    }
    for(unsigned i=9;i<14;++i) if(outcome->registers[i]>1) {e->status=4;return 0;}
    if(written>e->output_capacity-e->output_size) {e->status=7;return 0;}
    uint64_t copied=written<length?written:length;
    for(uint64_t i=0;i<copied;++i) e->output[e->output_size+i]=m->bytes[address-m->base+i];
    if(written>length) e->output[e->output_size+length]='\n';
    e->output_size+=written;
    for(unsigned i=0;i<14;++i) r[volatile_registers[i]]=outcome->registers[i];
    ++e->consumed; --e->calls_left;
    return 1;
}
static inline unsigned nirvana_step(struct nirvana_memory *m,uint64_t address) {
    struct nirvana_effects *e=m->effects;
    e->instruction=address;
    if(e->instructions_left==0) {e->status=5;return 0;}
    --e->instructions_left; ++e->started;
    return 1;
}
enum nirvana_target_kind {
    NIRVANA_DIRECT_TARGET=0,NIRVANA_MEMORY_TARGET=1,NIRVANA_PLT_TARGET=2
};
/* kind: direct/register value, indirect memory operand, direct PLT slot. */
static inline unsigned nirvana_call_puts(struct nirvana_memory *m,uint64_t *r,unsigned kind,uint64_t operand,uint64_t next,unsigned tail,uint64_t puts_address) {
    uint64_t target=kind==1?nirvana_load(m,operand,8):operand;
    if(!tail) {
        r[4]-=UINT64_C(8);
        nirvana_store(m,r[4],8,next);
    }
    if(kind==2) target=nirvana_load(m,operand,8);
    if(target!=puts_address) {
        m->effects->unknown_target=target; m->effects->status=2; return 0;
    }
    if(!nirvana_puts(m,r,r[7])) return 0;
    r[4]+=UINT64_C(8);
    return 1;
}
"#;
