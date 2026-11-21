/* Unsigned limb arithmetic implements DIV/IDIV without C signed overflow,
   division by zero, oversized shifts, or nonstandard integer extensions. */
static inline unsigned nv_unsigned_divide(uint64_t high,uint64_t low,uint64_t divisor,
                                          unsigned bits,uint64_t mask,uint64_t *quotient,uint64_t *remainder) {
    if(divisor==0 || high>=divisor) return 0;
    uint64_t q=0,r=high;
    for(unsigned i=bits;i!=0;--i) {
        unsigned carry=(unsigned)(r>>(bits-1));
        r=((r<<1)|((low>>(i-1))&UINT64_C(1)))&mask;
        if(carry || r>=divisor) {
            r=(r-divisor)&mask;
            q|=UINT64_C(1)<<(i-1);
        }
    }
    *quotient=q; *remainder=r;
    return 1;
}
static inline unsigned nv_divide(unsigned bits,unsigned is_signed,uint64_t rax,uint64_t rdx,
                                 uint64_t source,uint64_t *out_rax,uint64_t *out_rdx) {
    if(bits!=8 && bits!=16 && bits!=32 && bits!=64) return 0;
    uint64_t mask=UINT64_MAX>>(64-bits);
    uint64_t low=rax&mask, high=(bits==8 ? rax>>8 : rdx)&mask, divisor=source&mask;
    unsigned negative_n=0,negative_d=0;
    if(is_signed) {
        negative_n=(unsigned)(high>>(bits-1));
        negative_d=(unsigned)(divisor>>(bits-1));
        if(negative_n) {
            low=(UINT64_C(0)-low)&mask;
            high=(~high+(low==0 ? UINT64_C(1) : UINT64_C(0)))&mask;
        }
        if(negative_d) divisor=(UINT64_C(0)-divisor)&mask;
    }
    uint64_t quotient,remainder;
    if(!nv_unsigned_divide(high,low,divisor,bits,mask,&quotient,&remainder)) return 0;
    if(is_signed) {
        uint64_t half=UINT64_C(1)<<(bits-1);
        unsigned negative_q=negative_n^negative_d;
        if(quotient>half-(negative_q ? UINT64_C(0) : UINT64_C(1))) return 0;
        if(negative_q) quotient=(UINT64_C(0)-quotient)&mask;
        if(negative_n) remainder=(UINT64_C(0)-remainder)&mask;
    }
    if(bits==8) {
        *out_rax=(rax&~UINT64_C(65535))|quotient|(remainder<<8);
        *out_rdx=rdx;
    } else if(bits==16) {
        *out_rax=(rax&~mask)|quotient;
        *out_rdx=(rdx&~mask)|remainder;
    } else {
        *out_rax=quotient;
        *out_rdx=remainder;
    }
    return 1;
}
