#define _GNU_SOURCE
#include <assert.h>
#include <signal.h>
#include <setjmp.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <ucontext.h>
#include <unistd.h>

#define FLAGS UINT64_C(0x8c5)
#define STORE(op) __asm__ volatile("push %[initial]; popfq; " op "; pushfq; pop %[flags]; cld" : "+D"(pointer), "+c"(count), [flags]"=r"(flags) : "a"(value), [initial]"r"(initial) : "memory", "cc")
static void store(unsigned width,unsigned repeat,uint8_t **destination,uint64_t *remaining,uint64_t value,uint64_t initial,uint64_t *after) {
    uint8_t *pointer=*destination;uint64_t count=*remaining,flags;
    if(repeat) {
        switch(width) {
        case 1: STORE("rep stosb");break;
        case 2: STORE("rep stosw");break;
        case 4: STORE("rep stosl");break;
        default: STORE("rep stosq");break;
        }
    } else {
        switch(width) {
        case 1: STORE("stosb");break;
        case 2: STORE("stosw");break;
        case 4: STORE("stosl");break;
        default: STORE("stosq");break;
        }
    }
    *destination=pointer;*remaining=count;*after=flags;
}
static sigjmp_buf jump;
static uint64_t fault_count,fault_pointer,fault_flags;
static void fault(int signal,siginfo_t *info,void *context) {
    ucontext_t *u=context;(void)signal;(void)info;
    fault_count=(uint64_t)u->uc_mcontext.gregs[REG_RCX];
    fault_pointer=(uint64_t)u->uc_mcontext.gregs[REG_RDI];
    fault_flags=(uint64_t)u->uc_mcontext.gregs[REG_EFL];
    __asm__ volatile("cld" ::: "cc");
    siglongjmp(jump,1);
}
int main(void) {
    const uint64_t value=UINT64_C(0xf1e2d3c4b5a69788);
    uint8_t bytes[128],expected[128];
    for(unsigned width=1;width<=8;width*=2) for(unsigned repeat=0;repeat<2;++repeat)
        for(unsigned back=0;back<2;++back) for(unsigned n=0;n<=5;++n) {
            memset(bytes,0xa5,sizeof(bytes));memcpy(expected,bytes,sizeof(bytes));
            uint8_t *pointer=bytes+64;uint64_t count=n,flags;
            const unsigned elements=repeat?n:1;
            for(unsigned i=0;i<elements;++i)for(unsigned j=0;j<width;++j)
                expected[64+(back?-(int)(i*width):(int)(i*width))+j]=(uint8_t)(value>>(j*8));
            store(width,repeat,&pointer,&count,value,FLAGS|0x202|(back?0x400:0),&flags);
            assert(!memcmp(bytes,expected,sizeof(bytes)));
            assert(pointer==bytes+64+(back?-(int)(elements*width):(int)(elements*width)));
            assert(count==(repeat?0:n));assert((flags&(FLAGS|0x400))==(FLAGS|(back?0x400:0)));
        }
    struct sigaction action={0};action.sa_sigaction=fault;action.sa_flags=SA_SIGINFO;
    assert(sigaction(SIGSEGV,&action,0)==0);
    const size_t page=(size_t)sysconf(_SC_PAGESIZE);
    uint8_t *mapping=mmap(0,page*3,PROT_NONE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);assert(mapping!=MAP_FAILED);
    uint8_t *buffer=mapping+page;assert(mprotect(buffer,page,PROT_READ|PROT_WRITE)==0);
    for(volatile unsigned back=0;back<2;++back) {
        memset(buffer,0xa5,page);
        if(sigsetjmp(jump,1)==0) {
            uint8_t *pointer=back?buffer+8:buffer+page-16;uint64_t count=3,flags;
            store(8,1,&pointer,&count,value,FLAGS|0x202|(back?0x400:0),&flags);assert(0);
        }
        assert(fault_count==1);
        assert(fault_pointer==(uint64_t)(back?buffer-8:buffer+page));
        assert((fault_flags&(FLAGS|0x400))==(FLAGS|(back?0x400:0)));
        uint64_t first,second;memcpy(&first,back?buffer:buffer+page-16,8);memcpy(&second,back?buffer+8:buffer+page-8,8);
        assert(first==value && second==value);
    }
    assert(munmap(mapping,page*3)==0);return 0;
}
