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
static uintptr_t instruction;
#define MOVE(op) __asm__ volatile("push %[initial]; popfq; lea 1f(%%rip),%%r11; mov %%r11,%[pc]; 1: " op "; pushfq; pop %[flags]; cld" : "+S"(source), "+D"(destination), "+c"(count), [flags]"=r"(flags), [pc]"=m"(instruction) : [initial]"r"(initial) : "r11", "memory", "cc")
static void move(unsigned width,unsigned repeat,uint8_t **src,uint8_t **dst,uint64_t *remaining,uint64_t initial,uint64_t *after) {
    uint8_t *source=*src,*destination=*dst;uint64_t count=*remaining,flags;
    if(repeat) {
        switch(width) {
        case 1: MOVE("rep movsb");break;
        case 2: MOVE("rep movsw");break;
        case 4: MOVE("rep movsl");break;
        default: MOVE("rep movsq");break;
        }
    } else {
        switch(width) {
        case 1: MOVE("movsb");break;
        case 2: MOVE("movsw");break;
        case 4: MOVE("movsl");break;
        default: MOVE("movsq");break;
        }
    }
    *src=source;*dst=destination;*remaining=count;*after=flags;
}
static void reference(uint8_t *bytes,unsigned width,unsigned back,unsigned count,int source,int destination) {
    uint8_t element[8];
    for(unsigned i=0;i<count;++i) {
        memcpy(element,bytes+source,width);
        memcpy(bytes+destination,element,width);
        int delta=back?-(int)width:(int)width;
        source+=delta;destination+=delta;
    }
}
static sigjmp_buf jump;
static uint64_t fault_count,fault_source,fault_destination,fault_flags,fault_pc,fault_access;
static void fault(int signal,siginfo_t *info,void *context) {
    ucontext_t *u=context;(void)signal;(void)info;
    fault_count=(uint64_t)u->uc_mcontext.gregs[REG_RCX];
    fault_source=(uint64_t)u->uc_mcontext.gregs[REG_RSI];
    fault_destination=(uint64_t)u->uc_mcontext.gregs[REG_RDI];
    fault_flags=(uint64_t)u->uc_mcontext.gregs[REG_EFL];
    fault_pc=(uint64_t)u->uc_mcontext.gregs[REG_RIP];
    fault_access=(uint64_t)u->uc_mcontext.gregs[REG_ERR]&2;
    __asm__ volatile("cld" ::: "cc");
    siglongjmp(jump,1);
}
int main(void) {
    uint8_t bytes[160],expected[160];
    for(unsigned width=1;width<=8;width*=2) for(unsigned repeat=0;repeat<2;++repeat)
        for(unsigned back=0;back<2;++back) for(unsigned n=0;n<=5;++n)
            for(int overlap=-9;overlap<=9;++overlap) {
                for(unsigned i=0;i<sizeof(bytes);++i) bytes[i]=(uint8_t)(i*29+7);
                memcpy(expected,bytes,sizeof(bytes));
                uint8_t *source=bytes+72,*destination=bytes+72+overlap;
                uint64_t count=n,flags;
                unsigned elements=repeat?n:1;
                reference(expected,width,back,elements,72,72+overlap);
                move(width,repeat,&source,&destination,&count,FLAGS|0x202|(back?0x400:0),&flags);
                int delta=(back?-(int)width:(int)width)*(int)elements;
                assert(source==bytes+72+delta && destination==bytes+72+overlap+delta);
                assert(count==(repeat?0:n));assert(!memcmp(bytes,expected,sizeof(bytes)));
                assert((flags&(FLAGS|0x400))==(FLAGS|(back?0x400:0)));
            }
    for(unsigned width=1;width<=8;width*=2) for(unsigned back=0;back<2;++back) {
        uint8_t *source=(uint8_t *)(uintptr_t)1,*destination=(uint8_t *)(uintptr_t)UINTPTR_MAX;
        uint64_t count=0,flags;
        move(width,1,&source,&destination,&count,FLAGS|0x202|(back?0x400:0),&flags);
        assert((uintptr_t)source==1 && (uintptr_t)destination==UINTPTR_MAX && count==0);
        assert((flags&(FLAGS|0x400))==(FLAGS|(back?0x400:0)));
    }
    struct sigaction action={0};action.sa_sigaction=fault;action.sa_flags=SA_SIGINFO;
    assert(sigaction(SIGSEGV,&action,0)==0);
    const size_t page=(size_t)sysconf(_SC_PAGESIZE);
    uint8_t *mapping=mmap(0,page*6,PROT_NONE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);assert(mapping!=MAP_FAILED);
    uint8_t *src=mapping+page,*dst=mapping+page*4;
    assert(mprotect(src,page,PROT_READ|PROT_WRITE)==0 && mprotect(dst,page,PROT_READ|PROT_WRITE)==0);
    for(volatile unsigned width=1;width<=8;width*=2)
        for(volatile unsigned back=0;back<2;++back) for(volatile unsigned writing=0;writing<2;++writing) {
            for(size_t i=0;i<page;++i) { src[i]=(uint8_t)(i*29+7);dst[i]=0xa5; }
            uint8_t *source=writing?src+64:(back?src+width:src+page-2*width);
            uint8_t *destination=writing?(back?dst+width:dst+page-2*width):dst+64;
            uint8_t *initial_source=source,*initial_destination=destination;
            if(sigsetjmp(jump,1)==0) {
                uint64_t count=3,flags;
                move(width,1,&source,&destination,&count,FLAGS|0x202|(back?0x400:0),&flags);assert(0);
            }
            int delta=(back?-(int)width:(int)width)*2;
            assert(fault_count==1 && fault_source==(uintptr_t)initial_source+delta);
            assert(fault_destination==(uintptr_t)initial_destination+delta);
            assert(fault_pc==instruction && fault_access==(writing?2:0));
            assert((fault_flags&(FLAGS|0x400))==(FLAGS|(back?0x400:0)));
            for(unsigned i=0;i<2;++i) {
                int step=(back?-(int)width:(int)width)*(int)i;
                assert(!memcmp(initial_source+step,initial_destination+step,width));
            }
        }
    assert(munmap(mapping,page*6)==0);return 0;
}
