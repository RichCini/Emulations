/*
 * lsi11 processor simulator
 *
 * COPYRIGHT (c) 1993 R.W.Meister - All Rights Reserved
 *
 * V 1.0 - 22-Jun-93 - got enough working to enjoy it
 * V 1.1 - 10-Aug-93 - added LTC and LPT support
 * V 2.0 - 01-Sep-93 - command line arguments, file handling
 * V 2.1 - 11-Sep-93 - added Hazeltine 1510 terminal emulation
 * V 2.2 - 14-Sep-93 - doing ODT's I/O through h1510 routines
 * V 3.0 - 24-Dec-93 - added Extended Instruction Set
 * V 4.0 - 06-Jan-95 - using 64kb lookup table for instr. decode
 * V 4.1 - 08-Jan-95 - using 8kb lookup table for instr. decode
 * V 4.2 - 10-Jan-95 - using lookup table for branches
 * V 4.3 - 11-Jan-95 - ignoring fill characters in terminal output
 * V 4.4 - 13-Jan-95 - generating real 60hz ltc interrupts using pc timer
 * V 4.5 - 14-Jan-95 - using bioskbd to check if kbd chars available
 * V 4.6 - 25-Jan-95 - use direct port access for LPT
 * V 4.7 - 10-May-95 - improvements to H1510 emulator, ran LINT
 */

 /* RAC Notes:

    Built using OpenWatcom 1.9 on Windows XP or Watcom C 10.6 on Win31
    
    The following devices are at the standard CSR for the boards:
    - Console (DLV11): 177560
    - LTC (KW11-L): 177546
    - LPR (LPV11 Centronics): 177514
    - RXV11 (floppy): 177530-177536 (non-standard address, usually 177170)

    Comments:
    - The disk emulation code is a custom "PF" (personal computer floppy) device that
      sits at a custom device address. This may impact booting RT-11 as RT-11
      requires, I believe, the console and floppy to be at standard device addresses.

    - The default address for the RX11 is 177170-177173 vector 264 BR5
    
    - The RX01 is a SSSD IBM3270 format disk (77x26x128) for a raw size of 256,256, so
      a very standard underlying disk format.
 */

//#define DEBUG 1
//#define PROFILING 1
#define NOLTC   0       //0= disable LTC interrupt, 1= enable LTC1

#include <stdio.h>
#include <ctype.h>

#ifndef __TURBOC__
#include <sys/types.h>
#endif

#include <sys/stat.h>

#ifndef MSDOS
#include <sgtty.h>
#define OMODE 2
#define S_OUT putchar
#define HWD 0
#define LWD 1
#else
#include <stdlib.h>
#include <bios.h>
#include <dos.h>
#include <fcntl.h>
#include <io.h>
#include <malloc.h>
#include <string.h>
#include <time.h>
#include <conio.h>
//*** RAC
#include <i86.h>
#define OMODE (O_RDWR | O_BINARY)
#define S_OUT h_out
#define HWD 1
#define LWD 0
#endif

union {
    unsigned int uw;            /* as unsigned int */
    unsigned int * up;          /* as -> unsigned int */
} REG[8];                       /* general purpose registers */

#define SP REG[6]
#define PC REG[7]

unsigned int PSW;               /* processor status word & bits */
#define CBIT 0001
#define VBIT 0002
#define ZBIT 0004
#define NBIT 0010
#define TBIT 0020
#define IBIT 0200
#define BMSK 0361

/* branch truth table. a bit on means to take the specified branch. */
unsigned int btable[16] = {     /* indexed by low 4 bits of PSW */
    0052526,
    0114526,
    0062646,
    0124646,
    0054632,
    0114632,
    0064652,
    0124652,
    0053246,
    0115246,
    0063126,
    0125126,
    0055252,
    0115252,
    0065232,
    0125232
} ;

struct {
    unsigned int cr;            /* floppy control register @177530 */
    unsigned int bn;            /* floppy block number @177532 */
    unsigned int ba;            /* floppy memory address @177534 */
    unsigned int wc;            /* floppy word count @177536 */
} pf;
char ccsr[8];                   /* console registers @177560 */
char ltccsr[2];                 /* L.T.C. registers @177546 */
char lptcsr[4];                 /* line printer registers @177514 */
#define RCSR 0*2
#define RDBR 1*2
#define XCSR 2*2
#define XDBR 3*2

/* bits in control registers */
#define GO 1
#define RW 2
#define GETSIZE 4
#define IENABL 0100
#define READY 0200
#define ERRBIT 0100000
#define FTRACKS 80

/* hardware interrupt vectors */
#define T4VEC  0004
#define T10VEC 0010
#define BPTVEC 0014
#define IOTVEC 0020
#define EMTVEC 0030
#define TRPVEC 0034
#define KBDVEC 0060
#define TTYVEC 0064
#define LTCVEC 0100
#define LPTVEC 0200
#define PFVEC  0210

int icount;                     /* instruction counter for interrupts */
#define IBTWNI 100              /* instructions between checking for ints */
#define PENDIO 3                /* same as above but when I/O pending */

int intctl;                     /* interrupt control word & bits */
#define I_CONI 1
#define I_CONO 2
#define I_FLOP 4
#define I_LPT  8

#ifdef PROFILING
long icnts[20];                 /* for counting instruction groups */
long amodes[8][8];              /* ditto for addressing modes */
#endif
long begint;                    /* program starting time */
int drives[8];                  /* file descriptors for logical drives */
int fsizes[8];                  /* file sizes for logical drives */
char * fnames[8];               /* -> to logical disk file names */
int maxunit;                    /* highest unit number available (1-7) */
int sstep;                      /* single-stepping if -1 */
int wflag;                      /* wait flag */
int trcflg;                     /* trace control word */
unsigned int instr;             /* the actual instruction @PC++ */
unsigned int highpc;            /* largest value of PC allowable */
unsigned int oflag;             /* old terminal state */
unsigned int obreak;            /* break status */
char * cmem;                    /* -> memory arena */
char * srcadr;                  /* -> source */
char * effadr;                  /* -> destination */
#ifndef MSDOS
struct sgttyb ttyb;             /* for ioctl stuff */
char * iarray;                  /* instruction decode array */
#else
int ltccnt;                     /* line time clock ticks */
int lptport;                    /* line printer port */
union REGS dreg;                /* for intdos stuff */
struct SREGS sreg;
char far * trkbuf;              /* holds track buffer */
char far * farptr;              /* for track buffer */
char far * iarray;              /* instruction decode array */
void interrupt (*int70a)();     /* holds int70 handler address */
#endif

char gchar();                   /* function declaration */
int odt();                      /* function declaration */
int getea();                    /* function declaration */
#ifdef MSDOS
#ifdef PROFILING
void dumpcnts();                /* function declaration */
#endif
void scrout();                  /* function declaration */
void reseti();                  /* function declaration */
void rawtty();                  /* function declaration */
void diskio();                  /* function declaration */
void fileio();                  /* function declaration */
void flopio();                  /* function declaration */
void fmemcpy();                 /* function declaration */
void ivideo();                  /* function declaration */
void h_out();                   /* function declaration */
void showit();                  /* function declaration */
unsigned char h_in();           /* function declaration */
void getpos();                  /* function declaration */
void poscur();                  /* function declaration */
void cleol();                   /* function declaration */
void ttychr();                  /* function declaration */
void initia();                  /* function declaration */
void fillit();                  /* function declaration */
void interrupt int_70();

#define LEADIN '\176'           /* tilde (~) */
#define MAXCOL 79               /* # columns - 1 */
#define MAXROW 23               /* # rows - 1 */
#define VIDEOINT (void)int86(0x10,&dreg,&dreg)

int dflag, pflag, lflag, row, col, opage, omode, cstart, curend;
#endif

//int main(int argc, char *argv[])
int main(argc,argv)
int argc;
char ** argv;
{
    int cbit, nbit;             /* pre-operation bits */
    int i;                      /* general purpose */
    int j;                      /* general purpose */
    int k;                      /* general purpose */
    unsigned char ltcflg;       /* line time clock monitor */
    register unsigned int psw;  /* FAST processor status word */
    register unsigned int u;    /* general purpose */
    int vector;                 /* trap vector */
    char * p;                   /* for parsing command line args */
    unsigned int * intadr;      /* for getting integers */
    int gotleadin;              /* handles lead-in chars from h_in() */
    int *pp;                    /* used for getting the LPT port address */
    char pbuf[100];             /* for printing */
    union {
        unsigned int wd[2];
        long wds;
    } lw;                       /* for EIS */
    union {
        int ii;
        char aa[2];
    } sw[2];                    /* for swapping bytes */
    struct stat statbuf;        /* for file sizes */

    if (argc <= 1) {            /* need at least one logical drive */
        fprintf(stderr,"Usage: lsi11 drive_spec [...]\n");
        fprintf(stderr,"  If an MS-DOS drive letter (A/B) is specified, a real floppy\n");
        fprintf(stderr,"  disk is required. Otherwise, the name of a disk image in the\n");
        fprintf(stderr,"  current folder should be specified.\n");
        exit(1);
    } /* end if */
    ++argv; --argc;             /* skip over program name */

#ifdef MSDOS
//*** RAC
    //lptport = peek(0x40,0x8);   /* get printer port */
    pp = MK_FP(0x40,0x8);       /* get pointer to LPT from */
    //pp = (int *)0x0408;
    lptport = *pp;              /* dereference to get I/O port value */

//  iarray = (char far *)farcalloc(8192,1);
    iarray = (char far *) _fcalloc(8192,1);
#else
    iarray = (char *)calloc(8192,1);
#endif
    if (iarray == NULL) {
        fprintf(stderr,"Unable to allocate instruction array\n");
        exit(2);
    } /* end if */
    initia();                   /* initialize iarray */

    for (u = 0170000; u; u -= 010000) {
        if ((cmem = (char *)malloc(u)) != NULL) /* try for lots of memory */
            break;              /* got some */
    } /* end if */
    if (u >= 020000) {          /* did we get enough? */
        highpc = u - 1;         /* largest program address */
    }
    else {
        fprintf(stderr,"Unable to allocate sufficient memory\n");
        exit(2);
    } /* end if */

    i = 0;                      /* for indexing into drives array */
    while (argc > 0) {
        if (i >= 8) {
            fprintf(stderr,"Only 8 logical drives may be specified\n");
            exit(3);
        } /* end if */
        p = *argv;
        if (strlen(*argv) == 2 && p[1] == ':') {
            if (strchr("0aA",*p))
                drives[i] = 040000; /* drive A */
            else if (strchr("1bB",*p))
                drives[i] = 040001; /* drive B */
            else {
                fprintf(stderr,"Only floppy drive A: or B: is valid\n");
                exit(4);
            }
            ++argv; --argc; p = *argv;
            if (*p == '/')
                fsizes[i++] = atoi(p + 1);
            else {
                fprintf(stderr,"Missing /## for floppy drive %c:\n",
                        (drives[i] & 1) + 'A');
                exit(5);
            } /* end if */
        }
        else {
            if ((drives[i] = open(*argv,OMODE)) < 0) {
                fprintf(stderr,"Cannot open disk file %s\n",*argv);
                exit(6);
            } /* end if */
            fnames[i] = *argv;  /* remember file name */
            (void)fstat(drives[i],&statbuf);    /* get the file's size */
            fsizes[i] = (int)((statbuf.st_size + 511L) / BUFSIZ);
            i += 1;
        } /* end if */
        ++argv; --argc;
    } /* end while */
    maxunit = i;                /* remember highest unit available */

#ifdef MSDOS
    j = 0;                      /* look for largest floppy disk size */
    for (i = 0; i < maxunit; i++) {
        if (drives[i] & 040000) {   /* floppy drives only */
            if (fsizes[i] > j)
                j = fsizes[i];  /* remember largest # of sectors */
        } /* end if */
    } /* end for */

    if (j) {                    /* anything using floppy disks? */
        farptr = (char far *)_dos_getvect(0x1E);    /* -> disk table */
        farptr[4] = j;          /* allow all sectors per track */
        /* get a track buffer. if it would wrap over ffff, */
        /* get another one and then free the first one. */
        trkbuf = farptr = _fmalloc(j * 512);    /* get a track of space */
        i = (int)((long)FP_SEG(farptr) * 16L) + (long)FP_OFF(farptr);
        if (i + (j * 512) < i) {    /* buffer wraps over ffff? */
            trkbuf = _fmalloc(j * 512); /* try a 2nd buffer */
            _ffree(farptr);     /* then free first buffer */
        } /* end if */
    } /* end if */
    ivideo(0);                  /* set video system */
    ltcflg = 0;
#endif

    scrout("LSI-11 Simulator V 4.7 - Copyright (c) 1993 R.W.Meister\r\n");
    sprintf(pbuf,"\r\nMemory available: %u bytes (0-%06o)\r\n",highpc,highpc-1);
    scrout(pbuf);
    sprintf(pbuf,"\r\nParallel port: %#x\r\n",lptport);
    scrout(pbuf);

    for (i = 0; i <= maxunit; i++) {
        if (drives[i] != 0 || fsizes[i] != 0) {
            if (drives[i] & 040000) {
                sprintf(pbuf,"Unit %d: floppy disk drive %c: = %u blocks\r\n",
                        i,(drives[i] & 1) + 'A',fsizes[i] * 2 * FTRACKS);
                scrout(pbuf);
            }
            else {
                sprintf(pbuf,"Unit %d: file '%s' = %u blocks\r\n",
                        i,fnames[i],fsizes[i]);
                scrout(pbuf);
            } /* end if */
        } /* end if */
    } /* end for */

    for (u = 5; u; --u)
        REG[u].uw = 0;          /* init machine registers */
    gotleadin = psw = PSW = PC.uw = 0;
    SP.uw = 02000;              /* setup a nice stack */
    reseti();                   /* reset hardware */
    begint = time(NULL); 
    ltccnt = 0;

    /* bootstrap reads block 0 */
    pf.cr = 0;                  /* read unit 0 */
    pf.bn = 0;                  /* block 0 */
    pf.ba = 0;                  /* into location 0 */
    pf.wc = 256;                /* one block */
    diskio();                   /* let 'er rip */
    if (pf.cr & ERRBIT)         /* error? */
        cmem[0] = cmem[1] = 0;  /* set first word to 0 */
    pf.cr |= READY;             /* make sure interface is ready */

    icount = IBTWNI;            /* instructions between checking for ints */
    rawtty(1);                  /* enable raw mode */

#ifdef MSDOS
    ltcflg = 0;                 /* enable LTC routines */
#if 1
    // INT70h is the software interrupt called by the RTC chip via INT08h. In
    // DOSBox, it appears that this call isn't supported. Will need to check
    // other virtualized environments like Parallels, VirtualBox, or PCEm to
    // see whether others reflect the INT08h to INT70h. PCEm works because it
    // uses real ROMs. RT-11 will likely not boot without a working LTC. Its
    // also possible that it may not boot because the floppy device isn't at 
    // the standard CSR and interrupt.
    int70a = _dos_getvect(0x70);    /* -> int70 vector */
    _dos_setvect(0x70,int_70);      /* this is the INT70 callback */
    dreg.h.ah = 0x83;               /* event clock */
    dreg.h.al = 0;                  /* set it up */
    dreg.x.cx = 0;
    dreg.x.dx = (unsigned) 1000;    /* just some time */
    dreg.x.bx = FP_OFF(&ltcflg);
    sreg.es = FP_SEG(&ltcflg);      /* dummy flag to use */
    (void)int86x(0x15,&dreg,&dreg,&sreg);   /* INT15h event clock */
    // returns CF on error, clear if OK, ah=86h if unsupported
    if (dreg.x.cflag != 0){
    //if ( dreg.h.ah >= 0x80 ){
        sprintf(pbuf,"\r\nEvent timer not supported, AH= %#x\r\n",dreg.h.ah);
        scrout(pbuf);
    }
#endif
#endif

fetch:
    if (sstep) {                /* single-stepping? */
        PSW = psw;
        if (odt(0))             /* call odt */
            goto getout;        /* wanted to exit */
        psw = PSW;
    } /* end if */

    if (wflag)                  /* processing in wait mode? */
        goto wcheck;            /* deal with interrupts only */

    /* get the next instruction and update the PC */
    instr = *(unsigned int *)&cmem[PC.uw & ~1]; PC.uw += 2;
#ifdef DEBUG
    printf("%06o: %06o\r\n",PC.uw-2,instr);
#endif
    switch (iarray[instr>>3]) { /* index directly to code */
    case 1:                     /* double-op words */
    case 2:                     /* double-op bytes */
        if ((vector = getea(instr >> 6)) != 0)
            goto trapper;       /* illegal src */
        srcadr = effadr;
        psw &= BMSK;            /* clear all cc bits EXCEPT CARRY */
        if ((instr & 0100000) && instr < 0160000) { /* byte instructions */
            i = *srcadr & 0377; /* get source byte */
            if ((vector = getea(instr)) != 0)
                goto trapper;   /* illegal dst */
#ifdef PROFILING
            icnts[0] += 1L;
#endif
            switch ((instr & 070000) >> 12) {
            case 01:            /* MOVB */
                if ((instr & 070) == 0) {   /* movb to a register? */
                    if (i & 0200)
                        i |= 0177400;   /* sign extend it */
                    intadr = (unsigned int *)effadr;
                    *intadr = (unsigned)i;  /* store the entire word */
                    goto setw;
                } /* end if */
                break;          /* just store the byte */
            case 02:            /* CMPB */
                j = *effadr & 0377;
                if (i & 0200)
                    i |= 0177400;
                if (j & 0200)   /* sign-extend both ops */
                    j |= 0177400;
                k = i - j;
                psw |= CBIT;
                if ((i >= 0 && j < 0 && k < 0) ||
                    (i < 0 && j >= 0 && k >= 0))
                    psw |= VBIT;
                if (((unsigned int)i >= (unsigned int)j))
                    psw &= ~CBIT;
                i = k;
                goto setb;      /* just set cc - nothing to store */
            case 03:            /* BITB */
                i = i & (*effadr & 0377);
                goto setb;
            case 04:            /* BICB */
                j = *effadr & 0377;
                i = j & (~i);
                break;
            case 05:            /* BISB */
                i = i | (*effadr & 0377);
                break;
            } /* end switch */
            *effadr = i;        /* store the result */
            goto setb;
        }
        else {                  /* word instructions */
            intadr = (unsigned int *)((unsigned int)srcadr & 0177776);
            i = *intadr;        /* get current contents of word */
            if ((vector = getea(instr)) != 0)
                goto trapper;   /* illegal dst */
            intadr = (unsigned int *)((unsigned int)effadr & 0177776);
            j = *intadr;
#ifdef PROFILING
            icnts[1] += 1L;
#endif
            switch ((instr >> 12) & 017) {
            case 01:            /* MOV */
                break;          /* just store the word */
            case 02:            /* CMP */
                k = i - j;      /* reverse order from sub */
                psw |= CBIT;
                if ((i >= 0 && j < 0 && k < 0) ||
                    (i < 0 && j >= 0 && k >= 0))
                    psw |= VBIT;
                if (((unsigned int)i >= (unsigned int)j))
                    psw &= ~CBIT;
                i = k;
                goto setw;      /* just set cc - nothing to store */
            case 03:            /* BIT */
                i = i & j;
                goto setw;      /* nothing to store */
            case 04:            /* BIC */
                i = j & (~i);
                break;
            case 05:            /* BIS */
                i = i | j;
                break;
            case 06:            /* ADD */
                k = i + j;
                psw &= ~CBIT;
                if ((i >= 0 && j >= 0 && k < 0) ||
                    (i < 0 && j < 0 && k >= 0))
                    psw |= VBIT;
                if (((long)(unsigned int)i + (long)(unsigned int)j) >= 65536L)
                    psw |= CBIT;
                i = k;
                break;
            case 016:           /* SUB */
                k = j - i;      /* reverse order from cmp */
                psw &= ~CBIT;
                if ((i >= 0 && j < 0 && k >= 0) ||
                    (i < 0 && j >= 0 && k < 0))
                    psw |= VBIT;
                if ((unsigned int)i > (unsigned int)j)
                    psw |= CBIT;
                i = k;
                break;
            default:
                vector = T10VEC;    /* illegal instruction */
                goto trapper;
            } /* end switch */
            *intadr = (unsigned)i;  /* store the result */
            goto setw;
        } /* end if */
    case 3:                     /* branches 0004xx..0037xx */
#ifdef PROFILING
            icnts[2] += 1L;
#endif
        u = 1 << ((instr >> 8) & 7);    /* get opcode bits as mask bit */
        goto dobranch;
    case 4:                     /* branches 1000xx..1037xx */
#ifdef PROFILING
            icnts[3] += 1L;
#endif
        u = 0400 << ((instr >> 8) & 7); /* get opcode bits as mask bit */
dobranch:
        if ((btable[psw & 017] & u) != 0)   /* if bit on, do branch */
            PC.uw += ((int)((char)(instr & 0377)) * 2);
        break;
    case 6:                     /* single-op words */
    case 5:                     /* single-op bytes */
        if ((vector = getea(instr)) != 0)
            goto trapper;
        psw &= BMSK;            /* clear all cc bits EXCEPT CARRY */
        if (instr & 0100000) {  /* byte instructions */
#ifdef PROFILING
            icnts[4] += 1L;
#endif
            i = *effadr & 0377; /* get current contents of byte */
            switch ((instr & 07700) >> 6) {
            case 050:           /* CLRB */
                i = 0;
                psw &= ~CBIT;
                break;
            case 051:           /* COMB */
                i = ~i;
                psw |= CBIT;
                break;
            case 052:           /* INCB */
                if (i == 0177)
                    psw |= VBIT;
                i += 1;
                break;
            case 053:           /* DECB */
                if (i == 0200)
                    psw |= VBIT;
                i -= 1;
                break;
            case 054:           /* NEGB */
                i = -i;
                if ((i & 0377) == 0200)
                    psw |= VBIT;
                psw &= ~CBIT;
                if (i & 0377)
                    psw |= CBIT;
                break;
            case 055:           /* ADCB */
                if (i == 0177 && (psw & CBIT))
                    psw |= VBIT;
                if (psw & CBIT)
                    i += 1;
                if ((i & 0377) == 0 && (psw & CBIT))
                    psw |= CBIT;
                else
                    psw &= ~CBIT;
                break;
            case 056:           /* SBCB */
                if (i == 0200)
                    psw |= VBIT;
                if (psw & CBIT)
                    i -= 1;
                if ((i & 0377) == 0377 && (psw & CBIT))
                    psw |= CBIT;
                else
                    psw &= ~CBIT;
                break;
            case 057:           /* TSTB */
                psw &= ~CBIT;
                goto setb;      /* nothing to do but test the result */
            case 060:           /* RORB */
                cbit = (i & 1);
                i = ((unsigned)i >> 1) & 0177;
                if (psw & CBIT)
                    i = i | 0200;
                goto rotb;
            case 061:           /* ROLB */
                cbit = (i & 0200);
                i = (i << 1) & 0376;
                if (psw & CBIT)
                    i = i | 1;
                goto rotb;
            case 062:           /* ASRB */
                cbit = (i & 1);
                nbit = (i & 0200);
                i = ((unsigned)i >> 1) & 0177;
                if (nbit)
                    i = i | 0200;
                goto rotb;
            case 063:           /* ASLB */
                cbit = (i & 0200);
                i = (i << 1) & 0376;
rotb:           if (((i & 0200) && !cbit) || ((i & 0200) == 0 && cbit))
                    psw |= VBIT;
                psw &= ~CBIT;
                if (cbit)
                    psw |= CBIT;
                break;
            default:
                vector = T10VEC;    /* illegal instruction */
                goto trapper;
            } /* end switch */
            *effadr = i;        /* store result in all cases */
setb:       i &= 0377;
            if (i & 0200)       /* negative bit in low byte */
                psw |= NBIT;
            else if (i == 0)
                psw |= ZBIT;
        }
        else {                  /* word mode instructions */
#ifdef PROFILING
            icnts[5] += 1L;
#endif
            intadr = (unsigned int *)((unsigned int)effadr & 0177776);
            i = *intadr;        /* get current contents of word */
            switch ((instr & 07700) >> 6) {
            case 003:           /* SWAB */
                sw[0].ii = i;
                sw[1].aa[0] = sw[0].aa[1];
                sw[1].aa[1] = sw[0].aa[0];
                i = sw[1].ii;
                *intadr = (unsigned)i;
                psw &= ~CBIT;
                goto setb;      /* set cc based on low byte */
            case 050:           /* CLR */
                i = 0;
                psw &= ~CBIT;
                break;
            case 051:           /* COM */
                i = ~i;
                psw |= CBIT;
                break;
            case 052:           /* INC */
                if (i == 077777)
                    psw |= VBIT;
                i += 1;
                break;
            case 053:           /* DEC */
                if ((unsigned)i == 0100000)
                    psw |= VBIT;
                i -= 1;
                break;
            case 054:           /* NEG */
                i = -i;
                if ((unsigned)i == 0100000)
                    psw |= VBIT;
                psw &= ~CBIT;
                if (i)
                    psw |= CBIT;
                break;
            case 055:           /* ADC */
                if (i == 077777 && (psw & CBIT))
                    psw |= VBIT;
                if (psw & CBIT)
                    i += 1;
                if (i == 0 && (psw & CBIT))
                    psw |= CBIT;
                else
                    psw &= ~CBIT;
                break;
            case 056:           /* SBC */
                if ((unsigned)i == 0100000)
                    psw |= VBIT;
                if (psw & CBIT)
                    i -= 1;
                if ((unsigned)i == 0177777 && (psw & CBIT))
                    psw |= CBIT;
                else
                    psw &= ~CBIT;
                break;
            case 057:           /* TST */
                psw &= ~CBIT;
                goto setw;      /* nothing to do but test the result */
            case 060:           /* ROR */
                cbit = (i & 1);
                i = ((unsigned)i >> 1) & 077777;
                if (psw & CBIT)
                    i = i | 0100000;
                goto rotw;
            case 061:           /* ROL */
                cbit = (i & 0100000);
                i = (i << 1) & 0177776;
                if (psw & CBIT)
                    i = i | 1;
                goto rotw;
            case 062:           /* ASR */
                cbit = (i & 1);
                nbit = (i & 0100000);
                i = ((unsigned)i >> 1) & 077777;
                if (nbit)
                    i = i | 0100000;
                goto rotw;
            case 063:           /* ASL */
                cbit = (i & 0100000);
                i = (i << 1) & 0177776;
rotw:           if (((i & 0100000) && !cbit) || ((i & 0100000) == 0 && cbit))
                    psw |= VBIT;
                psw &= ~CBIT;
                if (cbit)
                    psw |= CBIT;
                break;
            default:
                vector = T10VEC;    /* illegal instruction */
                goto trapper;
            } /* end switch */
stow:       *intadr = (unsigned)i;  /* store result in all cases */
setw:       if (i < 0)
                psw |= NBIT;
            else if (i == 0)
                psw |= ZBIT;
        } /* end if */
        break;
    case 7:                     /* jsr */
        if ((instr & 070) == 0) {
            vector = T4VEC;     /* jsr to register */
            goto trapper;
        } /* end if */
        if ((vector = getea(instr)) != 0)
            goto trapper;
#ifdef PROFILING
        icnts[6] += 1L;
#endif
        u = (instr >> 6) & 7;   /* get register number and push it */
        *(unsigned int *)&cmem[(unsigned int)--SP.up] = REG[u].uw;
        REG[u].uw = PC.uw;      /* swap registers */
#ifdef DEBUG
        printf("jsr: ea %06o cm %06o\r\n",effadr,cmem);
#endif
        PC.uw = (unsigned int)(effadr - cmem);  /* new pc */
        break;
    case 8:                     /* rts */
#ifdef PROFILING
        icnts[7] += 1L;
#endif
        u = instr & 7;
        PC.uw = REG[u].uw;      /* set pc and restore reg */
        REG[u].uw = *(unsigned int *)&cmem[(unsigned int)SP.up++];
        break;
    case 9:                     /* jmp */
        if ((instr & 070) == 0) {
            vector = T4VEC;     /* jmp to a register */
            goto trapper;
        } /* end if */
        if ((vector = getea(instr)) != 0)
            goto trapper;
#ifdef DEBUG
        printf("jmp: ea %06o cm %06o\r\n",effadr,cmem);
#endif
#ifdef PROFILING
        icnts[8] += 1L;
#endif
        PC.uw = (unsigned int)(effadr - cmem);  /* new pc */
        break;
    case 10:                    /* condition codes */
#ifdef PROFILING
        icnts[9] += 1L;
#endif
        u = instr & 017;
        if (instr & 020)        /* set them */
            psw |= u;
        else                    /* clear them */
            psw &= ~u;
        break;
    case 11:                    /* xor */
        if ((vector = getea(instr)) != 0)
            goto trapper;
#ifdef PROFILING
        icnts[10] += 1L;
#endif
        psw &= BMSK;            /* clear all cc bits EXCEPT CARRY */
        u = (instr >> 6) & 7;   /* get register number */
        intadr = (unsigned int *)effadr;
        i = *intadr ^ REG[u].uw;    /* do the xor */
        goto stow;              /* store result and set cc */
    case 12:                    /* sob */
#ifdef PROFILING
        icnts[11] += 1L;
#endif
        u = (instr >> 6) & 7;   /* get register number */
        if (--REG[u].uw)        /* subtract one, and... */
            PC.uw -= ((instr & 077) * 2);   /* branch if not zero */
        break;
    case 13:                    /* sxt */
        if ((vector = getea(instr)) != 0)
            goto trapper;
#ifdef PROFILING
        icnts[12] += 1L;
#endif
        intadr = (unsigned int *)effadr;
        i = 0;
        psw &= ~(VBIT | ZBIT);
        if (psw & NBIT)
            i = -1;
        goto stow;
    case 14:                    /* emt & trap */
#ifdef PROFILING
        icnts[13] += 1L;
#endif
        vector = EMTVEC;        /* assume EMT */
#ifdef DEBUG
        printf("emt %03o\r\n",instr & 0377);
#endif
        if (instr & 0400)
            vector = TRPVEC;    /* make it TRAP */
        goto trapper;
    case 15:                    /* mtps, mfps */
        if ((vector = getea(instr)) != 0)
            goto trapper;
#ifdef PROFILING
        icnts[14] += 1L;
#endif
        if (instr < 0106500) {  /* MTPS */
            psw = (*effadr & 0377) & ~TBIT; /* set all bits except T */
        }
        else {                  /* MFPS */
            i = psw & 0377;
            psw &= BMSK;        /* clear all cc bits EXCEPT CARRY */
            if ((instr & 070) == 0) {   /* moving to a register? */
                if (i & 0200)
                    i |= 0177400;   /* sign extend it */
                intadr = (unsigned int *)effadr;
                goto stow;      /* and store it */
            }
            else {
                *effadr = i;    /* store result */
                goto setb;      /* and set N & Z bits */
            } /* end if */
        } /* end if */
        break;
    case 16:                    /* mark */
#ifdef PROFILING
        icnts[15] += 1L;
#endif
        SP.uw = PC.uw + ((instr & 077) * 2);
        PC.uw = REG[5].uw;
        REG[5].uw = *(unsigned int *)&cmem[(unsigned int)SP.up++];
        break;
    case 17:                    /* EIS */
#ifdef PROFILING
        icnts[16] += 1L;
#endif
        if ((vector = getea(instr)) != 0)
            goto trapper;
        u = (instr >> 6) & 7;   /* get register number */
        psw &= ~017;            /* clear all cc bits */
        switch ((instr & 07000) >> 9) {
        case 0:                 /* MUL */
            lw.wd[LWD] = REG[u].uw; /* sign extend high word */
            lw.wd[HWD] = ((lw.wd[LWD] & 0100000) ? 0177777 : 0);
            intadr = (unsigned int *)((unsigned int)effadr & 0177776);
            i = *intadr;        /* get current contents of word */
            lw.wds = lw.wds * (long)i;
            if (lw.wds < 0L)
                psw |= NBIT;
            else if (lw.wds == 0L)
                psw |= ZBIT;
            if (lw.wds < -32768L || lw.wds > 32767L)
                psw |= CBIT;    /* < -(2^15) or > (2^15)-1 */
            REG[u].uw = lw.wd[HWD];
            REG[u | 1].uw = lw.wd[LWD];
            break;
        case 1:                 /* DIV */
            u &= 6;             /* must be even register number */
            lw.wd[HWD] = REG[u].uw;
            lw.wd[LWD] = REG[u | 1].uw;
            intadr = (unsigned int *)((unsigned int)effadr & 0177776);
            i = *intadr;        /* get current contents of word */
            if (i == 0)         /* dividing by 0 not allowed */
                psw |= (CBIT | VBIT);
            else {              /* "Thee May Proceed" (T'Pau) */
                j = (int)(lw.wds / (long)i);    /* quotient */
                k = (int)(lw.wds % (long)i);    /* remainder */
                if (j < 0)
                    psw |= NBIT;
                else if (j == 0)
                    psw |= ZBIT;
                if ((lw.wds / (long)i) >= 65536L)
                    psw |= VBIT;
                REG[u].uw = j;  /* store quotient */
                REG[u | 1].uw = k;  /* store remainder */
            } /* end if */
            break;
        case 2:                 /* ASH */
            cbit = nbit = 0;
            j = REG[u].uw;
            intadr = (unsigned int *)((unsigned int)effadr & 0177776);
            i = *intadr;        /* get shift amount */
            k = i & 037;        /* get actual value */
            if (i & 040) {      /* negative value means right shift */
                while (k++ < 040) {
                    cbit = j & 1;   /* remember bit shifted out */
                    j >>= 1;    /* sign can NEVER change here */
                } /* end while */
            }
            else {
                while (k--) {
                    cbit = j & 0100000; /* remember bit shifted out */
                    j <<= 1;
                    if ((j >= 0 && (REG[u].uw & 0100000)) ||
                       (j < 0 && !(REG[u].uw & 0100000)))
                        nbit = 1;   /* changed sign */
                } /* end while */
            } /* end if */
            if (j < 0)
                psw |= NBIT;
            else if (j == 0)
                psw |= ZBIT;
            psw |= (nbit ? VBIT : 0);
            psw |= (cbit ? CBIT : 0);
            REG[u].uw = j;      /* store result */
            break;
        case 3:                 /* ASHC */
            cbit = nbit = 0;
            lw.wd[HWD] = REG[u].uw;
            lw.wd[LWD] = REG[u | 1].uw;
            intadr = (unsigned int *)((unsigned int)effadr & 0177776);
            i = *intadr;        /* get shift amount */
            k = i & 037;        /* get actual value */
            if (i & 040) {      /* negative value means right shift */
                while (k++ < 040) {
                    cbit = lw.wd[LWD] & 1;  /* remember C-bit */
                    lw.wds >>= 1;   /* sign can NEVER change here */
                } /* end while */
            }
            else {
                while (k--) {
                    cbit = lw.wd[HWD] & 0100000;    /* remember C-bit */
                    lw.wds <<= 1;
                    if ((!(lw.wd[HWD] & 0100000) && (REG[u].uw & 0100000)) ||
                        ((lw.wd[HWD] & 0100000) && !(REG[u].uw & 0100000)))
                        nbit = 1;   /* changed sign */
                } /* end while */
            } /* end if */
            if (lw.wds < 0)
                psw |= NBIT;
            else if (lw.wds == 0)
                psw |= ZBIT;
            psw |= (nbit ? VBIT : 0);
            psw |= (cbit ? CBIT : 0);
            REG[u].uw = lw.wd[HWD]; /* store result */
            REG[u | 1].uw = lw.wd[LWD];
            break;
        } /* end switch */
        break;
    case 18:                    /* halt, wait, rti, bpt, iot, reset, rtt */
#ifdef PROFILING
        icnts[17] += 1L;
#endif
        switch (instr) {
        case 0:                 /* HALT */
            if (ccsr[XDBR]) {   /* any output pending? */
                write(1,&ccsr[XDBR],1); /* ship it */
                ccsr[XDBR] = 0;
            } /* end if */
            PSW = psw;
            if (odt(1)) {       /* want to quit? */
getout:
                rawtty(0);      /* turn off raw mode */
                for (i = 0; i <= maxunit; i++) {
                    if (drives[i] && !(drives[i] & 040000))
                        close(drives[i]);
                } /* end for */
                free(cmem);     /* clean up */
#ifdef MSDOS
                dreg.h.ah = 0x83;   /* event clock */
                dreg.h.al = 1;  /* terminate it */
                dreg.x.bx = FP_OFF(&ltcflg);
                sreg.es = FP_SEG(&ltcflg);
                (void)int86x(0x15,&dreg,&dreg,&sreg);
                _dos_setvect(0x70,int70a);  /* reset vector */
//***RAC
//              farfree(iarray);    /* free instruction array */
                _ffree(iarray);
                _ffree(trkbuf); /* free first buffer */
                ivideo(1);      /* reset video system */
#else
                free(iarray);   /* free instruction array */
#endif
#ifdef PROFILING
                dumpcnts();
#endif
                exit(0);        /* good bye, so long, farewell... */
            } /* end if */
            break;              /* continue with next instruction */
        case 1:                 /* WAIT */
#ifdef DEBUG
            printf("setting wait flag @ %06o\r\n",PC.uw);
#endif
            wflag = 1;
            break;
        case 2:                 /* RTI */
            PC.uw = *(unsigned int *)&cmem[(unsigned int)SP.up++];
            psw = *(unsigned int *)&cmem[(unsigned int)SP.up++];
            if (psw & TBIT)
                trcflg = 1;     /* trap after current instruction */
            break;
        case 3:                 /* BPT */
            vector = BPTVEC;
            goto trapper;
        case 4:                 /* IOT */
            vector = IOTVEC;
            goto trapper;
        case 5:                 /* RESET */
            reseti();
            break;
        case 6:                 /* RTT */
            PC.uw = *(unsigned int *)&cmem[(unsigned int)SP.up++];
            psw = *(unsigned int *)&cmem[(unsigned int)SP.up++];
            if (psw & TBIT)
                trcflg = 2;     /* trap after next instruction */
            break;
        case 7:
            vector = T10VEC;    /* illegal/reserved instruction */
            goto trapper;
        } /* end switch */
        break;
    case 0:                     /* illegal/reserved instructions */
        vector = T10VEC;        /* illegal/reserved instruction */
        goto trapper;
    } /* end switch */

wcheck:                         /* come here if doing WAIT instruction */
#ifdef MSDOS
    if (ltccnt > 0 && (ltccsr[0] & IENABL) && (psw & IBIT) == 0) {
        ltccnt -= 1;            /* count this tick */
        vector = LTCVEC;        /* and do the interrupt */
        goto trapper;
    } /* end if */
#endif

    /* check for console tty or floppy disk interrupts */
    if (--icount <= 0) {        /* time for checking interrupts? */
        icount = IBTWNI;        /* reset counter */
#ifndef MSDOS
        ioctl(0,TIOCQCNT,&ttyb);
        if (ttyb.sg_ispeed) {   /* character(s) waiting? */
            read(0,&ccsr[RDBR],1);  /* get the character */
#else
        if (gotleadin) {        /* need to send second char of sequence? */
            ccsr[RDBR] = gotleadin; /* send it now */
            gotleadin = 0;      /* we used it */
            goto havechar;
        } /* end if */
        if (_bios_keybrd(_KEYBRD_READY) != 0) {
            i = _bios_keybrd(_KEYBRD_READ);
            if (i == 0x0E08)    /* convert backspace */
                i = 0177;       /* to rubout */
            i = h_in(i);        /* convert to hazeltine */
            gotleadin = 0;
            ccsr[RDBR] = i & 0177;
            if (i & 0200) {     /* lead-in required? */
                ccsr[RDBR] = LEADIN;    /* send it now */
                gotleadin = i & 0177;
            } /* end if */
#endif
havechar:
            if (ccsr[RDBR] == 0) {
                PSW = psw;
                if (odt(3))     /* pseudo-break hit */
                    goto getout;
                psw = PSW;
            }
            else {
                ccsr[RCSR] |= READY;    /* set ready bit */
                intctl |= I_CONI;   /* interrupt shortly */
            } /* end if */
        }
        else {
            ccsr[RCSR] &= ~READY;   /* not ready any more */
        } /* end if */

        if (intctl & I_CONI) {  /* transfer complete? */
            if ((ccsr[RCSR] & IENABL) && ((psw & IBIT) == 0)) {
                intctl &= ~I_CONI;
                vector = KBDVEC;    /* process interrupt */
                goto trapper;
            } /* end if */
        } /* end if */

        if (intctl & I_CONO) {  /* transfer complete? */
            ccsr[XCSR] |= READY;    /* device ready now */
            if ((ccsr[XCSR] & IENABL) && ((psw & IBIT) == 0)) {
                intctl &= ~I_CONO;
                vector = TTYVEC;    /* process interrupt */
                goto trapper;
            } /* end if */
        } /* end if */

        if (intctl & I_FLOP) {  /* transfer complete? */
            if ((pf.cr & IENABL) && ((psw & IBIT) == 0)) {
                intctl &= ~I_FLOP;
                vector = PFVEC; /* process interrupt */
                goto trapper;
            } /* end if */
        } /* end if */

#ifdef MSDOS
        if (intctl & I_LPT) {   /* transfer complete? */
            if ((lptcsr[0] & IENABL) && ((psw & IBIT) == 0)) {
//***RAC
//              if ((inportb(lptport+1) & 0x90) == 0x90) {
                if ((inp(lptport+1) & 0x90) == 0x90){
                    lptcsr[0] |= READY;
                    intctl &= ~I_LPT;
                    vector = LPTVEC;    /* process interrupt */
                    goto trapper;
                } /* end if */
            } /* end if */
        } /* end if */
#endif
    } /* end if */

    /* deal with pending output now */
    if (ccsr[XDBR]) {           /* xmit data reg needs outputting? */
#ifdef MSDOS
        h_out(ccsr[XDBR]);      /* look like a hazeltine */
#else
        write(1,&ccsr[XDBR],1); /* ship the byte */
#endif
        ccsr[XDBR] = 0;         /* we used the byte */
        ccsr[XCSR] &= ~READY;   /* not ready yet */
        intctl |= I_CONO;       /* interrupt next time around */
    } /* end if */
    if (ccsr[XCSR] & IENABL)
        intctl |= I_CONO;       /* re-enable interrupts */

#ifdef MSDOS
    if ((effadr == &lptcsr[2]) && lptcsr[2]) {  /* lpt data buffer w/data? */
//***RAC - changed all INP and OUTP
        outp(lptport,lptcsr[2]);    /* output byte */
        i = inp(lptport+2); /* get bit configuration */
        outp(lptport+2,i^1);    /* toggle strobe bit */
        outp(lptport+2,i);  /* and reset it */
        i = inp(lptport+1); /* get status byte */
        lptcsr[1] = lptcsr[2] = 0;  /* we used the byte */
        lptcsr[0] &= ~READY;    /* not ready yet */
        if ((i & 0x20) > 0 || (i & 0x8) == 0)   /* i/o error or out of paper? */
            lptcsr[1] = 0200;   /* error condition */
        else
            lptcsr[0] |= (((i & 0x90) == 0x90) ? READY : 0);
    }                           /* check lpt control register */
    else if (effadr == &lptcsr[0] || (lptcsr[0] & IENABL)) {
        i = inp(lptport+1); /* get status byte */
        if ((i & 0x20) > 0 || (i & 0x8) == 0)   /* i/o error or out of paper? */
            lptcsr[1] = 0200;   /* error condition */
        else
            lptcsr[0] |= (((i & 0x90) == 0x90) ? READY : 0);
        if ((lptcsr[0] & (IENABL | READY)) == (IENABL | READY))
            intctl |= I_LPT;    /* interrupt next time around */
    } /* end if */
#endif

    if (pf.cr & GO) {           /* want diskio done? */
        diskio();               /* do it */
        intctl |= I_FLOP;       /* interrupt next time around */
    } /* end if */

    if (trcflg > 0 && --trcflg <= 0) {  /* done enough instructions to trap? */
        trcflg = -1;            /* all done */
        if (psw & TBIT) {       /* t-bit set? */
            vector = 014;       /* do the trap now */
            goto trapper;
        } /* end if */
    } /* end if */

    goto fetch;                 /* get the next instruction */

    /* handle hardware interrupts and traps */
trapper:
#ifdef DEBUG
    printf("trap to %o near %06o, SP=%06o\r\n",vector,PC.uw,SP.uw);
#endif
    if (SP.uw > highpc) {
        PSW = psw;
        if (odt(2))             /* stack invalid */
            goto getout;
        psw = PSW;
    } /* end if */

    *(unsigned int *)&cmem[(unsigned int)--SP.up] = psw;    /* push PSW */
    *(unsigned int *)&cmem[(unsigned int)--SP.up] = PC.uw;  /* push PC */
    PC.uw = *(unsigned int *)&cmem[vector];  /* get new pc & psw */
    psw = *(unsigned int *)&cmem[vector + 2];
    wflag = 0;                  /* not waiting any more */
    goto fetch;
} /* end main() */

#ifdef PROFILING
#ifdef MSDOS
void
#endif
dumpcnts()
{
    register int i;
    register int j;
    long total, endtime;
    FILE * fx;

    endtime = time(NULL);
    fx = fopen("lsi11.cnt","w"); total = 0L;
    for (i = 0; i <= 17; i++) {
        fprintf(fx,"Group %02d: %08ld\n",i,icnts[i]);
        total += icnts[i];
    } /* end for */
    fprintf(fx,"%ld instructions in %ld seconds\n",total,endtime-begint);
    fprintf(fx,"\nRegister:      0        1        2        3        4        5        6        7\n");
    for (i = 0; i <= 7; i++) {
        fprintf(fx,"Mode %d:",i);
        for (j = 0; j <= 7; j++)
            fprintf(fx," %8ld",amodes[i][j]);
        fprintf(fx,"\n");
    } /* end for */
    fclose(fx);
} /* end dumpcnts() */
#endif

#ifdef MSDOS
void
#endif
reseti()                        /* reset interrupts etc */
{
    int i;

    ltccsr[0] = ltccsr[1] = ccsr[RCSR] = ccsr[RDBR] = ccsr[XDBR] = 0;
    ccsr[XCSR] = READY;         /* terminal always ready */
    lptcsr[0] = lptcsr[1] = 0;
#ifdef MSDOS
    i = _bios_printer(_PRINTER_STATUS,0,0);
    if (i & 0x28)               /* i/o error or out of paper? */
        lptcsr[1] = 0200;       /* error condition */
    else
        lptcsr[0] |= (((i & 0x90) == 0x90) ? READY : 0);
#endif
    pf.cr &= ~IENABL;           /* disk disabled */
    pf.cr |= READY;             /* and ready for work */
    intctl = trcflg = 0;        /* no interrupts or trace trap */
} /* end reseti() */

#ifdef MSDOS
void
#endif
rawtty(m)                       /* set/reset terminal raw mode */
int m;                          /* 1 = set raw, 0 = reset */
{
    if (m) {                    /* turn on raw mode */
#ifndef MSDOS
        ioctl(0,TIOCGETP,&ttyb);    /* get current keyboard status */
        oflag = ttyb.sg_flags;  /* save current status */
        ttyb.sg_flags &= ~(CRMOD | ECHO | XTABS);
        ttyb.sg_flags |= RAW;   /* set single char immediate */
        ioctl(0,TIOCSETP,&ttyb);
#else
        dreg.h.ah = 0x44;       /* ioctl */
        dreg.h.al = 0;          /* get status */
        dreg.x.bx = fileno(stdin);
        (void)intdos(&dreg,&dreg);
        if (dreg.x.cflag == 0) {
            oflag = dreg.x.dx & 0xDF;   /* save old status */
            dreg.x.dx = oflag | 0x20;   /* set raw mode */
            dreg.h.ah = 0x44;
            dreg.h.al = 1;      /* set status */
            dreg.x.bx = fileno(stdin);
            (void)intdos(&dreg,&dreg);
        } /* end if */
        dreg.h.ah = 0x33;
        dreg.h.al = 0;          /* get break status */
        (void)intdos(&dreg,&dreg);
        obreak = dreg.x.dx;     /* save it */
        dreg.x.dx = 0;          /* disable ^C */
        dreg.h.ah = 0x33;
        dreg.h.al = 1;          /* set break status */
        (void)intdos(&dreg,&dreg);
#endif
    }
    else {                      /* turn off raw mode */
#ifndef MSDOS
        ioctl(0,TIOCGETP,&ttyb);    /* get current keyboard status */
        ttyb.sg_flags = oflag;  /* reset terminal */
        ioctl(0,TIOCSETP,&ttyb);
#else
        dreg.h.ah = 0x44;
        dreg.h.al = 1;          /* set status */
        dreg.x.bx = fileno(stdin);
        dreg.x.dx = oflag & 0xDF;   /* make sure raw bit is off */
        (void)intdos(&dreg,&dreg);
        dreg.h.ah = 0x33;
        dreg.h.al = 1;          /* set break status */
        dreg.x.dx = obreak;     /* reset ^C */
        (void)intdos(&dreg,&dreg);
#endif
    } /* end if */
} /* end rawtty() */

char * odtmsg[] = {             /* tells how we got into odt */
    "S-Step",
    "HALT I",
    "Bad SP",
    "CTRL-@"
} ;

int                             /* return 0 to continue, >0 to quit */
odt(x)                          /* do console odt stuff */
int x;                          /* how we got here */
{
    unsigned int addr;          /* address */
    unsigned int value;         /* numeric value */
    unsigned int * ip;          /* int ptr */
    char * cp;
    char regmode;               /* 1 for register mode */
    char opened;                /* 1 for location opened */
    char havdig;                /* 1 for digit entered */
    char c;                     /* character input */
    char pbuf[32];

    /* dump pc, say why we're here */
    sprintf(pbuf,"\r\n%06o %s",PC.uw,odtmsg[x]); scrout(pbuf);
    value = addr = 0;

prompt:
    scrout("\r\n@@");           /* prompt */
    value = 0;
    havdig = regmode = opened = 0;
    ip = (unsigned int *)-1;
loop:
    c = gchar();                /* get and echo character */
    switch (c) {
    case '\n':                  /* <lf> */
        if (opened && ip != (unsigned int *)-1 && havdig)
            *ip = value;        /* store value */
        addr += 2;
        if (regmode) {
            cp = (char *)addr;
            if (cp > (char *)&REG[7].uw)
                cp = (char *)&REG[0].uw;  /* wrap around */
            value = (unsigned int)(cp - (char *)&REG[0].uw) / 2;
            sprintf(pbuf,"\r  R%o ",value); scrout(pbuf);
            addr = (unsigned int)cp;
        }
        else {
dothis:
            sprintf(pbuf,"\r  %06o ",addr); scrout(pbuf);
        } /* end if */
        goto nexta;
    case '\r':                  /* <cr> */
        if (opened && ip != (unsigned int *)-1 && havdig)
            *ip = value;        /* store value */
        goto prompt;
    case '@':                   /* indirect */
        addr = *ip & ~1;        /* make sure its even */
        havdig = regmode = 0;
        scrout("\r\n");
        goto dothis;
    case '_':                   /* indexed by pc */
        if (regmode || !opened)
            goto errp;          /* can't do this */
        addr = (*ip & ~1) + addr + 2;
        havdig = regmode = 0;
        scrout("\r\n");
        goto dothis;
    case 'H':                   /* <h>alt mode */
        sstep = ~sstep;         /* flip it */
        sprintf(pbuf," now %s",sstep ? "halted" : "running"); scrout(pbuf);
        goto prompt;
    case 'G':                   /* <g>o */
        reseti();               /* reset hardware */
        PSW = 0;
        PC.uw = value;          /* starting address; fall thru */
    case 'P':                   /* <p>roceed */
        return (0);             /* do next instruction */
        /* NOTREACHED */
    case 'Q':                   /* <q>uit */
    case 'X':                   /* e<x>it */
        scrout("\r\n");
        return (1);             /* want to exit */
        /* NOTREACHED */
    case 'R':                   /* <r>egister */
        regmode = 1;
        c = gchar();
        if (c == 'S') {
            value = (unsigned int)&PSW;
            havdig = 1;
        }
        else if (isdigit(c)) {
            if (c > '7')
                goto errp;
            value = (unsigned int)&REG[c & 7].uw;
            havdig = 1;
        }
        else
            goto errp;
        break;
    case '0':
    case '1':
    case '2':
    case '3':                   /* octal digits */
    case '4':
    case '5':
    case '6':
    case '7':
        if (isdigit(c)) {       /* build numeric value */
            value = (value * 8) + (c & 7);
            havdig = 1;
        }
        else
            goto errp;
        break;
    case '/':                   /* examine */
        if (!havdig)
            goto errp;
        addr = value;
nexta:
        if (regmode)
            ip = (unsigned int *)addr;  /* -> register */
        else {
            addr &= ~1;         /* make sure its even */
            if (addr > highpc)
                goto errp;
            ip = (unsigned int *)&cmem[addr];   /* get memory contents */
        } /* end if */
        sprintf(pbuf," %06o ",*ip); scrout(pbuf);
        opened = 1;
        value = 0;
        havdig = 0;
        break;
    default:
errp:
        S_OUT('?');
        goto prompt;
    } /* end switch */
    goto loop;
} /* end odt() */

#ifdef MSDOS
void
#endif
scrout(p)                       /* output string to screen */
register char * p;              /* -> string */
{
    register char c;

    while ((c = *p++) != '\0')  /* loop on string */
        S_OUT(c);               /* output character */
} /* end scrout() */

char
gchar()                         /* get char from console */
{
    char c;                     /* character storage */
#ifndef MSDOS
    read(0,&c,1);               /* get the character */
#else
    dreg.h.ah = 0x07;           /* direct stdin input */
    (void)intdos(&dreg,&dreg);
    c = dreg.h.al;              /* get the character */
#endif
    if (islower(c))             /* make upper-case alpha */
        c = toupper(c);
    S_OUT(c);                   /* echo it */
    return (c);                 /* and return it */
} /* end gchar() */

int                             /* returns vector (4) or (0) */
getea(i)                        /* get effective address */
unsigned int i;                 /* addressing mode & register */
{
    int r, mode;                /* register number and mode */
    int incr;                   /* auto incr/decr amount */
    unsigned int ofs;           /* offset into arena */
    unsigned int * iadr;        /* for indirection */
    register unsigned int * p;  /* points to register in use */

    r = i & 7;                  /* get reg # */
    mode = (i >> 3) & 7;        /* and mode */
#ifdef PROFILING
    amodes[mode][r] += 1L;
#endif

    /* SP, PC, indirect mode, or word instruction? */
    incr = 1;                   /* assume byte increment */
    if (r >= 6 || (mode & 1) || (instr & 0100000) == 0 ||
       (instr & 0170000) == 0160000)
        incr = 2;               /* make it word increment */

    p = &REG[r].uw;             /* -> register */
    switch (mode) {             /* what to do? */
    case 0:                     /* register direct */
        effadr = (char *)p;
        return (0);             /* can never fail */
    case 1:                     /* register indirect */
        ofs = *p;
        break;
    case 2:                     /* auto incr */
    case 3:                     /* auto incr indirect */
        ofs = *p;
        *p += incr;             /* post-incr */
        break;
    case 4:                     /* auto decr */
    case 5:                     /* auto decr indirect */
        *p -= incr;             /* pre-decr */
        ofs = *p;
        break;
    case 6:                     /* indexed */
    case 7:                     /* indexed indirect */
        ofs = *(unsigned int *)&cmem[(unsigned int)PC.up++];
        ofs += *p;              /* incase indexed off pc */
        break;
    } /* end switch */

    if (mode == 1 && ofs > highpc)  /* past end of memory? */
        goto chkio;

    effadr = &cmem[ofs];        /* -> word/byte we want */

    if (mode > 2 && (mode & 1)) {   /* indirect modes? */
        iadr = (unsigned int *)effadr;  /* address of extra word */
        effadr = &cmem[*iadr];  /* -> where it says */
    } /* end if */

    if ((ofs = (unsigned int)(effadr - cmem)) > highpc) {
chkio:                          /* check for I/O addresses */
        if (ofs >= 0177560 && ofs <= 0177567) {
            effadr = &ccsr[ofs & 7];
            if (icount > PENDIO)
                icount = PENDIO;
            return (0);         /* console tty */
        }
        else if (ofs >= 0177530 && ofs <= 0177537) {
            effadr = (char *)&pf.cr + (ofs & 7);
            if (icount > PENDIO)
                icount = PENDIO;
            return (0);         /* pc floppy or file */
        }
#ifdef MSDOS
        else if (ofs >= 0177514 && ofs <= 0177517) {
            effadr = &lptcsr[ofs & 3];
            if (icount > PENDIO)
                icount = PENDIO;
            return (0);         /* line printer */
        }
        else if (ofs >= 0177546 && ofs <= 0177547) {
            effadr = &ltccsr[ofs & 1];
            return (0);         /* line time clock */
        }
#endif
        else {
#ifdef DEBUG
            printf("instr %06o iadr %06o ofs %06o ea %06o\r\n",
                instr,iadr,ofs,effadr);
#endif
            return (T4VEC);     /* invalid memory */
        } /* end if */
    } /* end if */
    return (0);                 /* all is ok */
} /* end getea() */

#ifdef MSDOS
void
#endif
diskio()
{
    int unit;                   /* logical unit number */

    unit = (pf.cr >> 8) & 7;    /* get logical unit number */
    pf.cr &= ~(GO | READY | ERRBIT);    /* not ready yet */
    pf.ba &= ~1;                /* make sure an even address */
    if (unit >= maxunit) {      /* working with a non-existant drive? */
        pf.cr |= ERRBIT;        /* yes, no file open */
        goto spfdone;
    } /* end if */
    if (pf.cr & GETSIZE) {      /* special function for getting file's size */
        pf.wc = fsizes[unit];   /* get # blocks */
        if (drives[unit] & 040000)  /* floppy disk just has # sectors */
            pf.wc *= (2 * FTRACKS); /* convert to # of blocks */
        goto spfdone;
    } /* end if */

#ifdef DEBUG
    printf("%06o xfer %d words at block %d into %06o\r\n",
        pf.cr,pf.wc,pf.bn,pf.ba);
#endif
#ifdef MSDOS
    if (drives[unit] & 040000)
        flopio(unit);           /* floppy disk */
    else
#endif
        fileio(unit);           /* actual file */
spfdone:
    pf.cr |= READY;             /* ready now */
} /* end diskio() */

#ifdef MSDOS
void
#endif
fileio(unit)                    /* do file-oriented I/O */
int unit;                       /* logical unit to use */
{
    long offset;                /* byte offset into file */
    int rc;                     /* return code from r/w */
    int fd;                     /* file descriptor number */

    fd = drives[unit];          /* get file descriptor */
    if (pf.bn > (unsigned int) fsizes[unit])
        goto pasteof;
    offset = (long)BUFSIZ * (long)pf.bn;
    lseek(fd,offset,0);         /* position to correct block */
    if (pf.cr & RW) {           /* read or write? */
        rc = write(fd,cmem + pf.ba,pf.wc * 2);
        close(dup(fd));         /* flush data to file */
    }
    else
        rc = read(fd,cmem + pf.ba,pf.wc * 2);
    if (rc == -1 || rc != (pf.wc * 2))
pasteof:
        pf.cr |= ERRBIT;        /* error */
} /* end fileio() */

#ifdef MSDOS
void
flopio(unit)                    /* read/write diskette sectors */
int unit;                       /* logical unit to use */
{
    int rc;                     /* return code */
    int retries;                /* # retries till error */
    int mywc;                   /* word count for this track */
    int spc, spt;               /* sectors per cylinder, sectors per track */
    struct diskinfo_t dd;       /* int13 structure */

    spt = fsizes[unit];         /* sectors per track */
    spc = 2 * spt;              /* sectors per cylinder */
    if ((pf.cr & RW) && ((pf.wc % 256) > 0))
        pf.wc += (256 - (pf.wc % 256)); /* round up write's word count */

domore:
    retries = 5;
rwagain:
    dd.buffer = trkbuf;         /* use far buffer always */
    dd.drive = drives[unit] & 7;    /* drive */
    dd.track = pf.bn / spc;     /* track */
    dd.head = 0;                /* assume head 0 */
    if ((dd.sector = (pf.bn % spc) + 1) > spt) {
        dd.head = 1;            /* other side */
        dd.sector -= spt;       /* normalize sector */
    } /* end if */
    if (pf.wc < 256) {          /* short request? */
        dd.nsectors = 1;        /* make sure we get at least one */
        mywc = pf.wc;           /* count number of words to copy */
    }
    else {                      /* complete blocks */
        dd.nsectors = (spt + 1) - dd.sector;    /* max is 1 full track */
        rc = pf.wc / 256;       /* # blocks requested */
        if (rc < dd.nsectors)   /* less than one track left in request? */
            dd.nsectors = rc;   /* then read just that much */
        mywc = 256 * dd.nsectors;   /* # of words to copy */
    } /* end if */

    if (pf.cr & RW)             /* writing? copy user data to buffer */
//***RAC
//      fmemcpy(trkbuf,(char far *)(cmem + pf.ba),mywc);
        _fmemcpy(trkbuf,(char far *)(cmem + pf.ba),mywc);

    rc = _bios_disk((pf.cr & RW) ? _DISK_WRITE : _DISK_READ,&dd);
    if (rc != dd.nsectors) {    /* had some kind of error */
        if (--retries > 0) {    /* retries left? */
            (void)_bios_disk(_DISK_RESET,&dd);
            goto rwagain;       /* reset and try it again */
        } /* end if */
        fprintf(stderr,"diskio error %04X\r\n",rc);
        fprintf(stderr,"t:%d s:%d h:%d\r\n",dd.track,dd.sector,dd.head);
        fprintf(stderr,"d:%d n:%d a:%X\r\n",dd.drive,dd.nsectors,dd.buffer);
        pf.cr |= ERRBIT;        /* set error bit */
        return;                 /* that's all, folks */
    } /* end if */

    if ((pf.cr & RW) == 0)      /* reading? copy buffer data to user */
//***RAC
//fmemcpy((char far *)(cmem + pf.ba),trkbuf,mywc);
    _fmemcpy((char far *)(cmem + pf.ba),trkbuf,mywc);
    
    pf.bn += dd.nsectors;       /* update registers */
    pf.ba += (2 * mywc);
    if (pf.wc < 256)            /* if reading last partial block */
        pf.wc = 0;              /* request is now done */
    else
        pf.wc -= (256 * dd.nsectors);
    if (pf.wc > 0)              /* anything left in this request? */
        goto domore;            /* if so, keep going */
    return;
} /* end flopio() */

void
fmemcpy(to,from,num)            /* copy memory between far pointers */
short far * to;                 /* destination */
short far * from;               /* source */
unsigned int num;               /* # of words to move */
{
    if (num) {
        do {
            *to++ = *from++;    /* move whole words for speed */
        } while (--num);
    } /* end if */
} /* end fmemcpy() */

void
ivideo(mode)                    /* init video subsystem */
int mode;                       /* 0 to init, 1 to reset */
{
    if (mode == 0) {            /* initialize? */
        dflag = pflag = lflag = row = col = 0;
        dreg.h.ah = 0x0F;
        VIDEOINT;               /* get current page */
        opage = dreg.h.bh;
        omode = dreg.h.al;
        dreg.h.ah = 3;
        VIDEOINT;               /* get cursor type */
        cstart = dreg.h.ch;
        curend = dreg.h.cl;
        dreg.x.ax = 0x0003;
        VIDEOINT;               /* init to text mode */
        dreg.h.ah = 5;
        dreg.h.al = opage;
        VIDEOINT;               /* set to current page */
        dreg.h.ah = 0x0B;
        dreg.h.bh = 0;          /* set background & border */
        dreg.h.bl = 1;          /* to blue */
        VIDEOINT;
        poscur();
        cleol(1);               /* clear entire screen */
    }
    else {                      /* reset when done */
        dreg.h.ah = 0;
        dreg.h.al = omode;      /* reset video mode */
        VIDEOINT;
        dreg.h.ah = 1;
        dreg.h.ch = cstart;
        dreg.h.cl = curend;
        VIDEOINT;               /* restore cursor */
    } /* end if */
} /* end ivideo() */

unsigned char                   /* translated character to send to program */
h_in(ui)                        /* hazeltine keyboard processing */
int ui;                         /* incoming character */
{
    /* 0200 bit on (in returned value) means send lead-in first */
    if ((ui & 0x00FF) == 0) {   /* 0 in lo byte: scan code in hi byte */
        switch (ui >> 8) {      /* convert scan code to h1510 char(s) */
        default:                /* anything else means send BREAK */
            return ('\0');
        case 017:               /* backtab */
            return ('\026');
        case 0110:              /* up cursor */
            return ('\214');
        case 0120:              /* down cursor */
            return ('\213');
        case 0113:              /* left cursor */
            return ('\010');
        case 0115:              /* right cursor */
            return ('\020');
        case 0122:              /* insert */
            return ('\001');
        case 0123:              /* delete */
            return ('\023');
        case 0107:              /* home */
            return ('\222');
        case 0117:              /* erase to eol */
            return ('\234');
        case 0111:              /* page up */
            return ('\021');
        case 0121:              /* page down */
            return ('\031');
        } /* end switch */
    } /* end if */
    return (ui & 0177);         /* give back original character */
} /* end h_in() */

void
h_out(i)                        /* hazeltine output routine */
char i;                         /* character to process */
{
    /* handle cursor positioning sequence */
    if (pflag) {                /* already got leadin and ctrl char */
        switch (pflag) {
        case 1:                 /* x (column) is next */
            col = i;
            if (col > MAXCOL)
                col -= 96;
            pflag = 2;          /* advance state */
            break;
        case 2:                 /* followed by y (row) */
            row = i;
            if (row > MAXROW)
                row -= 32;
            pflag = 0;          /* sequence finished */
            poscur();
            break;
        } /* end switch */
        return;
    } /* end if */

    /* handle all other special characters */
    if (i == LEADIN) {
        lflag = 1;              /* begin processing leadin */
    }
    else if (i == '\020') {
        col += 1;               /* right cursor */
        poscur();
    }
    else if (i == '\011') {
        getpos();
        do {
            col += 1;           /* tab */
        } while (col & 7);
        poscur();
    }
    else if (lflag && i < ' ') {
        getpos();
        switch (i) {            /* process rest of lead-in sequence */
        case '\022':            /* home cursor */
            row = col = 0;
            poscur(); break;
        case '\014':            /* up cursor */
            row -= 1;
            if (row < 0)
                row = 0;
            poscur(); break;
        case '\013':            /* down cursor */
            row += 1;
            if (row > MAXROW)
                row = MAXROW;
            poscur(); break;
        case '\021':            /* position cursor */
            pflag = 1; break;
        case '\034':            /* home & clear screen */
        case '\035':            /* home & clear screen */
            row = col = 0;
            poscur();           /* FALL THROUGH */
        case '\030':            /* clear to eos */
            cleol(1); break;
        case '\017':            /* clear to eol */
            cleol(0); break;
        case '\031':            /* set dim mode */
            dflag = 1; break;
        case '\037':            /* set bright mode */
            dflag = 0; break;
        case '\032':            /* insert line */
            dreg.h.ah = 7;      /* scroll down */
            dreg.h.al = 1;      /* 1 row */
            dreg.h.bh = 0x1F;
            dreg.h.ch = row;
            dreg.h.cl = 0;
            dreg.h.dh = MAXROW;
            dreg.h.dl = MAXCOL;
            VIDEOINT;
            break;
        } /* end switch */
        lflag = 0;              /* done with leadin sequence */
        return;
    }
    else if (lflag && i >= ' ') {
        lflag = 0;              /* invalid lead-in sequence */
        showit(LEADIN);         /* show the lead-in */
        showit(i);              /* and the next character */
    }
    else {                      /* cr,lf,bs,bell, or printable */
        showit(i);              /* display ordinary characters */
    } /* end if */
} /* end h_out() */

char printable[] = "\a\b\n\r";  /* list of proccessable control characters */

void
showit(c)                       /* show character */
char c;                         /* what to display */
{
    if ((c >= ' ' && c <= '\176') || strchr(printable,c) != (char *)NULL) {
        ttychr(c);              /* this routine handles everything else */
        getpos();
        if (row > MAXROW) {     /* past end of active screen? */
            cleol(0);           /* erase bottom line */
            dreg.h.ah = 6;      /* scroll up */
            dreg.h.al = 1;      /* 1 row */
            dreg.h.bh = 0x1F;
            dreg.h.ch = 0;
            dreg.h.cl = 0;
            dreg.h.dh = MAXROW + 1;
            dreg.h.dl = MAXCOL;
            VIDEOINT;           /* scroll up one line */
            row -= 1;
            poscur();
        } /* end if */
    } /* end if */
} /* end showit() */

void
getpos()                        /* read cursor position */
{
    dreg.h.ah = 0x03;           /* read cursor position */
    dreg.h.bh = opage;
    VIDEOINT;
    row = dreg.h.dh;            /* current row */
    col = dreg.h.dl;            /* current column */
} /* end getpos() */

void
poscur()                        /* position cursor to current row/col */
{
    dreg.h.ah = 2;              /* position cursor */
    dreg.h.bh = opage;
    dreg.h.dh = row;            /* to here */
    dreg.h.dl = col;
    VIDEOINT;
} /* end poscur() */

void
cleol(m)                        /* clear to eos or eol */
char m;                         /* 0 for eol, 1 for eos */
{
    getpos();                   /* determine where we are */
    dreg.h.ah = 6;              /* scroll up */
    dreg.h.al = 0;              /* 0 rows = erase window */
    dreg.h.bh = 0x1F;
    dreg.h.ch = row;            /* from current position */
    dreg.h.cl = col;
    dreg.h.dh = row;            /* to the end of this line */
    dreg.h.dl = MAXCOL;
    VIDEOINT;                   /* have erased to eol */
    if (m) {                    /* want remainder of screen erased? */
        dreg.h.ah = 6;          /* scroll up */
        dreg.h.al = 0;          /* 0 rows = erase window */
        dreg.h.bh = 0x1F;
        dreg.h.ch = row + 1;    /* from next line */
        dreg.h.cl = 0;
        dreg.h.dh = MAXROW + 1; /* all rows */
        dreg.h.dl = MAXCOL;     /* all columns */
        VIDEOINT;
    } /* end if */
    dreg.h.ah = 1;
    dreg.h.ch = cstart;
    dreg.h.cl = curend;
    VIDEOINT;                   /* restore cursor */
    poscur();
} /* end cleol() */

void
ttychr(c)                       /* output character to screen */
char c;                         /* character to output */
{
    if (c >= ' ') {             /* printable? */
        dreg.h.ah = 9;
        dreg.h.al = c;          /* store char in-place with attribute */
        dreg.h.bh = opage;
        dreg.h.bl = (dflag ? 0x17 : 0x1F);
        dreg.x.cx = 1;          /* dim or bright white on blue background */
        VIDEOINT;
    } /* end if */
    dreg.h.ah = 0x0E;           /* now output it for real */
    dreg.h.al = c;
    dreg.h.bh = opage;
    dreg.h.bl = 0x1F;
    VIDEOINT;                   /* store character and advance cursor */
    getpos();
} /* end ttychr() */


/* 
    INT70H Timer Interrupt Callback
*/
static int jiffies = 0;
static int parts = 0;

void interrupt
int_70()                        /* process 976 usec timer interrupts */
{
    long far * lfp;

    lfp = MK_FP(0x40,0x9C);     /* where count interval is */
    *lfp = 1000L;               /* reset counter for more time */
    if (++jiffies >= 17) {      /* done enough for 16.667 msec? */
        jiffies = 0;            /* reset */
        ltccnt += 1;            /* count a tick */
        if ((++parts % 15) == 0) {
            jiffies -= 1;       /* add one jiffy every 15 ticks */
            parts = 0;
        } /* end if */
    } /* end if */
    _chain_intr(int70a);        /* do the original code now */
} /* end int_70() */
#endif

void
initia()                        /* initialize instruction array */
{
    fillit(0010000,0067777,1);  /* double-op word */
    fillit(0110000,0167777,2);  /* double-op byte */
    fillit(0000400,0003777,3);  /* branches */
    fillit(0100000,0103777,4);  /* branches */
    fillit(0000300,0000377,6);  /* single-op word */
    fillit(0005000,0006377,6);  /* single-op word */
    fillit(0105000,0106377,5);  /* single-op byte */
    fillit(0004000,0004777,7);  /* jsr */
    fillit(0000200,0000207,8);  /* rts */
    fillit(0000100,0000177,9);  /* jmp */
    fillit(0000240,0000277,10); /* condition codes */
    fillit(0074000,0074777,11); /* xor */
    fillit(0077000,0077777,12); /* sob */
    fillit(0006700,0006777,13); /* sxt */
    fillit(0104000,0104777,14); /* emt & trap */
    fillit(0106400,0106477,15); /* mtps */
    fillit(0106700,0106777,15); /* mfps */
    fillit(0006400,0006477,16); /* mark */
    fillit(0070000,0073777,17); /* eis */
    fillit(0000000,0000006,18); /* halt,wait,rti,bpt,iot,reset,rtt */
} /* end initia() */

void                            /* fill bytes in iarray */
fillit(unsigned int from, unsigned int to, unsigned int val)
{
    from >>= 3; to >>= 3;       /* store 8 instructions per byte */
    do {
#ifdef DEBUG
        if (iarray[from] != 0) {
            fprintf(stderr,"%06o had %d, wants %d\n",
                    from, iarray[from], val);
        } /* end if */
#endif
        iarray[from] = val;
    } while (++from <= to);
} /* end fillit() */

