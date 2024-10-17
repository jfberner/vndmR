
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <setjmp.h>
#include <ctype.h>

#ifndef LINUX 
#include <windows.h>
#include <windowsx.h>
#include <io.h>
#include <conio.h>
#include <winbase.h>
#include <winuser.h>
#include <commctrl.h>
#include <commdlg.h>
#include <process.h>
#else
#include <fcntl.h>
#define MAX_PATH 160
#define _MAX_PATH 160
#endif

#include "pag_uts.h"

typedef unsigned char Byte ;
typedef short int Tint ;
typedef unsigned short int Tuss ;
typedef int Fint ;
typedef unsigned int Fuss ;
typedef void ( * Proctyp )( void ) ;

#define Null (0L)

#define Cvals (256)
#define Tvals (65536)

#define Buffsz (512)        /* constants */
#define Biffsz (Buffsz*8)
#define Spewsize (2048) 
#define Ncolmt (75)
#define Argsize (1024)
#define Namesize (32)      /* max size of taxon names etc */
// #define Minram (16*1024*1024)
VTYPE int Minram ;
VTYPE int maxnest ; 

extern char cmdname[] ;   /* most recently read name or string */
extern char * current_command ;

extern char lobix[] ;     /* index of low bit in Byte -- do not use for ints */
extern char tmems[] ;     /* # on bits in a Tuss -- do not use for ints */

extern int flobix ( Fuss ) ;  /* low bit in 4 Bytes   */
extern int fhibix ( Fuss ) ;  /* high bit in 4 Bytes   */
extern int fmems( Fuss ) ;  /* on bits in a Fint */

extern int izatty( FILE * ) ;      /* misc. utility functions */
extern char * namov( char * , char * ) ;
extern char * strend( char * ) ;
extern int strlength( char * ) ;

extern int brevcomp( char * , char * ) ; 
        /* first brev, second name ; case sensitive */
extern int namecomp( char * , char * ) ; /* case insensitive */

extern char * setb( int , int , char * ) ; /* cnt, val , dest rets next location */
extern char *  identb( int , int , char * ) ; /* , val , dest */
extern int * seti( int , int , int * ) ;
extern int * movi( int , int * , int * ) ;

extern Fint vailram( void ) ;
extern void * lomark( void ) ;
extern void * loram( Fuss ) ;
extern void * hiram( Fuss ) ;
extern void * himark( void ) ;
extern void loset( void * ) ;
extern void hiset( void * ) ;
extern void freelo( void ) ;
extern void freehi( void ) ;
extern void freeli( void ) ;
extern void lockram( int * ) ;
extern void freelock( int * ) ;
extern void * loray( int , int , int ) ; /* rows , cols , elemsize */
extern void * hiray( int , int , int ) ;
#define lolocra( x , y , z ) ((x)=loray((y),(z),(sizeof(**(x)))))
#define hilocra( x , y , z ) ((x)=hiray((y),(z),(sizeof(**(x)))))
#define loloc( x , y ) ((x)=loram((y)*(sizeof(*(x)))))
#define hiloc( x , y ) ((x)=hiram((y)*(sizeof(*(x)aaaa))))
extern void * unihiralloc ( char *, int, int, int ) ;
extern void * uniloralloc ( char *, int, int, int ) ;
extern void loralloc ( char ** , int, int, int, int ) ; 
extern void locraso ( char **, int, int , int, int ) ; 

void newln ( void ) ;
VTYPE int (*printable) ( int, int, int *) ;           /* prints values from pointer  */
extern int printable_default ( int, int , int *) ;
extern int printable_optional ( int, int , int * ) ; 
VTYPE int (*printable_floats) ( int, int, double *) ;           /* prints values from pointer (floats) */
extern int printable_default_floats ( int, int , double *) ;
extern int printable_optional_floats ( int, int , double * ) ; 

extern char * wintvert ( int, int ) ;  /* prints with width, number  */
extern char * intvert( int ) ;    /* spew facility  */
extern void spewout( void ) ;     /* purge spew buffer and vert buffer */
extern void spewer ( void ) ;     /* called by spewout; counts printed lines  */ 
extern char * tospew( char * ) ;  /* insert one str into spew buffer */
extern char * tojoin( char * ) ;  /* insert one str into spew buffer, no blank */
extern char * spewln( void ) ;
extern char * spewch( int ) ;
extern char * spewchos( int ) ;
extern char * spewspx( int ) ;  /* cnt spaces into spewbiuff */
extern void spewjn( void ) ;    /*  purges spew buffer without new line  */
extern void joinem (char * , ... ) ;  /*  add str without blank  */ 

extern void spewem( char * , ... ) ;  /* put args in spew buffer, then purge */
extern void myp ( void * , ... ) ;    /* prints args , using "printf" format */
extern void myerr ( void * , ... ) ;    /* prints args , using "printf" format, and calls error trap  */

extern int safecall( Proctyp ) ;    /* longjump trap rets 1 on no error */
extern void errtrap( void ) ;

extern void errmsg( void * , ... ) ;  /* like spewem but purges input and calls errtrap */
extern void warnem ( char *, ... ) ;  /* like spewer, but beeps or does nothing, according to seetings  */ 
extern void mywarn ( void * , ... ) ;  /* like warnem, but using "printf" format */ 

extern int end_of_input( void ) ;
extern int end_of_input( void ) ;
extern void ask( char * ) ;

// extern int gtch( void ) ;     /* get next char (unsigned) as int */
// extern void ungtch( void ) ;  /* back up ONE char */

VTYPE int ( *gtch ) (void ) ;
extern int normal_gtch ( void ) ;
extern int macro_gtch ( void ) ;

VTYPE void ( *ungtch ) ( void ) ; 
extern void normal_ungtch ( void ) ;
extern void macro_ungtch ( void ) ;

extern int gtnb( void ) ;      /* get nect non whitespace char */
extern int gotc( int ) ;       /* if gtnb() matches arg, eats it and returns nonzero,
       otherwise ungtch and returns 0 */
extern int rdfilename( void )  ;
        /* into cmdname, any but ' ' or ';' , case kept */
extern int rdcmd( void ) ;  /* all alpha, set to lower, in cmdname */
extern int readid( void ) ;


extern void tntpivot( char * ) ;

/* GLOBAL VARIABLES */

VTYPE Tuss **matrix ;      /*  store original data, only terms. (NT x NC.) */
VTYPE Fuss **matrix4 ;
VTYPE Byte **matrix1 ;
VTYPE Tuss * cell2 ;
VTYPE Byte * cell1 ;
VTYPE Fuss * cell4 ; 
VTYPE int celldim ;
      // celldim = 1 for matrix cells of 8-bits (8 states)
      //           2 for matrix cells of 16-bits (16 states)
      //           4 for matrix cells of 32 bits (32 states)
#define MATSET( x , y , z ) if ( celldim == 2 ) (x) = matrix[(y)][(z)] ; else if ( celldim == 1 ) (x) = matrix1[y][z] ; else (x) = matrix4[(y)][(z)] ; 
#define SETMAT( x , y , z ) if ( celldim == 2 ) matrix[(y)][(z)] = (x) ; else if ( celldim == 1 ) matrix1[(y)][(z)] = (x) ; else matrix4[(y)][(z)] = (x) ; 
VTYPE unsigned short int * ancstates ;  /*   Used only for Sankoff -- points to taxon with ancestral states, 0 by default   */ 
VTYPE Fuss * ancstates4 ;
VTYPE unsigned char * ancstates1 ;
#define SETANC( x , y ) if ( celldim == 2 ) (x) = ancstates [ (y)  ] ; else if ( celldim == 4 ) (x) = ancstates4 [ (y) ] ; else (x) = ancstates1 [ (y) ] ;

VTYPE int nt , nodz, root, realnt ;     /* nt num currently active, realnt all in matrix */
VTYPE int nc; 
VTYPE char **taxname;       /*  Taxon names   */ 
VTYPE char **blockname ;    /*  Names of data blocks, for interleaved */
VTYPE int nblocks ; 
VTYPE char *taxact;        /*  whether taxon is active   */ 
VTYPE int scopis[2];      /*  used to get scopes   */ 

VTYPE char dataname[ MAX_PATH ] ; 
VTYPE char logfilename[ MAX_PATH ] ; 
VTYPE char treefilename[ MAX_PATH ] ;
#define SHT 0
VTYPE char tsavemode ;

/*  this is the basic tree stuff  */ 
VTYPE short int *lef, *rig, *sis, *anx, *nodlist, *nodfork, *issupp; 

// VTYPE Fuss INAPP = 0 ;     Note!!  to use inapplicables, this has to be set to ALL bits, and missing to one less
VTYPE Fuss MISSING ; 
#define MAXSTATE (32)
VTYPE Fuss maxstate ; 

VTYPE char ** charnames ;
VTYPE char *** statenames ; 

VTYPE int num_continuous_chars ; 

VTYPE short int *htulist;     /* to optimize stuff, one ch. at a time   */ 
VTYPE unsigned short int ***cost_matrix; 
VTYPE int have_asymmetric; 
VTYPE char **nodmsg;    /*  this is used by the tploter  */ 
VTYPE char send_to_base;   /*  in tread, ommitted terms. are
                        placed at tree base (1), or ommitted from tree (0)  */
VTYPE int outgroup; 
VTYPE char nakedtree;
VTYPE FILE * logfile, * treefile; 
VTYPE short int **mem_tree;
VTYPE int trees_in_mem;
VTYPE int maxtrees; 

VTYPE int screen_size;
VTYPE int screen_width;
VTYPE int linsdone;
VTYPE char pausing;
VTYPE char mybeep ;
VTYPE char warning ;
VTYPE char timeit;
VTYPE char timemenus ;
VTYPE char breakable ;
VTYPE char myecho;
VTYPE char tsavemode; 
VTYPE char dopiwe;
VTYPE char usetaxnames;
VTYPE char silent;
VTYPE char tmpsilent ; 

#define BRKPT( x )  { if( breakable == 1 ) intrupt( x ); }
         //   x is not used for anything !!!

VTYPE double *fitf; 
VTYPE double konk; 
VTYPE unsigned long int ranseed;
VTYPE short int * ladd; 

VTYPE char junkstr[40000];
int my_spawn ( char * , ... ) ; 
VTYPE int treemode ; 
VTYPE int currtree ;
VTYPE int recalctree ;

#ifndef LINUX 
VTYPE TEXTMETRIC ourtm;
VTYPE HDC hdc ;
VTYPE HWND hwnd, cmhwnd, sthwnd, txnhwnd, chrhwnd, findtxnhwnd, dosehwnd, treehwnd, matrixhwnd, commenthwnd;
HWND hProgWnd, hProgBarWnd;
#endif

int userstop ;


#ifdef LINUX
typedef long int DWORD ; 
#define IDYES 1
#define IDNO 0
#endif

#ifdef MACOID
unsigned long int macoid_rand ( void ) ; 
#define rand()  macoid_rand() 
#else 
#define rand() rand ()
#endif

typedef struct {
     int colR , colG, colB , thickness ; 
     int numpoints ;
     float * x , * y ; }  Maplintyp ; 
extern Maplintyp * maplin ;

#define int32 unsigned long int  
typedef struct { 
           int32 * lst ;
           int32 * splist ;
           double bootarval , bootspval ; 
           int fromrepl ; 
           int size ; 
           int mark ;
           int erase ;
           int numspp ; 
           double score ; } Artyp ; 
extern Artyp * recptr ; 

