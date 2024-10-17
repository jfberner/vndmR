/*  command executors  */

#ifndef CHARMODE
void windowcom ( void ) ;
#else
void systemcom ( void ) ;
#endif


#ifdef LINUX
typedef clock_t relos_t ;
#else
typedef time_t relos_t ; 
#endif


double lapsed ( relos_t ) ;             // time ellapsed since relos_t
void timeset ( relos_t * ) ;            // set relos_t to current time 

FILE * current_input ( void ) ;
char * current_input_name ( void ) ;

int nodzbelow ( short int * , short int ) ; 
void nodsizes ( short int *, short int * ) ; 
void delnodz ( short int *, short int * ) ; 
void reset_nodz ( short int *, int * ) ;     
void reset_nodz_doublep ( short int *, double * ) ; 
void dildit ( int, int, char * ) ; 
int reading_datafile( void ) ; 
void tview_abort ( char ) ; 
int rdtax ( void ) ; 
void gimetax ( int ) ;    // gives taxon name [if (usetaxname & 2)] or number [ if (usetaxname & 1) ] 
void notreeerror( void ) ;  // if no trees in memory, call errmsg
void errarg ( char ) ;    // errmsg for argument char 
void nodaterror( char * ) ; // if no data have been read, calls errmsg
void randinit ( void ) ;  
void randomlist ( int , unsigned short int * , int , char * ) ; // num of things , list , force first , list of activities 
void initnet ( int, int, int ) ;  // creates 3-taxon network: (arg1 ( arg2 arg3))
int gtnubrack ( void ) ; 
int piwe_init ( void ) ; 
short int * gettre ( int ) ;  // returns pointer to the tree
void intrupt ( int ) ; 
void tplotmem ( void ) ; 
int drawtree ( short int *, short int ); 
void copystates ( int , unsigned int , char * ) ; 
void puchar(int, int); 
int peep( void ) ; 
int gtnu( void );
double gtdouble ( void ) ; 
void init_tmpmask( void );
int mklist( short int *, short int *, short int, short int );
                         /*  list *, ancestor *, include htus (nt) or terms (0), basal node */
                         /*  returns number of items put in list  */ 
void mksis( short int *);   /*  makes (polyotmous) ancestor function
                                into complete tree  (sis and lef) */
int mkoptlist ( short int *, short int * ) ;
                        /*  makes ancestor function into complete tree (sis and lef),
                            puts list of nodes in first arg., and counts forks  */ 
void packdata( void ); 
void getscope( int, int, char *);
void display_charcodes( void ); 

VTYPE unsigned int tmpmask[257];

#define INF 32700
#define LINF 4294967295
#define B0 1431655765    /* 01010101010101010101... */
#define B1 2863311530    /* 10101010101010101010... */ 

VTYPE char * current_command  ;

int reading_screen( void ) ; 

void treemonofun (void );
void recursepruns ( int startat, signed char * tlist );
void retouchsmalltree ( void );
void constpack ( int **bu, int dn );
void rdgroups( int **dond, int *vals, int *cells );
void filter_trees( void );
void finalcons( void );
void buffcon (void);
void chkparms (void);
void chkout ( int on, int a, int b );
void parse_out( void );
void doyou (void);
void onoff( char *ps, char *txt);
void zert (int what, int where );
void callyou(void);
void datamem(void);
void mkbush( short int * an );
void savetree ( short int *an, FILE *where );
void saveanx( int cual );
void convertree( void );
void macfreelo(void);
void report_loops ( void );
void goback( void );
void dosap ( short int * tpr );
void copygil ( int scrolldiff );
static void errline(void);
void inpurge(void);
static void reader(void);
void echoit( char * str, char * plus );
void addsp(short int cual );
void donodmsg(int cual);
void calculatelineofs(int which);
void rotabra( short int *an);

#ifndef LINUX 
void win_drawtree ( HDC hdc, short int * an, short int nodnum ) ;
void Line ( HDC myhdc , int node , int fromx, int fromy, int tox, int toy ) ;
#endif

void movetree(int x, int y);
void updatecurrlen ( short int * tr );
void custom_search(void);
void randtreefun ( void );
void calculate_autoset ( void );
void sect_search(void);
void customized_search ( char * );
void noisy ( void );
void doabout ( void );
void filedrawtreefunc ( void );
void gray_menus ( void );
void savetreefunc ( void );
void treelenfun ( void );
void showtreefun ( void );
void blengthfun ( void );
void tcomfun ( void );
void prunefun (void );
void resolsfun (void );
void condenfun (void );
void comparefun (void );
void rerootfun (void );
void taxinclfun (void );
void nodnumfun (void );

#ifndef CHARMODE
#define FOCUS_ON(x) SetFocus ( GetDlgItem ( hdwnd , x ) ) ; return FALSE ; 
#endif
