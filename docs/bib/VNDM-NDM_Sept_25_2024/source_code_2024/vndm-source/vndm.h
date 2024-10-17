#include<stdio.h>
#include<conio.h>
#include<stdlib.h>
#define int32 unsigned long int  
#define BIT32 ( 1 << 31 ) 
double grid_startx = 0 ,
        grid_starty = 0 ,
        grid_height = 1 ,
        grid_width = 1 ; 
int initializing = 1 ; 
int query = 1 ; 
char numbits [ 65536 ] ; 
FILE * infile , * output , * logfile = NULL , * outspace = NULL ; 
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
Artyp * rec , * recptr , ** arlist ; 
int cols = 0 ; 
int rows = 0 ; 
int spp = 100 ; 
int maxsize = 10000 ; 
int32 *** matrix ; 
int32 *** assmatrix ; 
int32 * splist , * inflist ; 
int * numentries , * numassentries ; 
char ** isdefd ; 
int spcells , arcells ; 
int cut1 = 2 , 
    cut2 = 2 , 
    cut3 = 2 , 
    cut4 = 2  ; 
int numrecs , maxrecs = 0 ; 
char ** outmap ; 
int showcursor = 0 ; 
int cursrow , curscol ; 
int sharedspp ; 
int cursize ; 
int * archeckd , * tmplist ; 
int32 * intersptr , * lst , * inflst ; 

int totareas ; 
int sharedspp ; 
char * logfilename ; 
char comstring [ _MAX_PATH ] , prompt [ 75 ] ; 
int cursor_move = 1 ; 
int abslim = 7 , musthaveone = 1 ; // only for rule 4 
int32 * dablor , * dabland ; 
int * setlist , * nosetlist ; 
int outofset ; 
int markscore = 0 ;
int32 * widefilter ; 
int paint_mode = 0 ; 
int suboptimal = 0 ;

void cls ( void ) ; 
int divide_data ( void ) ;
int mgetch ( void ) ;

FILE * trackfile = NULL ; 

int * listin , * listadja , * listnonadja ;
int * listinpt , * listadjapt , * listnonadjapt ;
double * spscore ; 

double iifac = 0.5,
        iafac = 0.75 ,
        oufac = 0.5 ,
        oafac = 2 ,
        ononafac = 0.5 ;
double * dpres , * dout , * dass , * dinf , * dadja , * dnadja ;
int compare_perc = 0 ;
int min_pres_perc = 1 ; 

char ** fillist ;
int fill_large = 0 ; 

void doallscores ( void ) ;
void showcurset ( void ) ; 

#define SPKEY  ( 1 << 10 ) 
#define     RIG  (  77             | SPKEY ) 
#define      UP  (  72             | SPKEY ) 
#define     LEF  (  75             | SPKEY ) 
#define      DN  (  80             | SPKEY ) 
#define     END  (  79             | SPKEY ) 
#define     HOM  (  71             | SPKEY ) 
#define    ENTER (  13                     ) 
#define    BACK  (   8                     ) 
#define  ALTINS  (  162            | SPKEY ) 
#define  ALTDEL  (  163            | SPKEY )
#define    HOME  (   71            | SPKEY )

#define    ALT1   (   120           | SPKEY )
#define    ALTX  (  45             | SPKEY ) 
#define    ALTS  (  31             | SPKEY ) 
#define    ALTN  (  49             | SPKEY )
#define    ALTO  (  24             | SPKEY )  
#define    ALTP  (  25             | SPKEY ) 
#define    ALTD  (  32             | SPKEY ) 
#define    ALTM  (  50             | SPKEY ) 
#define    ALTI  (  23             | SPKEY ) 
#define    ALTU  (  22             | SPKEY ) 
#define    ALTC  (  46             | SPKEY ) 
#define    ALTA  (  30             | SPKEY ) 
#define    ALTH  (  35             | SPKEY ) 
#define    ALTE  (  18             | SPKEY ) 
#define    ALTV  (  47             | SPKEY ) 
#define    ALTW  (  17             | SPKEY ) 
#define    ALTF  (  33             | SPKEY ) 
#define    ALTG  (  34             | SPKEY ) 
#define    ALTK  (  37             | SPKEY ) 
#define    ALTL  (  38             | SPKEY )  
#define ALTEQUAL (  131            | SPKEY ) 
#define  ARROWUP (  72             | SPKEY ) 
#define  ARROWDN (  80             | SPKEY ) 
#define  ARROWRT (  77             | SPKEY ) 
#define  ARROWLF (  75             | SPKEY ) 


int use_edge_props = 0 ; 

#define MAXLINPTS 50000
#define MAXNUMLINS 100000
typedef struct {
     int colR , colG, colB , thickness ; 
     int numpoints ;
     float * x , * y ; }  Maplintyp ; 
Maplintyp * maplin ;
int nummaplins = 0 ; 

typedef struct {
     double * spmin , * spmax ;
     double * clmin , * clmax ;
     double min , max ;
     int numareas ;
     int * arlist ; 
     int is_xcess ; }  Constyp ;
Constyp * consen ;
int numcons ;

typedef struct {
    short int minc , maxc , minr , maxr ; }  MinMaxtyp ;
MinMaxtyp * spminmax ;     

