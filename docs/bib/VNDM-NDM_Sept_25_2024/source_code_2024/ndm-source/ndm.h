#include<stdio.h>
#include<stdlib.h>
#include<time.h>

#ifdef LINUX
#include <fcntl.h>
#define _MAX_PATH 260 
#endif

int autoreplace = 0 ;
int reset_swapping ;

int do_exact_search = 0 ; 
double bestscore = 1 ; 
double grid_startx = 0 ,
        grid_starty = 0 ,
        grid_height = 1 ,
        grid_width = 1 ;
double xframeshift = 50 , yframeshift = 50 ; 
int saveall = 0 ;
char str[30] ; 
int abslim = 3 , musthaveone = 1 ; // only for rule 4 
int ridofwides = 0 ; 
int cols = 10 ; 
int rows = 10 ; 
int spp = 100 ; 
int maxsize = 1000000 ; 
int xycols = 10 , xyrows = 10 ; 
#define int32 unsigned  int  
int32 ***matrix , *** fake_matrix ;
int32 ***assmatrix ; 
int * numentries , * fake_numentries , ** sized ;
int * numassentries ; 
int minscore = 2 ;
double minrealscore = 1.0 ;  
char ** isdefd ; 
int spcells , arcells ; 
typedef struct { 
           int32 * lst ;
           int32 * splist ; 
           int size ; 
           int erase ; 
           double score5 ;
           int numspp ;
           int key ; 
           int hicell , locell ; 
           char swapd ; } Artyp ;
int compare_perc = 0 ;
int min_pres_perc = 1 ; 
           
Artyp * rec , currec , * recptr ; 
int score5 ; 
int32 * intersptr ;

int * listin , * listout , * listadja , * listnonadja , * listedge ;
int * listinpt , * listoutpt , * listadjapt , * listnonadjapt , * listedgept ; 

int cut1 = 2 , 
    cut2 = 2 , 
    cut3 = 2 , 
    cut4 = 2  ; 
int maxrec = 100000 ; 
FILE * input , * output , * logfile = NULL ; 
int * tmplist , * setlist , * nosetlist ; 
int outofset ; 
int * archeckd ; 

#ifdef LINUX
clock_t linux_end , linux_init ; 
#endif 
time_t begin ; 

char numbits [ 65536 ] ; 
int query = 0 , breakable = 1 ; 
double suboptimal = 0 ;
double slopeval = 1 ; 
int make_random_data = 0 , probone = 50 , ranseed = 1 ; 
double sevals = 0 ; 
int32 ** curinters ; 
int32 ** curdablor , ** curdabland ; 
int numcheks = 0 ; 
int chkfreq = 1000 ;
int numreps = 0 ; 
void chkbyebye ( void ) ; 
char ** empcell ; 
int ** fromspot , atspot ;
int32 * widefilter ; 
int32 ** upand , ** upor ; 
int * bufsetlist , * bufnosetlist ; 
int yperc = 0 , xperc = 0 ; // percentage of cell wid/hei to include in neighbour cell
int fill_abslim = 7 ; 

int retouch = 1 ; 
int also_save_data = 1 ; 

int32 ** forsp , ** backsp ; 

/****  GLOBALS for calculations   */
int size ; 
int atcell ; 
int32 atbit ; 
#define BIT32 ( 1 << 31 ) 
int cursize ; 
int totbits , totareas ; 
double contars = 0 ; 
int gapsize ; 

void * mymem ( int ) ;
double dorule5 ( int ) ; 

int overflow_warn = 0 ; 
double ifac = 0.5 ,
        afac = 0.75 ,
        oufac = 0.5 ,
        oafac = 2 ,
        ononafac = 0.5 ;  
int translate_to_coords = 0 ;
int const_search = 0 ;
int32 * const_list ;
int32 last_const_bit ;
int last_const_cell ; 

/*****  This was used in determinig guide fields, in an
        attempt to produce reliable heuristics. It didn't work.
int numfields = 0 ;
int ** fieldlist ; 
int * fieldsize ;
int curfield ;
int atdepth ;
int evals ;
Artyp * nuars ; 
int32 ** distmat ;
int overestimate4 = 0 ;
*******/

int dontadd = 0 ; 
int use_wide_init = 0 ; 
int havcomb [ 65536 ] ; 
int key_combination ; 
int skip_superfluous = 0 ; 
int dump_suboptimal = 1 ; // if 0 , it retains areas (during heuristic search) even if scoring spp. < minscore
int cells_to_swap = 1 ; 
time_t init_search , now , last ; 
int max_buffer_clean = -1 , num_buffer_cleans = 0 ; 
int scoring_spp ; 
int32 * bigar , * smallarset , * bigarset ;
int bigarnumspp , smallarnumspp ; 
int32 last_sp_filter ;
Artyp * swaprec ;
int recinit ;
int arsexd = 0 ;
int * faraway , * farawaypt ;
int32 * farar ;
int * globnonadja ; 
int smallest_cell , largest_cell ;
int minframex , minframey , maxframex , maxframey ;
int dups_found = 0 ; 

typedef struct {
    Artyp * toar ;
    void * tolist ; } Listyp ;
Listyp * reclist , * nexreclist ;
Listyp ** sizelist ; 

int use_edge_props = 0 ;

FILE * startfile ;
FILE * bread_file ;
#define Spnamesz ( 50 )
char ** spname = NULL ; 

int post_individuation = 1 ;

typedef struct {
    short int minc , maxc , minr , maxr ; }  MinMaxtyp ;
MinMaxtyp * spminmax ;     
