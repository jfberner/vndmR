#include "vndm.h"
#include <windows.h>
#include <windowsx.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <malloc.h>
#include "ibm.h"
#include <io.h>
#include "winbase.h"
#include "process.h"
#include <winuser.h>
#include "commdlg.h"
#include "commctrl.h"
#include "wingdi.h"
#include "winsock.h"
#include "consts.h"
#include "dialog.h"
#include <tchar.h>
#include <time.h>
#define Spnamesz ( 50 )

#ifdef _DEBUGGING_
int spbecomes[ 15000 ] ;
#endif

int isforsample = 0 ;
Artyp * bootinit , * replinit ; 

typedef struct {
            int defd ; 
            int numrecs , trurecs ;
            float * x ;
            float * y ; } Coordtyp ; 
Coordtyp * xymatrix ;

typedef struct {
        float x ;
        float y ; }
        Tmptyp ;
Tmptyp * tmpcord ; 

#define MAXY ( 100000 ) 


int didaboot = 0 , consensus_is_sample = 0 , run_autosample = 0 , run_autoconsense = 0 , autoconsense_cut = -1 ;
int sample_area_cut = -50 , sample_spp_cut = -50 ; 

int ignore_sp_lists = 0 ; 
int32 * fakesplist ;

int run_autosave = 0 ; 
int sample_spp_prop = 50 , sample_rec_prop = 50 , sample_repls = 10 , sample_area_prob = 50 ; 

unsigned long int rseed = 1 ; 

double sch_minimum_total_score = 2.000 ;
int sch_minimum_scoring_spp = 2 ; 
int auto_fill_all = 0 ; 

char is_cons_duwc = 0 ; 
int frame_the_search = 0 , no_useful_spp , armaxc , armaxr , arminc , arminr ; 
unsigned long int grandsumofpoints = 0 , numcoordstofile ; 
int * consensus_sp_list ;
int num_of_spp_in_consensus_list ; 
extern int ridofdupes , show_individual_dots ; 
int weight_species = 0 ;
double weight_min = 1.0000 ;
double * species_weight ;
double sqrt ( double ) ; 

int * species_tree , num_higher_taxa , numterminals , spspace ;
int * treesis , * treefirs , treeroot , number_of_groups ; 
int * treelist , * acurl , * innerlist , * nodfork ; 

int read_as_a_dat_file = 0 , user_wants_a_break = 0 ;
int chain_spp = 1 , conscut = 100 ;
int make_radius_assumed = 0 ;
int maxgridmult = 3 ; 

int transposexy = 0 , nocommas = 0 ;
int transposexymap = 0 ;  
double mfactor = 1 , mminusx = 0 , mminusy = 0 ;
double mfactormap = 1 , mminusxmap = 0 , mminusymap = 0 ;
int mapcurshiftx = 0 , mapcurshifty = 0 ;
extern HWND mainwnd ;

int use_autosize_grid = 0 ; 
double assume_x_is = 0 , assume_y_is = 0 ; 
double fill_x_is = 0 , fill_y_is = 0 ; 
extern double set_autosizegrid () ; 
int expand_cell_definition = 0 , do_automatrix = 0 ; 
int ctrl_arrow_changes_org = 1 ;
int dolatlong = 1 ; 
int curcons ;
typedef struct { float fillx , filly , assx , assy ; } Filltyp ;
Filltyp * ind_fills = NULL ; 
double mincellwid , mincellhei ;

int xsign = 1 , ysign = -1 ;
int xsignmap = 1 , ysignmap = -1 ; 
int32 * consenbitz ; 
char ** spname = NULL ;
unsigned long int * spact , * spingrid ;
int num_spingrid = 0 ; 
double maxx = -1000000 , minx = 1000000000 , maxy = -1000000 , miny = 1000000000 ; 
double truecellwid , truecellhei ,
      xperc = 0 , yperc = 0 , xassperc = 0 , yassperc = 0 ; 

double minimum_sp_score = 0 ; 

char str[20] ; 
int grid_created = 0 , data_is_xydata = 0 ; 
extern HINSTANCE hInst ;
extern HWND hwnd ; 
int atcoordx = 0 , atcoordy = 0 ; 
int warned_yet = 0 ;
extern char junkstr[4000] ; 
void drawmap ( int32 * , int32 * , int32 * ) ;
extern char **sccol ; 

extern void ( * curcmd_loop ) ( int ) ;
void show_consensus ( int ) ;
void showspecies ( int ) ; 
void cmd_loop ( int ) ;
void show_duwc ( int ) ;
void errmsg ( void * , ... ) ;
void viewmarks ( int ) ; 

int just_out_of_duwc = 0 ; 


#define SET_UPDOWN( ctrl, from , to , pos ) \ 
          { Button_Enable ( GetDlgItem ( hdwnd , ctrl ) , TRUE ) ; \
            Button_Enable ( SendMessage( GetDlgItem ( hdwnd , ctrl ) , UDM_GETBUDDY, 0, 0 ) , TRUE ) ; \ 
            hWho = SendMessage( GetDlgItem ( hdwnd , ctrl ) , UDM_GETBUDDY, 0, 0) ; \ 
            i = GetDlgCtrlID ( hWho ) ;\
            wsprintf ( junkstr,"%i", pos ) ; \
            SetDlgItemText ( hdwnd , i , junkstr ) ;\
            hWho = GetDlgItem ( hdwnd , ctrl ) ; \
            i = ( to )  | ( ( from )  << 16 ) ; \
            SendMessage((hWho), UDM_SETRANGE, 0,  i ) ; \
            SendMessage((hWho), UDM_SETPOS, 0 , (WPARAM)(int) ( pos )) ; } 

#define GETINT( x , y ) \ 
          { GetDlgItemText(hdwnd, ( y ) , junkstr, 80); \ 
            x = atoi(junkstr); } 
#define BUTT_CHECK( ctrl ) SendDlgItemMessage( hdwnd,  ctrl , BM_SETCHECK, (WPARAM) BST_CHECKED , 0 )


int redoallscores = 0 ;
int current_species ; 
#define Null NULL 

HWND waitwin = NULL ; 

char * waitmsg ;

char * ndm_bin_name = NULL ; 

void emptycurset ( void )
{
    int a ;
    for ( a = arcells ; a -- ; ) recptr -> lst[a] = 0 ;
    for ( a = spcells ; a -- ; ) recptr -> splist[a] = 0 ;
    recptr -> score = 0 ;
    recptr -> size = 0 ;
    showcurset () ;
    sprintf ( junkstr , "Set %i is empty" , recptr - rec ) ; 
    captf ( junkstr ) ;
    return ; 
}

void make_list_of_spp_for_consensus ( int which )
{
    int * ip , a ;
    Constyp * conpt ;
    double * mamax ; 
    conpt = consen + which ;
    ip = consensus_sp_list ;
    num_of_spp_in_consensus_list = 0 ;
    mamax = conpt -> spmax ; 
    for ( a = 0 ; a < spp ; ++ a ) 
        if ( mamax [ a ] > 0 )
            ip [ num_of_spp_in_consensus_list ++ ] = a ; 
    return ;
}

void set_ndm_bin_name ( void )
{
    FILE * in ;
    char * cp ;
    int a = ' ' ;
    in = fopen ( ".vndm.rc" , "rb" ) ;
    if ( in == NULL ) return ;
    cp = ndm_bin_name = malloc ( ( _MAX_PATH + 2 ) * sizeof ( char ) ) ;
    if ( ndm_bin_name == NULL ) return ;
    while ( isspace ( a ) && !feof ( in ) ) a = getc ( in ) ;
    if ( feof ( in ) ) return ;
    while ( a != 13 && !feof ( in ) && ( cp - ndm_bin_name < _MAX_PATH ) ) {
        * cp ++ = a ;
        a = getc ( in ) ; }
    * cp = '\0' ;
    return ; 
}        
  
BOOL CALLBACK WaitFunc(HWND hdwnd, UINT message, WPARAM wParam, LPARAM lParam)
{
    int i , j ;
    HWND hWho ;
    switch(message) {
        case WM_INITDIALOG :
               SetDlgItemText( hdwnd, 69 , waitmsg );
               break ; 
        case WM_PAINT :
              SetDlgItemText( hdwnd, 69 , waitmsg );
              break ; 
        case WM_COMMAND :
             switch(LOWORD(wParam)){
                 case IDM_WRITEDATAINFO:
                     SetDlgItemText( hdwnd, 69 , waitmsg );
                     break ; 
                  default : break; }
         break; }
    return 0;
}

void updatewait ( char * message ) 
{
  waitmsg = message ;
  SendMessage ( waitwin , WM_COMMAND , IDM_WRITEDATAINFO , 0 ) ;  
  InvalidateRect ( waitwin , NULL , 1 ) ;
}

void pleasewait ( char * message )
{
  waitmsg = message ;
  if ( waitwin != NULL ) imdone () ; 
  waitwin =
     CreateDialog(hInst, "WaitDB", hwnd, (DLGPROC) WaitFunc);
}    


void imdone ( void )
{
    DestroyWindow ( waitwin ) ;
    waitwin = NULL ; 
}

void myprintf ( void * i , ... )
{
    void ** ip = &i ;
    void * ipp = * ip ;
    int a ;
    ipp = * ip ; 
    sprintf ( junkstr , ip [ 0 ]  , ip [ 1 ] , ip [ 2 ] , ip [ 3 ] , ip [ 4 ] , ip [ 5 ] , ip [ 6 ] , ip [ 7 ] , ip [ 8 ] , ip [ 9 ] ) ;
    spitit ( junkstr ) ; 
    return ; 
}

extern char screentitle[1024] ;
extern char screencapt[65535*5] ; 

void screenf ( void * i , ... )
{
    void ** ip = &i ;
    void * ipp = * ip ;
    int a ;
    char * cp = screentitle ; 
    ipp = * ip ; 
    sprintf ( screentitle , ip [ 0 ]  , ip [ 1 ] , ip [ 2 ] , ip [ 3 ] , ip [ 4 ] , ip [ 5 ] , ip [ 6 ] , ip [ 7 ] , ip [ 8 ] , ip [ 9 ] ) ;
    while ( *cp != '\n' && * cp ) ++ cp ;
    if ( *cp == '\n' ) * cp = '\0' ; 
    return ; 
}

void captf ( void * i , ... )
{
    void ** ip = &i ;
    void * ipp = * ip ;
    int a ;
    char * cp = screencapt; 
    ipp = * ip ; 
    sprintf ( screencapt, ip [ 0 ]  , ip [ 1 ] , ip [ 2 ] , ip [ 3 ] , ip [ 4 ] , ip [ 5 ] , ip [ 6 ] , ip [ 7 ] , ip [ 8 ] , ip [ 9 ] ) ;
    win_refresh () ; 
    return ; 
}

void show_copyright_notice ( void )
{   cls () ; 
    myprintf( "\n\
\n\
\
\
 /************************************************************************\\  \n\
 *                                                                        *  \n\
 *       VNDM version 3.1:  Program to Visualize Areas of Endemism        *  \n\
 *              Copyright © Pablo A. Goloboff 2001-2016                   *  \n\
 *                                                                        *  \n\
 *                                                                        *  \n\
 *                              NOTICE                                    *  \n\
 *                                                                        *  \n\
 *  Permission to use, copy, modify, and distribute this software (and    *  \n\
 *  any documentation) for any purpose and without fee is hereby granted  *  \n\
 *  provided that the above copyright notice appear in all copies and     *  \n\
 *  that both the copyright notice and this permission notice appear in   *  \n\
 *  supporting documentation.                                             *  \n\
 *                                                                        *  \n\
 *  Neither the Author nor his supporting Institution (Consejo Nacional   *  \n\
 *  de Investigaciones Cientificas y Tecnicas, Argentina) make any        *  \n\
 *  claims about the suitability of this software for any purpose         *  \n\
 *                                                                        *  \n\
 \\************************************************************************/   \
 \n \
  \n \n \n [ hit ENTER or left-click to continue ]\
 " ) ;
 win_refresh () ; 
 return ; 
}


double slope , ordalor ; 

int line_passes_within ( int y , int x )
{
  double top , bot , lef , rig ;
  double yval , xval ; 
  top = y ;
  bot = y + 1 ;
  lef = x ;
  rig = x + 1 ; 
  // check whether line intersects any of the 4 sides of the cell
  // left side ? 
  yval = ( slope * lef ) + ordalor ;
  if ( yval < bot && yval > top ) return 1 ; 
  // right side ? 
  yval = ( slope * rig ) + ordalor ;
  if ( yval < bot && yval > top ) return 1 ;
  // top side ?
  xval = ( top - ordalor ) / slope ;
  if ( xval < rig && xval > lef ) return 1 ; 
  // bottom side ?
  xval = ( bot - ordalor ) / slope ;
  if ( xval < rig && xval > lef ) return 1 ;
  return 0 ; 
}   

void ( * fill_between ) ( int , int , int , int ) ; 

void small_fill_between ( int ay , int ax , int by , int bx )
{
    int i , j , k ; 
    int adds = 0 ;
    double fromy , toy , fromx, tox ;
    int sqrstartx , sqrstarty , sqrendx , sqrendy , atx , aty ; 
    if ( ax == bx ) {
        if ( ay < by ) { i = ay ; ay = by ; by = i ; }
        for ( i = by ; ++ i < ay ; ) fillist [ i ] [ ax ] = 1 ; 
        return ; } 
    if ( ay == by ) {
        if ( ax < bx ) { i = ax ; ax = bx ; bx = i ; }
        for ( i = bx ; ++ i < ax ; ) fillist [ ay ] [ i ] = 1 ; 
        return ; }
    // calculate a line from A to B
    if ( ay < by ) {
        sqrstarty = fromy = ay + 1 ;
        sqrendy = toy = by ; }
    else {
        sqrstarty = toy = by + 1 ;
        sqrendy = fromy = ay ; }
    if ( ax > bx ) {
        sqrendx = fromx = ax ;
        sqrstartx = tox = bx + 1 ; }
    else {
        sqrstartx = fromx = ax + 1 ;
        sqrendx = tox = bx ; }
    if ( fromy == toy ) {   // line is horizontal
        if ( ax < bx )
             { i = ax ; ax = bx ; bx = i ; }
        else { i = ay ; ay = by ; by = i ; } 
        j = bx + ( ( ax - bx ) / 2 ) ;
        k = j ;
        if ( ( ( ax - bx ) & 1 ) ) ++ k ; 
        for ( i = bx ; ++ i < ax ; ) { 
            if ( i <= j ) fillist [ ay ] [ i ] = 1 ; 
            if ( i >= k ) fillist [ by ] [ i ] = 1 ; } 
         return ; }
    if ( fromx == tox ) {   // line is vertical
        if ( ay < by ) { i = ay ; ay = by ; by = i ; }
        else { i = ax ; ax = bx ; bx = i ; } 
        j = by + ( ( ay - by ) / 2 ) ; 
        k = j ;
        if ( ( ( ay - by ) & 1 ) ) ++ k ; 
        for ( i = by ; ++ i < ay ; ) { 
            if ( i <= j ) fillist [ i ] [ ax ] = 1 ; 
            if ( i >= k ) fillist [ i ] [ bx ] = 1 ; } 
        return ; }
    slope = ( fromy - toy ) / ( fromx - tox ) ;
    ordalor = fromy - ( ( ( toy - fromy ) / ( tox - fromx ) ) * fromx ) ;
    i = ax - bx ;
    j = ay - by ;
    if ( i < 0 ) i = -i ;
    if ( j < 0 ) j = -j ;
    if ( i == j ) { // this is a diagonal!!!
        if ( slope > 0 ) { 
           aty = sqrstarty ;  
           for ( atx = sqrstartx ; atx < sqrendx ; ++ aty , ++ atx )
                  fillist [ aty ] [ atx ] = 1 ; }
        else {
           aty = sqrendy - 1 ;
           for ( atx = sqrstartx ; atx < sqrendx ; -- aty , ++ atx ) 
                  fillist [ aty ] [ atx ] = 1 ; }
        return ; }  
    // visit cells in square (sqrstart/sqrend), and check whether line passes there
    for ( atx = sqrstartx ; atx <= sqrendx ; ++ atx ) 
        for ( aty = sqrstarty ; aty <= sqrendy ; ++aty )
           if ( fillist [ aty ] [ atx ] == 0 && isdefd [ aty ] [ atx ] )  
               if ( line_passes_within ( aty , atx ) )
                         fillist [ aty ] [ atx ] = 1 ; 
    return ; 
}     

void large_fill_between ( int ay , int ax , int by , int bx )
{
    int i , j , k ; 
    int adds = 0 ;
    double fromy , toy , fromx, tox ;
    int sqrstartx , sqrstarty , sqrendx , sqrendy , atx , aty ; 
    if ( ax == bx ) {
        if ( ay < by ) { i = ay ; ay = by ; by = i ; }
        for ( i = by ; ++ i < ay ; ) fillist [ i ] [ ax ] = 1 ; 
        return ; } 
    if ( ay == by ) {
        if ( ax < bx ) { i = ax ; ax = bx ; bx = i ; }
        for ( i = bx ; ++ i < ax ; ) fillist [ ay ] [ i ] = 1 ; 
        return ; }
    // calculate a line from A to B
    if ( ay < by ) {
        sqrstarty = fromy = ay + 1 ;
        sqrendy = toy = by ; }
    else {
        sqrstarty = toy = by + 1 ;
        sqrendy = fromy = ay ; }
    if ( ax > bx ) {
        sqrendx = fromx = ax ;
        sqrstartx = tox = bx + 1 ; }
    else {
        sqrstartx = fromx = ax + 1 ;
        sqrendx = tox = bx ; }
    if ( fromy == toy ) {   // line is horizontal
        if ( ax < bx ) { i = ax ; ax = bx ; bx = i ; }
        for ( i = bx ; ++ i < ax ; )  
            fillist [ ay ] [ i ] = fillist [ by ] [ i ] = 1 ;  
         return ; }
    if ( fromx == tox ) {   // line is vertical
        if ( ay < by ) { i = ay ; ay = by ; by = i ; }
        for ( i = by ; ++ i < ay ; )  
            fillist [ i ] [ ax ] = fillist [ i ] [ bx ] = 1 ;  
        return ; }
    slope = ( fromy - toy ) / ( fromx - tox ) ;
    ordalor = fromy - ( ( ( toy - fromy ) / ( tox - fromx ) ) * fromx ) ;
    // visit cells in square (sqrstart/sqrend), and check whether line passes there
    for ( atx = sqrstartx ; atx <= sqrendx ; ++ atx ) 
        for ( aty = sqrstarty ; aty <= sqrendy ; ++aty )
           if ( fillist [ aty ] [ atx ] == 0 && isdefd [ aty ] [ atx ] )  
               if ( line_passes_within ( aty , atx ) )
                         fillist [ aty ] [ atx ] = 1 ; 
    return ; 
}     

void auto_fill_assumed_records ( int sp )
{
    int sc = sp / 32 ;
    int32 sb = 1 << ( sp % 32 ) ;
    int chgs = 1 , a , b , ax , ay , bx , by ;
    signed int imaxx , imaxy , iminx , iminy ;
    int inminx , inmaxx ;
    if ( fill_large )
          fill_between = large_fill_between ;
    else fill_between = small_fill_between ;
    imaxx = imaxy = -1000000 ;
    iminx = iminy = totareas ; 
    for ( a = totareas ; a -- ; ) {
        ax = a % cols ;
        ay = a / cols ;
        fillist [ ay ] [ ax ] = 0 ; 
        if ( ( matrix [ ay ] [ ax ] [ sc ] & sb ) ) {
            fillist [ ay ] [ ax ] = 2 ;
            if ( imaxx < ax ) imaxx = ax ;
            if ( iminx > ax ) iminx = ax ;
            if ( imaxy < ay ) imaxy = ay ;
            if ( iminy > ay ) iminy = ay ; }} 
    // create outer lines ... 
    for ( ay = iminy ; ay <= imaxy ; ++ ay ) 
    for ( ax = iminx ; ax <= imaxx ; ++ ax ) {
          if ( fillist [ay][ax] < 2 ) continue ;
          for ( by = ay ; by <= imaxy ; ++ by )
          for ( bx = iminx ; bx <= imaxx ; ++ bx ) {
              if ( fillist [by][bx] < 2 ) continue ;
              if ( by==ay && bx==ax ) continue ; 
              fill_between ( ay , ax , by , bx ) ; }}
    // only to expand a little more...
    if ( fill_large ) {
       for ( ay = iminy ; ay <= imaxy ; ++ ay ) 
       for ( ax = iminx ; ax <= imaxx ; ++ ax ) {
             if ( !fillist [ay][ax] ) continue ;
             for ( by = ay ; by <= imaxy ; ++ by )
             for ( bx = iminx ; bx <= imaxx ; ++ bx ) {
                 if ( by==ay && bx==ax ) continue ;
                 if ( ( by > ay + 1 || ay > by + 1 ) && 
                      ( bx > ax + 1 || ax > bx + 1 ) )
                        continue ; 
                 if ( fillist[ay][ax]+fillist[by][bx] != 3 ) continue ;
                 fill_between ( ay , ax , by , bx ) ; }}}
    // fill the voids in between (only between the new lines!)...
    for ( ay = iminy ; ay <= imaxy ; ++ ay ) {
        inminx = totareas ; 
        for ( ax = iminx ; ax <= imaxx ; ++ ax ) 
            if ( inminx > ax && fillist[ay][ax] ) {
                inminx = ax ;
                break ; }
        inmaxx = -1 ; 
        for ( ax = imaxx ; ax >= iminx ; --ax ) 
            if ( inmaxx < ax && fillist[ay][ax] ) {
                inmaxx = ax ;
                break ; }
        for ( ax = inminx ; ax <= inmaxx ; ++ ax ) fillist[ay][ax] = 1 ; }
    // here, copy fillist back to assmatrix...
    numassentries [ sp ] = 0 ; 
    for ( a = totareas ; a -- ; ) {
        ax = a % cols ;
        ay = a / cols ;
        if ( !isdefd [ ay ] [ ax ] ) continue ; 
        if ( fillist [ ay ] [ ax ] ) assmatrix [ ay ] [ ax ] [ sc ] |= sb ; 
        if ( ( assmatrix [ ay ] [ ax ] [ sc ] & sb ) ) ++ numassentries [ sp ] ; } 
    return ; 
}                       

void auto_fill_all_records ( void )
{
    int a ;
    cls () ;
    if ( !sure ( "Auto-fill records for ALL species" ) ) return ;
    a = MessageBox ( hwnd , "Fill with expanded ranges?" , "Filling type" , MB_YESNO | MB_ICONWARNING ) ; 
    fill_large = ( a == IDYES ) ;
    cls () ; 
    for ( a = 0 ; a < spp ; ++ a ) 
        auto_fill_assumed_records ( a ) ; 
    doallscores () ;
    showcurset () ;
    if ( fill_large ) captf( "\nFilled large areas..." ) ;
    else captf( "\nFilled smaller areas..." ) ; 
    return ; 
}     

void auto_auto_fills ( int type )
{
    int a ;
    fill_large = ( type == 2 ) ;
    pleasewait ( "Filling records" ) ; 
    for ( a = 0 ; a < numterminals ; ++ a ) 
        auto_fill_assumed_records ( a ) ;
    imdone () ; 
    if ( fill_large ) captf( "\nFilled large areas..." ) ;
    else captf( "\nFilled smaller areas..." ) ; 
    return ; 
}     


void set_autofills_from_file ( void )
{
    int i ; 
    fill_large = 0 ; 
    while ( !feof ( infile ) ) {
        if ( ! fscanf ( infile , " %i" , &i ) ) break ;
        if ( i >= spp ) { 
           sprintf ( junkstr , "Sorry, no species %i" , i ) ;
           errmsg ( junkstr , Null ) ;
           break ; }
        auto_fill_assumed_records ( i ) ; } 
    add_species_groups () ; 
    doallscores () ;
    return ;
}    

/********  GENERAL SUPPORT FUNCTIONS **************/

int onbits ( int32 val ) 
{ unsigned short int * x , * y ; 
  x = ( unsigned short int * ) &val ; 
  y = x + 1 ; 
  return ( numbits [ * x ] + numbits [ * y ] ) ; 
} 

int nubi , num , depth ; 

void calculin( void ) 
{ 
    if ( depth == 16 ) { numbits [ num ] = nubi ; return ; } 
    num |= ( 1 << depth ) ; 
    ++ nubi ; 
    ++ depth ; 
    calculin () ; 
    -- depth ; 
    num ^= ( 1 << depth ) ; 
    -- nubi ; 
    ++ depth ; 
    calculin () ; 
    -- depth ; 
} 


void cls ( void )
{
  atcoordx = atcoordy = 0 ; 
  return; 
}

int show_coordinates = 0 ; 

#define YYY  ( 1 | 2 | 4 ) 
#define YYN  ( 1 | 2     ) 
#define YNY  ( 1 |     4 ) 
#define YNN  ( 1         ) 
#define NYY  (     2 | 4 ) 
#define NYN  (     2     ) 
#define NNY  (         4 ) 
#define NNN  (     0     )

#define yyy  'X'
#define yyn  'X'
#define yny  'A'
#define ynn  'Û'
#define nyy  '²'
#define nyn  '²'
#define nny  'a'
#define nnn  '°'
#define SPACE ' ' 

void show_lower_grid_coordinates ( void )
{
    char txt[15] ;
    int x , at , left ;
    double atcoord ; 
    at = 0 ;
    left = 1 ; 
    while ( left ) {
      atcoord = grid_startx ;
      left = 0 ; 
      for ( x = 0 ; x <= cols ; ++ x ) {
          sprintf ( txt , "%6.3f" , atcoord ) ;
          atcoord += grid_width ;
          if ( at < strlen ( txt ) ) { 
               myprintf("%c  " , txt [ at ] ) ;
               left = 1 ; }
          else myprintf( "   " ) ; }
      ++ at ;
      myprintf( "\n" ) ; } 
}    

void showcurset ( void )
{
      char marktxt[2] ; 
      marktxt[0]=marktxt[1]='\0' ; 
      if ( recptr -> mark ) marktxt[0] ='*' ; 
      screenf("Set %i%s of %i (size=%i). Score=%f.\n" , recptr - rec , marktxt , numrecs , recptr->size , recptr->score ) ; 
      drawmap ( recptr -> lst , NULL , NULL ) ;
      if ( didaboot )
           sprintf ( screencapt , "Sample values:\n    Area %6.2f\n    Spp  %6.2f" , recptr -> bootarval , recptr -> bootspval ) ; 
      else       
      if ( !numrecs ) captf ( "NO AREAS IN MEMORY (Use \"Actions/Create a new (empty) set\" for ditto)" ) ; 
      return ;
}

int written ; 

void bsav ( int bys , int num , char * ptr ) 
{ int a = num * bys; 
  written += a ; 
  while ( a -- ) putc ( * ptr ++ , logfile ) ; 
  return ; 
} 

int logsetsonly = 0 ; 

void logtofile ( void ) 
{  
   int a , b , option = 'x' ;
   char x ;
   Artyp * arp ; 
   a = 0 ; 
   while ( isspace ( comstring [ a ] ) && comstring [ a ] ) ++ a ; 
   if ( !comstring [ a ] ) return ; 
   logfilename = comstring + a ;
   if ( query && logsetsonly ) {
      logfile = fopen ( logfilename , "rb" ) ;
      if ( logfile != NULL ) {
          fclose ( logfile ) ;
          sprintf ( junkstr , "File \"%s\" exists.\n"
                              "Do you want to append areas at the end?" , logfilename ) ;
          a = MessageBox ( hwnd , junkstr , "Warning" , MB_YESNOCANCEL | MB_ICONWARNING ) ;
          if ( a == IDCANCEL ) return ; 
          if ( a == IDYES )
               logfile = fopen ( logfilename , "ab" ) ;
          else logfile = fopen ( logfilename , "wb" ) ; }
      else logfile = fopen ( logfilename , "wb" ) ; } 
   else 
      logfile = fopen ( logfilename , "wb" ) ; 
   if ( logfile == NULL ) {
        showcurset () ;
        curcmd_loop = cmd_loop ; 
        captf("Can't open file %s" , logfilename ) ; 
        return ; }
   written = 0 ; 
   if ( !logsetsonly ) { 
      bsav ( sizeof ( int ) , 1 , ( char * ) &abslim ) ; 
      bsav ( sizeof ( int ) , 1 , ( char * ) &musthaveone ) ;
      x = use_edge_props ;
      if ( spname != NULL ) x |= 2 ; 
      bsav ( sizeof ( int ) , 1 , ( char * ) &x ) ; 
      bsav ( sizeof ( double ) , 1 , ( char * ) &iifac ) ; 
      bsav ( sizeof ( double ) , 1 , ( char * ) &iafac ) ; 
      bsav ( sizeof ( double ) , 1 , ( char * ) &oufac ) ;
      bsav ( sizeof ( double ) , 1 , ( char * ) &oafac ) ; 
      bsav ( sizeof ( double ) , 1 , ( char * ) &ononafac ) ;
      bsav ( sizeof ( double ) , 1 , ( char * ) &min_pres_perc ) ; 
      bsav ( sizeof ( int ) , 1 , ( char * ) &compare_perc ) ; 
      bsav ( sizeof ( int ) , 1 , ( char * ) &rows ) ; 
      bsav ( sizeof ( int ) , 1 , ( char * ) &cols ) ; 
      bsav ( sizeof ( int ) , 1 , ( char * ) &spp ) ;
      if ( spname != NULL ) 
          for ( a = 0 ; a < spp ; ++ a ) 
              if ( spname[a] == NULL ) {
                  sprintf ( junkstr , "Sp. %i" , a ) ;
                  bsav ( sizeof ( char ) , Spnamesz , junkstr ) ; }
              else 
                  bsav ( sizeof ( char ) , Spnamesz , spname[a] ) ; 
      bsav ( sizeof ( double ) , 1 , ( char * ) &grid_starty ) ;
      bsav ( sizeof ( double ) , 1 , ( char * ) &grid_startx ) ;
      bsav ( sizeof ( double ) , 1 , ( char * ) &grid_height ) ;
      bsav ( sizeof ( double ) , 1 , ( char * ) &grid_width ) ;
      bsav ( sizeof ( int ) , spp , ( char * ) numentries ) ;
      bsav ( sizeof ( int ) , spp , ( char * ) numassentries ) ;
      for ( a = rows ; a -- ; ) bsav ( sizeof ( char ) , cols , ( char * ) isdefd [ a ] ) ; 
      for ( a = rows ; a -- ; )  
           for ( b = cols ; b -- ; )  
                if ( isdefd [ a ] [ b ] ) { 
                       bsav ( sizeof ( int32 ) , spcells , ( char * ) matrix [ a ] [ b ] ) ;
                       bsav ( sizeof ( int32 ) , spcells , ( char * ) assmatrix [ a ] [ b ] ) ; } 
      a = numrecs ; 
      bsav ( sizeof ( int ) , 1 , ( char * ) &a ) ; }
   arp = rec ; 
   for ( a = 0 ; a < numrecs ; ++ a , ++ arp ) { 
           bsav ( sizeof ( int32 ) , arcells , ( char * ) arp -> lst ) ; 
           bsav ( sizeof ( double ) , 1 , ( char * ) &( arp -> score ) ) ; 
           bsav ( sizeof ( int ) , 1 , ( char * ) &( arp -> size ) ) ; } 
   fclose ( logfile ) ; 
   showcurset () ; 
   captf("Results saved to file %s (%i bytes)", logfilename , written ) ; 
   return ; 
} 

void close_outputfile ( void )
{
    if ( outspace == NULL ) return ;
    fclose ( outspace ) ;
    outspace = NULL ;
    return ; 
}

void outputfile ( void ) 
{ 
   int a , b ; 
   char * outfilename ; 
   a = 0 ; 
   while ( isspace ( comstring [ a ] ) && comstring [ a ] ) ++ a ; 
   if ( !comstring [ a ] ) return ; 
   if ( outspace != NULL ) fclose ( output ) ; 
   outfilename = comstring + a ; 
   outspace = fopen ( outfilename , "wb" ) ; 
   if ( grid_created ) showcurset () ; 
   if ( outspace == NULL )  
        captf ("Can't open file %s" , outfilename ) ; 
   else captf("Opened file %s for output", outfilename ) ;
   numcoordstofile = 0 ; 
   return ; 
} 

void saveallsets ( void ) 
{  Artyp * old = recptr ; 
   recptr = rec ; 
   output = outspace ; 
   while ( ( recptr - rec ) < numrecs ) { 
        screenf("Set %i of %i (size=%i). Score=%f.\n" , 
                  recptr - rec , numrecs , recptr->size , recptr->score ) ; 
        drawmap ( recptr -> lst , NULL , NULL ) ;
        ++ recptr ; } 
   output = stdout ; 
   recptr = old ;
   showcurset () ; 
   captf ("Saved %i sets to file" , numrecs ) ; 
   return ; 
}

void savedata ( void ) 
{  int a , b , c , mc , numar ;
   int lim ;
   int * afare , * fato , n , m , j , k ; 
   int32 mb ;
   int trunspp ;
   if ( ysign  > 0 ) fprintf ( outspace , "ynegative\n" ) ;
   if ( xsign < 0 ) fprintf ( outspace , "xnegative\n" ) ;
   if ( dolatlong == 0 ) fprintf ( outspace , "longlat\n" ) ;
   if ( grid_startx < 10e200 ) { 
        fprintf ( outspace , "gridx %.8f %.8f\ngridy %.8f %.8f\n" ,
                 grid_startx , grid_width , grid_starty * ysign , grid_height ) ; }
   trunspp = 0 ;
   for ( a = 0 ; a < spp ; ++ a )
       if ( ( spact[a/32] & ( 1 << ( a % 32 ) ) ) ) ++ trunspp ;

   if ( species_tree == NULL )     
       fprintf(outspace , "rows %i\ncols %i\nspp %i\ndata" , rows , cols , trunspp ) ;
   else {
//       if ( trunspp != spp ) ermsg ( "OOOPS!!!... when using higher groups, shouldn't deactivate species!!!" ) ;
       fprintf(outspace , "rows %i\ncols %i\nspp %i\ndata" , rows , cols , spp ) ; }
   for ( a = 0 ; a < rows ; ++ a ) { 
      for ( b = 0 ; b < cols ; ++ b ) { 
         if ( !isdefd [ a ] [ b ] ) continue ; 
         fprintf(outspace,"\nA%i-%i\n" , a , b ) ;
         lim = spp ;
         if ( species_tree != NULL ) lim = numterminals ; 
         for ( c = 0 ; c < lim ; ++ c ) { 
             mb = 1 << ( c % 32 ) ; 
             mc = c / 32 ;
             if ( !( spact[mc] & mb ) ) {
                 if ( species_tree != NULL ) putc ( '0' , outspace ) ;
                 continue ; }
             if ( ( matrix [ a ] [ b ] [ mc ] & mb ) ) putc ( '1' , outspace ) ; 
             else
                 if ( ( assmatrix [ a ] [ b ] [ mc ] & mb ) ) putc ( '2' , outspace ) ; 
                 else putc ( '0' , outspace ) ; }}}
   fprintf(outspace , "\n;\n" ) ;

   if ( species_tree != NULL ) {
       fprintf ( outspace , "groups\n" ) ;
       for ( m = numterminals + 1 ; m < species_tree[ treeroot ] ; ++ m ) {
          fprintf ( outspace , "{ " ) ; 
          for ( k = 0 ; k < numterminals ; ++ k ) { 
             j = species_tree [ k ] ;
             while ( j != treeroot && j != m ) j = species_tree [ j ] ;
             if ( j == treeroot ) continue ;
             fprintf ( outspace , "%i " , k ) ; }
          fprintf ( outspace , " }\n" ) ; } 

      fprintf ( outspace , ";\n" ) ; }
   if ( weight_species ) {
       fprintf ( outspace , "spwts\n" ) ;
       for ( j = 0 ; j < spp ; ++ j ) {
           if ( !( spact [ j/32] & ( 1 << ( j % 32 ) ) ) ) continue ;
           fprintf ( outspace , "   %.20f\n" , species_weight[ j ] ) ; }
       fprintf ( outspace , ";\n" ) ; }
   showcurset () ; 
   captf("Saved data to file" ) ; 
   return ; 
} 

void savetofile ( void ) 
{ 
  int a , x ; 
   a = 0 ; 
   while ( isspace ( comstring [ a ] ) && comstring [ a ] ) ++ a ; 
   x = comstring [ a ] ; 
        if ( x == 0 ) saveallsets () ; 
   else if ( x == 'd' ) savedata () ;
   else if ( x == '@' ) save_for_framed_search ( ) ;
   else {
       sprintf ( junkstr , "Wrong option for saving: %c" , x ) ;
       errmsg ( junkstr , Null ) ; }
   return ; 
} 

void dohlp ( int pausit ) 
{  int a ;
   cls () ;

if ( !grid_created ) 
   myprintf ( "\
V-NDM 3.1 (viewer of results for NDM 3.1, by P. A. Goloboff, 2001-2016)\n\
 \n\
Select File/CreateMatrix to create a matrix from data points\n\
 \n\
Keys: \n\
   arrow keys      make cells smaller/bigger\n\
   ctrl + arrow    shift grid (no changes in cell size)\n\
   pg up/dn        enlarge display \n\
   +/-             enlarge display (only a little)\n\
   x/y             make cells narrower/shorter (only a little)\n\
   shift + x/y     make cells wider/higher (only a little)\n\
   ctrl x         quit!\n\
If map countour coordinates present:\n\
       F5           save map contour coordinates to file\n\
       left-clk     select point/segment\n\
       right-clk    move/add point\n\
       tab          select next point/segment\n\
       back         deselect last point/segment\n\
       arrow keys   if point/segment selected, move\n\
        + -         change point/segment selection\n\
       double click set target for auto-edit\n\
       enter        if autoedit is on, add point at target\n\
       esc/click    exit autoedit mode\n\
       home/end     if point/segment selected, move to first/last\n\
       space        cycle point/segment selection\n\
       del          delete point (if selected)\n \n \n [ hit ENTER or left-click to continue ]" ) ; 
else
if ( curcmd_loop == show_duwc ) {
   if ( is_cons_duwc ) 
   myprintf ( "\
   Viewing relationships between consensus areas:\n\
   \n\
   enter       go to next consensus\n\
   back        go to previous consensus\n\
   v           toggle list of species/areas\n\
               page UP/DN move between sets of\n\
               species endemic for one or the\n\
               other set, or both\n\
   ESC         quit consensus mode (back to area-viewing mode)\n \n \n [ hit ENTER or left-click to continue ]" ) ;
   else
   myprintf ( "\
   Viewing relationships between areas:\n\
   \n\
   enter       go to next area\n\
   back        go to previous area\n\
   v           toggle list of species/areas\n\
               page UP/DN move between sets of\n\
               species endemic for one or the\n\
               other set, or both\n\
   ESC         quit consensus mode (back to area-viewing mode)\n \n \n [ hit ENTER or left-click to continue ]" ) ; }
else if ( curcmd_loop == show_consensus )
   myprintf ( "\
   Viewing consensus areas:\n\
   \n\
    x       toggle min-max values\n\
    v       toggle list of species/areas\n\
            page UP/DN moves between species\n\
   ctl-m    mark all areas in current consensus\n\
   ctl-n    create a new area, piling up all areas\n\
            in current consensus\n\
   ctl-j    compare to specified consensus\n\
    u       un-mark all areas in current consensus\n\
    g       go to a consensus set\n\
   ESC      quit consensus mode (back to area-viewing mode)\n \n \n [ hit ENTER or left-click to continue ]" ) ;
else
if ( curcmd_loop == showspecies ) 
    myprintf ( "\
    Viewing species distributions:\n\
    \n\
    ctl-M       mark all sets to which this species gives score\n\
    g           go to a specified species\n\
    ctl-A       auto-fill assumed records for this species\n\
    ctl-S       create a new set from (=identical to) this species\n\
    w           toggle viewing of species included in groups (only\n\
                if groups defined, and current species is a group)\n\
    ESC         back to area-viewing mode\n \n \n [ hit ENTER or left-click to continue ]" ) ; 
else 
myprintf("\
     V-NDM 3.1 (viewer of results for NDM 3.1, by P. A. Goloboff, 2001-2011)\n\
  \n\
    ctl-x      quit                           ctl-l       save results to log file   \n\
    ctl-s      species maps                    l          save data and results      \n\
    ctl-a      auto-fill species records       o xxx      open outfile xxx            \n\
    ctl-n      new set                         v [-]      show [non]scoring spp.      \n\
    ctl-i      invert marks                   ctl-q y/n   query                       \n\
    ctl-v      view marked sets                h y/n      require full cell around    \n\
    ctl-del    delete set                      p y/n      use edge proportions        \n\
    ctl-d      show disjunct sets              m=S>N      mark if size > N.  Instead of =,\n\
    ctl-c      show contradictory sets                    use + or - to add or remove marks;\n\
    ctl-w      show included sets                         instead of S, use m (number of \n\
    ctl-u      show including sets                        scoring spp), v (score), c d w \n\
    ctl-9      show similar sets                          or u (relative to current set)\n\
    ctl-j      compare to set (* marked)      ctl-e       empty current set\n\
    ctl-h      help (this screen!)                        to current set); instead of >,\n\
    ctl-k      delete widespread spp                      use = or < \n\
    shf-m      save to metafile                m /        deletes all marked sets     \n\
     F12       synonym of shf-m                m ?        report number of marked sets\n\
    ctl-r      read sets from file             a N        random sp. data (p(pres)=N) \n\
    ctl-1      show areas w/unique spp         n          show cells with no records  \n\
    ctl-g      show grid coordinates           /N         shrink data (divide by N)   \n\
     z         show identical sets             f[iaodn]   set factor (i,a,o,d, or n)  \n\
    ctl-m      toggle mark of curset           d          discard duplicate areas     \n\
    ctl-p      set compare percentage          -          purify set of records       \n\
     F9        show copyright notice          ctrl-f      show species in sets: S/A, \n\
     g N       go to set N                                where S proportion of species\n\
     b N       set minimum sp score to N                  cells within area; A proportion\n\
     w N       weight species with K=N                    of area occupied by the species\n\
               (not: -)                                   (if negative, less than, instead\n\
     e N       max. empty cells around                    of greater than)\n\
 \n \n \n [ hit ENTER or left-click to continue ]") ;
  return ; 
} 

void copyar ( int a , int b ) 
{ 
  Artyp * sa , * sb ; 
  int32 * ipa , * ipb ; 
  int x , y ; 
  sa = rec + a ; 
  sb = rec + b ; 
  ipa = sa -> lst ; 
  ipb = sb -> lst ; 
  for ( x = arcells ; x -- ; ) * ipa ++ = * ipb ++ ; 
  ipa = sa -> splist ; 
  ipb = sb -> splist ; 
  for ( x = spcells ; x -- ; ) * ipa ++ = * ipb ++ ;
  sa -> bootarval = sb -> bootarval ; 
  sa -> bootspval = sb -> bootspval ; 
  sa -> fromrepl = sb -> fromrepl ; 
  sa -> size = sb -> size ; 
  sa -> score = sb -> score ; 
  sa -> mark = sb -> mark ;
  sa -> erase = sb -> erase ;
  sa -> numspp = sb -> numspp ; 
  return ; 
} 

/*****************  SCORE (RE-)CALCULATION ********************/
/*      Scores are passed onto VNDM  in the data file,        */
/*      but need recalculation when parms. are changed        */

int iscontig ( int j ) 
{   int32 mb , mc ; 
    int a , b , numar , x , y ; 
    int empties = 0 ; 
    x = j % cols ; 
    y = j / cols ;
    if ( !isdefd[y][x] ) return -1 ; 
    for ( a = x - 1 ; a <= x + 1 ; ++ a ) { 
         if ( a < 0 || a >= cols ) continue ; 
         for ( b = y - 1 ; b <= y + 1 ; ++ b ) { 
             if ( b < 0 || b >= rows ) continue ; 
             if ( b == y && a == x ) continue ; 
             numar = ( cols * b ) + a ; 
             mb = 1 << ( numar % 32 ) ; 
             mc = numar / 32 ; 
             if ( ( lst[mc] & mb ) != 0 ) return 1 ; }} 
    return 0 ; 
} 

void prepare_lists ( void )
{
    int32 mb ;
    int i , mc , wht ;
    int myc , myr ; 
    listinpt = listin ;
    listadjapt = listadja ; 
    listnonadjapt = listnonadja ;
    arminc = arminr = 32767 ;
    armaxc = armaxr = 0 ; 
    for ( i = 0 ; i < totareas ; ++ i ) {
        myc = i % cols ;
        myr = i / cols ; 
        mc = i / 32 ;
        mb = 1 << ( i % 32 ) ;
        if ( ( lst [ mc ] & mb ) ) {
            if ( myc > armaxc ) armaxc = myc ; 
            if ( myc < arminc ) arminc = myc ; 
            if ( myr > armaxr ) armaxr = myr ; 
            if ( myr < arminr ) arminr = myr ; 
            * listinpt ++ = i ; } 
        else {
            wht = iscontig ( i ) ;
            if ( wht < 0 ) continue ; 
            if ( wht ) * listadjapt ++ = i ;
            else * listnonadjapt ++ = i ; }}
    if ( arminc ) arminc -- ;
    if ( arminr ) arminr -- ;
    armaxc ++ ; 
    armaxr ++ ; 
    return ; 
}     

double dorule5 ( void )
{
    int a , b , x , isexo , scoring_spp = 0 ;
    int * lp ;
    int inf , ass , out , pres , outadja, outnonadja ;
    int32 mb , sb ;
    int32 * areapt ; 
    int mc , sc , j , k , numar , jj , kk , snumar , skipit , havesome , numemps ;
    double myscore = 0 , dsize ;
    double Eval ;
    int * fare , * fato ;
    MinMaxtyp * mmpt ;
    cursize = recptr -> size ;
    if ( cursize == 0 ) return 0 ;
    if ( ignore_sp_lists ) return recptr -> score ; 
    areapt = lst = recptr -> lst ;
    prepare_lists ( ) ;
    Eval = ( double ) ( listadjapt - listadja ) ; 
    mb = 1 ;
    mc = 0 ;
    for ( a = spcells ; a -- ; ) intersptr [ a ] = 0 ; 
    if ( cursize == 0 ) return 0 ;
    mmpt = spminmax ;
    for ( a = 0 ; a < spp ; ++ a , ++ mmpt ) {
        spscore [ a ] = 0 ; 
        mc = a / 32 ;
        if ( !( spact[mc] & mb ) ) {
            if ( mb == ( 1 << 31 ) ) { 
                 mb = 1 ; ++ mc ; }
            else mb <<= 1 ;
            continue ; }
        if ( ( mmpt -> minc < arminc ) || ( mmpt -> maxc > armaxc ) ||
             ( mmpt -> minr < arminr ) || ( mmpt -> maxr > armaxr ) ) { 
                if ( mb == ( 1 << 31 ) ) { 
                     mb = 1 ; ++ mc ; }
                else mb <<= 1 ;
                continue ; }
        if ( ( mmpt -> maxc < arminc ) || ( mmpt -> minc > armaxc ) ||
             ( mmpt -> maxr < arminr ) || ( mmpt -> minr > armaxr ) ) { 
                if ( mb == ( 1 << 31 ) ) { 
                     mb = 1 ; ++ mc ; }
                else mb <<= 1 ;
                continue ; }
        /***    Is species also found outside?   ********/
        isexo = outnonadja = 0 ; 
        for ( lp = listnonadja ; lp < listnonadjapt && !isexo ; ++ lp ) {
               numar = * lp ;
               j = numar % cols ;
               k = numar / cols ; 
               if ( ( matrix [ k ] [ j ] [ mc ] & mb ) ) isexo = 1 ;
               if ( ( assmatrix [ k ] [ j ] [ mc ] & mb ) ) ++ outnonadja ; } 
        if ( isexo ) {             
            if ( mb == ( 1 << 31 ) ) { 
                          mb = 1 ; ++ mc ; }
            else mb <<= 1 ;
            continue ; }
        /****   Count presences/absences/etc. *************/
        pres = ass = inf = out = outadja = 0 ;
        skipit = 0 ; 
        for ( lp = listin ; lp < listinpt && !skipit ; ++ lp ) {
                 numar = * lp ;
                 j = numar % cols ;
                 k = numar / cols ; 
                 if ( ( matrix [ k ] [ j ] [ mc ] & mb ) ) {
                         ++ pres ; 
                         continue ; }
                 havesome = 0 ;
                 if ( !musthaveone ) havesome = 1 ; 
                 numemps = 0 ; 
                 for ( jj = j - 1 ; jj <= j + 1 ; ++ jj ) {
                     if ( jj < 0 || jj >= cols ) continue ; 
                     for ( kk = k - 1 ; kk <= k + 1 ; ++ kk ) { 
                         if ( kk < 0 || kk >= rows ) continue ;
                         snumar = ( cols * kk ) + jj ;
                         if ( snumar == numar ) continue ; 
                         sb = 1 << ( snumar % 32 ) ;
                         sc = snumar / 32 ;
                         if ( ( areapt [ sc ] & sb ) == 0 ) continue ;  
                         if ( ( matrix [ kk ] [ jj ] [ mc ] & mb ) ) havesome = 1 ;
                         else 
                             if ( ++ numemps > abslim ) { jj = j + 1 ; break ; }}}
                if ( havesome && numemps <= abslim &&
                      ( iifac > iafac || ( assmatrix [ k ] [ j ] [ mc ] & mb ) == 0 ) )
                      ++ inf ;
                else { if ( ( assmatrix [ k ] [ j ] [ mc ] & mb ) == 0 ) skipit = 1 ;
                       else if ( musthaveone == 2 && !havesome ) skipit = 1 ; 
                        ++ ass ; }}
        if ( skipit || 
             ( pres * 100 ) / cursize < min_pres_perc || 
             ( min_pres_perc && pres < 2 && cursize > 1 ) ) {
                      if ( mb == ( 1 << 31 ) ) {
                                  mb = 1 ; ++ mc ; }
                      else mb <<= 1 ; 
                      continue ; } 
        for ( lp = listadja ; lp < listadjapt ; ++ lp ) {
                 numar = * lp ;
                 j = numar % cols ;
                 k = numar / cols ;
                 if ( ( matrix [ k ] [ j ] [ mc ] & mb ) ) ++ out ;
                 else if ( ( assmatrix [ k ] [ j ] [ mc ] & mb ) ) ++ outadja ; }
         /**** Calculating score ********/
         dout [ a ] = out ;
         dass [ a ] = ass ;
         dinf [ a ] = inf ;
         dpres [ a ] = pres ;
         dadja [ a ] = outadja ; 
         dnadja [ a ] = outnonadja ;  
         dsize = cursize ;

         if ( !use_edge_props ) 
           spscore [ a ] =
                   ( dpres [ a ] +
                     ( iifac * dinf [ a ] ) +
                     ( iafac * dass [ a ] )  )
                          /
                   ( dsize +
                     ( ( 1 / oufac ) * dout [ a ] ) + 
                     ( ( 1 / oafac ) * dadja [ a ] ) +
                     ( ( 1 / ononafac ) * dnadja [ a ] ) ) ;

         else {
           spscore [a] =
              ( ( dpres [a] +
                ( iifac * dinf [a]) +
                ( iafac * dass [a])  ) * 
                ( 1 -
                  ( ( ( dout[a] / oufac ) + ( dadja[a] / oafac ) ) / Eval ) ) ) 
                                 /
              ( dsize + ( ( 1 / ononafac ) * dnadja [a]) ) ;
           if ( spscore[a] < 0 ) spscore[a] = 0 ; }

           if ( spscore[a] < minimum_sp_score ) spscore[a] = 0 ;
           else {
              intersptr [ mc ] |= mb ;
              if ( !weight_species ) myscore += spscore [ a ] ;
              else myscore += spscore [ a ] * species_weight [ a ] ; }
         if ( mb == ( 1 << 31 ) ) {
                          mb = 1 ; ++ mc ; }
         else mb <<= 1 ;

        }

    /***  If Higher Groups defined, eliminate redundant values ***********/
    if ( species_tree != NULL ) {
        myscore = 0 ;
        for ( a = number_of_groups - 1 ; a > 0 ; a -- ) {
            j = treelist [ a ] - 1 ;
            * ( fare = fato = innerlist ) = j + 1 ;
            if ( spscore [ j ] == 0 ) continue ; 
            ++ fare ;
            Eval = 0 ;
            while ( fato < fare ) {
                if ( ( b = * fato ++ ) >= numterminals )
                  if ( ( b == j + 1 ) || ( spscore [ b - 1 ] == 0 ) )
                     for ( x = treefirs [ b ]  ; x >= 0 ; x = treesis [ x ] ) * fare ++ = x ; 
                if ( !weight_species ) 
                    if ( b < numterminals ) 
                         Eval += spscore [ b ] ;
                    else if ( b != j + 1 ) Eval += spscore [ b - 1 ] ;
                else 
                    if ( b < numterminals ) 
                         Eval += spscore [ b ] * species_weight [ b ] ;
                    else if ( b != j + 1 ) Eval += spscore [ b - 1 ] * species_weight [ b - 1 ] ; }
            if ( spscore [ j ] <= Eval ) spscore [ j ] = 0 ; 
            else {
                * ( fare = fato = innerlist ) = j + 1 ;
                ++ fare ;
                while ( fato < fare ) {
                    if ( ( b = * fato ++ ) >= numterminals )
                         for ( x = treefirs [ b ]  ; x >= 0 ; x = treesis [ x ] ) * fare ++ = x ;
                    if ( b < numterminals ) spscore [ b ] = 0 ;  
                    else if ( b != j + 1 ) spscore [ b - 1 ] = 0 ; }}}
         for ( a = 0 ; a < spp ; ++ a ) {
              if ( spscore [ a ] == 0 ) 
                  intersptr [ a / 32 ] &= ~ ( 1 << ( a % 32 ) ) ;
              else scoring_spp ++ ; 
              if ( !weight_species ) 
                   myscore += spscore [ a ] ; 
              else myscore += spscore [ a ] * species_weight [ a ] ; }}

    if ( initializing ) {
        Eval = recptr -> score - myscore ;
        if ( Eval < 0 ) Eval = -Eval ;
        if ( Eval < 0.000001 && weight_species ) Eval = 0 ; 
        if ( Eval > 0.000000000001 ) {
          if ( !warned_yet && 
               !sure ("The score for some areas differs from the one stored in the file   \n\nThis may indicate a mismatch between area- and data-files,   \nor a change in the parameters used to calculate scores   \n\nContinue anyway" ) ) 
                 { user_wants_a_break = 1 ; return 0 ; }
        warned_yet = 1 ; }}
    recptr -> score = myscore ;
    for ( a = spcells ; a -- ; ) recptr->splist[a] = intersptr [ a ] ;
    recptr -> numspp = scoring_spp ; 
    return myscore ;
} 


/****************  This is only to clean and purify sets ************/

int one_vs_other ( Artyp * nu , Artyp * ara )
{
    int nuisbest = 0 , araisbest = 0 ;
    int a ;
    int nunotra , ranotnu , nura ; 
    int32 x , * ptnu , * ptra ; 
    if ( ara -> score < ( nu -> score + suboptimal ) ) nuisbest = 1 ; 
    if ( nu -> score < ( ara -> score + suboptimal ) ) araisbest = 1 ;
    nunotra = ranotnu = nura = 0 ; 
    if ( nuisbest || araisbest ) {
        ptnu = nu->splist - 1 ;
        ptra = ara->splist - 1 ; 
        for ( a = spcells ; a -- ; ) {
            ++ ptnu ;
            ++ ptra ;
            nunotra += onbits ( ( * ptnu & ~ * ptra ) ) ;
            ranotnu += onbits ( ( * ptra & ~ * ptnu ) ) ;
            nura += onbits ( ( * ptra & * ptnu ) ) ; }}
    if ( nuisbest && ( ( ranotnu * 100 ) / ( ranotnu + nura ) ) <= compare_perc ) return 1 ;
    if ( araisbest && ( ( nunotra * 100 ) / ( nunotra + nura ) ) <= compare_perc ) return -1 ;  
    return 0 ;
} 

void delete_marks ( int val )
{
   Artyp * ara , * arf ;
   int fly ;
   int x, y ; 
   ara = rec - 1 ;
   recptr = rec + numrecs ; 
   while ( ++ ara < recptr )
               if ( ara -> erase == val ) ara -> erase = 1 ;
               else ara -> erase = 0 ; 
   fly = 0 ;
   ara = rec - 1 ; 
   while ( ++ ara < recptr )  
      if ( ara -> erase ) { 
            if ( ara -> erase == 1 ) fly ++ ;  
            arf = ara + 1 ; 
            while ( arf -> erase && arf < recptr ) ++ arf ; 
            if ( arf < recptr ) {
                   x = ara - rec ;
                   y = arf - rec ;
                   copyar ( x , y ) ; 
                   arf -> erase = 2 ; }}
   recptr -= fly ;
   numrecs = recptr - rec ;
   return ; 
}

void chk_superfluous ( Artyp * arsmall , Artyp * arbig )
{
    int a ;
    int binotsm , smnotbi , biandsm ; 
    int32 x , * ptsmall , * ptbig ;
    ptsmall = arsmall->splist - 1 ;
    ptbig = arbig->splist - 1 ;
    binotsm = smnotbi = biandsm = 0 ; 
    for ( a = spcells ; a -- ; ) {
        ++ ptsmall ;
        ++ ptbig ;
        biandsm += onbits ( * ptsmall & * ptbig ) ;
        binotsm += onbits ( * ptbig & ~ * ptsmall ) ;
        smnotbi += onbits ( * ptsmall & ~ * ptbig ) ; }
    if ( arsmall->score >= ( arbig->score + suboptimal ) && 
       ( ( binotsm * 100 ) / ( binotsm + biandsm ) ) <= compare_perc )
         arbig->erase = 1 ; 
    if ( arbig->score >= ( arsmall->score + suboptimal ) && smnotbi == 0 )
         arsmall->erase = 1 ;
    return ; 
}         

int iscontra ( Artyp * ara , Artyp * arb ) 
{  int32 * ca , * cb ; 
   int disj , anonb , bnona ; 
   int j ; 
   ca = ara->lst ; 
   cb = arb->lst ; 
   disj = 1 ; 
   anonb = bnona = 0 ; 
   for ( j = arcells ; j -- ; ) { 
       if ( * ca & * cb ) disj = 0 ; 
       if ( * ca & ~ * cb ) anonb = 1 ; 
       if ( * cb & ~ * ca ) bnona = 1 ; 
       if ( !disj && anonb && bnona ) break ; 
       ++ ca ; ++ cb ; } 
   if ( !disj && anonb && bnona ) return 1 ; 
   return 0 ; 
} 

int isduparea ( Artyp * nu )
{
    Artyp * ol ;
    int a , isid ;
    int32 * ap , * bp ; 
    ol = nu ;
    while ( ++ ol < recptr ) {
        ap = nu -> lst ;
        bp = ol -> lst ;
        isid = 1 ; 
        for ( a = arcells ; a -- ; )
             if ( * ap ++ != * bp ++ ) isid = 0 ;
        if ( isid ) return 1 ; }
    return 0 ;
}

void delete_duplicates ( int speak )
{
    Artyp * ar ;
    int had = numrecs ; 
    recptr = rec + numrecs ;
    for ( ar = rec ; ar < recptr ; ++ ar ) ar ->erase = 0 ; 
    for ( ar = rec ; ar < recptr ; ++ ar ) 
        if ( !ar-> erase && isduparea ( ar ) ) {
                    ar -> erase = 1 ;  } 
    delete_marks ( 1 ) ;
    recptr = rec ; 
    if ( speak ) {
        showcurset () ; 
        captf( "%i sets retained (%i duplicate sets discarded)" , numrecs , had - numrecs ) ; } 
    return ; 
}     

void doallscores ( void ) 
{ Artyp * old = recptr ;
  int prv = -1 , cur , done = 0 ;   
  if ( numrecs == 0 ) return ; 
  recptr = rec + numrecs ;
  pleasewait ( "Re-calculating all scores..." ) ; 
  while ( recptr -- > rec ) {
        cur = ( done ++ * 100 ) / numrecs ;
        if ( cur != prv ) prv = cur ;  
        if ( recptr -> size == 0 ) recptr->score = recptr->numspp = 0 ; 
        else dorule5 () ; } 
  imdone () ; 
  recptr = old ;
  redoallscores = 0 ; 
  return ; 
} 

void clean_areas ( void )
{
  Artyp * ara , * nu , * arf ;
  Artyp * mxrec = rec + numrecs ; 
  int keepit = 0 , a ;  
  int dumpit , had ; 
  int atstep = 1 ; 
  cls () ; 
  had = numrecs ;
  delete_duplicates ( 0 ) ; 
  doallscores () ;
  pleasewait ( "Cleaning areas..." ) ; 
  recptr = rec ;  
  while ( mxrec != recptr ) {
     recptr = mxrec = rec + numrecs ;
     atstep ++ ;
     for ( nu = rec ; nu < recptr ; ++ nu ) nu -> erase = 0 ;
     for ( nu = rec ; nu < recptr ; ++ nu ) { 
         ara = nu ; 
         while ( ++ ara < recptr ) {
           if ( ara -> erase && nu -> erase ) continue ; 
           if ( iscontra ( ara , nu ) ) {
             dumpit = one_vs_other ( nu , ara ) ;
             if ( dumpit == 1 ) ara -> erase = 1 ;
             if ( dumpit == -1 ) nu -> erase = 1 ; }}}
     for ( nu = rec ; nu < recptr ; ++ nu ) { 
         ara = nu ; 
         while ( ++ ara < recptr ) {
             if ( !ara -> erase && !nu -> erase ) continue ;
             if ( ara -> erase && nu -> erase ) continue ; 
             if ( iscontra ( ara , nu ) ) {
                 dumpit = one_vs_other ( nu , ara ) ;
                 if ( dumpit == 1 ) ara -> erase = 2 ;
                 if ( dumpit == -1 ) nu -> erase = 2 ; }}}
      delete_marks ( 2 ) ;  
      recptr = rec + numrecs ;  
      /****  Get rid of superfluous sets ***/
      for ( nu = rec ; nu < recptr ; ++ nu ) nu -> erase = 0 ;
      for ( nu = rec ; nu < recptr ; ++ nu ) { 
         ara = nu ; 
         while ( ++ ara < recptr ) {
            if ( ara -> erase || nu -> erase ) continue ; 
            a = oneintwo ( ara , nu ) ;
            if ( a == 1 ) // i.e. ara is inside nu
                chk_superfluous ( ara , nu ) ;  
            if ( a == -1 ) //i.e. nu is inside ara
                chk_superfluous ( nu , ara ) ; }}
      delete_marks ( 1 ) ;
      recptr = rec + numrecs ; } 
   recptr = rec ;
   imdone () ; 
   showcurset () ; 
   captf( "%i best sets retained (%i discarded)        " , numrecs , had - numrecs ) ; 
   return ; 
}

void fill_widefilter ( void )
{
    int a , c , x , y , j , k , sc ;
    int32 sb ;
    int empys , countit , atleastone ;
    int norids = 1 ;
    if ( !sure ( "Eliminate widespread species" ) ) return ; 
    for ( a = spcells ; a -- ; ) widefilter [ a ] = ~0 ;
    sc = 0 ;
    sb = 1 ;
    cls () ; 
    for ( a = 0 ; a < spp ; ++ a ) {
        countit = 1 ; 
        for ( y = 0 ; y < rows ; ++ y )
           for ( x = 0 ; x < cols ; ++ x ) {
               if ( !isdefd [y][x] ) continue ;
               atleastone = 0 ;
               empys = 0 ;
               for ( j = y -1 ; j <= y + 1 ; ++ j ) {
                    if ( j < 0 || j >= rows ) continue ; 
                    for ( k = x -1 ; k <= x + 1 ; ++ k ) {
                        if ( k < 0 || k >= cols ) continue ;
                        if ( j == y && k == x ) continue ;
                        if ( !isdefd [j][k] ) continue ;
                        if ( ( matrix [j][k][sc] & sb ) == 0 ) ++ empys ;
                        else atleastone = 1 ; }}
              if ( musthaveone && !atleastone ) { countit = 0 ; break ; }
              if ( empys > abslim ) { countit = 0 ; break ; }}
         if ( countit ) {
             norids = 0 ; 
             myprintf("Species %i - not counted (widespread)" , a ) ; 
             widefilter [ sc ] ^= sb ; }
         if ( sb == BIT32 ) { ++ sc ; sb = 1 ; }
         else sb <<= 1 ; }
   if ( norids ) {
       myprintf(" \nNo species is widespread, according to current parameters" ) ;
       return ; }
   for ( y = 0 ; y < rows ; ++ y )
      for ( x = 0 ; x < cols ; ++ x ) 
          if ( isdefd [ y ][ x ] ) 
             for ( c = 0 ; c < spcells ; ++ c )
                matrix [ y ][ x ][ c ] &= widefilter [ c ] ;
   return ;
}

void dobyebye ( void ) 
{ 
    save_color_codes () ; 
    PostQuitMessage ( 0 ) ; 
    exit ( 1 ) ; 
} 

int sure ( char * msg ) 
{  int x ;
   if ( !query ) return 1 ;
   sprintf ( junkstr , "%s?" , msg ) ; 
   x = MessageBox ( hwnd , junkstr , "Please confirm ... " , MB_YESNO | MB_ICONWARNING ) ; 
   if ( x == IDNO ) return 0 ; 
   return 1 ; 
} 

void donewset ( void ) 
{  int32 * lp ; 
   int a ; 
   if ( numrecs == maxrecs ) { 
         captf("Can't do any more new areas!" ) ; 
         return ; } 
   recptr = rec + numrecs ; 
   ++ numrecs ; 
   recptr -> score = 0 ; 
   recptr -> size = 0 ; 
   recptr -> mark = 0 ; 
   lp = recptr -> lst ; 
   for ( a = arcells ; a -- ; ) * lp ++ = 0 ; 
   lp = recptr -> splist ; 
   for ( a = spcells ; a -- ; ) * lp ++ = 0 ; 
   return ; 
} 

void deleteset ( void ) 
{   int a ;
    sprintf ( comstring , "Sure you want to delete set %i" , recptr - rec ) ; 
    if ( !sure ( comstring ) ) return ; 
    if ( numrecs == 1 ) {
         numrecs = 0 ; 
         donewset () ;
         return ; } 
    for ( a = recptr - rec ; ++ a < numrecs ; ) 
         copyar ( a - 1 , a ) ;
    -- numrecs ;
    if ( recptr - rec >= numrecs ) -- recptr ; 
    return ; 
} 

void handle_querymode ( void )
{
    char * at = comstring ;
    while ( isspace ( * at ) && * at ) ++ at ;
    if ( * at == 'y' || * at == '=' ) query = 1 ;
    if ( * at == 'n' || * at == '-' ) query = 0 ;
    return ;
}

void read_cursor_shift ( void )
{
   char * at = comstring ;
   signed int sign = 1 ; 
   signed int nuval ;
   while ( isspace ( * at ) && * at ) ++ at ;
   if ( ! * at ) return ;  
   if ( * at == '-' ) { sign = -1 ; ++ at ; }
   nuval = atoi ( at ) ;
   mapcurshiftx = nuval * sign ;
   while ( !isspace ( * at ) && * at ) ++ at ;
   while ( isspace ( * at ) && * at ) ++ at ;
   if ( * at == '-' ) { sign = -1 ; ++ at ; }
   nuval = atoi ( at ) ;
   mapcurshifty = nuval * sign ;
}   
    

int handle_factors ( void )
{
   char * at = comstring ;
   int ftyp ; 
   double * x , nuval ;
   while ( isspace ( * at ) && * at ) ++ at ;
   if ( ! * at ) {
       showcurset () ;
       sprintf ( screencapt , "Factors are i=%f, a=%f, o=%f, d=%f, n=%f" ,
                 ( float ) iifac , ( float ) iafac ,
                 ( float ) oufac , ( float ) oafac , ( float ) ononafac ) ;
       win_refresh () ;         
       return 0 ; } 
   ftyp = * at ++ ;
   while ( isspace ( * at ) && * at ) ++ at ;
   if ( ! * at ) { showcurset () ; return 0 ; } 
   if ( ftyp != 'i' && ftyp != 'a' && ftyp != 'o' && ftyp != 'd' && ftyp != 'n' ) {
       showcurset () ;
       captf( "Must give factor type (i,a,o,d,n)" ) ;
       return 0 ; }
   if ( ftyp == 'i' ) x = &iifac ;
   if ( ftyp == 'a' ) x = &iafac ;
   if ( ftyp == 'o' ) x = &oufac ;
   if ( ftyp == 'd' ) x = &oafac ;
   if ( ftyp == 'n' ) x = &ononafac ; 
   nuval = (double ) atof ( at ) ;
   if ( nuval < 0 ) { showcurset () ;
                       captf( "Cannot use negative values!" ) ;
                       return 0 ; } 
   if ( ( ftyp == 'o' || ftyp=='d' || ftyp=='n' ) 
         && ( nuval == 0 || nuval > 1000000 ) ) {
                showcurset () ;
                captf( "\nOut factor must be 0 < f <= 10^6" ) ;
                return 0 ; }
   if ( ( ftyp == 'i' || ftyp == 'a' ) && nuval > 1 ) {
              showcurset () ;
              captf( "\nInferred/Assumed factor must be 0 <= f <= 1" ) ;
              return 0 ; }
   if ( * x != nuval ) {
       * x = nuval ;
       doallscores () ; } 
   showcurset () ;
   captf( "New %c factor is %f" , ftyp , nuval ) ;
   return 0 ; 
}    

int handle_compare_perc ( void )
{
   char * at = comstring ;
   int nuval ;
   while ( isspace ( * at ) && * at ) ++ at ;
   if ( isdigit ( * at ) ) { 
         nuval = atoi ( at ) ;
         if ( nuval > 100 ) {
             showcurset () ;
             captf( "Compare percentage must be 0 - 100" ) ;
             return 0 ; }
         if ( compare_perc != nuval ) {
             compare_perc = nuval ;
             doallscores () ; }}
   showcurset () ;
   captf( "Compare percentage is %i " , compare_perc ) ;
   return 0 ; 
}    

int show_color_code ; 

void viewscore ( int ky ) 
{ char * at = comstring ; 
  static int x , cursp , markneg = 0 ; 
  static int i , j , k , mc , sc ;
  int spwid ;  
  int32 mb , sb , * scptr ; 
  static int * tmptodo , * tmpnex , numar ;
  static double mscore ;
  char * cp ;
  static int viewwas ;
  if ( ky == 0 ) {
    show_color_code = 0; 
    while ( isspace ( * at ) && * at ) ++ at ; 
    if ( * at == '-' ) markneg = 1 ;
    else markneg = 0 ; 
    cursize = recptr -> size ; 
    lst = recptr -> lst ;
    markscore = 1 ;
    if ( recptr -> fromrepl ) {
        mscore = recptr -> score ; 
        for ( j = 0 ; j < spcells ; ++ j )
           intersptr [ j ] = recptr -> splist [ j ] ;
        for ( j = 0 ; j < spp ; ++ j )
          if ( ( intersptr [ j / 32 ] & ( 1 << ( j % 32 ) ) ) )
               spscore [ j ] = 1 ;
          else spscore [ j ] = 0 ; } 
    else 
       mscore = dorule5 () ; 
    markscore = 0 ; 
    scptr = intersptr ; 
    tmpnex = tmptodo = tmplist ;
    viewwas = show_individual_dots ;
    show_individual_dots = 1 ; 
    if ( mscore != 0 ) { 
      mb = 1 ; 
      mc = 0 ; 
      for ( j = 0 ; j < spp ; ++ j ) { 
             if ( ( scptr [ mc ] & mb ) && !markneg ) * tmptodo ++ = j ;  
             if ( !( scptr [ mc ] & mb ) && markneg &&
                   ( spact [ mc ] & mb )   // i.e. only show non-scoring species if active!
                     ) * tmptodo ++ = j ; 
             if ( mb == BIT32 ) { mb = 1 ; ++ mc ; } 
            else mb <<= 1 ; }} 
    if ( tmptodo == tmplist ) { 
      showcurset () ;
      curcmd_loop = cmd_loop ; 
      if ( !markneg ) captf("\nNothing to view (score = 0)!" ) ;
      else captf("\nNothing to view (no non-scoring, active spp.)!" ) ;
      return ; }
   lst = splist ; }
  x = ky ; 
  while ( 1 ) {
       switch ( x ) { 
            case 0 : break ; 
            case VK_ESCAPE :
               markneg = 0 ; 
               showcurset () ;
               curcmd_loop = cmd_loop ;
               show_individual_dots = viewwas ; 
               return ;  
            case VK_RETURN : case VK_TAB : case VK_NEXT : 
                if ( ++ tmpnex == tmptodo ) tmpnex = tmplist ;
                break ; 
            case BACK : case VK_PRIOR :
                if ( -- tmpnex < tmplist ) tmpnex = tmptodo - 1 ;
                break ;
            case 'c' :
               show_color_code = 1 - show_color_code ;
               break ; 
            default :
               markneg = 0 ; 
               showcurset () ;
               curcmd_loop = cmd_loop ;
               show_individual_dots = viewwas ; 
               return ; } 
       cursp = current_species = * tmpnex ; 
       sb = 1 << ( cursp % 32 ) ; 
       sc = cursp / 32 ; 
       for ( j = arcells ; j -- ; ) lst [ j ] = inflist [ j ] = 0 ; 
       for ( j = 0 ; j < cols ; ++ j ) 
           for ( k = 0 ; k < rows ; ++ k ) { 
               if ( ( matrix [ k ] [ j ] [ sc ] & sb ) ) { 
                    numar = ( k * cols ) + j ; 
                    mb = 1 << ( numar % 32 ) ; 
                    mc = numar / 32 ; 
                    lst[mc] |= mb ; }
               else 
               if ( ( assmatrix [ k ] [ j ] [ sc ] & sb ) ) { 
                    numar = ( k * cols ) + j ; 
                    mb = 1 << ( numar % 32 ) ; 
                    mc = numar / 32 ; 
                    inflist[mc] |= mb ; }} 
       if ( spname == NULL ) 
              if ( markneg )
                   screenf("Species %i doesn't contribute score to set %i\n" , 
                            cursp , recptr - rec ) ;
              else 
                  if ( !weight_species ) 
                     screenf("Species %i contributes %f to score=%f for set %i\n" , 
                           cursp , spscore [ cursp ] , mscore , recptr - rec ) ;
                  else screenf("Species %i contributes %f*%f to score=%f for set %i\n" , 
                           cursp , spscore [ cursp ] , species_weight [ cursp ] , mscore , recptr - rec ) ;
       else 
              if ( markneg )
                   screenf("Species %i [%s] doesn't contribute score to set %i\n" , 
                            cursp , spname[cursp] , recptr - rec ) ;
              else
                if ( !weight_species ) 
                  screenf("Species %i [%s] contributes %f to score=%f for set %i\n" , 
                       cursp , spname[cursp] , spscore [ cursp ] , mscore , recptr - rec ) ;
                else screenf("Species %i [%s] contributes %f*%f to score=%f for set %i\n" , 
                       cursp , spname[cursp] , spscore [ cursp ] , species_weight [ cursp ] , mscore , recptr - rec ) ;

       if ( show_color_code ) 
            drawmap ( recptr -> lst , lst , inflist ) ;
       else drawmap ( recptr -> lst , NULL , NULL ) ;

       if ( !markneg ) {
            j = tmptodo - tmplist ; 
            sprintf ( screencapt , "Inside: pres=%.0f, inf=%.0f, ass=%.0f.  Outside: obs=%.0f, ass(adj)=%.0f, ass=%.0f.\n" ,
                    dpres[cursp], dinf[cursp] , dass[cursp] , dout[cursp] , dadja [cursp] , dnadja [cursp] ) ; 
            cp = screencapt + strlen ( screencapt ) ;
            i = sprintf ( cp , "%i scoring spp.: " , j ) ;
            cp += i ;
            spwid = 10 ;
            if ( spname != NULL ) spwid = 4 ; 
            for ( j = 0 ; j < tmptodo - tmplist ; ++ j ) {
                 if ( ( j % spwid ) == 0 ) {
                      * cp ++ = '\n' ; * cp ++ = ' ' ;
                      * cp ++ = ' ' ; * cp ++ = ' ' ; * cp ++ = ' ' ; }
                if ( spname != NULL ) {
                  if ( spname[tmplist[j]] != NULL )
                     i = sprintf ( cp , "%3i %-23s  " , tmplist[j] , spname[tmplist[j]] ) ;
                  else i = sprintf ( cp , "%-27i  " , tmplist[j] ) ; }
                else 
                     i = sprintf ( cp , "%i " , tmplist [ j ] ) ;
                 cp += i ; }} 
       break ; }
    return ; 
} 

void handle_fuses ( void )
{
    int x = 0 , a , b ;
    int nusz ;
    int32 * ol , * nu ;
    char * ptr ;
    int tofuse , fused = 0 ;
    Artyp * arp ;
    char * at = comstring ; 
    while ( 1 ) {
        ptr = at ;
        while ( * ptr && isspace ( * ptr ) ) ++ ptr ;
        if ( !* ptr ) {
            captf("Fused %i sets to current set", fused ) ; 
            return ; }
        if ( isdigit ( * ptr ) ) {
                tofuse = atoi ( comstring ) ;
                while ( isdigit ( * ptr ) ) ++ ptr ;
                at = ptr ; }
        else if ( * ptr == 'm' ) tofuse = -1 ;
        else {
            showcurset () ;
            captf("Give number of set to fuse or 'm' for marked sets" ) ;
            return ; }
        if ( tofuse >= numrecs ) {
            showcurset () ;
            captf("No set number %i" , tofuse ) ;
            return ; }
        nusz = 0 ; 
        if ( tofuse >= 0 ) {
           ++ fused ; 
           nu = recptr -> lst ;
           ol = rec[tofuse].lst ;
           for ( a = arcells ; a -- ; ) {
                * nu |= * ol ; 
                nusz += onbits ( * nu ) ;
                nu ++ ;
                ol ++ ; }}
        else {
            arp = rec + numrecs ;
            fused = 0 ; 
            for ( a = numrecs ; a -- ; )
                if ( ( -- arp ) -> mark ) {
                    nu = recptr -> lst ;
                    ol = rec[a].lst ;
                    ++ fused ; 
                    for ( b = arcells ; b -- ; ) {
                       * nu |= * ol ; 
                       nusz += onbits ( * nu ) ;
                       nu ++ ;
                       ol ++ ; }}}
        recptr -> size = nusz ;
        dorule5 () ; 
        showcurset () ; }
}

int handle_marks ( void ) 
{ 
    char * at ;     
    Artyp * arp , * arf ; 
    int val , action , comp , setto , num , a , b , exp , marks = 0 ;
    double lim ; 
    at = comstring ; 
    while ( isspace ( * at ) && * at && * at != '/' ) ++ at ;
    if ( * at == '/' ) {
       if ( sure ( "Delete all marked sets" ) ) {
           recptr = rec + numrecs ; 
           for ( arp = rec ; arp < recptr ; ++ arp )
                   if ( arp -> mark ) { ++ marks ; arp -> erase = 1 ; }
                   else arp -> erase = 0 ; 
           delete_marks ( 1 ) ;
           if ( !numrecs ) donewset () ; 
           recptr = rec ; 
           showcurset () ;
           captf("Deleted %i marked sets", marks ) ; }
        return 0 ; }
    if ( * at == '?' ) {
        arp = rec - 1 ;
        for ( a = 0 ; a < numrecs ; ++ a )
            if ( ( ++ arp ) -> mark ) ++ marks ;
        showcurset () ; 
        captf("%i sets are marked" , marks ) ;
        return 0 ; }
    if ( * at == '\0' ) return ' ' ; 
    showcurset () ; 
    action =  * at ++ ;  
    if ( action != '=' && action != '+' && action != '-' )  {
         captf("Error: valid mark actions are = + -" ) ; 
         return 0 ; } 
    setto = 1 ; 
    if ( action == '-' ) setto = 0 ; 
    while ( isspace ( * at ) && * at ) ++ at ; 
    val = tolower ( * at ++ ) ; 
    if ( val == '\0' ) { 
         if ( action == '-' ) {
              recptr -> mark = 0 ;
              captf("Un-marked set %i" , recptr - rec ) ; }
         else { if ( action == '=' ) {
                     arp = rec ;
                     for ( a = 0 ; a < numrecs ; ++ a ) { arp -> mark = 0 ; ++ arp ; }}
                recptr -> mark = 1 ;
                captf("Marked set %i" , recptr - rec ) ; }
         return 0 ; } 
    if ( val == 's' || val == 'v' || val == 'm' ) { 
            while ( isspace ( * at ) && * at ) ++ at ; 
            comp = tolower ( * at ++ ) ; 
            if ( comp != '=' && comp != '>' && comp != '<' ) { 
                    captf("Error: valid comparisons for marks are > = <" ) ; 
                    return 0 ; }
            while ( * at && isspace ( * at ) ) ++ at ;
            if ( isdigit ( * at ) ) lim = ( double ) atof ( at ) ;
            else {
                if ( val == 's' ) lim = recptr -> size ;
                else if ( val == 'v' ) lim = recptr -> score ;
                else lim = recptr -> numspp ; }
            arp = rec ; 
            for ( a = 0 ; a < numrecs ; ++ a ) { 
                  if ( action == '=' ) arp -> mark = 0 ; 
                  if ( comp == '=' ) { 
                         if ( val == 's' ) { 
                                 if ( lim == arp -> size ) {
                                        arp -> mark = setto ; ++ marks ; }} 
                         else if ( val == 'v' ) { 
                                 if ( lim == arp -> score ) { arp -> mark = setto ; ++ marks ; }}
                         else if ( lim == arp -> numspp ) { arp -> mark = setto ; ++ marks ; }} 
                  if ( comp == '>' ) { 
                         if ( val == 's' ) { 
                                 if ( lim < arp -> size ) { arp -> mark = setto ; ++ marks ; }} 
                         else if ( val == 'v' ) { 
                                if ( lim  < arp -> score ) { arp -> mark = setto ; ++ marks ; }}
                         else  if ( lim < arp -> numspp ) { arp -> mark = setto ; ++ marks ; }} 
                  if ( comp == '<' ) { 
                         if ( val == 's' ) { 
                                 if ( lim  > arp -> size ) { arp -> mark = setto ; ++ marks ; }} 
                         else if ( val == 'v' ) { 
                                if ( lim > arp -> score ) { arp -> mark = setto ; ++ marks ; }}
                         else if ( lim > arp -> numspp ) { arp -> mark = setto ; ++ marks ; }}
                  ++ arp ; }}
    if ( val == 'c' || val == 'u' || val == 'w' || val == 'd' || val == '=' ) { 
          arp = rec ;
          exp = 0 ;
          if ( val == 'c' ) exp = 2 ;
          if ( val == 'w' ) exp = 1 ;
          if ( val == 'u' ) exp = -1 ;
          if ( val == '=' ) exp = 3 ; 
          for ( a = 0 ; a < numrecs ; ++ a ) { 
                if ( action == '=' ) arp -> mark = 0 ; 
                if ( oneintwo ( arp , recptr ) == exp ) { arp -> mark = setto ; ++ marks ; }
                ++ arp ; }}
    if ( action == '-' ) captf("Un-marked %i sets" , marks ) ; 
    else captf("Marked %i sets" , marks ) ; 
    return 0 ; 
} 

void ermsg ( char * ptr ) 
{ 
  MessageBox ( hwnd , ptr , "ERROR" , MB_OK | MB_ICONERROR ) ; 
  SendMessage ( hwnd , WM_COMMAND, IDM_EXIT , 0 ) ;
  exit ( 0 ) ; 
  return ; 
} 

void memerr ( void * wht ) 
{ 
     if ( wht != NULL ) return ;
     if ( rows && cols && spp ) 
          sprintf ( junkstr , "\nNot enough memory to run data\nwith %i rows, %i cols, and %i spp.\n" , rows , cols , spp ) ;
     else  sprintf ( junkstr , "\nCannot read data for\n%i rows, %i cols, and %i spp.\n" , rows , cols , spp ) ;
     if ( !rows || !cols || !spp ||
          rows > 5000 || cols > 5000 || spp > 100000 )
             strcat ( junkstr , "(input file may be incorrect)\n" ) ; 
     ermsg ( junkstr ) ; 
} 


BOOL CALLBACK GetComStringFunc(HWND hdwnd, UINT message, WPARAM wParam, LPARAM lParam)
{
    int i , j ;
    HWND hWho ;
    switch(message) {
        case WM_INITDIALOG :
                   SetWindowText ( hdwnd , prompt ) ;
                   SetDlgItemText ( hdwnd , 69 , comstring ) ; 
                   SetFocus ( GetDlgItem ( hdwnd , 69 ) ) ; 
                   break ; 
        case WM_COMMAND :
                switch(LOWORD(wParam)){
                        case IDOK : 
                           GetDlgItemText(hdwnd, 69, junkstr, 80);
                           strcpy ( comstring , junkstr ) ; 
                           EndDialog ( hdwnd, 1 ) ;
                           return 1 ; 
                           break ;
                        case IDCANCEL :
                                EndDialog(hdwnd,0);
                                return 0;
                        default :
                                break; }
         break; }
    return 0;
}


void get_filename ( char type )
{
    char * save_path ; 
    OPENFILENAME ofn ;
          comstring[0]='\0' ; 
          save_path=comstring;
          memset(&ofn, 0, sizeof(OPENFILENAME));
          ofn.lStructSize = sizeof( OPENFILENAME);
          ofn.hwndOwner = hwnd;
          if ( type == '[' ) {
                 ofn.lpstrFilter = "Coordinate files (*.xyd)\0*.xyd\0\0";
                 ofn.lpstrTitle = "Open Coordinate File to Read"; }
          if ( type == '?' ) {
               ofn.lpstrFilter = "Line files (*.lin)\0*.lin\0\0";
               ofn.lpstrTitle = "Open Line File to Read"; }
          if ( type == '@' ) {
                 ofn.lpstrFilter = "Output files (*.out)\0*.out\0\0" ; 
                 ofn.lpstrTitle = "Open File"; }
          if ( type == 'o' ) {
              if ( grid_created ) {
                 ofn.lpstrFilter = "Output files (*.out)\0*.out\0Point files (*.xyd)\0*.xyd\0\0" ; 
                 // "Output files (*.out)\0*.out\0\0";
                 ofn.lpstrTitle = "Open Output File"; }
              else {
                 ofn.lpstrFilter = "Coordinate files (*.xyd)\0*.xyd\0\0";
                 ofn.lpstrTitle = "Create Coordinate File"; }}
          if ( tolower ( type ) == 'l' ) {
               ofn.lpstrFilter = "Log files (*.ndm)\0*.ndm\0\0";
               ofn.lpstrTitle = "Save results to Log file"; }
          if ( type == 'R' ) { // "read"
               ofn.lpstrFilter = "Log files (*.ndm)\0*.ndm\0\0";
               ofn.lpstrTitle = "Read sets from Log file"; }
          if ( type == 0 ) { // "read input data"
             if ( grid_created ) 
               ofn.lpstrFilter = "Log files (*.ndm)\0*.ndm\0\0";
             else ofn.lpstrFilter = "Dat files (*.dat)\0*.dat\0Point files (*.xyd)\0*.xyd\0Log files (*.ndm)\0*.ndm\0";
             ofn.lpstrTitle = "Open input file"; }
          ofn.lpstrFile = save_path;
          ofn.nMaxFile = MAX_PATH;
          ofn.lpstrFileTitle = save_path;
          ofn.nMaxFileTitle = MAX_PATH ;
          if ( query && (
               type == 'o' || tolower ( type ) == 'l' ) ) 
               ofn.Flags = OFN_OVERWRITEPROMPT | OFN_PATHMUSTEXIST ;
          else
            if ( type == 'R' || type == 0 || type == '?' || type == '[' )
                 ofn.Flags = OFN_FILEMUSTEXIST | OFN_HIDEREADONLY ; 
            else ofn.Flags = OFN_PATHMUSTEXIST ;
          if ( type == '@' ) {
              ofn.Flags = OFN_FILEMUSTEXIST | OFN_HIDEREADONLY ;
              ofn.lpstrDefExt = "out"; }
          if ( type == 'o' ) ofn.lpstrDefExt = "out";
          if ( tolower ( type ) == 'l' ) ofn.lpstrDefExt = "ndm";
          if ( type == 'o' || type == 'l' ) {
             if(!GetSaveFileName( &ofn )) {
                 * save_path = '\0' ; return ; }}
          else
             if(!GetOpenFileName( &ofn )) {
                 * save_path = '\0' ; return ; }
          InvalidateRect(hwnd,NULL,1);
          return ;
}

int chkiscom ( int a ) 
{   int x = a ;
    comstring[0] = '\0' ;
    if ( curcmd_loop != cmd_loop && x != 'g' && ( curcmd_loop != show_consensus || x != 'J' ) ) return 0 ; 
         if ( x == 'm' ) strcpy ( prompt , "Mark: " ) ; 
    else if ( x == '/' && outspace != NULL ) strcpy ( prompt , "Divide in: " ) ; 
    else if ( x == 's' ) strcpy ( prompt , "Save: " ) ;
    else if ( x == 'F' ) strcpy ( prompt , "Prop. records:" ) ;
    else if ( ( x == 'J' ) && ( curcmd_loop == cmd_loop || curcmd_loop == show_consensus ) ) {
              if ( curcmd_loop == cmd_loop ) strcpy ( prompt , "Compare to set:" ) ;
              else strcpy ( prompt , "Compare to consensus: " ) ; } 
    else if ( x == 'g' ) {
        if ( curcmd_loop == showspecies ) strcpy ( prompt , "Go to species: " ) ;
        else if ( curcmd_loop == show_consensus )
                strcpy ( prompt , "Go to consensus" ) ;
        else strcpy ( prompt , "Go to: " ) ; }
    else if ( x == '8' ) {
            strcpy ( prompt , "Type of sampling to test (1-3):" ) ;
            sprintf ( comstring , "1" ) ; }
    else if ( x == '9' ) strcpy ( prompt , "Similarity to show:" ) ; 
    else if ( x == 'Q' ) strcpy ( prompt , "Query (y/n): " ) ;
    else if ( x == 'f' ) strcpy ( prompt , "Factor (type,value): " ) ;
    else if ( x == 'P' )  strcpy ( prompt , "Compare Perc.: " ) ; 
    else if ( x == 'v' ) strcpy ( prompt, "Scoring spp.: ") ; 
    else if ( x == 'e' ) strcpy ( prompt , "Empty: ") ; 
    else if ( x == 'h' ) strcpy ( prompt, "One full cell min. (0-2)" ) ;
    else if ( x == 'a' ) strcpy ( prompt, "Create random data, P(pres): " ) ; 
    else if ( x == 'x' ) strcpy ( prompt , "Fuse sets: " ) ;
    else if ( x == 'p' ) strcpy ( prompt , "Edge props. (y/n)" ) ;
    else if ( x == 255 ) strcpy ( prompt , "New grid size (<cancel> to use current): " ) ; 
    else if ( x == 'w' ) {
        strcpy ( prompt , "Minimum taxon weight:" ) ;
        sprintf ( comstring , "%f" , weight_min ) ; }
    else if ( x == 'b' ) strcpy ( prompt , "Minimum species score:" ) ;  
    else if ( !grid_created && nummaplins && x == VK_F6 )
         sprintf ( prompt , "Mouse shift (%i,%i):" , mapcurshiftx , mapcurshifty ) ; 
    else {
          if ( x == 'o' || x == 'l' || x == 'R' || x == 'L' || x == 0 || x == '?' || x == '[' ) {
             get_filename ( x ) ;
             return 1 ; }
          return 0 ; }
    x = DialogBox (hInst, "GetComStringDB", hwnd, (DLGPROC) GetComStringFunc ) ; 
    if ( ! x ) comstring[0] = '\0' ; 
    return 1 ; 
} 

void dospmap ( int sp ) 
{ 
  int a , mc , ic , b , numar ; 
  int32 mb , ib ; 
  for ( a = arcells ; a -- ; ) splist [ a ] = inflist [ a ] = 0 ;  
  mb = 1 << ( sp % 32 ) ; 
  mc = sp / 32 ; 
  for ( a = rows ; a -- ; ) 
      for ( b = cols ; b -- ; )  
           if ( isdefd [ a ] [ b ] ) { 
               if ( ( matrix [ a ] [ b ] [ mc ] & mb ) ) { 
                   numar = ( cols * a ) + b ; 
                   ib = 1 << ( numar % 32 ) ; 
                   ic = numar / 32 ; 
                   splist [ ic ] |= ib ; }
               else 
               if ( ( assmatrix [ a ] [ b ] [ mc ] & mb ) ) { 
                   numar = ( cols * a ) + b ; 
                   ib = 1 << ( numar % 32 ) ; 
                   ic = numar / 32 ; 
                   inflist [ ic ] |= ib ; }}
  drawmap ( splist , NULL , inflist ) ; 
  return ; 
} 

extern int autopaintcells ; 

int paintspcell ( int acol , int arow , int mc , int mb , int sp )
{
    int chgd = 0 , bitison = 0 ; 
    if ( !isdefd [ arow ] [ acol ] ) return 0 ;  
    if ( ( lst[mc] & mb ) ) bitison = 1 ;
    if ( paint_mode == 1 ) { 
          if ( ( inflst[mc] & mb ) ) {
            if ( autopaintcells == 3 ) return 0 ; 
            lst[mc] |= mb ;
            if ( !bitison ) {
                numentries [ sp ] ++ ; 
                chgd = 1 ; }}
          else {
            inflst[mc] |= mb ;
            ++ numassentries [ sp ] ;
            chgd = 1 ; }}
    else {
        if ( bitison ) {
            lst[mc] &= ~mb ; 
            numentries [ sp ] -- ;
            if ( !( inflst[mc] & mb ) ) ++ numassentries[ sp ] ;
            inflst[mc] |= mb ; 
            chgd = 1 ; }
        else if ( ( inflst[mc] & mb ) ) {
            // if ( autopaintcells == 3 ) return 0 ; 
            -- numassentries[ sp ] ;
            inflst[mc] &= ~mb ;
            chgd = 1 ; }}
   return chgd ;
} 


void create_set_from_sp ( int sp )
{
    int mc = sp / 32 , ac , numar ;
    int x , y ;
    int mysz = 0 ;
    int32 * arpt ;  
    int32 mb = 1 << ( sp % 32 ) , bc ; 
    donewset () ;
    arpt = recptr -> lst ; 
    for ( y = 0 ; y < rows ; ++ y )
    for ( x = 0 ; x < cols ; ++ x ) {
        if ( ( matrix [ y ] [ x ] [ mc ] & mb ) ||
              ( assmatrix [ y ] [ x ] [ mc ] & mb ) ) {
                      numar = ( y * cols ) + x ;
                      ac = numar / 32 ;
                      bc = 1 << ( numar % 32 ) ;
                      arpt [ ac ] |= bc ;
                      ++ mysz ; }}
    recptr->size = mysz ; 
    dorule5 () ;
    return ; 
}         

void showfauna ( int ky ) 
{ static int x = 0 , cursp , a, b , c , mc , ac , numar , sc , j , k ; 
  static int32 mb , ab , * lp , sb ; 
  static int * done , * todo ;
  static int showwas ;
  static int sppprop ;
  static int innerprop ;
  char * cp , isneg ; 
  int spi , spj , spk ; 
  if ( !ky ) {
     show_color_code = 0 ; 
     showwas = show_individual_dots ;
     show_individual_dots = 1 ;
     sppprop = innerprop = isneg = 0 ; 
     if ( isdigit ( comstring[0] ) ) sppprop = atoi ( comstring ) ;
     a = 0 ; 
     while ( comstring[a] != '/' && comstring[a] != '\0' ) ++ a ;
     if ( comstring[a] == '/' ) {
         cp = comstring + a + 1 ;
         if ( * cp == '-' ) { isneg = 1 ; ++ cp ; } 
         if ( isdigit ( * cp ) ) innerprop = atoi ( cp ) ; } 
     done = todo = tmplist ; 
     lp = recptr -> lst ;
     for ( a = 0 ; a < spcells ; ++ a ) intersptr[a] = 0 ;
     if ( sppprop <= 0 && innerprop <= 0 ) 
       for ( a = 0 ; a < spp ; ++ a ) { 
          mc = a / 32 ; 
          mb = 1 << ( a % 32 ) ; 
          for ( b = 0 ; b < rows ; ++ b ) 
              for ( c = 0 ; c < cols ; ++ c ) { 
                  if ( ( matrix [ b ][ c ] [ mc ] & mb ) == 0 &&
                       ( assmatrix [ b ][ c ] [ mc ] & mb ) == 0 ) continue ; 
                  numar = ( b * cols ) + c ; 
                  ab = 1 << ( numar % 32 ) ; 
                  ac = numar / 32 ; 
                  if ( ( lp [ac] & ab ) ) { 
                          * todo ++ = a ;
                          intersptr[a/32] |= 1<<(a%32) ; 
                          b = rows ; 
                          break ; }}}
     else 
       for ( a = 0 ; a < spp ; ++ a ) { 
          mc = a / 32 ; 
          mb = 1 << ( a % 32 ) ; 
          spi = spj = spk = 0 ; 
          for ( b = 0 ; b < rows ; ++ b ) 
              for ( c = 0 ; c < cols ; ++ c ) {
                  numar = ( b * cols ) + c ; 
                  ab = 1 << ( numar % 32 ) ; 
                  ac = numar / 32 ;
                  if ( lp[ac] & ab ) ++ spk ; 
                  if ( ( matrix [ b ][ c ] [ mc ] & mb ) == 0 &&
                       ( assmatrix [ b ][ c ] [ mc ] & mb ) == 0 ) continue ;
                  ++ spi ; 
                  numar = ( b * cols ) + c ; 
                  ab = 1 << ( numar % 32 ) ; 
                  ac = numar / 32 ; 
                  if ( ( lp [ac] & ab ) ) ++ spj ; }
           if ( spj == 0 ) continue ; 
           if ( innerprop > 0 && spk ) { 
                if ( !isneg && spj * 100 / spk < innerprop ) continue ;
                if ( isneg && spj * 100 / spk > innerprop ) continue ; }
           if ( spj * 100 / spi >= sppprop ) {
                * todo ++ = a ;
                intersptr[a/32] |= 1<<(a%32) ; }}
     * todo = -1 ; 
     if ( todo == tmplist ) {
        show_individual_dots = showwas ;
        showcurset () ; 
        captf ("\nAREA %i: NO SPECIES" , recptr - rec ) ;
        curcmd_loop = cmd_loop ; 
        return ; }}
  x = ky ;
  while ( 1 ) { 
       switch ( x ) { 
            case 0 : break ; 
            case VK_ESCAPE :
                curcmd_loop = cmd_loop ;
                show_individual_dots = showwas ; 
                showcurset () ;
                return ; 
            case 'c' :
               show_color_code = 1 - show_color_code ;
               break ; 
            case VK_RETURN: case VK_TAB : case VK_NEXT : 
                        if ( todo == ++ done ) done = tmplist ; break ; 
            case BACK : case VK_PRIOR : 
               if ( tmplist > -- done ) done = todo - 1 ; break ; 
            default :
                curcmd_loop = cmd_loop ;
                show_individual_dots = showwas ; 
                showcurset () ;
                return ; } 
       cursp = * done ; 
       sb = 1 << ( cursp % 32 ) ; 
       sc = cursp / 32 ; 
       for ( j = arcells ; j -- ; ) splist [ j ] = inflist [ j ] = 0 ; 
       for ( j = 0 ; j < cols ; ++ j ) 
           for ( k = 0 ; k < rows ; ++ k ) { 
               if ( ( matrix [ k ] [ j ] [ sc ] & sb ) ) { 
                    numar = ( k * cols ) + j ; 
                    mb = 1 << ( numar % 32 ) ; 
                    mc = numar / 32 ; 
                    splist [mc] |= mb ; } 
               else if ( ( assmatrix [ k ] [ j ] [ sc ] & sb ) ) { 
                    numar = ( k * cols ) + j ; 
                    mb = 1 << ( numar % 32 ) ; 
                    mc = numar / 32 ; 
                    inflist [mc] |= mb ; }} 
       screenf("Species %i is found in area %i (area has %i spp.)\n" , cursp , recptr - rec , todo - tmplist ) ; 
       current_species = cursp ; 
       if ( show_color_code ) 
            drawmap ( recptr -> lst , splist , inflist ) ;
       else drawmap ( recptr -> lst , NULL , NULL ) ;
       if ( spname != NULL )
           if ( spname[ cursp ] != NULL )
               captf ( "%s" , spname[cursp] ) ; 
       break ; }
    return ; 
} 
      
void showspecies ( int x ) 
{  static int cursp = 0 , spwas ;
   static char disptxt[15] ;
   int how_many = -1 , just_created_set = 0 ;
   int i , j , k , totlis ; 
   char * cp ;
   static int included_sp , from_sp ;
   static int num_included_spp ;
   int * inclulist = ( int * ) dout ; 

   if ( !x ) {
       cursp = 0 ;
       included_sp = -1 ; } 
       
   current_species = cursp ;
   if ( included_sp >= 0 ) 
       current_species = cursp = inclulist [ included_sp ] ; 
   
   while ( 1 ) {  
      switch ( x ) { 
        case 0 : break ;
        case 'H': dohlp ( 1 ) ; break ;
        case 'w':
            if ( species_tree == NULL ) break ;
            if ( included_sp >= 0 ) { 
               included_sp = -1 ;
               cursp = current_species = from_sp ;
               break ; }
            if ( cursp < numterminals ) break ; 
            from_sp = cursp ; 
            num_included_spp = 0 ; 
            for ( i = 0 ; i < numterminals ; ++ i ) {
               for ( j = species_tree [ i ] ; j != treeroot ; j = species_tree [ j ] )
                  if ( j == cursp + 1 ) {
                     inclulist [ num_included_spp ++ ] = i ;
                     break ; }}
            cursp = current_species = inclulist [ included_sp = 0 ] ; 
            break ; 
        case 'M' :
              how_many = mark_all_scored_areas_for_this_sp ( cursp ) ;
              break ; 
        case VK_TAB : case VK_RETURN : case VK_NEXT : 
              if ( included_sp >= 0 ) {
                  if ( ++ included_sp >= num_included_spp ) included_sp = 0 ;
                  cursp = current_species = inclulist [ included_sp ] ;
                  break ; } 
              if ( ++ cursp == spp ) cursp = 0 ;
              current_species = cursp ; 
              break ; 
        case VK_BACK : case VK_PRIOR : 
              if ( included_sp >= 0 ) {
                  if ( -- included_sp < 0 ) included_sp = num_included_spp - 1 ;
                  cursp = current_species = inclulist [ included_sp ] ;
                  break ; } 
              if ( -- cursp < 0 ) cursp = spp - 1 ;
              current_species = cursp ; 
              break ; 
        case 'g' : 
           spwas = cursp ; 
           cursp = atoi ( comstring ) ; 
           if ( cursp < 0 || cursp >= spp ) cursp = spwas ;
           current_species = cursp ; 
           break ; 
        case 'V':
           if ( redoallscores ) {
               if ( species_tree != NULL ) 
                    add_species_groups () ; 
               doallscores () ; }
            curcmd_loop = viewmarks ; 
            viewmarks ( 0 ) ;
            return ;
        case VK_ESCAPE : case 'X' :
            if ( included_sp >= 0 ) {
                included_sp = -1 ;
                cursp = current_species = from_sp ;
                break ; } 
           if ( redoallscores ) {
               if ( species_tree != NULL ) 
                    add_species_groups () ; 
               doallscores () ; }
           showcurset () ;
           curcmd_loop = cmd_loop ; 
           return ;
        case 'A' :
           auto_fill_assumed_records ( cursp ) ;
           redoallscores = 1 ;
           break ; 
        case VK_HOME :
            cursp = 0 ;
            current_species = cursp ; 
            break ;
        case 'S' :
            sprintf ( junkstr , "Create a new set from sp. %i" , cursp ) ; 
            if ( !sure ( junkstr ) ) return ; 
            just_created_set = 1 ;
            create_set_from_sp ( cursp ) ;
            InvalidateRect ( hwnd , NULL , 1 ) ; 
            return ; 
        case VK_END :
             cursp = spp - 1 ;
             current_species = cursp ; 
             break ; 
        default :
           errmsg ( "Invalid key\n\(press <esc> to go back to normal mode)" , Null ) ; 
           return ; }
      disptxt[0] = '\0' ;
      recalculate_numentries ( cursp ) ; 
      if ( !( spact[cursp/32] & ( 1 << ( cursp % 32 ) ) ) )
         strcpy ( disptxt , "- inactive!" ) ;
      if ( included_sp >= 0 ) {
          if ( spname == NULL ) 
                screenf("Species %i is included in %\n" , cursp , from_sp ) ; 
          else  screenf("Species %i (%s) is included in %i\n" , cursp , spname[cursp] , from_sp ) ; } 
      else     
      if ( !weight_species ) 
          if ( spname == NULL ) 
                screenf("Species Nr. %i (%i cells) %s\n" , cursp , numentries [ cursp ]  , disptxt ) ; 
          else  screenf("Species Nr. %i (%i cells) - %s%s\n" , cursp , numentries [ cursp ] , spname[cursp] , disptxt ) ;
      else 
          if ( spname == NULL ) 
                screenf("Species Nr. %i (%i records, %i cells, weight=%f) %s\n" , cursp , xymatrix[cursp].numrecs , numentries [ cursp ]  , species_weight [ cursp ] , disptxt ) ; 
          else  screenf("Species Nr. %i (%i records, %i cells, weight=%f) - %s%s\n" , cursp , xymatrix[cursp].numrecs , numentries [ cursp ] , species_weight [ cursp ] , spname[cursp] , disptxt ) ;
      dospmap ( cursp ) ;
      if ( included_sp < 0 ) 
        if ( how_many >= 0 )
             captf ( "Marked %i areas to which this species gives score" , how_many ) ;
        else 
        if ( just_created_set )
           captf ( "Created a new set (%i) from this species" , numrecs - 1 ) ;

        else 
        if ( species_tree != NULL && cursp >= numterminals ) {
            cp = screencapt ;
            k = totlis = 0 ; 
            for ( i = 0 ; i < numterminals ; ++ i ) {
                j = species_tree [ i ] ;
                while ( j != treeroot && j != cursp + 1 ) 
                    j = species_tree [ j ] ;  
                if ( j == cursp + 1 ) {
                    if ( ++ totlis > 20 ) continue ; 
                    j = 1 ; 
                    if ( spname == NULL ) j = 0 ;
                    else if ( spname [ i ] == NULL ) j = 0 ;
                    if ( j ) cp += sprintf ( cp , "%20s" , spname [ i ] ) ;
                    else cp += sprintf ( cp , "%20i" , i ) ;
                    * cp = '\0' ; 
                    strcat ( cp , ", " ) ; cp += 2 ; 

                    if ( ++ k == 4 ) { * cp ++ = '\n' ; k = 0 ; }
                   }}
            * cp = '\0' ;
            if ( totlis > 20 ) cp += sprintf ( cp , "\n(etc.etc)\n" ) ;
            sprintf ( cp , "Total: %i species" , totlis ) ; 
            }

      break ; }
   return ; 
} 

int paintsetcell ( int acol , int arow , int mc , int mb )
{
    int chgd = 0 , bitison = 0 ; 
    if ( !paint_mode ) return  0 ;
    if ( !isdefd [ arow ] [ acol ] ) return  0 ;
    if ( ( lst[mc] & mb ) ) bitison = 1 ;
    if ( paint_mode == 1 ) { 
        if ( !bitison ) {
            lst[mc] |= mb ;
            recptr -> size += 1 ;
            chgd = 1 ; }}
    else {
        if ( bitison ) {
            lst[mc] &= ~mb ;
            recptr -> size -= 1 ; 
            chgd = 1 ; }}
   return chgd ;
} 

int oneintwo ( Artyp * ara , Artyp * arb ) // is A inside B?
{  int32 * ca , * cb ; 
   int disj , anonb , bnona ; 
   int j ; 
   ca = ara->lst ; 
   cb = arb->lst ; 
   disj = 1 ; 
   anonb = bnona = 0 ; 
   for ( j = arcells ; j -- ; ) { 
       if ( * ca & * cb ) disj = 0 ; 
       if ( * ca & ~ * cb ) anonb = 1 ; 
       if ( * cb & ~ * ca ) bnona = 1 ; 
       if ( !disj && anonb && bnona ) break ; 
       ++ ca ; ++ cb ; } 
   if ( !disj ) {
       if ( !anonb && !bnona ) return  3 ;    // IDENTICAL
       if ( bnona && anonb )   return  2 ;    // CONTRADICTORY
       if ( bnona && !anonb )  return  1 ;    // A IS WITHIN B  
       if ( anonb && !bnona )  return -1 ; }  // A IS CONTAINED IN B
                               return  0 ;    // A-B ARE DISJUNCT
} 

double do_set_similarity ( Artyp * one , Artyp * other )
{
    int shared , inanotb , inbnota ;
    double zult ; 
    int32 * lsta = one -> lst , * lstb = other -> lst , x , i ; 
    shared = inbnota = inanotb = 0 ;
    for ( i = 0 ; i < arcells ; ++ i , ++ lsta , ++ lstb ) {
        shared += onbits ( ( * lsta & * lstb ) ) ;
        inbnota += onbits ( ( * lstb & ~ * lsta ) ) ;
        inanotb += onbits ( ( * lsta & ~ * lstb ) ) ; }
    zult = ( double ) shared / ( shared + inbnota + inanotb ) ;
    return zult ; 
}        

void showsuperset ( int ky ) 
{ static Artyp ** done , ** todo , * old , ** tmpar , * datmp ;
  int32 * apt , * bpt ;
  int a , b , just_marked ; 
  int x = ky ;
  double thisval ; 
  static double simval ; 
  if ( !ky ) {
     done = todo = arlist ; 
     old = recptr ; 
     recptr = rec - 1 ;
     simval = atof ( comstring ) ; 
     for ( a = 0 ; a < numrecs ; ++ a ) { 
       ++ recptr ; 
       lst = recptr -> lst ; 
       if ( recptr == old ) continue ; 
       if ( do_set_similarity ( old , recptr ) >= simval ) * todo ++ = recptr ; } 
    if ( todo == arlist ) { 
      recptr = old ;
      showcurset () ;
      captf("No set has similarity %f (or greater) with set %i" , simval , old-rec ) ;
      curcmd_loop = cmd_loop ; 
      return ; }} 
  while ( 1 ) {
       just_marked = 0 ; 
       switch ( x ) { 
            case 0 : break ;
            case 'M' :
               for ( tmpar = arlist ; tmpar < todo ; ++ tmpar ) {
                  datmp = * tmpar ; 
                  datmp -> mark = 1 ;
                  ++ just_marked ; }
               break ; 
            case VK_ESCAPE :
                recptr = old ;
                showcurset () ; 
                curcmd_loop = cmd_loop ; return ; 
            case VK_RETURN : case VK_TAB :
               if ( ++ done == todo ) done = arlist ; break ; 
            case VK_BACK :
                if ( -- done < arlist ) done = todo - 1 ; break ; 
            default :
               recptr = old ;
               showcurset () ; 
               curcmd_loop = cmd_loop ;
               return ; } 
       recptr = * done ; 
       thisval = do_set_similarity ( recptr , old ) ; 
       screenf("Set %i (size=%i). Similarity to %i=%f.\n" , 
                  recptr - rec , recptr -> size , old - rec , thisval ) ; 
       drawmap ( recptr -> lst , NULL , NULL ) ;
       if ( just_marked )
         captf ( "Marked %i sets with similarity %f (or greater) to set %i" , just_marked , simval , old-rec ) ;  
       break ; }
    return ; 
} 

char cur_duwc_act ; 
Artyp * cons_duwc_start , * cons_duwc_for ; 

void put_consensus_in_duwc_buffer ( void )
{
    Artyp * at ;
    int a , i , mc ;
    int32 * lst , mb ;
    Constyp * conpt ;
    double val ;
    for ( i = 0 , at = cons_duwc_start = rec + numrecs ; i < numcons ; ++ i , ++ at ) {
       conpt = consen + i ; 
       for ( lst = at -> lst , a = arcells ; a -- ; )
          * lst ++ = 0 ; 
       for ( a = 0 , mb = 1 , mc = 0 ; a < totareas ; ++ a ) {
           val = conpt->clmax[a] ;
           if ( val > 0 ) 
              at -> lst [ mc ] |= mb ; 
           if ( mb == BIT32 ) { mb = 1 ; ++ mc ; }
           else mb <<= 1 ; }}
    return ; 
} 

void show_duwc ( int ky ) 
{ static Artyp ** done , ** todo , * old , ** tmpar , * datmp ;
  int32 * apt , * bpt ;
  int anonb , bnona , banda ; 
  int a , b , c , just_marked ; 
  int x = ky ;
  char mtxt[50] ;
  int exp ;
  int act = cur_duwc_act ;
  static int show_nth_sp ;
  static int list_the_spp ;
  unsigned long int * disppt ;
  char * cp ;
  int mc ;
  int shared ; 
  unsigned long int mb ;
  static int reference_set ; 
  Constyp * refcon , * nucon ; 
  exp = 0 ; strcpy (mtxt , "disjunct with" ) ;   
  if ( act == 'W' )     { exp = -1 ; strcpy ( mtxt , "within" ) ; }         
  if ( act == 'U' )     { exp = 1 ; strcpy ( mtxt , "contains" ) ; }   
  if ( act == 'C' )     { exp = 2 ; strcpy ( mtxt , "contradicts" ) ; }
  if ( act == '=' )     { exp = 3 ; strcpy ( mtxt , "same as" ) ; }
  if ( act == 'J' )     { exp = 4 ; strcpy ( mtxt , "compared to" ) ; }
  if ( !ky ) {
     if ( comstring[0] == '*' ) {
         reference_set = -1 ;
         b = 0 ; 
         if ( !is_cons_duwc ) 
            for ( a = 0 , datmp = rec ; a < numrecs ; ++ a , ++ datmp )
                if ( datmp -> mark && datmp != recptr ) ++ b ; 
         if ( !b ) {
            errmsg ( "No marks to compare!" ) ;
            if ( is_cons_duwc ) {
               curcmd_loop = show_consensus ;
               show_consensus ( 1 ) ; } 
            else { 
               showcurset () ;
               curcmd_loop = cmd_loop ; }
            return ; }}
     else {
        reference_set = atoi ( comstring ) ;
        if ( reference_set >= numrecs || reference_set < 0 ) {
             errmsg ( "No such set!" ) ;
             if ( is_cons_duwc ) {
                curcmd_loop = show_consensus ;
                show_consensus ( 1 ) ; } 
             else { 
                showcurset () ;
                curcmd_loop = cmd_loop ; }
             return ; }}
     if ( num_spingrid ) { 
         list_the_spp = 1 ; 
         show_nth_sp = 0 ; }
     else list_the_spp = 0 ; 
     if ( is_cons_duwc ) {
         if ( 10000 - numrecs < numcons ) errmsg ( "Sorry, not enough memory for requested calculation" , Null ) ;
         put_consensus_in_duwc_buffer () ;
         done = todo = arlist ; 
         old = cons_duwc_start + curcons ; 
         recptr = cons_duwc_start - 1 ;
         if ( exp == 4 ) 
             * todo ++ = cons_duwc_start + reference_set ;  
         else 
         for ( a = 0 ; a < numrecs ; ++ a ) { 
           ++ recptr ; 
           lst = recptr -> lst ; 
           if ( recptr == old ) continue ; 
           if ( oneintwo ( old , recptr ) == exp ) * todo ++ = recptr ; }
         } 
     else { 
         done = todo = arlist ; 
         old = recptr ; 
         recptr = rec - 1 ;
         if ( exp == 4 ) {
             if ( reference_set < 0 ) {
                 for ( a = b = 0 , datmp = rec ; a < numrecs ; ++ a , ++ datmp )
                     if ( datmp -> mark && datmp != old ) { ++ b ; * todo ++ = datmp ; }}
             else 
                * todo ++ = rec + reference_set ; } 
         else 
         for ( a = 0 ; a < numrecs ; ++ a ) { 
           ++ recptr ; 
           lst = recptr -> lst ; 
           if ( recptr == old ) continue ; 
           if ( oneintwo ( old , recptr ) == exp ) * todo ++ = recptr ; }}
    if ( todo == arlist ) { 
      if ( is_cons_duwc ) { 
          curcmd_loop = show_consensus ;
          just_out_of_duwc = act + 1 ; 
          show_consensus ( 1 ) ; } 
      else { 
         recptr = old ;
         showcurset () ;
         captf("No set %s set %i" , mtxt , old-rec ) ;
         curcmd_loop = cmd_loop ; } 
      return ; }} 
  while ( 1 ) {
       just_marked = 0 ; 
       switch ( x ) { 
            case 0 : break ;
            case 'H': dohlp ( 1 ) ; break ; 
            case 'M' :
                 for ( tmpar = arlist ; tmpar < todo ; ++ tmpar ) {
                     datmp = * tmpar ; 
                     datmp -> mark = 1 ;
                     ++ just_marked ; }
                 break ; 
            case VK_ESCAPE :
                if ( is_cons_duwc ) {
                   curcmd_loop = show_consensus ;
                   show_consensus ( 1 ) ; } 
                else { 
                   recptr = old ;
                   showcurset () ;
                   curcmd_loop = cmd_loop ; }
                return ; 
            case VK_RETURN : case VK_TAB :
               if ( ++ done == todo ) done = arlist ;
               if ( list_the_spp ) show_nth_sp = 0 ;
               break ; 
            case VK_BACK :
                if ( -- done < arlist ) done = todo - 1 ;
                if ( list_the_spp ) show_nth_sp = 0 ;
                break ;
            case VK_NEXT :
              if ( !list_the_spp ) break ;
              show_nth_sp ++ ;
              if ( show_nth_sp == 3 ) show_nth_sp = 0 ;
              break ; 
            case VK_PRIOR :
              if ( !list_the_spp ) break ;
              show_nth_sp -- ;
              if ( show_nth_sp < 0 ) show_nth_sp = 2 ;
              break ;
            case 'v' :
                 if ( !num_spingrid ) break ; 
                 list_the_spp = 1 - list_the_spp ;
                 if ( list_the_spp ) 
                     show_nth_sp = 0 ;
                 break ; 
            default :
               if ( is_cons_duwc ) 
                  curcmd_loop = show_consensus ;
               else { 
                  recptr = old ;
                  showcurset () ; 
                  curcmd_loop = cmd_loop ; }
               return ; } 
       recptr = * done ;
       if ( is_cons_duwc )
           screenf("Consensus Set %i %s %i\n" , 
                     recptr - cons_duwc_start , mtxt , old - cons_duwc_start ) ; 

       else 
          screenf("Set %i %s %i (sizes=%i-%i). Diff=%f.\n" , 
                     recptr - rec , mtxt , old - rec , 
                     recptr->size , old->size , 
                     recptr->score - old->score ) ; 
       drawmap ( old -> lst , recptr -> lst , NULL ) ;

       if ( is_cons_duwc ) {
          anonb = bnona = banda = 0 ;
          apt = recptr -> lst ;
          bpt = old -> lst ; 
          for ( a = arcells ; a -- ; ) {
              anonb += onbits ( * apt & ~ * bpt ) ;
              bnona += onbits ( * bpt & ~ * apt ) ;
              banda += onbits ( * apt & * bpt ) ;
              ++ apt ;
              ++ bpt ; }
          disppt = ( unsigned long int * ) dout ;
          shared = 0 ; 
          if ( list_the_spp ) {
              b = recptr - cons_duwc_start ;
              c = old - cons_duwc_start ;
              refcon = consen + b ; 
              nucon = consen + c ; 
              for ( a = 0 ; a < spp ; ++ a ) {
                  mc = a / 32 ;
                  mb = 1 << ( a % 32 ) ;
                  disppt [ mc ] &= ~mb ; 
                  if ( ! show_nth_sp ) if ( refcon -> spmax [ a ] > 0 && nucon -> spmax[ a ] == 0 ) disppt[mc] |= mb ;  
                  if ( show_nth_sp == 1 ) {
                      if ( refcon -> spmax [ a ] > 0 && nucon -> spmax[ a ] > 0 ) disppt[mc] |= mb ;
                      ++ shared ; }
                  if ( show_nth_sp == 2 ) if ( refcon -> spmax [ a ] == 0 && nucon -> spmax[ a ] > 0 ) disppt[mc] |= mb ; }}
          else for ( a = 0 ; a < spcells ; ++ a ) disppt [a] = 0 ; 
          captf ("%i cells in %i, %i in %i, %i shared" , anonb+banda , recptr - cons_duwc_start , bnona+banda , old - cons_duwc_start , banda ) ;
          if ( list_the_spp && num_spingrid ) {
              cp = screencapt + strlen ( screencapt ) ;
              sprintf ( cp , "\nDistribution of species for " ) ;
              cp += 29 ;
              if ( !show_nth_sp ) sprintf ( cp , "%i" , recptr - cons_duwc_start ) ;
              if ( show_nth_sp == 1 ) { sprintf ( cp , "both" ) ; if ( !shared ) strcat ( cp , " (none!)" ) ; }
              if ( show_nth_sp == 2 ) sprintf ( cp , "%i" , old - cons_duwc_start ) ; }
          } 
       if ( exp != 3 && !is_cons_duwc ) { 
          anonb = bnona = banda = 0 ;
          apt = recptr -> splist ;
          bpt = old -> splist ;
          disppt = ( unsigned long int * ) dout ;
          shared = 0 ; 
          for ( a = spcells ; a -- ; ) {
              if ( list_the_spp ) {
                   if ( !show_nth_sp ) * disppt = ( * apt & ~ * bpt ) ;
                   if ( show_nth_sp == 1 ) { * disppt = ( * apt & * bpt ) ; if ( * disppt ) ++ shared ; }
                   if ( show_nth_sp == 2 ) * disppt = ( * bpt & ~ * apt ) ; }
              else * disppt = 0 ;
              ++ disppt ; 
              anonb += onbits ( * apt & ~ * bpt ) ;
              bnona += onbits ( * bpt & ~ * apt ) ;
              banda += onbits ( * apt & * bpt ) ;
              ++ apt ;
              ++ bpt ; }
          if ( just_marked )
               captf ( "Marked %i sets that %s set %i" , just_marked , mtxt , old-rec ) ;
          else
           if ( ! ignore_sp_lists ) 
               captf( "Scoring spp.: %i common, %i set %i only, %i set %i only" ,
                       banda , anonb , recptr - rec , bnona , old - rec ) ;
           else captf ( "(can't produce spp. lists!)" ) ; 
          if ( list_the_spp && num_spingrid ) {
              cp = screencapt + strlen ( screencapt ) ;
              sprintf ( cp , "\nDistribution of species for " ) ;
              cp += 29 ;
              if ( !show_nth_sp ) sprintf ( cp , "%i" , recptr - rec ) ;
              if ( show_nth_sp == 1 ) { sprintf ( cp , "both" ) ; if ( !shared ) strcat ( cp , " (none!)" ) ; }
              if ( show_nth_sp == 2 ) sprintf ( cp , "%i" , old - rec ) ; }
          } 
       break ; }
    return ; 
} 


void viewmarks ( int ky ) 
{ static Artyp ** done , ** todo , * old ; 
  int a , b ; 
  int x = ky ;
  if ( ky == 0 ) {
    done = todo = arlist ; 
    old = recptr ; 
    recptr = rec - 1 ; 
    for ( a = 0 ; a < numrecs ; ++ a ) { 
       ++ recptr ; 
       if ( recptr -> mark ) * todo ++ = recptr ; } 
    if ( todo == arlist ) { 
      recptr = old ; 
      showcurset () ; 
      captf("\nNO MARKED AREAS" ) ;
      curcmd_loop = cmd_loop ; 
      return ; }}
  while ( 1 ) { 
       switch ( x ) { 
            case 0 : break ; 
            case VK_ESCAPE :
               // recptr = old ;
               showcurset () ;
               curcmd_loop = cmd_loop ; 
               return ;  
            case VK_RETURN : case VK_TAB : case VK_NEXT :
                if ( ++ done == todo ) done = arlist ; break ; 
            case VK_BACK : case VK_PRIOR : if ( -- done < arlist ) done = todo - 1 ; break ;
            case 'v' :
                curcmd_loop = viewscore ; 
                viewscore ( 0 ) ;
                break ; 
            default :
               recptr = old ;
               showcurset () ;
               curcmd_loop = cmd_loop ; 
               return ; } 
       recptr = * done ; 
       screenf("Set %i is marked (size=%i). Score=%f (%i marked sets).\n" , 
                  recptr - rec , 
                  recptr->size , 
                  recptr->score ,
                  todo - arlist ) ; 
       drawmap ( recptr -> lst , NULL , NULL ) ;
       break ; }
    return ; 
} 

void invertmarks ( void ) 
{  Artyp * old ;
   int marks = 0 , numarks = 0 ; 
   for ( old = rec ; old - rec < numrecs ; ++ old )  
      if ( old -> mark ) { old -> mark = 0 ; ++ marks ; }
      else { old -> mark = 1 ; ++ numarks ; }
   myprintf("\nInverted %i marks (%i sets are marked now)" , marks , numarks ) ; 
   return ; 
} 

int getonoff ( int * val ) 
{ char * at = comstring ; 
  while ( * at && isspace ( * at ) ) ++ at ; 
  if ( * at == 'y' ) { 
        if ( * val ) return 0 ; 
        * val = 1 ; return 1 ; } 
  if ( * at == 'n' ) { 
    if ( !*val ) return 0 ; 
    * val = 0 ; return 1 ; } 
} 

int randomize_data ( void )
{  int a , b , c , probone ;
   int32 ranseed ;
   char * at = comstring ;
   while ( * at && isspace ( * at ) ) ++ at ;
   if ( !isdigit ( * at ) ) {
        showcurset () ;
        captf("\nGive probability of presence" ) ;
        return 0 ; }
   probone = atoi ( at ) ;
   if ( probone < 1 || probone > 99 ) {
       showcurset () ;
       captf ("\nProbability of presence must be 1-99" ) ;
       return 0 ; }
   time ( &ranseed ) ; 
   srand ( ( int32 ) ranseed ) ; 
   for ( a = rows ; a -- ; )
       for ( b = cols ; b -- ; ) {
          if ( !isdefd [ a ] [ b ] ) continue ; 
          for ( c = spcells ; c -- ; ) matrix [ a ] [ b ] [ c ] = 0 ; 
          for ( c = spp ; c -- ; ) 
               if ( ( rand () % 100 ) < probone ) {
                    numentries [ c ] ++ ; 
                    matrix [ a ] [ b ] [ c / 32 ] |= 1 << ( c % 32 ) ; }}
   spingrid = NULL ;
   num_spingrid = 0 ; 
   doallscores () ; 
   showcurset () ;
   captf ("Created random data, p(pres)=%i" , probone ) ; 
   return 0 ;
}


void show_singles ( void )
{
    int a , b , c , nusp , numar ;
    int32 cell , shif ;
    for ( a = spcells ; a -- ; ) dablor [ a ] = dabland [ 0 ] ;
    for ( a = rows ; a -- ; )
        for ( b = cols ; b -- ; )
            for ( c = spcells ; c -- ; ) {
                  dabland [ c ] |= ( dablor [ c ] & matrix [ a ] [ b ] [ c ] ) ; 
                  dablor  [ c ] |= matrix [ a ] [ b ] [ c ] ; }
    for ( c = spcells ; c -- ; ) dablor [ c ] &= ~ dabland [ c ] ;
    for ( a = arcells ; a -- ; ) splist [ a ] = 0 ;
    for ( a = rows ; a -- ; )
        for ( b = cols ; b -- ; ) {
            nusp = 0 ;
            for ( c = spcells ; c -- ; )
               nusp += onbits ( ( dablor[c] & matrix [a][b][c] ) ) ;
            if ( nusp < 2 ) continue ; 
            numar = ( a * cols ) + b ;
            cell = numar / 32 ;
            shif = 1 << ( numar % 32 ) ;
            splist [ cell ] |= shif ; }
    screenf("Cells with unique species > 1\n" ) ; 
    drawmap ( splist , NULL , NULL ) ;
    return ;
}



int show_empty_cells ( void )
{
    int a , x , y , mc , ac , numar , somexs , tellexs ; 
    int32 mb , ab ; 
    for ( a = arcells ; a -- ; ) {
        splist [ a ] = ~0 ;
        inflist [ a ] = 0 ; } 
    for ( y = 0 ; y < rows ; ++ y ) 
        for ( x = 0 ; x < cols ; ++ x ) {
            if ( !isdefd [ y ] [ x ] ) continue ;
            numar = ( y * cols ) + x ;
            ac = numar / 32 ;
            ab = 1 << ( numar % 32 ) ;
            somexs = 0 ; 
            for ( a = spp ; a -- ; ) {
                mc = a / 32 ;
                mb = 1 << ( a % 32 ) ;
                if ( ( matrix [ y ] [ x ] [ mc ] & mb ) ) {
                    inflist [ ac ] &= ~ab ;
                    somexs = 0 ; 
                    splist [ ac ] &= ~ab ;
                    break ; }
                if ( ( assmatrix [ y ] [ x ] [ mc ] & mb ) ) {
                    inflist [ ac ] |= ab ;
                    somexs = 1 ; }}
            if ( somexs ) tellexs = 1 ; }
   screenf( "Cells with no species:" ) ;
   drawmap ( splist , inflist , NULL ) ;
   return 0 ;
} 

extern int sometextodo ; 
extern char screenmsg[1000] ; 

int first_time_weights = 1 ;
                    
void cmd_loop ( int x ) 
{  
    int a ;
    double tmp ; 
    int32 b ; 
    char * at ; 
    Artyp * recwas ; 
    if ( !grid_created ) {
        if ( ( x == VK_RETURN || x == ESC ) ) {
               sometextodo = 0 ;
               win_refresh () ; }
        if ( x != 'o' && x != '?' && x != VK_F6 && x != 'X' && x != 'H' ) return ; }
    while ( 1 ) {
              switch ( x ) { 
                   case 0 : case ' ' : break ; 
                   case ESC:
                     sometextodo = 0 ;
                     showcurset () ; 
                     win_refresh () ; 
                     break ; 
                   case 'X' :
                        if ( sure ( "Sure you want to quit" )) dobyebye () ;
                        break ; 
                   case VK_RETURN : case VK_TAB : case VK_NEXT : 
                      if ( ++ recptr >= rec + numrecs ) recptr = rec ;
                      if ( redoallscores ) doallscores () ; 
                      showcurset () ;
                      break ; 
                   case VK_BACK : case VK_PRIOR : 
                      if ( -- recptr < rec ) recptr = ( rec + numrecs ) - 1 ;
                      if ( redoallscores ) doallscores () ; 
                      showcurset () ;
                      break ;
                   case VK_HOME :
                      recptr = rec ;
                      if ( redoallscores ) doallscores () ; 
                      showcurset () ;
                      break ;
                   case VK_F6 :
                      if ( grid_created || !nummaplins ) break ; 
                      read_cursor_shift () ;
                      break ; 
                   case VK_END :
                     recptr = ( rec + numrecs ) - 1 ;
                      if ( redoallscores ) doallscores () ; 
                     showcurset () ;
                     break ;
                   case 'S' :
                      showspecies ( 0 ) ; 
                      curcmd_loop = showspecies ; 
                      break ; 
                   case 'G' :
                       show_coordinates = 1 - show_coordinates ;
                       win_refresh () ; 
                       break ;
                   case '/' :
                      if ( outspace == NULL ) {
                          MessageBox ( hwnd , "To shrink data, must\nopen output file first!" , "Error" , MB_OK | MB_ICONERROR ) ;
                          break ; }
                      divide_data () ;
                      break ;
                   case 'n' : x = show_empty_cells () ; break ; 
                   case 'g' : 
                      recwas = recptr ; 
                      recptr = rec + atoi ( comstring ) ; 
                      if ( recptr < rec || recptr >= rec + numrecs ) recptr = recwas ;
                      if ( redoallscores ) doallscores () ; 
                      showcurset () ; 
                      break ; 
                   case 'H' : dohlp ( 1 ) ; break ; 
                   case 'N' : 
                          donewset () ;
                          showcurset () ; 
                          break ; 
                   case 'w':
                         if ( comstring[0] == '-' ) {
                             weight_species = 0 ;
                             showcurset () ; 
                             sprintf ( junkstr , "Not weighting species" ) ;
                             captf ( junkstr ) ;
                             break ; }
                         if ( !isdigit ( comstring[0] ) && comstring[0] != '.' ) break ;
                         weight_species = 1 ; 
                         tmp = atof ( comstring ) ;
                         if ( tmp < 0 || tmp > 1 ) {
                             errmsg ( "Minimum taxon weight must be >= 0 and <= 1 " , Null ) ;
                             break ; }
                         if ( weight_min != tmp || first_time_weights ) {
                             first_time_weights = 0 ; 
                             weight_min = tmp ;
                             initialize_species_weights () ;
                             redoallscores = 1 ;
                             doallscores () ; }
                         showcurset () ; 
                         sprintf ( junkstr , "Minimum taxon weight is now %f" , weight_min ) ;
                         captf ( junkstr ) ;
                         break ;      
                   case 'b' :
                         if ( !isdigit ( comstring[0] ) && comstring[0] != '.' ) break ; 
                         tmp = atof ( comstring ) ;
                         if ( tmp < 0 || tmp > 1 ) {
                             errmsg ( "Species score must be between 0 and 1" , Null ) ;
                             break ; }
                         if ( minimum_sp_score != tmp ) {
                             minimum_sp_score = tmp ;
                             redoallscores = 1 ;
                             doallscores () ; }
                         showcurset () ; 
                         sprintf ( junkstr , "Minimum score for a species to be considered \"endemic\" is %f" , minimum_sp_score ) ;
                         captf ( junkstr ) ;
                         break ;      
                   case '9' :
                         if ( !isdigit ( comstring[0] ) && comstring[0] != '.' ) {
                             showcurset () ;
                             captf ( "\nMust give similarity (between 0.00 and 1.00) to display" ) ;
                             break ; }
                         curcmd_loop = showsuperset ; 
                         showsuperset ( 0 ) ;
                         break ;
                   case 'D' :
                   case 'C' :
                   case 'W' :
                   case 'U' :
                   case '=' :
                   case 'J' :
                         cur_duwc_act = x ; 
                         curcmd_loop = show_duwc ;
                         is_cons_duwc = 0 ; 
                         show_duwc ( 0 ) ;
                         break ;
                   case 'Q' : handle_querymode () ; break ;
                   case 'A' : auto_fill_all_records () ; break ;  
                   case 'F' :
                        curcmd_loop = showfauna ; 
                        showfauna ( 0 ) ;
                        break ; 
                   case 'V' :
                      curcmd_loop = viewmarks ; 
                      viewmarks ( 0 ) ;
                      break ; 
                   case 'v' :
                       curcmd_loop = viewscore ; 
                       viewscore ( 0 ) ;
                       break ; 
                   case 1 :
                       curcmd_loop = show_consensus ; 
                       show_consensus ( 0 ) ;
                       break ; 
                   case ALTDEL :
                       deleteset () ;
                       showcurset () ; 
                       break ; 
                   case 'l' :
                       logsetsonly = 0 ;
                       logtofile () ;
                       break ;
                   case 'L' :
                       logsetsonly = 1 ;
                       logtofile () ;
                       break ;
                   case 'o' : outputfile () ; break ; 
                   case 's' :
                      if ( outspace == NULL ) { 
                          errmsg ("Must open output file before saving!" , Null ) ; 
                          return ; } 
                      savetofile () ; break ;  
                   case 'm' : handle_marks () ; break ;
                   case 'f' : handle_factors () ; break ; 
                   case 'P'  : handle_compare_perc () ; break ; 
                   case 'x' : handle_fuses () ; break ; 
                   case 'p' :
                        a = use_edge_props ; 
                        getonoff ( &use_edge_props ) ; 
                        if ( a != use_edge_props ) doallscores () ; 
                        showcurset () ;
                        if ( use_edge_props ) captf ( "Using edge proportions" ) ;
                        else captf ( "Not using edge proportions" ) ; 
                        break ; 
                   case 'e' : 
                           at = comstring ; 
                           while ( isspace ( * at ) && * at ) ++ at ; 
                           if ( isdigit ( * at ) ) { 
                               a = atoi ( at ) ; 
                               if ( a < 1 && a > 8 ) { 
                                  captf("Empty cells must be 1-8" ) ; 
                                  break ; } 
                               if ( a != abslim ) { 
                                   abslim = a ; 
                                   doallscores () ; }}
                           showcurset () ; 
                           captf("Abs. limit is %i" , abslim ) ;
                           break ; 
                   case 'd' : delete_duplicates ( 1 ) ; break ;
                   case 189: 
                   case '-' : clean_areas () ; break ; 
                   case ALT1 : show_singles () ; break ; 
                   case 'h' :
                       a = musthaveone ; 
                       if ( isdigit ( comstring[0] ) ) {
                          a = atoi ( comstring ) ;
                          if ( a < 0 || a > 2 ) {
                              errmsg ( "One full cell around must be 0-2:\n   0   don't require\n   1   require only for non-assumed cells\n   2   require for all\n" ) ;
                              return ; }}
                       if ( a != musthaveone ) {
                           musthaveone = a ; 
                           doallscores () ; }
                       showcurset () ; 
                       if ( musthaveone ) {
                           if ( musthaveone == 2 ) captf("Must have one adjacent full cell (for all cells)" ) ;
                           else captf("Must have one adjacent full cell (for all unassumed cells)" ) ; }
                       else captf("Adjacent full cell not required" ) ; 
                       break ; 
                   case 'a' : x = randomize_data () ; doallscores () ; break ; 
                   case 'I' : invertmarks () ; break ;
                   case 'E' :
                      if ( !sure ( "Sure you want to empty current set" ) ) break ;
                      emptycurset () ;
                      break ; 
                   case 'M' :
                      a = recptr -> mark ;
                      a = 1 - a ;
                      recptr -> mark = a ;
                      showcurset () ; 
                      break ;
                   case 'K' : fill_widefilter () ; break ;
                   case '?' :
                       process_line_file ( ) ;
                       break ; 
                   case 'R' :
                      read_sets_from_file ( ) ;
                      break ; 
                   default : noisy () ; break ; }
       break ; }
    return ; 
} 

void * mymem ( int siz )
{
    char * p ;
    p = ( char * ) malloc ( siz ) ;
    if ( p == NULL ) 
            ermsg ( "\nNot enough memory to run\n" ) ;
    return ( char * ) p ;
} 

void get_spname ( int numsp )
{
    char x = ' ' ;
    int a , readnames = 0 , readfills = 0 ;
    char * cp ; 
    while ( isspace ( x ) && !feof ( infile ) ) x = getc ( infile ) ;
    if ( x != '[' && x != '(' ) { ungetc ( x , infile ) ; return ; }
    while ( ( x == '(' || x == '[' ) && !feof ( infile ) ) {
         if ( x == '[' ) {
            readnames = 1 ; 
            if ( spname == NULL ) {
                spname = ( char * ) mymem ( spp * sizeof ( char * ) ) ;
                for ( a = 0 ; a < spp ; ++ a ) spname[a] = NULL ; }
            if ( spname[numsp] == NULL ) 
                spname[numsp] = mymem ( Spnamesz * sizeof ( char ) ) ;
            cp = spname[numsp] ; 
            a = 0 ;
            x = ' ' ;
            while ( isspace ( x ) && !feof ( infile ) ) x = getc ( infile ) ; 
            while ( x != ']' && !feof ( infile ) ) {
                    if ( cp - spname[numsp] < Spnamesz - 1 ) 
                         *cp ++ = x ;
                    x = getc ( infile ) ; }
           * cp = '\0' ;
           if ( !readfills ) {
              x = ' ' ; 
              while ( isspace ( x ) && !feof ( infile ) ) x = getc ( infile ) ;
             if ( x != '(' ) { ungetc ( x , infile ) ; return ; }}}
        else {
            if ( ind_fills == NULL ) {
                ind_fills = mymem ( spp * sizeof ( Filltyp ) ) ;
                for ( a = 0 ; a < spp ; ++ a ) ind_fills[a].fillx = -1 ; }
            a = fscanf ( infile , "%f %f %f %f" , &(ind_fills[numsp].fillx) , &(ind_fills[numsp].filly) , &(ind_fills[numsp].assx) , &(ind_fills[numsp].assy) ) ;
            if ( a != 4 ) ermsg ( "Individual species fill must consist of four numbers:\nradius-X, radius-Y, assumed radius-X, assumed radius-Y,\nindicated as percentages of cell width/height" ) ;
            x = ' ' ; while ( isspace ( x ) && !feof ( infile ) ) x = getc ( infile ) ;
            if ( x != ')' ) ermsg ( "Individual species fill must end with a closing parentehesis" ) ;
            if ( !readnames ) {
                x = ' ' ; while ( isspace ( x ) && !feof ( infile ) ) x = getc ( infile ) ;
                if ( x != '[' ) { ungetc ( x , infile ) ; return ; }}}}
    return ; 
}   

void set_unnamed_spp ( void )
{
    int a ;
    if ( spname == NULL ) return ; 
    for ( a = 0 ; a < spp ; ++ a )
       if ( spname[a] == NULL ) {
           spname[a] = ( char * ) mymem ( Spnamesz * sizeof ( char ) ) ;
           sprintf ( spname[a] , "%i unnamed" , a ) ; }
    return ; 
}


int gonotblank ( FILE * fil )
{
    int x = ' ' ;
    while ( isspace ( x ) && !feof ( fil ) ) x = getc ( fil ) ;
    return x ; 
}    

int it_is_a_line_file ( char * str )
{
    char * cp = str ;
    int a ; 
    while ( * cp ) ++ cp ;
    if ( cp - str < 5 ) return 0 ;
    cp -= 3 ;
    for ( a = 0 ; a < 3 ; ++ a ) cp[a] = tolower(cp[a]); 
    if ( strcmp ( cp , "lin" ) ) return 0 ;
    else return 1 ;
}    

int eat_comma_preceded_nr ( int basic )
{
    int x ;
    float nada ;
    if ( nocommas ) return 0 ; 
    x = getc ( infile ) ;
    while ( isspace ( x ) ) x = getc ( infile ) ;
    if ( x == ',' ) {
        x = ' ' ;
        while ( isspace ( x ) ) x = getc ( infile ) ;
        if ( !isdigit ( x ) && x != '.' && x != '-' )
            if ( basic ) 
                  ermsg ( "Commas must be followed by a number\n(or indicate \"nocommas\" in the input file)" ) ;
            else ermsg ( "Commas must be followed by a number\n(or de-select \"File/UseCommaSeparator\")" ) ;
        if ( x != '-' ) ungetc ( x , infile ) ;
        fscanf ( infile , "%f" , &nada ) ;
        return 1 ; }
    ungetc ( x , infile ) ; 
    return 0 ; 
}
    
void read_map_definition ( int basic )
{ char str [ 10 ] , * cp ; 
  float * tmprec , * sptr ;
  Tmptyp * tmppr ;
  float wid , hei , cellwid , cellhei , startx , starty , xbeg , ybeg , xend , yend ;
  float myx , myy ; 
  int a , b , c , d , x ;
  int numsp , read , at ;
  int tmpsign ; 
  float xrad , yrad ;
  float inx , iny , tmpdouble ;
  int myR , myG, myB, mythick ;
  int isfirst ;
  float firsx , firsy ; 
  if ( maplin == NULL ) {
      maplin = ( Maplintyp * ) mymem ( MAXNUMLINS * sizeof ( Maplintyp ) ) ; 
      tmpcord = ( Tmptyp * ) mymem ( ( MAXLINPTS + 1 ) * sizeof ( Tmptyp ) ) ; }
  x = ' ' ; 
  myR = myG = myB = 0 ; 
  mythick = 2 ;
  while ( !feof ( infile ) ) {
           while ( isspace ( x ) )
               x = getc ( infile ) ;
           if ( x == '(' ) {
               fscanf ( infile , "%i" , &myR ) ;
               if ( gonotblank( infile ) != ',' ) {
                  errmsg ( "Values of RGB in line color definition must be separated by commas" ) ;
                  exit ( 0 ) ; }
               fscanf ( infile , "%i" , &myG ) ;
               if ( gonotblank( infile ) != ',' ) {
                  errmsg ( "Values of RGB in line color definition must be separated by commas" ) ;
                  exit ( 0 ) ; }
               fscanf ( infile , "%i" , &myB ) ;
               if ( gonotblank( infile ) != ',' ) {
                  errmsg ( "Values of RGB in line color definition must be separated by commas" ) ;
                  exit ( 0 ) ; }
               fscanf ( infile , "%i" , &mythick ) ;
               if ( gonotblank ( infile ) != ')' ) {
                   errmsg ( "Expected a closing parenthesis for line color definition" ) ;
                   exit ( 0 ) ; }
               x = ' ' ;
               continue ; } 
           cp = str ; 
           while ( !isspace ( x ) ) {
               * cp ++ = tolower ( x ) ;
               x = getc ( infile ) ; }
           * cp = '\0' ;
           if ( !strcmp ( str , "nocommas" ) ) { nocommas = 1 ; continue ; }
           if ( !strcmp ( str , "xpositive" ) ) { xsign = ysignmap = 1 ; continue ; }
           if ( !strcmp ( str , "ypositive" ) ) { ysign = ysignmap = -1 ; continue ; }
           if ( !strcmp ( str , "ynegative" ) ) { ysign = ysignmap = 1 ; x = ' '  ; continue ; }
           if ( !strcmp ( str , "xnegative" ) ) { xsign = xsignmap = 1 ; x = ' '  ; continue ; }
           if ( !strcmp ( str , "longlat" ) ) { dolatlong = 0 ; x = ' ' ; continue ; }
           if ( !strcmp ( str , "latlong" ) ) { dolatlong = 1 ; x = ' ' ; continue ; }
           if ( strcmp ( str , "line" ) ) {
               fprintf ( stderr , "\nError reading map definition (line %i)\n" , nummaplins ) ;
               ermsg ("Give xy data with line x y" ) ; }
           tmppr = tmpcord ;
           isfirst = 1 ; 
           while ( 1 ) {
              if ( tmppr - tmpcord >= MAXLINPTS ) {
                   read = tmppr - tmpcord ;
                   maplin[nummaplins].numpoints = read ;
                   a = read + 100 ;
                   if ( a < 300 ) a = 500 ; 
                   maplin[nummaplins].x = ( float * ) mymem ( a * sizeof ( float ) ) ; 
                   maplin[nummaplins].y = ( float * ) mymem ( a * sizeof ( float ) ) ; 
                   at = tmppr - tmpcord ;
                   maplin[nummaplins].x[at] = (tmppr-1)->x ; 
                   maplin[nummaplins].y[at] = (tmppr-1)->y ;
                   maplin[nummaplins].colR = myR ; 
                   maplin[nummaplins].colG = myG ; 
                   maplin[nummaplins].colB = myB ; 
                   maplin[nummaplins].thickness = mythick ; 
                   while ( at -- ) {
                          -- tmppr ; 
                          maplin[nummaplins].x[at] = tmppr->x ; 
                          maplin[nummaplins].y[at] = tmppr->y ; }
                   ++ nummaplins ;
                   if ( nummaplins >= MAXNUMLINS ) ermsg ( "Too many points/lines in file" ) ; 
                   tmpcord[0].x = tmpcord[read-1].x ; 
                   tmpcord[0].y = tmpcord[read-1].y ; 
                   tmppr = tmpcord + 1 ; }
              x = getc ( infile ) ;
              while ( isspace ( x ) ) x = getc ( infile ) ;
              if ( !isdigit ( x ) && x != '.' && x != '-' ) break ;
              if ( feof ( infile ) ) break ;
              tmpsign = 1 ;
              if ( x != '-' ) ungetc ( x , infile ) ;
              else tmpsign = -1 ; 
              fscanf ( infile , " %f" , &inx ) ;
              if ( !nocommas ) {
                   x = ' ' ;
                   while ( isspace ( x ) ) x = getc ( infile ) ; 
                   if ( x != ',' ) ermsg ( "All values for each point must be comma-separated\n(or de-select \"File/UseCommaSeparator\")" ) ;
                   while ( isspace ( x ) ) x = getc ( infile ) ; }
              inx = inx * tmpsign ; 
              if ( !fscanf ( infile , " %f" , &iny ) )
                   ermsg ( "All values of x-y must be given in pairs!") ;
              while ( eat_comma_preceded_nr ( basic ) ) ; 

              /**  IGNORE LINE IF IT CONNECTS BACK TO STARTING POINT! ****/
              if ( isfirst ) {
                  isfirst = 0 ;
                  firsx = inx ;
                  firsy = iny ; }
              else
                if ( firsx == inx && firsy == iny ) {
                   read = tmppr - tmpcord ;
                   maplin[nummaplins].numpoints = read ;
                   a = read + 100 ;
                   if ( a < 300 ) a = 300 ; 
                   maplin[nummaplins].x = ( float * ) mymem ( a * sizeof ( float ) ) ; 
                   maplin[nummaplins].y = ( float * ) mymem ( a * sizeof ( float ) ) ; 
                   at = tmppr - tmpcord ;
                   maplin[nummaplins].x[at] = (tmppr-1)->x ; 
                   maplin[nummaplins].y[at] = (tmppr-1)->y ;
                   maplin[nummaplins].colR = myR ; 
                   maplin[nummaplins].colG = myG ; 
                   maplin[nummaplins].colB = myB ; 
                   maplin[nummaplins].thickness = mythick ; 
                   while ( at -- ) {
                          -- tmppr ; 
                          maplin[nummaplins].x[at] = tmppr->x ; 
                          maplin[nummaplins].y[at] = tmppr->y ; }
                   ++ nummaplins ;
                   if ( nummaplins >= MAXNUMLINS ) ermsg ( "Too many points/lines in file" ) ; 
                   tmppr = tmpcord ;
                   isfirst = 1 ; 
                   continue ; }
              if ( transposexymap ) {
                   tmpdouble = inx ;
                   inx = iny ;
                   iny = tmpdouble ; }
              else if ( dolatlong ) {
                   tmpdouble = inx ;
                   inx = iny ;
                   iny = tmpdouble ; }
              inx = inx * xsignmap ; 
              inx = ( ( inx - mminusxmap ) * mfactormap ) ;
              tmppr -> x = inx ; 
//              if ( tmppr -> x > maxx ) maxx = tmppr -> x ; 
//              if ( tmppr -> x < minx ) minx = tmppr -> x ; 
              iny = iny * ysignmap ;
              iny = ( ( iny - mminusymap ) * mfactormap ) ;
              tmppr -> y = iny ; 
//              if ( tmppr -> y > maxy ) maxy = tmppr -> y ; 
//              if ( tmppr -> y < miny ) miny = tmppr -> y ;
              ++ tmppr ; }
           read = tmppr - tmpcord ;
           maplin[nummaplins].numpoints = read ;
           a = read + 100 ;
           if ( a < 300 ) a = 500 ; 
           maplin[nummaplins].x = ( float * ) mymem ( a * sizeof ( float ) ) ; 
           maplin[nummaplins].y = ( float * ) mymem ( a * sizeof ( float ) ) ; 
           at = tmppr - tmpcord ;
           maplin[nummaplins].x[at] = (tmppr-1)->x ; 
           maplin[nummaplins].y[at] = (tmppr-1)->y ;
           maplin[nummaplins].colR = myR ; 
           maplin[nummaplins].colG = myG ; 
           maplin[nummaplins].colB = myB ; 
           maplin[nummaplins].thickness = mythick ; 
           while ( at -- ) {
                  -- tmppr ; 
                  maplin[nummaplins].x[at] = tmppr->x ; 
                  maplin[nummaplins].y[at] = tmppr->y ; }
           ++ nummaplins ; }
    return ;
}

void process_line_file ( void )
{
    if ( comstring[0] == '\0' ) return ;
    infile = fopen ( comstring , "rb" ) ;
    read_map_definition ( 0 ) ;
    fclose ( infile ) ; 
}    

int records_read = 0 ; 

void numerr ( char * what )
{
    sprintf ( junkstr , "String \"%s\" must be followed by a number" , what ) ;
    ermsg ( junkstr ) ; 
}

void read_xydata ( void )
{ char str [ 10 ] , * cp ; 
  float * tmprec , * sptr ;
  Tmptyp * tmppr , * chkcor ;
  float wid , hei , cellwid , cellhei , startx , starty , xbeg , ybeg , xend , yend ;
  float myx , myy ; 
  int a , b , c , d , x , i , isnu ;
  int numsp , read , at ;
  float xrad , yrad ;
  float inx , iny , tmpdouble ;
  signed int rows_was ;
  int maxsp = 0 , theospp ;
  int resetspp = -1 ;
  double ad ; 
  data_is_xydata = 1 ; 
  spcells = ( spp + 31 ) / 32 ; 
  maplin = NULL ; 
  xymatrix = ( Coordtyp * ) mymem ( spp * sizeof ( Coordtyp ) ) ;
  for ( a = spp ; a -- ; ) xymatrix[a].defd = xymatrix[a].numrecs = 0 ; 
  tmpcord = ( Tmptyp * ) mymem ( MAXY * sizeof ( Tmptyp ) ) ; 
  x = ' ' ; 
  while ( !feof ( infile ) ) {
           while ( isspace ( x ) ) x = getc ( infile ) ;
           if ( feof ( infile ) ) break ; 
           cp = str ; 
           while ( !isspace ( x ) ) {
               * cp ++ = tolower ( x ) ;
               x = getc ( infile ) ;
               if ( feof ( infile ) ) break ; }
           * cp = '\0' ;

       if ( !strcmp ( str , "nocommas" ) ) { nocommas = 1 ; continue ; }
       if ( !strcmp ( str , "transpose" ) ) { transposexy = 1 ; continue ; }
       if ( !strcmp ( str , "notranspose" ) ) { transposexy = 0 ; continue ; }
       if ( !strcmp ( str , "latlong" ) ) { dolatlong = 1 ; continue ; }
       if ( !strcmp ( str , "longlat" ) ) { dolatlong = 0 ; continue ; }
       if ( !strcmp ( str , "xnegative" ) ) { xsign = -1 ; continue ; }
       if ( !strcmp ( str , "ynegative" ) ) { ysign = 1 ; continue ; }
       if ( !strcmp ( str , "xpositive" ) ) { xsign = 1 ; continue ; }
       if ( !strcmp ( str , "ypositive" ) ) { ysign = -1 ; continue ; }

          if ( !strcmp ( str , "groups" ) ) {
                theospp = spp ; 
                spp = maxsp + 1 ; 
                get_species_tree (theospp , 0 ) ;
                x = ' ' ;
                continue ; }
           if ( !strcmp ( str , "map" ) ) {
               spp = maxsp + 1 ; 
               read_map_definition ( 1 ) ;
               break ; }
           if ( !strcmp ( str , "*" ) ) {
                resetspp = maxsp + 1 ; 
                continue ; }
           if ( species_tree != NULL ) continue ; 
           if ( strcmp ( str , "sp" ) ) {
               if ( numsp >= 0 ) 
                     sprintf ( junkstr , "\nError reading data for sp. %i (%s)\n" , numsp , spname[ numsp ] ) ;
               else sprintf ( junkstr , "\nError expecting data data for first sp.\n" ) ;
               strcat ( junkstr , "Give xy data with sp N [x][y]" ) ; 
               ermsg ( junkstr ) ; } 
           if ( !fscanf ( infile , " %i" , &numsp ) ) ermsg ( "Must give species number after \"sp\"") ;
           if ( resetspp > 0 ) numsp += resetspp ; 
           if ( numsp > maxsp ) maxsp = numsp ;  
           if ( numsp >= spp ) ermsg ( "Wrong species number" ) ;
/*
           if ( xymatrix[numsp].defd ) {
                   sprintf ( junkstr ,"\nValues for sp. %i already defined\n" , numsp ) ; 
                   ermsg ( junkstr ) ; }
*/
           get_spname ( numsp ) ; 
           tmppr = tmpcord ;
           while ( 1 ) {
              if ( tmppr - tmpcord >= MAXY ) {
                  sprintf ( junkstr ,"Cannot read more than %i records per species\n" , MAXY ) ;
                  ermsg ( junkstr ) ; }
              x = getc ( infile ) ;
              while ( isspace ( x ) ) x = getc ( infile ) ;
              if ( !isdigit ( x ) && x != '.' && x != '-' ) break ;
              if ( feof ( infile ) ) break ;
              ungetc ( x , infile ) ;
              fscanf ( infile , " %f" , &inx ) ;
              if ( !nocommas ) {
                  x = ' ' ;
                  while ( isspace ( x ) ) x = getc ( infile ) ; 
                  if ( x != ',' ) ermsg ( "All values for each point must be comma-separated\n(or indicate \"nocommas\" in the input file)" ) ;
                  while ( isspace ( x ) ) x = getc ( infile ) ; }
              if ( !fscanf ( infile , " %f" , &iny ) )
                   ermsg ( "All values of x-y must be given in pairs!") ;
              while ( eat_comma_preceded_nr ( 1 ) ) ;
              if ( transposexy ) {
                   tmpdouble = inx ;
                   inx = iny ;
                   iny = tmpdouble ; }
              else if ( dolatlong ) {
                      tmpdouble = inx ;
                      inx = iny ;
                      iny = tmpdouble ; }
              inx = inx * xsign ; 
              inx = ( ( inx - mminusx ) * mfactor ) ;
              tmppr -> x = inx ;
              if ( tmppr -> x > maxx ) maxx = tmppr -> x ; 
              if ( tmppr -> x < minx ) minx = tmppr -> x ; 
              iny = iny * ysign ;
              iny = ( ( iny - mminusy ) * mfactor ) ;
              tmppr -> y = iny ; 
              if ( tmppr -> y > maxy ) maxy = tmppr -> y ; 
              if ( tmppr -> y < miny ) miny = tmppr -> y ; 
              isnu = 1 ;
              for ( chkcor = tmpcord ; chkcor < tmppr && isnu ; ++ chkcor )
                  if ( ( tmppr -> x == chkcor -> x ) && ( tmppr -> y == chkcor -> y ) ) isnu = 0 ; 
              if ( isnu ) 
                  ++ tmppr ; }
           read = tmppr - tmpcord ;
           records_read += read ; 
           // added march 5, 2020, to enable reading species in separate chunks
           if ( xymatrix[numsp].defd ) {
               for ( at = 0 ; at < xymatrix[numsp].numrecs ; ++ at ) {
                   if ( tmppr - tmpcord >= MAXY ) {
                        sprintf ( junkstr ,"Cannot read more than %i records per species\n" , MAXY ) ;
                        ermsg ( junkstr ) ; }
                   isnu = 1 ; 
                   for ( i = 0 ; i < read && isnu ; ++ i ) 
                       if ( tmpcord[i].x == xymatrix[ numsp ].x[at] &&
                            tmpcord[i].y == xymatrix[ numsp ].y[at] ) isnu = 0 ; 
                   if ( !isnu ) continue ;                         
                   tmppr -> x = xymatrix [ numsp ].x[at] ; 
                   tmppr -> y = xymatrix [ numsp ].y[at] ;
                   ++ tmppr ; }
               read = tmppr - tmpcord ;
               free ( xymatrix [ numsp ].x ) ; 
               free ( xymatrix [ numsp ].y ) ; }
           xymatrix[numsp].defd = 1 ; 
           xymatrix [ numsp ].x = ( float * ) mymem ( ( read + 1 ) * sizeof ( float ) ) ; 
           xymatrix [ numsp ].y = ( float * ) mymem ( ( read + 1 ) * sizeof ( float ) ) ; 
           at = 0 ; 
           while ( tmppr > tmpcord ) {
                  -- tmppr ;
                  xymatrix[numsp].x[at] = tmppr->x ; 
                  xymatrix[numsp].y[at] = tmppr->y ;
                  ++ at ; }
           xymatrix[numsp].numrecs = read ; }
   set_unnamed_spp ( ) ; 
   spcells = ( ( ( 2 * spp ) + 31 ) / 32 ) ;   // multiply by TWO, so that you can fit all tree nodes... 
   memerr ( spingrid = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ;
   for ( a = 0 ; a < spcells ; ++ a ) spingrid[a] = -1 ;
   num_spingrid = spp ;
   rows_was = rows ; 
   if ( rows < 0 ) {
       if ( grid_startx < 10e200 ) {
           truecellwid = grid_width ; 
           truecellhei = grid_height ; 
           cols = ( int ) ( ( maxx - minx ) / truecellwid ) + 1 ; 
           rows = ( int ) ( ( maxy - miny ) / truecellhei ) + 1 ; }
       else {
          rows = cols = 10 ; 
          truecellwid = ( maxx - minx ) / (cols-1 )  ; 
          truecellhei = ( maxy - miny ) / (rows-1) ;
          a = truecellhei * 100 ; 
          b = truecellwid * 100 ;
          truecellhei = ( double ) a / 100 ; 
          truecellwid = ( double ) b / 100 ; }}
   else {
      truecellwid = ( maxx - minx ) / (cols-1 )  ; 
      truecellhei = ( maxy - miny ) / (rows-1) ; }
   if ( grid_startx > 10e199 ) { 
      grid_startx = minx - ( truecellwid / 2 ) ;          // i.e. only assign a start if user did not specify it in file
      a = ( int ) grid_startx ;
      grid_startx = a ; } 
   if ( grid_starty > 10e199 ) { 
      grid_starty = miny - ( truecellhei / 2 ) ;
      a = ( int ) grid_starty ;
      grid_starty = a ; } 
   if ( grid_startx > 10e199 ) {
      while ( grid_startx +
             ( truecellwid * ( cols - 1 ) ) < maxx ) truecellwid += 0.01 ; 
      while ( grid_starty +
             ( truecellhei * ( rows - 1 ) ) < maxy ) truecellhei += 0.01 ; }
   else
     if ( rows_was < 0 ) {
      while ( grid_startx +
             ( truecellwid * ( cols - 1 ) ) < maxx ) ++ cols ; 
      while ( grid_starty +
             ( truecellhei * ( rows - 1 ) ) < maxy ) ++ rows ; }
   if ( species_tree != NULL ) 
        add_group_coordinates () ;
   else numterminals = spp ; 
   memerr ( species_weight = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( spminmax = ( MinMaxtyp * ) malloc ( spp * sizeof ( MinMaxtyp ) ) ) ; 
   return ; 
}

void reset_grid_magnitude ( void )
{
   int a , b ;
   double valx , valy ; 
   maxx = maxy = -1000000 ;
   minx = miny = 1000000000 ;
   for ( a = 0 ; a < spp ; ++ a )
        for ( b = 0 ; b < xymatrix[a].numrecs ; ++ b ) {
            valx = xymatrix[a].x[b] ;
            valy = xymatrix[a].y[b] ;
            if ( maxx < valx ) maxx = valx ; 
            if ( maxy < valy ) maxy = valy ; 
            if ( minx > valx ) minx = valx ; 
            if ( miny > valy ) miny = valy ; }
   while ( grid_startx +
           ( truecellwid * ( cols - 1 ) ) < maxx ) truecellwid += 0.01 ; 
   while ( grid_starty +
           ( truecellhei * ( rows - 1 ) ) < maxy ) truecellhei += 0.01 ; 
   grid_startx = minx - ( truecellwid / 2 ) ;
   grid_starty = miny - ( truecellhei / 2 ) ;
   return ; 
}

int isxflipped = 0 , isyflipped = 0 , istransposed = 0 ; 

void transpose_xy ( void )
{
   int a , b ;
   double val , bal ; 
   istransposed = 1 - istransposed ; 
   for ( a = 0 ; a < spp ; ++ a )
        for ( b = 0 ; b < xymatrix[a].numrecs ; ++ b ) {
            val = xymatrix[a].x[b] ;
            xymatrix[a].x[b] = xymatrix[a].y[b] ;
            xymatrix[a].y[b] = val ; }
   if ( nummaplins ) {
     for ( a = 0 ; a < nummaplins ; ++ a )
        for ( b = 0 ; b < maplin[a].numpoints ; ++ b ) {
            val = maplin[a].x[b] ;
            maplin[a].x[b] = maplin[a].y[b] ;
            maplin[a].y[b] = val ; }}
   reset_grid_magnitude () ;
   bal = truecellwid ;
   truecellhei = truecellwid ;
   truecellhei = bal ; 
   return ; 
}

void fliponx( void )
{
   int a , b ;
   double val ; 
   if ( istransposed ) 
        isyflipped = 1 - isyflipped ; 
   else isxflipped = 1 - isxflipped ; 
   for ( a = 0 ; a < spp ; ++ a )
        for ( b = 0 ; b < xymatrix[a].numrecs ; ++ b ) 
            xymatrix[a].x[b] = - xymatrix[a].x[b] ;
   if ( nummaplins ) {
     for ( a = 0 ; a < nummaplins ; ++ a )
        for ( b = 0 ; b < maplin[a].numpoints ; ++ b ) 
            maplin[a].x[b] = -maplin[a].x[b] ; }
   reset_grid_magnitude () ;
   return ; 
}

void flipony( void )
{
   int a , b ;
   double val ; 
   if ( !istransposed ) 
        isyflipped = 1 - isyflipped ; 
   else isxflipped = 1 - isxflipped ; 
   for ( a = 0 ; a < spp ; ++ a )
        for ( b = 0 ; b < xymatrix[a].numrecs ; ++ b ) 
            xymatrix[a].y[b] = -xymatrix[a].y[b] ;
   if ( nummaplins ) {
     for ( a = 0 ; a < nummaplins ; ++ a )
        for ( b = 0 ; b < maplin[a].numpoints ; ++ b ) 
            maplin[a].y[b] = -maplin[a].y[b] ; }
   reset_grid_magnitude () ;
   return ; 
}

void reset_original_diagram ( void ) 
{
   if ( istransposed ) transpose_xy () ; 
   if ( isxflipped ) fliponx () ; 
   if ( isyflipped ) flipony () ; 
}

void tmp_diagram_chg ( int tostate ) 
{
    int wasxflipped , wasyflipped , wastransposed , rowswas , colswas ; 
    double maxxwas , maxywas , truwidwas , truheiwas , xstartwas , ystartwas ; 
    if ( tostate == 0 ) {
         wasxflipped = isxflipped ; 
         wasyflipped = isyflipped ; 
         wastransposed = istransposed ; 
         maxxwas = maxx ; 
         maxywas = maxy ; 
         truwidwas = truecellwid ; 
         truheiwas = truecellhei ;
         rowswas = rows ; 
         colswas = cols ; 
         xstartwas = grid_startx ;
         ystartwas = grid_starty ;
         reset_original_diagram () ; }
    else {
         if ( wasxflipped ) fliponx () ; 
         if ( wasyflipped ) flipony () ; 
         if ( wastransposed ) transpose_xy () ; 
         isxflipped = wasxflipped ; 
         isyflipped = wasyflipped ; 
         istransposed = wastransposed ; 
         maxx = maxxwas ; 
         maxy = maxywas ; 
         truecellwid = truwidwas ; 
         truecellhei = truheiwas ;
         rows = rowswas ; 
         cols = colswas ; 
         grid_startx = xstartwas ;
         grid_starty = ystartwas ; }
}     

void chksinglefloat ( char * bs , double * nu ) 
{
  char tmpst[100] ; 
  if ( !strcmp ( str , bs ) ) {
      if ( !fscanf ( infile, " %s", tmpst ) ) { 
           sprintf ( junkstr , "Expected number after %s" , bs ) ; 
           ermsg ( junkstr ) ; } 
      * nu = atof ( tmpst ) ; }
  return ; 
}

void chkword ( char * bs , int * nu ) 
{ 
  if ( !strcmp ( str , bs ) )  
      if ( !fscanf ( infile, " %i", nu ) ) { 
           sprintf ( junkstr , "Expected number after %s" , bs ) ; 
           ermsg ( junkstr ) ; } 
  return ; 
}

void chkdouble ( char * bs , double * nua , double * nub )
{
  float a ;
  int mysign , x ; 
  if ( strcmp ( str , bs ) ) return ;
  x = ' ' ;
  mysign = 1 ; 
  while ( isspace ( x ) ) x = getc ( infile ) ;
  if ( x == '-' ) mysign = -1 ;
  else ungetc ( x , infile ) ; 
  if ( !fscanf ( infile, " %f", &a ) )  {
      sprintf ( junkstr , "Expected number after %s" , bs ) ; 
      ermsg ( junkstr ) ; } 
  * nua = a * mysign ; 
  x = ' ' ;
  mysign = 1 ; 
  while ( isspace ( x ) ) x = getc ( infile ) ;
  if ( x == '-' ) mysign = -1 ;
  else ungetc ( x , infile ) ; 
  if ( !fscanf ( infile, " %f", &a ) )  {
      sprintf ( junkstr , "Expected TWO numbers after %s" , bs ) ; 
      ermsg ( junkstr ) ; } 
  *nub = a * mysign ;       
  return ; 
}    

void chkdoubleint ( char * bs , int * nua , int * nub )
{
  int a ;
  int mysign , x ; 
  if ( strcmp ( str , bs ) ) return ;
  x = ' ' ;
  mysign = 1 ; 
  while ( isspace ( x ) ) x = getc ( infile ) ;
  if ( x == '-' ) mysign = -1 ;
  else ungetc ( x , infile ) ; 
  if ( !fscanf ( infile, " %i", &a ) )  {
      sprintf ( junkstr , "Expected number after %s" , bs ) ; 
      ermsg ( junkstr ) ; } 
  * nua = a * mysign ; 
  x = ' ' ;
  mysign = 1 ; 
  while ( isspace ( x ) ) x = getc ( infile ) ;
  if ( x == '-' ) mysign = -1 ;
  else ungetc ( x , infile ) ; 
  if ( !fscanf ( infile, " %i", &a ) )  {
      sprintf ( junkstr , "Expected TWO numbers after %s" , bs ) ; 
      ermsg ( junkstr ) ; } 
  *nub = a * mysign ;       
  return ; 
}    

void read_xyfile ( void ) 
{   int a ;
    float ad ;
    str[0]=0;
    rows = cols = -1 ; 
    while ( strcmp ( str , "xydata" ) ) {
       fscanf ( infile , " %s", &str ) ; 
       if ( feof ( infile ) ) ermsg ( "Found EOF before data appeared!" ) ;
       if ( !strcmp ( str , "nocommas" ) ) nocommas = 1 ; 
       if ( !strcmp ( str , "transpose" ) ) { transposexy = 1 ; transposexymap = 1 ; }
       if ( !strcmp ( str , "latlong" ) ) dolatlong = 1 ;
       if ( !strcmp ( str , "longlat" ) ) dolatlong = 0 ;
       if ( !strcmp ( str , "transposemap" ) ) transposexymap = 1 ; 
       if ( !strcmp ( str , "xnegative" ) ) { xsign = -1 ; xsignmap = -1 ; }
       if ( !strcmp ( str , "ynegative" ) ) { ysign = 1 ; ysignmap = 1 ; }
       if ( !strcmp ( str , "xnegativemap" ) ) xsignmap = -1 ; 
       if ( !strcmp ( str , "ynegativemap" ) ) ysignmap = 1 ; 
       if ( !strcmp ( str , "autogrid" ) ) use_autosize_grid = 1 ;
       if ( !strcmp ( str , "automatrix" ) ) do_automatrix = 1 ;
       if ( !strcmp ( str , "ignorespp" ) ) ignore_sp_lists = 1 ; 
       if ( !strcmp ( str , "maxareas" ) ) {
             if ( !fscanf ( infile , " %s" , &str ) ) numerr ( "maxareas" ) ; 
             maxrecs = atoi ( str ) ; continue ; } 
       if ( !strcmp ( str , "autofill" ) ) {
             if ( !fscanf ( infile , " %s" , &str ) ) numerr ( "autofill" ) ; 
             auto_fill_all = atoi ( str ) ; continue ; } 
       if ( !strcmp ( str , "abslim" ) ) {
             if ( !fscanf ( infile , " %s" , &str ) ) numerr ( "abslim" ) ; 
             abslim = atoi ( str ) ; continue ; } 
       if ( !strcmp ( str , "musthaveone" ) ) {
             if ( !fscanf ( infile , " %s" , &str ) ) numerr ( "musthaveone" ) ; 
             musthaveone = atoi ( str ) ; continue ; } 
       if ( !strcmp ( str , "use_edge_props" ) ) {
             if ( !fscanf ( infile , " %s" , &str ) ) numerr ( "use_edge_props" ) ; 
             use_edge_props = atoi ( str ) ; continue ; } 
       if ( !strcmp ( str , "iifac" ) ) {
             if ( !fscanf ( infile , " %s" , &str ) ) numerr ( "iifac" ) ; 
             iifac = atof ( str ) ; continue ; } 
       if ( !strcmp ( str , "iafac" ) ) {
             if ( !fscanf ( infile , " %s" , &str ) ) numerr ( "iafac" ) ; 
             iafac = atof ( str ) ; continue ; } 
       if ( !strcmp ( str , "oufac" ) ) {
             if ( !fscanf ( infile , " %s" , &str ) ) numerr ( "oufac" ) ; 
             oufac = atof ( str ) ; continue ; } 
       if ( !strcmp ( str , "oafac" ) ) {
             if ( !fscanf ( infile , " %s" , &str ) ) numerr ( "oafac" ) ; 
             oafac = atof ( str ) ; continue ; } 
       if ( !strcmp ( str , "ononafac" ) ) {
             if ( !fscanf ( infile , " %s" , &str ) ) numerr ( "ononafac" ) ; 
             ononafac = atof ( str ) ; continue ; } 
       if ( !strcmp ( str , "min_pres_perc" ) ) {
             if ( !fscanf ( infile , " %s" , &str ) ) numerr ( "min_pres_perc" ) ; 
             min_pres_perc = atoi ( str ) ; continue ; } 
       if ( !strcmp ( str , "compare_perc" ) ) {
             if ( !fscanf ( infile , " %s" , &str ) ) numerr ( "compare_perc" ) ; 
             compare_perc = atoi ( str ) ; continue ; } 
       if ( !strcmp ( str , "minimum_sp_score" ) ) {
             if ( !fscanf ( infile , " %s" , &str ) ) numerr ( "minimum_sp_score" ) ; 
             minimum_sp_score = atof ( str ) ; continue ; } 
       if ( !strcmp ( str , "minimum_scoring_spp" ) ) {
             if ( !fscanf ( infile , " %s" , &str ) ) numerr ( "minimum_scoring_spp" ) ; 
             sch_minimum_scoring_spp = atoi ( str ) ; continue ; } 
       if ( !strcmp ( str , "minimum_total_score" ) ) {
             if ( !fscanf ( infile , " %s" , &str ) ) numerr ( "minimum_total_score" ) ; 
             sch_minimum_total_score = atof ( str ) ; continue ; } 
       chksinglefloat ( "mfactor" , &mfactor ) ; 
       chksinglefloat ( "mminusx" , &mminusx ) ; 
       chksinglefloat ( "mminusy" , &mminusy ) ; 
       chksinglefloat ( "mfactormap" , &mfactormap ) ; 
       chksinglefloat ( "mminusxmap" , &mminusxmap ) ; 
       chksinglefloat ( "mminusymap" , &mminusymap ) ; 
       chkword ( "rows" , &rows ) ; 
       chkword ( "cols" , &cols ) ; 
       chkword ( "spp" , &spp ) ;
       chkword ( "samplespp" , &sample_spp_prop ) ;
       chkword ( "samplerec" , &sample_rec_prop ) ; 
       chkword ( "samplerepls" , &sample_repls ) ; 
       chkword ( "samplearea" , &sample_area_prob ) ; 
       chkword ( "sampleseed" , &rseed ) ; 
       chkword ( "autosample" , &run_autosample ) ;
       chkword ( "sampleareacut" , &sample_area_cut ) ; 
       chkword ( "samplesppcut" , &sample_spp_cut ) ; 
       chkword ( "autoconsense" , &autoconsense_cut ) ;
       if ( !strcmp ( str , "autosave" ) ) run_autosave = 1 ; 
       chkdouble ( "gridx" , &grid_startx , &grid_width ) ; 
       chkdouble ( "gridy" , &grid_starty , &grid_height ) ;
       chkdouble ( "fill" , &fill_x_is , &fill_y_is ) ; 
       chkdouble ( "assume" , &assume_x_is , &assume_y_is ) ;
      }
   if ( run_autosample > 3 ) ermsg ( "Sample must be of types 0-3" ) ; 
   if ( autoconsense_cut >= 0 ) run_autoconsense = 1 ;       
   if ( rows == 0 || cols == 0 ) ermsg ( "Rows/Cols cannot be 0" ) ;
   if ( grid_startx < 10e200 ) {
      if ( grid_starty > 10e199 ) ermsg ( "If you specify X coordinates, you must also specify Y coordinates" ) ; 
      grid_startx *= xsign ; } 
   if ( grid_starty < 10e200 ) {
      if ( grid_startx > 10e199 ) ermsg ( "If you specify Y coordinates, you must also specify Y coordinates" ) ; 
      grid_starty *= ysign ; }
   if ( ( rows > 0 && cols < 0 ) || ( rows < 0 && cols > 0 ) ) ermsg ( "You cannot specify only columns or rows --must do both!" ) ;  
   if ( rows > 0 && grid_startx < 10e200 ) ermsg ( "If you specify grid origin and size,\nyou cannot specify also rows and columns" ) ; 
   if ( rows > 0 && use_autosize_grid )
       if ( !sure ( "\"Autogrid\" overrides specification of rows/cols. Continue" ) ) exit ( 0 ) ; 
   read_xydata () ;
   for ( a = 0 ; a < spp ; ++ a ) 
       xymatrix[a].trurecs = xymatrix[a].numrecs ;
}

int bytesread = 0 ; 
static int exit_on_eof = 1 ; 

int bread ( int bys , int num , char * ptr ) 
{ int a = num * bys , b ;
  bytesread += a ;
  b = getc ( infile ) ; 
  if ( feof ( infile ) ) { 
       if ( exit_on_eof ) {
           errmsg ( "Couldn't read data (unexpected EOF)" , NULL ) ;
           exit ( 0 ) ; }
       else return 0 ; } 
  ungetc ( b , infile ) ; 
  while ( a -- ) 
         * ptr ++ = getc ( infile ) ; 
  return 1 ; 
} 

void read_data ( void ) 
{ 
   int a , b , c ;
   Artyp * dorec ; 
   bread ( sizeof ( int ) , 1 , ( char * ) &abslim ) ; 
   bread ( sizeof ( int ) , 1 , ( char * ) &musthaveone ) ;
   bread ( sizeof ( int ) , 1 , ( char * ) &use_edge_props ) ;
   a = use_edge_props & 2 ;
   use_edge_props &= 1 ;
   bread ( sizeof ( double ) , 1 , ( char * ) &iifac ) ; 
   bread ( sizeof ( double ) , 1 , ( char * ) &iafac ) ; 
   bread ( sizeof ( double ) , 1 , ( char * ) &oufac ) ; 
   bread ( sizeof ( double ) , 1 , ( char * ) &oafac ) ; 
   bread ( sizeof ( double ) , 1 , ( char * ) &ononafac ) ;
   bread ( sizeof ( double ) , 1 , ( char * ) &min_pres_perc ) ; 
   bread ( sizeof ( int ) , 1 , ( char * ) &compare_perc ) ; 
   bread ( sizeof ( int ) , 1 , ( char * ) &rows ) ; 
   bread ( sizeof ( int ) , 1 , ( char * ) &cols ) ; 
   bread ( sizeof ( int ) , 1 , ( char * ) &spp ) ;
   // Get the names here, if present...
   if ( a ) {
       memerr ( spname = ( char ** ) malloc ( spp * sizeof ( char * ) ) ) ; 
       for ( a = 0 ; a < spp ; ++ a ) {
           memerr ( spname[a] = ( char * ) malloc ( Spnamesz * sizeof ( char ) ) ) ; 
           bread ( sizeof ( char ) , Spnamesz , spname[a] ) ; }}
   bread ( sizeof ( double ) , 1 , ( char * ) &grid_starty ) ;
   bread ( sizeof ( double ) , 1 , ( char * ) &grid_startx ) ;
   bread ( sizeof ( double ) , 1 , ( char * ) &grid_height ) ;
   bread ( sizeof ( double ) , 1 , ( char * ) &grid_width ) ;
   cls () ; 

   spcells = ( spp + 31 ) / 32 ; 
   arcells = ( ( rows * cols ) + 31 ) / 32 ; 
   totareas = rows * cols ;
   memerr ( widefilter = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ; 
   memerr ( archeckd = ( int * ) malloc ( totareas * sizeof ( int ) ) ) ;
   memerr ( fillist = ( char ** ) malloc ( rows * sizeof ( char * ) ) ) ;
   for ( a = rows ; a -- ; )
        memerr ( fillist [ a ] = ( char * ) malloc ( cols * sizeof ( char ) ) ) ; 
   a = totareas ; 
   if ( a < ( spp + 31 ) ) a = spp + 31 ; 
   memerr ( tmplist = ( int * ) malloc ( a * sizeof ( int ) ) ) ; 
   memerr ( intersptr = (int32 *) malloc ( spcells * sizeof ( int32 ) ) ) ; 
   memerr ( dablor = (int32 *) malloc ( spcells * sizeof ( int32 ) ) ) ; 
   memerr ( dabland = (int32 *) malloc ( spcells * sizeof ( int32 ) ) ) ; 
   memerr ( setlist = ( int * ) malloc ( rows * cols * sizeof ( int ) ) ) ; 
   memerr ( nosetlist = ( int * ) malloc ( rows * cols * sizeof ( int ) ) ) ; 
   memerr ( numentries = ( int * ) malloc ( spp * sizeof ( int ) ) ) ; 
   memerr ( numassentries = ( int * ) malloc ( spp * sizeof ( int ) ) ) ;
   memerr ( listin = ( int * ) malloc ( totareas * sizeof ( int ) ) ) ; 
   memerr ( listadja = ( int * ) malloc ( totareas * sizeof ( int ) ) ) ; 
   memerr ( listnonadja = ( int * ) malloc ( totareas * sizeof ( int ) ) ) ;
   memerr ( spscore = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dout = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dpres = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dinf = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dass = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dadja = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dnadja = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   bread ( sizeof ( int ) , spp , ( char * ) numentries ) ;
   bread ( sizeof ( int ) , spp , ( char * ) numassentries ) ;
   memerr ( isdefd = ( char ** ) malloc ( rows * sizeof ( char * ) ) ) ; 
   for ( a = rows ; a -- ; ) { 
        memerr ( isdefd [ a ] = ( char * ) malloc ( cols * sizeof ( char ) ) ) ; 
        bread ( sizeof ( char ) , cols , ( char * ) isdefd [ a ] ) ; } 
   memerr ( matrix = ( int32 *** ) malloc ( rows * sizeof ( int32 ** ) ) ) ; 
   memerr ( assmatrix = ( int32 *** ) malloc ( rows * sizeof ( int32 ** ) ) ) ; 
   for ( a = rows ; a -- ; ) { 
        memerr ( matrix [ a ] = ( int32 ** ) malloc ( cols * sizeof ( int32 * ) ) ) ; 
        memerr ( assmatrix [ a ] = ( int32 ** ) malloc ( cols * sizeof ( int32 * ) ) ) ; 
        for ( b = cols ; b -- ; )  { 
             memerr ( matrix [ a ] [ b ] = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ; 
             memerr ( assmatrix [ a ] [ b ] = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ; 
             if ( isdefd [ a ] [ b ] ) { 
                    bread ( sizeof ( int32 ) , spcells , ( char * ) matrix [ a ] [ b ] ) ; 
                    bread ( sizeof ( int32 ) , spcells , ( char * ) assmatrix [ a ] [ b ] ) ; }
             else for ( c = spcells ; c -- ; ) matrix [ a ] [ b ] [ c ] = assmatrix [ a ] [ b ] [ c ] = 0 ; }}
   bread ( sizeof ( int ) , 1 , ( char * ) &numrecs ) ; 

   if ( !maxrecs ) maxrecs = numrecs + 100000 ; 
   memerr ( rec = ( Artyp * ) malloc ( ( maxrecs ) * sizeof ( Artyp ) ) ) ; 
   memerr ( arlist = ( Artyp ** ) malloc ( ( maxrecs ) * sizeof ( Artyp * ) ) ) ; 
   dorec = rec ; 
   for ( a = maxrecs ; a -- ; ) { 
       memerr ( dorec -> lst = ( int32 * ) malloc ( arcells * sizeof ( int32 ) ) ) ; 
       memerr ( dorec -> splist = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ; 
       ++ dorec ; } 
   if ( numrecs ) { 
      dorec = rec ; // + numrecs ; 
      a = numrecs ; 
      while ( a -- ) { 
           // -- dorec ; 
           bread ( sizeof ( int32 ) , arcells , ( char * ) dorec -> lst ) ; 
           bread ( sizeof ( double ) , 1 , ( char * ) &(dorec->score) ) ; 
           bread ( sizeof ( int ) , 1 , ( char * ) &( dorec->size ) ) ; 
           dorec->mark = 0 ;
           ++ dorec ; 
           }} 
   memerr ( splist = ( int32 * ) malloc ( arcells * sizeof ( int32 ) ) ) ;
   memerr ( inflist = ( int32 * ) malloc ( arcells * sizeof ( int32 ) ) ) ;
   memerr ( sccol = ( char ** ) malloc ( ( cols + 2 ) * sizeof ( char *  ) ) ) ; 
   for ( a = 0 ; a < ( cols + 2 ) ; ++ a ) 
          memerr ( sccol [ a ] = ( char * ) malloc ( ( rows + 2 ) * sizeof ( char ) ) ) ;   
   recalculate_numentries ( -1 ) ;
   memerr ( spact = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ;
   for ( a = 0 ; a < spcells ; ++ a ) spact[a] = -1 ;
   grid_created = 1 ; 
   return ; 
} 

void read_sets_from_file ( void )
{
    if ( comstring[0] == '\0' ) return ;
    infile = fopen ( comstring , "rb" ) ;
    warned_yet = 0 ; 
    read_areas () ;
    fclose ( infile ) ; 
}    

void recalculate_numentries ( int which )
{
    int x , y , a , b , c ;
    unsigned long int mb , mc ;
    if ( which >= 0 ) {
        b = which ; 
        mc = b / 32 ;
        mb = 1 << ( b % 32 ) ; 
        x = y = 0 ;
       for ( a = rows ; a -- ; )
          for ( c = cols ; c -- ; ) {
            if ( ( matrix[a][c][mc] & mb ) ) ++ x ; 
            if ( ( assmatrix[a][c][mc] & mb ) ) ++ y ; }
        numentries [b] = x ; 
        numassentries [b] = y ; }
    else     
    for ( b = spp ; b -- ; ) {
        mc = b / 32 ;
        mb = 1 << ( b % 32 ) ; 
        x = y = 0 ;
       for ( a = rows ; a -- ; )
          for ( c = cols ; c -- ; ) {
            if ( ( matrix[a][c][mc] & mb ) ) ++ x ; 
            if ( ( assmatrix[a][c][mc] & mb ) ) ++ y ; }
        numentries [b] = x ; 
        numassentries [b] = y ; }
    return ; 
}           

int didanemptyone ;

void check_the_new_scores ( int from_which ) 
{ Artyp * old = recptr ;
  int at = numrecs ; 
  if ( numrecs == 0 ) return ; 
  recptr = rec + at ;
  pleasewait ( "Re-calculating scores for new areas..." ) ;
  initializing = 1 ; 
  while ( at -- > from_which ) {
        -- recptr ; 
        if ( recptr -> size == 0 ) recptr->score = recptr->numspp = 0 ; 
        else dorule5 () ;
        if ( user_wants_a_break ) { recptr = rec + ( numrecs = from_which ) ; break ; }} 
  initializing = 0 ; 
  imdone () ;
  didanemptyone = 0 ; 
  if ( !numrecs ) { didanemptyone = 1 ; donewset () ; }
  return ; 
} 

void read_areas ( void )
{
   int a = 0 ;
   int had = numrecs ;
   int shoulbe ; 
   Artyp * dorec ; 
   exit_on_eof = 0 ; 
   cls () ;
// init_time () ; 
   pleasewait ( "Reading sets..." ) ; 
   if ( a + numrecs >= maxrecs ) {
       imdone () ; 
       sprintf ( junkstr , "\nCan't read more than %i records" , maxrecs ) ;
       MessageBox ( hwnd , junkstr, "Error" , MB_OK | MB_ICONERROR ) ;
       return ; }
    dorec = rec + numrecs ; 
    while ( !feof ( infile ) ) { 
           if ( !bread ( sizeof ( int32 ) , arcells , ( char * ) dorec -> lst ) ) break ; 
           if ( !bread ( sizeof ( double ) , 1 , ( char * ) &( dorec -> score ) ) ) break ; 
           if ( !bread ( sizeof ( int ) , 1 , ( char * ) &( dorec->size ) ) ) break ; 
           dorec -> mark = 0 ;
           dorec -> bootarval = dorec -> bootspval = 0 ; 
           ++ a ; 
           ++ dorec ; }
   exit_on_eof = 1 ; 
   numrecs += a ;
   shoulbe = numrecs ; 
   imdone () ;
   if ( ridofdupes ) delete_duplicates ( 0 ) ; 
   check_the_new_scores ( had ) ;
// show_time ( "check scores" ) ; 
   if ( !user_wants_a_break ) 
     if ( ridofdupes )
        myprintf( "Read %i sets (total now: %i; %i records discarded)\n \n \n [ hit ENTER or left-click to continue ]" , a , numrecs , shoulbe - numrecs ) ;
     else   
        myprintf( "Read %i sets (total: %i)\n \n \n [ hit ENTER or left-click to continue ]" , a , numrecs ) ;
   else
     if ( didanemptyone )
          myprintf( "%i sets contained in file (none read, created an empty set)\n \n \n [ hit ENTER or left-click to continue ]" , a ) ;     
     else 
          myprintf( "%i sets contained in file (none read; %i now in memory)\n \n \n [ hit ENTER or left-click to continue ]" , a , numrecs ) ;
   user_wants_a_break = didanemptyone = 0 ; 
   return ; 
}    

void denovo ( char * rowsst , char * colsst , char * sppst )
{ 
   int a , b , c ;
   int trurows , trucols ; 
   Artyp * dorec ;
   trurows = rows = atoi ( rowsst ) ;
   trucols = cols = atoi ( colsst ) ;
   spp = atoi ( sppst ) ;
   if ( rows <= 0 || cols <= 0 || spp <= 0 ) ermsg ( "Error in number of rows, cols, or spp" ) ; 
   spcells = ( spp + 31 ) / 32 ; 
   /*  This is used to allocate extra mem., so that grid size can be changed... */
   rows = rows * maxgridmult ;
   cols = cols * maxgridmult ;
   mincellwid = truecellwid / maxgridmult ; 
   mincellhei = truecellhei / maxgridmult ; 
   arcells = ( ( rows * cols ) + 31 ) / 32 ; 
   totareas = rows * cols ;
   memerr ( widefilter = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ; 
   memerr ( archeckd = ( int * ) malloc ( totareas * sizeof ( int ) ) ) ;
   memerr ( fillist = ( char ** ) malloc ( rows * sizeof ( char * ) ) ) ;
   for ( a = rows ; a -- ; )
        memerr ( fillist [ a ] = ( char * ) malloc ( cols * sizeof ( char ) ) ) ; 
   a = totareas ; 
   if ( a < ( spp + 31 ) ) a = spp + 31 ; 
   memerr ( tmplist = ( int * ) malloc ( a * sizeof ( int ) ) ) ; 
   memerr ( intersptr = (int32 *) malloc ( spcells * sizeof ( int32 ) ) ) ; 
   memerr ( dablor = (int32 *) malloc ( spcells * sizeof ( int32 ) ) ) ; 
   memerr ( dabland = (int32 *) malloc ( spcells * sizeof ( int32 ) ) ) ; 
   memerr ( setlist = ( int * ) malloc ( rows * cols * sizeof ( int ) ) ) ; 
   memerr ( nosetlist = ( int * ) malloc ( rows * cols * sizeof ( int ) ) ) ; 
   memerr ( numentries = ( int * ) malloc ( spp * sizeof ( int ) ) ) ; 
   memerr ( numassentries = ( int * ) malloc ( spp * sizeof ( int ) ) ) ;
   memerr ( listin = ( int * ) malloc ( totareas * sizeof ( int ) ) ) ; 
   memerr ( listadja = ( int * ) malloc ( totareas * sizeof ( int ) ) ) ; 
   memerr ( listnonadja = ( int * ) malloc ( totareas * sizeof ( int ) ) ) ;
   memerr ( spscore = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dout = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dpres = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dinf = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dass = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dadja = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dnadja = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( isdefd = ( char ** ) malloc ( rows * sizeof ( char * ) ) ) ; 
   for ( a = rows ; a -- ; )  
        memerr ( isdefd [ a ] = ( char * ) malloc ( cols * sizeof ( char ) ) ) ; 
   memerr ( matrix = ( int32 *** ) malloc ( rows * sizeof ( int32 ** ) ) ) ; 
   memerr ( assmatrix = ( int32 *** ) malloc ( rows * sizeof ( int32 ** ) ) ) ; 
   for ( a = rows ; a -- ; ) { 
        memerr ( matrix [ a ] = ( int32 ** ) malloc ( cols * sizeof ( int32 * ) ) ) ; 
        memerr ( assmatrix [ a ] = ( int32 ** ) malloc ( cols * sizeof ( int32 * ) ) ) ; 
        for ( b = cols ; b -- ; )  { 
             memerr ( matrix [ a ] [ b ] = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ; 
             memerr ( assmatrix [ a ] [ b ] = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ; }}
   if ( !maxrecs ) 
   maxrecs = numrecs + 10000 ; 
   memerr ( rec = ( Artyp * ) malloc ( ( maxrecs ) * sizeof ( Artyp ) ) ) ; 
   memerr ( arlist = ( Artyp ** ) malloc ( ( maxrecs ) * sizeof ( Artyp * ) ) ) ; 
   dorec = rec ;
   if ( ignore_sp_lists ) {
       memerr ( fakesplist = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ;
       for ( a = 0 ; a < spcells ; ++ a ) fakesplist [ a ] = 0 ; }
   for ( a = maxrecs ; a -- ; ) { 
       memerr ( dorec -> lst = ( int32 * ) malloc ( arcells * sizeof ( int32 ) ) ) ;
       if ( ignore_sp_lists ) dorec -> splist = fakesplist ; 
       else memerr ( dorec -> splist = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ; 
       ++ dorec ; } 
   numrecs = 0 ; 
   for ( a = rows ; a -- ; )
     for ( b = cols ; b -- ; ) {
       isdefd[a][b] = 0 ; 
       for ( c = spcells ; c -- ; ) matrix [a][b][c] = assmatrix [a][b][c] = 0 ; }    
   for ( c = spp ; c -- ; ) numentries[c] = numassentries[c] = 0 ; 
   memerr ( splist = ( int32 * ) malloc ( arcells * sizeof ( int32 ) ) ) ;
   memerr ( inflist = ( int32 * ) malloc ( arcells * sizeof ( int32 ) ) ) ;
   memerr ( sccol = ( char ** ) malloc ( ( cols + 2 ) * sizeof ( char *  ) ) ) ; 
   for ( a = 0 ; a < ( cols + 2 ) ; ++ a ) 
          memerr ( sccol [ a ] = ( char * ) malloc ( ( rows + 2 ) * sizeof ( char ) ) ) ;   
  /*  recalculate_numentries ( -1 ) ;  */    // this was pointless; matrix hasn't been filled yet!!
   memerr ( spact = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ;
   for ( a = 0 ; a < spcells ; ++ a ) spact[a] = -1 ;
   rows = trurows ;
   cols = trucols ; 
   arcells = ( ( rows * cols ) + 31 ) / 32 ; 
   totareas = rows * cols ;
   imdone () ; 
   grid_created = 2 ;
   donewset () ;
   cls () ;
   initializing = 0 ;
   showcurset () ; 
   sprintf ( junkstr , "\nCreated matrix, %i rows x %i cols" , rows , cols ) ; 
   spitit ( junkstr ) ; 
   imdone () ; 

return ; 

/***   Obsolete code ...
   spcells = ( spp + 31 ) / 32 ; 
   arcells = ( ( rows * cols ) + 31 ) / 32 ; 
   totareas = rows * cols ; 
   memerr ( widefilter = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ;
   memerr ( archeckd = ( int * ) malloc ( totareas * sizeof ( int ) ) ) ; 
   a = totareas ; 
   if ( a < ( spp + 31 ) ) a = spp + 31 ; 
   memerr ( tmplist = ( int * ) malloc ( a * sizeof ( int ) ) ) ; 
   memerr ( intersptr = (int32 *) malloc ( spcells * sizeof ( int32 ) ) ) ; 
   memerr ( dablor = (int32 *) malloc ( spcells * sizeof ( int32 ) ) ) ; 
   memerr ( dabland = (int32 *) malloc ( spcells * sizeof ( int32 ) ) ) ; 
   memerr ( setlist = ( int * ) malloc ( rows * cols * sizeof ( int ) ) ) ; 
   memerr ( nosetlist = ( int * ) malloc ( rows * cols * sizeof ( int ) ) ) ; 
   memerr ( numentries = ( int * ) malloc ( spp * sizeof ( int ) ) ) ;
   memerr ( numassentries = ( int * ) malloc ( spp * sizeof ( int ) ) ) ;
   memerr ( listin = ( int * ) malloc ( totareas * sizeof ( int ) ) ) ; 
   memerr ( listadja = ( int * ) malloc ( totareas * sizeof ( int ) ) ) ; 
   memerr ( listnonadja = ( int * ) malloc ( totareas * sizeof ( int ) ) ) ;
   memerr ( spscore = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dout = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dpres = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dinf = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dass = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dadja = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dnadja = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( fillist = ( char ** ) malloc ( rows * sizeof ( char * ) ) ) ;
   for ( a = rows ; a -- ; )
        memerr ( fillist [ a ] = ( char * ) malloc ( cols * sizeof ( char ) ) ) ; 
   for ( a = spp ; a -- ; ) numentries [ a ] = numassentries [ a ] = 0 ; 
   memerr ( isdefd = ( char ** ) malloc ( rows * sizeof ( char * ) ) ) ; 
   for ( a = rows ; a -- ; ) { 
        memerr ( isdefd [ a ] = ( char * ) malloc ( cols * sizeof ( char ) ) ) ;
        for ( b = cols ; b -- ; ) isdefd [a][b] = 1 ; }
   memerr ( matrix = ( int32 *** ) malloc ( rows * sizeof ( int32 ** ) ) ) ; 
   memerr ( assmatrix = ( int32 *** ) malloc ( rows * sizeof ( int32 ** ) ) ) ; 
   for ( a = rows ; a -- ; ) { 
        memerr ( matrix [ a ] = ( int32 ** ) malloc ( cols * sizeof ( int32 * ) ) ) ; 
        memerr ( assmatrix [ a ] = ( int32 ** ) malloc ( cols * sizeof ( int32 * ) ) ) ; 
        for ( b = cols ; b -- ; )  { 
             memerr ( matrix [ a ] [ b ] = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ; 
             memerr ( assmatrix [ a ] [ b ] = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ; 
             for ( c = spcells ; c -- ; ) matrix [ a ] [ b ] [ c ] = assmatrix [ a ] [ b ] [ c ] = 0 ; }}
   numrecs = 0 ;
   maxrecs = numrecs + 100 ; 
   memerr ( rec = ( Artyp * ) malloc ( ( maxrecs ) * sizeof ( Artyp ) ) ) ; 
   memerr ( arlist = ( Artyp ** ) malloc ( ( maxrecs ) * sizeof ( Artyp * ) ) ) ; 
   dorec = rec ; 
   for ( a = maxrecs ; a -- ; ) { 
       memerr ( dorec -> lst = ( int32 * ) malloc ( arcells * sizeof ( int32 ) ) ) ; 
       memerr ( dorec -> splist = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ; 
       ++ dorec ; } 
   memerr ( splist = ( int32 * ) malloc ( arcells * sizeof ( int32 ) ) ) ; 
   memerr ( inflist = ( int32 * ) malloc ( arcells * sizeof ( int32 ) ) ) ;
   memerr ( sccol = ( char ** ) malloc ( ( cols + 2 ) * sizeof ( char *  ) ) ) ; 
   for ( a = 0 ; a < ( cols + 2 ) ; ++ a ) 
          memerr ( sccol [ a ] = ( char * ) malloc ( ( rows + 2 ) * sizeof ( char ) ) ) ;   
   memerr ( spact = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ;
   for ( a = 0 ; a < spcells ; ++ a ) spact[a] = -1 ; 
   cls () ;
   donewset () ;
   showcurset () ; 
   return ;
*******/
   
} 

void chk_numrecs ( void )
{
    if ( numrecs ) return ;
    if ( !grid_created ) return ; 
    // if ( !sure ( "No records in input file.  Create a new set" ) ) dobyebye () ;
    donewset () ;
    return ; 
}      

extern char vndm_infilename[_MAX_PATH ] ;

int isxyfile ( char * fnam )
{
    char * cp = fnam ;
    if ( fnam == NULL ) return 0 ; 
    while ( * cp ) cp ++ ;
    while ( cp > fnam && * cp != '.' ) -- cp ;
    ++ cp ;
    if ( strlen ( cp ) != 3 ) return 0 ; 
    if ( tolower( cp[0] ) == 'x' && 
         tolower( cp[1] ) == 'y' && 
         tolower( cp[2] ) == 'd' ) return 1 ;
    return 0 ;
}

int is_ndm_file ( char * fnam )
{
    char * cp = fnam ;
    if ( fnam == NULL ) return 0 ; 
    while ( * cp ) cp ++ ;
    while ( cp > fnam && * cp != '.' ) -- cp ;
    ++ cp ;
    if ( strlen ( cp ) != 3 ) return 0 ; 
    if ( tolower( cp[0] ) == 'n' && 
         tolower( cp[1] ) == 'd' && 
         tolower( cp[2] ) == 'm' ) return 1 ;
    return 0 ;
}

int is_dat_file ( char * fnam )
{
    char * cp = fnam ;
    if ( fnam == NULL ) return 0 ; 
    while ( * cp ) cp ++ ;
    while ( cp > fnam && * cp != '.' ) -- cp ;
    ++ cp ;
    if ( strlen ( cp ) != 3 ) return 0 ; 
    if ( tolower( cp[0] ) == 'd' && 
         tolower( cp[1] ) == 'a' && 
         tolower( cp[2] ) == 't' ) return 1 ;
    return 0 ;
}

#define MAXLINFILES 25 

int fake_main ( int margc , char ** margv ) 
{ int scratched = 0 ; 
  int a ;
  int fromarg = 1 ;
  int numlinfiles = 0 ; 
  double tmp ;
  int doarg , datfileis = 0 , havesomexyd = 0 ;
  int no_xyd_or_dat = 1 , read_as_ndm_file = 0 ; 
  maplin = NULL ;
  grid_startx = grid_starty = 10e200 ;
  set_ndm_bin_name () ; 
  if ( margc < 2 || !strcmp ( margv[1] , "new" ) ) {
        if ( margc < 2 ) {
           fromarg = 0 ; 
           get_filename ( 0 ) ;
           if ( comstring[0]=='\0' ) {
                 SendMessage ( hwnd , WM_COMMAND, IDM_EXIT , 0 ) ;
                 exit ( 0 ) ; }
            else {
                strcpy ( vndm_infilename , comstring ) ; 
                infile = fopen ( comstring , "rb" ) ;
                if ( infile == NULL ) {
                    sprintf ( junkstr , "Can't open file %s for input" , comstring ) ;
                    ermsg ( junkstr ) ; }
                if ( is_dat_file ( comstring ) ) { read_as_a_dat_file = 1 ; read_input_matrix ( ) ; }
                else if ( isxyfile ( comstring ) ) { read_xyfile () ; end_xy_file () ; havesomexyd = 1 ; }
                else if ( is_ndm_file ( comstring ) ) { read_as_ndm_file = 1 ; read_data () ; }
                else ermsg ( "Sorry, only files of type:\n\n    DAT\n    XYD\n    NDM\n\nare used for data input.\n" ) ;
                fclose ( infile ) ; }}
        else {
            if ( margc < 5 ) ermsg ( "Must specify rows cols spp !!" ) ;
            denovo ( margv[2] , margv[3] , margv[4] ) ;
            grid_created = 1 ; 
            scratched = 1 ; }}
 output = stdout ; 
 if ( !scratched ) {
  pleasewait ( "Reading input file(s)...") ;
  /** First, read any *.dat files in arguments *******/
  for ( doarg = 1 ; doarg < margc ; ++ doarg ) {
     if ( is_ndm_file ( margv [ doarg ] ) ) read_as_ndm_file = 1 ; 
     if ( isxyfile ( margv [ doarg ] ) ) {
         if ( havesomexyd ) ermsg ( "Cannot read more than one *.XYD file" ) ; 
         no_xyd_or_dat = 0 ;
         ++ havesomexyd ; }
     if ( is_dat_file ( margv[doarg] ) ) {
          no_xyd_or_dat = 0 ;
          if ( read_as_a_dat_file ) ermsg ( "ERROR: cannot read more than one *.DAT file" ) ; 
          infile = fopen ( margv [ doarg ] , "rb" ) ; 
          if ( infile == NULL )  
              ermsg ( "Can't open input file" ) ;
          strcpy ( vndm_infilename , margv[doarg] ) ;
          read_input_matrix ( ) ;
          fclose ( infile ) ;
          datfileis = doarg ; }}
  if ( !havesomexyd && !read_as_a_dat_file && !read_as_ndm_file )
     ermsg ( "Sorry, only files of type:\n\n    DAT\n    XYD\n    NDM\n\nare used for data input.\n" ) ;

  /** Now, chek the rest of arguments *******/
  for ( doarg = 1 ; doarg < margc ; ++ doarg ) {
     if ( doarg == datfileis ) continue ;
     infile = fopen ( margv [ doarg ] , "rb" ) ; 
     if ( strcmp ( margv [ doarg ] , "-names" ) && strcmp ( margv [ doarg ] , "-fill" ) && infile == NULL )  
          ermsg ( "Can't open input file" ) ;
     if ( isxyfile ( margv[doarg] ) ) {
       if ( read_as_a_dat_file ) {
            if ( grid_startx > 10e199 || grid_starty > 10e199 ) ermsg ( "To read point coordinates with a *.DAT file,\nyou must specify grid location in the *.DAT file\n(using \"gridx\" and \"gridy\")" ) ; 
            strcpy ( comstring , margv[doarg] ) ; 
            post_read_xyfile () ; }
       else {
         datfileis = doarg ; 
         strcpy ( vndm_infilename , margv[doarg] ) ;
         read_xyfile () ;
         end_xy_file () ; }}
     else
      if ( no_xyd_or_dat && is_ndm_file ( margv[doarg]) ) {
            datfileis = doarg ; 
            strcpy ( vndm_infilename , margv[doarg] ) ;
            read_data () ;
            break ; }
     if ( strcmp ( margv [ doarg ] , "-names" ) ) 
         fclose ( infile ) ; 
     if ( strcmp ( margv [ doarg ] , "-fill" ) ) 
         fclose ( infile ) ; }
     imdone () ;      
     a = 1 ;
     while ( a < margc ) {
          if ( !strcmp ( margv[a] , "-names" ) ) {
              if ( a == margc - 1 ) ermsg ( "Option \"-name\" requires specification of a file with taxon names" ) ; 
              infile = fopen ( margv [ ++ a ] , "rb" ) ;
              if ( infile == NULL ) ermsg ( "Oops, file with taxon names not found!" ) ; 
              parse_taxon_names () ; 
              ++ a ; 
              continue ; }
          if ( !strcmp ( margv[a] , "-fill" ) ) {
              if ( a == margc - 1 ) ermsg ( "Option \"-fill\" requires specification of a file with taxon numbers" ) ; 
              infile = fopen ( margv [ ++ a ] , "rb" ) ;
              if ( infile == NULL ) ermsg ( "Oops, file with taxon numbers not found!" ) ; 
              set_autofills_from_file () ; 
              ++ a ; 
              continue ; }
          if ( it_is_a_line_file ( margv[a] ) ) {
              infile = fopen ( margv[a] , "rb" ) ;
              if ( infile == NULL )  
                   ermsg ( "Can't open file with line definitions" ) ;
              read_map_definition ( 1 ) ;
              fclose ( infile ) ; 
              ++ a ;
              continue ; }
        if ( !is_ndm_file ( margv[a] ) || a == datfileis ) { ++ a ; continue ; }
        infile = fopen ( margv [ a ] , "rb" ) ;
        if ( infile == NULL )  
           ermsg ( "Can't open input file" ) ;
        ++ a ;
        if ( data_is_xydata && !grid_created ) ermsg ( "Cannot read sets from file until matrix is created!\n(Use \"automatrix\" in *.XYD file to create matrix automatically)" ) ;         
        read_areas () ;
        fclose ( infile ) ; }}
 nubi = num = depth = 0 ;
 dograndsumofpoints () ; 
 calculin() ;
 initializing = 0 ; 
 chk_numrecs () ; 
 recptr = rec ;
 curcmd_loop = cmd_loop ; 
 if ( grid_created ) 
      showcurset () ;
 if ( run_autosample ) run_the_autosample () ;
 return ; 
} 

int32 ***numa = NULL , *** nuinfma ;
char ** nudefd ; 

int divide_data ( void )
{
     int mc , numar ; 
     int32 mb ; 
     int a , b , c ;
     int nuro , nuco ;
     int ratio = ' ' ;
     char * at = comstring ; 
     while ( ratio != 13 && isspace ( ratio ) && ratio != '\0' ) 
         ratio = * at ++ ;
     if ( !isdigit ( ratio ) ) return 0 ; 
     ratio = ratio - '0' ; 
     if ( outspace == NULL ) {
         curcmd_loop = cmd_loop ;
         showcurset () ; 
         captf("Must open output file before saving!" ) ; 
         return 0 ; }
     memerr ( ( numa = ( int32 *** ) malloc ( ( 1 + ( rows / ratio ))  * sizeof ( int32 ** ) ) ) ) ;
     memerr ( ( nuinfma = ( int32 *** ) malloc ( ( 1 + ( rows / ratio ))  * sizeof ( int32 ** ) ) ) ) ;
     memerr ( ( nudefd = ( char ** ) malloc ( ( 1 + ( rows / ratio )) * sizeof ( char * ) ) ) ) ; 
     for ( a = 1 + ( rows / ratio ) ; a -- ; ) {
            memerr ( ( numa [ a ] = ( int32 ** ) malloc ( ( 1 + ( cols / ratio )) * sizeof ( int32 * ) ) ) ) ; 
            memerr ( ( nuinfma [ a ] = ( int32 ** ) malloc ( ( 1 + ( cols / ratio )) * sizeof ( int32 * ) ) ) ) ; 
            memerr ( ( nudefd [ a ] = ( char * ) malloc ( ( 1 + ( cols / ratio )) * sizeof ( char ) ) ) ) ; 
            for ( b = 1 + ( cols / ratio ) ; b -- ; ) { 
                memerr ( ( numa [ a ] [ b ] = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ) ;
                memerr ( ( nuinfma [ a ] [ b ] = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ) ;
                nudefd [ a ] [ b ] = 0 ; 
                for ( c = spcells ; c -- ; )
                     numa [ a ] [ b ] [ c ] = nuinfma [ a ] [ b ] [ c ] = 0 ; }}
     for ( a = rows ; a -- ; ) {
         nuro = a / ratio ; 
         for ( b = cols ; b -- ; ) {
              if ( !isdefd [ a ] [ b ] ) continue ;
              nuco = b / ratio ;
              nudefd [ nuro ] [ nuco ] = 1 ; 
              for ( c = spcells ; c -- ; ) { 
                   numa [ nuro ] [ nuco ] [ c ] |= matrix [ a ] [ b ] [ c ] ;
                   nuinfma [ nuro ] [ nuco ] [ c ] |= assmatrix [ a ] [ b ] [ c ] ; }}}
     nuro = rows / ratio ;
     nuco = cols / ratio ; 
     fprintf(outspace , "rows %i\ncols %i\nspp %i\ndata" , nuro , nuco , spp ) ; 
     for ( a = 0 ; a < nuro ; ++ a ) { 
      for ( b = 0 ; b < nuco ; ++ b ) { 
         if ( !nudefd [ a ] [ b ] ) continue ; 
         fprintf(outspace,"\nA%i-%i\n" , a , b ) ; 
         for ( c = 0 ; c < spp ; ++ c ) { 
             mb = 1 << ( c % 32 ) ; 
             mc = c / 32 ; 
             if ( ( numa [ a ] [ b ] [ mc ] & mb ) ) putc ( '1' , outspace ) ; 
             else
               if ( ( nuinfma [ a ] [ b ] [ mc ] & mb ) ) putc ( '2' , outspace ) ;
               else putc ( '0' , outspace ) ; }}}
   for ( a = 1 + ( rows / ratio ) ; a -- ; ) { 
        for ( b = 1 + ( cols / ratio ) ; b -- ; ) { 
            realloc ( ( void * ) numa [ a ] [ b ] , 0 ) ;
            realloc ( ( void * ) nuinfma [ a ] [ b ] , 0 ) ; } 
        realloc ( ( void * ) numa [ a ] , 0 ) ;
        realloc ( ( void * ) nuinfma [ a ] , 0 ) ;
        realloc ( ( void * ) nudefd [ a ] , 0 ) ; }
   realloc ( ( void * ) numa , 0 ) ;
   realloc ( ( void * ) nuinfma , 0 ) ;
   realloc ( ( void * ) nudefd , 0 ) ; 
   fprintf(outspace , "\n;\n" ) ;
   curcmd_loop = cmd_loop ; 
   showcurset () ; 
   captf( "\nSaved data (divided in %i) to file" , ratio ) ; 
   return 0 ; 
}    

void setjunkstrtocurfunc ( )
{
    if ( curcmd_loop == cmd_loop ) strcpy ( junkstr , " " ) ;
    if ( curcmd_loop == show_consensus ) {
        if ( chain_spp )
             sprintf ( junkstr , "Cut %i, against any included area", conscut ) ;
        else sprintf ( junkstr , "Cut %i, against every included area", conscut ) ; }
    if ( curcmd_loop == viewscore ) strcpy ( junkstr , "Viewing scores..." ) ;
    if ( curcmd_loop == showspecies ) strcpy ( junkstr , "Showing species distribution(s)..." ) ;
    if ( curcmd_loop == showfauna ) strcpy ( junkstr , "Viewing fauna..." ) ; 
    if ( curcmd_loop == viewmarks ) strcpy ( junkstr , "Viewing marked sets..." ) ; 
    if ( curcmd_loop == show_duwc ) {
        if ( cur_duwc_act == 'W' ) strcpy ( junkstr , "Viewing contained sets...") ;
        if ( cur_duwc_act == 'U' ) strcpy ( junkstr , "Viewing containing sets..." ) ; 
        if ( cur_duwc_act == 'C' ) strcpy ( junkstr , "Viewing overlapping sets...") ; 
        if ( cur_duwc_act == '=' ) strcpy ( junkstr , "Viewing identical sets..." ) ; }
    return ;
}    

void setcellon ( int which , int isdblclk )
{
    unsigned long int mc , mb ;
    int sp = current_species ;
    int cursrow , curscol ;
    Artyp * ar ; 
    if ( curcmd_loop != cmd_loop && 
         curcmd_loop != showspecies ) return ; 
    cursrow = which / cols ; 
    curscol = which % cols ;
    if ( !isdefd[cursrow][curscol] && !isdblclk ) return ;
    if ( curcmd_loop == cmd_loop ) {
        mc = which / 32 ;
        mb = 1 << ( which % 32 ) ;
        if ( isdblclk ) {
            if ( isdefd[cursrow][curscol] ) return ; 
            if ( !isdefd[cursrow][curscol] ) 
              for ( ar = rec + numrecs ; ar -- > rec ; ) 
                    ar -> lst[mc] &= ~mb ; 
            isdefd[cursrow][curscol] = 1 ; }
        else {
            if ( ( recptr -> lst[mc] & mb ) ) return ;
            ++ recptr -> size ;
            recptr -> lst[mc] |= mb ;
            dorule5 ( ) ; }
        showcurset () ; }
    if ( curcmd_loop == showspecies ) {
         if ( species_tree != NULL && sp >= numterminals ) {
            errmsg ( "Cannot edit distribution of species groups!" , NULL ) ;
            return ; }
         if ( isdblclk ) {
             errmsg ( "Double click (right button)\nadds a cell in default mode!\nPress <esc> to go to default mode." , NULL ) ;
             return ; }
         mb = 1 << ( sp % 32 ) ; 
         mc = sp / 32 ; 
         lst = matrix [ cursrow ] [ curscol ] ;
         inflst = assmatrix [ cursrow ] [ curscol ] ;
         paint_mode = 1 ; 
         if ( paintspcell ( curscol , cursrow , mc , mb , sp ) )
              redoallscores = 1 ;
         else return ; 
         screenf("Species Nr. %i (%i cells)\n" , sp , numentries [ sp ]  ) ; 
         dospmap ( sp ) ; }
    return ; 
}            
        
void setcelloff ( int which , int isdblclk )
{
    unsigned long int mc , mb , msk , j , k ; 
    int sp = current_species ;
    int cursrow , curscol , numar ;
    Artyp * ar ; 
    if ( curcmd_loop != cmd_loop && 
         curcmd_loop != showspecies ) return ; 
    cursrow = which / cols ; 
    curscol = which % cols ; 
    if ( curcmd_loop == cmd_loop ) {
        if ( isdblclk ) {
              if ( !isdefd[cursrow][curscol] ) return ;
              if ( !sure ( "Delete cell from all areas" ) ) return ; 
              numar = which ; 
              isdefd [ cursrow ] [ curscol ] = 0 ; 
              for ( j = spp ; j -- ; )  
                  if ( ( matrix [ cursrow ] [ curscol ] [ j / 32 ] & ( 1 << ( j % 32 ) ) ) ) 
                      { -- numentries [ j ] ; 
                        matrix [ cursrow ] [ curscol ] [ j / 32 ] ^= ( 1 << ( j % 32 ) ) ; } 
              j = ( cursrow * cols ) + curscol ; 
              msk = 1 << ( numar % 32 ) ; 
              mc = numar / 32 ; 
              ar = rec - 1 ; 
              for ( k = 0 ; k < numrecs ; ++ k ) { 
                ++ ar ; 
                if ( ( ar -> lst[ j / 32 ] & ( 1 << ( j % 32 ) ) ) ) { 
                        -- ar -> size ; 
                        ar -> lst[ j / 32] ^= ( 1 << ( j % 32 ) ) ; }}
              redoallscores = 0 ;
              doallscores () ; }
        else {
           mc = which / 32 ;
           mb = 1 << ( which % 32 ) ;
           if ( !( recptr -> lst[mc] & mb ) ) return ;
           -- recptr -> size ;
           recptr -> lst[mc] &= ~mb ; 
           dorule5 ( ) ; }
        showcurset () ; }
    if ( curcmd_loop == showspecies ) {
         if ( species_tree != NULL && sp >= numterminals ) {
            errmsg ( "Cannot edit distribution of species groups!" , NULL ) ;
            return ; }
         if ( isdblclk ) {
             errmsg ( "Double click (right button)\neliminates cells in default mode!\nPress <esc> to go to default mode." , NULL ) ;
             return ; }
         mb = 1 << ( sp % 32 ) ; 
         mc = sp / 32 ; 
         lst = matrix [ cursrow ] [ curscol ] ;
         inflst = assmatrix [ cursrow ] [ curscol ] ;
         paint_mode = 0 ; 
         if ( paintspcell ( curscol , cursrow , mc , mb , sp ) )
              redoallscores = 1 ;
         else return ; 
         screenf("Species Nr. %i (%i cells)\n" , sp , numentries [ sp ]  ) ; 
         dospmap ( sp ) ; }
    win_refresh () ; 
    return ; 
}

short int * treeis , * matchtab ;
short int numtaxa ; 

void create_file_for_tnt ( FILE * where , int ass_is_pres ) 
{  int a , b , c , mc , numar ; 
   int32 mb ;
   int actspp = 0 ;
   for ( a = 0 ; a < spp ; ++ a ) 
       if ( ( spact[a/32] & ( 1 << ( a % 32 ) ) ) ) ++ actspp ; 
   fprintf(where , "break=; report=;piwe=;\nxread 'Data from VNDM' %i %i\n" ,
            actspp , numtaxa ) ;
   fprintf ( where , "\nROOT\n" ) ;
   for ( c = 0 ; c < spp ; ++ c )
         if ( ( spact[c/32] & ( 1 << (c % 32 ) ) ) )
             putc ( '0' , where ) ; 
   for ( a = 0 ; a < rows ; ++ a ) { 
      for ( b = 0 ; b < cols ; ++ b ) { 
         if ( !isdefd [ a ] [ b ] ) continue ;
         fprintf(where ,"\nA%i_%i\n" , a , b ) ; 
         for ( c = 0 ; c < spp ; ++ c ) {
             mb = 1 << ( c % 32 ) ; 
             mc = c / 32 ; 
             if ( !( spact[mc] & mb ) ) continue ; 
             if ( ( matrix [ a ] [ b ] [ mc ] & mb ) ) putc ( '1' , where ) ; 
             else
                 if ( ( assmatrix [ a ] [ b ] [ mc ] & mb ) &&
                       ass_is_pres ) putc ( '1' , where ) ; 
                 else putc ( '0' , where ) ; }}}
   fprintf( where , "\n;\n" ) ;
   fprintf ( where ,
        "piwe- ; \n"
        "hold 100 ; \n"
        "riddup*;   \n"
        "ratchet : iter 15 ;\n"
        "mult20 = ho1 rat ; \n"
        "hold+1;         \n"
        "conden ;        \n"
        "collap notemp ; \n"
        "riddup-;        \n"
        "nelsen*;        \n"
        "taxname- ;      \n"
        "tsave*tmp.tre;  \n"
        "save/;  \n"
        "quit;   \n" ) ; 
   return ; 
} 

int my_spawn( char * argus, ...)
{
    char jstr[512], qqqstr[512];
    STARTUPINFO startinfo;
    PROCESS_INFORMATION pinfo;
    char **cpp = &argus, *cp;
    DWORD how;
    how = 0;
    qqqstr[0] = 0 ;
    while( cp = * cpp ++ ) { 
            strcat(qqqstr, cp );
            strcat(qqqstr," ");}
        startinfo.cb = sizeof(STARTUPINFO);
        startinfo.lpReserved = NULL;
        startinfo.lpDesktop = NULL;
        if ( !isforsample ) 
             wsprintf(jstr,"SEARCHING...");
        else wsprintf(jstr,"REPL. %i" , isforsample );
        startinfo.lpTitle = jstr;
        startinfo.dwFlags = STARTF_USEPOSITION | STARTF_USESIZE ;
        startinfo.dwX = 350 ; 
        startinfo.dwXSize = 400 ; 
        startinfo.dwY = 150 ; 
        startinfo.dwYSize = 230 ; 
        startinfo.cbReserved2 = NULL;
        startinfo.wShowWindow = SW_SHOW;
        if(CreateProcess(NULL, qqqstr, NULL, NULL, FALSE ,
            HIGH_PRIORITY_CLASS | 0, NULL, NULL, &startinfo, &pinfo))
        WaitForSingleObject(pinfo.hProcess,INFINITE);
            else {
                noisy() ; 
                MessageBox(hwnd,"Could not spawn SEARCH!","Spawn error",MB_OK | MB_ICONERROR );
                return(255);
            }
        GetExitCodeProcess(pinfo.hProcess, &how);
        return( how );
}


int treadcom( FILE * inp )
{ int trees_read = 0, a , i ;
  char car = ' ';
  while ( getc ( inp ) != 39 && !feof ( inp ) ) ;
  while ( getc ( inp ) != 39 && !feof ( inp ) ) ;
  while ( isspace ( car = getc ( inp ) ) && !feof ( inp ) ) ;
  if ( feof ( inp ) ) return 0 ; 
  return leatre( treeis , inp );
} 

int leatre( short int * where , FILE * inp )
{
   int htu, unbalpars, atnode, i;
   short int *an;
   char car = '('; 
   an = where ;
   for( htu = numtaxa; htu--; ) an[htu] = 0; 
   htu = atnode = numtaxa - 1; 
   unbalpars = 0; 
   while(car!='*' && car!=';') { 
      if(car=='(')
          { an[htu+1]=atnode;
            atnode = ++htu;
            --unbalpars; } 
      else if(car==')') { atnode = an[atnode]; ++unbalpars; }
            else { ungetc ( car , inp ) ; 
                   fscanf ( inp , " %i" , &i ) ;
                   if( an[i] ) {
                       sprintf ( junkstr , "Taxon %i repeated" , i ) ; 
                       errmsg( junkstr , Null);
                       return 0 ; }
                   an[ i ] = atnode; }
      car = ' ' ;
      while ( isspace ( car ) ) car = getc ( inp ) ; }
   if(unbalpars>0) {
       errmsg("Too many trailing parentheses in tread", Null);
       return 0 ; }
   an[numtaxa] = ++htu;
   for ( i = htu ; i -- > numtaxa; ) matchtab [ i ] = 0 ;
   for ( i = htu ; i -- ; )
          ++ matchtab [ an [ i ] ] ; 
   for ( i = htu ; i -- > numtaxa; )
        if ( matchtab [ i ] < 2 ) {
            errmsg("Sorry, couldn't read tree (unbalanced parents.)", Null ) ;
            return 0 ; }
   return 1 ;
} 

void grouptoarea ( int nod )
{
   int a , b , x ; 
   for ( a = arcells ; a -- ; ) recptr -> lst [a] = 0 ;
   recptr -> size = recptr -> mark = 0 ;
   for ( a = 1 ; a < numtaxa ; ++ a ) {
       b = treeis[a] ; 
       while ( b != nod && b != numtaxa ) b = treeis[b] ;
       if ( b == nod ) {
           x = matchtab[a] ;
           recptr -> size ++ ;
           recptr -> lst [ x / 32 ] |= 1 << ( x % 32 ) ; }}
   dorule5 ( ) ;
   return ; 
}   

void make_tree_into_areas ( void )
{
    FILE * inp ;
    int a , b , didanempty = 0 ;
    inp = fopen ( "tmp.tre" , "r" ) ;
    if ( inp == NULL ) {
        errmsg ( "Sorry, cannot open tree-file!" , Null ) ;
        return ; }
    if ( !treadcom ( inp ) ) {
        errmsg ( "Sorry, error reading tree from file!" , Null ) ;
        return ; }
    pleasewait ( "Creating sets from tree" ) ; 
    numtaxa = 1 ; 
    for ( a = 0 ; a < rows ; ++ a )  
      for ( b = 0 ; b < cols ; ++ b ) { 
         if ( !isdefd [ a ] [ b ] ) continue ;
         matchtab[numtaxa] = ( a * cols ) + b ; 
         numtaxa ++ ; }
    numrecs = 0 ;
    recptr = rec ; 
    for ( a = treeis[numtaxa] ; -- a > numtaxa ; ) {
        if ( treeis[a] == treeis[0] ) continue ; 
        grouptoarea ( a ) ;
        recptr ++ ;
        numrecs ++ ;
        if ( numrecs == maxrecs ) {
            imdone () ;
            sprintf ( junkstr , "Cannot store more than %isets" , maxrecs ) ;
            errmsg ( junkstr , Null ) ; 
            break ; }}
     if ( recptr == rec ) {
         didanempty = 1 ;
         donewset () ; } 
     imdone () ; 
     curcmd_loop = cmd_loop ;
     recptr = rec ; 
     showcurset () ;
     if ( didanempty ) captf ( "No areas found!" ) ; 
     return ; 
}            

void doparsearch ( int ass_is_pres )
{
    FILE * saveto ;
    int a , b ; 
    strcpy ( comstring , "tmp.tnt" ) ;
    saveto = fopen ( comstring , "w" ) ;
    if ( saveto == NULL ) {
         errmsg ( "Sorry, can't open temporary file" , Null ) ;
         return ; }
    numtaxa = 1 ;
    for ( a = rows ; a -- ; ) for ( b = cols ; b -- ; )
      if ( isdefd[a][b] ) ++ numtaxa ; 
    matchtab = malloc ( 2 * numtaxa * sizeof ( short int ) ) ; 
    treeis = malloc ( 2 * numtaxa * sizeof ( short int ) ) ; 
    create_file_for_tnt ( saveto , ass_is_pres ) ;
    fclose ( saveto ) ;
    system ( "del tmp.tre" ) ; 
    a = my_spawn ( "tnt" , "tmp.tnt" , Null ) ;
    if ( a != 0 ) {
        MessageBox ( hwnd , "Place TNT (tnt.exe) in your path.\n\If you do not have TNT, check at\n"
                            "https://www.lillo.org.ar/phylogeny/tnt \n" , "Notice..." , MB_OK | MB_ICONINFORMATION ) ; 
        free ( treeis ) ;
        free ( matchtab ) ; 
        return ; }
    make_tree_into_areas () ; 
    free ( treeis ) ;
    free ( matchtab ) ;
    win_refresh () ; 
    return ; 
}

#define SETINT( x , y ) \
          { sprintf ( junkstr , "%i" , x ) ; \
            SetDlgItemText ( hdwnd , y , junkstr ) ; } 
#define GETINT( x , y ) \ 
          { GetDlgItemText(hdwnd, ( y ) , junkstr, 80); \ 
            x = atoi(junkstr); } 
#define SETFL( x , y ) \
          { sprintf ( junkstr , "%.3f" , x ) ; \
            SetDlgItemText ( hdwnd , y , junkstr ) ; } 
#define GETFL( x , y ) \ 
          { GetDlgItemText(hdwnd, ( y ) , junkstr, 80); \ 
            x = atof(junkstr); } 
#define BUTT_CHECK( ctrl ) SendDlgItemMessage( hdwnd,  ctrl , BM_SETCHECK, (WPARAM) BST_CHECKED , 0 )
#define BUTT_UNCHEK( ctrl ) SendDlgItemMessage( hdwnd,  ctrl , BM_SETCHECK, (WPARAM) BST_UNCHECKED , 0 )

char schstring[2048] ;
int skip_superfluous = 1 ;
int xskip_superfluous = 1 ;
int replace_existing_sets = 1 ;

BOOL CALLBACK RunNDMFunc(HWND hdwnd, UINT message, WPARAM wParam, LPARAM lParam)
{
    int i , j ;
    static int
        usswap = 1 , usprechk = 1 , 
        usclean = 0 , usn = 50000 , usm ;
    static double usM , usr = 0.99 ; 
    static int
        myswap , myp , mym , 
        myclean , myn , myperc , myk , mystart , myskipsup , myxskip , myreplace ;
    static double myM , myr , usersubo ;
    static int myprechk ;
    static int mynumreps = 1 ;
    static int myframeit ; 
    char * cp ; 
    HWND hWho ;
    switch(message) {
        case WM_INITDIALOG :
                   usM = sch_minimum_total_score ;
                   usm = sch_minimum_scoring_spp ; 
                   SETFL ( usr , 111 ) ;
                   SETFL ( usM , 112 ) ;
                   SETINT ( usm , 118 ) ;
                   if ( usswap == 1 ) BUTT_CHECK ( 114 ) ;
                   else BUTT_CHECK ( 115 ) ;
                   myprechk = usprechk ; 
                   if ( myprechk ) BUTT_CHECK ( 144 ) ;
                   if ( use_edge_props ) BUTT_CHECK ( 116 ) ;
                   SETINT ( usclean , 122 ) ;
                   SETINT ( usn , 125 ) ;
                   SETINT ( compare_perc , 129 ) ;
                   SetDlgItemText ( hdwnd , 134 , "none" ) ;
                   myr = usr ;
                   myM = usM ;
                   mym = usm ; 
                   myswap = usswap ;
                   myp = use_edge_props ;
                   myclean = usclean ;
                   myn = usn ;
                   myperc = compare_perc ;
                   myk = -1 ;
                   myframeit = 0 ; 
                   mystart = usersubo = 0 ;
                   myskipsup = skip_superfluous ;
                   myxskip = xskip_superfluous ;
                   myreplace = replace_existing_sets ; 
                   if ( myskipsup ) BUTT_CHECK ( 145 ) ;
                   if ( myxskip ) BUTT_CHECK ( 146 ) ;
                   if ( myreplace ) BUTT_CHECK ( 149 ) ; 
                   SETFL ( usersubo , 143 ) ;  
                   SetFocus ( GetDlgItem ( hdwnd , IDOK ) ) ;
                   SET_UPDOWN( 152, 1 , 32767 , rseed ) ;
                   SET_UPDOWN ( 156 , 1 , 1000 , mynumreps ) ; 
                   break ; 
        case WM_COMMAND :
                switch(LOWORD(wParam)){
                        case 146 :
                           myxskip = 1 - myxskip ;
                           break ; 
                        case 145 :
                           myskipsup = 1 - myskipsup ;
                           break ; 
                        case 144 :
                            myprechk = 1 - myprechk ;
                            break ; 
                        case 140 :
                            mystart = 1 - mystart ;
                            break ; 
                        case 114 : myswap = 1 ; break ;
                        case 115 :  myswap = 2 ; break ;
                        case 158 :
                           myframeit = 1 - myframeit ;
                           if ( myframeit ) {
                              GetDlgItemText( hdwnd, 134 , junkstr, 80);
                              if ( !strcmp ( junkstr , "none" ) ) {
                                  i = recptr - rec ; 
                                  SETINT ( i , 134 ) ; }} 
                           break ; 
                        case 116 :
                           myp = 1 - myp ;
                           break ;
                        case 149 :
                            myreplace = 1 - myreplace ;
                            break ; 
                        case IDOK:
                            GETINT ( rseed , 151 ) ;
                            GETINT ( mynumreps , 155 ) ; 
                            GETFL ( myr , 111 ) ;
                            GETFL ( myM , 112 ) ;
                            GETINT ( mym , 118 ) ;
                            GETINT ( myclean , 122 ) ;
                            GETINT ( myn , 125 ) ;
                            GETINT ( myperc , 129 ) ;
                            GETFL ( usersubo , 143 ) ; 
                            sch_minimum_total_score = usM ;
                            sch_minimum_scoring_spp = usm ; 
                            compare_perc = myperc ;
                            use_edge_props = myp ;
                            frame_the_search = 0 ; 
                            GetDlgItemText(hdwnd, 134 , junkstr, 80);
                            if ( isdigit ( junkstr [0] ) ) {
                                myk = atoi ( junkstr ) ;
                                if ( myframeit ) frame_the_search = 1 ; }

                            if ( !isforsample )      
                                sprintf ( schstring, 
                                     "tmp.dat -ltmp.ndm -! -data -r%f -M%f -m%i -swap%i -n%i -%%%i -fi%f -fa%f -fo%f -fd%f -fn%f -e%i -T%i " ,
                                     myr , myM , mym , myswap , myn , myperc ,
                                     iifac , iafac , oufac , oafac , ononafac , abslim , min_pres_perc ) ;
                            else 
                                sprintf ( schstring, 
                                     "tmp.dat -ltmp.ndm -data -r%f -M%f -m%i -swap%i -n%i -%%%i -fi%f -fa%f -fo%f -fd%f -fn%f -e%i -T%i " ,
                                     myr , myM , mym , myswap , myn , myperc ,
                                     iifac , iafac , oufac , oafac , ononafac , abslim , min_pres_perc ) ;
                            usclean = myclean ; 
                            if ( myclean > 0 ) {
                                cp = schstring + strlen ( schstring ) ;
                                sprintf ( cp , "-clean %i ", myclean ) ; }
                            if ( musthaveone != 1 ) {
                                cp = schstring + strlen ( schstring ) ;
                                sprintf ( cp , "-h%i ", musthaveone ) ; }
                            if ( usersubo > 0 ) {
                                cp = schstring + strlen ( schstring ) ;
                                sprintf ( cp , " -o%f ", usersubo ) ; }
                            if ( mystart ) {
                                i = query ;
                                query = 0 ; 
                                sprintf ( comstring , "tmp.ini" ) ;
                                cmd_loop ( 'L' ) ;
                                query = i ; 
                                strcat ( schstring , " -starttmp.ini " ) ; }
                            if ( myprechk ) strcat ( schstring , "-postchk " ) ;
                            if ( rseed != 1 ) {
                                cp = schstring + strlen ( schstring ) ;
                                sprintf ( cp , "-d%i ", rseed ) ; }
                            if ( mynumreps > 1 ) {
                                cp = schstring + strlen ( schstring ) ;
                                sprintf ( cp , "-#%i ", mynumreps ) ; }
                            if ( minimum_sp_score > 0 ) {
                                cp = schstring + strlen ( schstring ) ;
                                sprintf ( cp , "-b%f ", minimum_sp_score ) ; }
                            usr = myr ;
                            usM = myM ;
                            usm = mym ;
                            usswap = myswap ;
                            usn = myn ;
                            usprechk = myprechk ;
                            skip_superfluous = myskipsup ;
                            xskip_superfluous = myxskip ;
                            replace_existing_sets = myreplace ; 
                            if ( myxskip ) strcat ( schstring , "-sskip " ) ;
                            else
                               if ( myskipsup ) strcat ( schstring , "-skip " ) ; 
                            if ( myk >= 0 ) {
                                if ( myk > 0 ) copyar ( 0 , myk ) ;
                                recptr = rec ;
                                numrecs = 1 ;
                                if ( !myframeit ) {   // when framing, must save constraint area as reduced...
                                    sprintf ( comstring , "tmp.kkk" ) ;
                                    cmd_loop ( 'L' ) ; }
                                strcat ( schstring, "-ktmp.kkk " ) ; }
                            if ( myp ) strcat ( schstring , "-p " ) ;    
                            EndDialog(hdwnd,1);
                            break ; 
                        case IDCANCEL :
                           EndDialog(hdwnd,0);
                        default : break; }
         break; }
    return 0;
}

void dondmsearch ( int for_linux )
{
    int a , b ;
    FILE * scriptfile ; 
    Artyp * recptr = rec + numrecs ; 
    b = 0 ;
    for ( a = 0 ; a < spcells && !b ; ++ a )
       if ( spact[a] ) ++ b ;
    if ( !b ) {
        MessageBox ( hwnd , "Nothing to search:\n   no active species!" , "Error" , MB_OK | MB_ICONERROR ) ;
        return ; }
/*******
    if ( !for_linux ) 
     while ( recptr -- > rec ) 
        if ( recptr -> size > 0 ) {           
            if ( !sure ( "Doing a new search will discard all\nthe existing sets. Do it anyway" ) ) return ;
            break ; }
********/
    a = DialogBox ( hInst, "RunNDMDB", hwnd, (DLGPROC) RunNDMFunc ) ;
    if ( !a ) return ;
    strcpy ( comstring , "tmp.dat" ) ;
    cmd_loop ( 'o' ) ;
    strcpy ( comstring , "d" ) ;
    if ( frame_the_search ) {
        if ( rec[ 0 ].size == 0 ) {
            MessageBox ( hwnd , "Area to use as frame is empty" , "Error" , MB_OK | MB_ICONERROR ) ;
            return ; }
        strcpy ( comstring , "@" ) ; }
    cmd_loop ( 's' ) ;
    fclose ( outspace ) ;
    if ( no_useful_spp ) return ; 
    outspace = NULL ;
    if ( !for_linux ) {
       ShowWindow ( hwnd , SW_MINIMIZE ) ;
       if ( ndm_bin_name == NULL ) 
            a = my_spawn ( "ndm" , schstring , Null ) ;
       else 
            a = my_spawn ( ndm_bin_name , schstring , Null ) ;
       ShowWindow ( hwnd , SW_RESTORE ) ; 
       if ( a == 255 ) {
           errmsg ( "Cannot run NDM!\n(try specifying location of\nbin in file \".vndm.rc\")" , Null ) ; return ; }
       if ( replace_existing_sets ) {
           numrecs = 0 ;
           recptr = rec ; }
       else recptr = rec + numrecs ; 
       strcpy ( comstring , "tmp.ndm" ) ;
       scriptfile = fopen ( comstring , "rb" ) ;
       if ( scriptfile != NULL ) {
           a = getc ( scriptfile ) ;
           ungetc ( a , scriptfile ) ;
           if ( !feof ( scriptfile ) ) {
              fclose ( scriptfile ) ;
              if ( frame_the_search ) read_reduced_sets_from_file ( ) ; 
              else read_sets_from_file ( ) ;
              recptr = rec ;
              curcmd_loop = cmd_loop ; 
              delete_duplicates ( 1 ) ; }
           else fclose ( scriptfile ) ; }
       if ( numrecs ) {
           showcurset () ;
           captf ( "NDM SEARCH: %i distinct sets found (duplicates discarded)" , numrecs ) ; }
       else {
           donewset () ;
           showcurset () ; 
           captf ( "NDM SEARCH: no set found (one empty set created)" ) ; }}
   else {  // i.e. create script for Linux
         scriptfile = fopen ( "runndm" , "w" ) ;
         if ( scriptfile == NULL ) {
             showcurset () ;
             errmsg ( "Cannot open file \"runndm\" to write script" , Null ) ;
             return ; }
         fprintf ( scriptfile , "ndm %s -bground &" , schstring ) ;
         fclose ( scriptfile ) ;
         captf ( "Created Linux script, in file \"runndm\"\n(data in \"tmp.dat\", results will be written to \"tmp.ndm\")" ) ; }
}    


BOOL CALLBACK GetFIAODNFunc(HWND hdwnd, UINT message, WPARAM wParam, LPARAM lParam)
{
    int i , j ;
    double nui , nua , nuo , nud , nun ; 
    HWND hWho ;
    switch(message) {
        case WM_INITDIALOG :
                   SETFL ( iifac , 104 ) ;
                   SETFL ( iafac , 105 ) ;
                   SETFL ( oufac , 106 ) ;
                   SETFL ( oafac , 114 ) ;
                   SETFL ( ononafac , 115 ) ;
                   break ; 
        case WM_COMMAND :
                switch(LOWORD(wParam)){
                     case IDOK:
                        GETFL ( nui , 104 ) ;
                        GETFL ( nua , 105 ) ;
                        GETFL ( nuo , 106 ) ;
                        GETFL ( nud , 114 ) ;
                        GETFL ( nun , 115 ) ;

                        if ( nuo <= 0 || nuo > 1000000 || 
                             nud <= 0 || nud > 1000000 || 
                             nun <= 0 || nun > 1000000 ) {
                                        showcurset () ;
                                        captf( "\nOut factors must be 0 < f <= 10^6" ) ;
                                        EndDialog(hdwnd,1);
                                        return 0 ; }
                        if ( nui > 1 || nua > 1 ) {
                                      showcurset () ;
                                      captf( "\nInferred/Assumed factor must be 0 <= f <= 1" ) ;
                                      EndDialog(hdwnd,0);
                                      return 0 ; }
                        i = 0 ;
                        if ( nui != iifac ) i = 1 ; 
                        if ( nua != iafac ) i = 1 ; 
                        if ( nuo != oufac ) i = 1 ; 
                        if ( nud != oafac ) i = 1 ; 
                        if ( nun != ononafac ) i = 1 ; 
                        iifac = nui ;
                        iafac = nua ;
                        oufac = nuo ;
                        oafac = nud ;
                        ononafac = nun ;

                        EndDialog(hdwnd,i);
                        return i ; 
                        break ; 
                     case IDCANCEL :
                           EndDialog(hdwnd,0);
                     default : break; }
         break; }
    return 0;
}


void dlg_fiaodn ( void )
{
    int a ; 
    a = DialogBox ( hInst, "FIAODNDB", hwnd, (DLGPROC) GetFIAODNFunc ) ; 
    win_refresh () ; 
    if ( !a ) return ;
    curcmd_loop = cmd_loop ; 
    doallscores () ;
    showcurset () ;
    return ; 
}    

void calculate_score_onoff ( int which )
{
    unsigned long int was ;
    int szwas = recptr -> size ; 
    char * cp = junkstr + strlen ( junkstr ) ;
    double with , wout ; 
    unsigned long int mc = which / 32 ;
    unsigned long int mb = 1 << ( which % 32 ) ; 
    was = recptr -> lst[mc] ;
    recptr -> lst[mc] |= mb ;
    if ( was != recptr -> lst[mc] ) recptr -> size ++ ;
    with = dorule5 () ;
    recptr -> size = szwas ;
    recptr -> lst[mc] &= ~mb ;
    if ( was != recptr -> lst[mc] ) recptr -> size -- ;
    wout = dorule5 () ;
    recptr -> size = szwas ;
    recptr -> lst[mc] = was ;
    dorule5 () ; 
    if ( with == wout ) sprintf ( cp , " (same)" ) ; 
    else
      if ( ( with > wout && !( was & mb ) ) ||
         ( with < wout && ( was & mb ) ) ) 
         if ( with > wout ) 
             sprintf ( cp , " (change GAINS %.5f)" , with - wout ) ;
         else sprintf ( cp , " (change GAINS %.5f)" , wout - with ) ;
    else 
       if ( with < wout ) sprintf ( cp , " (change loss %.5f)" , wout - with ) ;
       else sprintf ( cp , " (change loss %.5f)" , with - wout ) ;
    return ; 
}


void change_basic_grid ( int act , int iscontrol , int iscapital )
{
    double widwas , heiwas ; 
    if ( !iscontrol ) {
       if ( act == VK_DOWN ) truecellhei += 0.5 ;
       if ( act == VK_UP ) truecellhei -= 0.5 ;
       if ( act == VK_RIGHT ) truecellwid += 0.5 ;
       if ( act == VK_LEFT ) truecellwid -= 0.5 ;
       if ( tolower ( act ) == 'x' ) 
           if ( iscapital ) 
                truecellwid += 0.01 ;
           else truecellwid -= 0.01 ;
       if ( tolower ( act ) == 'y' )
           if ( iscapital ) truecellhei += 0.01 ;
           else truecellhei -= 0.01 ; 
       if ( truecellhei < 0.01 ) truecellhei = 0.01 ; 
       if ( truecellwid < 0.01 ) truecellwid = 0.01 ;
       cols = 2 ; 
       while ( grid_startx + ( truecellwid * ( cols - 1 ) ) < maxx ) ++ cols ; 
       rows = 2 ; 
       while ( grid_starty + ( truecellhei * ( rows - 1 ) ) < maxy ) ++ rows ; }
    else {
      if ( ctrl_arrow_changes_org ) {
         if ( act == VK_DOWN ) grid_starty += 0.1 ;
         if ( act == VK_UP )  grid_starty -= 0.1 ;
         if ( act == VK_RIGHT ) grid_startx += 0.1 ;
         if ( act == VK_LEFT ) grid_startx -= 0.1 ;
         /******  negative coordinates are now allowed... 
         if ( grid_startx <= 0 ) grid_startx = 0 ;
         if ( grid_starty <= 0 ) grid_starty = 0 ; *****/ }
      else {
         heiwas = truecellhei ; 
         widwas = truecellwid ; 
         if ( act == VK_UP ) truecellhei += ( truecellhei * 0.33333333333333333) ;
         if ( act == VK_DOWN )  truecellhei -=  ( truecellhei * 0.25 ) ;
         if ( act == VK_LEFT ) truecellwid += ( truecellwid * 0.3333333333333333) ;
         if ( act == VK_RIGHT ) truecellwid -= ( truecellwid * 0.25 ) ;
         if ( grid_created ) {
             if ( truecellhei < mincellhei || truecellwid < mincellwid ) { 
                 sprintf ( junkstr + 1 , "Cannot reduce cell size to less than a third the\noriginal size (i.e. less than %.5fx%.5f)\nReduce to the maximum possible" , mincellwid , mincellhei ) ; 
                 query ++ ; 
                 if ( ! sure ( junkstr + 1 ) ) {
                     query -- ; 
                     truecellhei = heiwas ; 
                     truecellwid = widwas ;
                     return ; }
                  query -- ; 
                  if ( truecellhei < mincellhei ) truecellhei = mincellhei ;    
                  if ( truecellwid < mincellwid ) truecellwid = mincellwid ; }}
         if ( truecellhei < 0.01 ) truecellhei = 0.01 ; 
         if ( truecellwid < 0.01 ) truecellwid = 0.01 ;
         cols = 2 ; 
         while ( grid_startx + ( truecellwid * ( cols - 1 ) ) < maxx ) ++ cols ; 
         rows = 2 ; 
         while ( grid_starty + ( truecellhei * ( rows - 1 ) ) < maxy ) ++ rows ;
         }}  
    return ; 
}

  
void create_matrix_from_points ( int makeanew  )
{
   int a , b , c ;
   int trurows = rows , trucols = cols ; 
   Artyp * dorec ;
   pleasewait ( "Allocating memory" ) ;   
   spcells = ( spp + 31 ) / 32 ; 
   /*  This is used to allocate extra mem., so that grid size can be changed... */
   rows = rows * maxgridmult ;
   cols = cols * maxgridmult ;
   mincellwid = truecellwid / maxgridmult ; 
   mincellhei = truecellhei / maxgridmult ; 
   arcells = ( ( rows * cols ) + 31 ) / 32 ; 
   totareas = rows * cols ;
   memerr ( widefilter = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ; 
   memerr ( archeckd = ( int * ) malloc ( totareas * sizeof ( int ) ) ) ;
   memerr ( fillist = ( char ** ) malloc ( rows * sizeof ( char * ) ) ) ;
   for ( a = rows ; a -- ; )
        memerr ( fillist [ a ] = ( char * ) malloc ( cols * sizeof ( char ) ) ) ; 
   a = totareas ; 
   if ( a < ( spp + 31 ) ) a = spp + 31 ; 
   memerr ( tmplist = ( int * ) malloc ( a * sizeof ( int ) ) ) ; 
   memerr ( intersptr = (int32 *) malloc ( spcells * sizeof ( int32 ) ) ) ; 
   memerr ( dablor = (int32 *) malloc ( spcells * sizeof ( int32 ) ) ) ; 
   memerr ( dabland = (int32 *) malloc ( spcells * sizeof ( int32 ) ) ) ; 
   memerr ( setlist = ( int * ) malloc ( rows * cols * sizeof ( int ) ) ) ; 
   memerr ( nosetlist = ( int * ) malloc ( rows * cols * sizeof ( int ) ) ) ; 
   memerr ( numentries = ( int * ) malloc ( spp * sizeof ( int ) ) ) ; 
   memerr ( numassentries = ( int * ) malloc ( spp * sizeof ( int ) ) ) ;
   memerr ( listin = ( int * ) malloc ( totareas * sizeof ( int ) ) ) ; 
   memerr ( listadja = ( int * ) malloc ( totareas * sizeof ( int ) ) ) ; 
   memerr ( listnonadja = ( int * ) malloc ( totareas * sizeof ( int ) ) ) ;
   memerr ( spscore = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dout = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dpres = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dinf = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dass = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dadja = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dnadja = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( isdefd = ( char ** ) malloc ( rows * sizeof ( char * ) ) ) ; 
   for ( a = rows ; a -- ; )  
        memerr ( isdefd [ a ] = ( char * ) malloc ( cols * sizeof ( char ) ) ) ; 
   memerr ( matrix = ( int32 *** ) malloc ( rows * sizeof ( int32 ** ) ) ) ; 
   memerr ( assmatrix = ( int32 *** ) malloc ( rows * sizeof ( int32 ** ) ) ) ; 
   for ( a = rows ; a -- ; ) { 
        memerr ( matrix [ a ] = ( int32 ** ) malloc ( cols * sizeof ( int32 * ) ) ) ; 
        memerr ( assmatrix [ a ] = ( int32 ** ) malloc ( cols * sizeof ( int32 * ) ) ) ; 
        for ( b = cols ; b -- ; )  { 
             memerr ( matrix [ a ] [ b ] = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ; 
             memerr ( assmatrix [ a ] [ b ] = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ; }}
   if ( !maxrecs ) 
   maxrecs = numrecs + 10000 ; 
   memerr ( rec = ( Artyp * ) malloc ( ( maxrecs ) * sizeof ( Artyp ) ) ) ; 
   memerr ( arlist = ( Artyp ** ) malloc ( ( maxrecs ) * sizeof ( Artyp * ) ) ) ; 
   dorec = rec ;
   if ( ignore_sp_lists ) {
       memerr ( fakesplist = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ;
       for ( a = 0 ; a < spcells ; ++ a ) fakesplist [ a ] = 0 ; }
   for ( a = maxrecs ; a -- ; ) { 
       memerr ( dorec -> lst = ( int32 * ) malloc ( arcells * sizeof ( int32 ) ) ) ;
       if ( ignore_sp_lists ) dorec -> splist = fakesplist ; 
       else memerr ( dorec -> splist = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ; 
       ++ dorec ; } 
   numrecs = 0 ; 
   for ( a = rows ; a -- ; )
     for ( b = cols ; b -- ; ) {
       isdefd[a][b] = 0 ; 
       for ( c = spcells ; c -- ; ) matrix [a][b][c] = assmatrix [a][b][c] = 0 ; }    
   for ( c = spp ; c -- ; ) numentries[c] = numassentries[c] = 0 ; 
   memerr ( splist = ( int32 * ) malloc ( arcells * sizeof ( int32 ) ) ) ;
   memerr ( inflist = ( int32 * ) malloc ( arcells * sizeof ( int32 ) ) ) ;
   memerr ( sccol = ( char ** ) malloc ( ( cols + 2 ) * sizeof ( char *  ) ) ) ; 
   for ( a = 0 ; a < ( cols + 2 ) ; ++ a ) 
          memerr ( sccol [ a ] = ( char * ) malloc ( ( rows + 2 ) * sizeof ( char ) ) ) ;   
  /*  recalculate_numentries ( -1 ) ;  */    // this was pointless; matrix hasn't been filled yet!!
   memerr ( spact = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ;
   for ( a = 0 ; a < spcells ; ++ a ) spact[a] = -1 ;
   rows = trurows ;
   cols = trucols ; 
   arcells = ( ( rows * cols ) + 31 ) / 32 ; 
   totareas = rows * cols ;
   imdone () ; 
   pleasewait ( "Creating matrix from points" ) ;   
   nitmatrix () ; 
   grid_created = 2 ;
   if ( makeanew  ) {
       donewset () ;
       cls () ;
       initializing = 0 ;
       showcurset () ; }
   sprintf ( junkstr , "\nCreated matrix, %i rows x %i cols" , rows , cols ) ; 
   spitit ( junkstr ) ; 
   imdone () ; 
}

int created_rows , created_cols ;
double created_wid = -1 , created_hei = -1 , created_orgy , created_orgx ;

void transfer_areas ( void )
{
    Artyp * rp ;
    double xbeg , xend , ybeg , yend ;
    int jx , jy , k ; 
    int a , b , c , d ; 
    double nux , nuy ;
    double at ; 
    int tojxend , tojyend , tojxbeg , tojybeg  ; 
    int oltota = created_rows * created_cols ;
    int32 mb , mc ; 
    for ( a = 0 , rp = rec ; a < numrecs ; ++ a , ++ rp ) {
        for ( b = 0 ; b < arcells ; ++ b ) splist[b] = 0 ; 
        for ( b = 0 , mb = 1 , mc = 0 ; b < oltota ; ++ b ) {
            if ( ( rp->lst[mc] & mb ) ) {
                jy = b / created_cols ;
                jx = b % created_cols ;
                xbeg = created_orgx + ( created_wid * jx ) ;
                ybeg = created_orgy + ( created_hei * jy ) ;
                xend = xbeg + created_wid ; 
                yend = ybeg + created_hei ;

                if ( jx > 0 ) {
                     k = ( jx - 1 ) + ( jy * created_cols ) ; 
                     if ( ( rp->lst[k/32] & ( 1 << ( k%32) ) ) == 0 ) 
                        xbeg += ( created_wid / 2 ) ; }
                if ( jx < created_cols - 1 ) {
                     k = ( jx + 1 ) + ( jy * created_cols ) ; 
                     if ( ( rp->lst[k/32] & ( 1 << ( k%32) ) ) == 0 ) 
                        xend -= ( created_wid / 2 ) ; }
                if ( jy > 0 ) {
                     k = jx  + ( ( jy - 1 ) * created_cols ) ; 
                     if ( ( rp->lst[k/32] & ( 1 << ( k%32) ) ) == 0 ) 
                        ybeg += ( created_hei / 2 ) ; }
                if ( jx < created_rows - 1 ) {
                     k = jx  + ( ( jy + 1 ) * created_cols ) ; 
                     if ( ( rp->lst[k/32] & ( 1 << ( k%32) ) ) == 0 ) 
                        yend -= ( created_hei / 2 ) ; }
                /***  For points just in corner...   **/
                if ( truecellwid < created_wid ) {
                  xbeg -= 0.0001 ; 
                  xend += 0.0001 ; }
                if ( truecellhei < created_hei ) {
                   ybeg -= 0.0001 ; 
                   yend += 0.0001 ; }

                tojxbeg = ( xbeg - grid_startx ) / truecellwid ;
                tojxend = tojxbeg ;
                while ( xend > 
                        ( grid_startx + ( ( tojxend + 1 ) * truecellwid ) ) )
                         ++ tojxend ; 
               
                tojybeg = ( ybeg - grid_starty ) / truecellhei ; 
                tojyend = tojybeg ;
                while ( yend >
                        ( grid_starty + ( ( tojyend + 1 ) * truecellhei ) ) ) 
                        ++ tojyend ; 

                for ( c = tojxbeg ; c <= tojxend ; ++ c )
                   for ( d = tojybeg ; d <= tojyend ; ++ d ) {
                       k = c + ( d * cols ) ;
                       splist[k/32] |= 1 << ( k % 32 ) ; }}
            if ( mb == BIT32 ) { mb = 1 ; ++ mc ; }
            else mb <<= 1 ; }
         rp -> size = 0 ;
         for ( b = arcells ; b -- ; ) {
             rp -> size += onbits ( ( mb = splist[b] ) ) ;
             rp -> lst[b] = mb ; }}
    return ;
}


time_t begin ;

void init_time ( void )
{ 
   begin = clock () ;
   return ; 
}

void show_time ( char * txt )
{
   sprintf ( junkstr ,"\nTime used to %s:\n            %.2f secs.\n" , txt , ( float ) ( clock () - begin ) / CLK_TCK ) ;
   MessageBox ( hwnd , junkstr  , "Stopwatch" , MB_OK ) ; 
   return ;
}   


void nitmatrix ( void )
{
   signed int a , b , c , d , e , f , at , numcell ;
   signed int xis , yis , sc ; 
   unsigned long int x , sb ; 
   double xrad , yrad , xassrad , yassrad , startx , starty ;
   double myy , myx ;
   double xbeg , xend , ybeg , yend ;
   double bakrad , assbakrad ;
   double dcol , drow , dd ;
   int coldif , rowdif ;
   double xedge , yedge , rad , assrad , bakxperc = xperc , bakyperc = yperc , bakxassperc = xassperc , bakyassperc = yassperc ;
   MinMaxtyp * mmpt ; 
   xrad = (double) xperc / 100 ; 
   yrad = (double) yperc / 100 ; 
   xassrad = (double) xassperc / 100 ; 
   yassrad = (double) yassperc / 100 ;
   bakxperc = xperc ;
   bakyperc = yperc ;
   bakxassperc = xassperc ; 
   bakyassperc = yassperc ; 
   if ( xassrad < xrad ) xassrad = xrad ; 
   if ( yassrad < yrad ) yassrad = yrad ;
   rad = ( xrad < yrad ) ? xrad : yrad ;
   assrad = ( xassrad < yassrad ) ? xassrad : yassrad ;
   startx = grid_startx ;
   starty = grid_starty ;
   grid_height = truecellhei ;
   grid_width = truecellwid ;
   /*  Back-up just in case there are individual fills defined  */ 
   bakrad = rad ; 
   assbakrad = assrad ;
   if ( species_tree != NULL ) spp = numterminals ;
   for ( c = spp ; c -- ; ) 
      numentries [ c ] = numassentries [ c ] = 0 ;
   mmpt = spminmax ;    
   for ( c = 0 ; c < spp ; ++ c , ++ mmpt ) {
        xbeg = startx + ( b * truecellwid ) ; 
        xend = xbeg + truecellwid ;
        ybeg = starty + ( a * truecellhei ) ;
        yend = ybeg + truecellhei ;
        sc = c / 32 ;
        sb = 1 << ( c % 32 ) ;
        mmpt -> minc = mmpt -> minr = 32767 ; 
        mmpt -> maxc = mmpt -> maxr = 0 ; 
        if ( ind_fills != NULL ) 
          if ( ind_fills[c].fillx >= 0 ) {
              xperc = ind_fills[c].fillx ; 
              yperc = ind_fills[c].filly ; 
              xassperc = ind_fills[c].assx ; 
              yassperc = ind_fills[c].assy ;
              xrad = (double) xperc / 100 ;
              yrad = (double) yperc / 100 ;
              xassrad = (double) xassperc / 100 ;
              yassrad = (double) yassperc / 100 ;
              if ( xassrad < xrad ) xassrad = xrad ;
              if ( yassrad < yrad ) yassrad = yrad ;
              rad = ( xrad < yrad ) ? xrad : yrad ;
              assrad = ( xassrad < yassrad ) ? xassrad : yassrad ; }
        for ( d = xymatrix[c].numrecs ; d -- ; ) {
            myx = xymatrix[c].x[d] ;
            myy = xymatrix[c].y[d] ;
            drow = ( myy - starty ) / truecellhei ;  
            a = ( int ) drow ; 
            dcol = ( myx - startx ) / truecellwid ;
            b = ( int ) dcol ;
            if ( a < 0 || b < 0 || a >= rows || b >= cols ) continue ;  // these fall outside the grid... 
            if ( ( assmatrix [a][b][sc] & sb ) ) {
                 -- numassentries [ c ] ; 
                 assmatrix [e][f][sc] &= ~sb ; } 
            if ( ! ( matrix [a][b][sc] & sb ) ) ++ numentries [ c ] ;
            if ( mmpt -> minc > b ) mmpt -> minc = b ; 
            if ( mmpt -> maxc < b ) mmpt -> maxc = b ; 
            if ( mmpt -> minr > a ) mmpt -> minr = a ; 
            if ( mmpt -> maxr < a ) mmpt -> maxr = a ; 
            matrix [a][b][sc] |= sb ;
            isdefd[a][b] = 1 ;
            /**   calculate position of point, in units of cell height/width *********/
            xbeg = startx + ( b * truecellwid ) ; 
            xend = xbeg + truecellwid ;
            ybeg = starty + ( a * truecellhei ) ;
            yend = ybeg + truecellhei ;
            myx = ( myx - xbeg ) / truecellwid ;  
            myy = ( myy - ybeg ) / truecellhei ;
            /****  Fill presences ***********/
            coldif = ( int ) rad + 1 ;
            rowdif = ( int ) rad + 1 ;  
            for ( e = a - rowdif ; e <= a + rowdif ; ++ e ) {
                if ( e < 0 || e >= rows ) continue ;
                for ( f = b - coldif ; f <= b + coldif ; ++ f ) {
                    if ( f < 0 || f >= cols ) continue ;
                    if ( e == a && f == b ) continue ; 
                    yedge = 1 + e - a ; if ( e == a ) yedge = myy ; if ( e > a ) yedge = e - a ; 
                    xedge = 1 + f - b ; if ( f == b ) xedge = myx ; if ( f > b ) xedge = f - b ; 
                    dd = sqrt ( ( ( myx - xedge ) * ( myx - xedge ) ) + ( ( myy - yedge ) * ( myy - yedge ) ) ) ; 
                    if ( dd > rad ) continue ; 
                    if ( ( assmatrix [e][f][sc] & sb ) ) {
                         -- numassentries [ c ] ;
                         assmatrix [e][f][sc] &= ~sb ; } 
                    if ( ! ( matrix [e][f][sc] & sb ) ) ++ numentries [ c ] ; 
                    if ( mmpt -> minc > f ) mmpt -> minc = f ; 
                    if ( mmpt -> maxc < f ) mmpt -> maxc = f ; 
                    if ( mmpt -> minr > e ) mmpt -> minr = e ; 
                    if ( mmpt -> maxr < e ) mmpt -> maxr = e ; 
                    matrix [e][f][sc] |= sb ;
                    isdefd[e][f] = 1 ; }}
            // ****  And assumed ... ***********/
            if ( assrad <= rad ) continue ; 
            coldif = ( int ) assrad + 1 ;
            rowdif = ( int ) assrad + 1 ;  
            for ( e = a - rowdif ; e <= a + rowdif ; ++ e ) {
                if ( e < 0 || e >= rows ) continue ;
                for ( f = b - coldif ; f <= b + coldif ; ++ f ) {
                    if ( f < 0 || f >= cols ) continue ;
                    if ( e == a && f == b ) continue ; 
                    if ( ( matrix [e][f][sc] & sb ) ) continue ; 
                    yedge = 1 + e - a ; if ( e == a ) yedge = myy ; if ( e > a ) yedge = e - a ; 
                    xedge = 1 + f - b ; if ( f == b ) xedge = myx ; if ( f > b ) xedge = f - b ; 
                    dd = sqrt ( ( ( myx - xedge ) * ( myx - xedge ) ) + ( ( myy - yedge ) * ( myy - yedge ) ) ) ; 
                    if ( dd > assrad ) continue ; 
                    if ( ! ( assmatrix [e][f][sc] & sb ) ) ++ numassentries [ c ] ; 
                    assmatrix [e][f][sc] |= sb ;
                    isdefd[e][f] = 1 ; }}} 
                    
            if ( ind_fills != NULL ) 
              if ( ind_fills[c].fillx >= 0 ) {
                xperc = bakxperc ;
                yperc = bakyperc ;
                xassperc = bakxassperc ; 
                yassperc = bakyassperc ; 
                rad = bakrad ;
                assrad = assbakrad ; }}

   if ( expand_cell_definition ) {
       for ( a = 0 ; a < rows ; ++ a ) {
         for ( b = 0 ; b < cols ; ++ b ) 
           for ( c = -1 ; c < 2 && !isdefd[a][b] ; ++ c ) 
             for ( d = -1 ; d < 2 && !isdefd[a][b] ; ++ d ) {
                xis = b + c ;
                yis = a + d ;
                if ( xis < 0 || xis >= cols || yis < 0 || yis >= rows ||
                     ( xis == b && yis == a ) ) continue ;
                if ( ( isdefd[yis][xis] & 1 ) ) isdefd[a][b] = 2 ; }}
       for ( a = 0 ; a < rows ; ++ a ) 
         for ( b = 0 ; b < cols ; ++ b )
            if ( isdefd[a][b] ) isdefd[a][b] = 1 ; }
   totareas = rows * cols ;
   arcells = ( totareas + 31 ) / 32 ; 
   if ( ( created_wid != truecellwid || created_hei != truecellhei ) 
        && created_wid > 0 ) 
        transfer_areas () ; 
   created_rows = rows ;
   created_cols = cols ;
   created_wid = truecellwid ; 
   created_hei = truecellhei ;
   created_orgx = grid_startx ; 
   created_orgy = grid_starty ;
   if ( auto_fill_all ) auto_auto_fills ( auto_fill_all ) ; 
   add_species_groups () ;
   return ; 
}

/********   OLD ******
void nitmatrix ( void )
{
   signed int a , b , c , d , at ;
   signed int xis , yis ; 
   unsigned long int x ; 
   double xrad , yrad , xassrad , yassrad , startx , starty ;
   double myy , myx ;
   double xbeg , xend , ybeg , yend ;
   double bakradx , bakrady , bakassradx , bakassrady , bakxperc , bakyperc , bakxassperc , bakyassperc ; 

init_time () ; 

   xrad = (double) ( truecellwid * xperc ) / 100 ; 
   yrad = (double) ( truecellhei * yperc ) / 100 ; 
   xassrad = (double) ( truecellwid * xassperc ) / 100 ; 
   yassrad = (double) ( truecellhei * yassperc ) / 100 ;
   if ( xassrad < xrad ) xassrad = xrad ; 
   if ( yassrad < yrad ) yassrad = yrad ; 
   startx = grid_startx ;
   starty = grid_starty ;
   grid_height = truecellhei ;
   grid_width = truecellwid ;
   //  Back-up just in case there are individual fills defined  
   bakradx = xrad ; 
   bakrady = yrad ;
   bakassradx = xassrad ; 
   bakassrady = yassrad ; 
   bakxassperc = xassperc ; 
   bakyassperc = yassperc ;
   bakxperc = xperc ; 
   bakyperc = yperc ;
   if ( species_tree != NULL ) spp = numterminals ;
   for ( a = 0 ; a < rows ; ++a ) 
      for ( b = 0 ; b < cols ; ++ b ) {
        xbeg = startx + ( b * truecellwid ) ; 
        xend = xbeg + truecellwid ;
        ybeg = starty + ( a * truecellhei ) ;
        yend = ybeg + truecellhei ; 
        for ( c = spp ; c -- ; ) {
            if ( ind_fills != NULL ) 
              if ( ind_fills[c].fillx >= 0 ) {
                  xperc = ind_fills[c].fillx ; 
                  yperc = ind_fills[c].filly ; 
                  xassperc = ind_fills[c].assx ; 
                  yassperc = ind_fills[c].assy ;
                  xrad = (double) ( truecellwid * xperc ) / 100 ;
                  yrad = (double) ( truecellhei * yperc ) / 100 ;
                  xassrad = (double) ( truecellwid * xassperc ) / 100 ;
                  yassrad = (double) ( truecellhei * yassperc ) / 100 ;
                  if ( xassrad < xrad ) xassrad = xrad ;
                  if ( yassrad < yrad ) yassrad = yrad ; }
            for ( d = xymatrix[c].numrecs ; d -- ; ) {
                myx = xymatrix[c].x[d] ;
                myy = xymatrix[c].y[d] ;
                if (
                     ( myx + xassrad ) >= xbeg      &&
                     ( myx - xassrad ) <= xend      &&
                     ( myy + yassrad ) >= ybeg      &&
                     ( myy - yassrad ) <= yend
                   ) {
                     if ( xperc < xassperc || yperc < yassperc ) {
                         if ( 
                               ( myx + xrad ) >= xbeg      &&
                               ( myx - xrad ) <= xend      &&
                               ( myy + yrad ) >= ybeg      &&
                               ( myy - yrad ) <= yend )
                             matrix [a][b][c/32] |= ( 1 << ( c % 32 ) ) ;
                          else 
                             assmatrix [a][b][c/32] |= ( 1 << ( c % 32 ) ) ; }
                     else 
                        matrix [a][b][c/32] |= ( 1 << ( c % 32 ) ) ;
                     isdefd[a][b] = 1 ; }}
            if ( ind_fills != NULL ) 
              if ( ind_fills[c].fillx >= 0 ) {
                xrad = bakradx ;
                yrad = bakrady ;
                xassrad = bakassradx ;
                yassrad = bakassrady ;
                xassperc = bakxassperc ; 
                yassperc = bakyassperc ;
                xperc = bakxperc ; 
                yperc = bakyperc ; }}}
   for ( a = spp ; a -- ; ) {
      numentries [ a ] = numassentries [ a ] = 0 ; 
      x = 1 << ( a % 32 ) ;
      at = a / 32 ; 
      for ( b = rows ; b -- ; )
        for ( c = cols ; c -- ; ) {
          if ( ( assmatrix [ b ] [ c ] [ at ] & x ) ) 
                numassentries [ a ] ++ ;
          else 
          if ( ( matrix [ b ] [ c ] [ at ] & x ) ) 
               { numentries [ a ] ++ ; numassentries[a] ++ ; }}}
   if ( expand_cell_definition ) 
   for ( a = 0 ; a < rows ; ++ a ) {
     for ( b = 0 ; b < cols ; ++ b ) 
       for ( c = -1 ; c < 2 && !isdefd[a][b] ; ++ c ) 
         for ( d = -1 ; d < 2 && !isdefd[a][b] ; ++ d ) {
            xis = b + c ;
            yis = a + d ;
            if ( xis < 0 || xis >= cols || yis < 0 || yis >= rows ||
                 ( xis == b && yis == a ) ) continue ;
            if ( ( isdefd[yis][xis] & 1 ) ) isdefd[a][b] = 2 ; }}
   for ( a = 0 ; a < rows ; ++ a ) 
     for ( b = 0 ; b < cols ; ++ b )
        if ( isdefd[a][b] ) isdefd[a][b] = 1 ; 
   totareas = rows * cols ;
   arcells = ( totareas + 31 ) / 32 ; 
   if ( ( created_wid != truecellwid || created_hei != truecellhei ) 
        && created_wid > 0 ) 
        transfer_areas () ; 
   created_rows = rows ;
   created_cols = cols ;
   created_wid = truecellwid ; 
   created_hei = truecellhei ;
   created_orgx = grid_startx ; 
   created_orgy = grid_starty ;
   add_species_groups () ;

show_time () ; 
   
   return ; 
} ****************/

int confirm_grid_move ( void )
{
    int a ;
    static int warnd_already = 0 ;
    if ( warnd_already ) return 1 ; 
    for ( a = spp ; a -- ; ) 
       if ( numassentries[a] ) {
           sprintf ( junkstr + 1 , "Moving grid will reset assumed records to those\nimplied by current radius (%.0f-%.0f for filling,\n%.0f-%.0f for assumed records). Continue" , xperc , yperc , xassperc , yassperc ) ; 
           if ( !sure ( junkstr + 1 ) ) return 0 ;
           warnd_already = 1 ; 
           break ; }
    return 1 ;
}


void redo_matrix ( void )
{
   int a , b , c ; 
   if ( !num_spingrid ) {
       showcurset () ; 
       captf ( "Cannot change grid (data were not read as coordinates)" ) ;
       return ; }
   if ( !confirm_grid_move () ) return ; 
   for ( a = rows ; a -- ; )
     for ( b = cols ; b -- ; ) {
       isdefd[a][b] = 0 ; 
       for ( c = spcells ; c -- ; ) matrix [a][b][c] = assmatrix [a][b][c] = 0 ; }    
   for ( c = spp ; c -- ; ) numentries[c] = numassentries[c] = 0 ; 
   nitmatrix () ; 
   dorule5 () ;
   showcurset () ; 
   redoallscores = 1 ;
   sprintf ( junkstr , "Changed grid (origin x-y = %.3f-%.3f, cell size %.3f-%.3f)" ,
        grid_startx , grid_starty , truecellwid , truecellhei ) ; 
   captf ( junkstr ) ;
   return ; 
}


double chk_a_move ( void )
{
   int a , b , c ; 
   for ( a = rows ; a -- ; )
     for ( b = cols ; b -- ; ) {
       isdefd[a][b] = 0 ; 
       for ( c = spcells ; c -- ; ) matrix [a][b][c] = assmatrix [a][b][c] = 0 ; }    
   for ( c = spp ; c -- ; ) numentries[c] = numassentries[c] = 0 ; 
   nitmatrix () ; 
   return dorule5 () ;
}

void find_optimum_grid_position ( void )
{
   double tryx , tryy , mvsz = 0.5 * truecellwid , xlim , ylim ;
   double curbest , this , nitbest ;
   double besx = grid_startx , besy = grid_starty ;
   double curx , cury ;
   double nitx = besx , nity = besy ; 
   int a ; 
   if ( !num_spingrid ) {
       showcurset () ; 
       captf ( "Cannot change grid (data were not read as coordinates)" ) ;
       return ; }
   if ( !confirm_grid_move () ) return ; 
   nitbest = curbest = recptr -> score = chk_a_move () ;
   sprintf ( junkstr , "Set %i best score %.3f" , recptr - rec , curbest ) ;
   pleasewait ( junkstr ) ; 
   redoallscores = 1 ;
   while ( mvsz >= 0.001 ) {
       sprintf ( junkstr , "Set %i best score %.3f" , recptr - rec , curbest ) ;
       updatewait ( junkstr ) ; 
       tryx = grid_startx - ( mvsz * 2 ) ;
       tryy = grid_starty - ( mvsz * 2 ) ;
       xlim = tryx + ( mvsz * 4 ) ;
       ylim = tryy + ( mvsz * 4 ) ;
       curx = grid_startx ;
       cury = grid_starty ; 
       while ( tryx < xlim ) {
        grid_startx = tryx ;
        while ( tryy < ylim ) {
          grid_starty = tryy ;
          this = chk_a_move () ;
          if ( this > curbest ) {
            besx = tryx ; 
            besy = tryy ;
            curbest = this ; }
          tryy += mvsz ; } 
        tryx += mvsz ; }
      if ( curx == besx && cury == besy ) {
           if ( mvsz == 0.001 ) {
               grid_startx = besx ; 
               grid_starty = besy ; 
               break ; }
           mvsz = mvsz / 2 ;
           if ( mvsz < 0.001 ) mvsz = 0.001 ; }
      grid_startx = besx ; 
      grid_starty = besy ; }
   chk_a_move () ; 
   imdone () ; 
   showcurset () ; 
   redoallscores = 1 ;
   if ( besx == nitx && nity == besy )
     sprintf ( junkstr , "Grid was already optimal (origin x-y = %.3f-%.3f)" , grid_startx , grid_starty ) ; 
   else 
     sprintf ( junkstr , "Moved grid (origin x-y = %.3f-%.3f)\nScore changed from %.5f to %.5f" ,
          grid_startx , grid_starty , nitbest , recptr -> score ) ; 
   captf ( junkstr ) ;
}


#define MAXCONS 10000
int numarcells ;
int showmaxvals ;
double consen_intrvl ;
double consen_minval , consen_maxval ;  

void * consmem ( int thesiz )
{
    char * p ;
     p = ( char * ) malloc ( thesiz ) ; 
    if ( p == NULL ) 
        MessageBox ( mainwnd , "Sorry, not enough memory to consense" , "ERROR" , MB_OK | MB_ICONERROR ) ;
    return ( char * ) p ;
} 


/**
#define consmem(x)  mymem( x )
 ***/

int calculate_consensus ( void )
{
    Artyp * thisrec ;
    Constyp * conpt ;
    int a , b , c ;
    static int nited = 0 ; 
    numcons = 0 ;
    if ( !nited ) {
        numarcells = ( numrecs + 31 ) / 32 ;
        consenbitz = consmem ( arcells * sizeof ( int32 ) ) ;
        if ( consenbitz == NULL ) return 0 ; 
        if ( ( consen = consmem ( MAXCONS * sizeof ( Constyp ) ) ) == NULL ) return 0 ; 
        if ( ( consensus_sp_list = consmem ( spp * sizeof ( int ) ) ) == NULL ) return 0 ; 
        for ( a = 0 , conpt = consen ; a < 3  ; ++ a , ++ conpt ) {
          if ( ( conpt->spmin = consmem ( spp * sizeof ( double  ) ) ) == NULL ) return 0 ; 
          if ( ( conpt->spmax = consmem ( spp * sizeof ( double  ) ) ) == NULL ) return 0 ; 
          if ( ( conpt->clmin = consmem ( totareas * sizeof ( double  ) ) ) == NULL ) return 0 ; 
          if ( ( conpt->clmax = consmem ( totareas * sizeof ( double  ) ) ) == NULL ) return 0 ;
          if ( ( conpt->arlist = consmem ( 2 * numarcells * sizeof ( int32 ) ) ) == NULL ) return 0 ; }
        for ( ; a < MAXCONS ; ++ a , ++ conpt ) conpt->spmin = NULL ; 
        nited = 1 ; }
    else if ( numarcells < ( numrecs + 31 ) / 32 ) {
            sprintf ( junkstr ,"Cannot recalculate consensus for more than twice the\nnumber of areas (calculated for up to %i before)\n" ,
                numarcells * 32 ) ; 
            MessageBox ( mainwnd , junkstr , "ERROR" , MB_OK | MB_ICONERROR ) ;
            return 0 ; }
    c = work_the_cons () ;
    imdone () ;
    if ( c )
    if ( consensus_is_sample < 3 ) 
        for ( a = 0 , conpt = consen ; a < numcons ; ++ a , ++ conpt ) {
           conpt -> numareas = 0 ; 
           for ( b = 0 ; b < numarcells ; ++ b )
               conpt -> numareas += onbits ( conpt->arlist[b] ) ; }
    else 
        for ( a = 0 , conpt = consen ; a < numcons ; ++ a , ++ conpt ) {
           conpt -> numareas = 0 ;
           for ( c = 0 ; c < sample_repls ; ++ c ) 
              for ( b = 0 ; b < numrecs ; ++ b ) 
                  if ( ( 1 << ( b % 32 ) ) & conpt->arlist[b/32 ] ) 
                      if ( rec[b].fromrepl == c ) { conpt -> numareas ++ ; b = numrecs ; }}
    return a ; 
}


int make_nuconsar ( Artyp * mrec , double scorval )
{
    int a , b , c , d ;
    int32 sb , sc ;
    Constyp * conpt ;
    if ( consen[numcons].spmin == NULL ) {
        for ( a = 0 , conpt = consen + numcons ;
              a < 10 ;
              ++ a , ++ conpt ) {
          if ( ( conpt->spmin = consmem ( spp * sizeof ( double ) ) ) == NULL ) return 0 ;
          if ( ( conpt->spmax = consmem ( spp * sizeof ( double  ) ) ) == NULL ) return 0 ;
          if ( ( conpt->clmin = consmem ( totareas * sizeof ( double  ) ) ) == NULL ) return 0 ;
          if ( ( conpt->clmax = consmem ( totareas * sizeof ( double  ) ) ) == NULL ) return 0 ;
          if ( ( conpt->arlist = consmem ( numarcells * sizeof ( int32 ) ) ) == NULL ) return 0 ; }}
     conpt = consen + numcons ;
     for ( a = 0 ; a < numarcells ; ++ a ) conpt->arlist[a] = 0 ; 
     a = mrec - rec ;
     conpt->arlist[a/32] = 1 << ( a %32 )  ;
     conpt->numareas = 1 ;
     for ( d = 0 , sb = 1 , sc = 0 ; d < spp ; ++ d ) {
            if ( ( intersptr[sc] & sb ) ) 
                conpt->spmax[d] = conpt->spmin[d] = spscore[d] ; 
            else conpt->spmin[d] = conpt->spmax[d] = 0 ;
            if ( sb == BIT32 ) { sb = 1 ; ++ sc ; }
            else sb <<= 1 ; }
     conpt -> min = conpt -> max = scorval ; 
     for ( d = 0 , sb = 1 , sc = 0 ; d < totareas ; ++ d ) {
           if ( ( mrec->lst[sc] & sb ) ) 
               conpt->clmax[d] = conpt->clmin[d] = scorval ; 
           else conpt->clmin[d] = conpt->clmax[d] = 0 ;
           if ( sb == BIT32 ) { sb = 1 ; ++ sc ; }
           else sb <<= 1 ; }
     ++ numcons ; 
     return 1 ;
}
        
int work_the_cons ( void )
{
        
    Artyp * thisrec ;
    Constyp * conpt ;
    int32 mb , mc , sb , sc , * app , * bpp ;
    int32 ina , inb , both ; 
    int a , b , c , d ;
    double mscore , perc ; 
    int maxarchk = 0 , isnucons , addit ;
    int chgs = 1 ;
    int turns = 0 ;
    while ( chgs ) {
     if ( turns ) imdone () ;
     sprintf ( junkstr , "Consensing (round %i)" , ++ turns ) ;
     pleasewait ( junkstr ) ; 
     chgs = 0 ; 
     for ( a = 0 , thisrec = rec ; a < numrecs ; ++ a , ++ thisrec ) {
        if ( consensus_is_sample == 3 && thisrec -> fromrepl <= 0 ) continue ; 
        if ( consensus_is_sample && consensus_is_sample != 3 && thisrec >= bootinit ) break ;  
        isnucons = 1 ;
        recptr = thisrec ; 
        cursize = recptr -> size ;
        if ( consensus_is_sample ) { 
            if ( consensus_is_sample == 1 ) { mscore = recptr -> bootarval ; if ( mscore == 0 ) mscore = 10e-10 ; } 
            if ( consensus_is_sample == 2 ) { mscore = recptr -> bootspval ; if ( mscore == 0 ) mscore = 10e-10 ; } 
            if ( consensus_is_sample == 3 ) mscore = recptr -> score ;
            for ( d = 0 ; d < spcells ; ++ d ) intersptr[ d ] = recptr -> splist [ d ] ; 
            for ( d = 0 ; d < spp ; ++ d ) {
              if ( ( recptr -> splist[ d / 32 ] & ( 1 << ( d % 32 ) ) ) ) spscore[d] = 1 ;
              else spscore[d] = 0 ; }}
        else 
            mscore = dorule5 () ;
        for ( b = 0 , conpt = consen ; b < numcons ; ++ b , ++ conpt ) {
            if ( ( conpt->arlist[a/32] & ( 1 << ( a % 32 ) ) ) ) {
                isnucons = 0 ; 
                continue ; }
            addit = 1 ;
            if ( chain_spp ) addit = 0 ; 
            for ( c = 0 , mb = 1 , mc = 0 ; c < maxarchk ; ++ c ) {
               if ( consensus_is_sample == 3 && rec[c].fromrepl <= 0 ) {
                   if ( ( mb == BIT32 ) ) { mb = 1 ; ++ mc ; }
                   else mb <<= 1 ; 
                   continue ; }
               if ( consensus_is_sample && consensus_is_sample != 3 && c >= bootinit - rec ) break ;  
               if ( ( mb & conpt->arlist[ mc ] ) && ( c != thisrec - rec ) ) {
                   app = rec[c].splist ; 
                   bpp = thisrec->splist ;
                   both = ina = inb = 0 ; 
                   for ( d = 0 ; d < spcells ; ++ d ) {
                       both += onbits ( * app & * bpp ) ;
                       ina += onbits ( * app & ~ * bpp ) ; 
                       inb += onbits ( * bpp & ~ * app ) ;
                       ++ app ; ++ bpp ; }
                   perc = ( double ) ( both * 100 ) / ( both + ina + inb ) ;
                   if ( chain_spp )
                       { if ( perc >= ( double ) conscut ) { addit = 1 ; break ; }}
                   else 
                       if ( perc < ( double ) conscut ) { addit = 0 ; break ; }}
               if ( ( mb == BIT32 ) ) { mb = 1 ; ++ mc ; }
               else mb <<= 1 ; }
            if ( !addit ) continue ; 
            isnucons = 0 ;
            chgs = 1 ; 
            conpt->arlist[a/32] |= 1 << ( a %32 )  ;
            if ( conpt -> min > mscore ) 
                 conpt -> min = mscore ; 
            if ( conpt -> max < mscore ) 
                 conpt -> max = mscore ; 
            for ( d = 0 , sb = 1 , sc = 0 ; d < spp ; ++ d ) {
               if ( ( intersptr[sc] & sb ) ) {
                   if ( conpt->spmax[d] < spscore[d] ) 
                        conpt->spmax[d] = spscore[d] ; 
                   if ( conpt->spmin[d] > spscore[d] ) 
                        conpt->spmin[d] = spscore[d] ; }
               else conpt->spmin[d] = 0 ;
               if ( sb == BIT32 ) { sb = 1 ; ++ sc ; }
               else sb <<= 1 ; }
            for ( d = 0 , sb = 1 , sc = 0 ; d < totareas ; ++ d ) {
               if ( ( thisrec->lst[sc] & sb ) ) {
                   if ( conpt->clmax[d] < mscore ) 
                        conpt->clmax[d] = mscore ; 
                   if ( conpt->clmin[d] > mscore ) 
                        conpt->clmin[d] = mscore ; }
               else conpt->clmin[d] = 0 ;
               if ( sb == BIT32 ) { sb = 1 ; ++ sc ; }
               else sb <<= 1 ; }}
       if ( turns == 1 ) {       
          if ( isnucons ) {
              if ( !make_nuconsar ( thisrec , mscore ) ) return 0 ;
              chgs = 1 ; }
           ++ maxarchk ; }}
    mark_xces_cons () ;
    wipe_xces () ; }
    return 1 ; 
}

BOOL CALLBACK ConsOptFunc(HWND hdwnd, UINT message, WPARAM wParam, LPARAM lParam)
{
    static inchain ; 
    static int i ; 
    HWND hWho ;
    switch(message) {
        case WM_INITDIALOG :
             SET_UPDOWN( 110 , 0 , 100 , conscut ) ;
             if ( chain_spp ) BUTT_CHECK( 114 ) ;
             else BUTT_CHECK( 113 ) ;
             inchain = chain_spp ; 
             break ; 
        case WM_COMMAND :
                switch(LOWORD(wParam)){
                   case 113 : inchain = 0 ; break ; 
                   case 114 : inchain = 1 ; break ; 
                   case IDOK:
                     chain_spp = inchain ;
                     GETINT( conscut , 109 ) ; 
                     EndDialog(hdwnd,1);
                     return 1 ; 
                   case IDCANCEL :
                      EndDialog(hdwnd,0);
                      return 0 ; 
                      default : break; }
         break; }
    return 0;
}

double * maxconscore ; 

void show_consensus ( int ky ) 
{ 
  static int x , cursp = 0 ; 
  static int a , i , j , k , mc ; 
  int32 mb , inbits ; 
  int curwas ;
  static int list_the_spp ;
  int numspcols ; 
  Constyp * conpt ;
  Artyp * rpt ;
  int32 * lpt ; 
  static Artyp * olrec ;  
  char * cp ;
  double range , val , imat ;
  int just_marked = 0 ;
  static int show_nth_sp ; 
  if ( ky == 0 ) {
      olrec = recptr ;
      if ( !run_autoconsense ) 
           i = DialogBox (hInst, "ConsOptDB", hwnd, (DLGPROC) ConsOptFunc ) ;
      else { conscut = autoconsense_cut ; i = 1 ; }
      if ( i == 0 ) {
          recptr = olrec ; 
          curcmd_loop = cmd_loop ; return ; }
      if ( !calculate_consensus () ) {
          recptr = olrec ; 
          curcmd_loop = cmd_loop ; return ; }
      showmaxvals = 1 ;
      list_the_spp = 0 ;
      if ( consensus_is_sample == 3 ) list_the_spp = 1 ; 
      curcons = 0 ;
      make_list_of_spp_for_consensus ( curcons ) ; 
      current_species = -1 ; 
      recptr = rec ; }
  x = ky ; 
  while ( 1 ) {
       switch ( x ) { 
            case 0 : break ;
            case 'H': dohlp ( 1 ) ; break ; 
            case VK_ESCAPE  :
               recptr = olrec ; 
               showcurset () ;
               curcmd_loop = cmd_loop ;
               show_nth_sp = 0 ;  
               return ; 
            case VK_RETURN : case VK_TAB : 
                if ( just_out_of_duwc ) just_out_of_duwc = 0 ;  
                else if ( ++ curcons == numcons ) curcons = 0 ;
                make_list_of_spp_for_consensus ( curcons ) ;
                show_nth_sp = 0 ;  
                break ; 
            case BACK : 
                if ( just_out_of_duwc ) just_out_of_duwc = 0 ;  
                else if ( -- curcons < 0 ) curcons = numcons - 1 ;
                make_list_of_spp_for_consensus ( curcons ) ; 
                show_nth_sp = 0 ;  
                break ;
            case VK_NEXT :
              if ( !list_the_spp ) break ;
              show_nth_sp ++ ;
              if ( show_nth_sp >= num_of_spp_in_consensus_list ) show_nth_sp = 0 ;
              break ; 
            case VK_PRIOR :
              if ( !list_the_spp ) break ;
              show_nth_sp -- ;
              if ( show_nth_sp < 0 ) show_nth_sp = num_of_spp_in_consensus_list - 1 ;
              break ;
            case 'D' :
            case 'C' :
            case 'W' :
            case 'U' :
            case 'J' :
                cur_duwc_act = x ; 
                curcmd_loop = show_duwc ;
                is_cons_duwc = 1 ; 
                show_nth_sp = -1 ;  
                show_duwc ( 0 ) ;
                break ;
            case 'u' :
                conpt = consen + curcons ; 
                for ( a = 0 , mb = 1 , mc = 0 ; a < numrecs ; ++ a ) {
                     if ( ( conpt->arlist[mc] & mb ) ) {
                          if ( rec[a].mark ) -- just_marked ;
                          rec[a].mark = 0 ; }
                     if ( mb == BIT32 ) { mb = 1 ; ++ mc ; }
                     else mb <<= 1 ; }
                break ;
            case 'N':
                a = numrecs ; 
                donewset () ;
                if ( a == numrecs ) break ;
                conpt = consen + curcons ; 
                for ( a = 0 , mb = 1 , mc = 0 ; a < numrecs ; ++ a ) {
                     if ( ( conpt->arlist[mc] & mb ) ) 
                        for ( i = arcells ; i -- ; )
                            rec[numrecs-1].lst[i] |= rec[a].lst[i] ; 
                     if ( mb == BIT32 ) { mb = 1 ; ++ mc ; }
                     else mb <<= 1 ; }
                break ; 
            case 'M' :
                conpt = consen + curcons ; 
                for ( a = 0 , mb = 1 , mc = 0 ; a < numrecs ; ++ a ) {
                     if ( ( conpt->arlist[mc] & mb ) ) {
                          rec[a].mark = 1 ;
                          ++ just_marked ; }
                     if ( mb == BIT32 ) { mb = 1 ; ++ mc ; }
                     else mb <<= 1 ; }
                break ; 
            case 'g' :
               curwas = curcons ; 
               curcons = atoi ( comstring ) ; 
               if ( curcons < 0 || curcons >= numcons ) curcons = curwas ;
               make_list_of_spp_for_consensus ( curcons ) ; 
               show_nth_sp = 0 ;  
               break ; 
            case 'x' :
                showmaxvals = 1 - showmaxvals ;
                break ;
            case 'v':
              list_the_spp = 1 - list_the_spp ;
              if ( list_the_spp )
                   show_nth_sp = 0 ; 
              else current_species = -1 ; 
              break ;
            case 1 : break ; 
            default :
               showcurset () ; 
               curcmd_loop = cmd_loop ;
               return ; } 
       if ( curcmd_loop == show_duwc ) return ; 
       conpt = consen + curcons ;
       maxconscore = conpt -> spmax ; 
       if ( just_out_of_duwc )  {
           -- just_out_of_duwc ; 
           if ( just_out_of_duwc == 0 ) screenf ( "Consensus area %i is disjunct with no other" , curcons ) ; 
           if ( just_out_of_duwc == 'W' ) screenf ( "Consensus area %i contains no other" , curcons ) ; 
           if ( just_out_of_duwc == 'U' ) screenf ( "Consensus area %i is within no other" , curcons ) ; 
           if ( just_out_of_duwc == 'C' ) screenf ( "Consensus area %i partly overlaps no other" , curcons ) ;
           ++ just_out_of_duwc ; }
       else
       if ( consensus_is_sample ) {
           if ( consensus_is_sample == 1 ) 
              if ( showmaxvals ) 
                   screenf("Cons %i of %i (%i areas; AREA)\n" , curcons , numcons , conpt->numareas ) ;
              else screenf("Cons %i of %i (%i areas; area)\n" , curcons , numcons , conpt->numareas ) ; 
           else if ( consensus_is_sample == 2 ) 
              if ( showmaxvals ) 
                   screenf("Cons %i of %i (%i areas; SPP)\n" , curcons , numcons , conpt->numareas ) ;
              else screenf("Cons %i of %i (%i areas; spp)\n" , curcons , numcons , conpt->numareas ) ;
           else 
              if ( showmaxvals ) 
                   screenf("Cons %i of %i (found in %i repls.)\n" , curcons , numcons , conpt->numareas ) ;
              else screenf("Cons %i of %i (found in %i repls.)\n" , curcons , numcons , conpt->numareas ) ; 
             }
       else        
           if ( showmaxvals ) 
               screenf("Consensus area %i of %i (from %i areas; max. values)\n" ,
                   curcons , numcons , conpt->numareas ) ;
           else 
               screenf("Consensus area %i of %i (from %i areas; min. values)\n" ,
                   curcons , numcons , conpt->numareas ) ;
       range = conpt->max - conpt->min ;
       consen_minval = conpt->min ;
       consen_maxval = conpt->max ;
       if ( ! consensus_is_sample ) {
           consen_intrvl = range / 7 ;
           if ( consen_intrvl < 0.25 ) consen_intrvl = 0.25 ; }
       else { 
           consen_intrvl = range / 5 ;
           if ( consen_intrvl < 0.05 ) consen_intrvl = 0.05 ; } 
       for ( a = arcells ; a -- ; )
          consenbitz[a] = splist[a] = inflist[a] = 0  ;
       for ( a = 0 , mb = 1 , mc = 0 ; a < totareas ; ++ a ) {
           val = conpt->clmax[a] ;
           if ( !showmaxvals ) val = conpt->clmin[a] ;
           if ( val > 0 ) {
              inbits = 1 ;
              imat = conpt->min + consen_intrvl ; 
              while ( imat < val && inbits < 7 ) {
                  imat += consen_intrvl ;
                  ++ inbits ; }
              if ( ( inbits & 1 ) ) consenbitz[mc]|= mb ; 
              if ( ( inbits & 2 ) ) splist[mc]|= mb ; 
              if ( ( inbits & 4 ) ) inflist[mc]|= mb ; }
           if ( mb == BIT32 ) { mb = 1 ; ++ mc ; }
           else mb <<= 1 ; }
       drawmap ( consenbitz , splist , inflist ) ;
       if ( just_marked ) {
           if ( just_marked > 0 ) 
              captf ( "Marked %i areas (corresponding to consensus area %i)" ,
                       just_marked , curcons ) ;
           else {
               just_marked =-just_marked ; 
               captf ( "Un-Marked %i areas (corresponding to consensus area %i)" ,
                       just_marked , curcons ) ; }}
       else 
       if ( list_the_spp ) {
            j = 0 ;
            for ( a = 0 ; a < spp ; ++ a ) if ( conpt->spmax[a] > 0 ) ++ j ;
            current_species = consensus_sp_list [ show_nth_sp ] ;
            if ( consensus_is_sample ) 
                captf( "%i scoring spp.(*=all sets):" , j ) ; 
            else     
            if ( spname != NULL )
                 captf( "Showing %i; %i species give score:" , current_species , j ) ; 
            else 
                captf( "Showing %s; %i species give score:" , spname[current_species] , j ) ; 
            cp = screencapt + strlen ( screencapt ) ;
            k = 0 ;
            numspcols = 5 ;
            if ( spname != NULL && !consensus_is_sample ) numspcols = 2 ;
            for ( j = 0 ; j < spp ; ++ j ) {
                 if ( conpt->spmax[j] == 0 ) continue ;
                 sprintf ( junkstr , "%i unnamed" , j ) ; 
                 if ( ( k % numspcols ) == 0 ) {
                      * cp ++ = '\n' ; * cp ++ = ' ' ;
                      * cp ++ = ' ' ; * cp ++ = ' ' ; * cp ++ = ' ' ; }
                 if ( consensus_is_sample ) {
                     cp += sprintf ( cp , "%3i" , j ) ;
                     if ( conpt->spmin[j] > 0 )
                        cp += sprintf ( cp , "*  " ) ; 
                     else cp += sprintf ( cp , "   " ) ;
                     ++ k ;
                     continue ; }
                 else {
                     i = 1 ;
                     if ( spname == NULL ) i = 0 ;
                     else if ( spname[j] == NULL ) i = 0 ; 
                     if ( i ) {
                         if ( strcmp ( spname[j] , junkstr ) ) 
                               i = sprintf ( cp , "%3i %23s(%.3f" , j , spname[j] , conpt->spmin[j] ) ;
                         else 
                               i = sprintf ( cp , "%27i(%.3f" , j , conpt->spmin[j] ) ; }
                     else
                        i = sprintf ( cp , "%3i(%.3f" , j , conpt->spmin[j] ) ; }
                 cp += i ;
                 if ( conpt->spmax[j] > conpt->spmin[j] )
                    cp += sprintf ( cp , "-%.3f) " , conpt->spmax[j] ) ;
                 else cp += sprintf ( cp , ")       " ) ;
                 if ( spname != NULL ) cp += sprintf ( cp , "    " ) ; 
                 ++ k ; }
            * cp = '\0' ; }
       else
        if ( consensus_is_sample < 3 ) {
         captf( "Areas included:" , j ) ;
         cp = screencapt + strlen ( screencapt ) ;
         j = 0 ; 
         for ( a = 0 , mb = 1 , mc = 0 ; a < numrecs ; ++ a ) {
             if ( ( conpt->arlist[mc] & mb ) ) {
                 recptr = rec + a ; 
                 if ( ( j % 10 ) == 0 ) {
                      * cp ++ = '\n' ; * cp ++ = ' ' ;
                      * cp ++ = ' ' ; * cp ++ = ' ' ; * cp ++ = ' ' ; }
                 i = sprintf ( cp , "%4i " , a ) ;
                 ++ j ; 
                 cp += i ; }
             if ( mb == BIT32 ) { mb = 1 ; ++ mc ; }
             else mb <<= 1 ; }}
       else screencapt [ 0 ] = 0 ; 
       break ; }
    return ; 
} 

void mark_xces_cons ( void )
{
    Constyp * cona , * conb ;
    int a , b , c ;
    int nodiff ; 
    for ( a = 0 , cona = consen ; a < numcons ; ++ a , ++ cona )
          cona -> is_xcess = 0 ;
    for ( a = 0 , cona = consen ; a < numcons - 1 ; ++ a , ++ cona ) {
       if ( cona->is_xcess ) continue ; 
       for ( b = a , conb = consen + a + 1 ; ++ b < numcons ; ++ conb ) {
           if ( conb->is_xcess ) continue ; 
           nodiff = 1 ;
           if ( cona->max != conb->max ) nodiff = 0 ;  
           if ( cona->min != conb->min ) nodiff = 0 ;  
           for ( c = 0 ; c < numarcells && nodiff ; ++ c ) 
               if ( cona->arlist[c] != conb->arlist[c] ) nodiff = 0 ; 
           if ( nodiff ) conb->is_xcess = 1 ; }}
    return ;
}

void copycons ( Constyp * dest , Constyp * src )
{
    int a , b ; 
    double * vdest , * vsrc ;
    int32 * idest , * isrc ;
    vdest = dest->spmax ;
    vsrc = src->spmax ;
    for ( a = 0 ; a < spp ; ++ a ) * vdest ++ = * vsrc ++ ; 
    vdest = dest->spmin ;
    vsrc = src->spmin ;
    for ( a = 0 ; a < spp ; ++ a ) * vdest ++ = * vsrc ++ ; 
    vdest = dest->clmax ;
    vsrc = src->clmax ;
    for ( a = 0 ; a < totareas ; ++ a ) * vdest ++ = * vsrc ++ ; 
    vdest = dest->clmin ;
    vsrc = src->clmin ;
    for ( a = 0 ; a < totareas ; ++ a ) * vdest ++ = * vsrc ++ ;
    dest->max = src->max ; 
    dest->min = src->min ;
    idest = dest->arlist ; 
    isrc = src->arlist ;
    for ( a = 0 ; a < numarcells ; ++ a ) * idest ++ = * isrc ++ ;
}    

void wipe_xces ( void )
{
    int a ;
    Constyp * cona , * conb ;
    int nunum = 0 ;
    int nxreal = -1 ; 
    for ( a = 0 , cona = consen ; a < numcons ; ++ a , ++ cona ) {
        if ( !cona->is_xcess ) continue ;
        if ( nxreal < 0 ) nxreal = a + 1 ;
        conb = consen + nxreal ; 
        for (   ; nxreal < numcons && conb->is_xcess ;
                  ++ nxreal , ++ conb ) ;
        if ( nxreal < numcons && !( conb->is_xcess ) ) {
             copycons ( cona , conb ) ;
             cona -> is_xcess = 0 ; 
             conb -> is_xcess = 1 ; }}
    for ( a = 0 , cona = consen ; a < numcons ; ++ a , ++ cona ) {
        if ( ( cona->is_xcess ) ) break ;
        ++ nunum ; }
    numcons = nunum ;
    return ;
}
        

void list_endemic_taxa ( void )
{
    static int nited = 0 ;
    static double * msc ;
    int32 mb , mc ;
    int a , b , some = 0 ; 
    Artyp * recwas = recptr ; 
    if ( !nited ) msc = malloc ( spp * sizeof ( double ) ) ;
    if ( msc == NULL ) {
        MessageBox ( mainwnd , "Sorry, not enough memory to list taxa" , "ERROR" , MB_OK | MB_ICONERROR ) ;
        return ; }
    nited = 1 ;
    for ( a = spp ; a -- ; ) msc[a] = 0 ;
    pleasewait ( "Listing endemic taxa..." ) ; 
    for ( a = 0 ; a < numrecs ; ++ a ) {
        recptr = rec + a ; 
        cursize = recptr -> size ; 
        dorule5 () ;
        for ( b = 0 , mb = 1 , mc = 0 ; b < spp ; ++ b ) {
          if ( ( intersptr[mc] & mb ) ) {
                if ( spscore[b] > msc[b] ) msc[b] = spscore[b] ; }
          if ( mb == BIT32 ) { mb = 1 ; mc ++ ; }
          else mb <<= 1 ; }}
    for ( a = spp ; a -- ; ) if ( msc[a] > 0 ) ++ some ;
    if ( !some ) {
        imdone () ; 
        fprintf ( outspace , "\nNo species is endemic of any area!\n" ) ;
        return ; }
    fprintf ( outspace , "\n%i species are endemic to some area:\n" , some ) ;
    for ( a = 0 ; a < spp ; ++ a ) 
        if ( msc[a] > 0 )
          if ( spname == NULL )
            fprintf ( outspace , "\t%i (%.5f)\n" , a , msc[a] ) ; 
          else 
            fprintf ( outspace , "\t%i %s (%.5f)\n" , a , spname[a] , msc[a] ) ; 
    imdone () ; 
    return ;
}                

char namchain[4096] ; 

void parse_taxon_names ( void ) 
{
   int numsp , i , j , k ;
   int isfirs ;
   char * cp ;
   int * lix , * liy ; 

//   if ( spname != NULL ) ermsg ( "Taxon names already defined!" ) ; 

   while ( !feof ( infile ) ) {
         if ( ! fscanf ( infile , " %i" , &numsp ) ) break ; 
         if ( feof ( infile ) ) break ; 
         get_spname ( numsp ) ; }

   for ( i = 0 ; i < numterminals ; ++ i )
      if ( spname[ i ] == NULL ) { 
            spname [ i ] = ( char * ) mymem ( 7 * sizeof ( char ) ) ;
            sprintf ( spname[i] , "%i" , i ) ; }

   if ( species_tree != NULL ) {
      for ( i = numterminals + 1 ; i < species_tree [ treeroot ] ; ++ i ) {
            if ( spname[i-1] != NULL ) continue ; 
            * ( lix = liy = innerlist ) = i ;
            ++ liy ;
            cp = namchain ;
            cp += sprintf ( cp , "%i=" , i - 1 ) ; 
            isfirs = 1 ; 
            while ( lix < liy ) {
                j = * lix ++ ; 
                if ( j >= numterminals ) 
                   for ( k = treefirs[j] ; k != -1 ; k = treesis [ k ] ) * liy ++ = k ;
                else { 
                    if ( !isfirs ) { * cp ++ = '+' ; * cp = 0 ; }
                    isfirs = 0 ;
                    cp += sprintf ( cp , "%i" , j ) ; }}
            j = strlen ( namchain ) ;
            spname [ i - 1 ] = ( char * ) mymem ( ( j + 1 ) * sizeof ( char ) ) ;
            strcpy ( spname[ i - 1 ] , namchain ) ; }}
            
   return ; 
}

void fake_a_grid ( void )
{
   Coordtyp * cp ;
   int32 * sppt ; 
   int i ; 
   num_spingrid = spp ;
   cp = xymatrix = mymem ( spp * sizeof ( Coordtyp ) ) ;
   sppt = spingrid = mymem ( ( ( spp + 31 ) / 32 ) * sizeof ( int32 ) ) ; 
   for ( i = ( spp + 31 ) / 32 ; i -- ; ) * sppt ++ = -1 ;    
   for ( i = 0 ; i < spp ; ++ i , ++ cp ) cp -> numrecs = 0 ;
}

void erase_all_marks ( void )
{
    Artyp * this ;
    int a ; 
    for ( a = 0 , this = rec ; a < numrecs ; ++ a , ++ this ) 
        this -> mark = 0 ;
    captf ( "Erased all marks" ) ;         
    return ; 
}

int mark_all_scored_areas_for_this_sp ( int which )
{
    int32 sb ;
    int sc ;
    int a , i ;
    Artyp * arp , * old ;
    int32 mylis ; 
    sb = 1 << ( which % 32 ) ;
    sc = which / 32 ; 
    for ( a = i = 0 , arp = rec ; i < numrecs ; ++ i , ++ arp ) {
         // recptr = arp ; 
         // cursize = recptr -> size ; 
         // dorule5 () ; 
         // if ( ( intersptr[sc] & sb ) ) { arp -> mark = 1 ; ++ a ; }
         if ( ( arp -> splist [sc] & sb ) ) { arp -> mark = 1 ; ++ a ; }}
    return a ; 
}

void log_marked_sets_to_file ( void ) 
{  
   int a , b , option = 'x' , numarks = 0 ;
   char x ;
   Artyp * arp ; 
   a = 0 ; 
   while ( isspace ( comstring [ a ] ) && comstring [ a ] ) ++ a ; 
   if ( !comstring [ a ] ) return ; 
   logfilename = comstring + a ;
   if ( query ) {
      logfile = fopen ( logfilename , "rb" ) ;
      if ( logfile != NULL ) {
          fclose ( logfile ) ;
          sprintf ( junkstr , "File \"%s\" exists.\n"
                              "Do you want to append areas at the end?" , logfilename ) ;
          a = MessageBox ( hwnd , junkstr , "Warning" , MB_YESNOCANCEL | MB_ICONWARNING ) ;
          if ( a == IDCANCEL ) return ; 
          if ( a == IDYES )
               logfile = fopen ( logfilename , "ab" ) ;
          else logfile = fopen ( logfilename , "wb" ) ; }
      else logfile = fopen ( logfilename , "wb" ) ; } 
   else 
      logfile = fopen ( logfilename , "wb" ) ; 
   if ( logfile == NULL ) {
        showcurset () ;
        curcmd_loop = cmd_loop ; 
        captf("Can't open file %s" , logfilename ) ; 
        return ; }
   written = 0 ; 
   arp = rec ; 
   for ( a = 0 ; a < numrecs ; ++ a , ++ arp ) 
       if ( arp -> mark ) {
           ++ numarks ; 
           bsav ( sizeof ( int32 ) , arcells , ( char * ) arp -> lst ) ; 
           bsav ( sizeof ( double ) , 1 , ( char * ) &( arp -> score ) ) ; 
           bsav ( sizeof ( int ) , 1 , ( char * ) &( arp -> size ) ) ; } 
   showcurset () ; 
   fclose ( logfile ) ; 
   captf("Results (for %i marked areas) saved to file %s (%i bytes)", numarks , logfilename , written ) ; 
   return ; 
} 

void save_marked_areas_to_log ( void )
{
    int a , numarks = 0 ;
    Artyp * arp ;
    for ( a = 0 , arp = rec ; a < numrecs && !numarks ; ++ a , ++ arp )
         if ( arp -> mark ) numarks ++ ;
    if ( !numarks )  {
        showcurset () ; 
        captf ( "\nNO MARKED AREAS" ) ; }
    else {
        chkiscom ( 'L' ) ;
        log_marked_sets_to_file () ; }
    return ; 
}

void pileupmarks ( void ) 
{  int32 * lp , * lpold ;
   Artyp * prv ; 
   int i , a , merged = 0 ; 
   if ( numrecs == maxrecs ) { 
         captf("Can't do more than 100 new areas!" ) ; 
         return ; } 
   recptr = rec + numrecs ; 
   recptr -> score = 0 ; 
   recptr -> size = 0 ; 
   recptr -> mark = 0 ;
   lp = recptr -> lst ; 
   for ( a = arcells ; a -- ; ) * lp ++ = 0 ; 
   for ( i = 0 , prv = rec ; i < numrecs ; ++ i , ++ prv ) {
       if ( ! ( prv -> mark ) ) continue ;
       ++ merged ; 
       lp = recptr -> lst ;
       lpold = prv -> lst ; 
       for ( a = arcells ; a -- ; ) * lp ++ |= * lpold ++ ; }
   lp = recptr -> lst ;
   for ( a = arcells ; a -- ; ) recptr -> size += onbits ( * lp ++ ) ;
   ++ numrecs ; 
   dorule5 () ;
   showcurset () ;
   captf( "\nNew set (produced by piling up %i marked sets)" , merged ) ;
   return ; 
} 

double ** spp_x_area ;
int ** nums_x_area ; 

void effect_writesppinfo ( int talk )
{
    int i , a , scorefor ; 
    Artyp * arp = recptr ;
    int32 * lst , mb , mc ;
    double highest , next ; 
    spp_x_area = malloc ( spp * sizeof ( double * ) ) ;
    if ( spp_x_area == NULL ) {
        captf ( "Sorry, not enough RAM available for this operation" ) ;
        return ; }
    for ( i = 0 ; i < spp ; ++ i ) {
         spp_x_area[i] = malloc ( numrecs * sizeof ( double ) ) ;
         if ( spp_x_area[i] == NULL ) {
             while ( -- i ) free ( spp_x_area[i] ) ;
             free ( spp_x_area ) ;
             captf ( "Sorry, not enough RAM available for this operation" ) ; }}
    fprintf ( outspace , "\n------------------------------------------------\nINFORMATION ON ENDEMIC SPECIES\n------------------------------------------------\n" ) ; 
    pleasewait ( "Calculating individual species scores" ) ; 
    for ( a = 0 , recptr = rec ; a < numrecs ; ++ a , ++ recptr ) {
            dorule5 () ;
            lst = intersptr ;
            for ( i = 0 ; i < spp ; ++ i ) {
                if ( ( lst [ i / 32 ] & ( 1 << ( i % 32 ) ) ) ) spp_x_area[i][a] = spscore[i] ;
                else spp_x_area[i][a] = 0 ; }}
    for ( i = 0 ; i < spp ; ++ i ) {
        scorefor = 0 ; 
        highest = 0 ;
        for ( a = 0 ; a < numrecs ; ++ a ) {
            if ( spp_x_area[i][a] == 0 ) continue ;
            ++ scorefor ; 
            if ( highest < spp_x_area[i][a] ) 
                 highest = spp_x_area[i][a] ; }
        fprintf ( outspace , "\nSp. %i " , i ) ;
        if ( spname != NULL )
            fprintf ( outspace , "%s" , spname[i] ) ;
        if ( data_is_xydata )
            fprintf ( outspace , " (%i records)" , xymatrix[i].numrecs ) ;
        fprintf ( outspace , "\n" ) ; 
        fprintf ( outspace , "Endemic for %i sets (set/score):\n" , scorefor ) ;
        while ( highest > 0 ) {
           next = 0 ;
           for ( a = 0 ; a < numrecs ; ++ a ) {
              if ( spp_x_area[i][a] == highest ) {
                  fprintf ( outspace , "   %4i: %.6f\n" , a , highest ) ;
                  spp_x_area[i][a] = 0 ; }
              else {
                if ( next < spp_x_area[i][a] ) 
                     next = spp_x_area[i][a] ; }}
           highest = next ; }
       }
    recptr = arp ; 
    imdone () ; 
    for ( i = 0 ; i < spp ; ++ i ) free ( ( void * ) spp_x_area[i] ) ;
    free ( ( void * ) spp_x_area ) ;
    spp_x_area = NULL ; 
    if ( talk ) captf ( "Wrote info on endemic spp. to output file" ) ;
    else captf ( "Wrote all info to output file" ) ;
}

void effect_writesetsinfo ( int talk )
{
    int a , i , numendems ;
    int32 mb , mc ; 
    Artyp * arp = recptr ;
    spp_x_area = malloc ( spp * sizeof ( double * ) ) ;
    if ( spp_x_area == NULL ) {
        captf ( "Sorry, not enough RAM available for this operation" ) ;
        return ; }
    for ( i = 0 ; i < spp ; ++ i ) {
         spp_x_area[i] = malloc ( numrecs * sizeof ( double ) ) ;
         if ( spp_x_area[i] == NULL ) {
             while ( -- i ) free ( spp_x_area[i] ) ;
             free ( spp_x_area ) ;
             captf ( "Sorry, not enough RAM available for this operation" ) ; }}
    fprintf ( outspace , "\n------------------------------------------------\nINFORMATION ON AREAS\n------------------------------------------------\n" ) ; 
    pleasewait ( "Calculating individual species scores" ) ; 
    for ( a = 0 , recptr = rec ; a < numrecs ; ++ a , ++ recptr ) {
            dorule5 () ;
            lst = intersptr ;
            for ( i = 0 ; i < spp ; ++ i ) {
                if ( ( lst [ i / 32 ] & ( 1 << ( i % 32 ) ) ) ) spp_x_area[i][a] = spscore[i] ;
                else spp_x_area[i][a] = 0 ; }}
    recptr = arp ; 
    for ( arp = rec , a = 0 ; a < numrecs ; ++ a , ++ arp ) {
        fprintf ( outspace , "\nSET NR. %i, size %i, score %.6f\n%i scoring spp. (sp/score):\n" , a , arp -> size , arp -> score , arp -> numspp ) ;
        for ( i = 0 ; i < spp ; ++ i )
            if ( ( arp -> splist[ i / 32 ] & ( 1 << ( i % 32 ) ) ) ) {
                   fprintf ( outspace , "    %i " , i ) ;
                   if ( spname != NULL )
                       fprintf ( outspace , "%s: " , spname[i] ) ;
#ifdef _DEBUGGING_
fprintf ( outspace , "   %i: " , spbecomes [ i ] ) ; 
#endif
                   fprintf ( outspace , "%.6f\n" , spp_x_area[i][a] ) ; }}
    imdone () ; 
    for ( i = 0 ; i < spp ; ++ i ) free ( ( void * ) spp_x_area[i] ) ;
    free ( ( void * ) spp_x_area ) ; 
    spp_x_area = NULL ; 
    if ( talk ) captf ( "Wrote info on sets (and their endemics) to output file" ) ;
}

void effect_writeconsinfo ( int talk )
{
  static int x , cursp = 0 ; 
  static int a , i , j , k , mc ; 
  int32 mb , inbits ; 
  int curwas ;
  static int list_the_spp ;
  int numspcols ; 
  Constyp * conpt ;
  Artyp * rpt ; 
  char * cp ;
  double range , val , imat ;
  int just_marked = 0 ;
  int curconswas = curcons ; 
  if ( !consensus_is_sample ) {
     fprintf ( outspace , "\n------------------------------------------------\nINFORMATION ON CONSENSUS AREAS\n------------------------------------------------\n" ) ; 
     if ( !chain_spp ) 
          fprintf ( outspace , "With cut %i, calculated against each of the other areas, " , conscut ) ; 
     else fprintf ( outspace , "With cut %i, Calculated against any of the other areas, " , conscut ) ; 
     fprintf ( outspace , "TOTAL: %i consensus areas\n\n" , numcons ) ; }
  else {
      if ( consensus_is_sample == 1 ) fprintf ( outspace , "------------------------------------\nCONSENSUS INFORMATION ON AREA RECOVERY\n" ) ;
      else if ( consensus_is_sample == 2 ) fprintf ( outspace , "\n------------------------------------\nCONSENSUS INFORMATION ON SPP. RECOVERY\n" ) ; 
      else fprintf ( outspace , "\n------------------------------------\nCONSENSUS INFORMATION ON AREAS FOUND BY SAMPLED DATA\n" ) ;
      fprintf ( outspace , "\n" ) ; }
  for ( curcons = 0 ; curcons < numcons ; ++ curcons ) {
       conpt = consen + curcons ;
       if ( consensus_is_sample == 3 )
            fprintf ( outspace , "Consensus area %i (from %i replicates), " , curcons , conpt->numareas ) ;
       else fprintf ( outspace , "Consensus area %i (from %i areas), " , curcons , conpt->numareas ) ;
       range = conpt->max - conpt->min ;
       consen_minval = conpt->min ;
       consen_maxval = conpt->max ;
       if ( consensus_is_sample ) {
         if ( consensus_is_sample == 1 ) 
            fprintf ( outspace , "Area Recovery for included areas: %.2f-%.2f\n" , consen_minval , consen_maxval ) ; 
         else if ( consensus_is_sample == 2 ) 
           fprintf ( outspace , "Spp. Recovery for included areas: %.2f-%.2f\n" , consen_minval , consen_maxval ) ;
           }
       else {           
           consen_intrvl = range / 7 ;
           if ( consen_intrvl < 0.25 ) consen_intrvl = 0.25 ; 
           j = 0 ;
           for ( a = 0 ; a < spp ; ++ a ) if ( conpt->spmax[a] > 0 ) ++ j ; 
           fprintf ( outspace , "%i species give score:\n" , j ) ; 
           for ( j = 0 ; j < spp ; ++ j ) {
              if ( conpt->spmax[j] == 0 ) continue ;
              fprintf ( outspace , "    %i " , j ) ;
              if ( spname != NULL )
                   fprintf ( outspace , "%s (%i): " , spname[j] , j ) ;
              fprintf ( outspace , "(%.3f" , conpt->spmin[j] ) ;
              if ( conpt->spmax[j] > conpt->spmin[j] )
                 fprintf ( outspace , "-%.3f) " , conpt->spmax[j] ) ;
              else fprintf ( outspace , ")" ) ;
              fprintf ( outspace , "\n" ) ; }}
       if ( !consensus_is_sample ) 
            fprintf ( outspace , "Areas included: " ) ;
       else if ( consensus_is_sample == 1 ) fprintf ( outspace , "Areas included (with area recovery vals): " ) ;
       else if ( consensus_is_sample == 2 ) fprintf ( outspace , "Areas included (with spp. recovery vals): " ) ;
       else fprintf ( outspace , "Areas included (replicate): " ) ;
       for ( a = j = 0 , mb = 1 , mc = 0 ; a < numrecs ; ++ a ) {
           if ( ( conpt->arlist[mc] & mb ) ) {
               recptr = rec + a ; 
               if ( ( j % 10 ) == 0 ) 
                   fprintf ( outspace , "\n        " ) ;
               if ( !consensus_is_sample ) 
                    fprintf ( outspace , "%i " , a ) ;
               else {
                  if ( consensus_is_sample == 1 ) fprintf ( outspace , "%i(%.2f) " , a , recptr -> bootarval ) ;
                  else if ( consensus_is_sample == 2 ) fprintf ( outspace , "%i(%.2f) " , a , recptr -> bootspval ) ;
                  else fprintf ( outspace , "%i(%3i) " , a , recptr -> fromrepl ) ;}
               ++ j ; 
               cp += i ; }
           if ( mb == BIT32 ) { mb = 1 ; ++ mc ; }
           else mb <<= 1 ; }
       fprintf ( outspace , "\n\n" ) ; }
    curcons = curconswas ; 
    if ( talk ) captf ( "Wrote info on consensus areas to output file" ) ;
}

void dograndsumofpoints ( void ) 

{
    unsigned long int totpoints = 0 ;
    int i ; 
    if ( data_is_xydata ) {
        for ( i = 0 ; i < numterminals ; ++ i ) {
            if ( xymatrix[i].numrecs == 0 ) continue ;
            totpoints += xymatrix[i].numrecs ; }}
    grandsumofpoints = totpoints ; 
    return ;
}

void effect_writedatainfo ( int talk )
{
    int a , i , j , spread = 0 , totpoints = 0 ; 
    fprintf ( outspace , "\n------------------------------------------------\nINFORMATION ON DATA\n------------------------------------------------\n" ) ; 
    if ( data_is_xydata ) {
        for ( i = 0 ; i < numterminals /*spp */ ; ++ i ) {
            if ( xymatrix[i].numrecs == 0 ) continue ;
            ++ spread ;
            totpoints += xymatrix[i].numrecs ; }
        fprintf ( outspace , "\nRead records for %i species (%i unique points total" , spread , totpoints ) ;
        if ( species_tree != NULL ) fprintf ( outspace , " plus %i clades" , number_of_groups - 1 ) ; 
        fprintf ( outspace , ")\n" ) ; 
        }
    else fprintf ( outspace , "\nNo point records \n" ) ; 
    if ( grid_created ) {
        nums_x_area = malloc ( rows * sizeof ( double * ) ) ;
        if ( nums_x_area == NULL ) {
            captf ( "Sorry, not enough RAM available for this operation" ) ;
            return ; }
        for ( i = 0 ; i < rows ; ++ i ) {
             nums_x_area[i] = malloc ( cols * sizeof ( double ) ) ;
             if ( nums_x_area[i] == NULL ) {
                 while ( -- i ) free ( nums_x_area[i] ) ;
                 free ( nums_x_area ) ;
                 captf ( "Sorry, not enough RAM available for this operation" ) ; }}
        if ( data_is_xydata ) {
            fill_matrix_for_numpoints ( 1 ) ;
            fprintf ( outspace , "\nTOTAL RECORDS/CELL (%i ROWS x %i COLS):\n" , rows , cols ) ;
            write_nums_x_area () ; 
            fill_matrix_for_numpoints ( 0 ) ;
            fprintf ( outspace , "\nNUMBER OF SPECIES/CELL (%i ROWS x %i COLS):\n" , rows , cols ) ;
            write_nums_x_area () ;
            fill_nums_of_species ( 1 ) ; 
            fprintf ( outspace , "\nNUMBER OF SPECIES/CELL, including assumed records (%i ROWS x %i COLS):\n" , rows , cols ) ;
            write_nums_x_area () ; }
        else {
            fill_nums_of_species ( 0 ) ; 
            fprintf ( outspace , "\nNUMBER OF SPECIES/CELL (%i ROWS x %i COLS):\n" , rows , cols ) ;
            write_nums_x_area () ;
            fill_nums_of_species ( 1 ) ; 
            fprintf ( outspace , "\nNUMBER OF SPECIES/CELL, including assumed records (%i ROWS x %i COLS):\n" , rows , cols ) ;
            write_nums_x_area () ; }

        for ( i = 0 ; i < rows ; ++ i ) free ( ( void * ) nums_x_area[i] ) ;
        free ( ( void * ) nums_x_area ) ;
        nums_x_area = NULL ; }
    if ( talk ) captf ( "Wrote info on data to output file" ) ;

}

void write_nums_x_area ( void )
{
    int i , j ;
    fprintf ( outspace , "row\\col" ) ; 
    for ( i = 0 ; i < cols ; ++ i ) fprintf ( outspace , " %5i " , i ) ;
    fprintf ( outspace , "\n" ) ; 
    for ( i = 0 ; i < rows ; ++ i ) {
        fprintf ( outspace , " %-5i " , i ) ;
        for ( j = 0 ; j < cols ; ++ j ) fprintf ( outspace , "%6i " , nums_x_area[i][j] ) ;
        fprintf ( outspace , "\n" ) ; }
    return ;
}

void fill_matrix_for_numpoints ( int dototrecords )
{
   signed int a , b , c , d , at ;
   signed int xis , yis ; 
   unsigned long int x ; 
   double startx , starty ;
   double grid_height , grid_width , myy , myx ;
   double xbeg , xend , ybeg , yend ; 
   startx = grid_startx ;
   starty = grid_starty ;
   grid_height = truecellhei ;
   grid_width = truecellwid ; 
   for ( a = 0 ; a < rows ; ++a ) 
     for ( b = 0 ; b < cols ; ++ b ) {
        nums_x_area[a][b] = 0 ; 
        xbeg = startx + ( b * truecellwid ) ; 
        xend = xbeg + truecellwid ;
        ybeg = starty + ( a * truecellhei ) ;
        yend = ybeg + truecellhei ; 
        for ( c = spp ; c -- ; ) 
            for ( d = xymatrix[c].numrecs ; d -- ; ) {
                myx = xymatrix[c].x[d] ;
                myy = xymatrix[c].y[d] ;
                if ( myx >= xbeg && myx <= xend && myy >= ybeg && myy <= yend ) {
                     nums_x_area[a][b] ++ ;
                     if ( !dototrecords ) break ; }}}
   return ; 
}

void fill_nums_of_species ( int all )
{
    int i , j , k ;
    int32 * mysp , mb , mc ;
    for ( i = 0 ; i < rows ; ++ i ) 
      for ( j = 0 ; j < cols ; ++ j ) {
        nums_x_area[i][j] = 0 ;
        for ( k = 0 ; k < spp ; ++ k ) 
            if ( ( matrix[i][j][k/32] & ( 1 << ( k % 32 ) ) ) ||
                 ( assmatrix[i][j][k/32] & ( 1 << ( k % 32 ) ) ) ) ++ nums_x_area[i][j] ; }
    return ;
}

/*** Reading a 0/1/2 matrix ********/

void ndm_chkdouble ( char * bs , double * nua , double * nub )
{
  int mysign , x ;
  float f ; 
  if ( strcmp ( str , bs ) ) return ; 
  x = ' ' ;
  mysign = 1 ; 
  while ( isspace ( x ) ) x = getc ( infile ) ;
  if ( x == '-' ) mysign = -1 ;
  else ungetc ( x , infile ) ; 
  if ( !fscanf ( infile , " %f", &f ) )  
      ermsg ( "Error in input file. Number expected" ) ;
  * nua = f * mysign ; 
  x = ' ' ;
  mysign = 1 ; 
  while ( isspace ( x ) ) x = getc ( infile ) ;
  if ( x == '-' ) mysign = -1 ;
  else ungetc ( x , infile ) ; 
  if ( !fscanf ( infile , " %f", &f ) )  
      ermsg ( "Error in input file.  TWO numbers expected" ) ;
  * nub = f * mysign ; 
  return ; 
}    

void nexar ( int * a , int * b ) 
{ int x = getc ( infile ) ; 
  while ( isspace ( x ) ) x = getc ( infile ) ; 
  if ( tolower ( x ) != 'a' ) ermsg ( "Expected area definition (Ai-j)" ) ; 
  if ( !fscanf ( infile , " %i" , a ) ) ermsg ( "Expected area definition (Ai-j)" ) ; 
  x = getc ( infile ) ; 
  if ( x != '-' ) ermsg  ("Areas must be indicated with Ai-j" ) ; 
  if ( !fscanf ( infile , " %i" , b ) ) ermsg ( "Expected area definition (Ai-j)" ) ; 
  return ; 
} 

int nexnu ( void ) 
{ 
   int x = getc ( infile ) ; 
   while ( isspace ( x ) ) x = getc ( infile ) ; 
   if ( x == ';' ) return -1 ; 
   if ( x == '1' ) return 1 ; 
   if ( x == '2' ) return 2 ; 
   if ( x == '0' ) return 0 ; 
   ungetc ( x , infile ) ; 
   return 3 ; 
} 

extern int faked_a_grid ;

void read_input_matrix ( void )
{
   int a , b , c , x , i , valsread , valstoread , maxvalread = 0 ; 
   int32 * ptr , * infptr ; 
   int atb ;
   int theospp ; 
   Artyp * dorec ;
   MinMaxtyp * mmpt ; 
   str[0]=0 ;
   read_as_a_dat_file = 1 ; 
   while ( strcmp ( str , "data" ) ) {
       fscanf ( infile , " %s", &str ) ; 
       if ( feof ( infile ) ) ermsg ( "Found EOF before data appeared!" ) ; 
       if ( !strcmp ( str , "xnegative" ) ) xsign = xsignmap = -1 ; 
       if ( !strcmp ( str , "ynegative" ) ) ysign = ysignmap = 1 ; 
       chkword ( "rows" , &rows ) ; 
       chkword ( "cols" , &cols ) ; 
       chkword ( "spp" , &spp ) ;
       ndm_chkdouble ( "gridx" , &grid_startx , &grid_width ) ; 
       ndm_chkdouble ( "gridy" , &grid_starty , &grid_height ) ; }
   if ( grid_startx < 10e200 ) {
      if ( grid_starty > 10e199 ) ermsg ( "If you specify X coordinates, you must also specify Y coordinates" ) ; 
      grid_startx *= xsign ;
      created_orgx = grid_startx ; 
      truecellwid = grid_width ; }
   if ( grid_starty < 10e200 ) {
      if ( grid_startx > 10e199 ) ermsg ( "If you specify Y coordinates, you must also specify Y coordinates" ) ; 
      grid_starty *= ysign ;
      created_orgy = grid_starty ; 
      truecellhei = grid_height ; }

   spcells = ( spp + 31 ) / 32 ; 
   arcells = ( ( rows * cols ) + 31 ) / 32 ; 
   totareas = rows * cols ;
   memerr ( widefilter = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ; 
   memerr ( archeckd = ( int * ) malloc ( totareas * sizeof ( int ) ) ) ;
   memerr ( fillist = ( char ** ) malloc ( rows * sizeof ( char * ) ) ) ;
   for ( a = rows ; a -- ; )
        memerr ( fillist [ a ] = ( char * ) malloc ( cols * sizeof ( char ) ) ) ; 
   a = totareas ; 
   if ( a < ( spp + 31 ) ) a = spp + 31 ; 
   memerr ( tmplist = ( int * ) malloc ( a * sizeof ( int ) ) ) ; 
   memerr ( intersptr = (int32 *) malloc ( spcells * sizeof ( int32 ) ) ) ; 
   memerr ( dablor = (int32 *) malloc ( spcells * sizeof ( int32 ) ) ) ; 
   memerr ( dabland = (int32 *) malloc ( spcells * sizeof ( int32 ) ) ) ; 
   memerr ( setlist = ( int * ) malloc ( rows * cols * sizeof ( int ) ) ) ; 
   memerr ( nosetlist = ( int * ) malloc ( rows * cols * sizeof ( int ) ) ) ; 
   memerr ( numentries = ( int * ) malloc ( spp * sizeof ( int ) ) ) ; 
   memerr ( numassentries = ( int * ) malloc ( spp * sizeof ( int ) ) ) ;
   memerr ( listin = ( int * ) malloc ( totareas * sizeof ( int ) ) ) ; 
   memerr ( listadja = ( int * ) malloc ( totareas * sizeof ( int ) ) ) ; 
   memerr ( listnonadja = ( int * ) malloc ( totareas * sizeof ( int ) ) ) ;
   memerr ( spscore = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dout = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dpres = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dinf = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dass = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dadja = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( dnadja = ( double * ) malloc ( spp * sizeof ( double ) ) ) ;
   memerr ( isdefd = ( char ** ) malloc ( rows * sizeof ( char * ) ) ) ;
   species_tree = NULL ; 
   spspace = spp ; 
   num_higher_taxa = 0 ; 
   for ( a = rows ; a -- ; ) { 
        memerr ( isdefd [ a ] = ( char * ) malloc ( cols * sizeof ( char ) ) ) ;
        for ( b = 0 ; b < cols ; ++ b ) isdefd[a][b] = 0 ; } 
   memerr ( matrix = ( int32 *** ) malloc ( rows * sizeof ( int32 ** ) ) ) ; 
   memerr ( assmatrix = ( int32 *** ) malloc ( rows * sizeof ( int32 ** ) ) ) ; 
   for ( a = rows ; a -- ; ) { 
        memerr ( matrix [ a ] = ( int32 ** ) malloc ( cols * sizeof ( int32 * ) ) ) ; 
        memerr ( assmatrix [ a ] = ( int32 ** ) malloc ( cols * sizeof ( int32 * ) ) ) ; 
        for ( b = cols ; b -- ; )  { 
             memerr ( matrix [ a ] [ b ] = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ; 
             memerr ( assmatrix [ a ] [ b ] = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ;  
             for ( c = spcells ; c -- ; ) matrix [ a ] [ b ] [ c ] = assmatrix [ a ] [ b ] [ c ] = 0 ; }}
   maxrecs = 10000 ; 
   memerr ( rec = ( Artyp * ) malloc ( ( maxrecs ) * sizeof ( Artyp ) ) ) ; 
   memerr ( arlist = ( Artyp ** ) malloc ( ( maxrecs ) * sizeof ( Artyp * ) ) ) ; 
   dorec = rec ; 
   for ( a = maxrecs ; a -- ; ) { 
       memerr ( dorec -> lst = ( int32 * ) malloc ( arcells * sizeof ( int32 ) ) ) ; 
       memerr ( dorec -> splist = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ; 
       ++ dorec ; } 
   numrecs = 0 ; 
   memerr ( splist = ( int32 * ) malloc ( arcells * sizeof ( int32 ) ) ) ;
   memerr ( inflist = ( int32 * ) malloc ( arcells * sizeof ( int32 ) ) ) ;
   memerr ( sccol = ( char ** ) malloc ( ( cols + 2 ) * sizeof ( char *  ) ) ) ; 
   for ( a = 0 ; a < ( cols + 2 ) ; ++ a ) 
          memerr ( sccol [ a ] = ( char * ) malloc ( ( rows + 2 ) * sizeof ( char ) ) ) ;   
   recalculate_numentries ( -1 ) ;
   memerr ( spact = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ;
   memerr ( spminmax = ( MinMaxtyp * ) malloc ( spp * sizeof ( MinMaxtyp ) ) ) ; 
   for ( a = 0 ; a < spcells ; ++ a ) spact[a] = -1 ;
   grid_created = 1 ; 
   /*** Reading data *********/
   nums_x_area = malloc ( rows * sizeof ( double * ) ) ;
   if ( nums_x_area == NULL ) {
       ermsg ( "Sorry, not enough RAM available for this operation" ) ;
       return ; }
   for ( i = 0 ; i < rows ; ++ i ) {
        nums_x_area[i] = malloc ( cols * sizeof ( double ) ) ;
        if ( nums_x_area[i] == NULL ) {
            while ( -- i ) free ( nums_x_area[i] ) ;
            free ( nums_x_area ) ;
            ermsg ( "Sorry, not enough RAM available for this operation" ) ; }
        for ( b = 0 ; b < cols ; ++ b ) nums_x_area[i][b] = 0 ; }
   valstoread = 0 ;

   mmpt = spminmax ; 
   for ( a = 0 ; a < spp ; ++ a , ++ mmpt ) {
       mmpt -> minc = mmpt -> minr = 32767 ; 
       mmpt -> maxc = mmpt -> maxr = 0 ; }

   while ( 1 ) { 
       nexar ( &a , &b ) ; 
       if ( a >= rows || b >= cols ) {
              sprintf ( junkstr , "Cannot read value for area %i-%i (maxrows=%i, maxcols=%i)\n" , b , a , rows, cols ) ; 
              ermsg ( junkstr ) ; } 
       x = nexnu () ;
       valsread = nums_x_area[a][b] ;
       ptr = matrix[a][b] + ( valsread / 32 ) ; 
       infptr = assmatrix[a][b] + ( valsread / 32 ) ;
       atb = ( valsread % 32 ) ; 
       mmpt = spminmax + valsread ; 
       while ( ( x <= 2 && x >= 0 ) && !feof ( infile ) ) {
           if ( x == 1 ) { 
               if ( mmpt -> minc > b ) mmpt -> minc = b ; 
               if ( mmpt -> maxc < b ) mmpt -> maxc = b ; 
               if ( mmpt -> minr > a ) mmpt -> minr = a ; 
               if ( mmpt -> maxr < a ) mmpt -> maxr = a ; 
               ++ numentries [ valsread ] ;
               ++ numassentries [ valsread ] ; 
               * ptr |= ( 1 << atb ) ;
               * infptr |= ( 1 << atb ) ; }
           if ( x == 2 ) { 
               ++ numassentries [ valsread ] ; 
               * infptr |= ( 1 << atb ) ; }
           ++ nums_x_area[a][b] ; 
           ++ valsread ;
           ++ mmpt ; 
           if ( valsread > spp ) {
                   sprintf ( junkstr , "Too many species for area %i-%i" , a , b ) ; 
                   ermsg ( junkstr ) ; }
           if ( ++ atb == 32 ) { 
              atb = 0 ; 
              * ++ ptr = 0 ;
              * ++ infptr = 0 ; 
              if ( ptr - matrix[a][b] > spcells ) { 
                   sprintf ( junkstr , "Too many species for area %i-%i" , a , b ) ; 
                   ermsg ( junkstr ) ; }}
           x = nexnu () ; } 
       isdefd [ a ] [ b ] = 1 ;
       if ( valsread > maxvalread ) maxvalread = valsread ; 
       if ( feof ( infile ) || x < 0 ) break ; }
   theospp = numterminals = spp ; 
   if ( spname == NULL ) {
        spname = ( char * ) mymem ( spp * sizeof ( char * ) ) ;
        for ( a = 0 ; a < spp ; ++ a ) spname[a] = NULL ; }
   spp = maxvalread ; 
   if ( x < 0 )
      get_species_tree ( theospp , 1 ) ;   // this function increases "spp", if needed
   imdone () ; 
   for ( i = 0 ; i < rows ; ++ i ) free ( ( void * ) nums_x_area[i] ) ;
   free ( ( void * ) nums_x_area ) ;
   nums_x_area = NULL ;
   add_species_groups () ;
   i = ( ( ( 2 * spp ) + 31 ) / 32 ) ;   // multiply by TWO, so that you can fit all tree nodes... 
   memerr ( spingrid = ( int32 * ) malloc ( i * sizeof ( int32 ) ) ) ;
   shift_group_names () ; 
   spcells = ( spp + 31 ) / 32 ; 
   if ( grid_startx < 10e200 ) {
       grid_created = data_is_xydata = 2 ;
       maplin = NULL ; 
       xymatrix = ( Coordtyp * ) mymem ( spp * sizeof ( Coordtyp ) ) ;
       for ( a = spp ; a -- ; ) xymatrix[a].defd = xymatrix[a].numrecs = 0 ; }
   return ; 
}

void deleteunmarks ( void )
{
    Artyp * this ;
    int numdeletes = 0 , a ; 
    for ( a = 0 , this = rec ; a < numrecs ; ++ a , ++ this ) {
        this -> erase = this -> mark ; 
        if ( !this -> mark ) ++ numdeletes ; }
    delete_marks ( 0 ) ;
    curcmd_loop = cmd_loop ;
    a = 0 ; 
    if ( !numrecs ) { a = 1 ; donewset () ; }
    recptr = rec ; 
    showcurset () ;
    if ( !a ) 
         captf ( "Deleted %i un-marked sets" , numdeletes ) ;
    else captf ( "Deleted %i un-marked sets (none remained; created a new, empty one)" , numdeletes ) ;
    return ; 
}            

    
void set_recptr_to ( int which )
{
    if ( which >= numrecs ) ermsg ( "OOPS!! Cannot set current record" ) ;
    recptr = rec + which ;
}


/*********   To read points after having read a *.dat matrix ****************/
void post_read_xydata ( void )
{ char str [ 10 ] , * cp ; 
  float * tmprec , * sptr ;
  Tmptyp * tmppr ;
  float wid , hei , cellwid , cellhei , startx , starty , xbeg , ybeg , xend , yend ;
  float myx , myy ; 
  int a , b , c , d , x ;
  int numsp , read , at ;
  float xrad , yrad ;
  float inx , iny , tmpdouble ;
  data_is_xydata = 1 ; 
  spcells = ( spp + 31 ) / 32 ; 
  xymatrix = ( Coordtyp * ) mymem ( spp * sizeof ( Coordtyp ) ) ;
  for ( a = spp ; a -- ; ) xymatrix[a].defd = xymatrix[a].numrecs = 0 ; 
  tmpcord = ( Tmptyp * ) mymem ( MAXY * sizeof ( Tmptyp ) ) ; 
  x = ' ' ; 
  while ( !feof ( infile ) ) {
           while ( isspace ( x ) ) x = getc ( infile ) ;
           cp = str ; 
           while ( !isspace ( x ) ) {
               * cp ++ = tolower ( x ) ;
               x = getc ( infile ) ; }
           * cp = '\0' ;
           if ( !strcmp ( str , "map" ) ) { read_map_definition ( 1 ) ; break ; }
           if ( strcmp ( str , "sp" ) ) {
               if ( numsp >= 0 ) 
                     fprintf ( stderr , "\nError reading data for sp. %i\n" , numsp ) ;
               else fprintf ( stderr , "\nError expecting data data for first sp.\n" ) ;
               ermsg ("Give xy data with sp N [x][y]" ) ; } 
           if ( !fscanf ( infile , " %i" , &numsp ) ) ermsg ( "Must give species number after \"sp\"") ;
           if ( numsp >= spp ) ermsg ( "Wrong species number" ) ;
           if ( xymatrix[numsp].defd ) {
                   sprintf ( junkstr ,"\nValues for sp. %i already defined\n" , numsp ) ; 
                   ermsg ( junkstr ) ; }
           get_spname ( numsp ) ; 
           tmppr = tmpcord ;
           while ( 1 ) {
              if ( tmppr - tmpcord >= MAXY ) {
                  sprintf ( junkstr ,"Cannot read more than %i areas per species\n" , MAXY ) ;
                  ermsg ( junkstr ) ; }
              x = getc ( infile ) ;
              while ( isspace ( x ) ) x = getc ( infile ) ;
              if ( !isdigit ( x ) && x != '.' && x != '-' ) break ;
              if ( feof ( infile ) ) break ;
              ungetc ( x , infile ) ;
              fscanf ( infile , " %f" , &inx ) ;
              if ( !nocommas ) {
                  x = ' ' ;
                  while ( isspace ( x ) ) x = getc ( infile ) ; 
                  if ( x != ',' ) ermsg ( "All values for each point must be comma-separated\n(or indicate \"nocommas\" in the input file)" ) ;
                  while ( isspace ( x ) ) x = getc ( infile ) ; }
              if ( !fscanf ( infile , " %f" , &iny ) )
                   ermsg ( "All values of x-y must be given in pairs!") ;
              while ( eat_comma_preceded_nr ( 1 ) ) ;
              if ( transposexy ) {
                   tmpdouble = inx ;
                   inx = iny ;
                   iny = tmpdouble ; }
              else if ( dolatlong ) {
                      tmpdouble = inx ;
                      inx = iny ;
                      iny = tmpdouble ; }
              inx = inx * xsign ; 
              inx = ( ( inx - mminusx ) * mfactor ) ;
              tmppr -> x = inx ; 
              if ( tmppr -> x > maxx ) maxx = tmppr -> x ; 
              if ( tmppr -> x < minx ) minx = tmppr -> x ; 
              iny = iny * ysign ;
              iny = ( ( iny - mminusy ) * mfactor ) ;
              tmppr -> y = iny ; 
              if ( tmppr -> y > maxy ) maxy = tmppr -> y ; 
              if ( tmppr -> y < miny ) miny = tmppr -> y ; 
              ++ tmppr ; }
           read = tmppr - tmpcord ; 
           xymatrix [ numsp ].x = ( float * ) mymem ( ( read + 1 ) * sizeof ( float ) ) ; 
           xymatrix [ numsp ].y = ( float * ) mymem ( ( read + 1 ) * sizeof ( float ) ) ; 
           at = 0 ; 
           while ( tmppr > tmpcord ) {
                  -- tmppr ;
                  xymatrix[numsp].x[at] = tmppr->x ; 
                  xymatrix[numsp].y[at] = tmppr->y ;
                  ++ at ; }
           records_read += read ; 
           xymatrix[numsp].numrecs = read ; }
   set_unnamed_spp ( ) ;
   spcells = ( ( spp + 31 ) / 32 ) ; 
   memerr ( spingrid = ( int32 * ) malloc ( spcells * sizeof ( int32 ) ) ) ;
   for ( a = 0 ; a < spcells ; ++ a ) spingrid[a] = -1 ;
   num_spingrid = spp ;
   return ; 
}

void post_read_xyfile ( void ) 
{   int a ;
    str[0]=0;
    infile = fopen ( comstring , "rb" ) ;
    if ( infile == NULL ) ermsg ( "Cannot open file for input" ) ;
    while ( strcmp ( str , "xydata" ) ) {
       fscanf ( infile , " %s", &str ) ; 
       if ( feof ( infile ) ) ermsg ( "Found EOF before data appeared!" ) ;
       if ( !strcmp ( str , "nocommas" ) ) nocommas = 1 ; 
       if ( !strcmp ( str , "transpose" ) ) { transposexy = 1 ; transposexymap = 1 ; }
       if ( !strcmp ( str , "latlong" ) ) dolatlong = 1 ;
       if ( !strcmp ( str , "longlat" ) ) dolatlong = 0 ;
       if ( !strcmp ( str , "transposemap" ) ) transposexymap = 1 ; 
       if ( !strcmp ( str , "xnegative" ) ) { xsign = -1 ; xsignmap = -1 ; }
       if ( !strcmp ( str , "ynegative" ) ) { ysign = 1 ; ysignmap = 1 ; }
       if ( !strcmp ( str , "xnegativemap" ) ) xsignmap = -1 ; 
       if ( !strcmp ( str , "ynegativemap" ) ) ysignmap = 1 ; 
       // if ( !strcmp ( str , "autogrid" ) ) use_autosize_grid = 1 ;
       // if ( !strcmp ( str , "automatrix" ) ) do_automatrix = 1 ; 
       // chksinglefloat ( "mfactor" , &mfactor ) ; 
       chksinglefloat ( "mminusx" , &mminusx ) ; 
       chksinglefloat ( "mminusy" , &mminusy ) ; 
       chksinglefloat ( "mfactormap" , &mfactormap ) ; 
       chksinglefloat ( "mminusxmap" , &mminusxmap ) ; 
       chksinglefloat ( "mminusymap" , &mminusymap ) ; 
       // chkword ( "rows" , &rows ) ; 
       // chkword ( "cols" , &cols ) ; 
       // chkword ( "spp" , &spp ) ;
       // chkdouble ( "gridx" , &grid_startx , &grid_width ) ; 
       // chkdouble ( "gridy" , &grid_starty , &grid_height ) ;
       // chkdouble ( "fill" , &fill_x_is , &fill_y_is ) ; 
       // chkdouble ( "assume" , &assume_x_is , &assume_y_is ) ; 
       }
   read_as_a_dat_file = 0 ; 
   post_read_xydata () ;
}

void end_xy_file ( void )
{
    double tmp ; 
    xperc = fill_x_is ; 
    yperc = fill_y_is ; 
    xassperc = assume_x_is ; 
    yassperc = assume_y_is ; 
    if ( use_autosize_grid ) {
       tmp = set_autosizegrid () ; 
       truecellwid = truecellhei = tmp ; 
       cols = 2 ; 
       while ( grid_startx + ( truecellwid * ( cols - 1 ) ) < maxx ) ++ cols ; 
       rows = 2 ; 
       while ( grid_starty + ( truecellhei * ( rows - 1 ) ) < maxy ) ++ rows ; }  
    if ( do_automatrix ) create_matrix_from_points ( 0 ) ;
    return ; 
}

/***************************************************************************\
|                   Facilities for Defining Higher Groups                   |
\***************************************************************************/

void mksis ( int * an )
{ int * list = treelist ; 
  int * x = list , * y = list + 1;
  int * last , nd ; 
  int a, i;
  last = list ; 
  for ( a = 2*numterminals-1 ; a -- ; ) 
      treesis [ a ] = treefirs [ a ] = list [ a ] = -1 ;
  for ( a = numterminals ; a -- ; ) {
      i = an [ nd = a ] ; 
      if ( !i ) continue ; 
      while ( i != numterminals && treefirs [ i ] < 0 ) {
                    last [ i ] = treefirs [ i ] = nd ;
                    nd = i ;
                    i = an [ i ] ; }
      if ( treefirs [ i ] < 0 ) treefirs [ i ] = nd ; // i.e. i == numterminals 
      if ( last [ i ] >= 0 ) treesis [ last [ i ] ] = nd ;
      last [ i ] = nd ; }
   return ;
} 

void add_node_to_species_tree ( int * list , int lisz )
{
    int trusz = 0 , lastis ;
    int x , a , b , c ; 
    for ( a = 0 ; a < species_tree [ treeroot] ; ++ a ) treelist [ a ] = acurl [ a ] = 0 ;
    /** all sizes... */ 
    acurl [ treeroot ] = numterminals ; 
    for ( a = 0 ; a < species_tree [ treeroot] ; ++ a )
        for ( b = species_tree [ a ] ; b != treeroot ; b = species_tree [ b ] )
              acurl [ b ] ++  ;
    /*** find minimum common node ******/
    for ( x = 0 ; x < lisz ; ++ x ) {
        a = list [ x ] ; 
        if ( treelist [ a ] ) continue ;
        ++ trusz ;
        treelist [ a ] ++ ;
        b = lastis = a ;  
        while ( b != treeroot ) 
            ++ treelist [ b = species_tree [ b ] ] ; }
    a = species_tree [ lastis ] ;
    while ( treelist [ a ] < trusz ) a = species_tree [ a ] ; 
    /**  Sanity check *****/
    // here, should add some check to avoid adding contradictory groups (e.g. 2-3-4 to a tree with 1-2-3)
    if ( trusz == acurl [ a ] )
        ermsg ( "Cannot define duplicate groups!" ) ;
    /** Create new node *****/
    for ( b = 0 ; b < species_tree [ treeroot] ; ++ b ) treelist [ b ] = 0 ;
    for ( b = 0 ; b < lisz ; ++ b ) {
        c = list [ b ] ; 
        while ( species_tree [ c ] != a && !treelist [ c ] ) c = species_tree [ c ] ;
        if ( treelist [ c ] ) continue ; 
        treelist [ c ] = 1 ;
        species_tree [ c ] = species_tree [ treeroot ] ; }
    species_tree [ species_tree [ treeroot ] ] = a ; 
    species_tree [ treeroot ] ++ ; 
    /*** Make final tree *****/
    mksis ( species_tree ) ;
    return ; 

}

int mkoptlist ( int *list, int *an )  
{ int * x = list ; 
  int * y = list + 1;
  int * last , nd ; 
  int a, i , nodz = 2*numterminals - 1 ;
  int nt = numterminals ; 
  last = list ; 
  for ( a = nodz ; a -- ; ) {
      treesis [ a ] = treefirs [ a ] = list [ a ] = -1 ;
      nodfork [ a ] = 0 ; } 
  for ( a = nt ; a -- ; ) {
      i = an [ nd = a ] ; 
      if ( !i ) continue ; 
      while ( i != nt && treefirs [ i ] < 0 ) {
                    last [ i ] = treefirs [ i ] = nd ;
                    ++ nodfork [ i ] ; 
                    nd = i ;
                    i = an [ i ] ; }
      ++ nodfork [ i ] ;
      if ( treefirs [ i ] < 0 ) treefirs [ i ] = nd ; // i.e. i == nt
      if ( last [ i ] >= 0 ) treesis [ last [ i ] ] = nd ;
      last [ i ] = nd ; }
   * x = nt ; 
   while ( x < y ) {
       a = treefirs [ * x ++ ] ;
       while ( a >= 0 ) { if ( a >= nt ) * y ++ = a ; a = treesis [ a ] ; }}
   return ( x - list ) ;
} 
    
void get_species_tree ( int theospp , int chkstring ) 
{
    int x = 0 , a, b , c ;
    int32 bizin , bizout ;
    int cellin , cellout ;
    int * afare , * fatto ;
    int tot = 0 ;
    int addtosp = 0 ; 

int addednod ; 
char * cp ; 
    
    numterminals = spp ;
    if ( chkstring ) {
       fscanf ( infile , " %s", &str ) ; 
       if ( feof ( infile ) ) return ; 
       if ( strcmp ( str , "groups" ) ) return ; }
    memerr ( species_tree = ( int * ) malloc ( spp * 2 * sizeof ( int ) ) ) ;
    memerr ( treefirs = ( int * ) malloc ( spp * 2 * sizeof ( int ) ) ) ;
    memerr ( treesis = ( int * ) malloc ( spp * 2 * sizeof ( int ) ) ) ;
    memerr ( nodfork = ( int * ) malloc ( spp * 2 * sizeof ( int ) ) ) ;
    memerr ( innerlist = ( int * ) malloc ( spp * 2 * sizeof ( int ) ) ) ;
    memerr ( treelist = ( int * ) malloc ( spp * 2 * sizeof ( int ) ) ) ;
    memerr ( acurl = ( int * ) malloc ( spp * 2 * sizeof ( int ) ) ) ;
    treeroot = spp ; 
    species_tree [ treeroot ] = spp + 1 ; 
    for ( a = spp ; a -- ; ) {
         species_tree [ a ] = treeroot ;
         treesis [ a ] = a + 1 ; }
    treefirs [ treeroot ] = 0 ;
    treesis [ spp - 1 ] = -1 ;
    while ( x != ';' && !feof ( infile ) ) {
         x = getc ( infile ) ;
         if ( isspace ( x ) ) continue ;
         if ( x == '*' ) 
             if ( ! fscanf ( infile , " %i" , &addtosp ) ) ermsg ( "For group definition, symbol \"*\" must\nbe followed by previous number of spp" ) ; 
         if ( x == 123 /** open brace ***/ ) {
             ++ tot ;
             if ( ( spp + tot > theospp  ) ) ermsg ( "Cannot define so many groups --increase spp" ) ;
             if ( tot == spp - 1 ) ermsg ( "Cannot define so many groups" ) ; 
             a = 0 ;
             while ( x != 125  /** closing brace ***/  ) {
                 x = getc ( infile ) ;
                 if ( isspace ( x ) ) continue ;
                 ungetc ( x , infile ) ;
                 if ( isdigit ( x ) ) {
                     fscanf ( infile , " %i" , &b ) ;
                     b += addtosp ; 
                     innerlist [ a ++ ] = b ; }}
             if ( a > numterminals ) ermsg ( "List of terminals in \"groups\" too long" ) ;
             if ( a < 2 ) ermsg ( "Groups must include 2 or more taxa" ) ;
             addednod = species_tree [ treeroot ] ; 
             add_node_to_species_tree ( innerlist , a ) ;

x = getc ( infile ) ;
while ( isspace ( x ) || x == '}' ) x = getc ( infile ) ; 
if ( x != '[' ) {
    ungetc ( x , infile ) ;
    sprintf ( ( spname [ addednod ] = mymem ( 32 ) ) , "GRP-%i" ,  addednod-treeroot-1) ; 
    continue ; }
cp = junkstr ;
while ( isspace ( x = getc ( infile ) ) ) ;
while ( x != ']' ) {
    * cp ++ = x ;
    x = getc ( infile ) ; }
* cp = '\0' ;  
strcpy ( ( spname [ addednod ] = mymem ( strlen ( junkstr ) + 11 ) ) , junkstr ) ; 

             }}
     number_of_groups = mkoptlist ( treelist , species_tree ) ;
     return ; 
}

void add_species_groups ( void )
{
    int32 bin , bout ;
    int cin , cout , m , n , a , b , j , k ;
    int * fato , * afare ;
    MinMaxtyp * mmpt ; 
    if ( species_tree == NULL ) return ;
    spp = numterminals ;
    mmpt = spminmax + numterminals ; 
    for ( n = numterminals + 1 ; n < species_tree [ treeroot ] ; ++ n , ++ mmpt ) {
        bout = 1 << ( spp % 32 ) ;
        cout = spp / 32 ;
        mmpt -> minc = mmpt -> minr = 32767 ; 
        mmpt -> maxc = mmpt -> maxr = 0 ; 
        for ( a = 0 ; a < rows ; ++ a )
            for ( b = 0 ; b < cols ; ++ b ) {
                matrix [ a ] [ b ] [ cout ] &= ~bout ; 
                assmatrix [ a ] [ b ] [ cout ] &= ~bout ; }
        numentries [ spp ] = numassentries [ spp ] = 0 ; 
        * ( fato = afare = innerlist ) = n ;
        ++ afare ; 
        while ( fato < afare ) {
            j = * fato ++ ;
            if ( j >= numterminals ) 
                for ( k = treefirs [ j ] ; k >= 0 ; k = treesis [ k ] ) * afare ++ = k ;
            else {
                bin = 1 << ( j % 32 ) ;
                cin = j / 32 ;
                if ( mmpt -> minc > spminmax[j].minc ) mmpt -> minc = spminmax[j].minc ; 
                if ( mmpt -> minr > spminmax[j].minr ) mmpt -> minr = spminmax[j].minr ; 
                if ( mmpt -> maxc < spminmax[j].maxc ) mmpt -> maxc = spminmax[j].maxc ; 
                if ( mmpt -> maxr < spminmax[j].maxr ) mmpt -> maxr = spminmax[j].maxr ; 
                for ( a = 0 ; a < rows ; ++ a )
                   for ( b = 0 ; b < cols ; ++ b ) {
                       if ( ( matrix [ a ] [ b ] [ cin ] & bin ) ) {
                           if ( ! ( matrix [ a ] [ b ] [ cout ] & bout ) ) ++ numentries [ spp ] ;
                           matrix [ a ] [ b ] [ cout ] |= bout ; }
                       if ( ( assmatrix [ a ] [ b ] [ cin ] & bin ) ) {
                           if ( ! ( assmatrix [ a ] [ b ] [ cout ] & bout ) ) ++ numassentries [ spp ] ;
                           assmatrix [ a ] [ b ] [ cout ] |= bout ; }}}}
        ++ spp ; }
    return ; 
}

void add_group_coordinates ( void )
{
    int32 bin , bout ;
    int cin , cout , m , n , a , b , j , k ;
    int * fato , * afare , tot ;
    if ( species_tree == NULL ) return ; 
    spp = numterminals ; 
    for ( n = numterminals + 1 ; n < species_tree [ treeroot ] ; ++ n ) {
        xymatrix[ spp ]. numrecs = 0 ;
        xymatrix[ spp ]. defd = 1 ; 
        * ( fato = afare = innerlist ) = n ;
        ++ afare ;
        tot = 0 ; 
        while ( fato < afare ) {
            j = * fato ++ ;
            if ( j >= numterminals ) 
                for ( k = treefirs [ j ] ; k >= 0 ; k = treesis [ k ] ) * afare ++ = k ;
            else 
                tot += xymatrix[ j ].numrecs ; }
        xymatrix [ spp ].x = ( float * ) mymem ( ( tot + 1 ) * sizeof ( float ) ) ; 
        xymatrix [ spp ].y = ( float * ) mymem ( ( tot + 1 ) * sizeof ( float ) ) ; 
        * ( fato = afare = innerlist ) = n ;
        ++ afare ; 
        while ( fato < afare ) {
            j = * fato ++ ;
            if ( j >= numterminals ) 
                for ( k = treefirs [ j ] ; k >= 0 ; k = treesis [ k ] ) * afare ++ = k ;
            else {
                b = xymatrix[ spp ].numrecs ; 
                for ( a = 0 ; a < xymatrix[j].numrecs ; ++ a , ++ b ) {
                      xymatrix[ spp ] . x [ b ] = xymatrix[ j ] . x [ a ] ; 
                      xymatrix[ spp ] . y [ b ] = xymatrix[ j ] . y [ a ] ; }
                xymatrix [ spp ]. numrecs = b ; }}
        if ( spname != NULL ) {
           if ( spname [ n ] == NULL ) 
                sprintf ( junkstr , "GRP-%i" , n - numterminals - 1 ) ; 
           else {
                sprintf ( junkstr , "GRP-%i" , n - numterminals - 1 ) ;
                if ( strcmp ( junkstr , spname[n] ) ) 
                     sprintf ( junkstr + strlen ( junkstr ) , "-%s" , spname [ n ] ) ; }
           if ( spname [ spp ] != NULL ) free ( spname [ spp ] ) ; 
           spname [ spp ] = mymem ( strlen ( junkstr ) + 1 ) ;
           strcpy ( spname[ spp ] , junkstr ) ; }
        ++ spp ; }
    for ( a = numterminals ; a < spp ; ++ a )    //  Do not plot higher groups (a waste of time!) 
        spingrid[a/32] &= ~ ( 1 << ( a % 32 ) ) ; 

    return ; 
}

void shift_group_names ( void )
{
    int32 bin , bout ;
    int cin , cout , m , n , a , b , j , k ;
    int * fato , * afare , tot ;
    if ( species_tree == NULL ) return ; 
    spp = numterminals ; 
    for ( n = numterminals + 1 ; n < species_tree [ treeroot ] ; ++ n ) {
        * ( fato = afare = innerlist ) = n ;
        ++ afare ;
        if ( spname != NULL ) {
           if ( spname [ n ] == NULL ) 
                sprintf ( junkstr , "GRP-%i" , n - numterminals - 1 ) ; 
           else {
                sprintf ( junkstr , "GRP-%i-" , n - numterminals - 1 ) ;
                sprintf ( junkstr + strlen ( junkstr ) , "%s" , spname [ n ] ) ; }
           if ( spname [ spp ] != NULL ) free ( spname [ spp ] ) ; 
           spname [ spp ] = mymem ( strlen ( junkstr ) + 1 ) ;
           strcpy ( spname[ spp ] , junkstr ) ; }
        ++ spp ; }
    for ( a = numterminals ; a < spp ; ++ a )    //  Do not plot higher groups (a waste of time!) 
        spingrid[a/32] &= ~ ( 1 << ( a % 32 ) ) ; 
    return ; 
}

void initialize_species_weights ( void )
{
    int a ;
    double d , e ;
    int minpts = 1000000000 ;
    double minival , factor , obsint , wantint , bottom , dminpts ; 
    for ( a = 0 ; a < spp ; ++ a ) 
        if ( xymatrix[a].numrecs < minpts && xymatrix[a].numrecs )
               minpts = xymatrix[a].numrecs ; 
    dminpts = ( double ) minpts ; 
    minival = ( dminpts - 1 ) / ( 0.5 + dminpts - 1 ) ;
    bottom = weight_min ; 
    obsint = 1 - minival ;
    wantint = 1 - bottom ;
    factor = wantint / obsint ; 
    for ( a = 0 ; a < spp ; ++ a ) {
        if ( xymatrix[a].numrecs == 0 ) { species_weight [ a ] = 0 ; continue ; }
        d = ( double ) xymatrix[a].numrecs ; 
        e = ( ( ( ( d - 1 ) / ( 0.5 + d - 1 ) ) - minival ) * factor ) + bottom ;
        sprintf ( junkstr , "%.20f" , e ) ; 
        species_weight [ a ] = atof ( junkstr ) ; }
    return ; 
}

void save_shrunk_data ( int rowfuse , int colfuse ) 
{  int a , b , c , mc , numar ;
   int lim ;
   int * afare , * fato , n , m , j , k ;
   int nurows , nucols ; 
   int32 mb ;
   int trunspp , aa , bb , printit ;
   int maxval ;
   int apass , bpass ; 
   if ( ysign  > 0 ) fprintf ( outspace , "ynegative\n" ) ;
   if ( xsign < 0 ) fprintf ( outspace , "xnegative\n" ) ;
   if ( dolatlong == 0 ) fprintf ( outspace , "longlat\n" ) ;
   if ( grid_startx < 10e200 ) {
     if ( !dolatlong ) 
        fprintf ( outspace , "gridx %.8f %.8f\ngridy %.8f %.8f\n" ,
                 grid_startx , grid_width * rowfuse , grid_starty * ysign , grid_height * colfuse ) ;
     else 
        fprintf ( outspace , "gridx %.8f %.8f\ngridy %.8f %.8f\n" ,
                 grid_startx , grid_width * colfuse , grid_starty * ysign , grid_height * rowfuse ) ; }
   trunspp = 0 ;
   for ( a = 0 ; a < spp ; ++ a )
       if ( ( spact[a/32] & ( 1 << ( a % 32 ) ) ) ) ++ trunspp ;
   /*** Calculate new number of rows/cols ********/
   nucols = cols / colfuse ;
   if ( ( cols % colfuse ) ) ++ nucols ; 
   nurows = rows / rowfuse ;
   if ( ( rows % rowfuse ) ) ++ nurows ; 
   if ( species_tree == NULL )     
       fprintf(outspace , "rows %i\ncols %i\nspp %i\ndata" , nurows , nucols , trunspp ) ;
   else {
       if ( trunspp != spp ) ermsg ( "OOOPS!!!... when using higher groups, shouldn't deactivate species!!!" ) ;
       fprintf(outspace , "rows %i\ncols %i\nspp %i\ndata" , nurows , nucols , spp ) ; }
   /*** Save, fusing on the fly *****/
   for ( a = 0 ; a < nurows ; a ++ ) { 
      for ( b = 0 ; b < nucols ; b ++ ) {
         /** Is any of the cells defined?? *********/
         printit = 0 ;
         for ( aa = a * rowfuse , apass = 0 ; apass < rowfuse && !printit && aa < rows ; ++ aa , ++ apass )
             for ( bb = b * colfuse , bpass = 0 ; bpass < colfuse && !printit && bb < cols ; ++ bb , ++ bpass )
                  if ( isdefd [ aa ] [ bb ] ) printit = 1 ; 
         if ( !printit ) continue ;
         /*** Now, fuse ... ********/
         fprintf(outspace,"\nA%i-%i\n" , a , b ) ;
         lim = spp ;
         if ( species_tree != NULL ) lim = numterminals ; 
         for ( c = 0 ; c < lim ; ++ c ) {
            maxval = 0 ; 
            mb = 1 << ( c % 32 ) ; 
            mc = c / 32 ;
            if ( !( spact[mc] & mb ) ) continue ; 
            for ( aa = a * rowfuse , apass = 0 ; apass < rowfuse && maxval < 2 && aa < rows ; ++ aa , ++ apass )
                for ( bb = b * colfuse , bpass = 0 ; bpass < colfuse && maxval < 2 && bb < cols ; ++ bb , ++ bpass ) {
                     if ( ( matrix [ aa ] [ bb ] [ mc ] & mb ) ) maxval = 2 ; 
                     else
                        if ( !maxval ) 
                          if ( ( assmatrix [ aa ] [ bb ] [ mc ] & mb ) ) maxval = 1 ; }
            if ( !maxval ) putc ( '0' , outspace ) ;
            else if ( maxval == 1 ) putc ( '2' , outspace ) ;
            else putc ( '1' , outspace ) ; }}}
   fprintf(outspace , "\n;\n" ) ;
   if ( species_tree != NULL ) {
       fprintf ( outspace , "groups\n" ) ;
       for ( m = numterminals+1 ; m < species_tree [ treeroot ] ; ++ m ) {
           fprintf ( outspace , "{" ) ;
           * ( afare = fato = innerlist ) = m ;
           ++ afare ; 
           while ( fato < afare ) {
               j = * fato ++ ;
               if ( j >= numterminals )
                   for ( k = treefirs [ j ] ; k >= 0 ; k = treesis [ k ] ) * afare ++ = k ;
               else fprintf ( outspace , "%i " , j ) ; }
           fprintf ( outspace , "}\n" ) ; }
      fprintf ( outspace , ";\n" ) ; }
   if ( weight_species ) {
       fprintf ( outspace , "spwts\n" ) ;
       for ( j = 0 ; j < spp ; ++ j ) {
           if ( !( spact [ j/32] & ( 1 << ( j % 32 ) ) ) ) continue ;
           fprintf ( outspace , "   %.20f\n" , species_weight[ j ] ) ; }
       fprintf ( outspace , ";\n" ) ; }
   showcurset () ;
   sprintf ( junkstr , "Saved data to file (now with %i rows, %i cols)" , nurows , nucols ) ; 
   captf( junkstr ) ; 
   return ; 
} 

extern int32 * given_spp ;

void seek_sets_for_given_spp ( int is_text )
{
    int match , bestmatch = 1 , nummatches = 0 ;
    int a , b , i , mc ;
    int total = 0 ; 
    int32 both ; 
    int32 mb ;
    Artyp * arp , * darp ;
    int32 * dali ;
    for ( i = 0 ; i < spcells ; ++ i ) total += onbits ( given_spp [ i ] ) ; 
    for ( a = 0 , arp = rec ; a < numrecs ; ++ a , ++ arp ) arp -> mark = 0 ; 
    for ( a = 0 , arp = rec ; a < numrecs ; ++ a , ++ arp ) {
        match = 0 ;
        dali = arp -> splist ; 
        for ( i = 0 ; i < spcells ; ++ i ) {
            both = dali [ i ] & given_spp [ i ] ;
            match += onbits ( both ) ; }
        if ( match > bestmatch )  
             bestmatch = match ; 
         arp -> mark = match ; }
    if ( !is_text ) {
         nummatches = 0 ; 
         for ( a = 0 , arp = rec ; a < numrecs ; ++ a , ++ arp ) 
             if ( ( bestmatch - arp -> mark ) <= 3 && arp -> mark ) {
                arp -> mark = 1 ;
                ++ nummatches ; } 
             else arp -> mark = 0 ; 
         captf ( "Marked %i areas (with up to %i of %i spp.)" , nummatches , bestmatch , total ) ; }
    else {
         nummatches = 0 ; 
         for ( a = 0 , arp = rec ; a < numrecs ; ++ a , ++ arp ) 
             if ( ( bestmatch - arp -> mark ) <= 3 && arp -> mark ) 
                ++ nummatches ;  
         fprintf ( outspace , "\n" ) ; 
         fprintf ( outspace , "SETS WITH UP TO %i (OF %i SPECIES SELECTED)\n"  , nummatches , total ) ; 
         for ( a = 0 , arp = rec ; a < numrecs ; ++ a , ++ arp ) 
             if ( ( bestmatch - arp -> mark ) <= 3 && arp -> mark ) {
                 fprintf ( outspace , "Area %i (%i spp.);\n" , a , arp -> mark ) ;
                 arp -> mark = 1 ; 
                 dali = arp -> splist ; 
                 for ( i = 0 ; i < spp ; ++ i ) {
                     mc = i / 32 ;
                     mb = 1 << ( i % 32 ) ;
                     both = dali [ mc ] & given_spp [ mc ] & mb ;
                     if ( both ) fprintf ( outspace , "    %i %s\n" , i , spname [ i ] ) ; }}
             else arp -> mark = 0 ; 
         fprintf ( outspace , "\n" ) ; }
    return ;
}

void speak_all_overlaps ( int for_consensus )
{ static Artyp * now ;
  int a , b , i , j ;
  int anonb , bnona , banda ;
  unsigned long int * apt , * bpt ; 
  if ( for_consensus ) {
         if ( 10000 - numrecs < numcons ) {
             errmsg ( "Sorry, not enough memory for requested calculation" , Null ) ;
             return ; }
         put_consensus_in_duwc_buffer () ;
         fprintf ( outspace , "\n------------------------------------------------\nPARTIAL OVERLAPS BETWEEN CONSENSUS AREAS\n------------------------------------------------\n" ) ; 
         for ( now = cons_duwc_start , i = 0 ; i < numcons ; ++ i , ++ now ) {
             anonb = bnona = banda = 0 ;
             apt = now -> lst ;
             for ( b = arcells ; b -- ; ) {
                  anonb += onbits ( * apt ) ;
                  ++ apt ; }
             fprintf ( outspace , "\nConsensus Area %i (%i cells):\n   " , i , anonb ) ; 
             recptr = cons_duwc_start - 1 ;
             j = 0 ; 
             for ( a = 0 ; a < numcons ; ++ a ) { 
               ++ recptr ; 
               if ( recptr == now ) continue ; 
               if ( oneintwo ( now , recptr ) == 2 ) {
                   anonb = bnona = banda = 0 ;
                   apt = recptr -> lst ;
                   bpt = now -> lst ; 
                   for ( b = arcells ; b -- ; ) {
                       anonb += onbits ( * apt & ~ * bpt ) ;
                       bnona += onbits ( * bpt & ~ * apt ) ;
                       banda += onbits ( * apt & * bpt ) ;
                       ++ apt ;
                       ++ bpt ; }
                   if ( j ++ ) fprintf ( outspace , ", " ) ; 
                   fprintf ( outspace , "%i (%i/%i)" , a , banda , banda + anonb ) ; }}
             if ( !j ) fprintf ( outspace , "none" ) ;
             fprintf ( outspace , "\n" ) ; }}
    else {
         fprintf ( outspace , "\n------------------------------------------------\nPARTIAL OVERLAPS BETWEEN AREAS\n------------------------------------------------\n" ) ; 
         for ( now = rec , i = 0 ; i < numrecs ; ++ i , ++ now ) {
             anonb = bnona = banda = 0 ;
             apt = now -> lst ;
             for ( b = arcells ; b -- ; ) {
                  anonb += onbits ( * apt ) ;
                  ++ apt ; }
             fprintf ( outspace , "\nArea %i (%i cells):\n   " , i , anonb ) ; 
             recptr = rec - 1 ;
             j = 0 ; 
             for ( a = 0 ; a < numrecs ; ++ a ) { 
               ++ recptr ; 
               if ( recptr == now ) continue ; 
               if ( oneintwo ( now , recptr ) == 2 ) {
                   anonb = bnona = banda = 0 ;
                   apt = recptr -> lst ;
                   bpt = now -> lst ; 
                   for ( b = arcells ; b -- ; ) {
                       anonb += onbits ( * apt & ~ * bpt ) ;
                       bnona += onbits ( * bpt & ~ * apt ) ;
                       banda += onbits ( * apt & * bpt ) ;
                       ++ apt ;
                       ++ bpt ; }
                   if ( j ++ ) fprintf ( outspace , ", " ) ;
                   fprintf ( outspace , "%i (%i/%i)" , a , banda , banda + anonb ) ; }}
             if ( !j ) fprintf ( outspace , "none" ) ;
             fprintf ( outspace , "\n" ) ; }}
   return ;
}

typedef struct 
      { int up , diag , lef ; 
        int min ; } Stringcomptyp ; 
Stringcomptyp ** cellcost ;
double name_match_limit = 0.9 ;
int * spbecs ; 

void alloc_needwunsch_mem ( int wid , int hei )
{
   int i , to ;
   to = wid + 1 ;
   if ( to < hei + 1 ) to = hei + 1 ; 
   cellcost = mymem ( to * sizeof ( Stringcomptyp * ) ) ;
   for ( i = 0 ; i < to ; ++ i )
      cellcost[i] = mymem ( to * sizeof ( Stringcomptyp ) ) ;
}

int numcalls = 0 ; 

double needwunsch_cmp ( char * ap , char * bp , char * endofa , char * endofb , double limit ) 
{
    int wid , hei , i , j , dacos , denom ; 
    char * app , * bpp ; 
    char * abecs , * bbecs , * anp , * bnp ;
    double val ;
    static int mademem = 0 ;
    static long int killat , bestofrow ; 
    int HIGH = 10000000 ;
    int gapcost , gapextcost , suscost ; 
    if ( endofa == NULL ) wid = strlen ( ap ) ;
    else wid = endofa - ap ;
    if ( wid > 100 ) wid = 100 ; 
    if ( endofb == NULL ) hei = strlen ( bp ) ;
    else hei = endofb - bp ;
    if ( hei > 100 ) hei = 100 ; 
    gapcost = gapextcost = suscost = 1 ;

++ numcalls ; 

    if ( wid == 1 && hei == 1 && tolower ( ap[0] ) != tolower ( bp[0] ) ) return 0 ;
    denom = wid ;
    if ( wid > hei ) denom = hei ; 
    if ( !mademem ) {
        ++ wid ;
        ++ hei ;
        alloc_needwunsch_mem ( 101 , 101 ) ; 
        app = mymem ( 102 * sizeof ( char ) ) ; 
        bpp = mymem ( 102 * sizeof ( char ) ) ;
        i = ap[99] ; ap[99]='\0' ; strcpy ( ( app + 1 ) , ap ) ; ap[99]=i ; 
        i = bp[99] ; bp[99]='\0' ; strcpy ( ( bpp + 1 ) , bp ) ; bp[99]=i ; 
        * ( ap = app ) = 1 ;
        * ( bp = bpp ) = 1 ;
        mademem = 1 ; }
    cellcost[0][0].min = cellcost[0][0].diag = 0 ;
    cellcost[0][0].up = cellcost[0][0].lef = HIGH ; 
    if ( tolower ( ap[0] ) != tolower ( bp[0] ) ) 
       cellcost[0][0].min = cellcost[0][0].diag = 1 ;
    bpp = bp ; 
    for ( j = 0 ; j < hei ; ++ j ) {
       bestofrow = 100000000 ;
       app = ap ; 
       for ( i = 0 ; i < wid ; ++ i ) {
          if ( !i && !j ) {
             bestofrow = 0 ;
             if ( tolower ( ap[0] ) != tolower ( bp[0] ) ) bestofrow = 1 ; 
             ++ app ; 
             continue ; }
          dacos = 0 ; 
          if ( tolower ( * app ) != tolower ( * bpp ) ) dacos = suscost ; 
          if ( j ) {
            if ( cellcost[i][j-1].min == cellcost[i][j-1].up )  
               cellcost[i][j].up = cellcost[i][j-1].min + gapextcost ; 
            else 
               cellcost[i][j].up = cellcost[i][j-1].min + gapcost ; }
          else cellcost[i][j].up = cellcost[i][j].diag = HIGH ; 
          if ( i ) {
            if ( cellcost[i-1][j].min == cellcost[i-1][j].lef ) 
               cellcost[i][j].lef = cellcost[i-1][j].min + gapextcost ; 
            else 
               cellcost[i][j].lef = cellcost[i-1][j].min + gapcost ; }
          else cellcost[i][j].lef = cellcost[i][j].diag = HIGH ; 
          if ( i && j ) cellcost[i][j].diag = cellcost[i-1][j-1].min + dacos ; 
          dacos = cellcost[i][j].diag ; 
          if ( dacos > cellcost[i][j].up ) dacos = cellcost[i][j].up ; 
          if ( dacos > cellcost[i][j].lef ) dacos = cellcost[i][j].lef ; 
          cellcost[i][j].min = dacos ;
          if ( dacos < bestofrow ) bestofrow = dacos ; 
          ++ app ; }
       if ( limit > 0  ) {
          val = ( double ) bestofrow / ( double ) denom ;
          val = 1 - val ;
          if ( val < name_match_limit ) return 0 ; }
       ++ bpp ; }
    dacos = cellcost[wid-1][hei-1].min ;
    if ( dacos == 0 ) return 1 ; 
    val = ( double ) dacos / ( double ) denom ;
    val = 1 - val ;
    return val ; 
}

void makesp ( int what , int into )
{
    spbecs [ what ] = into ;
    return ;
}

char * setstring ( char * to , char * from )
{
    int i ;
    char * cp = from , * go = to ;
    while ( isspace ( * cp ) && * cp ) ++ cp ;
    if ( ! * cp ) { * to = '\0' ; return cp ; }
    while ( !isspace ( * cp ) && * cp && go - to < 100 && * cp != '_' ) * go ++ = * cp ++ ;
    * go = '\0' ;
    return cp ; 
}

char kuka[102] , kukb[102] ; 
int is_superset ( int i , int j )
{
    int k , n ;
    char * ap , * bp ;
    int diff = 0 ;
    char * sa , * sb ;
    double val ; 
    ap = spname [ i ] ;
    bp = spname [ j ] ;
    sa = kuka ;
    sb = kukb ; 
    while ( !diff ) {
         ap = setstring ( sa , ap ) ;
         bp = setstring ( sb , bp ) ;
         if ( ! * sa || ! * sb ) {
             if ( * sa && ! * sb ) return j ;
             if ( ! * sa && * sb ) return i ;
             return -1 ; }
         val = needwunsch_cmp ( sa , sb , NULL , NULL , 0.80 ) ;
         if ( val < 0.80 ) diff = 1 ; }
     return -1 ;         
}

void save_only_coords ( int type )
{
    int i , j , k , n , totpoints , p , q ;
    int chktaxa = 0 , choice , somesyn ;
    int remvd = 0 ;
    int nowsv = numcoordstofile , skipit ;
    double val ;
    char * endis ;
    unsigned long int mb ;
    int mc ;
    int * sptable ; 

    if ( type == 1 ) chktaxa = 1 ; 

    sptable = ( int * ) dass ; 
    spbecs = ( int * ) dout ;
    for ( i = 0 ; i < numterminals ; ++ i ) spbecs [ i ] = i ; 

    if ( chktaxa ) {
        fprintf ( outspace ,"--------------------\nSYNONYMIES:\n" ) ; 
        for ( i = 0 ; i < numterminals ; ++ i ) {
           if ( spbecs[ i ] != i ) continue ; 
           if ( xymatrix[i].numrecs == 0 ) {
               spbecs[ i ] = -1 ; 
               continue ; }
           endis = spname[ i ] + strlen ( spname [ i ] ) ;
           somesyn = 0 ; 
           for ( j = i ; ++ j < numterminals ; ) {
               if ( spbecs[j] != j ) continue ;  
               if ( xymatrix[j].numrecs == 0 ) {
                   spbecs[ j ] = -1 ; 
                   continue ; }
               choice = IDNO ;
               val = needwunsch_cmp ( spname[i] , spname[j] , endis , NULL , name_match_limit ) ;
               if ( val >= name_match_limit ) {
                   if ( val < 0.94 ) { 
                       sprintf ( junkstr , "Taxa:\n\n    %s (%i)\n\nand\n\n    %s (%i)\n\nare very similar.\n\nMake them identical?\n" , spname[i] , i , spname[j] , j ) ;
                       choice = MessageBox ( hwnd , junkstr , "Warning" , MB_YESNOCANCEL ) ; }
                   else choice = IDYES ; 
                   if ( choice == IDCANCEL ) return ;  
                   if ( choice == IDYES ) {
                        if ( !somesyn ) fprintf ( outspace , "%s\n" , spname[i] ) ;
                        somesyn = 1 ;
                        fprintf ( outspace , "    = %s\n" , spname[j] ) ;    
                        makesp( j , i ) ; }
                   else {
                        if ( !somesyn ) fprintf ( outspace , "%s\n" , spname[i] ) ;
                        fprintf ( outspace , "    NOT %s\n" , spname[j] ) ; }}}}

        for ( i = 0 ; i < numterminals ; ++ i ) {
           if ( spbecs[ i ] != i ) continue ; 
           for ( j = i ; ++ j < numterminals ; ) {
               if ( spbecs[j] != j ) continue ;  
               k = is_superset ( j , i ) ;
               if ( k >= 0 ) {
                  if ( i == k ) n = j ;
                  else n = i ; 
                  endis = junkstr + sprintf ( junkstr , "\nTaxon:\n\n    %s (%i, %i pts.)\n\nseems a super-set of:\n\n    %s (%i, %i pts.)" , spname[k] , k , xymatrix[k].numrecs , spname[n] , n , xymatrix[n].numrecs ) ;
                  for ( p = i ; ++ p < numterminals ; ++ p ) {
                       if ( spbecs[p] != p ) continue ;
                       if ( p == j ) continue ; 
                       q = is_superset ( k , p ) ;
                       if ( q == k ) 
                          endis += sprintf ( endis , "\n\n    %s (%i, %i pts.)" , spname[p] , p , xymatrix[p].numrecs ) ; }
                  fprintf ( outspace , "%s" , junkstr ) ; 
                  strcat ( junkstr , "\n\nEliminate it?\n" ) ; 
                  choice = MessageBox ( hwnd , junkstr , "Warning" , MB_YESNOCANCEL ) ;
                  if ( choice == IDCANCEL ) return ;
                  if ( choice == IDYES ) {
                      fprintf ( outspace , "\n\n --- REMOVED %s!!\n" , spname[k]) ; 
                      spbecs[ k ] = -1 ;
                      if ( k == i ) break ; }
                  else { fprintf ( outspace , "\n\n --- retained\n" ) ; break ; }}}}        
       }

      for ( i = 0 ; i < numterminals ; ++ i ) {
           if ( spbecs[ i ] != i ) continue ; 
           if ( xymatrix[i].numrecs == 0 ) {
               spbecs[ i ] = -1 ; 
               continue ; }
           if ( type == 2 ) {
              mc = i / 32 ;
              mb = 1 << ( i % 32 ) ;
              if ( ! ( spact[ mc ] & mb ) ) continue ; }  
           fprintf ( outspace , "sp %i " , nowsv ++ ) ;
           if ( ind_fills != NULL )
              if ( ind_fills[i].fillx >= 0 )  
                  fprintf ( outspace , "( %f %f %f %f ) " , ind_fills[i].fillx , ind_fills[i].filly , ind_fills[i].assx , ind_fills[i].assy ) ; 
           fprintf ( outspace , "[ %s ]\n" , spname[ i ] ) ; 
           for ( k = 0 ; k < xymatrix[i].numrecs ; ++ k )
               fprintf ( outspace , " %f %f\n" , -xymatrix[i].y[k] , xymatrix[i].x[k] ) ;
           for ( j = i ; ++ j < numterminals ; ++ j )  
               if ( spbecs[ j ] == i ) {
                  for ( k = 0 ; k < xymatrix[j].numrecs ; ++ k )
                     fprintf ( outspace , " %f %f\n" , -xymatrix[j].y[k] , xymatrix[j].x[k] ) ; }} 
    numcoordstofile += nowsv ;

    if ( species_tree != NULL ) {
        k = 0 ;
        for ( i = 0 ; i < numterminals ; ++ i ) {
            if ( spbecs [ i ] != i ) sptable [ i ] = -1 ;
            else sptable [ i ] = k ++ ; }
        if ( have_groups_after_compression ( sptable , 0 ) ) {
           fprintf ( outspace , "\ngroups\n" ) ; 
           have_groups_after_compression ( sptable , 1 ) ; } 
       } 
    return ;
}

int have_groups_after_compression ( int * table , int save )
{
    int ngroups = 0 ;
    int a , b , c , this , some ;
    char * cp ; 
    for ( a = numterminals + 1 ; a < species_tree [ treeroot ] ; ++ a ) {
        this = 0 ;
        for ( b = 0 ; b < numterminals ; ++ b ) {
          if ( table [ b ] < 0 ) continue ; 
          for ( c = species_tree [ b ] ; c != treeroot && c != a ; c = species_tree [ c ] ) ;
          if ( c == a ) ++ this ; }
        if ( this < 2 ) continue ; 
        ++ ngroups ;
        if ( !save ) {
            if ( ngroups ) return 1 ; }
        else {
          some = 0 ;   
          for ( b = 0 ; b < numterminals ; ++ b ) {
             if ( table [ b ] < 0 ) continue ; 
             for ( c = species_tree [ b ] ; c != treeroot && c != a ; c = species_tree [ c ] ) ;
             if ( c == a ) {
                 if ( !some ) fprintf ( outspace , "{ " ) ;
                 some = 1 ; 
                 fprintf ( outspace , "%i " , table[ b ] ) ; }}
          fprintf ( outspace , " } " ) ;
          if ( spname != NULL ) 
              if ( spname [ a - 1 ] != NULL ) {
                  sprintf ( junkstr , "GRP-%i" , a - numterminals - 1 ) ;
                  if ( strcmp ( spname[a-1] , junkstr ) ) { 
                      cp = spname [ a - 1 ] + 5 ;
                      while ( * cp != '-' ) ++ cp ;
                      ++ cp ; 
                      fprintf ( outspace , " [ %s ]" , cp ) ; }}
          fprintf ( outspace , "\n" ) ; }}
    return 0 ; 
} 

int framinc , framaxc , framinr , framaxr ;
int redcols , redrows ;
int redarcells ; 

void save_for_framed_search ( void )
{
   int a , b , c , mc , numar , ax , ay ;
   int lim , atcol , atrow ;
   int atr , atc ; 
   int * afare , * fato , n , m , j , k ; 
   int32 mb ;
   int trunspp ;
   unsigned long int * dumpsp = ( unsigned long int * ) dout ;
   int * extass = ( unsigned long int * ) dinf ; 
   int * cellist = listin ;
   int * sptable = ( unsigned long int * ) dpres ; 
   int minc , maxc , minr , maxr ;
   int sc ;
   int32 sb ;
   pleasewait ( "Reducing data set" ) ; 
   get_min_max_square ( &framinc , &framaxc , &framinr , &framaxr ) ;
   for ( a = 0 ; a < spcells ; ++ a ) dumpsp [ a ] = 0 ;
   for ( a = 0 ; a < spp ; ++ a ) {
       sc = a / 32 ;
       sb = 1 << a % 32 ;
       extass [ a ] = 0 ; 
       if ( ! ( spact[sc] & sb ) ) dumpsp [ sc ] |= sb ; }
   for ( a = 0 ; a < arcells ; ++ a ) cellist [ a ] = 0 ; 
   minc = framinc - 1 ;
   if ( minc < 0 ) minc = 0 ;
   minr = framinr - 1 ;
   if ( minr < 0 ) minr = 0 ;
   maxc = framaxc + 1 ;
   if ( maxc >= cols ) maxc = cols - 1 ;
   maxr = framaxr + 1 ;
   if ( maxr >= rows ) maxr = rows - 1 ;
   for ( a = minc ; a <= maxc ; ++ a ) 
      for ( b = minr ; b <= maxr ; ++ b ) {
          numar = ( b * cols ) + a ; 
          mc = numar / 32 ;
          mb = 1 << ( numar % 32 ) ;
          cellist [ mc ] |= mb ; }     // cellist: bit is 1 for every cell in frame and an outer layer of 1; 0 otherwise.
          
   // Only save spp. for which no observed records outside of frame and at least one record (obs. or ass.) within frame;
   // also count number of ass. records outside of frame (can't be calculated in reduced data set!)... 
   for ( a = 0 ; a < spp ; ++ a ) {
      sc = a / 32 ;
      sb = 1 << a % 32 ;
      k = 0 ;
      if ( ( dumpsp [ sc ] & sb ) ) continue ; 
      for ( b = totareas ; b -- ; ) {
         ax = b % cols ;
         ay = b / cols ;
         mc = b / 32 ;
         mb = 1 << ( b % 32 ) ;
         if ( !( cellist [ mc ] & mb ) ) {  // this is outside of (enlarged) square
             if ( ( matrix [ ay ] [ ax ] [ sc ] & sb ) ) {
                  dumpsp [ sc ] |= sb ;
                  if ( species_tree != NULL && a < numterminals )
                      for ( j = species_tree [ a ] ; j != treeroot ; j = species_tree [ j ] ) 
                          dumpsp [ ( j - 1 ) / 32 ] |= 1 << ( ( j - 1 ) % 32 ) ; }
             else if ( ( assmatrix [ ay ] [ ax ] [ sc ] & sb ) ) extass [ a ] ++ ; }
         else // this is inside 
           if ( ( matrix [ ay ] [ ax ] [ sc ] & sb ) || ( assmatrix [ ay ] [ ax ] [ sc ] & sb ) ) ++ k ; }
      if ( !k ) dumpsp [ sc ] |= sb ; } 
       
   // count # of spp and do table of correspondences   old sp. number --> new sp. number 
   trunspp = 0 ;
   for ( a = 0 ; a < spp ; ++ a ) {
      sptable [ a ] = -1 ; 
      sc = a / 32 ;
      sb = 1 << a % 32 ;
      if ( ! ( dumpsp [ sc ] & sb ) ) 
          sptable [ a ] = trunspp ++ ; }

   no_useful_spp = 0 ; 
   if ( !trunspp ) {
      imdone () ; 
      no_useful_spp = 1 ; 
      MessageBox ( hwnd , "Frame selected can't contain any areas" , "Note!" , MB_YESNO ) ;
      return ; }

   redcols = ( maxc - minc ) + 1 ;
   redrows = ( maxr - minr ) + 1 ;
   redarcells =  ( ( redrows * redcols ) + 31 ) / 32 ; 
   fprintf(outspace , "rows %i\ncols %i\nspp %i\ndata" , redrows , redcols , trunspp+1 ) ;

   for ( a = minr , atr = 0 ; a <= maxr ; ++ a , ++ atr ) { 
      for ( b = minc , atc = 0 ; b <= maxc ; ++ b , ++ atc ) { 
         if ( !isdefd [ a ] [ b ] ) continue ; 
         fprintf(outspace,"\nA%i-%i\n" , atr , atc ) ;
         lim = spp ;
         if ( species_tree != NULL ) lim = numterminals ; 
         for ( c = 0 ; c < lim ; ++ c ) { 
             mb = 1 << ( c % 32 ) ; 
             mc = c / 32 ;
             if ( ( dumpsp [mc] & mb ) ) continue ; 
             if ( ( matrix [ a ] [ b ] [ mc ] & mb ) ) putc ( '1' , outspace ) ; 
             else
                 if ( ( assmatrix [ a ] [ b ] [ mc ] & mb ) ) putc ( '2' , outspace ) ; 
                 else putc ( '0' , outspace ) ; }}}
   fprintf(outspace , "\n;\n" ) ;

   fprintf ( outspace , "extass " ) ;

#ifdef _DEBUGGING_
b = 0 ; 
#endif
   
   for ( a = 0 ; a < spp ; ++ a ) {
      sc = a / 32 ;
      sb = 1 << a % 32 ;
#ifdef _DEBUGGING_
spbecomes [ a ] = -1 ;
#endif
      if ( ( dumpsp [ sc ] & sb ) ) continue ;
#ifdef _DEBUGGING_
spbecomes [ a ] = b ++ ;
#endif
      fprintf ( outspace , "%i " , extass[ a ] ) ; }
   fprintf ( outspace , "\n;\n" ) ; 

   if ( species_tree != NULL ) {
       fprintf ( outspace , "groups\n" ) ;
       for ( m = numterminals + 1 ; m < species_tree[ treeroot ] ; ++ m ) {
          if ( ( dumpsp [ ( m - 1 ) / 32 ] & ( 1 << ( ( m - 1 ) % 32 ) ) ) ) continue ; 
          a = 0 ; 
          for ( k = 0 ; k < numterminals ; ++ k ) { 
             j = species_tree [ k ] ;
             while ( j != treeroot && j != m ) j = species_tree [ j ] ;
             if ( j == treeroot ) continue ;
             ++ a ; }
          if ( a < 2 ) continue ; 
          fprintf ( outspace , "{ " ) ; 
          for ( k = 0 ; k < numterminals ; ++ k ) { 
             j = species_tree [ k ] ;
             while ( j != treeroot && j != m ) j = species_tree [ j ] ;
             if ( j == treeroot ) continue ;
             fprintf ( outspace , "%i " , sptable [ k ] ) ; }
          fprintf ( outspace , " }\n" ) ; } 

      fprintf ( outspace , ";\n" ) ; }

   if ( weight_species ) {
       fprintf ( outspace , "spwts\n" ) ;
       for ( j = 0 ; j < spp ; ++ j ) {
           if ( ( dumpsp [ j / 32 ] & ( 1 << ( j % 32 ) ) ) ) continue ; 
           fprintf ( outspace , "   %.20f\n" , species_weight[ j ] ) ; }
       fprintf ( outspace , ";\n" ) ; }


   // Now, create a frame, and save it as constraint in file "tmp.kkk" 
   for ( a = 0 ; a < arcells ; ++ a ) cellist [ a ] = 0 ;
   if ( framinc ) atcol = 1 ;
   else atcol = 0 ; 
   for ( a = framinc ; a <= framaxc ; ++ a , ++ atcol ) {
      if ( framinr ) atrow = 1 ;
      else atrow = 0 ; 
      for ( b = framinr ; b <= framaxr ; ++ b , ++ atrow ) {
          numar = ( atrow * redcols ) + atcol ; 
          mc = numar / 32 ;
          mb = 1 << ( numar % 32 ) ;
          cellist [ mc ] |= mb ; }} // cellist: bit is 1 for every cell in frame; 0 otherwise.
   logfile = fopen ( "tmp.kkk" , "w" ) ; 
   if ( logfile == NULL ) {
      no_useful_spp = 1 ; 
      MessageBox ( hwnd , "Cannot open log file to save constraints" , "Note!" , MB_YESNO ) ;
      return ; }
   bsav ( sizeof ( int32 ) , redarcells , ( char * ) cellist ) ;
   bsav ( sizeof ( double ) , 1 , ( char * ) &( recptr -> score ) ) ;
   a = ( 1 + framaxc - framinc ) * ( 1 + framaxr - framinr ) ; 
   bsav ( sizeof ( int ) , 1 , ( char * ) &a ) ;
   fclose ( logfile ) ; 
   imdone () ;
   return ; 
} 


void move_from_red_to_full ( int32 * tol )
{
    int32 * from = listin , rc , rb , rat ;
    int atcol , atrow , a , b ;
    int32 mc , mb , at ; 
    atcol = framinc - 1 ;
    if ( atcol < 0 ) atcol = 0 ;
    for ( a = arcells ; a -- ; ) tol [ a ] = 0 ; 
    for ( a = 0 ; a < redcols ; ++ a , ++ atcol ) {
       atrow = framinr - 1 ;
       if ( atrow < 0 ) atrow = 0 ;
       for ( b = 0 ; b < redrows ; ++ b , ++ atrow ) {
           rat = ( b * redcols ) + a ; 
           rc = rat / 32 ;
           rb = 1 << ( rat % 32 ) ;
           if ( ( from [ rc ] & rb ) ) {  // Bit is ON, move it to corresponding place...
               at = ( atrow * cols ) + atcol ;
               mc = at / 32 ;
               mb = 1 << ( at % 32 ) ;
               tol [ mc ] |= mb ; }}}
    return ; 
}    
    
void read_reduced_sets_from_file ( void )
{
   int a = 0 ;
   int had = numrecs ;
   int shoulbe ; 
   Artyp * dorec ;
   int32 * cellist = listin ;
   exit_on_eof = 0 ; 
   infile = fopen ( "tmp.ndm", "rb" ) ;
   cls () ;
   pleasewait ( "Reading sets..." ) ; 
   dorec = rec + numrecs ; 
   while ( !feof ( infile ) ) { 
           if ( !bread ( sizeof ( int32 ) , redarcells , ( char * ) cellist ) ) break ;
           move_from_red_to_full ( dorec -> lst ) ; 
           if ( !bread ( sizeof ( double ) , 1 , ( char * ) &( dorec -> score ) ) ) break ; 
           if ( !bread ( sizeof ( int ) , 1 , ( char * ) &( dorec -> size ) ) ) break ; 
           dorec -> mark = 0 ;
           ++ a ; 
           ++ dorec ; }
   exit_on_eof = 1 ; 
   numrecs += a ;
   shoulbe = numrecs ; 
   imdone () ;
   if ( ridofdupes ) delete_duplicates ( 0 ) ;
   recptr = rec ; 
   check_the_new_scores ( had ) ;
   if ( !user_wants_a_break ) 
     if ( ridofdupes )
        myprintf( "Read %i sets (total now: %i; %i records discarded)\n \n \n [ hit ENTER or left-click to continue ]" , a , numrecs , shoulbe - numrecs ) ;
     else   
        myprintf( "Read %i sets (total: %i)\n \n \n [ hit ENTER or left-click to continue ]" , a , numrecs ) ;
   else
     if ( didanemptyone )
          myprintf( "%i sets contained in file (none read, created an empty set)\n \n \n [ hit ENTER or left-click to continue ]" , a ) ;     
     else 
          myprintf( "%i sets contained in file (none read; %i now in memory)\n \n \n [ hit ENTER or left-click to continue ]" , a , numrecs ) ;
   user_wants_a_break = didanemptyone = 0 ; 
   fclose ( infile ) ; 
   return ; 
}

int diff_string ( char * a , char * b )
{
    while ( * a && tolower ( * a ) == tolower ( * b ) ) { ++ a ; ++ b ; }
    return ( * a != * b ) ; 
}

int superset_at_level ( int i , int j , int lvl )
{
    int k , n ;
    char * ap , * bp ;
    int diff = 0 ;
    char * sa , * sb ;
    double val ;
    ap = spname [ i ] ;
    bp = spname [ j ] ;
    sa = kuka ;
    sb = kukb ; 
    while ( !diff && lvl ) {
         lvl -- ; 
         ap = setstring ( sa , ap ) ;
         bp = setstring ( sb , bp ) ;
         if ( ! * sa || ! * sb ) return 0 ;
         if ( diff_string ( sa , sb ) ) return 0 ; }
     return 1 ; 
}

int * tmpspecies_tree = NULL ;
int * tmptreesis , * tmptreefirs , tmptreeroot , number_of_groups ; 
int * tmptreelist , * tmpacurl , * tmpinnerlist , * tmpnodfork ; 

void find_and_save_higher_groups ( void )
{
    int * spbecs ;
    int a , i , j , k , n , p , q = 0 , endis , choice ;
    int some , at ;
    char * cp ;
    int numsavd = 0 ;
    int levelexists ;
    int tmpsz ; 
    if ( tmpspecies_tree == NULL ) {
       memerr ( tmpspecies_tree = ( int * ) malloc ( numterminals * 2 * sizeof ( int ) ) ) ;
       memerr ( tmptreefirs = ( int * ) malloc ( numterminals * 2 * sizeof ( int ) ) ) ;
       memerr ( tmptreesis = ( int * ) malloc ( numterminals * 2 * sizeof ( int ) ) ) ;
       memerr ( tmpnodfork = ( int * ) malloc ( numterminals * 2 * sizeof ( int ) ) ) ;
       memerr ( tmpinnerlist = ( int * ) malloc ( numterminals * 2 * sizeof ( int ) ) ) ;
       memerr ( tmptreelist = ( int * ) malloc ( numterminals * 2 * sizeof ( int ) ) ) ;
       memerr ( tmpacurl = ( int * ) malloc ( numterminals * 2 * sizeof ( int ) ) ) ; }
    tmpspecies_tree [ tmptreeroot = numterminals ] = numterminals + 1 ; 
    for ( a = numterminals ; a -- ; ) {
         tmpspecies_tree [ a ] = tmptreeroot ;
         tmptreesis [ a ] = a + 1 ; }
    tmptreefirs [ tmptreeroot ] = 0 ;
    tmptreesis [ numterminals - 1 ] = -1 ;

    spbecs = ( int * ) dout ;
    pleasewait ( "Checking name super-sets" ) ; 
    while ( 1 ) {
        ++ q ;
        levelexists = 0 ; 
        for ( i = 0 ; i < numterminals ; ++ i ) spbecs [ i ] = i ;
        for ( i = 0 ; i < numterminals ; ++ i ) {
           some = 0 ;  
           if ( spbecs[ i ] != i ) continue ;
           tmpinnerlist [ 0 ] = i ;
           tmpsz = 1 ; 
           for ( j = i ; ++ j < numterminals ; ) {
               if ( spbecs[j] != j ) continue ;  
               n = superset_at_level ( j , i , q ) ;
               if ( n ) {
                   ++ some ;
                   levelexists = 1 ;
                   tmpinnerlist [ tmpsz ++ ] = j ; 
                   spbecs [ j ] = i ; }}
           if ( some ) {
               if ( query ) {
                  at = 0 ; 
                  cp = spname [ i ] ;
                  while ( isspace ( * cp ) && * cp ) ++ cp ;
                  if ( * cp ) {
                      while ( * ++ cp ) 
                          if ( isspace ( * cp ) || * cp == '_' ) {
                              while ( isspace ( * cp ) && * cp ) ++ cp ; 
                              if ( ++ at >= q ) break ; }}
                  j = * cp ; * cp = '\0' ; 
                  sprintf ( junkstr , "There is a group \"%s\"\nSave it?" , spname[i] ) ;
                  * cp = j ;
                  choice = MessageBox ( hwnd , junkstr , "Saving..." , MB_YESNOCANCEL ) ; }
               else choice = IDYES ; 
               if ( choice == IDCANCEL ) { imdone () ; return ; }
               if ( choice == IDYES ) 
                   add_node_to_temporary_tree ( tmpinnerlist , tmpsz ) ; }
            }
        if ( !levelexists ) break ; }
   imdone () ;

//   tmpsz = mkoptlist ( tmptreelist , tmpspecies_tree ) ;  

   if ( tmpspecies_tree[tmptreeroot] > tmptreeroot + 1 ) {
      pleasewait ( "Saving groups found" ) ; 
      fprintf ( outspace , "\ngroups\n" ) ; 
      for ( a = tmptreeroot + 1 ; a < tmpspecies_tree[tmptreeroot] ; ++ a ) 
          save_tmptreenod ( a ) ;
      imdone () ; }
   
   return ;                  
}

void save_tmptreenod ( int nd )
{
    int depth = 0 , at ;
    int i , j , isin , u ;
    char * cp ;
    int isfirst = -1 ;
    i = nd ; 
    while ( i != tmptreeroot ) { ++ depth ; i = tmpspecies_tree [ i ] ; }
    for ( j = 0 ; j < numterminals ; ++ j ) {
        isin = 0 ; 
        for ( i = tmpspecies_tree [ j ] ; i != tmptreeroot && !isin ; i = tmpspecies_tree [ i ] )
               if ( i == nd ) isin = 1 ;
        if ( isin ) {
            if ( isfirst < 0 ) fprintf ( outspace , "{ " , i ) ;
            isfirst = j ;
            fprintf ( outspace , "%i " , j ) ; }}
     j = isfirst ; 
     at = 0 ; 
     cp = spname [ j ] ;
     while ( isspace ( * cp ) && * cp ) ++ cp ;
     if ( * cp ) {
         while ( * ++ cp ) 
             if ( isspace ( * cp ) || * cp == '_' ) {
                 while ( isspace ( * cp ) && * cp ) ++ cp ; 
                 if ( ++ at >= depth ) break ; }}
     u = * cp ; * cp = '\0' ; 
     fprintf ( outspace , " } [ %s ]\n" , spname[j] ) ; 
     * cp = u ;
     return ; 
}

void tmpmksis ( int * an )
{ int * list = tmptreelist ; 
  int * x = list , * y = list + 1;
  int * last , nd ; 
  int a, i;
  last = list ; 
  for ( a = 2*numterminals-1 ; a -- ; ) 
      tmptreesis [ a ] = tmptreefirs [ a ] = list [ a ] = -1 ;
  for ( a = numterminals ; a -- ; ) {
      i = an [ nd = a ] ; 
      if ( !i ) continue ; 
      while ( i != numterminals && tmptreefirs [ i ] < 0 ) {
                    last [ i ] = tmptreefirs [ i ] = nd ;
                    nd = i ;
                    i = an [ i ] ; }
      if ( tmptreefirs [ i ] < 0 ) tmptreefirs [ i ] = nd ; // i.e. i == numterminals 
      if ( last [ i ] >= 0 ) tmptreesis [ last [ i ] ] = nd ;
      last [ i ] = nd ; }
   return ;
} 


void add_node_to_temporary_tree ( int * list , int lisz )
{
    int trusz = 0 , lastis ;
    int x , a , b , c ; 
    for ( a = 0 ; a < tmpspecies_tree [ tmptreeroot] ; ++ a ) tmptreelist [ a ] = tmpacurl [ a ] = 0 ;
    /** all sizes... */ 
    tmpacurl [ tmptreeroot ] = numterminals ; 
    for ( a = 0 ; a < tmpspecies_tree [ tmptreeroot] ; ++ a )
        for ( b = tmpspecies_tree [ a ] ; b != tmptreeroot ; b = tmpspecies_tree [ b ] )
              tmpacurl [ b ] ++  ;
    /*** find minimum common node ******/
    for ( x = 0 ; x < lisz ; ++ x ) {
        a = list [ x ] ; 
        if ( tmptreelist [ a ] ) continue ;
        ++ trusz ;
        tmptreelist [ a ] ++ ;
        b = lastis = a ;  
        while ( b != tmptreeroot ) 
            ++ tmptreelist [ b = tmpspecies_tree [ b ] ] ; }
    a = tmpspecies_tree [ lastis ] ;
    while ( tmptreelist [ a ] < trusz ) a = tmpspecies_tree [ a ] ; 

    if ( trusz == tmpacurl [ a ] ) return ;   // a duplicate group ... ignore... 

    /** Create new node *****/
    for ( b = 0 ; b < tmpspecies_tree [ treeroot] ; ++ b ) tmptreelist [ b ] = 0 ;
    for ( b = 0 ; b < lisz ; ++ b ) {
        c = list [ b ] ; 
        while ( tmpspecies_tree [ c ] != a && !tmptreelist [ c ] ) c = tmpspecies_tree [ c ] ;
        if ( tmptreelist [ c ] ) continue ; 
        tmptreelist [ c ] = 1 ;
        tmpspecies_tree [ c ] = tmpspecies_tree [ tmptreeroot ] ; }
    tmpspecies_tree [ tmpspecies_tree [ tmptreeroot ] ] = a ; 
    tmpspecies_tree [ tmptreeroot ] ++ ; 
    /*** Make final tree *****/
    tmpmksis ( tmpspecies_tree ) ;
    return ; 
}

void ( * samplit ) ( int ) ; 

void reset_matrix ( void )
{
   int a , b , c , d , i , j , siz , left ;
   int trurows = rows , trucols = cols ; 
   Artyp * dorec ;
   for ( a = rows ; a -- ; )
     for ( b = cols ; b -- ; ) 
       for ( c = spcells ; c -- ; ) matrix [a][b][c] = assmatrix [a][b][c] = 0 ;  
   for ( c = spp ; c -- ; ) numentries[c] = numassentries[c] = 0 ; 

   for ( a = 0 ; a < spcells ; ++ a ) spact[a] = -1 ;
   trurows = rows ;
   trucols = cols ;
   created_wid = truecellwid ;
   created_hei = truecellhei ; 
   nitmatrix () ; 
   grid_created = 2 ;
}

void undosample ()
{
    int c ; 
    for ( c = 0 ; c < spp ; ++ c ) 
       xymatrix[c].numrecs = xymatrix[c].trurecs ;
    reset_matrix ( ) ;
}

void sample_delete_duplicates ( Artyp * from )
{
    Artyp * ar ;
    int had = numrecs ; 
    recptr = rec + numrecs ;
    for ( ar = rec ; ar < recptr ; ++ ar ) ar ->erase = 0 ; 
    for ( ar = from ; ar < recptr ; ++ ar ) 
        if ( !ar-> erase && isduparea ( ar ) ) {
                    ar -> erase = 1 ;  } 
    delete_marks ( 1 ) ;
    recptr = rec ; 
    return ; 
}     

int sampled_search ( int repl , int isauto )
{
    int a , b ;
    FILE * scriptfile ; 
    Artyp * recptr = rec + numrecs , * from ; 
    b = 0 ;
    for ( a = 0 ; a < spcells && !b ; ++ a )
       if ( spact[a] ) ++ b ;
    if ( !b ) {
        MessageBox ( hwnd , "Nothing to search:\n   no active species!" , "Error" , MB_OK | MB_ICONERROR ) ;
        return 0 ; }
    if ( !repl && !isauto ) {
         isforsample = 1 ; 
         a = DialogBox ( hInst, "RunNDMDB", hwnd, (DLGPROC) RunNDMFunc ) ;
         isforsample = 0 ; 
         if ( !a ) return 0 ; }
    strcpy ( comstring , "tmp.dat" ) ;
    cmd_loop ( 'o' ) ;
    strcpy ( comstring , "d" ) ;
    if ( frame_the_search ) {
            MessageBox ( hwnd , "Cannot use framed searches for resampling" , "Error" , MB_OK | MB_ICONERROR ) ;
            return 0 ; }
    cmd_loop ( 's' ) ;
    fclose ( outspace ) ;
    if ( no_useful_spp ) return 0 ; 
    outspace = NULL ;
    isforsample = repl + 1 ;  
    if ( ndm_bin_name == NULL ) 
         a = my_spawn ( "ndm" , schstring , Null ) ;
    else a = my_spawn ( ndm_bin_name , schstring , Null ) ;
    isforsample = 0 ;  
    if ( a == 255 ) {
           errmsg ( "Cannot run NDM!\n(try specifying location of\nbin in file \".vndm.rc\")" , Null ) ; return 0 ; }
   from = recptr = rec + numrecs ; 
   strcpy ( comstring , "tmp.ndm" ) ;
   scriptfile = fopen ( comstring , "rb" ) ;
   if ( scriptfile != NULL ) {
       a = getc ( scriptfile ) ;
       ungetc ( a , scriptfile ) ;
       if ( !feof ( scriptfile ) ) {
          fclose ( scriptfile ) ;
          read_sets_from_file ( ) ;
          recptr = rec ;
          curcmd_loop = cmd_loop ; 
          sample_delete_duplicates ( from ) ; }
       else fclose ( scriptfile ) ; }
return 1 ; 
}

double do_species_similarity ( Artyp * aa , Artyp * ab )
{
    int32 * app , * bpp ;
    int i ;
    int both , ina , inb ;
    double perc , den , num ; 
    app = aa -> splist ; 
    bpp = ab -> splist ;
    both = ina = inb = 0 ; 
    for ( i = 0 ; i < spcells ; ++ i ) {
        both += onbits ( * app & * bpp ) ;
        ina += onbits ( * app & ~ * bpp ) ; 
        inb += onbits ( * bpp & ~ * app ) ;
        ++ app ; ++ bpp ; }
     num = ( double ) both * 100 ;
     den = ( both + ina + inb ) ; 
     perc = num / den ;
     return perc ; 
}    

void prepare_sch_string ( void )
{
    int i , j ;
    static int
        usswap = 1 , usprechk = 1 , 
        usclean = 0 , usn = 50000 , usm ;
    static double usM , usr = 0.99 ; 
    static int
        myswap , myp , mym , 
        myclean , myn , myperc , myk , mystart , myskipsup , myxskip , myreplace ;
    static double myM , myr , usersubo ;
    static int myprechk ;
    static int mynumreps = 1 ;
    static int myframeit ; 
    char * cp ;
    // Dialog initialization... 
                   usM = sch_minimum_total_score ;
                   usm = sch_minimum_scoring_spp ; 
                   myprechk = usprechk ; 
                   myr = usr ;
                   myM = usM ;
                   mym = usm ; 
                   myswap = usswap ;
                   myp = use_edge_props ;
                   myclean = usclean ;
                   myn = usn ;
                   myperc = compare_perc ;
                   myk = -1 ;
                   myframeit = 0 ; 
                   mystart = usersubo = 0 ;
                   myskipsup = skip_superfluous ;
                   myxskip = xskip_superfluous ;
                   myreplace = replace_existing_sets ; 
     // OK button ...
                sch_minimum_total_score = usM ;
                sch_minimum_scoring_spp = usm ; 
                compare_perc = myperc ;
                use_edge_props = myp ;
                frame_the_search = 0 ; 
                sprintf ( schstring, "\
                         tmp.dat -ltmp.ndm -data -r%f -M%f -m%i -swap%i -n%i -%%%i -fi%f -fa%f -fo%f -fd%f -fn%f -e%i -T%i " ,
                         myr , myM , mym , myswap , myn , myperc ,
                         iifac , iafac , oufac , oafac , ononafac , abslim , min_pres_perc ) ;
                if ( musthaveone != 1 ) {
                    cp = schstring + strlen ( schstring ) ;
                    sprintf ( cp , "-h%i ", musthaveone ) ; }
                if ( usersubo > 0 ) {
                    cp = schstring + strlen ( schstring ) ;
                    sprintf ( cp , " -o%f ", usersubo ) ; }
                if ( mystart ) {
                    i = query ;
                    query = 0 ; 
                    sprintf ( comstring , "tmp.ini" ) ;
                    cmd_loop ( 'L' ) ;
                    query = i ; 
                    strcat ( schstring , " -starttmp.ini " ) ; }
                if ( myprechk ) strcat ( schstring , "-postchk " ) ;
                if ( rseed != 1 ) {
                    cp = schstring + strlen ( schstring ) ;
                    sprintf ( cp , "-d%i ", rseed ) ; }
                if ( mynumreps > 1 ) {
                    cp = schstring + strlen ( schstring ) ;
                    sprintf ( cp , "-#%i ", mynumreps ) ; }
                if ( minimum_sp_score > 0 ) {
                    cp = schstring + strlen ( schstring ) ;
                    sprintf ( cp , "-b%f ", minimum_sp_score ) ; }
                usr = myr ;
                usM = myM ;
                usm = mym ;
                usswap = myswap ;
                usn = myn ;
                usprechk = myprechk ;
                skip_superfluous = myskipsup ;
                xskip_superfluous = myxskip ;
                replace_existing_sets = myreplace ; 
                if ( myxskip ) strcat ( schstring , "-sskip " ) ;
                else
                   if ( myskipsup ) strcat ( schstring , "-skip " ) ; 
                if ( myk >= 0 ) {
                    if ( myk > 0 ) copyar ( 0 , myk ) ;
                    recptr = rec ;
                    numrecs = 1 ;
                    if ( !myframeit ) {   // when framing, must save constraint area as reduced...
                        sprintf ( comstring , "tmp.kkk" ) ;
                        cmd_loop ( 'L' ) ; }
                    strcat ( schstring, "-ktmp.kkk " ) ; }
                if ( myp ) strcat ( schstring , "-p " ) ;    
}
    
void run_the_autosample ( void )
{
    prepare_sch_string () ;
    the_fuckin_sample ( run_autosample , 1 ) ;
}

extern int max_drawn_y , max_drawn_x ; 

void save_all_areas_to_metafile ( HDC myhdc )
{
    int i , done = 0 ; 
    recptr = rec - 1 ;
    atcoordy = atcoordx = 0 ; 
    for ( i = 0 ; i < numrecs ; ++ i ) {
        cmd_loop ( VK_RETURN ) ;
        showmap ( myhdc ) ;
        ++ done ; 
        if ( done == 5 ) {
             atcoordy = - ( max_drawn_y + 25 ) ;
             atcoordx = done = 0 ; }
        else {
           atcoordx = - max_drawn_x ;
           atcoordy -= 25 ; }
    }
    cmd_loop ( VK_RETURN ) ;
    atcoordy = atcoordx = 0 ; 
}

void save_all_consensus_to_metafile ( HDC myhdc )
{
    int i , done = 0 ; 
    curcons = -1 ;
    atcoordx = 0 ; 
    for ( i = 0 ; i < numcons ; ++ i ) {
        show_consensus ( VK_RETURN ) ;
        current_species = -1 ; 
        showmap ( myhdc ) ;
        ++ done ; 
        if ( done == 5 ) {
             atcoordy = - ( max_drawn_y + 25 ) ;
             atcoordx = done = 0 ; }
        else             
           atcoordx = - max_drawn_x ; 
    }
    show_consensus ( VK_RETURN ) ;
    atcoordy = atcoordx = 0 ; 
}

void diagnose_repl ( int which )
{
    Artyp * rp , * otrp ;
    int i ;
    double f , best ;
    double fs , bests ;
    double mincomp = 50 ;
    if ( sample_area_cut > 50 ) mincomp = sample_area_cut ; 
    if ( sample_spp_cut > 50 ) mincomp = sample_spp_cut ; 
    recptr = rec + numrecs ; 
    for ( otrp = replinit ; otrp < recptr ; ++ otrp ) otrp -> fromrepl = which ; 
    for ( rp = rec ; rp < bootinit ; ++ rp ) {
        best = bests = 0 ; 
        for ( otrp = replinit ; otrp < recptr ; ++ otrp ) {
            f = do_set_similarity ( rp , otrp ) * 100 ;
            fs = do_species_similarity ( rp , otrp ) ;
            if ( f >= mincomp && fs >= mincomp ) otrp -> fromrepl = -which ; 
            if ( sample_area_cut ) {
              if ( sample_area_cut > 0 ) {
                 if ( sample_area_cut <= f ) f = 100 ;
                 if ( sample_area_cut > f ) f = 0 ; }
              else 
                 if ( -sample_area_cut > f ) f = 0 ; }
            if ( sample_spp_cut ) {
              if ( sample_spp_cut > 0 ) {
                 if ( sample_spp_cut <= fs ) fs = 100 ;
                 if ( sample_spp_cut > fs ) fs = 0 ; }
              else if ( -sample_spp_cut > fs ) fs = 0 ; }
            if ( f > best ) best = f ;
            if ( fs > bests ) bests = fs ;
            }
        rp -> bootarval += best ;
        rp -> bootspval += bests ;
       }
}

void sampletype1 ( int numrep )
{
   int a , b , c , d , i , j , left ;
   int trurows = rows , trucols = cols ;
   double x , y ; 
   Artyp * dorec ;
   for ( c = 0 ; c < spp ; ++ c ) 
       xymatrix[c].numrecs = xymatrix[c].trurecs ;
   /**  the actual sampling ****/
   for ( c = 0 ; c < spp ; ++ c ) {
       left = xymatrix[c].numrecs ;
       for ( d = 0 ; d < left ; ++ d ) {
           i = ( rand () % 100 ) ;
           if ( i < sample_rec_prop ) {
              x = xymatrix[c].x[left-1] ;
              y = xymatrix[c].y[left-1] ; 
              xymatrix[c].x[left-1] = xymatrix[c].x[d] ; 
              xymatrix[c].y[left-1] = xymatrix[c].y[d] ;
              xymatrix[c].x[d] = x ; 
              xymatrix[c].y[d] = y ; 
              -- left ;
              -- d ; }
        xymatrix[c].numrecs = left ; }}
   /*** end sampling ****/
   reset_matrix () ; 
}

void sampletype2 ( int numrep )
{
   int a , b , c , d , i , j , left ;
   int trurows = rows , trucols = cols ;
   double x , y ; 
   Artyp * dorec ;
   for ( c = 0 ; c < spp ; ++ c ) 
       xymatrix[c].numrecs = xymatrix[c].trurecs ;
   /**  the actual sampling ****/
   for ( c = 0 ; c < spp ; ++ c ) {
       left = xymatrix[c].numrecs ;
       i = ( rand () % 100 ) ;
       if ( i >= sample_spp_prop ) continue ; 
       for ( d = 0 ; d < left ; ++ d ) {
           i = ( rand () % 100 ) ;
           if ( i < sample_rec_prop ) {
              x = xymatrix[c].x[left-1] ;
              y = xymatrix[c].y[left-1] ; 
              xymatrix[c].x[left-1] = xymatrix[c].x[d] ; 
              xymatrix[c].y[left-1] = xymatrix[c].y[d] ;
              xymatrix[c].x[d] = x ; 
              xymatrix[c].y[d] = y ; 
              -- left ;
              -- d ; }
        xymatrix[c].numrecs = left ; }}
   /*** end sampling ****/
   reset_matrix () ; 
}

int32 * refar = NULL ; 

void sampletype3 ( int numrep )
{
   int a , b , c , d , i , j , left ;
   int trurows = rows , trucols = cols ;
   double x , y , myx , myy , drow , dcol ; 
   Artyp * dorec ;
   for ( c = 0 ; c < spp ; ++ c ) 
       xymatrix[c].numrecs = xymatrix[c].trurecs ;
   /**  the actual sampling ****/
   for ( c = 0 ; c < spp ; ++ c ) {
       left = xymatrix[c].numrecs ;
       i = ( rand () % 100 ) ;
       if ( i >= sample_spp_prop ) continue ; 
       for ( d = 0 ; d < left ; ++ d ) {
           myx = xymatrix[c].x[d] ; 
           myy = xymatrix[c].y[d] ;
           drow = ( myy - grid_starty ) / truecellhei ;  
           a = ( int ) drow ; 
           dcol = ( myx - grid_startx ) / truecellwid ;
           b = ( int ) dcol ;
           if ( a < 0 || b < 0 || a >= rows || b >= cols ) continue ;  // these fall outside the grid... 
           i = ( a * cols ) + b ;
           if ( ( refar[ i / 32 ] & ( 1 << ( i % 32 ) ) ) == 0 ) continue ; 
           i = ( rand () % 100 ) ;
           if ( i < sample_area_prob ) {
               x = xymatrix[c].x[left-1] ;
               y = xymatrix[c].y[left-1] ; 
               xymatrix[c].x[left-1] = xymatrix[c].x[d] ; 
               xymatrix[c].y[left-1] = xymatrix[c].y[d] ;
               xymatrix[c].x[d] = x ; 
               xymatrix[c].y[d] = y ; 
               -- left ;
               -- d ; }
            xymatrix[c].numrecs = left ; }}
   /*** end sampling ****/
   reset_matrix () ; 
}

/*** Used only for developing ...
void test_the_sample ( int type )
{
   int i , c ;
   int isneg = 0 ; 
   Artyp * rp ; 
   if ( type == 1 ) samplit = sampletype1 ;
   if ( type == 2 ) samplit = sampletype2 ;
   if ( type == 3 ) {
       memerr ( refar = ( int32 * ) malloc ( arcells * sizeof ( int32 ) ) ) ;
       for ( i = 0 ; i < arcells ; ++ i )
          refar [ i ] = rec [ numrecs - 1 ].lst[i ] ;
       if ( sample_area_prob < 0 ) {
          isneg = 1 ; 
          for ( i = 0 ; i < arcells ; ++ i )
              refar [ i ] = ~refar [ i ] ;
          sample_area_prob = -sample_area_prob ; } 
       samplit = sampletype3 ; }
   srand ( (unsigned long int ) rseed ) ;
   bootinit = rec + numrecs ; 
   samplit ( i ) ;
   showcurset () ;
   if ( isneg ) sample_area_prob = -sample_area_prob ; 
   curcmd_loop = cmd_loop ; 
}
****/

void the_fuckin_sample ( int type , int isauto )
{
   int i , c ;
   int isneg = 0 ; 
   Artyp * rp ; 
   if ( type == 1 ) samplit = sampletype1 ;
   if ( type == 2 ) samplit = sampletype2 ;
   if ( type == 3 ) {
       memerr ( refar = ( int32 * ) malloc ( arcells * sizeof ( int32 ) ) ) ;
       for ( i = 0 ; i < arcells ; ++ i )
          refar [ i ] = rec [ numrecs - 1 ].lst[i ] ;
       -- numrecs ; 
       if ( sample_area_prob < 0 ) {
          isneg = 1 ; 
          for ( i = 0 ; i < arcells ; ++ i )
              refar [ i ] = ~refar [ i ] ;
          sample_area_prob = -sample_area_prob ; } 
       samplit = sampletype3 ; }
   srand ( (unsigned long int ) rseed ) ;
   bootinit = rec + numrecs ; 
   for ( rp = rec ; rp < bootinit ; ++ rp )
        rp -> bootarval = rp -> bootspval = 0 ; 
   for ( i = 0 ; i < sample_repls ; ++ i ) {
          samplit ( i ) ;
          replinit = rec + numrecs ; 
          if ( !sampled_search ( i , isauto ) ) break ;
          diagnose_repl ( i + 1 ) ; }
   for ( rp = rec ; rp < bootinit ; ++ rp ) {
        rp -> bootarval /= sample_repls ; 
        rp -> bootspval /= sample_repls ; } 
   didaboot = 1 ; 
   undosample () ;
   recptr = rec ;
   showcurset () ;
   if ( isneg ) sample_area_prob = -sample_area_prob ; 
   curcmd_loop = cmd_loop ; 
}

void save_data_within_curset( void )
{
    int a , b , c , i , j , k , x , pres , isexo , inited = 0;
    int32 * areapt = recptr -> lst , mb , cb ;
    int * lp ;
    char * cp ; 
    int * fare , * fato ;
    int mc , cc , myc , myr ;
    double begridx = 10000000 , begridy = 10000000000; 
    dorule5() ; 
    for ( b = 0 ; b < rows ; ++ b ) 
        for ( c = 0 ; c < cols ; ++ c ) {
            cc = ( ( cols * b ) + c ) / 32 ;
            cb = 1 << ( ( ( cols * b ) + c ) % 32 ) ;
            if ( !( areapt [ cc ] & cb ) ) continue ; 
            if ( begridx > ( created_orgx + ( truecellwid * c ) ) )
                 begridx = ( created_orgx + ( truecellwid * c ) ) ; 
            if ( begridy > ( created_orgy + ( truecellhei * b ) ) )  
                 begridy = ( created_orgy + ( truecellhei * b ) ) ; } 
    fprintf ( outspace , "longlat\nynegative\nfill %.2f %.2f\nassume %.2f %.2f\n" , 
              xperc , yperc , xassperc , yassperc ) ; 
    // fprintf ( outspace , "rows %i\ncols %i\nautomatrix\n" , rows , cols ) ;
    chkiscom ( 255 ) ;
    if ( comstring[ 0 ] == '\0' ) 
         fprintf ( outspace , "gridx %.5f %.5f \ngridy %.5f %.5f\nautomatrix\n" , begridx , truecellwid , begridy , truecellhei ) ;
    else fprintf ( outspace , "gridx %.5f %s \ngridy %.5f %s\nautomatrix\n" , begridx , comstring , begridy , comstring ) ;
    fprintf ( outspace , "spp %i\nnocommas\nxydata\n" , spp ) ;
    for ( a = 0 ; a < spp ; ++ a ) {
        spscore [ a ] = 1 ; 
        mc = a / 32 ;
        mb = 1 << ( a % 32 ) ; 
        pres = isexo = 0 ;
        for ( i = 0 ; i < totareas ; ++ i ) {
            myc = i % cols ;
            myr = i / cols ; 
            cc = i / 32 ;
            cb = 1 << ( i % 32 ) ;
            if ( ( areapt [ cc ] & cb ) == 0 ) {
                if ( ( matrix [ myr ] [ myc ] [ mc ] & mb ) ) {
                    isexo = 1 ;
                    break ; }}
            else 
                if ( ( matrix [ myr ] [ myc ] [ mc ] & mb ) ) 
                    pres = 1 ; } 
        if ( isexo || !pres ) { spscore [ a ] = 0 ; continue ; }
        if ( a >= numterminals ) continue ; 
        fprintf ( outspace , "sp %i " , a ) ;
        if ( spname != NULL ) fprintf ( outspace , "[ %s ]" , spname [ a ] ) ;
        fprintf ( outspace , "\n" ) ;
        for ( b = 0 ; b < xymatrix[a].numrecs ; ++ b ) 
           fprintf ( outspace , " %.6f %.6f\n" , xymatrix[a].x[b] , xymatrix[a].y[b] ) ; }
    if ( species_tree != NULL ) {
        for ( a = number_of_groups - 1 ; a > 0 ; a -- ) {
            j = treelist [ a ] - 1 ;
            * ( fare = fato = innerlist ) = j + 1 ;
            //if ( spscore [ j ] == 0 ) continue ; 
            ++ fare ;
            if ( !inited ) 
                fprintf ( outspace , "\ngroups\n" ) ;
            inited = 1 ;
            fprintf ( outspace , "{ " ) ; 
            while ( fato < fare ) {
                if ( ( b = * fato ++ ) >= numterminals )
                     for ( x = treefirs [ b ]  ; x >= 0 ; x = treesis [ x ] ) * fare ++ = x ;
                else fprintf ( outspace , "%i " , b ) ; }
            fprintf ( outspace , " } " ) ;
            if ( spname != NULL ) {
                cp = spname [ j ] ;
                while ( * cp != '-' ) ++ cp ; ++ cp ; while ( * cp != '-' ) ++ cp ; ++ cp ; 
                fprintf ( outspace , "[ %s ] " , cp ) ;
            fprintf ( outspace , "\n" ) ;  }}
       if ( inited ) fprintf ( outspace , ";\n" ) ; }

   if ( nummaplins ) {
      fprintf ( outspace , "map\n" ) ; 
      for ( a = 0 ; a < nummaplins ; ++ a ) {
         fprintf ( outspace , "line " ) ; 
         for ( b = 0 ; b < maplin[a].numpoints ; ++ b ) 
            fprintf ( outspace , "%.6f %.6f " , maplin[a].x[b] , maplin[a].y[b] ) ;
         fprintf ( outspace , "\n" ) ; }}
   
    sprintf ( junkstr , "Saved data within set %i to output file" , recptr - rec ) ; 
    captf ( junkstr ) ;
    return ;
}

void save_list_of_scoring_spp_in_marked_sets( void )
{
    Artyp * olpt = recptr ;
    int * treeback = species_tree ; 
    int i ; 
    recptr = rec + numrecs ;
    pleasewait ( "Finding list of scoring spp..." ) ;
    species_tree = NULL ; 
    while ( recptr -- > rec ) {
        if ( recptr -> mark == 0 ) continue ; 
        dorule5 () ;
        for ( i = 0 ; i < spp ; ++ i )
           if ( spscore[i] > 0 )
              fprintf ( outspace , "%i " , i ) ; }
    species_tree = treeback ; 
    imdone () ;
    recptr = olpt ;
    showcurset () ; 
    captf ( "Saved list of scoring species" ) ;
}

void get_list_of_taxa_to_wipe_from_file ( void )
{
    FILE * where ;
    int i , numdone = 0 ;
    int32 flg ; 
    get_filename ( '@' ) ;
    if ( comstring[0] == '\0' ) return ;
    where = fopen ( comstring , "rb" ) ;
    if ( where == NULL ) {
        sprintf ( junkstr , "Error: can't open file %s" , comstring ) ;
        captf ( junkstr ) ;
        return ; }
    while ( !feof ( where ) ) {
        if ( fscanf ( where , " %i" , &i ) ) {
           if ( i >= spp ) {
              sprintf ( junkstr , "Wrong species number: %i?" , i ) ;
              ermsg ( junkstr ) ;
              return ; }
           flg = 1 << ( i % 32 ) ;
           if ( ( spact [ i / 32 ] & flg ) ) ++ numdone ; 
           flg = -1 ^ flg ; 
           spact [ i / 32 ] &= flg ; }}
    fclose ( where ) ;        
    sprintf ( junkstr , "Deactivated %i spp" , numdone ) ;
}    

