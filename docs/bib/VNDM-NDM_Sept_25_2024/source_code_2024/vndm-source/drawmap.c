#include <windows.h>
#include <windowsx.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#define VTYPE extern 
#include "winvndm.h"
#include <stdlib.h>
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

#define int32 unsigned long int 

BOOL CALLBACK FakeGridSizePosFunc(HWND , UINT , WPARAM , LPARAM ) ;

extern int show_color_code , consensus_is_sample ; 
extern double * dout ; 
extern int ysign , xsign , spcells , is_cons_duwc , hide_the_map ; 
extern int only_show_points ; 
int show_individual_dots = 0 ; 
extern int cursize , markscore ;
extern unsigned int * lst ; 
extern int make_radius_assumed , ctrl_arrow_changes_org ; 
extern double consen_minval , consen_intrvl , consen_maxval ;
extern double mincellwid , mincellhei ; 
int black_n_white = 0 ; 
extern int PointWidth ; 
extern unsigned long int * spact , * spingrid ;
extern int num_spingrid ;
extern double truecellwid , truecellhei ;
extern double xperc , yperc , xassperc , yassperc ;
extern unsigned long int * intersptr , * splist ;
extern int * tmplist ;
extern int current_species ;
extern HPEN hBranchpen , hYellowPen , hBlackPen , hWhitePen ;
extern double minx , miny ; 


/***  USED ONLY TO DRAW MAP ********/
#define MAXLINPTS 50000
#define MAXNUMLINS 100000 

extern int nummaplins , selpoint_only ;
int selected_maplin = -1 , selmappoint , selmappointmax ; 
POINT mapptlist[ 50000 ] ;
HPEN hMapRedPen , hMapGreenPen; 
HPEN hMapPen ;
double autolinepointx , autolinepointy ;
int doautolines = 0 ;
extern int rbuttisdn ;
HWND mainwnd ;
int lasmousecoordsx = 65535 , lasmousecoordsy = 65535 ; 
void get_curs_coords ( double * , double * ) ;
extern int last_point_extend ; 

/*
typedef struct { 
           int32 * lst ;
           int32 * splist ; 
           int size ; 
           int mark ;
           int erase ;
           int numspp ; 
           double score ; } Artyp ; 
extern Artyp * rec , * recptr ; */
extern Artyp * rec ; 

/**********  This is used to "consense" areas **************/
typedef struct {
     double * spmin , * spmax ;
     double * clmin , * clmax ;
     double min , max ; 
     int numareas ;
     int * arlist ;
     int is_xcess ; }  Constyp ;
extern Constyp * consen ;
extern int numcons ;

int grid_effect = 300 ; 

extern int grid_created , faked_a_grid ;
extern int numrecs , spp ; 
static int nited = 0 ;
extern char filename[MAX_PATH+3];
HBRUSH brushtoset ;
int nucolis ; 
extern HINSTANCE hInst ; 
extern int atcoordx , atcoordy ; 
char screentitle[1024] ;
char screencapt[65535*5] ; 
void MyLine ( HDC , int , int , int , int ) ; 

extern void (*curcmd_loop ) ( int ) ;
extern void viewscore ( int ) ;
extern void show_duwc ( int ) ;
extern void showfauna ( int ) ;
extern void showspecies ( int ) ; 
extern void cmd_loop ( int ) ; 
extern void show_consensus ( int ) ;

extern int cols , rows ;
extern char ** isdefd ;
extern int cursrow , curscol ;
extern int showcursor ;
extern int show_coordinates ;
extern double grid_starty , grid_height ;
extern double grid_startx , grid_width ; 


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

void myprintf ( void * , ... ) ; 

int crh = 'Ú' ,
    cho = 'Ä' ,
    cdn = 'Â' ,
    cup = 'Á' ,
    csi = 'Ã' ,
    cco = '´' ,
    ctr = 'Å' , 
    cka = '¿' ,
    cve = '³' , 
    cel = 'À' , 
    cjo = 'Ù' ;
#define SETCP( x, y, z ) { * cp ++ = ( x ) ; * cp ++ = ( y ) ; * cp ++ = ( z ) ; } 

char ** sccol = NULL ; 

void create_map_pens ( void )
{
    static int created = 0 ;
    if ( created ) {
        DeleteObject(hMapPen) ;
        DeleteObject(hMapRedPen) ; }
    created = 1 ;       
    hMapRedPen = CreatePen ( PS_SOLID, 8 , RGB ( 255 , 0 , 0 ) ) ;
    hMapGreenPen = CreatePen ( PS_SOLID, 2 , RGB ( 0 , 255 , 0 ) ) ;
    hMapPen = CreatePen ( PS_SOLID, 2 , RGB ( 0 , 0 , 0 ) ) ;
}
    
void drawmap ( int32 * gp , int32 * othr , int32 * thrd ) 
{ int a , b , numar , mc ; 
  char * cp ;
  int key ;
  double atcoord ; 
  int32 mb ; 
  if ( !grid_created ) return ; 
  for ( a = 0 ; a < rows ; ++ a ) { 
        for ( b = 0 ; b < cols ; ++ b ) {
              if ( !isdefd[a][b] ) {
                      sccol[b][a] = 8 ; continue ; }
              numar = ( cols * a ) + b ; 
              mb = 1 << ( numar % 32 ) ; 
              mc = numar / 32 ;
              key = 0 ; 
              if ( ( gp [ mc ] & mb ) ) key |= 1 ;
              if ( othr != NULL && ( othr [ mc ] & mb ) ) key |= 2 ;
              if ( thrd != NULL && ( thrd [ mc ] & mb ) ) key |= 4 ;
              sccol[b][a] = key ; }} 
  screencapt[0] = '\0' ; 
  win_refresh () ;
} 


int cellwid = 12 , cellhei = 12 ; 
extern int bthick ; 

HBRUSH fillcol[32] ;
HBRUSH consfillcol[32] ;


void save_one_color ( HBRUSH thisbrush , FILE * to )
{   LOGBRUSH brushinfo ; 
    int curcolis , redis , greenis , blueis ;
    GetObject ( thisbrush , sizeof ( LOGBRUSH ) , &brushinfo ) ; 
    curcolis = brushinfo.lbColor ;
    redis = curcolis & 255 ; 
    greenis = ( curcolis & ( 255 << 8 ) ) >> 8 ; 
    blueis = ( curcolis & ( 255 << 16 ) ) >> 16 ;
    fprintf ( to , "%c%c%c" , redis ,greenis , blueis ) ;
    return ;
}

void save_color_codes ( void )
{
    FILE * colfile ;
    if ( !nited ) return ;
    if ( black_n_white ) return ; 
    GetWindowsDirectory ( filename , MAX_PATH ) ;
    strcat ( filename,"\\vndm_colors.ini") ;
    colfile = fopen ( filename,"wb") ;
    save_one_color ( fillcol[ 1 | 2 | 4 ] , colfile ) ; 
    save_one_color ( fillcol[     2 | 4 ] , colfile ) ; 
    save_one_color ( fillcol[ 1 |     4 ] , colfile ) ; 
    save_one_color ( fillcol[ 1 | 2     ] , colfile ) ; 
    save_one_color ( fillcol[     2     ] , colfile ) ; 
    save_one_color ( fillcol[         4 ] , colfile ) ; 
    save_one_color ( fillcol[ 1         ] , colfile ) ; 
    save_one_color ( fillcol[   0       ] , colfile ) ; 
    save_one_color ( fillcol[    8      ] , colfile ) ;
    fclose ( colfile ) ;
    GetWindowsDirectory ( filename , MAX_PATH ) ;
    strcat ( filename,"\\vndm_conscolors.ini") ;
    colfile = fopen ( filename,"wb") ;
    save_one_color ( consfillcol[ 1 | 2 | 4 ] , colfile ) ; 
    save_one_color ( consfillcol[     2 | 4 ] , colfile ) ; 
    save_one_color ( consfillcol[ 1 |     4 ] , colfile ) ; 
    save_one_color ( consfillcol[ 1 | 2     ] , colfile ) ; 
    save_one_color ( consfillcol[     2     ] , colfile ) ; 
    save_one_color ( consfillcol[         4 ] , colfile ) ; 
    save_one_color ( consfillcol[ 1         ] , colfile ) ; 
    save_one_color ( consfillcol[   0       ] , colfile ) ; 
    save_one_color ( consfillcol[    8      ] , colfile ) ;
    fclose ( colfile ) ;
    return ; 
}    

HBRUSH read_one_color ( FILE * frm )
{
    int rd , gr , bl ;
    rd = getc ( frm ) ; 
    gr = getc ( frm ) ; 
    bl = getc ( frm ) ;
    return CreateSolidBrush ( RGB ( rd , gr , bl  ) ) ; 
}

int read_saved_colors ( HBRUSH * myfillcol )
{
    FILE * colfile ; 
    GetWindowsDirectory ( filename , MAX_PATH ) ;
    if ( myfillcol == fillcol ) 
         strcat ( filename,"\\vndm_colors.ini") ;
    else strcat ( filename,"\\vndm_conscolors.ini") ;
    colfile = fopen ( filename,"rb") ;
    if ( colfile == NULL ) return 0 ; 
    myfillcol[ 1 | 2 | 4 ] = read_one_color ( colfile ) ; 
    myfillcol[     2 | 4 ] = read_one_color ( colfile ) ; 
    myfillcol[ 1 |     4 ] = read_one_color ( colfile ) ; 
    myfillcol[ 1 | 2     ] = read_one_color ( colfile ) ; 
    myfillcol[     2     ] = read_one_color ( colfile ) ; 
    myfillcol[         4 ] = read_one_color ( colfile ) ; 
    myfillcol[ 1         ] = read_one_color ( colfile ) ; 
    myfillcol[   0       ] = read_one_color ( colfile ) ; 
    myfillcol[    8      ] = read_one_color ( colfile ) ; 
    return 1 ;
}    

void reset_cell_colors ( void )
{
   if ( !sure ( "Sure you want to re-set\ncell colors to defaults" ) ) return ; 
   reset_fillcolors ( 0 ) ;
}    

void reset_fillcolors ( int all )
{
    if ( curcmd_loop != show_consensus || all ) {
      DeleteObject ( fillcol[ 1 | 2 | 4 ] ) ; 
      DeleteObject ( fillcol[     2 | 4 ] ) ; 
      DeleteObject ( fillcol[ 1 |     4 ] ) ; 
      DeleteObject ( fillcol[ 1 | 2     ] ) ; 
      DeleteObject ( fillcol[     2     ] ) ; 
      DeleteObject ( fillcol[         4 ] ) ; 
      DeleteObject ( fillcol[ 1         ] ) ; 
      DeleteObject ( fillcol[   0       ] ) ; 
      DeleteObject ( fillcol[    8      ] ) ; 
      DeleteObject ( consfillcol[ 1 | 2 | 4 ] ) ; 
      set_fillcol ( 1 , fillcol ) ; }
    if ( curcmd_loop == show_consensus || all ) {
      DeleteObject ( consfillcol[     2 | 4 ] ) ; 
      DeleteObject ( consfillcol[ 1 |     4 ] ) ; 
      DeleteObject ( consfillcol[ 1 | 2     ] ) ; 
      DeleteObject ( consfillcol[     2     ] ) ; 
      DeleteObject ( consfillcol[         4 ] ) ; 
      DeleteObject ( consfillcol[ 1         ] ) ; 
      DeleteObject ( consfillcol[   0       ] ) ; 
      DeleteObject ( consfillcol[    8      ] ) ; 
      set_fillcol ( 1 , consfillcol ) ; }
}


HBITMAP density_bmp[8] ;
HBITMAP fill_bmp[8] ;


void initialize_fill_bitmaps ( void )
{
    int a ;
    for ( a = 0 ; a < 8 ; ++ a )
      density_bmp[a] = LoadBitmap ( hInst , MAKEINTRESOURCE ( a ) ) ;
    for ( a = 0 ; a < 8 ; ++ a )
      fill_bmp[a] = LoadBitmap ( hInst , MAKEINTRESOURCE ( 10+a ) ) ;
}
    
void set_fillcol ( int forcit , HBRUSH * myfillcol )
{
    int a ;
    if ( !forcit && read_saved_colors (  myfillcol ) ) return ; 
    if ( black_n_white ) {
     if ( myfillcol == fillcol ) 
       for ( a = 0 ; a < 8 ; ++ a )
           myfillcol[a] = CreatePatternBrush ( fill_bmp[a] ) ;
     else
       for ( a = 0 ; a < 8 ; ++ a )
         myfillcol[a] = CreatePatternBrush ( density_bmp[a] ) ; }
    else 
    if ( myfillcol == fillcol ) {
      myfillcol[ 1 | 2 | 4 ] = CreateSolidBrush ( RGB ( 0 , 0 , 0 ) ) ;    
      myfillcol[     2 | 4 ] = CreateSolidBrush ( RGB ( 0 , 255 , 255 ) ) ;  
      myfillcol[ 1 |     4 ] = CreateSolidBrush ( RGB ( 0 , 255 , 0 ) ) ;     // in, ass
      myfillcol[ 1 | 2     ] = CreateSolidBrush ( RGB ( 160 , 0 , 150 ) ) ;   // in, pres
      myfillcol[     2     ] = CreateSolidBrush ( RGB ( 0 , 0 , 210 ) ) ;     // out, pres
      myfillcol[         4 ] = CreateSolidBrush ( RGB ( 140 , 220 , 255 ) ) ; // out, ass
      myfillcol[ 1         ] = CreateSolidBrush ( RGB ( 255 , 0 , 0 ) ) ;     // in, abs
      myfillcol[   0       ] = CreateSolidBrush ( RGB ( 150, 180 , 0 ) ) ; } // just ground
    else {
      myfillcol[ 0 ] = CreateSolidBrush ( RGB ( 200 , 180 , 0 ) ) ;    
      myfillcol[ 1 ] = CreateSolidBrush ( RGB ( 255 , 220 , 220 ) ) ;    
      myfillcol[ 2 ] = CreateSolidBrush ( RGB ( 255 , 180 , 180 ) ) ;    
      myfillcol[ 3 ] = CreateSolidBrush ( RGB ( 255 , 140 , 140 ) ) ;    
      myfillcol[ 4 ] = CreateSolidBrush ( RGB ( 255 , 90 , 90 ) ) ;    
      myfillcol[ 5 ] = CreateSolidBrush ( RGB ( 255 , 0 , 0 ) ) ;    
      myfillcol[ 6 ] = CreateSolidBrush ( RGB ( 210 , 0 , 0 ) ) ;    
      myfillcol[ 7 ] = CreateSolidBrush ( RGB ( 150 , 0 , 0 ) ) ; }
    myfillcol[    8      ] = CreateSolidBrush ( RGB ( 255 , 255 , 255 ) ) ; 
}

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


void SpinAccel ( HWND hctrl , int frst , int secd )
{
    UDACCEL acel[3] ; 
    acel[0].nSec = 0 ; 
    acel[0].nInc = frst ; 
    acel[1].nSec = 2 ; 
    acel[1].nInc = secd ;
    acel[2].nSec = 4 ; 
    acel[2].nInc = secd ;
    SendMessage( hctrl , UDM_SETACCEL, 3 , acel ) ; 
} 


BOOL CALLBACK LastPointModeFunc(HWND hdwnd, UINT message, WPARAM wParam, LPARAM lParam)
{
    static int i , j ;
    HWND hWho ;
    int curcolis ; 
    switch(message) {
        case WM_INITDIALOG :
          i = last_point_extend ;
          if ( i ) BUTT_CHECK( 103 ) ;
          else BUTT_CHECK( 102 ) ; 
          break ; 
        case WM_COMMAND :
                switch(LOWORD(wParam)){
                        case 103 : i = 1 ; break ;
                        case 102 : i = 0 ; break ; 
                        case IDOK :
                           last_point_extend = i ; 
                           EndDialog ( hdwnd, 1 ) ;
                           return 1 ; 
                        case IDCANCEL :
                                EndDialog(hdwnd,0);
                                return 0;
                        default : break; }
         break; }
    return 0;
}


BOOL CALLBACK SetColorFunc(HWND hdwnd, UINT message, WPARAM wParam, LPARAM lParam)
{
    int i , j , redis , greenis , blueis ;
    static int nitr , nitg , nitb ; 
    LOGBRUSH brushinfo ; 
    HWND hWho ;
    static HDC wash ; 
    PAINTSTRUCT paintstruct;
    static HANDLE curbrush ;
    int curcolis ; 
    switch(message) {
        case WM_INITDIALOG :
          GetObject ( brushtoset , sizeof ( LOGBRUSH ) , &brushinfo ) ; 
          curcolis = brushinfo.lbColor ;
          redis = curcolis & 255 ; 
          greenis = ( curcolis & ( 255 << 8 ) ) >> 8 ; 
          blueis = ( curcolis & ( 255 << 16 ) ) >> 16 ;
          nitr = redis ;
          nitg = greenis ;
          nitb = blueis ; 
          SET_UPDOWN ( 101 , 0 , 255 , redis ) ; 
          SET_UPDOWN ( 103 , 0 , 255 , greenis ) ; 
          SET_UPDOWN ( 105 , 0 , 255 , blueis ) ;
          SpinAccel ( GetDlgItem ( hdwnd , 101 ) , 10 , 10 ) ; 
          SpinAccel ( GetDlgItem ( hdwnd , 103 ) , 10 , 10 ) ; 
          SpinAccel ( GetDlgItem ( hdwnd , 105 ) , 10 , 10 ) ; 
          curbrush = CreateSolidBrush ( RGB ( redis , greenis , blueis ) ) ;   
          break ; 
       case WM_PAINT :
           wash = BeginPaint( hdwnd, &paintstruct);
           SelectObject ( wash , curbrush ) ; 
           Rectangle ( wash , 200 , 60 , 240 , 100 ) ; 
           EndPaint( hdwnd, &paintstruct);
           break ;
       case WM_VSCROLL :
           GETINT ( redis , 100 ) ; 
           GETINT ( greenis , 102 ) ; 
           GETINT ( blueis , 104 ) ;
           DeleteObject ( curbrush ) ; 
           curbrush = CreateSolidBrush ( RGB ( redis , greenis , blueis ) ) ;   
           InvalidateRect ( hdwnd , NULL , 1 ) ;
           break ;
        case WM_COMMAND :
                switch(LOWORD(wParam)){
                        case IDOK :
                           GETINT ( redis , 100 ) ; 
                           GETINT ( greenis , 102 ) ; 
                           GETINT ( blueis , 104 ) ;
                           DeleteObject ( curbrush  ) ; 
                           DeleteObject ( brushtoset ) ; 
                           brushtoset = CreateSolidBrush ( RGB ( redis , greenis , blueis ) ) ;   
                           EndDialog ( hdwnd, 1 ) ;
                           return 1 ; 
                        case IDCANCEL :
                                DeleteObject ( curbrush  ) ; 
                                EndDialog(hdwnd,0);
                                return 0;
                        default :
                                break; }
         break; }
    return 0;
}

void setcolorcode ( int which )
{
    int x ; 
    if ( curcmd_loop == show_consensus ) 
         brushtoset = consfillcol [ which ] ;
    else brushtoset = fillcol [ which ] ;
    x = DialogBox (hInst, "SetColorDB", hwnd, (DLGPROC) SetColorFunc ) ; 
    if ( !x ) return ; 
    if ( curcmd_loop == show_consensus ) {
       DeleteObject ( consfillcol [ which ] ) ;
       consfillcol[ which ] = brushtoset ; }
    else {
       DeleteObject ( fillcol [ which ] ) ;
       fillcol[ which ] = brushtoset ; }
    win_refresh () ; 
    return ;
}

int showingx , showingy ;

void showcolorcode ( HDC myhdc , int value , char * txt )
{
   if ( curcmd_loop == show_consensus ) 
        SelectObject ( myhdc , consfillcol[ value ] ) ;
   else SelectObject ( myhdc , fillcol[ value ] ) ; 
   Rectangle ( myhdc , showingx , showingy , showingx+cellwid , showingy+cellhei ) ;     
   TextOut ( myhdc , showingx + 10 + cellwid , showingy - 2 , txt , strlen ( txt ) ) ;
   showingy += ( cellhei * 3 ) / 2 ; 
}    


/****  THESE ARE VARIABLES USED IN SCOPE READING FUNCTION, BELOW *************/
#define SELECT_DIALOG StartSelectFun ( hdwnd )  
char selthings [ Namesize ] , unselthings [ Namesize ] ;
char ** selthingnames ;
extern signed char * inortax ; 
int selnumthings ;
int * tmpcurlist ; 
char * selectlist ;
char itemnamespace [Namesize];
char * itemname;
#define TOGGLE(x)  x = 1 - x ; 

/************END OF VARIABLES FOR SCOPE READING FUNCTION ********/

/*****  THIS A SCOPE READING FUNCTION ... goes all the way to "end of scope reading"  ****/

void nametheitem ( int a )
{
    if ( selthingnames && selthingnames[ a ] ) itemname = selthingnames[a] ;
    else {
        itemname = itemnamespace ;
        sprintf ( itemname , "%i" , a ) ; } 
}

int prepare_selmem ()
{ int a ;
  a = spp ;
  if ( tmpcurlist != NULL && selectlist != NULL ) return 1 ; 
  tmpcurlist = malloc ( a * sizeof ( int ) ) ; 
  selectlist = malloc ( a * sizeof ( char ) ) ;
  if ( tmpcurlist == NULL || selectlist == NULL ) return 0 ;
  for ( a = spp ; a -- ; ) selectlist[a] = 0 ; 
  return 1 ; 
} 

int invert_nodsel ; 

void prepare_selection ( unsigned long int * myact , 
            char * thgs , char * unthgs , char ** thgnams, int numthgs )
{   int a ; 
    strcpy ( selthings, thgs ) ;
    strcpy ( unselthings , unthgs ) ; 
    selthingnames = thgnams ;
    selnumthings = numthgs ;
    for ( a = numthgs ; a-- ; ) {
        if ( ( myact[a/32] & ( 1 << ( a % 32 ) ) ) ) 
             tmpcurlist [ a ] = selectlist [ a ] = 0 ;
        else tmpcurlist [ a ] = selectlist [ a ] = 1 ; }
    invert_nodsel = 0 ; 
}

int namtrun ( char * a , char * b )
{  // is A a trunc of B ??
   while ( tolower ( * a ) == tolower ( * b ) && * a ) { ++ a ; ++ b ; }
   if ( * a ) return 0 ;
   return 1 ; 
}

BOOL CALLBACK SelectFunc(HWND hdwnd, UINT message, WPARAM wParam, LPARAM lParam )  
{
  static HWND hselwnd , hunselwnd , hWho ;
  int a , b , n , i , insel, inunsel , isdash ;
  int selitems , x , y , last ;
  static int block_intersect ; 
  char * strg ;
  char * cp , * cpp ; 
  switch(message) {
          case WM_INITDIALOG :
             hselwnd= GetDlgItem ( hdwnd , 105 ) ; 
             hunselwnd= GetDlgItem ( hdwnd , 106 ) ;
             insel = inunsel = 0 ;
             if ( selnumthings > 100 ) {
                   if ( selthingnames ) { 
                        SendMessage ( hselwnd , LB_INITSTORAGE , selnumthings, selnumthings * Namesize ) ; 
                        SendMessage ( hselwnd , LB_INITSTORAGE , selnumthings, selnumthings * Namesize ) ;  
                        SendMessage ( hunselwnd , LB_INITSTORAGE , selnumthings, selnumthings * Namesize ) ; 
                        SendMessage ( hunselwnd , LB_INITSTORAGE , selnumthings, selnumthings * Namesize ) ; } 
                   else { 
                        SendMessage ( hselwnd , LB_INITSTORAGE , selnumthings, selnumthings * 5 ) ; 
                        SendMessage ( hselwnd , LB_INITSTORAGE , selnumthings, selnumthings * 5 ) ; 
                        SendMessage ( hunselwnd , LB_INITSTORAGE , selnumthings, selnumthings * 5 ) ; 
                        SendMessage ( hunselwnd , LB_INITSTORAGE , selnumthings, selnumthings * 5 ) ; }}
             for ( a = 0 ; a < selnumthings ; a ++ ) {
                 if ( !selectlist [ a ] ) {
                         nametheitem ( a ) ; 
                         ListBox_InsertString ( hunselwnd , inunsel , itemname ) ;
                         ListBox_SetItemData ( hunselwnd , inunsel , a ) ; 
                         inunsel ++ ; }
                 if ( selectlist [ a ] == 1 ) { 
                         nametheitem ( a ) ; 
                         ListBox_InsertString ( hselwnd , insel , itemname ) ;
                         ListBox_SetItemData ( hselwnd , insel , a ) ; 
                         insel ++ ; }}
             wsprintf( junkstr, "%i %s", insel, selthings ) ; 
             SetDlgItemText(hdwnd, 107, junkstr);
             wsprintf ( junkstr, "%i %s", inunsel, unselthings ) ; 
             SetDlgItemText(hdwnd, 108, junkstr);
             SetWindowRedraw ( hunselwnd , TRUE ) ; 
             SetWindowRedraw ( hselwnd , TRUE ) ;
             InvalidateRect ( hunselwnd , NULL , TRUE ) ; 
             InvalidateRect ( hselwnd , NULL , TRUE ) ;
             resize_select_dialog ( hdwnd , 0 , 0 ) ; 
             FOCUS_ON (IDOK ) ; 
             break;

         case WM_SIZE :
             resize_select_dialog ( hdwnd , 1 , 0 ) ;
             break ; 
             
          case WM_COMMAND :

                 switch ( HIWORD ( wParam )) {  
                    case LBN_DBLCLK : //   first move to "selected", then to "unselected"
                           selitems = SendMessage ( hunselwnd , LB_GETSELITEMS , selnumthings, tmpcurlist ) ;
                           SetWindowRedraw ( hunselwnd , FALSE ) ; 
                           SetWindowRedraw ( hselwnd , FALSE ) ;
                           y = ListBox_GetCount ( hselwnd ) ;
                           b = 0 ; 
                           for ( a = 0 ; a < selitems ; a ++ ) {
                                 x = ListBox_GetItemData ( hunselwnd , tmpcurlist[a] ) ;
                                 nametheitem ( x ) ; 
                                 for (  ; b < y ; ++ b ) 
                                       if ( x < ListBox_GetItemData ( hselwnd , b ) ) break ;
                                 ListBox_InsertString ( hselwnd , b , itemname ) ;
                                 ListBox_SetItemData ( hselwnd , b , x ) ;
                                 ++ y ;  ++b ; }
                           for ( a = selitems ; a-- ; ) 
                                 ListBox_DeleteString ( hunselwnd , tmpcurlist[a] ) ; 
                           selitems = SendMessage ( hselwnd , LB_GETSELITEMS , selnumthings, tmpcurlist ) ;
                           y = ListBox_GetCount ( hunselwnd ) ;
                           b = 0 ; 
                           for ( a = 0 ; a < selitems ; a ++ ) {
                                 x = ListBox_GetItemData ( hselwnd , tmpcurlist[a] ) ;
                                 nametheitem ( x ) ; 
                                 for (  ; b < y ; ++ b ) 
                                       if ( x < ListBox_GetItemData ( hunselwnd , b ) ) break ;
                                 ListBox_InsertString ( hunselwnd , b , itemname ) ;
                                 ListBox_SetItemData ( hunselwnd , b , x ) ;
                                 ++ y ;  ++b ; }
                           for ( a = selitems ; a-- ; ) 
                                 ListBox_DeleteString ( hselwnd , tmpcurlist[a] ) ; 
                           SetWindowRedraw ( hunselwnd , TRUE ) ; 
                           SetWindowRedraw ( hselwnd , TRUE ) ;
                           insel = ListBox_GetCount ( hselwnd ) ;
                           inunsel = ListBox_GetCount ( hunselwnd ) ;
                           InvalidateRect ( hunselwnd , NULL , TRUE ) ; 
                           InvalidateRect ( hselwnd , NULL , TRUE ) ;
                           wsprintf( junkstr, "%i %s", insel, selthings ) ; 
                           SetDlgItemText(hdwnd, 107, junkstr);
                           wsprintf ( junkstr, "%i %s", inunsel, unselthings ) ; 
                           SetDlgItemText(hdwnd, 108, junkstr);
                           break ;
                      default: break ; } 
              switch(LOWORD(wParam)){
                        case 112 : // invert selection
                           SetWindowRedraw ( hunselwnd , FALSE ) ; 
                           SetWindowRedraw ( hselwnd , FALSE ) ;
                           selitems = ListBox_GetCount ( hselwnd ) ; 
                           y = ListBox_GetCount ( hunselwnd ) ;
                           for ( a = 0 ; a < selitems ; a ++ ) {
                                 x = ListBox_GetItemData ( hselwnd , a ) ;
                                 nametheitem ( x ) ; 
                                 ListBox_InsertString ( hunselwnd , a , itemname ) ;
                                 ListBox_SetItemData ( hunselwnd , a , x ) ; } 
                           for ( a = selitems ; a -- ; )  
                                 ListBox_DeleteString ( hselwnd , 0 ) ;
                           b = selitems ;       
                           for ( a = 0 ; a < y ; a ++ ) {
                                 x = ListBox_GetItemData ( hunselwnd , b ) ;
                                 nametheitem ( x ) ; 
                                 ListBox_InsertString ( hselwnd , a , itemname ) ;
                                 ListBox_SetItemData ( hselwnd , a , x ) ;
                                 ++ b ; } 
                           for ( a = y ; a -- ; ) 
                                 ListBox_DeleteString ( hunselwnd , selitems ) ;
                           SetWindowRedraw ( hunselwnd , TRUE ) ; 
                           SetWindowRedraw ( hselwnd , TRUE ) ;
                           insel = ListBox_GetCount ( hselwnd ) ;
                           inunsel = ListBox_GetCount ( hunselwnd ) ;
                           InvalidateRect ( hunselwnd , NULL , TRUE ) ; 
                           InvalidateRect ( hselwnd , NULL , TRUE ) ;
                           wsprintf( junkstr, "%i %s", insel, selthings ) ; 
                           SetDlgItemText(hdwnd, 107, junkstr);
                           wsprintf ( junkstr, "%i %s", inunsel, unselthings ) ; 
                           SetDlgItemText(hdwnd, 108, junkstr);
                           break ; 

                        case 110 : // Move to "selected"
                           GetDlgItemText ( hdwnd , 111 , junkstr , Namesize ) ;
                           if ( !strlen ( junkstr )) 
                                selitems = SendMessage ( hunselwnd , LB_GETSELITEMS , selnumthings, tmpcurlist ) ;
                           else {
                               y = ListBox_GetCount ( hunselwnd ) ;
                               if ( isdigit ( junkstr [ 0 ] ) ) {
                                  cp = junkstr ;
                                  selitems = 0 ; 
                                  last = 0 ; 
                                  while ( isdigit ( * cp ) || * cp == '-' ) {
                                      cpp = cp ;
                                      isdash = 0 ; 
                                      if ( * cpp == '-' ) {
                                          isdash = 1 ;
                                          ++ cpp ; 
                                          while ( isspace ( * cpp ) && * cpp ) ++ cpp ;
                                          cp = cpp ; 
                                          if ( !isdigit ( * cpp ) ) {
                                              noisy() ; 
                                              wsprintf ( junkstr , "Ranges must have TWO numbers separated by a dash" ) ; 
                                              MessageBox(hdwnd, junkstr ,"ERROR",MB_OK | MB_ICONERROR ); 
                                              break ; }}
                                      while ( isdigit ( * cpp ) ) ++ cpp ;
                                      x = * cpp ;
                                      * cpp = 0 ;
                                      a = atoi ( cp ) ;
                                      if ( isdash && a < last ) {
                                          n = a ;
                                          a = last ;
                                          last = n ; }
                                      * cpp = x ;
                                      cp = cpp ;
                                      while ( isspace ( * cp ) && * cp ) ++ cp ;
                                      if ( * cp == '-' ) { last = a ; continue ; }
                                      if ( a >= selnumthings ) {
                                          noisy() ; 
                                          wsprintf ( junkstr , "Only %i items (0-%i) to select from!", selnumthings , selnumthings-1 ) ; 
                                          MessageBox(hdwnd, junkstr ,"ERROR",MB_OK | MB_ICONERROR ); break ; }
                                      if ( !isdash ) {
                                         n = 0 ; 
                                         for ( b = y ; b -- ; ) if ( ListBox_GetItemData ( hunselwnd , b ) == a ) { n = 1 ; break ; }
                                         if ( n ) tmpcurlist [ selitems ++ ] = b ;
                                         else { wsprintf ( junkstr , "Item %i is already selected", a ) ; 
                                                noisy() ; 
                                                MessageBox(hdwnd, junkstr ,"ERROR",MB_OK | MB_ICONERROR ); break ; }}
                                      else {
                                          for ( i = last ; i <= a ; ++ i ) {
                                              n = 0 ; 
                                              for ( b = y ; b -- ; ) if ( ListBox_GetItemData ( hunselwnd , b ) == i ) { n = 1 ; break ; }
                                              if ( n ) tmpcurlist [ selitems ++ ] = b ;
                                              else { wsprintf ( junkstr , "Item %i is already selected", i ) ; 
                                                     noisy() ; 
                                                     MessageBox(hdwnd, junkstr ,"ERROR",MB_OK | MB_ICONERROR ); break ; }}}}  
                                    }
                               else {
                                   selitems = 0 ; 
                                   for ( b = 0 ; b < y ; ++ b ) {
                                       x = ListBox_GetItemData ( hunselwnd, b ) ;
                                       nametheitem ( x ) ;
                                       if ( namtrun ( junkstr , itemname ) )
                                                tmpcurlist [ selitems ++ ] = b ; }
                                   if ( !selitems ) {
                                      noisy() ; 
                                      MessageBox(hdwnd, "Name doesn't match any unselected item" ,"ERROR",MB_OK | MB_ICONERROR );
                                      break ; }}
                              SetDlgItemText(hdwnd, 111, ""); }
                           SetWindowRedraw ( hunselwnd , FALSE ) ; 
                           SetWindowRedraw ( hselwnd , FALSE ) ;
                           y = ListBox_GetCount ( hselwnd ) ;
                           b = 0 ; 
                           for ( a = 0 ; a < selitems ; a ++ ) {
                                 x = ListBox_GetItemData ( hunselwnd , tmpcurlist[a] ) ;
                                 nametheitem ( x ) ; 
                                 for (  ; b < y ; ++ b ) 
                                       if ( x < ListBox_GetItemData ( hselwnd , b ) ) break ;
                                 ListBox_InsertString ( hselwnd , b , itemname ) ;
                                 ListBox_SetItemData ( hselwnd , b , x ) ;
                                 ++ y ;  ++b ; }
                           for ( a = selitems ; a-- ; ) 
                                 ListBox_DeleteString ( hunselwnd , tmpcurlist[a] ) ; 
                           SetWindowRedraw ( hunselwnd , TRUE ) ; 
                           SetWindowRedraw ( hselwnd , TRUE ) ;
                           insel = ListBox_GetCount ( hselwnd ) ;
                           inunsel = ListBox_GetCount ( hunselwnd ) ;
                           InvalidateRect ( hunselwnd , NULL , TRUE ) ; 
                           InvalidateRect ( hselwnd , NULL , TRUE ) ;
                           wsprintf( junkstr, "%i %s", insel, selthings ) ; 
                           SetDlgItemText(hdwnd, 107, junkstr);
                           wsprintf ( junkstr, "%i %s", inunsel, unselthings ) ; 
                           SetDlgItemText(hdwnd, 108, junkstr);
                           FOCUS_ON ( 111 ) ; 
                           break ; 
                        case 109 : // Move to "un-selected"
                           GetDlgItemText ( hdwnd , 111 , junkstr , Namesize ) ;
                           if ( !strlen ( junkstr )) 
                                selitems = SendMessage ( hselwnd , LB_GETSELITEMS , selnumthings, tmpcurlist ) ;
                           else {
                               y = ListBox_GetCount ( hselwnd ) ;
                               if ( isdigit ( junkstr [ 0 ] ) ) {
                                  cp = junkstr ;
                                  selitems = 0 ; 
                                  last = 0 ; 
                                  while ( isdigit ( * cp ) || * cp == '-' ) {
                                      cpp = cp ;
                                      isdash = 0 ; 
                                      if ( * cpp == '-' ) {
                                          isdash = 1 ;
                                          ++ cpp ; 
                                          while ( isspace ( * cpp ) && * cpp ) ++ cpp ;
                                          cp = cpp ; 
                                          if ( !isdigit ( * cpp ) ) {
                                              noisy() ; 
                                              wsprintf ( junkstr , "Ranges must have TWO numbers separated by a dash" ) ; 
                                              MessageBox(hdwnd, junkstr ,"ERROR",MB_OK | MB_ICONERROR ); 
                                              break ; }}
                                      while ( isdigit ( * cpp ) ) ++ cpp ;
                                      x = * cpp ;
                                      * cpp = 0 ;
                                      a = atoi ( cp ) ;
                                      if ( isdash && a < last ) {
                                          n = a ;
                                          a = last ;
                                          last = n ; }
                                      * cpp = x ;
                                      cp = cpp ;
                                      while ( isspace ( * cp ) && * cp ) ++ cp ;
                                      if ( * cp == '-' ) { last = a ; continue ; }
                                      if ( a >= selnumthings ) {
                                          noisy() ; 
                                          wsprintf ( junkstr , "Only %i items (0-%i) to select from!", selnumthings , selnumthings-1 ) ; 
                                          MessageBox(hdwnd, junkstr ,"ERROR",MB_OK | MB_ICONERROR ); break ; }
                                      if ( !isdash ) {
                                         n = 0 ; 
                                         for ( b = y ; b -- ; ) if ( ListBox_GetItemData ( hselwnd , b ) == a ) { n = 1 ; break ; }
                                         if ( n ) tmpcurlist [ selitems ++ ] = b ;
                                         else { wsprintf ( junkstr , "Item %i is already un-selected", a ) ; 
                                                noisy() ; 
                                                MessageBox(hdwnd, junkstr ,"ERROR",MB_OK | MB_ICONERROR ); break ; }}
                                      else {
                                          for ( i = last ; i <= a ; ++ i ) {
                                              n = 0 ; 
                                              for ( b = y ; b -- ; ) if ( ListBox_GetItemData ( hselwnd , b ) == i ) { n = 1 ; break ; }
                                              if ( n ) tmpcurlist [ selitems ++ ] = b ;
                                              else { wsprintf ( junkstr , "Item %i is already selected", i ) ; 
                                                     noisy() ; 
                                                     MessageBox(hdwnd, junkstr ,"ERROR",MB_OK | MB_ICONERROR ); break ; }}}}}
                               else {
                                   selitems = 0 ; 
                                   for ( b = 0 ; b < y ; ++ b ) {
                                       x = ListBox_GetItemData ( hselwnd, b ) ;
                                       nametheitem ( x ) ;
                                       if ( namtrun ( junkstr , itemname ) )
                                                tmpcurlist [ selitems ++ ] = b ; }
                                   if ( !selitems ) {
                                      noisy() ; 
                                      MessageBox(hdwnd, "Name doesn't match any selected item" ,"ERROR",MB_OK | MB_ICONERROR );
                                      break ; }}
                               SetDlgItemText(hdwnd, 111, ""); }
                           SetWindowRedraw ( hunselwnd , FALSE ) ; 
                           SetWindowRedraw ( hselwnd , FALSE ) ;
                           y = ListBox_GetCount ( hunselwnd ) ;
                           b = 0 ; 
                           for ( a = 0 ; a < selitems ; a ++ ) {
                                 x = ListBox_GetItemData ( hselwnd , tmpcurlist[a] ) ;
                                 nametheitem ( x ) ; 
                                 for (  ; b < y ; ++ b ) 
                                       if ( x < ListBox_GetItemData ( hunselwnd , b ) ) break ;
                                 ListBox_InsertString ( hunselwnd , b , itemname ) ;
                                 ListBox_SetItemData ( hunselwnd , b , x ) ;
                                 ++ y ;  ++b ; }
                           for ( a = selitems ; a-- ; ) 
                                 ListBox_DeleteString ( hselwnd , tmpcurlist[a] ) ; 
                           SetWindowRedraw ( hunselwnd , TRUE ) ; 
                           SetWindowRedraw ( hselwnd , TRUE ) ;
                           insel = ListBox_GetCount ( hselwnd ) ;
                           inunsel = ListBox_GetCount ( hunselwnd ) ;
                           InvalidateRect ( hunselwnd , NULL , TRUE ) ; 
                           InvalidateRect ( hselwnd , NULL , TRUE ) ;
                           wsprintf( junkstr, "%i %s", insel, selthings ) ; 
                           SetDlgItemText(hdwnd, 107, junkstr);
                           wsprintf ( junkstr, "%i %s", inunsel, unselthings ) ; 
                           SetDlgItemText(hdwnd, 108, junkstr);
                           FOCUS_ON ( 111 ) ; 
                           break ; 
                        case IDOK :
                           insel = ListBox_GetCount ( hselwnd ) ;
                           for ( a = selnumthings ; a-- ; ) selectlist [ a ] = 0 ; 
                           for ( b = insel ; b -- ; ) 
                               selectlist [ ListBox_GetItemData ( hselwnd , b ) ] = 1 ;  
                           EndDialog ( hdwnd, 1 ) ;
                           break ; 
                        case IDCANCEL: 
                           EndDialog ( hdwnd, 0 ) ;
                           break ; 
                        default :
                           break;
                }
         break; }
    return 0;
}

extern char ** spname ;

int StartSelectFun( HWND hdwnd )
{
    int setto , a , b ;
    short int * vt ;
    a = DialogBox ( hInst, "Selectdb", hdwnd , (DLGPROC) SelectFunc ) ;
    if ( a ) {
      for ( a = 0 ; a < spp ; ++ a )
           if ( !selectlist[a] )
                spact[a/32] |= 1 << ( a % 32 ) ;
           else spact[a/32] &= ~ ( 1 << ( a % 32 ) ) ;
      doallscores () ; }
    curcmd_loop = cmd_loop ;
    showcurset () ; 
    return ;
} 

void taxon_selfun( void )
{
    prepare_selmem () ; 
    prepare_selection ( spact , "Inactive species" , "Active species" , spname , spp ) ;
    StartSelectFun ( hwnd ) ;
    return ;
}


int StartSpingridFun( HWND hdwnd )
{
    int setto , a , b ;
    short int * vt ;
    a = DialogBox ( hInst, "Selectdb", hdwnd , (DLGPROC) SelectFunc ) ;
    if ( a ) {
      num_spingrid = 0 ; 
      for ( a = 0 ; a < spp ; ++ a )
           if ( !selectlist[a] ) {
                spingrid[a/32] |= 1 << ( a % 32 ) ;
                ++ num_spingrid ; }
           else spingrid[a/32] &= ~ ( 1 << ( a % 32 ) ) ; }
    return ;
} 

void spingrid_selfun( void )
{
    prepare_selmem () ; 
    prepare_selection ( spingrid , "Inactive species" , "Active species" , spname , spp ) ;
    StartSpingridFun ( hwnd ) ;
    return ;
}


int32 * given_spp = NULL ; 

void find_sets_for_given_species ( int is_text  )
{
    int a , i ; 
    if ( given_spp == NULL )
        given_spp = ( int32 * ) mymem ( spcells * sizeof ( int32 ) ) ;
    for ( i = spcells ; i -- ; ) given_spp [ i ] = -1 ; 
    prepare_selmem () ; 
    prepare_selection ( given_spp , "Species in List" , "Not in list" , spname , spp ) ;
    a = DialogBox ( hInst , "Selectdb", hwnd , (DLGPROC) SelectFunc ) ;
    if ( a ) {
      for ( i = spcells ; i -- ; ) given_spp [ i ] = 0 ; 
      for ( a = i = 0 ; a < spp ; ++ a )
           if ( selectlist[a] ) { 
                given_spp [a/32] |= 1 << ( a % 32 ) ;
                ++ i ; }
           else given_spp [a/32] &= ~ ( 1 << ( a % 32 ) ) ; 
      seek_sets_for_given_spp ( is_text ) ; }
    return ;
}

typedef struct {
            int defd ; 
            int numrecs , trurecs ;
            float * x ;
            float * y ; } Coordtyp ; 
extern Coordtyp * xymatrix ;


double set_autosizegrid ( void )
{
    double dadis , closest , totsum = 0 ;
    int a , b , c , d ;
    unsigned long int nure = 0 ;
    double basx , basy ; 
    for ( a = 0 ; a < spp ; ++ a ) {
       if ( xymatrix[a].numrecs < 2 ) continue ; 
       for ( b = xymatrix[a].numrecs ; b -- ; ) {
          basx = xymatrix[a].x[b] ;
          basy = xymatrix[a].y[b] ;
          closest = 1000000000 ; 
          for ( d = xymatrix[a].numrecs ; d -- ; ) {
                   if ( b == d ) continue ; 
                   dadis = pow ( ( pow ( ( basx - xymatrix[a].x[d] ) , 2 ) + pow ( ( basy - xymatrix[a].y[d] ) , 2 ) ) , 0.5 ) ;
                   if ( closest > dadis ) closest = dadis ; }
          totsum += closest ; 
          ++ nure  ; }}
    totsum = totsum / nure ;
    return ( 2.5 * totsum ) ;
}
             
void show_basic_grid ( HDC myhdc )
{
    int a , b , c , x , y , mc , myrecs ;
    int atx , aty , xstart , ystart , xend , yend ;
    double dxend , dyend , dx , dy ;
    HPEN tmppen ;
    int usd_tmppen ; 
    Fuss mb ;

    if ( spingrid == NULL ) return ;

    if ( !only_show_points && nummaplins ) {
      SelectObject(myhdc,hMapPen); 
      for ( a = 0 ; a < nummaplins ; ++ a ) {
        usd_tmppen = 0 ; 
        if ( maplin[a].colR == 0 && maplin[a].colG == 0 && maplin[a].colB == 0 && maplin[a].thickness == 2 ) SelectObject(myhdc,hMapPen);
        else {
               usd_tmppen = 1 ; 
               tmppen = CreatePen ( PS_SOLID, maplin[a].thickness , RGB ( maplin[a].colR , maplin[a].colG  , maplin[a].colB  ) ) ;
               SelectObject(myhdc,tmppen); }
        for ( b = 0 ; b < maplin[a].numpoints ; ++ b ) {
            x = 5 + ( ( ( ( maplin[a].x[b] - grid_startx ) * grid_effect ) / 100 ) ) - atcoordx ;  
            y = 5 + ( ( ( ( maplin[a].y[b] - grid_starty ) * grid_effect ) / 100 ) ) - atcoordy ;     
            mapptlist[b].x = x ;
            mapptlist[b].y = y ; }
        Polyline ( myhdc , &mapptlist[0] , maplin[a].numpoints ) ;
        if ( usd_tmppen ) DeleteObject ( tmppen ) ;
        if ( a == selected_maplin ) {
             SelectObject(myhdc,hMapRedPen);
             for ( c = selmappoint ; c <= selmappointmax ; ++ c ) {
                xstart = 5 + ( ( ( ( maplin[a].x[c] - grid_startx ) * grid_effect ) / 100 ) ) - atcoordx ;  
                ystart = 5 + ( ( ( ( maplin[a].y[c] - grid_starty ) * grid_effect ) / 100 ) ) - atcoordy ;     
                if ( selpoint_only ) { xend = xstart + 1 ; yend = ystart ; }
                else {
                   xend = 5 + ( ( ( ( maplin[a].x[selmappoint+1] - grid_startx ) * grid_effect ) / 100 ) ) - atcoordx ;  
                   yend = 5 + ( ( ( ( maplin[a].y[selmappoint+1] - grid_starty ) * grid_effect ) / 100 ) ) - atcoordy ; }     
                MyLine ( myhdc , xstart , ystart , xend, yend ) ; }
             SelectObject(myhdc,hMapPen); 
             if ( rbuttisdn ) {
                 rbuttisdn = 1 ; 
                 SelectObject ( myhdc , hMapGreenPen ) ;
                 get_curs_coords ( &dx , &dy ) ; 
                 xstart = 5 + ( ( ( ( dx - grid_startx ) * grid_effect ) / 100 ) ) - atcoordx ;  
                 ystart = 5 + ( ( ( ( dy - grid_starty ) * grid_effect ) / 100 ) ) - atcoordy ;

        lasmousecoordsx = xend = xstart ;
        lasmousecoordsy = yend = ystart ;
        if ( selpoint_only ) {
             if ( selmappoint == maplin[selected_maplin].numpoints - 1
                && last_point_extend ) {
                  xstart = 5 + ( ( ( ( maplin[a].x[selmappoint] - grid_startx ) * grid_effect ) / 100 ) ) - atcoordx ;   
                  ystart = 5 + ( ( ( ( maplin[a].y[selmappoint] - grid_starty ) * grid_effect ) / 100 ) ) - atcoordy ;
                  MyLine ( myhdc , xstart , ystart , xend , yend ) ; }
             else {
                if ( selmappoint ) {
                  xstart = 5 + ( ( ( ( maplin[a].x[selmappoint-1] - grid_startx ) * grid_effect ) / 100 ) ) - atcoordx ;   
                  ystart = 5 + ( ( ( ( maplin[a].y[selmappoint-1] - grid_starty ) * grid_effect ) / 100 ) ) - atcoordy ;
                  MyLine ( myhdc , xstart , ystart , xend , yend ) ; }
               xstart = xend ;
               ystart = yend ;
               if ( selmappoint < maplin[a].numpoints - 1 ) {
                  xend = 5 + ( ( ( ( maplin[a].x[selmappoint+1] - grid_startx ) * grid_effect ) / 100 ) ) - atcoordx ;  
                  yend = 5 + ( ( ( ( maplin[a].y[selmappoint+1] - grid_starty ) * grid_effect ) / 100 ) ) - atcoordy ;
                  MyLine ( myhdc , xstart , ystart , xend , yend ) ; }}}
         else {
             xstart = 5 + ( ( ( ( maplin[a].x[selmappoint] - grid_startx ) * grid_effect ) / 100 ) ) - atcoordx ;  
             ystart = 5 + ( ( ( ( maplin[a].y[selmappoint] - grid_starty ) * grid_effect ) / 100 ) ) - atcoordy ;
             MyLine ( myhdc , xstart , ystart , xend , yend ) ;
             xstart = xend ;
             ystart = yend ; 
             xend = 5 + ( ( ( ( maplin[a].x[selmappoint+1] - grid_startx ) * grid_effect ) / 100 ) ) - atcoordx ;  
             yend = 5 + ( ( ( ( maplin[a].y[selmappoint+1] - grid_starty ) * grid_effect ) / 100 ) ) - atcoordy ;
             MyLine ( myhdc , xstart , ystart , xend , yend ) ; }
        SelectObject ( myhdc , hMapPen ) ; }}}
      if ( doautolines ) {
         xstart = 5 + ( ( ( ( autolinepointx - grid_startx ) * grid_effect ) / 100 ) ) - atcoordx ;  
         ystart = 5 + ( ( ( ( autolinepointy - grid_starty ) * grid_effect ) / 100 ) ) - atcoordy ;  
         xstart -= 5 ;         
         ystart -= 5 ;
         xend = xstart + 10 ; 
         yend = ystart + 10 ;
         SelectObject ( myhdc , hMapGreenPen ) ;
         MyLine ( myhdc , xstart , ystart , xend , yend ) ;
         xstart += 10 ;
         xend -= 10 ; 
         MyLine ( myhdc , xstart , ystart , xend , yend ) ;
         SelectObject ( myhdc , hMapPen ) ; }}

    SelectObject ( myhdc , hBlackPen ) ;
    for ( a = 0 ; a < spp ; ++ a ) {
        mc = a / 32 ;
        mb = 1 << ( a % 32 ) ;
        if ( ( spingrid[mc] & mb ) == 0 ) continue ;
        myrecs = xymatrix[a].numrecs ;
        for ( b = myrecs ; b -- ; ) {
            x = 5 + ( ( ( ( xymatrix[a].x[b] - grid_startx ) * grid_effect ) / 100 ) ) - atcoordx ;  
            y = 5 + ( ( ( ( xymatrix[a].y[b] - grid_starty ) * grid_effect ) / 100 ) ) - atcoordy ;     
            MyLine ( myhdc , x , y , x+1, y ) ; }}

  if ( only_show_points ) return ; 

  SelectObject ( myhdc , hBranchpen ) ; 
  xstart = xend = ( 5 - atcoordx ) ; // + ( ( ( grid_startx - minx ) * grid_effect ) / 100 ) ; 
  dxend = ( double ) cols * ( ( truecellwid * grid_effect ) / 100 ) ;
  xend += ( int ) dxend ; 
  ystart = yend = ( 5 - atcoordy ) ; // + ( ( ( grid_starty - miny ) * grid_effect ) / 100 ) ;
  dyend = ( double ) rows * ( ( truecellhei * grid_effect ) / 100 ) ;
  yend += ( int ) dyend ; 
  atx = xstart ;
  aty = ystart ; 
  for ( a = 0 ; a ++ <= cols ; ) {
      MyLine ( myhdc , atx , ystart , atx , yend ) ;
      dxend = ( double ) ( ( a * truecellwid ) * grid_effect ) / 100 ;  
      atx = xstart + ( int ) dxend ; }
  for ( a = 0 ; a ++ <= rows ; ) {
      MyLine ( myhdc , xstart , aty , xend , aty ) ;
      dyend = ( double ) ( ( a * truecellhei ) * grid_effect ) / 100 ;
      aty = ystart + ( int ) dyend  ; }
}


BOOL CALLBACK RadiusSizeFunc(HWND hdwnd, UINT message, WPARAM wParam, LPARAM lParam)
{
    int i , j , redis , greenis , blueis ;
    int myx , myy ;
    int myassx , myassy ; 
    HWND hWho ;
    switch(message) {
        case WM_INITDIALOG :
          myx = ( int ) xperc ;
          myy = ( int ) yperc ; 
          myassx = ( int ) xassperc ;
          myassy = ( int ) yassperc ; 
          SET_UPDOWN ( 114 , 0 , 500 , myx ) ; 
          SET_UPDOWN ( 115 , 0 , 500 , myy ) ; 
          SET_UPDOWN ( 123 , 0 , 1000 , myassx ) ; 
          SET_UPDOWN ( 124 , 0 , 1000 , myassy ) ; 
          hWho = GetDlgItem ( hdwnd , 123 ) ;
          SpinAccel ( hWho , 1 , 5 ) ;
          hWho = GetDlgItem ( hdwnd , 124 ) ;
          SpinAccel ( hWho , 1 , 5 ) ;
          hWho = GetDlgItem ( hdwnd , 114 ) ;
          SpinAccel ( hWho , 1 , 5 ) ;
          hWho = GetDlgItem ( hdwnd , 115 ) ;
          SpinAccel ( hWho , 1 , 5 ) ;
          FOCUS_ON (IDOK ) ;
          break ; 
        case WM_COMMAND :
                switch(LOWORD(wParam)){
                        case IDOK :
                           GETINT ( xperc , 107 ) ; 
                           GETINT ( yperc , 111 ) ; 
                           GETINT ( xassperc , 121 ) ; 
                           GETINT ( yassperc , 122 ) ; 
                           EndDialog ( hdwnd, 1 ) ;
                           return 1 ; 
                        case IDCANCEL :
                                EndDialog(hdwnd,0);
                                return 0;
                        default :
                                break; }
         break; }
    return 0;
}

void set_radius_size ( void )
{
    int x ; 
    DialogBox (hInst, "RadiusSizeDB", hwnd, (DLGPROC) RadiusSizeFunc ) ; 
    return ;
}

BOOL CALLBACK GridSizePosFunc(HWND hdwnd, UINT message, WPARAM wParam, LPARAM lParam)
{
    int i , j , redis , greenis , blueis ;
    int myx , myy ;
    static int myctrlact ; 
    double siz ; 
    HWND hWho ;
    switch(message) {
        case WM_INITDIALOG :
          sprintf ( junkstr , "%.3f" , truecellwid ) ; 
          SetDlgItemText ( hdwnd , 104 , junkstr ) ;
          sprintf ( junkstr , "%.3f" , truecellhei ) ; 
          SetDlgItemText ( hdwnd , 106 , junkstr ) ;
          sprintf ( junkstr , "%.3f" , grid_startx * xsign ) ; 
          SetDlgItemText ( hdwnd , 108 , junkstr ) ;
          sprintf ( junkstr , "%.3f" , grid_starty * ysign ) ; 
          SetDlgItemText ( hdwnd , 110 , junkstr ) ;
          if ( ctrl_arrow_changes_org ) BUTT_CHECK( 115 ) ;
          else BUTT_CHECK ( 116 ) ;
          myctrlact = ctrl_arrow_changes_org ; 
          FOCUS_ON (IDOK ) ;
          break ; 
        case WM_COMMAND :
                switch(LOWORD(wParam)){
                        case 120 :
                            siz = set_autosizegrid () ;
                            sprintf ( junkstr , "%.3f" , siz ) ; 
                            SetDlgItemText ( hdwnd , 104 , junkstr ) ;
                            sprintf ( junkstr , "%.3f" , siz ) ; 
                            SetDlgItemText ( hdwnd , 106 , junkstr ) ;
                            sprintf ( junkstr , "%.3f" , grid_startx ) ; 
                            SetDlgItemText ( hdwnd , 108 , junkstr ) ;
                            sprintf ( junkstr , "%.3f" , grid_starty ) ; 
                            SetDlgItemText ( hdwnd , 110 , junkstr ) ;
                            FOCUS_ON (IDOK ) ;
                            break ; 
                        case 115 : myctrlact = 1 ; break ; 
                        case 116 : myctrlact = 0 ; break ; 
                        case IDOK :
                           ctrl_arrow_changes_org = myctrlact ; 
                           GetDlgItemText(hdwnd, 104 , junkstr, 80);  
                           truecellwid = atof(junkstr);  
                           GetDlgItemText(hdwnd, 106 , junkstr, 80);  
                           truecellhei = atof(junkstr);  
                           GetDlgItemText(hdwnd, 108 , junkstr, 80);  
                           grid_startx = atof(junkstr) * xsign ;  
                           GetDlgItemText(hdwnd, 110 , junkstr, 80);  
                           grid_starty = atof(junkstr) * ysign ;  
                           EndDialog ( hdwnd, 1 ) ;
                           return 1 ; 
                        case IDCANCEL :
                                EndDialog(hdwnd,0);
                                return 0;
                        default :
                                break; }
         break; }
    return 0;
}

extern double maxx , maxy ;
extern int ctrl_arrow_changes_org , data_is_xydata; 

void set_grid_size_and_pos ( void )
{
    int x ;
    double widwas = truecellwid, heiwas = truecellhei ,
           orgxwas = grid_startx , orgywas = grid_starty ;

    if ( !data_is_xydata 
          /* !num_spingrid && grid_startx > 10e99 && grid_starty > 10e99 */ ) {
        x = DialogBox (hInst, "FakeGridSizePosDB", hwnd, (DLGPROC) FakeGridSizePosFunc ) ;
        if ( x ) fake_a_grid () ;
        return ; }
           
    if ( grid_created )
        if ( !confirm_grid_move () ) return ; 
    x = DialogBox (hInst, "GridSizePosDB", hwnd, (DLGPROC) GridSizePosFunc ) ; 
    if ( x && grid_created && ( truecellwid < mincellwid || truecellhei < mincellhei ) ) { 
         sprintf ( junkstr , "Cannot reduce cell size to less than a third the\noriginal size (i.e. less than %.5fx%.5f)" , mincellwid , mincellhei ) ; 
         MessageBox ( mainwnd , junkstr , "ERRROR" , MB_OK | MB_ICONERROR ) ;
         truecellwid = widwas ;
         truecellhei = heiwas ;
         grid_startx = orgxwas ;
         grid_starty = orgywas ;
         return ; }
    if ( x ) {
       cols = 2 ; 
       while ( grid_startx + ( truecellwid * ( cols - 1 ) ) < maxx ) ++ cols ; 
       rows = 2 ; 
       while ( grid_starty + ( truecellhei * ( rows - 1 ) ) < maxy ) ++ rows ; }  
    if ( !grid_created ||
        ( widwas == truecellwid && heiwas == truecellhei &&
          orgxwas == grid_startx && orgywas == grid_starty ) ) return ;
    chk_a_move () ;
    doallscores () ;
    curcmd_loop = cmd_loop ;
    recptr = rec ; 
    showcurset () ; 
    return ;
}

extern double * maxconscore ; 

int max_drawn_y , max_drawn_x ; 


void showmap ( HDC myhdc )
{
  int xstart , ystart , xend , yend , atx , aty ;
  int was , atlin = 1 ; 
  int a , b , bb ;
  char * cp , * at ;
  double x , y ;
  unsigned long int mb ;
  unsigned long int * disppt = ( unsigned long int * ) dout ; 
  int mc , myrecs ;
  HPEN tmppen ;
  int usd_tmppen ;
  max_drawn_y = 0 ; 
  if ( sccol == NULL || numrecs == 0 ) return ;
  SelectObject(myhdc,hBranchpen);
  if ( !nited ) {
       set_fillcol ( 0 , fillcol ) ;
       set_fillcol ( 0 , consfillcol ) ; }
  nited = 1 ;
  TextOut ( myhdc , 10 - atcoordx , 10 - atcoordy , screentitle , strlen(screentitle) ) ;
  xstart = xend = 10 - atcoordx ; 
  for ( a = cols ; a -- ; ) xend += cellwid ; 
  ystart = yend = 30 - atcoordy ;
  for ( a = rows ; a -- ; ) yend += cellhei ; 
  atx = xstart ;
  aty = ystart ; 
  for ( a = 0 ; a <= cols ; ++ a ) {
      MyLine ( myhdc , atx , ystart , atx , yend ) ;
      atx += cellwid ; }
  for ( a = 0 ; a <= rows ; ++ a ) {
      MyLine ( myhdc , xstart , aty , xend , aty ) ;
      aty += cellhei ; }
  atx = xstart ;
  for ( a = 0 ; a < cols ; ++ a ) {
      aty = ystart ; 
      for ( b = 0 ; b < rows ; ++ b ) {
          if ( sccol[a][b] < 8 ) {
            if ( curcmd_loop == show_consensus ) 
                 SelectObject ( myhdc , ( consfillcol[sccol[a][b]] ) ) ;
            else SelectObject ( myhdc , ( fillcol[sccol[a][b]] ) ) ; 
            Rectangle ( myhdc ,
                         atx , aty ,
                        ( atx + cellwid ) + ( bthick/2 ) ,
                        ( aty + cellhei ) + ( bthick/2 ) 
                      ) ; } 
          aty += cellhei ; }
      atx += cellwid ; }

  if ( curcmd_loop == cmd_loop && show_coordinates ) {
      sprintf ( junkstr , "%.4f" , grid_starty ) ; 
      showingy = ( 30 - atcoordy ) - 7 ;
      showingx = ( 30 + ( cellwid * cols )) - atcoordx ;
      TextOut ( myhdc , showingx, showingy , junkstr , strlen(junkstr ) ) ;    
      showingy += ( cellhei * rows ) ; 
      sprintf ( junkstr , "%.4f" , grid_starty + ( rows * grid_height ) ) ; 
      TextOut ( myhdc , showingx, showingy , junkstr , strlen(junkstr ) ) ;
      sprintf ( junkstr , "%.4f" , grid_startx ) ; 
      showingy = ( 30 - atcoordy ) + ( cellhei * rows ) + ( cellhei / 2 ) ; 
      showingx =  7 - atcoordx ; 
      TextOut ( myhdc , showingx, showingy , junkstr , strlen(junkstr ) ) ;    
      showingx += ( cellwid * cols ) - ( cellwid / 2 ) ; 
      sprintf ( junkstr , "%.4f" , grid_startx + ( cols * grid_width ) ) ; 
      TextOut ( myhdc , showingx, showingy , junkstr , strlen(junkstr ) ) ; }      

  if ( ( curcmd_loop == viewscore || curcmd_loop == showfauna ) && show_color_code ) {
      showingy = 50 - atcoordy ;
      showingx = ( 30 + ( cellwid * cols )) - atcoordx ;
      showcolorcode ( myhdc , 0 , "Just ground!" ) ; 
      showcolorcode ( myhdc , ( 1 ) , "Inside area, species absent" ) ;
      showcolorcode ( myhdc , ( 1 | 2 ) , "Inside area, species present" ) ;
      showcolorcode ( myhdc , ( 1 | 4 ) , "Inside area, species assumed" ) ;
      showcolorcode ( myhdc , ( 2 ) , "Outside area, species present" ) ;
      showcolorcode ( myhdc , ( 4 ) , "Outside area, species assumed" ) ; }

  if ( curcmd_loop == show_duwc ) {
      showingy = 50 - atcoordy ;
      showingx = ( 30 + ( cellwid * cols )) - atcoordx ;
      showcolorcode ( myhdc , 0 , "Just ground!" ) ;
      if ( is_cons_duwc ) {
         showcolorcode ( myhdc , ( 1 ) , "reference set") ; 
         showcolorcode ( myhdc , ( 2 ) , "the other" ) ;
         showcolorcode ( myhdc , ( 1 | 2 ) , "both" ) ; }
      else { 
         sprintf ( junkstr , "set %i" , recptr - rec ) ;
         showcolorcode ( myhdc , ( 1 ) , junkstr ) ; 
         showcolorcode ( myhdc , ( 2 ) , "reference set" ) ;
         showcolorcode ( myhdc , ( 1 | 2 ) , "both" ) ; } 
      }

  if ( curcmd_loop == cmd_loop ) {
      showingx = ( 30 + ( cellwid * cols )) - atcoordx ;
      max_drawn_x = showingx + 20 ; }
      
  if ( curcmd_loop == show_consensus ) {
      showingy = 30 - atcoordy ;
      showingx = ( 30 + ( cellwid * cols )) - atcoordx ;
      showcolorcode ( myhdc , 0 , "Just ground!" ) ;
      max_drawn_x = showingx + 140 ; 
      b = -1 ;
      x = consen_minval ; 
      for ( a = 1 ; a < 8 && x <= consen_maxval ; ++ a ) {
          if ( !consensus_is_sample ) 
              if ( consen_intrvl > 0 ) 
                   sprintf ( junkstr , "%.5f - %.5f" , x , x + consen_intrvl ) ;
              else sprintf ( junkstr , "%.5f" , x ) ;
          else 
              if ( consen_intrvl > 0 ) 
                   sprintf ( junkstr , "%.2f-%.2f" , x , x + consen_intrvl ) ;
              else sprintf ( junkstr , "%.2f" , x ) ;
          x += consen_intrvl ; 
          showcolorcode ( myhdc , a , junkstr ) ;
          if ( consen_intrvl == 0 ) break ; }}

  cp = at = screencapt ;
  max_drawn_y = aty ; 
  if ( * cp == '\n' ) {
       ++ atlin ;
       ++ at ; }
  while ( * cp != '\0' ) {
        ++ cp ; 
        if ( * cp == '\n' || * cp == '\0' ) {
            was = * cp ; 
            * cp = '\0' ;
            TextOut ( myhdc , 10 - atcoordx , aty + ( 17 * atlin ) , at , strlen ( at ) ) ;
            atlin ++ ;
            if ( was == '\0' ) break ;
            max_drawn_y = aty + ( 17 * atlin ) ; 
            * cp = '\n' ; 
            at = ++ cp ; }}

  if ( nummaplins ) {
    SelectObject(myhdc,hBlackPen); 
    for ( a = 0 ; a < nummaplins ; ++ a ) {
        usd_tmppen = 0 ; 
        if ( maplin[a].colR == 0 && maplin[a].colG == 0 && maplin[a].colB == 0 && maplin[a].thickness == 2 ) SelectObject(myhdc,hBlackPen);
        else {
               usd_tmppen = 1 ; 
               tmppen = CreatePen ( PS_SOLID, maplin[a].thickness , RGB ( maplin[a].colR , maplin[a].colG  , maplin[a].colB  ) ) ;
               SelectObject(myhdc,tmppen); }
        for ( bb = b = 0 ; bb < maplin[a].numpoints ; ++ bb ) {
            x = maplin[a].x[bb] ;
            y = maplin[a].y[bb] ;

//xxxxxxxxxx

if ( hide_the_map ) 
    if ( x > maxx || x < minx || y > maxy || y < miny ) {
       if ( b > 1 ) {
            Polyline ( myhdc , &mapptlist[0] , b ) ;
            b = 0 ; }
        continue ;
    }

            x = maplin[a].x[bb] - grid_startx ;
            y = maplin[a].y[bb] - grid_starty ;

            x = ( cellwid * x ) / truecellwid ; 
            atx = x + ( 10 - atcoordx ) ;  
            y = ( cellhei * y ) / truecellhei ; 
            aty = y + ( 30 - atcoordy ) ;  
            mapptlist[b].x = atx ;
            mapptlist[b].y = aty ;
            ++ b ; 
            



            }
        if ( b > 1 ) Polyline ( myhdc , &mapptlist[0] , b ) ;
        if ( usd_tmppen ) DeleteObject ( tmppen ) ; }}

  if ( num_spingrid /* && show_individual_dots */ ) {
    SelectObject(myhdc,hBlackPen);
    if ( show_individual_dots ) 
     for ( a = 0 ; a < spp ; ++ a ) {
        mc = a / 32 ;
        mb = 1 << ( a % 32 ) ;
        if ( curcmd_loop == showfauna ) continue ;
        if ( curcmd_loop == show_duwc && ( disppt[mc] & mb ) ) continue ; 
        if ( curcmd_loop == show_consensus ) continue ; 
        if ( curcmd_loop == cmd_loop && ( recptr -> splist [mc] & mb ) ) continue ;
        if ( curcmd_loop == viewscore || curcmd_loop == showspecies ) {
            if ( a == current_species ) continue ; 
            if ( curcmd_loop == showspecies ) {
                if ( a != current_species ) continue ; }
            else if ( ( intersptr[mc] & mb ) == 0 ) continue ; }
        else if ( ( spingrid[mc] & mb ) == 0 ) continue ;
        myrecs = xymatrix[a].numrecs ;
        for ( b = myrecs ; b -- ; ) {
            x = xymatrix[a].x[b] - grid_startx ;
            y = xymatrix[a].y[b] - grid_starty ;
            x = ( cellwid * x ) / truecellwid ; 
            atx = x + ( 10 - atcoordx ) ;  
            y = ( cellhei * y ) / truecellhei ; 
            aty = y + ( 30 - atcoordy ) ;  
            MyLine ( myhdc , atx , aty , atx+1 , aty ) ; }}

    if ( cmd_loop == curcmd_loop || curcmd_loop == show_consensus || curcmd_loop == show_duwc ) { 
        SelectObject( myhdc , hYellowPen ) ;  
        for ( a = 0 ; a < spp ; ++ a ) {
            mc = a / 32 ;
            mb = 1 << ( a % 32 ) ;
            if ( curcmd_loop == show_duwc && !( disppt[mc] & mb ) ) continue ; 
            if ( curcmd_loop == show_consensus ) {
                if ( maxconscore[a] == 0 ) continue ;
                if ( current_species >= 0 && a != current_species ) continue ; }
            if ( curcmd_loop == showfauna ) continue ;
            if ( curcmd_loop == cmd_loop && ( recptr -> splist [mc] & mb ) == 0 ) continue ;
            myrecs = xymatrix[a].numrecs ;
            for ( b = myrecs ; b -- ; ) {
                x = xymatrix[a].x[b] - grid_startx ;
                y = xymatrix[a].y[b] - grid_starty ;
                x = ( cellwid * x ) / truecellwid ; 
                atx = x + ( 10 - atcoordx ) ;  
                y = ( cellhei * y ) / truecellhei ; 
                aty = y + ( 30 - atcoordy ) ;  
                MyLine ( myhdc , atx , aty , atx+1 , aty ) ; }}}

        if ( curcmd_loop == viewscore || curcmd_loop == showfauna
             || curcmd_loop == showspecies ) {
              a = current_species ; 
              mc = a / 32 ;
              mb = 1 << ( a % 32 ) ;

              if ( black_n_white )
                    SelectObject(myhdc,hWhitePen);
              else SelectObject(myhdc,hYellowPen); 
        
              myrecs = xymatrix[a].numrecs ;
              for ( b = myrecs ; b -- ; ) {
                    x = xymatrix[a].x[b] - grid_startx ;
                    y = xymatrix[a].y[b] - grid_starty ;
                    x = ( cellwid * x ) / truecellwid ; 
                    atx = x + ( 10 - atcoordx ) ;  
                    y = ( cellhei * y ) / truecellhei ; 
                    aty = y + ( 30 - atcoordy ) ;  
                    MyLine ( myhdc , atx , aty , atx+1 , aty ) ; }

              SelectObject(myhdc,hBlackPen); }

   SelectObject(myhdc,hBranchpen) ; }
  return ;
}       


int get_selected_maplin ( HWND mywnd , int * selpt )
{
   long int a , b , aa , bb , xend , xstart , yend , ystart ;
   long int x , y ;
   double dx , dy ;
   int sqorgx , sqorgy , sqendx , sqendy , tmp ;
   static int * listlastpt = NULL , lastlin = -1 ; 
   POINT cursat ; 
   if ( listlastpt == NULL ) {
     listlastpt = mymem ( nummaplins * sizeof ( int ) ) ;
     for ( a = 0 ; a < nummaplins ; ++ a ) listlastpt[a] = -1 ; }
   GetCursorPos ( &cursat ) ;
   ScreenToClient ( mywnd , &cursat ) ; 
   x = cursat.x ;
   y = cursat.y ;
   a = lastlin ; 
   for ( aa = 0 ; aa < nummaplins ; ++ aa ) {
       if ( ++ a >= nummaplins ) a = 0 ;
       b = listlastpt[a] ; 
       for ( bb = 0 ; bb < maplin[a].numpoints ; ++ bb ) {
            if ( ++ b >= maplin[a].numpoints ) b = 0 ; 
            sqorgx = 5 + ( ( ( ( maplin[a].x[b] - grid_startx ) * grid_effect ) / 100 ) ) - atcoordx ;  
            sqorgy = 5 + ( ( ( ( maplin[a].y[b] - grid_starty ) * grid_effect ) / 100 ) ) - atcoordy ;     
            sqendx = 5 + ( ( ( ( maplin[a].x[b+1] - grid_startx ) * grid_effect ) / 100 ) ) - atcoordx ;  
            sqendy = 5 + ( ( ( ( maplin[a].y[b+1] - grid_starty ) * grid_effect ) / 100 ) ) - atcoordy ;
            if ( sqorgx > sqendx ) { tmp = sqorgx ; sqorgx = sqendx ; sqendx = tmp ; }
            if ( sqorgy > sqendy ) { tmp = sqorgy ; sqorgy = sqendy ; sqendy = tmp ; }    
            if ( sqorgx == sqendx ) { sqorgx -= 10 ; sqendx += 10 ; }
            if ( sqorgy == sqendy ) { sqorgy -= 10 ; sqendy += 10 ; }
            if ( x >= sqorgx && x <= sqendx &&
                 y >= sqorgy && y <= sqendy ) {
                     selmappointmax = * selpt = b ;
                     if ( selpoint_only ) {
                        lastlin = a ;
                        listlastpt[a] = b ; }
                     return a ; }}}
   return -1 ;        
}

void add_point_to_mapline ( HWND mywnd )
{
   long int a , b , xend , xstart , yend , ystart ;
   long int x , y , numpts ; 
   double dx , dy ;
   int sqorgx , sqorgy , sqendx , sqendy , tmp ; 
   POINT cursat ; 
   GetCursorPos ( &cursat ) ;
   ScreenToClient ( mywnd , &cursat ) ; 
   numpts = maplin[selected_maplin].numpoints ; 
   x = cursat.x ;
   y = cursat.y ;
   dx  = ( ( ( double ) ( x + atcoordx - 5 ) * 100 ) / grid_effect ) + grid_startx ; 
   dy  = ( ( ( double ) ( y + atcoordy - 5 ) * 100 ) / grid_effect ) + grid_starty ; 
   if ( selpoint_only ) {
     if ( selmappoint == maplin[selected_maplin].numpoints - 1 &&
        last_point_extend ) {
          if ( numpts == MAXLINPTS ) {
              sprintf ( junkstr , "Sorry, cannot have more than %i points in a line" , MAXLINPTS ) ;
              MessageBox ( hwnd , junkstr , "Error" , MB_OK | MB_ICONERROR ) ;
              return ; }
          maplin[selected_maplin].x[numpts] = dx ; 
          maplin[selected_maplin].y[numpts] = dy ;
          ++ maplin[selected_maplin].numpoints ;
          ++ numpts ; 
          maplin[selected_maplin].x[numpts] = dx ; 
          maplin[selected_maplin].y[numpts] = dy ;
          ++ selmappoint ;
          selmappointmax = selmappoint ; }
     else {
        maplin[selected_maplin].x[selmappoint] = dx ; 
        maplin[selected_maplin].y[selmappoint] = dy ;
        if ( selmappoint == numpts-1 ) {
            maplin[selected_maplin].x[selmappoint+1] = dx ; 
            maplin[selected_maplin].y[selmappoint+1] = dy ; }}}
   else {
     if ( numpts >= MAXLINPTS ) {
         sprintf ( junkstr , "Sorry, cannot have more than %i points in a line" , MAXLINPTS ) ;
         MessageBox ( hwnd , junkstr , "Error" , MB_OK | MB_ICONERROR ) ;
         return ; }
     for ( a = numpts ; a > selmappoint ; -- a ) {
         maplin[selected_maplin].x[a] = maplin[selected_maplin].x[a-1] ; 
         maplin[selected_maplin].y[a] = maplin[selected_maplin].y[a-1] ; }
     maplin[selected_maplin].x[selmappoint+1] = dx ; 
     maplin[selected_maplin].y[selmappoint+1] = dy ;
     maplin[selected_maplin].numpoints ++ ;
     a = maplin[selected_maplin].numpoints ; 
     maplin[selected_maplin].x[a] = maplin[selected_maplin].x[a-1] ;  
     maplin[selected_maplin].y[a] = maplin[selected_maplin].y[a-1] ; 
     if ( ++ selmappoint >= maplin[selected_maplin].numpoints )
          selmappoint = maplin[selected_maplin].numpoints -1 ;
     selmappointmax = selmappoint ; }
   return ;
}

void delete_maplin_point ( void )
{
   int a , numpts ;
   numpts = maplin[selected_maplin].numpoints ; 
   if ( selpoint_only ) {
       if ( selmappoint == 0 ) {
               MessageBox ( hwnd , "Sorry, cannot delete staring point" , "Error" , MB_OK | MB_ICONERROR ) ;
               return ; }
       for ( a = selmappoint ; a < numpts ; ++ a ) {
           maplin[selected_maplin].x[a] = maplin[selected_maplin].x[a+1] ;  
           maplin[selected_maplin].y[a] = maplin[selected_maplin].y[a+1] ; }      
       maplin[selected_maplin].numpoints -- ;
       a = maplin[selected_maplin].numpoints ; 
       maplin[selected_maplin].x[a] = maplin[selected_maplin].x[a-1] ;  
       maplin[selected_maplin].y[a] = maplin[selected_maplin].y[a-1] ;       
       -- selmappoint ;
       -- selmappointmax ;
       if ( selmappoint < 0 ) {
            selmappoint = 0 ;
            if ( selmappointmax < 0 ) selmappointmax = 0 ; }}
}
    
void enlarge_point_selection ( int i )
{
   int j ; 
   if ( i == VK_END ) {
       j = 1 ;
       if ( !selpoint_only ) j = 2 ; 
       selmappoint = selmappointmax =
            maplin[selected_maplin].numpoints - j ;
       return ; }
   if ( i == VK_HOME ) {
       selmappoint = selmappointmax = 0 ; 
       return ; }
   if ( i == VK_TAB || i == VK_BACK ) {
      if ( i == VK_TAB ) selmappointmax ++ ;
      else selmappointmax -- ; }
   else {
      if ( i == VK_ADD ) {
          if ( !selpoint_only &&
              selmappoint == maplin[selected_maplin].numpoints - 2 ) return ; 
          selmappointmax ++ ; selmappoint ++ ; }
      else {
            selmappointmax -- ; selmappoint -- ; }}
   if ( selmappoint < 0 ) selmappoint = 0 ; 
   if ( selmappoint >= maplin[selected_maplin].numpoints )
        selmappoint = maplin[selected_maplin].numpoints - 1 ; 
   if ( selmappointmax < selmappoint ) selmappointmax = selmappoint ; 
   if ( selmappointmax >= maplin[selected_maplin].numpoints )
        selmappointmax = maplin[selected_maplin].numpoints - 1 ; 
}


void get_curs_coords ( double * dx , double * dy )
{
   POINT cursat ;
   int x , y  ; 
   GetCursorPos ( &cursat ) ;
   ScreenToClient ( mainwnd , &cursat ) ; 
   x = cursat.x ;
   y = cursat.y ;
   * dx = ( ( ( double ) ( x + atcoordx - 5 ) * 100 ) / grid_effect ) + grid_startx ; 
   * dy = ( ( ( double ) ( y + atcoordy - 5 ) * 100 ) / grid_effect ) + grid_starty ; 
   return ;
}    

void set_autoline_mode ( HWND mywnd )
{
    
   long int a , b , xend , xstart , yend , ystart ;
   long int x , y , numpts ; 
   double dx , dy ;
   int sqorgx , sqorgy , sqendx , sqendy , tmp ; 
   POINT cursat ; 
   GetCursorPos ( &cursat ) ;
   ScreenToClient ( mywnd , &cursat ) ; 
   numpts = maplin[selected_maplin].numpoints ; 
   x = cursat.x ;
   y = cursat.y ;
   autolinepointx = ( double ) ( ( ( x + atcoordx - 5 ) * 100 ) / grid_effect ) + grid_startx ; 
   autolinepointy = ( double ) ( ( ( y + atcoordy - 5 ) * 100 ) / grid_effect ) + grid_starty ; 
   doautolines = 1 ; 
   return ;
}

void add_autoline ( void )
{
   long int a , b , xend , xstart , yend , ystart ;
   long int x , y , numpts ; 
   double dx , dy ;
   int sqorgx , sqorgy , sqendx , sqendy , tmp ; 
   numpts = maplin[selected_maplin].numpoints ;
   if ( numpts >= MAXLINPTS ) {
       sprintf ( junkstr , "Sorry, cannot have more than %i points in a line" , MAXLINPTS ) ;
       MessageBox ( hwnd , junkstr , "Error" , MB_OK | MB_ICONERROR ) ;
       return ; }
   dx  = autolinepointx ; 
   dy  = autolinepointy ; 
   for ( a = numpts ; a > selmappoint ; -- a ) {
         maplin[selected_maplin].x[a] = maplin[selected_maplin].x[a-1] ; 
         maplin[selected_maplin].y[a] = maplin[selected_maplin].y[a-1] ; }
     maplin[selected_maplin].x[selmappoint+1] = dx ; 
     maplin[selected_maplin].y[selmappoint+1] = dy ;
     maplin[selected_maplin].numpoints ++ ;
     a = maplin[selected_maplin].numpoints ; 
     maplin[selected_maplin].x[a] = maplin[selected_maplin].x[a-1] ;  
     maplin[selected_maplin].y[a] = maplin[selected_maplin].y[a-1] ; 
     if ( ++ selmappoint >= maplin[selected_maplin].numpoints )
          selmappoint = maplin[selected_maplin].numpoints -1 ;
   selmappointmax = selmappoint ; 
   return ;
}

int new_mouse_position ( void )
{
    double dx , dy ;
    int x , y ;
    get_curs_coords ( &dx , &dy ) ;
    x = 5 + ( ( ( ( double ) ( dx - grid_startx ) * grid_effect ) / 100 ) ) - atcoordx ;  
    y = 5 + ( ( ( ( double ) ( dy - grid_starty ) * grid_effect ) / 100 ) ) - atcoordy ;
    if ( x == lasmousecoordsx && y == lasmousecoordsy ) 
       return 0 ; 
    return 1 ;
}


void start_a_new_line ( void )
{
    double dx , dy ;
    if ( nummaplins >= MAXNUMLINS ) {
         sprintf ( junkstr , "Can't have more than %i lines\n(with up to %i segments each)" ,
         MAXNUMLINS , MAXLINPTS ) ; 
         MessageBox ( mainwnd , junkstr , "ERROR" , MB_OK | MB_ICONERROR ) ;
         return ; }
    get_curs_coords ( &dx , & dy ) ;
    if ( maplin == NULL ) maplin = mymem ( MAXNUMLINS * sizeof ( Maplintyp ) ) ; 
    maplin[nummaplins].x = mymem (( MAXLINPTS + 2 ) * sizeof ( float ) ) ; 
    maplin[nummaplins].y = mymem (( MAXLINPTS + 2 ) * sizeof ( float ) ) ; 
    maplin[nummaplins].x[0] = dx ; 
    maplin[nummaplins].y[0] = dy ; 
    maplin[nummaplins].x[1] = dx + truecellwid ; 
    maplin[nummaplins].y[1] = dy + truecellwid ;
    maplin[nummaplins].x[2] = dx + truecellwid ; 
    maplin[nummaplins].y[2] = dy + truecellwid ;
    maplin[nummaplins].numpoints = 2 ;
    selected_maplin = nummaplins ++ ;
    selmappoint = selmappointmax = 1 ;
    selpoint_only = 1 ;
    return ;
}


time_t prvchk , thischk ; 

void move_autoline_tgt ( int i )
{
    double nuv , add ;
    double dx , dxx ;
    int c ;
    static int numpixs = 1 ; 
    static int nited = 0 ;
    static int lasdir = 0 ;
    static int repets ;
    double laps ; 
    if ( nited && i == lasdir ) {
         thischk = clock () ;
         laps = ( double ) ( thischk - prvchk ) / CLK_TCK ;
         if ( laps < 0.25 ) {
            ++ repets ;
            if ( !( repets % 4 ) ) {
                   if ( numpixs < 10 ) numpixs += 2 ;
                   else numpixs += 4 ; 
                   repets = 0 ; }   
            if ( numpixs > 20 ) numpixs = 20 ; }
         if ( laps > 0.25 ) { numpixs = 1 ; repets = 0 ; }}
    nited = 1 ;
    if ( lasdir != i ) { repets = 0 ; numpixs = 1 ; }
    lasdir = i ;
    prvchk = clock() ; 
    dx  = ( ( ( double ) ( atcoordx - 5 ) * 100 ) / grid_effect ) + grid_startx ; 
    dxx  = ( ( ( double ) ( numpixs + atcoordx - 5 ) * 100 ) / grid_effect ) + grid_startx ; 
    add = dxx - dx ;
    if ( add < 0 ) add = -add ;
    if ( add < 0.0000001 ) add = 0.000001 ; 
    if ( i == VK_UP || i == VK_LEFT ) add = -add ;
    if ( i == VK_UP || i == VK_DOWN )
       autolinepointy += add ; 
    else 
       autolinepointx += add ; 
}
    

void move_selected_point ( int i )
{
    double nuv , add ;
    double dx , dxx ;
    int c ; 
    static int numpixs = 1 ; 
    static int nited = 0 ;
    static int lasdir = 0 ;
    static int repets ;
    double laps ; 
    if ( nited && i == lasdir ) {
         thischk = clock () ;
         laps = ( double ) ( thischk - prvchk ) / CLK_TCK ;
         if ( laps < 0.25 ) {
            ++ repets ;
            if ( !( repets % 4 ) ) {
                   if ( numpixs < 10 ) numpixs += 2 ;
                   else numpixs += 4 ; 
                   repets = 0 ; }   
            if ( numpixs > 20 ) numpixs = 20 ; }
         if ( laps > 0.25 ) { numpixs = 1 ; repets = 0 ; }}
    nited = 1 ;
    if ( lasdir != i ) { repets = 0 ; numpixs = 1 ; }
    lasdir = i ;
    prvchk = clock() ; 
    dx  = ( ( ( double ) ( atcoordx - 5 ) * 100 ) / grid_effect ) + grid_startx ; 
    dxx  = ( ( ( double ) ( numpixs + atcoordx - 5 ) * 100 ) / grid_effect ) + grid_startx ; 
    add = dxx - dx ;
    if ( add < 0 ) add = -add ;
    if ( add < 0.0000001 ) add = 0.000001 ; 
    if ( i == VK_UP || i == VK_LEFT ) add = -add ;
    if ( i == VK_UP || i == VK_DOWN ) 
        for ( c = selmappoint ; c <= selmappointmax ; ++ c ) 
            maplin[selected_maplin].y[c] += add ;
    else 
       for ( c = selmappoint ; c <= selmappointmax ; ++ c ) 
           maplin[selected_maplin].x[c] += add ;
}
    

typedef struct 
    { double x , y ; } Pointyp ; 

char RGB_string_space[15] ; 

char * RGB_string ( HBRUSH thisbrush ) 
{
    LOGBRUSH brushinfo ; 
    int curcolis , redis , greenis , blueis ;
    GetObject ( thisbrush , sizeof ( LOGBRUSH ) , &brushinfo ) ; 
    curcolis = brushinfo.lbColor ;
    redis = curcolis & 255 ; 
    greenis = ( curcolis & ( 255 << 8 ) ) >> 8 ; 
    blueis = ( curcolis & ( 255 << 16 ) ) >> 16 ;
    sprintf ( RGB_string_space , "%i,%i,%i" , redis ,greenis , blueis ) ;
    return RGB_string_space ;
}

extern int isxflipped , isyflipped , istransposed ;
extern double created_orgx , created_orgy ; 

void atruepoint ( Pointyp * pt )
{
    double tmp ;
    if ( istransposed ) {
         tmp = pt -> x ;
         pt -> x = pt -> y ;
         pt -> y = tmp ; }
    if ( isxflipped ) pt -> x = -( pt -> x ) ; 
    if ( isyflipped ) pt -> y = -( pt -> y ) ;
    return ; 
}        


extern int curcons ; 

void export_area_coords ( HWND hdwnd ) 
{
   int a , b , c , myrecs ; 
   double x ; 
   HBRUSH colbr ; 
   char * cp = screencapt ;
   Constyp * conpt ; 
   Pointyp uplef , uprig , lolef , lorig ; 
   FILE * cfp ; 
   OPENFILENAME opbuff;
   char coordffilter[] = "Area coordinate files (*.acf)\0*.acf\0" ;
   char * tricol ;
   double tmpa , tmpb ;
   int mc ;
   Fuss mb ; 
/*
   if ( !num_spingrid ) {
      noisy() ; 
      sprintf ( junkstr , "To save coordinates for areas, data \nmust have been read as X-Y!" ) ; 
      MessageBox(hdwnd, junkstr ,"ERROR", MB_OK | MB_ICONERROR );
      return ; }
*/
   junkstr[0]='\0';
   memset(&opbuff, 0, sizeof(OPENFILENAME));
   opbuff.lStructSize = sizeof(OPENFILENAME);
   opbuff.hwndOwner = hwnd;
   opbuff.lpstrFilter = coordffilter ;
   opbuff.nFilterIndex = 1;
   opbuff.lpstrFile = junkstr ;
   opbuff.lpstrTitle = "Save map to area-coordinates files...";
   opbuff.nMaxFile = sizeof(junkstr); 
   opbuff.lpstrFileTitle = filename;
   opbuff.nMaxFileTitle = sizeof(filename)-1;
   opbuff.lpstrDefExt = "acf" ;
   opbuff.Flags = OFN_OVERWRITEPROMPT | OFN_PATHMUSTEXIST | OFN_HIDEREADONLY ; 
   if(!GetOpenFileName(&opbuff)) return ; 
   cfp = fopen ( junkstr , "w" ) ; 
   if ( cfp == NULL ) {
      noisy() ; 
      strcat ( junkstr , ": file cannot be opened" ) ; 
      MessageBox(hdwnd, junkstr ,"ERROR",MB_OK | MB_ICONERROR );
      return ; }
   x = consen_minval ; 
   for ( a = 1 ; a < 8 ; ++ a ) {
        tricol = NULL ; 
        for ( b = 0 ; b < rows ; ++ b ) 
             for ( c = 0 ; c < cols ; ++ c ) {
                  if ( sccol[c][b] != a ) continue ;
                  if ( tricol == NULL ) {
                      if ( curcmd_loop == show_consensus ) colbr = consfillcol[sccol[c][b]] ; 
                      else colbr = fillcol[sccol[c][b]] ; 
                      tricol = RGB_string ( colbr ) ; }
                      if ( curcmd_loop == show_consensus )
                         fprintf ( cfp , 
                                "DESCRIPTION=SCORE_%.3f-%.3f\n" , x , x+consen_intrvl ) ;
                      else
                         fprintf ( cfp , 
                                "DESCRIPTION=CELL_%i-%i\n" , b , c ) ;
                      fprintf ( cfp , 
                                "BORDER_COLOR=RGB(%s)\n"
                                "BORDER_STYLE=Solid\n"
                                "BORDER_WIDTH=3\n"
                                "FILL_COLOR=RGB(%s)\n"
                                "FILL_STYLE=Cross-Hatch\n"
                                "CLOSED=YES\n" , tricol , tricol ) ; 
                  uplef.x = created_orgx + ( truecellwid * c ) ; 
                  uplef.y = created_orgy + ( truecellhei * b ) ; 
                  uprig.x = created_orgx + ( truecellwid * ( c + 1 ) ) ; 
                  uprig.y = uplef.y ; 
                  lolef.x = uplef.x ; 
                  lolef.y = created_orgy + ( truecellhei * ( b + 1 ) ) ; 
                  lorig.x = uprig.x ; 
                  lorig.y = lolef.y ; 

                  atruepoint ( &uplef ) ; 
                  atruepoint ( &uprig ) ; 
                  atruepoint ( &lorig ) ; 
                  atruepoint ( &lolef ) ; 

                  fprintf ( cfp , "%.4f %.4f\n" , uplef.x , uplef.y ) ; 
                  fprintf ( cfp , "%.4f %.4f\n" , uprig.x , uprig.y ) ; 
                  fprintf ( cfp , "%.4f %.4f\n" , lorig.x , lorig.y ) ; 
                  fprintf ( cfp , "%.4f %.4f\n" , lolef.x , lolef.y ) ; 
                  fprintf ( cfp , "%.4f %.4f\n" , uplef.x , uplef.y ) ;
                  fprintf ( cfp , "\n" ) ; }
        x += consen_intrvl ; }
    if ( !num_spingrid ) {
          if ( curcmd_loop == show_consensus ) {
             conpt = consen + curcons ;
             for ( a = 0 ; a < spp ; ++ a ) {
               if ( conpt->spmax[a] <= 0 ) continue ;
               if ( spname == NULL ) sprintf ( junkstr , "species %i" , a ) ;
               else strcpy ( junkstr , spname[a] ) ; 
               for ( b = 0 ; b < xymatrix[a].numrecs ; ++ b ) {
                   uplef.x = xymatrix[a].x[b] ; 
                   uplef.y = xymatrix[a].y[b] ;
                   atruepoint ( &uplef ) ;
                   fprintf ( cfp ,           
                         "DESCRIPTION=%s\n"
                         "POINT_SYMBOL=Endemic species\n" 
                         "%.4f %.4f\n\n" , junkstr , uplef.x , uplef.y ) ; }}}
          else {
            cursize = recptr -> size ; 
            lst = recptr -> lst ;
            markscore = 1 ; 
            dorule5 () ; 
            markscore = 0 ; 
            for ( a = 0 ; a < spp ; ++ a ) {
               mc = a / 32 ;
               mb = 1 << ( a % 32 ) ;
               if ( ( intersptr[mc] & mb ) == 0 ) continue ; 
               if ( ( spingrid[mc] & mb ) == 0 ) continue ;
               myrecs = xymatrix[a].numrecs ;
               if ( spname == NULL ) sprintf ( junkstr , "species %i" , a ) ;
               else strcpy ( junkstr , spname[a] ) ; 
               for ( b = 0 ; b < myrecs ; ++ b ) {
                       uplef.x = xymatrix[a].x[b] ; 
                       uplef.y = xymatrix[a].y[b] ; 
                       atruepoint ( &uplef ) ;
                       fprintf ( cfp ,           
                         "DESCRIPTION=%s\n"
                         "POINT_SYMBOL=Endemic species\n" 
                         "%.4f %.4f\n\n" , junkstr , uplef.x , uplef.y ) ; }}}}
    fclose ( cfp ) ; 
    sprintf ( screencapt , "\nSaved coordinates for area to file %s" , junkstr ) ; 
    win_refresh () ; 
    return ; 
}


BOOL CALLBACK FakeGridSizePosFunc(HWND hdwnd, UINT message, WPARAM wParam, LPARAM lParam)
{
    double xlef , xrig , yup , ydn ;
    int ncol , nrow ; 
    HWND hWho ;
    switch(message) {
        case WM_INITDIALOG :
            if ( grid_startx > 10e199 ) {
                      sprintf ( junkstr , "%.3f" , 0 ) ; 
                      SetDlgItemText ( hdwnd , 104 , junkstr ) ;
                      sprintf ( junkstr , "%.3f" , 0.5 ) ;
                      SetDlgItemText ( hdwnd , 106 , junkstr ) ; }
            else {
                sprintf ( junkstr , "%.6f" , grid_startx ) ; 
                SetDlgItemText ( hdwnd , 104 , junkstr ) ;
                sprintf ( junkstr , "%.6f" , grid_width ) ;
                SetDlgItemText ( hdwnd , 106 , junkstr ) ; }
            if ( grid_startx > 10e199 ) {
                      sprintf ( junkstr , "%.3f" , 0 ) ; 
                      SetDlgItemText ( hdwnd , 108 , junkstr ) ;
                      sprintf ( junkstr , "%.3f" , 0.5 ) ; 
                      SetDlgItemText ( hdwnd , 110 , junkstr ) ; }
            else {
                  sprintf ( junkstr , "%.6f" , grid_starty  ) ; 
                  SetDlgItemText ( hdwnd , 108 , junkstr ) ;
                  sprintf ( junkstr , "%.6f" , grid_height ) ; 
                  SetDlgItemText ( hdwnd , 110 , junkstr ) ; }
            strcpy ( junkstr , "0" ) ; 
            SetDlgItemText ( hdwnd , 124 , junkstr ) ;
            SetDlgItemText ( hdwnd , 134 , junkstr ) ;
            FOCUS_ON (IDOK ) ;
            break ; 
        case WM_COMMAND :
                switch(LOWORD(wParam)){
                        case IDOK :
                           GetDlgItemText(hdwnd, 104 , junkstr, 80);  
                           xlef = atof(junkstr);  
                           GetDlgItemText(hdwnd, 106 , junkstr, 80);  
                           xrig = atof(junkstr);
                           GetDlgItemText(hdwnd, 108 , junkstr, 80);  
                           yup = atof(junkstr);  
                           GetDlgItemText(hdwnd, 110 , junkstr, 80);  
                           ydn = atof(junkstr);
                           GetDlgItemText(hdwnd, 124 , junkstr, 80);
                           ncol = atoi ( junkstr ) ; 
                           GetDlgItemText(hdwnd, 134 , junkstr, 80);
                           nrow = atoi ( junkstr ) ; 
                           EndDialog ( hdwnd, 1 ) ;
                           truecellwid = xrig - xlef ;
                           truecellhei = ydn - yup ;
                           grid_startx = xlef - ( ncol * truecellwid ) ;
                           grid_starty = yup - ( nrow * truecellhei ) ; 
                           minx = grid_startx + ( truecellwid / 2 ) ; 
                           maxx = grid_startx + ( truecellwid * cols ) - ( truecellwid / 2 ) ;
                           miny = grid_starty + ( truecellhei / 2 ) ; 
                           maxy = grid_starty + ( truecellhei * rows ) - ( truecellhei / 2 ) ;
                           grid_created = 1 ;
                           faked_a_grid = 1 ;
                           created_orgx = grid_startx ; 
                           created_orgy = grid_starty ; 
                           return 1 ; 
                        case IDCANCEL :
                             EndDialog(hdwnd,0);
                             return 0;
                        default :
                                break; }
         break; }
    return 0;
}


void export_divagis_area_coords ( HWND hdwnd ) 
{
   int a , b , c , myrecs ; 
   double x ; 
   HBRUSH colbr ; 
   char * cp = screencapt ;
   Constyp * conpt ; 
   Pointyp uplef , uprig , lolef , lorig ; 
   FILE * cfp ; 
   OPENFILENAME opbuff;
   char file1name[ _MAX_PATH ] , file2name [ _MAX_PATH ] ; 
   char txtfilter[] = "DIVAGIS coordinate files (*.txt)\0*.txt\0" ;
   char * tricol ;
   double tmpa , tmpb ;
   int mc ;
   int numcuad = 1 ; 
   Fuss mb ; 
/**
   if ( !num_spingrid ) {
      noisy() ; 
      sprintf ( junkstr , "To save coordinates for areas, data \nmust have been read as X-Y!" ) ; 
      MessageBox(hdwnd, junkstr ,"ERROR", MB_OK | MB_ICONERROR );
      return ; }
*/
   junkstr[0]='\0';
   memset(&opbuff, 0, sizeof(OPENFILENAME));
   opbuff.lStructSize = sizeof(OPENFILENAME);
   opbuff.hwndOwner = hwnd;
   opbuff.lpstrFilter = txtfilter ;
   opbuff.nFilterIndex = 1;
   opbuff.lpstrFile = junkstr ;
   opbuff.lpstrTitle = "File to save cell coordinates...";
   opbuff.nMaxFile = sizeof(junkstr); 
   opbuff.lpstrFileTitle = filename;
   opbuff.nMaxFileTitle = sizeof(filename)-1;
   opbuff.lpstrDefExt = "txt" ;
   opbuff.Flags = OFN_OVERWRITEPROMPT | OFN_PATHMUSTEXIST | OFN_HIDEREADONLY ; 
   if(!GetOpenFileName(&opbuff)) return ;
   strcpy ( file1name , junkstr ) ; 
   cfp = fopen ( junkstr , "w" ) ; 
   if ( cfp == NULL ) {
      noisy() ; 
      strcat ( junkstr , ": file cannot be opened" ) ; 
      MessageBox(hdwnd, junkstr ,"ERROR",MB_OK | MB_ICONERROR );
      return ; }
   x = consen_minval ;
   /*** First, save cell coordinates *************/
   for ( a = 1 ; a < 8 ; ++ a ) {
        tricol = NULL ; 
        for ( b = 0 ; b < rows ; ++ b ) 
             for ( c = 0 ; c < cols ; ++ c ) {
                  if ( sccol[c][b] != a ) continue ;
                  if ( tricol == NULL ) {
                      if ( curcmd_loop == show_consensus ) colbr = consfillcol[sccol[c][b]] ; 
                      else colbr = fillcol[sccol[c][b]] ; 
                      tricol = RGB_string ( colbr ) ; }
                  uplef.x = created_orgx + ( truecellwid * c ) ; 
                  uplef.y = created_orgy + ( truecellhei * b ) ; 
                  uprig.x = created_orgx + ( truecellwid * ( c + 1 ) ) ; 
                  uprig.y = uplef.y ; 
                  lolef.x = uplef.x ; 
                  lolef.y = created_orgy + ( truecellhei * ( b + 1 ) ) ; 
                  lorig.x = uprig.x ; 
                  lorig.y = lolef.y ; 

                  atruepoint ( &uplef ) ; 
                  atruepoint ( &uprig ) ; 
                  atruepoint ( &lorig ) ; 
                  atruepoint ( &lolef ) ;
                  
                  fprintf ( cfp , "%i " , numcuad ++ ) ; 
                  fprintf ( cfp , "%.4f %.4f\n" , uplef.x , -uplef.y ) ; 
                  fprintf ( cfp , "%.4f %.4f\n" , uprig.x , -uprig.y ) ; 
                  fprintf ( cfp , "%.4f %.4f\n" , lorig.x , -lorig.y ) ; 
                  fprintf ( cfp , "%.4f %.4f\n" , lolef.x , -lolef.y ) ; 
                  fprintf ( cfp , "%.4f %.4f\n" , uplef.x , -uplef.y ) ;
                  fprintf ( cfp , "END\n" ) ; }
        x += consen_intrvl ; }
    fclose ( cfp ) ; 
    /*** Now, save point coordinates *********/
    if ( num_spingrid ) {
        junkstr[0]='\0';
        memset(&opbuff, 0, sizeof(OPENFILENAME));
        opbuff.lStructSize = sizeof(OPENFILENAME);
        opbuff.hwndOwner = hwnd;
        opbuff.lpstrFilter = txtfilter ;
        opbuff.nFilterIndex = 1;
        opbuff.lpstrFile = junkstr ;
        opbuff.lpstrTitle = "File to save point coordinates...";
        opbuff.nMaxFile = sizeof(junkstr); 
        opbuff.lpstrFileTitle = filename;
        opbuff.nMaxFileTitle = sizeof(filename)-1;
        opbuff.lpstrDefExt = "txt" ;
        opbuff.Flags = OFN_OVERWRITEPROMPT | OFN_PATHMUSTEXIST | OFN_HIDEREADONLY ; 
        if(!GetOpenFileName(&opbuff)) return ; 
        cfp = fopen ( junkstr , "w" ) ; 
        strcpy ( file2name , junkstr ) ; 
        if ( cfp == NULL ) {
          noisy() ; 
          strcat ( junkstr , ": file cannot be opened" ) ; 
          MessageBox(hdwnd, junkstr ,"ERROR",MB_OK | MB_ICONERROR );
          return ; }
        fprintf ( cfp , "SPECIES\tLongitude\tLatitude\n" ) ; 
        if ( curcmd_loop == show_consensus ) {
             conpt = consen + curcons ;
             for ( a = 0 ; a < spp ; ++ a ) {
               if ( conpt->spmax[a] <= 0 ) continue ;
               if ( spname == NULL ) sprintf ( junkstr , "species %i" , a ) ;
               else strcpy ( junkstr , spname[a] ) ; 
               for ( b = 0 ; b < xymatrix[a].numrecs ; ++ b ) {
                   uplef.x = xymatrix[a].x[b] ; 
                   uplef.y = xymatrix[a].y[b] ;
                   atruepoint ( &uplef ) ;
                   fprintf ( cfp ,           
                         "%s\t"
                         "%.4f\t%.4f\n" , junkstr , uplef.x , -uplef.y ) ; }}}
        else {
            cursize = recptr -> size ; 
            lst = recptr -> lst ;
            markscore = 1 ; 
            dorule5 () ; 
            markscore = 0 ; 
            for ( a = 0 ; a < spp ; ++ a ) {
               mc = a / 32 ;
               mb = 1 << ( a % 32 ) ;
               if ( ( intersptr[mc] & mb ) == 0 ) continue ; 
               if ( ( spingrid[mc] & mb ) == 0 ) continue ;
               myrecs = xymatrix[a].numrecs ;
               if ( spname == NULL ) sprintf ( junkstr , "species %i" , a ) ;
               else strcpy ( junkstr , spname[a] ) ; 
               for ( b = 0 ; b < myrecs ; ++ b ) {
                       uplef.x = xymatrix[a].x[b] ; 
                       uplef.y = xymatrix[a].y[b] ; 
                       atruepoint ( &uplef ) ;
                       fprintf ( cfp ,           
                         "%s\t"
                         "%.4f\t%.4f\n" , junkstr , uplef.x , -uplef.y ) ; }}}
        fclose ( cfp ) ;
        sprintf ( screencapt , "\nSaved coordinates to files %s (cells) and %s (points)" , file1name , file2name ) ; 
      }
    else sprintf ( screencapt , "\nSaved coordinates for cells to file %s (no points to save)" , file1name ) ; 
    win_refresh () ; 
    return ; 
}


