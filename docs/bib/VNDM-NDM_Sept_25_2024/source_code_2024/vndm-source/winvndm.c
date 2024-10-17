/*****
  NOTE: a few portions of this code taken from the code for
        TNT --some, written by K.C.Nixon 1999 
******/           

#include <windows.h>
#include <windowsx.h>
#include <stdio.h>
#include <string.h>
#define VTYPE   
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
#include <tchar.h>

extern ignore_sp_lists ; 
int data_is_sampled = 0 ; 
extern int query , consensus_is_sample , didaboot , run_autoconsense , run_autosave ; 
extern Artyp * bootinit , * rec ; 
int hide_the_map = 1 ; 
int ridofdupes = 0 ; 
extern int weight_species , use_edge_props ; 
extern int * species_tree ; 
extern int nocommas , dolatlong ; 
extern FILE * outspace ;
extern char cur_duwc_act ; 
extern char ** isdefd ; 
int WINBUFSIZ ;
int PointWidth = 3 ; 
extern int black_n_white , show_individual_dots ; 
extern int grid_effect ; 
extern int grid_created , data_is_xydata ;
int faked_a_grid = 0 ; 
extern unsigned long int * spingrid ;
extern int num_spingrid ;
extern double truecellhei , truecellwid ;
extern double grid_starty , grid_startx ; 
#define SPKEY  ( 1 << 10 ) 
#define ALTEQUAL (  131            | SPKEY ) 
#define    ALT1   (   120           | SPKEY )
#define  ALTDEL  (  163            | SPKEY )
int fake_main ( int , char ** ) ; 
extern int cellhei , cellwid ; 
extern int rows , cols , spp ;
extern int numrecs ; 
int sometextodo = 0 ;
extern int atcoordx , atcoordy ; 
extern char ** sccol ; 
void (*curcmd_loop ) ( int ) ;
void viewscore ( int ) ;
void show_duwc ( int ) ;
void cmd_loop ( int ) ;
void showspecies ( int ) ;
void show_consensus ( int ) ;
void viewmarks ( int ) ;
void showsuperset ( int ) ; 
extern char comstring[] ; 
int screen_shift = 0 ;
int maxlinwidth ;
int min_screen_shift ;
int autoshift = 1 ; 
int text_width ;
int WinHeight ;
int WinWidth ; 
#define MAXSCREEN_SIZE 150
int linwidth [ MAXSCREEN_SIZE ] ; 
int report_score_difference = 0 ; 
int autopaintcells = 0 ; 
int trackmouse = 1 ; 
int last_clicked_cell = -1 ;
extern char ** spname ;
typedef struct {
            int defd ; 
            int numrecs , trurecs ;
            float * x ;
            float * y ; } Coordtyp ; 
extern Coordtyp * xymatrix ;
extern int expand_cell_definition , just_out_of_duwc ;

#define   inva      InvalidateRect ( hwnd, NULL , 1 )  
#define TOGGLE(x)  x = 1 - x ; 
#define DERR( x ) { noisy() ; MessageBox ( hdwnd, x, "ERROR", MB_OK | MB_ICONERROR ) ; break ; } 
#define BUTT_CHECK( ctrl ) SendDlgItemMessage( hdwnd,  ctrl , BM_SETCHECK, (WPARAM) BST_CHECKED , 0 )
#define BUTT_UNCHEK( ctrl ) SendDlgItemMessage( hdwnd,  ctrl , BM_SETCHECK, (WPARAM) BST_UNCHECKED , 0 )
#define CTRL_DISABLE( ctrl ) Button_Enable ( GetDlgItem ( hdwnd , ctrl ) , FALSE )   
#define SPIN_DISABLE( ctrl ) \ 
                   { SetDlgItemText ( hdwnd , GetDlgCtrlID ( SendMessage( GetDlgItem ( hdwnd , ctrl ) , UDM_GETBUDDY, 0, 0) ) , "" ) ; \
                     Button_Enable ( SendMessage( GetDlgItem ( hdwnd , ctrl ) , UDM_GETBUDDY, 0, 0 ) , FALSE ) ; \ 
                     Button_Enable ( GetDlgItem ( hdwnd , ctrl ) , FALSE ) ; } 
#define CTRL_ENABLE( ctrl ) Button_Enable ( GetDlgItem ( hdwnd , ctrl ) , TRUE )   
#define SETTEXT( x , y ) \
          { sprintf ( junkstr , "%s" , x ) ; SetDlgItemText ( hdwnd , y , junkstr ) ; } 
#define SETINT( x , y ) \
          { sprintf ( junkstr , "%i" , x ) ; \
            SetDlgItemText ( hdwnd , y , junkstr ) ; } 
#define GETINT( x , y ) \ 
          { GetDlgItemText(hdwnd, ( y ) , junkstr, 80); \ 
            x = atoi(junkstr); } 
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
#define ON_SPIN case WM_VSCROLL
#define CHG_UPDOWN( ctrl ) \
            { hWho = GetDlgItem ( hdwnd , ctrl ) ; \
              i = ( SendMessage(  hWho , UDM_GETPOS, 0, 0) ) & 65535 ; \
              wsprintf ( junkstr ,"%i",  i ) ; \
              hWho = SendMessage ( GetDlgItem (hdwnd , ctrl ) , UDM_GETBUDDY, 0 , 0 ) ; \
              i = GetDlgCtrlID ( hWho ) ; \
              SetDlgItemText(hdwnd, i , junkstr ); } 

void read_batch_menu_file ( FILE * , char * ) ; 
char vndm_infilename[_MAX_PATH ] ; 

/****  THESE ARE VARIABLES USED IN SCOPE READING FUNCTION, BELOW *************/
#define SELECT_DIALOG StartSelectFun ( hdwnd )  
#define GROUPSELECT_DIALOG( z , x , y )  resetscopelist ( z , (x) , ( y ) ) ; 
char selthings [ Namesize ] , unselthings [ Namesize ] ;
char ** selthingnames ;
signed char * inortax ; 
int selnumthings ;
int * tmpcurlist ; 
char * selectlist ;
char itemnamespace [Namesize];
char * itemname;
BOOL CALLBACK LastPointModeFunc(HWND , UINT , WPARAM, LPARAM ) ;
BOOL CALLBACK MatrixShrinkFunc(HWND , UINT , WPARAM, LPARAM ) ;
int ready_to_start_line = 0 ; 
extern int last_point_extend ;

/************END OF VARIABLES FOR SCOPE READING FUNCTION ********/

int only_show_points = 0 ; 
static HDC Userfile_emf = NULL ;
void showmap ( HDC ) ;
void show_basic_grid ( HDC ) ; 
static int num_emf_trees ; 
unsigned long int emf_addtoy ; 
void draw_to_userfile ( short int * ) ;
int data_type ; 
int show_tools = 1 ; 
int keep_treemode = 1 ; 
int stepmat_to_do ; 
int autosetit ; 
int autoset_nt = 0 ; 
int store_treemsg ; 
int batch_memory = 0 ; 
char last_menu_batch_name [ Namesize ] ;
#define MAX_ACTION_RECORD 100
#define MAX_TOTAL_BATCH 300 
char ** menu_batch_names ; 
int storing_batch_menus = 0 , running_batch_menus = 0 ;
int at_batch_scope_inst , at_batch_inst ;
int have_batch_to_run = 0 ; 
int max_batch_actions = 20 ; 
int nt_batch = 100 , nc_batch = 300 , ntrees_batch = 1000 ; 
char treecharcomd [ Namesize ] ; 
int txtdatin ;
int autotreegroups ; 

extern int nummaplins , selected_maplin , selmappoint , selmappointmax ;
extern selpoint_only = 0 ; 
int get_selected_maplin ( HWND , int * ) ;
void add_point_to_mapline ( HWND ) ;
void delete_maplin_point ( HWND) ;
extern int doautolines ;
int rbuttisdn = 0 ; 
extern HWND mainwnd ;
extern int lasmousecoordsx , lasmousecoordsy ;
int last_point_extend = 1 ;
int grid_is_locked = 0 ; 


int allow_edition = 0 ;
extern int query ; 

static short int *BoxTree;
HANDLE ColorCode[256] ;
HANDLE ColorAmbig ;
int UserColor[11][3] ; 
int do_color_map = 1 ;
int goto_treenode = -1 ;
POINT Cursat ;
char * MarkedNod ;
int HaveMarkedNodz ;

int text_height = 18;
int password_ok = 0 ;
int abortit = 0 ;
char password[25] ;
unsigned long int serial ; 

char use_charnames ;
int preview_trees ; 

int ignore_continuous = 0 ; 
short int * scoplist ;
int scoplim ; 
char * junkptr ; 

HMENU hmu ;
HFONT hfont ;
CHOOSEFONT cfo;
LOGFONT lf ;

#define BUGCHK 1

HCURSOR hNormal, hGlass, hCollapse;
LRESULT CALLBACK WindowFunc(HWND, UINT, WPARAM, LPARAM);

HWND hList, hStatusWnd, Tablehwnd, Prunehwnd, BoxTreehwnd, toolhwnd;
HWND mathwnd[10], hStatusWnd, hProgWnd, dqchwnd, captionhwnd;
HINSTANCE hInst, PsInst;
HMENU hmainmenu, hTreeMenu, hCladMenu, hCurrentMenu;
 FILE *inpf;
short int largest_node, imat ;
static int treelbow = 0 ; 
int bleng = 30, bspan = 14, bthick = 2 ;
static int tree_orgx, tree_orgy ;
static int maxtree_orgx = 0 , maxtree_orgy = 0 ;
static int tracktrees = 1 ; 
HPEN hBranchpen , hYellowPen , hBlackPen , hWhitePen;
static HPEN hRedMarkPen , hGreenMarkPen;
static HPEN hNodPen = NULL ;
static int NodPenWidth ; 
static double currtreelen ; 
#define MEMTREES 1
static int tablestart, tableend , * tablevals ; 
static int treeboxing = 0 ; 

unsigned dwChildId;
unsigned _stdcall ArnThread(void *lpdata);
unsigned _stdcall RatchetThread(void *lpdata);
unsigned _stdcall AnalyzeThread(void *lpdata);
unsigned _stdcall JackThread(void *lpdata);
unsigned _stdcall ChremThread(void *lpdata);

OPENFILENAME opbuff;

int cwids[5];

RECT WinDim;
RECT BoxDim ;

#define NUMPARTS 5
int parts[NUMPARTS+1];
char szWinName[] = "MyWin"; /* name of window class */
char filefilter[] = "TNT files (*.tnt)\0*.tnt\0Tree files (*.tre)\0*.tre\0Data files (*.dat)\0*.dat\0ALL files\0*.*\0";
char trffilter[] = "Tree files (*.tre)\0*.tre\0ALL files\0*.*\0";
char exefilter[] = "EXECUTABLES (*.exe)\0*.exe\0";
char metaffilter[] = "Metafiles (*.emf)\0*.emf\0" ; 
char mapffilter[] = "Coordinate Files (*.xyd)\0*.xyd\0" ; 
static char fn[MAX_PATH];
char filename[MAX_PATH+3];

int files_to_recall = 0 ;
int recall_more_files = 1 ; 
char last_five_infiles[6][MAX_PATH+3] ;
char iscompactfile[6] ;
int mark_treefile = 0 ; 
MENUITEMINFO lastfiles[6] , * ufalala ;
char * newfilename ; 

int blanks_in ( char * txt )
{
    char * cp = txt ;
    while ( * cp != '\0' ) {
         if ( * cp == ' ' ) * cp = '^' ;
         ++ cp ; }
    return 0 ;            
}

void tntoggle ( char * a , char * cmd , char * c0 , char * c1 )
{
    if ( * a ) {
        dotnt ( "%s %s;" , cmd , c1 ) ;
        if ( storing_batch_menus ) * a = 0 ; }
    else { 
        dotnt ( "%s %s;" , cmd , c0 ) ;
        if ( storing_batch_menus ) * a = 1 ; }
    return ; 
} 
    
void quit_windows_interface ( void )
{
    DestroyWindow ( hwnd ) ;
    hwnd = NULL ; 
}     

int winismin = 0 ; 

void set_font_xfeatures ( LOGFONT * thef ) 
{
    thef->lfEscapement = 0 ;
    thef->lfOrientation = 0 ;
    thef->lfWeight = 400 ;
    thef->lfItalic = 0 ;
    thef->lfUnderline = 0 ;
    thef->lfStrikeOut = 0 ;
    thef->lfCharSet = DEFAULT_CHARSET ;
    thef->lfOutPrecision = 3 ;
    thef->lfClipPrecision = 2 ;
    thef->lfQuality = 1 ;  
}


void no_cmd_loop ( int i ) { return ; }

int WINAPI WinMain(HINSTANCE hThisInst, HINSTANCE hPrevInst, LPSTR lpszArgs, int nWinMode)

{
    MSG msg;
    WNDCLASSEX wcl;
    HACCEL hAccel;
    int i , a, found_semic ;
    clock_t ini ;
    sccol = NULL ; 
    curcmd_loop = no_cmd_loop ;     
    hGlass = LoadCursor(NULL, IDC_WAIT);
    hCollapse = LoadCursor(hThisInst,"Collapse");
    /* Define a window class */
    wcl.cbSize = sizeof(WNDCLASSEX);
    wcl.hInstance = hThisInst; 
    wcl.lpszClassName = szWinName; 
    wcl.lpfnWndProc = WindowFunc; 
    wcl.style = CS_DBLCLKS; 
    wcl.hIcon = LoadIcon(hThisInst, "VNDM"); 
    wcl.hIconSm = NULL; 
    wcl.hCursor = LoadCursor(NULL, IDC_ARROW ); 
    hNormal = wcl.hCursor;
    wcl.lpszMenuName = "CladMenu"; 
    wcl.cbClsExtra = 0; 
    wcl.cbWndExtra = 0; 
    wcl.hbrBackground = (HBRUSH) GetStockObject(WHITE_BRUSH);
    if(!RegisterClassEx(&wcl)) return(0);
    sprintf(junkstr, "VNDM - 3.1" );
    hwnd = CreateWindow(
        szWinName, 
        junkstr, 
        WS_OVERLAPPEDWINDOW | WS_VSCROLL | WS_HSCROLL ,   
        CW_USEDEFAULT, 
        CW_USEDEFAULT, 
        CW_USEDEFAULT, 
        CW_USEDEFAULT, 
        HWND_DESKTOP, 
        NULL,
        hThisInst, 
        NULL 
    );
    mainwnd = hwnd ; 
    hInst = hThisInst;
    hAccel = LoadAccelerators(hThisInst, "CladMenu");

    ShowWindow ( hwnd , SW_MAXIMIZE ) ;
    UpdateWindow(hwnd);
    InitCommonControls();
    InvalidateRect(hwnd,NULL,1);

    hmainmenu = GetMenu(hwnd);

    hCladMenu = LoadMenu(hInst,"CladMenu");
    strcpy(junkstr,"NADA!");
    hStatusWnd = CreateStatusWindow(WS_CHILD | WS_VISIBLE | CCS_BOTTOM | SBARS_SIZEGRIP, junkstr, hwnd, 101);
    ResetStatus(hwnd);
 
    hmu = GetMenu(hwnd);
    EnableMenuItem(hmu, IDM_FILE, MF_ENABLED);
    EnableMenuItem(hmu, IDM_SETTINGS, MF_ENABLED);
    EnableMenuItem(hmu, IDM_FORMATS , MF_ENABLED ) ; 
    EnableMenuItem(hmu, IDM_HELP, MF_ENABLED);
    EnableMenuItem(hmu, IDM_CONSOLE, MF_ENABLED);
    EnableMenuItem(hmu, IDM_ABOUT, MF_ENABLED);
    cmhwnd = NULL ;
    DrawMenuBar ( hwnd ) ; 

    hRedMarkPen = CreatePen ( PS_SOLID, 8 , RGB ( 255 , 0 , 0 ) ) ;
    hGreenMarkPen = CreatePen ( PS_SOLID, 8 , RGB ( 0 , 255 , 100 ) ) ;
    create_map_pens () ; 
    strcpy ( lf.lfFaceName , "Courier" ) ;
    lf.lfHeight = 18 ; 
    lf.lfWeight = FW_DONTCARE ;
    lf.lfCharSet = DEFAULT_CHARSET ;
    lf.lfPitchAndFamily = 49 ;
    set_font_xfeatures ( &lf ) ; 
    hfont = CreateFontIndirect(&lf);
    hdc = GetDC ( hwnd ) ; 
    SelectFont ( hdc , hfont ) ;
    GetTextFace ( hdc , 80 , junkstr ) ;
    if ( strcmp ( junkstr ,"Courier" ) ) {
       strcpy ( lf.lfFaceName , "Terminal" ) ;
       lf.lfHeight = 16 ; 
       lf.lfWeight = FW_DONTCARE ;
       lf.lfCharSet = DEFAULT_CHARSET ;
       lf.lfPitchAndFamily = 49 ; 
       hfont = CreateFontIndirect(&lf);
       hdc = GetDC ( hwnd ) ; 
       SelectFont ( hdc , hfont ) ;
       GetTextFace ( hdc , 80 , junkstr ) ;
       if ( strcmp ( junkstr ,"Terminal" ) ) {
          i = MessageBox ( hwnd , "The fonts \"Terminal\" and \"Courier\" (which make best viewing) are not available.\n\n     Continue anyway ?\n" , "Warning" , MB_YESNO | MB_ICONWARNING ) ; 
          if ( i == IDNO ) exit ( 0 ) ; }}
    set_screen_size ( 0 ) ;
    GetClientRect(hwnd, &BoxDim);

    fake_main ( __argc , __argv ) ;
   
    sprintf(junkstr, "VNDM - 3.1 - %s" , vndm_infilename );
    SetWindowText ( hwnd , junkstr ) ; 

    WINBUFSIZ = 2 * rows ;
    maxlinwidth = 2 * cols ; 

    GetClientRect(hwnd, &WinDim);
    cellhei = ( WinDim.bottom - WinDim.top ) / ( rows + 2 ) ;
    cellwid = ( WinDim.right - WinDim.left ) / ( cols + 2 ) ;
    if ( cellhei > 12 ) cellhei = 12 ;
    if ( cellwid > 12 ) cellwid = 12 ;

    initialize_fill_bitmaps () ; 

    /******  save autoconsensus and quit **************/
    if ( run_autoconsense ) {
        if ( didaboot ) consensus_is_sample = 1 ;
        cmd_loop ( 1 ) ; }

    if ( run_autosave ) {
        auto_save_all_results ( ) ;
        exit ( 0 ) ; }
         
    if ( !abortit ) {
      while(GetMessage(&msg, NULL, 0, 0) ) {
           if(!IsDialogMessage(BoxTreehwnd, &msg)){
              if(!TranslateAccelerator(hwnd, hAccel, &msg)){
                  TranslateMessage(&msg); 
                  DispatchMessage(&msg); 
              }}}} 
    if(IsMenu(hCladMenu))DestroyMenu(hCladMenu);
    ReleaseDC(hwnd, hdc);
    return msg.wParam;
}


int clickatcell ( HWND mywnd )
{  long int a , b , xend , xstart , yend , ystart ;
   long int x , y ; 
   GetCursorPos ( &Cursat ) ;
   ScreenToClient ( mywnd , &Cursat ) ; 
   x = Cursat.x ;
   y = Cursat.y ; 
   xend = 10 - atcoordx ; 
   for ( a = 0 ; a < cols ; ++ a ) {
       xstart = xend ; 
       xend += cellwid ;
       if ( xstart < x && xend > x ) {
           yend = 30 - atcoordy ;
           for ( b = 0 ; b < rows ; ++ b ) {
               ystart = yend ;
               yend += cellhei ;
               if ( ystart <= y && yend >= y )
                    return ( ( b * cols ) + a ) ; }}}
   return -1 ; 
}

void get_min_max_square ( int * c , int * C , int * r , int * R )
{
    int minc = 1000000000 , maxc = 0 , minr = 1000000000 , maxr = 0 ;
    int a , b , mc , snumar ;
    unsigned long int mb ; 
    unsigned long int * areapt = recptr -> lst ;
    if ( recptr -> size == 0 ) {
       * c = * C = * r = * R = -1 ;
       return ; }
    for ( a = 0 ; a < cols ; ++ a ) 
      for ( b = 0 ; b < rows ; ++ b ) {
         if ( !isdefd [ b ] [ a ] ) continue ; 
         snumar = ( cols * b ) + a ;
         mb = 1 << ( snumar % 32 ) ;
         mc = snumar / 32 ;
         if ( ( areapt [ mc ] & mb ) == 0 ) continue ;
         if ( a > maxc ) maxc = a ; 
         if ( a < minc ) minc = a ; 
         if ( b > maxr ) maxr = b ; 
         if ( b < minr ) minr = b ; }
   * c = minc ;
   * C = maxc ;
   * r = minr ;
   * R = maxr ;
   return ; 
}    

int fill_inside_area ( HWND mywnd )
{
    int whr = clickatcell( mywnd ) ;
    int i , j , mc , a , b ; 
    int minc , maxc , minr , maxr ;
    unsigned long int mb , snumar , * areapt = recptr -> lst ;
    int myc , myr ; 
    if ( whr < 0 ) return 0 ;
    get_min_max_square ( &minc , &maxc , &minr , &maxr ) ;
    if ( minc < 0 ) return 0 ; 
    myc = whr % cols ;
    myr = whr / cols ; 
    if ( myc < minc ) minc = myc ;
    if ( myc > maxc ) maxc = myc ; 
    if ( myr < minr ) minr = myr ;
    if ( myr > maxr ) maxr = myr ; 
    for ( a = minc ; a <= maxc ; ++ a )
      for ( b = minr ; b <= maxr ; ++ b ) {
         if ( !isdefd [ b ] [ a ] ) continue ; 
         snumar = ( cols * b ) + a ;
         mb = 1 << ( snumar % 32 ) ;
         mc = snumar / 32 ;
         if ( ( areapt [ mc ] & mb ) == 0 ) {
             ++ recptr -> size ;
             areapt [ mc ] |= mb ; }} 
   dorule5 () ; 
   showcurset () ; 
   return 1 ; 
}

int showingx , showingy ;

int cursisin ( int x , int y )
{
    if ( x > showingx && x < ( showingx + cellwid ) &&
         y > showingy && y < ( showingy + cellhei ) ) return 1 ;
    showingy += ( cellhei * 3 ) / 2 ;
    return 0 ; 
}

int clickatcolor ( HWND mywnd )
{  long int a , b , xend , xstart , yend , ystart ;
   long int x , y ;
   if ( black_n_white ) return -1 ; 
   GetCursorPos ( &Cursat ) ;
   ScreenToClient ( mywnd , &Cursat ) ; 
   x = Cursat.x ;
   y = Cursat.y ; 
   if ( curcmd_loop == show_consensus ) {
      showingy = 30 - atcoordy ;
      showingx = ( 30 + ( cellwid * cols )) - atcoordx ; 
      if ( cursisin ( x , y ) ) return 0 ;
      for ( a = 1 ; a < 8 ; ++ a ) 
           if ( cursisin ( x , y ) ) return a ; }
   if ( curcmd_loop == viewscore ) {
      showingy = 50 - atcoordy ;
      showingx = ( 30 + ( cellwid * cols )) - atcoordx ; 
      if ( cursisin ( x , y ) ) return 0 ; 
      if ( cursisin ( x , y ) ) return 1 ; 
      if ( cursisin ( x , y ) ) return ( 1 | 2 ) ; 
      if ( cursisin ( x , y ) ) return ( 1 | 4 ) ; 
      if ( cursisin ( x , y ) ) return ( 2 ) ; 
      if ( cursisin ( x , y ) ) return ( 4 ) ; }
   if ( curcmd_loop == show_duwc ) {
      showingy = 50 - atcoordy ;
      showingx = ( 30 + ( cellwid * cols )) - atcoordx ; 
      if ( cursisin ( x , y ) ) return 0 ; 
      if ( cursisin ( x , y ) ) return 1 ; 
      if ( cursisin ( x , y ) ) return ( 2 ) ; 
      if ( cursisin ( x , y ) ) return ( 1 | 2 ) ; }
   return -1 ;
}   

void copygil ( int where )
{
    atcoordy -= where * ( cellhei * rows ) / 10 ;
    if ( atcoordy < 0 ) atcoordy = 0 ; 
    return ;
}

int give_scroll_pos ( void )
{
    return atcoordy / cellhei ;
}

int give_total_lines ( void )
{
    return ( 2 * rows ) ;
}


HBITMAP hbitmap ;
HDC hMemoryDC , Introhdc ;
BITMAP bm ; 
extern int logsetsonly ; 

#define GLOCKERR  \
     if ( grid_is_locked ) {   \
          MessageBox ( hwnd , "Grid is locked (unlock with Settings/LockGrid)" , "ERROR" , MB_OK | MB_ICONERROR ) ; \
          break ; }

LRESULT CALLBACK WindowFunc(HWND hwnd, UINT message, WPARAM wParam, LPARAM lParam)

{
    int a , b , c , iscapital , iscontrol ;
    char chari ; 
    int response, i,j,k,l, old_xread, skipit ;
    char * cp ;
    short int * man ;
    double adoub ; 
    HCURSOR tmpcurs ; 
    PAINTSTRUCT paintstruct;
    char localstr[512], save_path[MAX_PATH];
    RECT rect;
    OPENFILENAME ofn;
    static SCROLLINFO sinfo ;
    hmainmenu = GetMenu(hwnd);
    switch(message) {
        case WM_SIZE :
        case WM_MOVE : 
           SendMessage(hStatusWnd, WM_SIZE, wParam, lParam);
           if ( cmhwnd != NULL ) SendMessage( cmhwnd , WM_SIZE , wParam , lParam ) ; 
           set_screen_size ( 1 ) ; 
           ResetStatus(hwnd);
           break;

        case WM_MOUSEWHEEL :
           j = LOWORD ( wParam ) ;
           i = GET_WHEEL_DELTA_WPARAM(wParam);
           if ( !i ) break ;
           if ( !grid_created ) {
              if ( ( j & MK_CONTROL ) ) {
                  if ( i > 0 )
                       SendMessage ( hwnd , WM_KEYDOWN , VK_NEXT , 0 ) ;
                  else SendMessage ( hwnd , WM_KEYDOWN , VK_PRIOR , 0 ) ; }
              else {
                  if ( i < 0 ) SendMessage ( hwnd , WM_VSCROLL , SB_PAGEDOWN , 0 ) ;
                  else SendMessage ( hwnd , WM_VSCROLL , SB_PAGEUP , 0 ) ; }}
           else {
              if ( ( j & MK_CONTROL ) ) {
                  if ( i > 0 ) 
                       SendMessage ( hwnd , WM_COMMAND , IDM_CTRLMOUSEWHEELDN , 0 ) ; 
                  else SendMessage ( hwnd , WM_COMMAND , IDM_CTRLMOUSEWHEELUP , 0 ) ; }
              else {
                  if ( i < 0 ) SendMessage ( hwnd , WM_VSCROLL , SB_PAGEDOWN , 0 ) ;
                  else SendMessage ( hwnd , WM_VSCROLL , SB_PAGEUP , 0 ) ; }}
           break ; 

        case WM_MOUSEMOVE :
            if ( !grid_created && rbuttisdn ) {
                if ( new_mouse_position () )
                     inva ;
                break ; }
            if ( !trackmouse && !autopaintcells ) break ; 
            last_clicked_cell = clickatcell ( hwnd ) ;
            if ( trackmouse ) 
                  if ( last_clicked_cell >= 0 ) UpdateStatus ( hwnd ) ;
            if ( last_clicked_cell < 0 ) break ;
            if ( autopaintcells != 0 && wParam != 0 && 
                 ( curcmd_loop == cmd_loop || 
                   ( curcmd_loop == showspecies && ( autopaintcells & 1 ) ) ) ) {     
               if ( ( wParam & MK_LBUTTON ) ) {
                  response = last_clicked_cell ; 
                  if ( autopaintcells == 2 ) 
                     setcellon ( response , 1 ) ;
                  if ( ( autopaintcells & 1 ) ) 
                     setcellon ( response , 0 ) ; }
               else
               if ( ( wParam & MK_RBUTTON ) ) {
                  response = last_clicked_cell ; 
                  if ( autopaintcells == 2 ) 
                     setcelloff ( response , 1 ) ;
                  if ( ( autopaintcells & 1 ) ) 
                      setcelloff ( response , 0 ) ; }}
            break;
        case WM_LBUTTONUP :
           j = LOWORD ( wParam ) ;
           if ( ( j & MK_CONTROL ) && allow_edition && curcmd_loop == cmd_loop ) {
                 if ( !fill_inside_area ( hwnd ) ) 
                        MessageBox ( hwnd, "Note: ctrl-click embeds all existing cells in a square\n(i.e. click in between some cells to use)", "Warning", MB_OK ) ;
                 break ; }            
             if ( grid_created && !allow_edition && !autopaintcells ) {
                   if ( !sometextodo ) curcmd_loop ( VK_BACK ) ; 
                   sometextodo = just_out_of_duwc = 0 ;
                   inva ; 
                   break ; }
             rbuttisdn = 0 ;
             lasmousecoordsx = lasmousecoordsy = 65535 ;
             if ( ready_to_start_line ) {
               ready_to_start_line = 0 ;
               if ( !grid_created ) { start_a_new_line () ; inva ; }
               break ; }
             if ( !nummaplins || grid_created ) break ;
             a = selected_maplin ; 
             selected_maplin = get_selected_maplin ( hwnd , &selmappoint ) ;
             if ( a != selected_maplin ) selpoint_only = 1 ;
             else selpoint_only = 1 - selpoint_only ;
             if ( selected_maplin >= 0 &&
                  selmappoint == maplin[selected_maplin].numpoints - 1 )
                  selpoint_only = 1 ;  
             if ( doautolines ) selpoint_only = 0 ; 
             InvalidateRect ( hwnd, NULL , 1 ) ;  
             break ;
        case WM_RBUTTONUP :
            if ( grid_created && !allow_edition && !autopaintcells ) {
                if ( !sometextodo ) { curcmd_loop ( VK_RETURN ) ; inva ; }
                just_out_of_duwc = 0 ; 
                break ; }
            rbuttisdn = just_out_of_duwc = 0 ; 
            lasmousecoordsx = lasmousecoordsy = 65535 ; 
            if ( doautolines ) break ; 
            if ( selected_maplin < 0 ) break ;
            add_point_to_mapline ( hwnd ) ;
            InvalidateRect ( hwnd, NULL , 1 ) ;  
            break ; 
        case WM_LBUTTONDBLCLK :
           rbuttisdn = just_out_of_duwc = 0 ; 
           lasmousecoordsx = lasmousecoordsy = 65535 ; 
           if ( !grid_created ) {
               if ( nummaplins && selected_maplin >= 0 )
                   set_autoline_mode ( hwnd ) ; 
               selpoint_only = 0 ; 
               break ; }
           last_clicked_cell = -1 ;
           response = clickatcell ( hwnd ) ; 
           if ( response < 0 ) {
                 response = clickatcolor ( hwnd ) ;
                 if ( response >= 0 ) setcolorcode ( response ) ;
                 break ; }
           if ( !allow_edition ) break ;
           setcellon ( response , 1 ) ;  
           break ;         
        case WM_RBUTTONDBLCLK :
             rbuttisdn = just_out_of_duwc = 0 ; 
             lasmousecoordsx = lasmousecoordsy = 65535 ; 
             last_clicked_cell = -1 ; 
             if ( !allow_edition ) break ;
             response = clickatcell ( hwnd ) ; 
             if ( response < 0 ) break ;
             setcelloff ( response , 1 ) ; 
             break ;         
        case WM_LBUTTONDOWN :
             rbuttisdn = 0 ; 
             lasmousecoordsx = lasmousecoordsy = 65535 ; 
             doautolines = 0 ; 
             if ( sometextodo ) sometextodo = 2 ; 
             last_clicked_cell = -1 ; 
             if ( !allow_edition ) {
                 last_clicked_cell = clickatcell ( hwnd ) ;
                 win_refresh () ; 
                 break ; }
             last_clicked_cell = response = clickatcell ( hwnd ) ; 
             if ( response < 0 ) break ;
             setcellon ( response , 0 ) ; 
             break ; 
        case WM_RBUTTONDOWN :
             doautolines = rbuttisdn = 0 ;
             lasmousecoordsx = lasmousecoordsy = 65535 ; 
             if ( !grid_created && selected_maplin >= 0 ) {
                  rbuttisdn = 1 ;
                  inva ;
                  break ; }
             last_clicked_cell = -1 ; 
             if ( !allow_edition ) break ;
             response = clickatcell ( hwnd ) ; 
             if ( response < 0 ) break ;
             setcelloff ( response , 0 ) ; 
             break ; 
        case WM_CREATE :
                hBranchpen = CreatePen(PS_SOLID, 2 , RGB(0,0,0));
                hYellowPen = CreatePen(PS_SOLID, 3 , RGB(255,255,0));
                hWhitePen = CreatePen(PS_SOLID, 3 , RGB(255,255,255));
                hBlackPen = CreatePen(PS_SOLID, 3 , RGB(0,0,0));
                gray_menus () ; 
                break;
        case WM_PAINT :
                gray_menus () ;
                hdc = BeginPaint(hwnd, &paintstruct);
                SelectFont ( hdc , hfont ) ; 
                GetTextMetrics(hdc,&ourtm);
                text_height = (int )ourtm.tmHeight + ourtm.tmExternalLeading ;
                text_width = (int ) ourtm.tmAveCharWidth ;
                SelectObject(hdc,hBranchpen);
                if ( sometextodo ) show_text ( hdc ) ; 
                else 
                    if ( grid_created ) showmap ( hdc ) ;
                    else show_basic_grid ( hdc ) ; 
                sinfo.cbSize = sizeof ( SCROLLINFO ) ;
                sinfo.fMask = SIF_POS ;
                sinfo.nMin = 0 ;
                sinfo.nMax = 100 ; 
                j = give_scroll_pos ( ) ;
                if ( j > 100 ) j = 100 ; 
                sinfo.nPos = j ;  
                SetScrollInfo ( hwnd , SB_VERT , &sinfo , TRUE ) ;
                if ( grid_created ) 
                    if ( atcoordx < ( maxlinwidth * cellwid ) ) 
                        sinfo.nPos = ( 100 * atcoordx ) / ( maxlinwidth * cellwid ) ;
                    else sinfo.nPos = 100 ;
                else {
                    i = ( cellwid * cols * ( grid_effect / 100 ) ) ; 
                    if ( i && ( atcoordx * 100 ) / i < 100 )     
                        sinfo.nPos = ( atcoordx * 100 ) / i ; 
                    else sinfo.nPos = 100 ; }
                SetScrollInfo ( hwnd , SB_HORZ , &sinfo , TRUE ) ; 
                UpdateStatus(hwnd);
                EndPaint(hwnd, &paintstruct);
                break;
         case WM_DESTROY :
                        save_color_codes () ; 
                        PostQuitMessage(0);
                        break;
         case WM_KEYDOWN :
                    last_clicked_cell = -1 ; 
                    i = a = wParam ;
                    sometextodo = 0 ;
                    iscontrol = ( GetAsyncKeyState ( VK_CONTROL ) < 0 ) ;
                    if ( iscontrol ) {
                        if ( i == VK_DELETE ) i = ALTDEL ;
                        else if ( i == '=' ) i = ALTEQUAL ;
                        else if ( i == '1' ) i = ALT1 ; 
                        else i = toupper ( a ) ; }
                    else i = tolower ( a ) ;
                    if ( i == 'z' ) i = '=' ; 
                    if ( i == 'm' || i == 'c' ||
                         ( !grid_created && ( i == 'x' || i == 'y' ) ) ) {
                        iscapital = ( GetAsyncKeyState ( VK_SHIFT ) < 0 ) ;
                        if ( iscapital ) {
                            if ( i == 'm' ) i = VK_F12 ;
                            if ( i == 'c' ) i = VK_F11 ; }}
                    if ( i == a && i == VK_SUBTRACT ) i = '-' ;
                    if ( i == a && i == VK_DIVIDE ) i = '/' ; 
                    if ( !grid_created ) {
                         if ( nummaplins &&
                             ( i == VK_TAB || i == VK_BACK || i == VK_ADD || i == '-' ||
                               i == VK_END || i == VK_HOME )
                              && selected_maplin >= 0 ) {
                              enlarge_point_selection ( i ) ; inva ; break ; }
                         if ( i == VK_SPACE && selected_maplin >= 0 &&
                              selmappoint == selmappointmax &&
                              selmappoint < maplin[selected_maplin].numpoints - 1 ) {
                              selpoint_only = 1 - selpoint_only ;
                              inva ;
                              break ; }
                         if ( doautolines ) {
                             if ( i == VK_RETURN ) { add_autoline () ; inva ; break ; }
                             if ( i == VK_ESCAPE ) { doautolines = rbuttisdn = 0 ; inva ; break ; }}
                             if ( i == VK_NEXT || i == VK_PRIOR ) {
                                if ( i == VK_NEXT ) grid_effect += 15 ;
                                else { grid_effect -= 15 ; if ( grid_effect < 1 ) grid_effect = 1 ; }
                                i = VK_SHIFT ;
                                inva ;
                                break ; }
                        if ( !iscontrol && ( tolower ( i ) == 'x' || tolower ( i )  == 'y' ) ) { 
                            change_basic_grid ( i , 0 , iscapital ) ;
                            inva ;
                            break ; }}
                  switch ( i ){
                   case VK_HOME:
                         sinfo.nMin = 0 ;
                         sinfo.nMax = 100 ;
                         atcoordy = atcoordx = 0 ;
                         inva ;
                         break ; 
                   case VK_DELETE :
                     if ( grid_created || !nummaplins ) break ;
                     if ( selected_maplin < 0 ) break ; 
                     delete_maplin_point ( hwnd ) ;
                     InvalidateRect ( hwnd , NULL , 1 ) ;
                     break ; 
                   case VK_SHIFT : case VK_CONTROL : break ;
                   case VK_ADD : case '-' :
                     if ( i == '-' ) grid_effect -- ;
                     else grid_effect ++ ;
                     if ( !grid_effect ) grid_effect = 1 ; 
                     inva ; 
                     break ; 
                    case VK_F12 :
                        save_metafile ( ) ;
                        break ; 
                    case VK_F1 :
                        if ( a != i ) {
                             chkiscom ( i ) ; 
                             curcmd_loop ( i ) ;
                             break ; }
                        DeleteObject(hBranchpen) ;
                        bthick -= 1 ;
                        if ( !bthick ) bthick = 1 ; 
                        hBranchpen = CreatePen(PS_SOLID, bthick, RGB(0,0,0));
                        InvalidateRect ( hwnd, NULL , 1 ) ;  
                        break;                        
                    case VK_F3:
                        DeleteObject (hYellowPen);
                        DeleteObject (hWhitePen);
                        DeleteObject(hBlackPen);
                        PointWidth -- ;
                        if ( PointWidth < 1 ) PointWidth = 1 ; 
                        hYellowPen = CreatePen(PS_SOLID, PointWidth , RGB(255,255,0));
                        hWhitePen = CreatePen(PS_SOLID, PointWidth , RGB(255,255,255));
                        hBlackPen = CreatePen(PS_SOLID, PointWidth , RGB(0,0,0));
                        InvalidateRect ( hwnd, NULL , 1 ) ; 
                        break ; 
                    case VK_F4:
                        DeleteObject ( hYellowPen);
                        DeleteObject (hWhitePen);
                        DeleteObject(hBlackPen);
                        PointWidth ++ ;
                        hYellowPen = CreatePen(PS_SOLID, PointWidth , RGB(255,255,0));
                        hWhitePen = CreatePen(PS_SOLID, PointWidth , RGB(255,255,255));
                        hBlackPen = CreatePen(PS_SOLID, PointWidth , RGB(0,0,0));
                        InvalidateRect ( hwnd, NULL , 1 ) ; 
                        break ; 
                    case VK_F2 :
                        DeleteObject(hBranchpen);
                        bthick += 1 ;
                        hBranchpen = CreatePen(PS_SOLID, bthick, RGB(0,0,0));
                        InvalidateRect ( hwnd, NULL , 1 ) ; 
                        break;                        
                    case VK_UP :
                        if ( !grid_created ) {
                              if ( nummaplins && selected_maplin >= 0 && doautolines ) {
                                   move_autoline_tgt ( i ) ; inva ; break ; }
                              if ( nummaplins && selected_maplin >= 0 && selpoint_only ) {           
                                 move_selected_point ( i ) ;
                                 InvalidateRect ( hwnd , NULL , 1 ) ;
                                 break ; }
                            GLOCKERR ; 
                            change_basic_grid ( i , iscontrol , iscapital ) ; inva ; break ; }
                            if ( iscontrol ) {
                                if ( curcmd_loop != cmd_loop ) break ; 
                                change_basic_grid ( i , iscontrol, 0 ) ;
                                redo_matrix () ;
                                break ; }
                        -- cellhei ;
                        if ( !cellhei ) cellhei = 1 ; 
                        InvalidateRect(hwnd,NULL,1);
                        break;
                    case VK_DOWN :
                        if ( !grid_created ) {
                             if ( nummaplins && selected_maplin >= 0 && doautolines ) {
                                   move_autoline_tgt ( i ) ; inva ; break ; }
                              if ( nummaplins && selected_maplin >= 0 && selpoint_only ) {           
                                 move_selected_point ( i ) ;
                                 InvalidateRect ( hwnd , NULL , 1 ) ;
                                 break ; }
                            GLOCKERR ; 
                            change_basic_grid ( i , iscontrol , iscapital ) ; inva ; break ; }
                            if ( iscontrol ) {
                                if ( curcmd_loop != cmd_loop ) break ; 
                                change_basic_grid ( i , iscontrol, 0 ) ;
                                redo_matrix () ;
                                break ; }
                        ++ cellhei ; 
                        InvalidateRect(hwnd,NULL,1);
                        break;
                    case VK_LEFT :
                        if ( !grid_created ) {
                            if ( nummaplins && selected_maplin >= 0 && doautolines ) {
                                   move_autoline_tgt ( i ) ; inva ; break ; }
                            if ( nummaplins && selected_maplin >= 0 && selpoint_only ) {           
                                 move_selected_point ( i ) ;
                                 InvalidateRect ( hwnd , NULL , 1 ) ;
                                 break ; }
                            GLOCKERR ; 
                            change_basic_grid ( i , iscontrol , iscapital ) ; inva ; break ; }
                            if ( iscontrol ) {
                                if ( curcmd_loop != cmd_loop ) break ; 
                                change_basic_grid ( i , iscontrol, 0 ) ;
                                redo_matrix () ;
                                break ; }
                        -- cellwid ;
                        if ( !cellwid ) cellwid = 1 ; 
                        InvalidateRect(hwnd,NULL,1); 
                        break;
                    case VK_RIGHT :
                        if ( !grid_created ) {
                            if ( nummaplins && selected_maplin >= 0 && doautolines ) {
                                   move_autoline_tgt ( i ) ; inva ; break ; }
                            if ( nummaplins && selected_maplin >= 0 && selpoint_only ) {           
                                 move_selected_point ( i ) ;
                                 InvalidateRect ( hwnd , NULL , 1 ) ;
                                 break ; }
                            GLOCKERR ; 
                            change_basic_grid ( i , iscontrol , iscapital ) ; inva ; break ; }
                            if ( iscontrol ) {
                                if ( curcmd_loop != cmd_loop ) break ; 
                                change_basic_grid ( i , iscontrol, 0 ) ;
                                redo_matrix () ;
                                break ; }
                        ++ cellwid ; 
                        InvalidateRect(hwnd,NULL,1); 
                        break;
                    default :
                        chkiscom ( i ) ;
                        curcmd_loop ( i ) ;
                        inva ; 
                        break ; }

                    just_out_of_duwc = 0 ; 

                    break;

        case WM_COMMAND :
            last_clicked_cell = -1 ; 
            sometextodo = just_out_of_duwc = 0 ;
            i = LOWORD ( wParam ) ;
            switch( i ){
                case IDM_COPYRIGHT:
                    show_copyright_notice () ;
                    break ; 
               case IDM_SETEDGEUSAGE:
                   if ( curcmd_loop != cmd_loop ) curcmd_loop ( VK_ESCAPE ) ;
                   chkiscom ('p' ) ;
                   cmd_loop ( 'p' ) ;
                   gray_menus () ;
                   inva ;
                   break ; 
               case IDM_WEIGHTSPECIES:
                       if ( !weight_species ) {
                          if ( curcmd_loop != cmd_loop ) curcmd_loop ( VK_ESCAPE ) ;
                          chkiscom ( 'w' ) ;
                          cmd_loop ( 'w' ) ; }
                       else weight_species = 0 ;
                       gray_menus () ; 
                       inva ;
                       break ; 
               case IDM_CTRLMOUSEWHEELUP:
                      -- cellwid ; -- cellhei ;
                      if ( cellwid < 2 ) cellwid = 2 ;
                      if ( cellhei < 2 ) cellhei = 2 ;
                      inva ;
                      break ; 
               case IDM_CTRLMOUSEWHEELDN:
                      ++ cellwid ; ++ cellhei ;
                      inva ;
                      break ; 
               case IDM_WRITEVERYTHING:
                      effect_writedatainfo ( 0 ) ;
                      effect_writesetsinfo ( 0 ) ;
                      if ( curcmd_loop == show_consensus ) effect_writeconsinfo ( 0 ) ;
                      effect_writesppinfo ( 0 ) ;
                      inva ;
                      break ; 
               case IDM_SETFROMSPECIES:
                      curcmd_loop ( 'S' ) ;
                      inva ;
                      break ; 
               case IDM_WRITEDATAINFO:
                        effect_writedatainfo ( 1 ) ;
                        inva ;
                        break ;
               case IDM_REPORTOVERLAPS:
                      if ( curcmd_loop == show_consensus ) speak_all_overlaps ( 1 ) ;
                      else speak_all_overlaps ( 0 ) ;
                      inva ; 
                      break ; 
               case IDM_WRITECONSINFO:
                       effect_writeconsinfo ( 1 ) ;
                       inva ;
                       break ; 
               case IDM_WRITESETSINFO:
                      effect_writesetsinfo ( 1 ) ;
                      inva ;
                      break ;
               case IDM_MAKENOQUERIES :
                    query = 1 - query ;
                    inva ;
                    break ; 
               case IDM_WRITESPPINFO:
                      effect_writesppinfo ( 1 ) ;
                      inva ; 
                      break ; 
               case IDM_PILEUPMARKS:
                     if ( curcmd_loop != cmd_loop ) curcmd_loop ( VK_ESCAPE ) ; 
                     pileupmarks () ;
                     inva ;
                     break ; 
               case IDM_SHOWSUPERSET:
                       chkiscom ( '9' ) ;
                       cmd_loop ( '9' ) ;
                       inva ;
                       break ;
               case IDM_SAVEMARKEDAREAS:
                         save_marked_areas_to_log () ;
                         inva ;
                         break ; 
                case IDM_READLONGLAT:
                       dolatlong = 1 - dolatlong ;
                       inva ;
                      break ;
               case IDM_USECOMMASEPARATS:
                      nocommas = 1 - nocommas ;
                      inva ;
                      break ; 
               case IDM_GOTOPREVSET:
                        curcmd_loop ( VK_BACK ) ;
                        inva ;
                        break ;
               case IDM_GOTONEXTSET:
                        curcmd_loop ( VK_RETURN ) ;
                        inva ;
                        break ;
               case IDM_INREFWITHIN:
                      if ( curcmd_loop == show_duwc ) curcmd_loop ( VK_ESCAPE ) ; 
                      else
                         if ( curcmd_loop == show_consensus ) show_consensus ( 'W' ) ; 
                         else cmd_loop ( 'W' ) ;
                      inva ;
                      break ;
               case IDM_INREFCONTAINING:
                      if ( curcmd_loop == show_duwc ) curcmd_loop ( VK_ESCAPE ) ; 
                      else
                         if ( curcmd_loop == show_consensus ) show_consensus ( 'U' ) ; 
                         else cmd_loop ( 'U' ) ;
                      inva ;
                      break ;
               case IDM_INREFDISJUNCT:
                      if ( curcmd_loop == show_duwc ) curcmd_loop ( VK_ESCAPE ) ; 
                      else
                         if ( curcmd_loop == show_consensus ) show_consensus ( 'D' ) ; 
                         else cmd_loop ( 'D' ) ;
                      inva ;
                      break ;
               case IDM_INREFPARTIAL:
                      if ( curcmd_loop == show_duwc ) curcmd_loop ( VK_ESCAPE ) ; 
                      else
                         if ( curcmd_loop == show_consensus ) show_consensus ( 'C' ) ; 
                         else cmd_loop ( 'C' ) ;
                      inva ;
                      break ;
               case IDM_ERASEALLMARKS:
                       if ( sure ( "Sure you want to erase all marks" ) ) 
                            erase_all_marks () ;
                       if ( curcmd_loop == viewmarks ) curcmd_loop ( VK_ESCAPE ) ; 
                       inva ;
                       break ;  
               case IDM_CREATEANEWSET:
                       if ( curcmd_loop != cmd_loop ) curcmd_loop ( VK_ESCAPE ) ;
                       cmd_loop ( 'N' ) ;
                       inva ;
                       break ; 
               case IDM_DELETEVAR:
                       cmd_loop ( ALTDEL ) ;
                       inva ;
                       break ;
               case IDM_MARKSETSINCURCOMP:
                        if ( curcmd_loop == show_duwc || curcmd_loop == showspecies || curcmd_loop == showsuperset || curcmd_loop == show_consensus ) curcmd_loop ( 'M' ) ;
                        else curcmd_loop ( 'm' ) ;
                        gray_menus () ; 
                        inva ;
                        break ;
               case IDM_MARKAREAS :
                        curcmd_loop ( 'M' ) ;
                        inva ;
                        break ;
               case IDM_SHOWALLSPECIES:
                       if ( curcmd_loop == showspecies ) curcmd_loop ( VK_ESCAPE ) ;
                       else {        
                          if ( curcmd_loop != cmd_loop ) curcmd_loop ( VK_ESCAPE ) ;
                          cmd_loop ( 'S' ) ; }
                       inva ;
                       break ; 
               case IDM_SHOWSCORINGSPECIES:
                       if ( curcmd_loop == viewscore ) curcmd_loop ( VK_ESCAPE ) ; 
                       else cmd_loop ( 'v' ) ;
                       inva ;
                       break ; 
               case IDM_SETMINIMUMSPSCORE:
                       if ( curcmd_loop != cmd_loop ) curcmd_loop ( VK_ESCAPE ) ;
                       chkiscom ( 'b' ) ;
                       cmd_loop ( 'b' ) ;
                       break ;
               case IDM_INVERTMARKS:
                   a = 0 ; 
                    if ( curcmd_loop == viewmarks ) { viewmarks ( VK_ESCAPE ) ; a = 1 ; }
                    invertmarks () ;
                    if ( a ) cmd_loop ( 'V' ) ;   
                    inva ;
                    break ;
               case IDM_DELETEUNMARKS:
                      deleteunmarks () ; 
                      inva ;
                      break ; 
               case IDM_DELETEMARKS:
                     curcmd_loop ( VK_ESCAPE ) ;   
                     strcpy ( comstring , "/" ) ;
                     handle_marks ( ) ;
                     inva ;
                     break ;
               case IDM_VIEWMARKS:
                     if ( curcmd_loop == viewmarks ) curcmd_loop = viewscore ;
                     else {
                        if ( curcmd_loop != cmd_loop ) curcmd_loop ( VK_ESCAPE ) ;
                        cmd_loop ( 'V' ) ; }
                     inva ; 
                     gray_menus () ;
                     break ;
               case IDM_OPENANDREPLACE:
                       curcmd_loop ( VK_ESCAPE ) ;
                       chkiscom ( 'R' ) ;
                       if ( comstring[0] ) {
                           numrecs = 0 ; 
                           cmd_loop ( 'R' ) ;
                           set_recptr_to ( 0 ) ;
                           showcurset () ; }
                       break;
               case IDM_OPENPOINTSONLY:
                       curcmd_loop ( VK_ESCAPE ) ;
                       chkiscom ( '[' ) ;
                       if ( comstring[0] ) 
                           post_read_xyfile () ;
                       inva ; 
                       break ; 
               case IDM_CORELMETAFILE :
                    save_metafile ( ) ;
                    break ;
               case IDM_ALLTOMETAFILE:
                   save_all_to_metafile ( ) ;
                   break ; 
               case IDM_LOLLIPOP : 
                   export_area_coords ( hwnd ) ; 
                   break ; 
               case IDM_DIVALOLLIPOP : 
                   export_divagis_area_coords ( hwnd ) ; 
                   break ; 
               case IDM_BACKTOSTART: 
                   reset_original_diagram () ; 
                   inva ; 
                   break ; 
               case IDM_TRANSPOSEXY :
                   transpose_xy () ;
                   inva ;
                   break ;
               case IDM_EXPANDVAR :
                   expand_cell_definition = 1 - expand_cell_definition ;
                   inva ;
                   break ; 
               case IDM_FLIPONX :
                   fliponx () ;
                   inva ;
                   break ;
               case IDM_FLIPONY :
                   flipony () ;
                   inva ;
                   break ;
               case IDM_CSSCYCLES :
                       find_optimum_grid_position () ;
                       inva ;
                       break ; 
               case IDM_INCREASEFONTSIZE :
                       set_grid_size_and_pos () ;
                       inva ;
                       break ;

/*           used only for developing...  
             case IDM_SAMPLETEST:
                if ( data_is_sampled ) {
                    data_is_sampled = 0 ; 
                    undosample () ;
                    curcmd_loop = cmd_loop ; } 
                else { 
                   chkiscom ( '8' ) ;
                   i = comstring[ 0 ] + 1 - '1' ;
                   if ( i >= 1 && i <= 3 ) { 
                       data_is_sampled = 1 ; 
                       test_the_sample ( i ) ; }}
                inva ;
                break ;
***/

case IDM_SAMPLEALL:
case IDM_SAMPLESPP:
case IDM_SAMPLEAREA:
case IDM_SAMPLEUNDO:
      i = LOWORD ( wParam ) ;
      the_fuckin_sample ( ( i - IDM_SAMPLEALL + 1 ) , 0 ) ;
      inva ;
      break ; 
                       
               case IDM_NEWMATRIX :
                       create_matrix_from_points ( 1 ) ;
                       inva ;
                       break ;
               case IDM_SWITCHMATRIX:
                       set_radius_size () ;
                       break ;         
               case IDM_TAXSTATS :
                      spingrid_selfun () ;
                      inva ; 
                      break ; 

case IDM_JUDGESPECIESTXT:
      find_sets_for_given_species ( 1 ) ;
      inva ;
      break ; 
case IDM_JUDGESPECIESMRK:
      if ( without_splists () ) break ; 
      if ( curcmd_loop == showspecies ) showspecies ( 'M' ) ;
      else find_sets_for_given_species ( 0 ) ;
      inva ;
      break ; 

case IDM_LIST_OF_SCORING_SPP :
        save_list_of_scoring_spp_in_marked_sets () ;
        inva ;
        break ;
case IDM_GETTAXA_TO_WIPE:
      get_list_of_taxa_to_wipe_from_file () ;
      inva ;
      break ;

               case IDM_MARKIDTAXA :
                      taxon_selfun () ;
                      break ; 
               case IDM_SHOWNONE :      // "Do not auto-edit"
                      autopaintcells = 0 ;
                      gray_menus () ; 
                      break ; 
               case IDM_SHOWADD :       // "Make cells on/off"
                      //report_score_difference = 0 ;
                      autopaintcells = 1 ;
                      gray_menus () ; 
                      break ; 
               case IDM_SHOWACT :     // "Make cells defined/undefined"
                      report_score_difference = 0 ;
                      query = 0 ; 
                      autopaintcells = 2 ;
                      gray_menus () ; 
                      break ; 
               case IDM_SORTTAXA:      // "Make cells assumed"
                      //report_score_difference = 0 ;
                      autopaintcells = 3 ;
                      gray_menus () ; 
                      break ; 
               case IDM_DESCRIBE :
                     report_score_difference = 1 - report_score_difference ;
                     if ( report_score_difference ) {
                        trackmouse = 1 ; 
                        autopaintcells = 0 ; }
                     gray_menus () ;
                     break ;
              case IDM_HIDEMAP :
                     hide_the_map = 1 - hide_the_map ;
                     inva ; 
                     break ; 
              case IDM_ONLY_POINTS :
                   only_show_points = 1 - only_show_points ;
                   gray_menus () ; inva ;
                   break ; 
               case IDM_RESOLUTION :
                 show_individual_dots = 1 - show_individual_dots ;
                 gray_menus () ;
                 inva ; 
                 break ; 
               case IDM_SELECTMOUSE :
                 trackmouse = 1 - trackmouse ;
                 if ( !trackmouse ) report_score_difference = 0 ; 
                 gray_menus () ; 
                 break ; 
               case IDM_DFTFACTOR :
                   dlg_fiaodn () ;
                   inva ;
                   break ; 
               case IDM_VARCOLORS :
                  reset_cell_colors () ;
                  inva ;
                  break ; 
               case IDM_HELP :
                    dohlp ( 1 ) ; 
                    break ;
               case IDM_ABOUT :
                  MessageBox ( hwnd , 
                    "VNDM (vers. 3.1)\n"
                    "Copyright (c) Pablo A. Goloboff (2001-2016)\n"
                    "\n"
                    "Thanks to GBIF, CONICET, NSF, NASA, and FAPESP\n"
                    "for support...\n"
                    "\n"
                    "If you publish results using NDM/VNDM,\n"
                    "please cite programs as such:\n\n"
                    "   Goloboff, P. 2004.  NDM/VNDM, Programs\n"
                    "      for identification of areas of endemism.\n"
                    "      Program and documentation, available at\n"
                    "      www.lillo.org.ar/phylogeny/endemism.\n\n"
                    "NDM/VNDM implement the methods published in:\n\n"
                    "   Szumik, C., F. Cuezzo, P. Goloboff, and\n"
                    "      A. Chalup. 2002. An optimality criterion\n"
                    "      to determine areas of endemism. Syst.\n"
                    "      Biol. 51:806-816.\n\n"
                    "   Szumik, C., and P. Goloboff. 2004. Areas \n"
                    "      of Endemism: An Improved Optimality\n"
                    "      Criterion.  Syst. Biol. 53:968-977." , "About..." , MB_OK ) ;
                    break ;
             case IDM_SEARCH :
                   dondmsearch ( 0 ) ;
                   break ;
             case IDM_OUTDESCRIBE : 
                   dondmsearch ( 1 ) ;
                   break ;
             case IDM_TRADSEARCH :
                   doparsearch ( 0 ) ;
                   break ; 
             case IDM_SECTSEARCH :
                   doparsearch ( 1 ) ;
                   break ; 
             case IDM_OPENLINEDEFS:
                        chkiscom ( '?' ) ;
                        cmd_loop ( '?' ) ;
                        break ; 
             case IDM_OPEN :
                        ridofdupes = 0 ; 
                        curcmd_loop ( VK_ESCAPE ) ; 
                        chkiscom ( 'R' ) ;
                        cmd_loop ( 'R' ) ; 
                        break;
             case IDM_OPEN_NODUPES:
                        ridofdupes = 1 ; 
                        curcmd_loop ( VK_ESCAPE ) ; 
                        chkiscom ( 'R' ) ;
                        cmd_loop ( 'R' ) ;
                        ridofdupes = 0 ; 
                        break ;  
             case IDM_CLOSEOUTPUT :
                    close_outputfile () ;
                    break ;
             case IDM_OPENOUTPUT :
                        a = 0 ; 
                        if ( curcmd_loop == show_consensus ) {
                            a = 1 ;
                            curcmd_loop = cmd_loop ; }
                        else curcmd_loop ( VK_ESCAPE ) ; 
                        chkiscom ( 'o' ) ;
                        cmd_loop ( 'o' ) ;
                        if ( a ) { curcmd_loop = show_consensus ; curcmd_loop ( 1 ) ; }
                        inva ; 
                        break;
             case IDM_CHARDATAEDIT :
                        allow_edition = 1 - allow_edition ;
                        if ( !allow_edition ) autopaintcells = 0 ; 
                        gray_menus () ;
                        inva ;
                        break ;
             case IDM_BEEP :
                         query = 1 - query ;
                         gray_menus () ;
                         inva ;
                         break ;
             case IDM_NEWMAPLINE :
                      i = MessageBox ( hwnd , 
                      "Press and release left mouse button to"
                      "\ncreate starting point of new map line" , "New map line..." , MB_OKCANCEL ) ; 
                      if ( i == IDCANCEL ) break ;
                      if ( !last_point_extend ) 
                          MessageBox ( hwnd , "Mode of edition of last point\nchanged to \"extend\"" , "NOTE..." , MB_OK ) ; 
                      last_point_extend = 1 ; 
                      ready_to_start_line = 1 ;
                      gray_menus () ; 
                      break ; 
             case IDM_LASTPOINT :
                      DialogBox (hInst, "LastPointModeDB", hwnd, (DLGPROC) LastPointModeFunc ) ;
                      inva ;
                      break ;
             case IDM_LOCKGRID :
                       if ( grid_created ) break ; 
                       grid_is_locked = 1 - grid_is_locked ;
                       gray_menus () ;
                       break ;
             case IDM_CONSENSUS :
                       if ( without_splists () ) break ; 
                       consensus_is_sample = 0 ; 
                       if ( curcmd_loop == show_consensus ) show_consensus ( VK_ESCAPE ) ; 
                       else {
                           if ( curcmd_loop != cmd_loop ) curcmd_loop ( VK_ESCAPE ) ; 
                           cmd_loop ( 1 ) ; }
                       inva ; 
                       gray_menus () ;
                       break ;
             case IDM_CONSENSUS_BOOTAREA :
             case IDM_CONSENSUS_BOOTSPP:
             case IDM_CONSENSUS_UNIQUE: 
                       if ( without_splists () ) break ; 
                       consensus_is_sample = LOWORD ( wParam ) - IDM_CONSENSUS_BOOTAREA + 1 ;
                       if ( curcmd_loop == show_consensus ) show_consensus ( VK_ESCAPE ) ; 
                       else {
                           if ( curcmd_loop != cmd_loop ) curcmd_loop ( VK_ESCAPE ) ; 
                           cmd_loop ( 1 ) ; }
                       inva ; 
                       gray_menus () ;
                       break ;
             case IDM_LISTTAX :
                       list_endemic_taxa () ;
                       break ; 
             case IDM_BLACK :
                        black_n_white = 1 - black_n_white ;
                        reset_fillcolors ( 1 ) ;
                        gray_menus () ; 
                        inva ; 
                        break ; 
             case IDM_MATRIXSAVE :
                        if ( !grid_created ) {
                            save_xydata () ; break ; }
                        strcpy ( comstring , "d" ) ;
                        cmd_loop ( 's' ) ;
                        inva ; 
                        break ;
             case IDM_COORDSAVEALL :
                   save_only_coords ( 0 ) ;
                   break ; 
             case IDM_FINDHIGHER :
                   find_and_save_higher_groups ( ) ;
                   break ; 
             case IDM_COORDSAVETYPOS :
                   save_only_coords ( 1 ) ;
                   break ; 
             case IDM_COORDSAVEACTIVE :
                   save_only_coords ( 2 ) ;
                   break ; 
             case IDM_SHRINK :
                        a = DialogBox (hInst, "MATRIXSHRINKDB", hwnd, (DLGPROC) MatrixShrinkFunc ) ;
                        inva ; 
                        break ;
             case IDM_PARTIALDATA:
                   save_data_within_curset () ;
                   inva ;
                   break ; 
             case IDM_SAVEDATA :
                        chkiscom ( 'l' ) ;
                        logsetsonly = 0 ;
                        cmd_loop ( 'l' ) ;
                        break ;
             case IDM_SAVEASS : 
                        chkiscom ( 'L' ) ;
                        logsetsonly = 1 ;
                        cmd_loop ( 'L' ) ;
                        break ;
             case IDM_EXIT :
                        save_color_codes () ; 
                        PostQuitMessage(0);
                        break;
             default :
                        noisy() ;
                        MessageBox ( hwnd, "Sooorry, option is not implemented yet", "Ooops. . . ", MB_OK ) ; 
                        return DefWindowProc(hwnd, message, wParam, lParam);
                }
             break;

        case WM_VSCROLL :
                switch (LOWORD(wParam)) {
                    case SB_THUMBPOSITION :
                        sinfo.cbSize = sizeof ( SCROLLINFO ) ;
                        sinfo.fMask = SIF_POS | SIF_TRACKPOS ;
                        sinfo.nMin = 0 ;
                        sinfo.nMax = 100 ;
                        GetScrollInfo ( hwnd , SB_VERT , &sinfo ) ;
                        copygil ( - WINBUFSIZ ) ;
                        j = give_total_lines() ;
                        sinfo.nTrackPos = 100 - sinfo.nTrackPos ; 
                        i = ( sinfo.nTrackPos * j ) / 100 ;
                        copygil ( i ) ;  
                        InvalidateRect(hwnd,NULL,1);
                        break;
                    case SB_THUMBTRACK :
                        sinfo.cbSize = sizeof ( SCROLLINFO ) ;
                        sinfo.fMask = SIF_POS | SIF_TRACKPOS ;
                        sinfo.nMin = 0 ;
                        sinfo.nMax = 100 ;
                        GetScrollInfo ( hwnd , SB_VERT , &sinfo ) ;
                        copygil ( - WINBUFSIZ ) ;
                        j = give_total_lines() ;
                        sinfo.nTrackPos = 100 - sinfo.nTrackPos ; 
                        i = ( sinfo.nTrackPos * j ) / 100 ;
                        copygil ( i ) ;  
                        InvalidateRect(hwnd,NULL,1);
                        break;
                    case SB_PAGEDOWN :
                        copygil( -1 ) ;
                        InvalidateRect(hwnd,NULL,1);
                        break;
                    case SB_PAGEUP :
                        copygil ( 1 ) ;
                        InvalidateRect(hwnd,NULL,1);
                        break;
                    case SB_LINEDOWN :
                        copygil ( -1 ) ; 
                        InvalidateRect(hwnd,NULL,1);
                        break;
                    case SB_LINEUP :
                        copygil ( 1 ) ; 
                        InvalidateRect(hwnd,NULL,1);
                        break;
                    default :
                         break;
                }
                break;
        case WM_HSCROLL :
                switch (LOWORD(wParam)) {
                    case SB_THUMBPOSITION :
                        sinfo.cbSize = sizeof ( SCROLLINFO ) ;
                        sinfo.fMask = SIF_POS | SIF_TRACKPOS ;
                        sinfo.nMin = 0 ;
                        sinfo.nMax = 100 ;
                        GetScrollInfo ( hwnd , SB_HORZ , &sinfo ) ;
                        if ( !grid_created ) 
                            atcoordx = ( sinfo.nTrackPos *
                                      ( grid_effect / 100 ) * cellwid * cols ) / 100 ;    
                        else 
                            atcoordx = ( sinfo.nTrackPos * maxlinwidth ) / 100 ;    
                        InvalidateRect(hwnd,NULL,1);
                        break;
                    case SB_THUMBTRACK :
                        sinfo.cbSize = sizeof ( SCROLLINFO ) ;
                        sinfo.fMask = SIF_POS | SIF_TRACKPOS ;
                        sinfo.nMin = 0 ;
                        sinfo.nMax = 100 ;
                        GetScrollInfo ( hwnd , SB_HORZ , &sinfo ) ;
                        if ( !grid_created ) 
                            atcoordx = ( sinfo.nTrackPos *
                                      ( grid_effect / 100 ) * cellwid * cols ) / 100 ;
                        else 
                            atcoordx = ( sinfo.nTrackPos * maxlinwidth ) / 100 ;    
                        InvalidateRect(hwnd,NULL,1);
                        break;
                    case SB_LINELEFT :
                    case SB_PAGELEFT :
                        if ( screen_shift > maxlinwidth ) screen_shift = maxlinwidth ;  
                        if ( !grid_created ) 
                             atcoordx -= ( cellwid * grid_effect ) / 100 ;
                        else atcoordx -= cellwid ; 
                        if ( atcoordx < 0 ) atcoordx = 0 ;  
                        InvalidateRect(hwnd,NULL,1);
                        break;
                    case SB_LINERIGHT :
                    case SB_PAGERIGHT :
                        if ( !grid_created ) {
                           atcoordx += ( cellwid * grid_effect ) / 100 ;
                           if ( atcoordx > ( cellwid * grid_effect * maxlinwidth ) / 100 )
                                atcoordx = ( cellwid * grid_effect * maxlinwidth ) / 100 ; }    
                        else {
                           atcoordx += cellwid ;
                           if ( atcoordx > ( cellwid * maxlinwidth ) )
                                atcoordx = ( cellwid * maxlinwidth ) ; }
                        InvalidateRect(hwnd,NULL,1);
                        break;
                    default :
                         break;
                }

                break;
            
        default : return DefWindowProc(hwnd, message, wParam, lParam);
    }
    return(0);
}

RECT CmdDim , RecDim , StatDim ;
POINT dlgpos ;
#define MAXCMDBUF ( 10 ) 
char cmdbuf[MAXCMDBUF][200] ;
int atcmdbuf = 0 ;
int cmdbufrd = 0 ; 

int win_refresh ( void )
{
    inva ;
} 

static short int * isshrinkable ; 

void MyLine ( HDC myhdc , int fromx, int fromy, int tox, int toy )
{
    MoveToEx ( myhdc , fromx , fromy , NULL ) ;
    LineTo ( myhdc , tox , toy ) ;
    return ;
} 
    
int ResetStatus(HWND xhwnd)
{
    int i;
    GetClientRect(xhwnd, &WinDim);
    for(i = 1 ;i <= NUMPARTS ; ++i)
        parts[i-1] = WinDim.right/NUMPARTS * i;
    parts[NUMPARTS-2] = WinDim.right - 10;
    SendMessage(hStatusWnd, SB_SETPARTS, (WPARAM) NUMPARTS, (LPARAM) parts);
    UpdateStatus(hwnd);   
    return(1);
}

/* ---------------------- UPDATESTATUS -------------------------------*/

extern int records_read ;
extern unsigned long int grandsumofpoints ; 

int UpdateStatus(HWND xhwnd)
{
    int i;
    strcpy(junkstr," ");
    for(i=0;i< NUMPARTS ;++i){
       SendMessage(hStatusWnd, SB_SETTEXT, (WPARAM) i, (LPARAM) junkstr);
    }

    // DATA 
    if ( grandsumofpoints )
      wsprintf ( junkstr , "%i cols x %i rows x %i spp (%i points)" , cols , rows , spp , grandsumofpoints ) ; 
    else 
      wsprintf ( junkstr , "%i cols x %i rows x %i spp" , cols , rows , spp ) ; 
    SendMessage(hStatusWnd, SB_SETTEXT, (WPARAM) 0, (LPARAM) junkstr );

    // NUMBER OF SETS
    wsprintf(junkstr,"%i sets in memory", numrecs ) ; 
    SendMessage(hStatusWnd, SB_SETTEXT, (WPARAM) 1, (LPARAM) junkstr );

    if ( sccol != NULL ) {
       wsprintf ( junkstr , "Cell size %i x %i" , cellwid , cellhei ) ; 
       SendMessage(hStatusWnd, SB_SETTEXT, (WPARAM) 2, (LPARAM) junkstr ) ;
       if ( last_clicked_cell < 0 ) 
          setjunkstrtocurfunc ( ) ; 
       else {
           sprintf ( junkstr , "Cell: %i-%i" , last_clicked_cell % cols , last_clicked_cell / cols ) ; 
           if ( report_score_difference &&
                curcmd_loop == cmd_loop ) calculate_score_onoff ( last_clicked_cell ) ; }
       SendMessage(hStatusWnd, SB_SETTEXT, (WPARAM) 3, (LPARAM) junkstr );}      
    else if ( spingrid != NULL && !grid_created ) {
             sprintf ( junkstr , "%i records, %i species" , records_read , num_spingrid ) ; 
             SendMessage(hStatusWnd, SB_SETTEXT, (WPARAM) 2, (LPARAM) junkstr );
             sprintf ( junkstr , "Cells: %.2fx%.2f (origin: %.2f - %.2f)" ,
                                    truecellwid , truecellhei , grid_startx , grid_starty ) ; 
             SendMessage(hStatusWnd, SB_SETTEXT, (WPARAM) 3, (LPARAM) junkstr ); }      
    return 0 ;
}

        
int win_display_state_names = -1 ;

#define SPINACCEL( x , y , z ) \
    { hWho = GetDlgItem ( hdwnd , ( x ) ) ; \
      SpinAccel ( hWho , ( y ) , ( z ) ) ; } 

void SpinAccel ( HWND hctrl , int frst , int secd )
{
    UDACCEL acel[3] ; 
    acel[0].nSec = 0 ; 
    acel[0].nInc = 1 ; 
    acel[1].nSec = 2 ; 
    acel[1].nInc = frst ;
    acel[2].nSec = 4 ; 
    acel[2].nInc = secd ;
    SendMessage( hctrl , UDM_SETACCEL, 3 , acel ) ; 
} 

void noisy ( void )
{
    MessageBeep(0xFFFFFFFF ) ; 
    return ;
}

HMENU pupu ; 
    
void blackit ( BOOL condit, UINT idis )
{
    if ( condit == FALSE && !storing_batch_menus )
        EnableMenuItem( pupu, idis, MF_GRAYED );
    else 
        EnableMenuItem( pupu, idis, MF_ENABLED );
} 

void markit ( BOOL condit, UINT idis )
{
    if ( condit == FALSE )
          CheckMenuItem( pupu , idis, MF_UNCHECKED );
    else CheckMenuItem( pupu , idis, MF_CHECKED );
}

extern int read_as_a_dat_file ;

void gray_menus ( void )
{   pupu = GetMenu ( hwnd ) ;
    markit ( allow_edition , IDM_CHARDATAEDIT ) ; 
    markit ( query , IDM_BEEP ) ;
    markit ( use_edge_props , IDM_SETEDGEUSAGE ) ; 
    markit ( hide_the_map , IDM_HIDEMAP ) ;
    if ( recptr != NULL ) 
         blackit ( ( recptr -> size > 0 ) && ( curcmd_loop == cmd_loop ) && grid_created , IDM_PARTIALDATA ) ; 
    blackit ( maplin != NULL , IDM_HIDEMAP ) ;
    blackit ( ( !faked_a_grid && num_spingrid ) , IDM_EXPANDVAR ) ;
    markit ( expand_cell_definition == 0 , IDM_EXPANDVAR ) ; 
    markit ( trackmouse , IDM_SELECTMOUSE ) ;
    markit ( ( !faked_a_grid && ( num_spingrid && show_individual_dots ) ) , IDM_RESOLUTION ) ; 
    markit ( ( num_spingrid && only_show_points ) , IDM_ONLY_POINTS ) ;
    markit ( weight_species , IDM_WEIGHTSPECIES ) ;
    markit ( ( query == 0 ) , IDM_MAKENOQUERIES ) ; 
    blackit ( data_is_xydata , IDM_WEIGHTSPECIES ) ;
    blackit ( ( spname != NULL && outspace != NULL ) , IDM_FINDHIGHER ) ; 
    blackit ( ( outspace != NULL && ( data_is_xydata || grid_created || faked_a_grid || num_spingrid ) ) , IDM_COORDSAVE ) ; 
    blackit ( ( !grid_created ) , IDM_ONLY_POINTS ) ; 
    blackit ( ( ( outspace != NULL && curcmd_loop == cmd_loop ) ) , IDM_MATRIXSAVE ) ; 
    blackit ( ( ( outspace != NULL && curcmd_loop == cmd_loop && grid_created ) ) , IDM_SHRINK ) ; 
    blackit ( ( curcmd_loop == cmd_loop && grid_created ) , IDM_SAVEDATA ) ; 
    blackit ( ( curcmd_loop == cmd_loop && grid_created ) , IDM_SAVEASS ) ;
    blackit ( ( ( curcmd_loop == cmd_loop || curcmd_loop == show_consensus )
                  && ( faked_a_grid || ( grid_created && data_is_xydata ) ) ) , IDM_LOLLIPOP ) ;
    markit ( autopaintcells == 0 , IDM_SHOWNONE ) ; 
    markit ( autopaintcells == 1 , IDM_SHOWADD ) ; 
    markit ( autopaintcells == 2 , IDM_SHOWACT ) ; 
    markit ( autopaintcells == 3 , IDM_SORTTAXA ) ;
    markit ( report_score_difference , IDM_DESCRIBE ) ;
    markit ( grid_is_locked && !grid_created , IDM_LOCKGRID ) ;
    markit ( curcmd_loop == show_consensus , IDM_CONSENSUS ) ;
    blackit ( curcmd_loop != show_consensus && didaboot , IDM_CONSENSUS_BOOTAREA ) ; 
    blackit ( curcmd_loop != show_consensus && didaboot , IDM_CONSENSUS_BOOTSPP ) ;
    blackit ( curcmd_loop != show_consensus && didaboot , IDM_CONSENSUS_UNIQUE ) ;
    blackit ( ( curcmd_loop == cmd_loop || curcmd_loop == show_consensus ) , IDM_ALLTOMETAFILE ) ;
    markit ( data_is_sampled , IDM_SAMPLETEST ) ; 

blackit ( ( grid_created && grid_startx < 10e99 ) , IDM_SUPRALOLLIPOP ) ; 

// blackit ( species_tree == NULL , IDM_MARKIDTAXA ) ; 

blackit ( outspace != NULL , IDM_CLOSEOUTPUT ) ;
blackit ( ( grid_created && curcmd_loop == cmd_loop ) , IDM_MARKAREAS ) ; 
blackit ( ( grid_created && curcmd_loop == cmd_loop ) , IDM_UNMARKAREAS ) ;
blackit ( grid_created , IDM_GOTOPREVSET ) ;
blackit ( grid_created , IDM_GOTONEXTSET ) ;
blackit ( ( grid_created && ( curcmd_loop == cmd_loop || curcmd_loop == show_consensus || ( curcmd_loop == show_duwc && cur_duwc_act == 'W' ) ) ) , IDM_INREFWITHIN ) ; 
blackit ( ( grid_created && ( curcmd_loop == cmd_loop || curcmd_loop == show_consensus || ( curcmd_loop == show_duwc && cur_duwc_act == 'U' ) ) ) , IDM_INREFCONTAINING ) ; 
blackit ( ( grid_created && ( curcmd_loop == cmd_loop || curcmd_loop == show_consensus || ( curcmd_loop == show_duwc && cur_duwc_act == 'D' ) ) ) , IDM_INREFDISJUNCT ) ; 
blackit ( ( grid_created && ( curcmd_loop == cmd_loop || curcmd_loop == show_consensus || ( curcmd_loop == show_duwc && cur_duwc_act == 'C' ) ) ) , IDM_INREFPARTIAL ) ;
blackit ( ( grid_created && curcmd_loop == cmd_loop ) , IDM_DELETEVAR ) ;
markit ( ( curcmd_loop == show_duwc && cur_duwc_act == 'W' )  , IDM_INREFWITHIN ) ;
markit ( ( curcmd_loop == show_duwc && cur_duwc_act == 'D' ) , IDM_INREFDISJUNCT ) ;
markit ( ( curcmd_loop == show_duwc && cur_duwc_act == 'C' ) , IDM_INREFPARTIAL ) ;
markit ( ( curcmd_loop == show_duwc && cur_duwc_act == 'U' ) , IDM_INREFCONTAINING ) ;
markit ( ( curcmd_loop == showspecies ) , IDM_SHOWALLSPECIES ) ;
markit ( ( curcmd_loop == viewmarks ) , IDM_VIEWMARKS ) ;
blackit ( grid_created , IDM_VIEWMARKS ) ;
blackit ( grid_created , IDM_ERASEALLMARKS ) ;
blackit ( grid_created , IDM_MENUACTIONS ) ;
blackit ( ( curcmd_loop == show_duwc || curcmd_loop == showspecies || curcmd_loop == show_consensus || curcmd_loop == showsuperset ) , IDM_MARKSETSINCURCOMP ) ;
blackit ( grid_created , IDM_CREATEANEWSET ) ;
blackit ( ( curcmd_loop == cmd_loop || curcmd_loop == viewscore || curcmd_loop == viewmarks ) , IDM_SHOWSCORINGSPECIES ) ;
markit ( ( curcmd_loop == viewscore ) , IDM_SHOWSCORINGSPECIES ) ;
markit ( nocommas==0 , IDM_USECOMMASEPARATS ) ;
markit ( dolatlong==0 , IDM_READLONGLAT ) ; 
blackit ( ( curcmd_loop == cmd_loop && grid_created ) , IDM_SAVEMARKEDAREAS ) ;
blackit ( ( curcmd_loop == cmd_loop && grid_created ) , IDM_SHOWSUPERSET ) ; 
markit ( ( curcmd_loop == showsuperset ) , IDM_SHOWSUPERSET ) ; 
blackit ( outspace != NULL , IDM_OPENWRITELIST ) ; 
blackit ( curcmd_loop == show_consensus , IDM_WRITECONSINFO ) ; 
blackit ( ( grid_created || data_is_xydata ) , IDM_WRITEDATAINFO ) ; 
blackit ( curcmd_loop == showspecies , IDM_SETFROMSPECIES ) ;
blackit ( ( read_as_a_dat_file &&
            grid_created && data_is_xydata != 1 && grid_startx < 10e199 && grid_starty < 10e199 ) ,
            IDM_OPENPOINTSONLY ) ; 

    blackit ( !grid_created , IDM_LOCKGRID ) ; 
    blackit ( outspace != NULL , IDM_LISTTAX ) ;
    blackit ( !faked_a_grid && num_spingrid && grid_created , IDM_RESOLUTION ) ;
    blackit ( numrecs && grid_created , IDM_CONSENSUS ) ; 
    blackit ( grid_created == 0 , IDM_COORDINATESYSTEM ) ; 
    blackit ( grid_created == 0 , IDM_NEWMAPLINE ) ;
    blackit ( grid_created == 0 , IDM_LASTPOINT ) ; 
    blackit ( grid_created , IDM_GETANALYZE ) ;
    blackit ( grid_created , IDM_OPEN ) ; 
    blackit ( ( data_is_xydata && spingrid != NULL ) , IDM_TAXSTATS ) ;
    blackit ( data_is_xydata , IDM_TRIMMATRIX ) ;
    blackit ( data_is_xydata , IDM_RESIZE ) ;
//    blackit ( ( data_is_xydata || num_spingrid == 0 ) , IDM_INCREASEFONTSIZE ) ;   // Note: this is now ALWAYS black...
    blackit ( grid_created == 0 , IDM_NEWMATRIX ) ;
    blackit ( !faked_a_grid && ( grid_created == 0 || num_spingrid > 0 ) , IDM_SWITCHMATRIX ) ;
    blackit ( curcmd_loop == cmd_loop && grid_created && data_is_xydata ,
               IDM_CSSCYCLES ) ; 
    blackit ( grid_created , IDM_CHARDATAEDIT ) ;
    blackit ( grid_created , IDM_UNLOCKED ) ; 
    blackit ( grid_created , IDM_SELECTMOUSE ) ; 
    blackit ( grid_created , IDM_DESCRIBE ) ;
    blackit ( grid_created , IDM_COLORS ) ; 
    blackit ( grid_created && !black_n_white , IDM_VARCOLORS ) ; 
    blackit ( grid_created , IDM_BLACK ) ;
    markit ( black_n_white , IDM_BLACK ) ; 
    DrawMenuBar ( hwnd ) ;
} 

void tree_win_reset ( void )
{
    tree_orgx = tree_orgy = 20 ;
    currtree = 0 ;
    treemode = 0 ;
    goto_treenode = -1 ; 
}     


void errmsg ( void * i , ... )
{
    void ** ip = &i ;
    void * ipp = * ip ;
    int a ; 
    for ( a = 0 ; a < 10 ; ++ a ) {
        if ( ip [ a ] == NULL ) break ; 
        if ( ip [ a ] == junkstr )
               errmsg ( "An error occured when calling ERRMSG.  Would you please notify Pablo?" , Null ) ; }
    ipp = * ip ; 
    sprintf ( junkstr , ip [ 0 ]  , ip [ 1 ] , ip [ 2 ] , ip [ 3 ] , ip [ 4 ] , ip [ 5 ] , ip [ 6 ] , ip [ 7 ] , ip [ 8 ] , ip [ 9 ] ) ;
    MessageBox ( hwnd , junkstr , "ERROR" , MB_OK ) ;  
    return ; 
}

int without_splists ( void )
{
   if ( !ignore_sp_lists ) return 0 ; 
   errmsg ( "Cannot execute this option if species not listed for each area" ) ;
   return 1 ; 
}

void dotnt ( void * i , ... )
{
    void ** ip = &i ;
    void * ipp = * ip ;
    int a ; 
    for ( a = 0 ; a < 10 ; ++ a )
        if ( ip [ a ] == junkstr )
               errmsg ( "An error occured when calling DOTNT().  Would you please notify Pablo?" , Null ) ; 
    ipp = * ip ; 
    sprintf ( junkstr , ip [ 0 ]  , ip [ 1 ] , ip [ 2 ] , ip [ 3 ] , ip [ 4 ] , ip [ 5 ] , ip [ 6 ] , ip [ 7 ] , ip [ 8 ] , ip [ 9 ] ) ;
    dotnt ( junkstr ) ; 
    return ; 
}

void set_screen_size ( int inited )
{
    int i ;
    RECT tmpdim ; 
    GetClientRect(hwnd, &WinDim);
    WinHeight = i = WinDim.bottom - WinDim.top ;
    if ( cmhwnd != NULL && !treemode ) {
        GetClientRect ( cmhwnd , &tmpdim ) ;
        i = tmpdim.bottom - tmpdim.top ; 
        WinHeight -= i ;
        i = WinHeight ; } 
    WinWidth = WinDim.right - WinDim.left ; 
    hdc = GetDC ( hwnd ) ; 
    SelectFont ( hdc , hfont ) ; 
    GetTextMetrics(hdc,&ourtm);
    text_height = (int )ourtm.tmHeight + ourtm.tmExternalLeading ;
    i = ( i / text_height ) - 1 ;
    if ( i < i ) i = 1 ; 
    if ( i != screen_size ) {
          screen_size = i ;
          if ( screen_size > MAXSCREEN_SIZE ) screen_size = MAXSCREEN_SIZE ; 
          copygil ( 0 ) ; } 
    i = WinDim.right - WinDim.left ; 
    text_width = (int ) ourtm.tmAveCharWidth ;
    screen_width = i / text_width + 1 ;
    if ( !inited ) bspan = text_height ;
    InvalidateRect( hwnd , NULL , 1 ) ;
    return ;
} 
    
void reset_screen_shift ( void )
{
    screen_shift = 0 ;
}

void eofscreen ( void )
{
    copygil ( -WINBUFSIZ ) ;
    copygil ( screen_size ) ; 
    reset_screen_shift () ; 
}

char screenmsg[1000] ; 

void spitit ( char * what )
{
    cls () ;
    sometextodo = 1 ;
    strcpy ( screenmsg , what ) ;
    win_refresh () ; 
    return ; 
}

void show_text ( HDC myhdc )
{
  char * cp = screenmsg , * at = screenmsg ;
  int was , atlin = 1 ;
  if ( * cp == '\n' ) {
      ++ at ; ++ atlin ; }
  while ( * cp != '\0' ) {
        ++ cp ; 
        if ( * cp == '\n' || * cp == '\0' ) {
            was = * cp ; 
            * cp = '\0' ;
            TextOut ( myhdc , 10 - atcoordx , ( 17 * atlin ) - atcoordy , at , strlen ( at ) ) ;
            atlin ++ ;
            if ( was == '\0' ) break ;
            * cp = '\n' ; 
            at = ++ cp ; }}
  return ;
}

void save_xydata ( void )
{
     int a , b ; 
     FILE * thef ;
     thef = outspace ; 
     fprintf ( thef , "spp %i" , spp ) ;
     fprintf ( thef , "\nxydata" ) ; 
     tmp_diagram_chg ( 0 ) ; 
     for ( a = 0 ; a < spp ; ++ a ) {
          if ( xymatrix[a].numrecs == 0 ) continue ; 
          fprintf ( thef , "\nsp %i" , a ) ;
          sprintf ( junkstr , "%i unnamed" , a ) ; 
          if ( spname != NULL && strcmp ( spname[a], junkstr ) )
               fprintf ( thef , " [ %s ]" , spname[a] ) ;
          fprintf ( thef , "\n" ) ;
          for ( b = 0 ; b < xymatrix[a].numrecs ; ++ b )
              fprintf ( thef , "%f %f " , xymatrix[a].x[b] , xymatrix[a].y[b] ) ; }    
     if ( nummaplins ) {
         fprintf ( thef , "\nmap" ) ;
         for ( a = 0 ; a < nummaplins ; ++ a ) {
             fprintf ( thef , "\nline " ) ;
             for ( b = 0 ; b < maplin[a].numpoints ; ++ b )
                 fprintf ( thef , "   %f %f" , maplin[a].x[b] , maplin[a].y[b] ) ; }  
         fprintf ( thef , "\n" ) ; }
     tmp_diagram_chg ( 1 ) ; 
     fclose ( thef ) ;
     cls () ;
     return ;
}
    
void save_metafile ( void )
{
     HDC myhdc ; 
     HENHMETAFILE hehm ; 
     LPCTSTR metafnp ; 
      fn[0]='\0';
      memset(&opbuff, 0, sizeof(OPENFILENAME));
      opbuff.lStructSize = sizeof(OPENFILENAME);
      opbuff.hwndOwner = hwnd;
      opbuff.lpstrFilter = metaffilter ;
      opbuff.nFilterIndex = 1;
      opbuff.lpstrFile = fn ;
      opbuff.lpstrTitle = "Save map to metafile...";
      opbuff.nMaxFile = sizeof(fn);
      opbuff.lpstrFileTitle = filename;
      opbuff.nMaxFileTitle = sizeof(filename)-1;
      opbuff.lpstrDefExt = "emf" ;
      opbuff.Flags = OFN_OVERWRITEPROMPT | OFN_PATHMUSTEXIST | OFN_HIDEREADONLY ; 
      if(!GetOpenFileName(&opbuff)) return ; 
      metafnp = ( LPCTSTR) fn ; 
      myhdc = NULL ; 
      myhdc = CreateEnhMetaFile ( myhdc , metafnp , NULL , "VNDM\0Map\0\0" ) ; 
      if ( myhdc == NULL ) {
           MessageBox ( hwnd , "Sorry, couldn't open metafile!" , "Error" , MB_OK ) ; 
           InvalidateRect ( hwnd , NULL , 1 ) ; 
           SetFocus ( hwnd ) ; 
           return ; }
      SelectFont ( myhdc , hfont ) ;
      cls () ;
      if ( grid_created ) showmap ( myhdc ) ;
      else show_basic_grid ( myhdc ) ; 
      hehm = CloseEnhMetaFile ( myhdc ) ;
      DeleteEnhMetaFile ( hehm ) ; 
      return ;
}

BOOL CALLBACK MatrixShrinkFunc(HWND hdwnd, UINT message, WPARAM wParam, LPARAM lParam)
{
    double xlef , xrig , yup , ydn ;
    static int myrowfuse , mycolfuse ; 
    
    HWND hWho ;
    switch(message) {
        case WM_INITDIALOG :
            myrowfuse = mycolfuse = 2 ;
            BUTT_CHECK ( 112 ) ; 
            BUTT_CHECK ( 212 ) ; 
            FOCUS_ON (IDOK ) ;
            break ; 
        case WM_COMMAND :
                switch(LOWORD(wParam)){
                        case 111: case 112: case 113: case 114: case 115: myrowfuse = LOWORD(wParam) - 110 ; break ; 
                        case 211: case 212: case 213: case 214: case 215: mycolfuse = LOWORD(wParam) - 210 ; break ; 
                        case IDOK :
                           EndDialog(hdwnd,1);
                           save_shrunk_data ( myrowfuse , mycolfuse ) ; 
                           return 1 ; 
                        case IDCANCEL :
                             EndDialog(hdwnd,0);
                             return 0;
                        default : break; }
         break; }
    return 0;
}


void save_all_areas_to_metafile ( HDC ) ; 
void save_all_consensus_to_metafile ( HDC ) ; 

void save_all_to_metafile ( void )
{
     HDC myhdc ; 
     HENHMETAFILE hehm ; 
     LPCTSTR metafnp ; 
      fn[0]='\0';
      memset(&opbuff, 0, sizeof(OPENFILENAME));
      opbuff.lStructSize = sizeof(OPENFILENAME);
      opbuff.hwndOwner = hwnd;
      opbuff.lpstrFilter = metaffilter ;
      opbuff.nFilterIndex = 1;
      opbuff.lpstrFile = fn ;
      opbuff.lpstrTitle = "Save map to metafile...";
      opbuff.nMaxFile = sizeof(fn);
      opbuff.lpstrFileTitle = filename;
      opbuff.nMaxFileTitle = sizeof(filename)-1;
      opbuff.lpstrDefExt = "emf" ;
      opbuff.Flags = OFN_OVERWRITEPROMPT | OFN_PATHMUSTEXIST | OFN_HIDEREADONLY ; 
      if(!GetOpenFileName(&opbuff)) return ; 
      metafnp = ( LPCTSTR) fn ; 
      myhdc = NULL ; 
      myhdc = CreateEnhMetaFile ( myhdc , metafnp , NULL , "VNDM\0Map\0\0" ) ; 
      if ( myhdc == NULL ) {
           MessageBox ( hwnd , "Sorry, couldn't open metafile!" , "Error" , MB_OK ) ; 
           InvalidateRect ( hwnd , NULL , 1 ) ; 
           SetFocus ( hwnd ) ; 
           return ; }
      SelectFont ( myhdc , hfont ) ;
      cls () ;
      if ( grid_created ) showmap ( myhdc ) ;
      else show_basic_grid ( myhdc ) ;

      if ( curcmd_loop == cmd_loop ) save_all_areas_to_metafile ( myhdc ) ; 
      if ( curcmd_loop == show_consensus ) save_all_consensus_to_metafile ( myhdc ) ; 
      
      hehm = CloseEnhMetaFile ( myhdc ) ;
      DeleteEnhMetaFile ( hehm ) ; 
      return ;
}

extern int max_drawn_y ;
extern int numcons ; 

void auto_save_all_results ( void )
{
     HDC myhdc ; 
     HENHMETAFILE hehm ; 
     TCHAR metafnp[ _MAX_PATH ] ;
     long int was ; 
     if ( curcmd_loop == cmd_loop ) strcpy ( metafnp , "areas-all.emf" ) ;
     else strcpy ( metafnp , "consensus-all.emf" ) ;
     myhdc = NULL ; 
     myhdc = CreateEnhMetaFile ( myhdc , metafnp , NULL , "VNDM\0Map\0\0" ) ; 
     if ( myhdc == NULL ) {
           MessageBox ( hwnd , "Sorry, couldn't open metafile!" , "Error" , MB_OK ) ; 
           InvalidateRect ( hwnd , NULL , 1 ) ; 
           SetFocus ( hwnd ) ; 
           return ; }
      SelectFont ( myhdc , hfont ) ;
      cls () ;
      if ( curcmd_loop == cmd_loop ) {
          if ( didaboot ) numrecs = bootinit - rec ; 
          save_all_areas_to_metafile ( myhdc ) ; }
      if ( curcmd_loop == show_consensus ) {

           atcoordy -= 25 ;
           strcpy ( junkstr , "CONSENSUS (AREA VALS)" ) ; 
           TextOut ( myhdc , 10 , -15 - atcoordy , junkstr , strlen ( junkstr ) ) ;
           
           save_all_consensus_to_metafile ( myhdc ) ;
           if ( didaboot ) {
               outspace = fopen ( "consensus-all.txt" , "wb" ) ; 
               effect_writeconsinfo ( 0 ) ; 
               atcoordy = - ( max_drawn_y + 15 ) ;

           atcoordy -= 25 ;
           strcpy ( junkstr , "CONSENSUS (SPP VALS)" ) ; 
           TextOut ( myhdc , 10 , -15 - atcoordy , junkstr , strlen ( junkstr ) ) ;
               
               show_consensus ( VK_ESCAPE ) ;
               consensus_is_sample = 2 ;
               cmd_loop ( 1 ) ;
               save_all_consensus_to_metafile ( myhdc ) ;
               effect_writeconsinfo ( 0 ) ;
           atcoordy = - ( max_drawn_y + 15 ) ; 
           TextOut ( myhdc , 20 , -atcoordy , " " , 1 ) ;
           hehm = CloseEnhMetaFile ( myhdc ) ;
           DeleteEnhMetaFile ( hehm ) ; 

           /*** Consensus of Areas found only in sampled data ******/
           strcpy ( metafnp , "unique-areas.emf" ) ;
           myhdc = NULL ; 
           myhdc = CreateEnhMetaFile ( myhdc , metafnp , NULL , "VNDM\0Map\0\0" ) ; 
           if ( myhdc == NULL ) {
                 MessageBox ( hwnd , "Sorry, couldn't open metafile!" , "Error" , MB_OK ) ; 
                 InvalidateRect ( hwnd , NULL , 1 ) ; 
                 SetFocus ( hwnd ) ; 
                 return ; }
           SelectFont ( myhdc , hfont ) ;
           strcpy ( junkstr , "AREAS FOUND IN SAMPLED DATA (and not full data)" ) ; 
           TextOut ( myhdc , 10 , 15 , junkstr , strlen ( junkstr ) ) ;
           was = atcoordy = -25 ; 


            show_consensus ( VK_ESCAPE ) ;
            consensus_is_sample = 3 ;
            cmd_loop ( 1 ) ;
            save_all_consensus_to_metafile ( myhdc ) ;
            if ( !numcons ) {
                   atcoordy = was - 20 ;
                   strcpy ( junkstr , "(none)" ) ; 
                   TextOut ( myhdc , 30 , -atcoordy , junkstr , strlen ( junkstr ) ) ;
                   } 
            else {
                   atcoordy = - ( max_drawn_y + 10 ) ; 
                   TextOut ( myhdc , 20 , -atcoordy , " " , 1 ) ;
                   effect_writeconsinfo ( 0 ) ; }
              }}
      hehm = CloseEnhMetaFile ( myhdc ) ;
      DeleteEnhMetaFile ( hehm ) ; 
      return ;
}




