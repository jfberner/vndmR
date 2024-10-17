#define   inva      InvalidateRect ( hwnd, NULL , 1 )  
#include <windows.h>
#include <windowsx.h>
#include <stdio.h>
#include <string.h>
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
#include <tchar.h>

RECT SelectDim ;
RECT ListBoxDim ; 
RECT CurDim ; 

#define HCTRL(x) GetDlgItem ( hdwnd , x )  

HWND ushwnd ;

void DoWindowRect ( HWND hw , RECT * rec )
{
    POINT pt ; 
    GetWindowRect ( hw , rec ) ;
    pt.x = rec->left ;
    pt.y = rec -> top ;
    ScreenToClient ( ushwnd , &pt ) ;
    rec->left = pt.x ;
    rec->top = pt.y ; 
    pt.x = rec-> right;
    pt.y = rec -> bottom ;
    ScreenToClient ( ushwnd , &pt ) ;
    rec->right = pt.x ;
    rec->bottom = pt.y ;
}     

int Heightof ( int ctrl )
{
    RECT r ;
    DoWindowRect ( GetDlgItem ( ushwnd , ctrl ) , &r ) ;
    return r.bottom - r.top ;
}     

int Widthof ( int ctrl )
{
    RECT r ; 
    DoWindowRect ( GetDlgItem ( ushwnd , ctrl ) , &r ) ;
    return r.right - r.left ;
}     

int initlzd = 0 ; 
    
void resize_select_dialog ( HWND hdwnd , int action , int moveandbmp )
{
    int SelectHeight , SelectWidth ,
         midwid , okhei , selwid , selhei , midhei , arrhei ,
         okwidth , txthei , txtwid , edithei , querywid , sharewid ,
         bmpsz , mvsz ; 
    int chg ; 
    RECT CtrlDim ;
    ushwnd = hdwnd ; 
    if ( action || !initlzd ) {
         initlzd = 1 ; 
         GetWindowRect ( hdwnd , &CurDim ) ; 
         DoWindowRect ( hdwnd, &SelectDim); }
    else
       MoveWindow ( hdwnd , CurDim.left , CurDim.top , CurDim.right - CurDim.left , CurDim.bottom - CurDim.top , TRUE ) ; 
    SelectHeight = SelectDim.bottom ;
    SelectWidth = SelectDim.right ;
    okhei = Heightof ( IDOK ) ;
    okwidth = Widthof ( IDOK ) ; 
    arrhei = Heightof ( 109 ) ; 
    midwid = Widthof ( 109 ) ;
    midhei = ( 3 * arrhei ) + 20 ; 
    txthei = Heightof ( 108 ) ;
    txtwid = Widthof ( 107 ) ;
    querywid = Widthof ( 212 ) ;
    if ( moveandbmp == 2 && querywid < ( Widthof ( 108 ) + 3 + Widthof ( 117 ) ) ) 
         querywid = Widthof ( 108 ) + 3 + Widthof ( 117 ) ; 
    selhei = SelectHeight - ( ( 2 * okhei ) + txthei + 50 ) ; 
    selwid = ( ( SelectWidth - ( midwid + 20 ) ) - 30 ) / 2 ;
    edithei = Heightof ( 111 ) ;
    sharewid = ( SelectWidth - ( ( selwid / 2 ) + 15 + okwidth ) ) // x.pos of OK button
               - selwid + 20 ; // x.pos of median buttons
    chg = 0 ; 
    if ( selhei < midhei ) {
           chg = 1 ; 
           SelectHeight = ( midhei + ( 2 * okhei ) + txthei + 50 ) ;
           selhei = SelectHeight - ( ( 2 * okhei ) + txthei + 50 ) ; }  
    if ( selwid < querywid ) {
            chg = 1 ; 
            SelectWidth = ( 2 * querywid ) + midwid + 50 ; 
            selwid = ( ( SelectWidth - ( midwid + 20 ) ) - 30 ) / 2 ; } 
    if ( chg ) { 
           MoveWindow ( hdwnd , CurDim.left , CurDim.top , SelectWidth - SelectDim.left , SelectHeight - SelectDim.top , TRUE ) ;
           GetWindowRect ( hdwnd , &CurDim ) ; 
           DoWindowRect( hdwnd, &SelectDim);
           SelectHeight = SelectDim.bottom ;
           SelectWidth = SelectDim.right ; } 
    MoveWindow ( HCTRL ( 105 ) , 10 , Heightof ( 107 ) + 20 , selwid , selhei , TRUE ) ;
    MoveWindow ( HCTRL ( 106 ) , 30 + midwid + selwid , Heightof ( 108 ) + 20 , selwid , selhei , TRUE ) ;
    MoveWindow ( HCTRL ( 107 ) , 10 , 10 , txtwid, txthei , TRUE ) ; 
    MoveWindow ( HCTRL ( 108 ) , 30 + midwid + selwid , 10 , txtwid , txthei , TRUE ) ; 
    MoveWindow ( HCTRL ( IDOK ) , SelectWidth - ( ( selwid / 2 ) + 10 + ( okwidth / 2 ) ) , SelectHeight - ( 2 * ( okhei + 10 ) ) , okwidth , okhei , TRUE ) ; 
    MoveWindow ( HCTRL ( IDCANCEL ) , SelectWidth - ( ( selwid / 2 ) + 10 + ( okwidth / 2 ) ) , SelectHeight - ( okhei + 10 ) , okwidth , okhei , TRUE ) ;
    MoveWindow ( HCTRL ( 109 ) , selwid + 20 , ( ( selhei - midhei ) / 2 ) + 20 + txthei , midwid , arrhei , TRUE ) ;
    MoveWindow ( HCTRL ( 110 ) , selwid + 20 , ( ( selhei - midhei ) / 2 ) + 30 + arrhei + txthei , midwid , arrhei , TRUE ) ; 
    MoveWindow ( HCTRL ( 112 ) , selwid + 20 , ( ( selhei - midhei ) / 2 ) + 40 + ( 2 * arrhei ) + txthei , midwid , arrhei , TRUE ) ;
    MoveWindow ( HCTRL ( 212 ) , 10 , 5 + ( SelectHeight - ( 2 * ( okhei + 10 ) ) ) , querywid , txthei + 2 , TRUE ) ;
    MoveWindow ( HCTRL ( 111 ) , 10 , ( SelectHeight - ( okhei + 10 ) ) - 5 , selwid , edithei , TRUE ) ;

    if ( !moveandbmp ) 
        MoveWindow ( HCTRL ( 113 ) , selwid + 20 , SelectHeight - ( 2 * ( okhei + 10 ) ) , sharewid , 3 * txthei , TRUE ) ;
    else {
        mvsz = Heightof ( 113 ) ;
        if ( moveandbmp == 2 ) {
           bmpsz = Heightof ( 118 ) ; 
           MoveWindow ( HCTRL ( 118 ) , ( 10 + selwid ) - bmpsz , ( 10 + ( txthei / 2 )) - ( bmpsz / 2 ) , bmpsz , bmpsz , TRUE ) ; 
           MoveWindow ( HCTRL ( 117 ) , ( 30 + midwid + ( 2 * selwid ) ) - bmpsz , ( 10 + ( txthei / 2 )) - ( bmpsz / 2 ) , bmpsz , bmpsz , TRUE ) ; } 
        MoveWindow ( HCTRL ( 113 ) , selwid + 20 , ( ( ( selhei - midhei ) / 2 ) + 10 + txthei ) - mvsz , mvsz , mvsz , TRUE ) ; 
        MoveWindow ( HCTRL ( 114 ) , selwid + 20 , ( ( selhei - midhei ) / 2 ) + 50 + ( 3 * arrhei ) + txthei , mvsz , mvsz , TRUE ) ; 
        MoveWindow ( HCTRL ( 115 ) , selwid + 25 + mvsz , ( ( ( selhei - midhei ) / 2 ) + 10 + txthei ) - mvsz , midwid - ( mvsz + 5 ) , txthei , TRUE ) ; 
        MoveWindow ( HCTRL ( 116 ) , selwid + 25 + mvsz , ( ( selhei - midhei ) / 2 ) + 50 + ( 3 * arrhei ) + txthei + ( mvsz / 2 ) , midwid - ( mvsz + 5 ) , txthei , TRUE ) ; } 
    InvalidateRect ( HCTRL ( 105 ) , NULL , 1 ) ; 
    InvalidateRect ( HCTRL ( 106 ) , NULL , 1 ) ;
    InvalidateRect ( hdwnd , NULL , 1 ) ;
    return ; 
}     




