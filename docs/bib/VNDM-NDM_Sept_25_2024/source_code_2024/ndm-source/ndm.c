#include "ndm.h"

/*
   Updates: 
   Version 1 (2001):           integer only calculations
   Version 1.5 (July 2002):    included score as a floating point
   Version 1.6 (Nov. 2003):    added -p option for edge-effect
   Version 2.0 (July 2004):    keeps grid dimensions, Windows VNDM,
                               added species names, can start search
                               from sets in a file
   Version 2.2 (Jan 2004):     nothing significant in NDM, version number
                               just matches changes to VNDM.
   Version 2.5 (Oct 2005):     nothing significant in NDM, version number
                               just matches changes to VNDM.
   Version 2.6 (Feb 2006):     added the -sskip option, and improved the
                               -skip option, which greatly speeds up searches
   Version 3.1 (Nov. 2016):    added pre-checking for distant records (stored
                               in spminmax), which increases speed x2 to x4
                               added "framed" searches; other fixes and additions
   Version 3.1 (March 2022):   fixed faulty code at new_is_superfluous(), which
                               could cause loops in the structure listing areas
                               by size
*/

#ifdef LINUX 
#define CLOCK_TICKS CLOCKS_PER_SEC 
int running_in_background = 0 ; 
FILE * bgroundfile ; 
#else
#define CLOCK_TICKS CLK_TCK 
#endif

void * mymem ( int ) ; 
int get_species_tree ( int , int ) ; 
int32 * ranswaplist ; 
int * userextass = NULL ; 
int weight_species = 0 ;
float * species_weight ; 

int num_replicates = 1 , randomize_startpoint , * daspranlist ;
double minimum_sp_score = -1000 ;

/*** Handling higher groups ********/
int * species_tree , num_higher_taxa , numterminals , spspace ;
int * treesis , * treefirs , treeroot , number_of_groups ; 
int * treelist , * acurl , * innerlist , * nodfork ;
double * indspscore = NULL ; 

int arminc , arminr , armaxc , armaxr ; 

void show_copyright_notice ( void )
{ fprintf ( stderr , "\n\
\n\
\
\
 /************************************************************************\\    \n\
 *                                                                        *    \n\
 *       NDM version 3.1:  Program to search for areas of endemism        *    \n\
 *           Copyright © Pablo A. Goloboff 2001-2005                      *    \n\
 *                                                                        *    \n\
 *                                                                        *    \n\
 *                              NOTICE                                    *    \n\
 *                                                                        *    \n\
 *  Permission to use, copy, modify, and distribute this software (and    *    \n\
 *  any documentation) for any purpose and without fee is hereby granted  *    \n\
 *  provided that the above copyright notice appear in all copies and     *    \n\
 *  that both the copyright notice and this permission notice appear in   *    \n\
 *  supporting documentation.                                             *    \n\
 *                                                                        *    \n\
 *  Neither the Author nor his supporting Institution (Consejo Nacional   *    \n\
 *  de Investigaciones Cientificas y Tecnicas, Argentina) make any        *    \n\
 *  claims about the suitability of this software for any purpose         *    \n\
 *                                                                        *    \n\
 \\************************************************************************/   \
 \
 \n" ) ;

 return ; 
}


/*********  THIS PART DOES THE HEURISTICS ***************/ 
/*        (the key function is "heuristics")            */

int new_is_superfluous ( void )
{
    int mustclean = 0 , dumpit , a ;
    int beatsitself = 0 ; 
    Artyp * ol ;
    Listyp * rl , * nl , * prvlist ; 
    Artyp * ara , * nu ; 
    if ( !skip_superfluous ) return 0 ;
    nu = recptr - 1 ;
    ara = rec ;
    if ( swaprec -> score5 < nu -> score5            // i.e. move makes set being 
         && one_vs_other ( nu , swaprec ) > 0 )      // swapped superfluous...
           beatsitself = 1 ; 
    while ( ++ ara < nu ) {
           if ( ara -> erase ) continue ; 
           if ( iscontra ( ara , nu ) ) {
             dumpit = one_vs_other ( nu , ara ) ;
             if ( dumpit == 1 ) { ara -> erase = 2 ; if ( !mustclean ) mustclean = 1 ; } 
             if ( dumpit == -1 ) { nu -> erase = 2 ; mustclean = 2 ; break ; }}}
    if ( mustclean < 2 ) { 
       ara = rec ;
       while ( ++ ara < nu ) {
            if ( ara -> erase ) continue ; 
            a = oneintwo ( ara , nu ) ;
            if ( a == 1 ) // i.e. ara is inside nu
                chk_superfluous ( ara , nu ) ;  
            if ( a == -1 ) //i.e. nu is inside ara
                chk_superfluous ( nu , ara ) ;
            if ( ara -> erase ) { ara -> erase = 2 ; if ( !mustclean ) mustclean = 1 ; } 
            if ( nu -> erase ) { nu -> erase = 2 ; mustclean = 2 ; break ; }}}

    if ( mustclean == 2 ) {
               -- nexreclist ;
               sizelist [ cursize ] = nexreclist -> tolist ;
               -- recptr ;
               for ( ara = rec ; ara < recptr ; ++ ara ) ara -> erase &= ~2 ;
               return 1 ; } 

    if ( beatsitself && autoreplace ) {
           -- havcomb [ swaprec -> key ] ;
           // take swaprec off list...
           rl = sizelist [ swaprec -> size ] ;
           prvlist = NULL ; 
           while ( rl -> toar != swaprec ) {
               prvlist = rl ; 
               rl = ( Listyp * ) rl -> tolist ; }
           if ( prvlist == NULL ) 
                sizelist [ swaprec -> size ] = ( Listyp * ) rl -> tolist ;
           else prvlist -> tolist = rl -> tolist ; 
           // ...and put "nu" in the list...
           /********* Faulty code; this part can create loops; fixed March 2022 ********            
           reclist [ swaprec - rec ].tolist = sizelist [ nu -> size ] ;  
           a = swaprec - rec ; 
           sizelist [ nu -> size ] = reclist + a ;
           *****************************************************************************/
           /************* Replacemente code begins here ********************************/
           nl = rl ;  /* the list entry for swaprec, found above  */ 
           -- nexreclist ; 
           rl = sizelist[ nu->size ] ;
           sizelist [ nu -> size ] = nl ;
           if ( rl == NULL ) nl -> tolist = NULL ;  // in case no areas of this size existed before 
           else nl -> tolist = ( Listyp * ) rl -> tolist ;  // i.e. new area is the entry point, point it to where it pointed...
           nl -> toar = swaprec ;
           /********** end of replacemente code March 2022 *****************************/
           copyar ( swaprec , nu ) ;
           -- recptr ; 
           if ( mustclean ) {
              swaprec -> erase = 1023 ;
              swaprec = NULL ;
              a = 0 ; 
              for ( ara = rec ; ara < recptr ; ++ ara ) {
                  if ( swaprec == NULL ) 
                      if ( ara -> erase < 1 ) ++ a ;
                      else if ( ara -> erase == 1023 ) {
                               swaprec = rec + a ;
                               ara -> erase = 0 ; }
                  if ( ara -> erase > 1 ) ara -> erase = 1 ; }
              delete_marks ( 1 ) ; 
              reset_reclist () ; }
           -- swaprec ; 
           reset_swapping = 1 ;
           return 0 ; }

    if ( mustclean ) {
           for ( ara = rec ; ara < recptr ; ++ ara )
                if ( ara -> erase > 1 ) ara -> erase = 1 ; 
           if ( recptr - rec == maxrec - 1 ) {
               delete_marks ( 1 ) ; 
               reset_reclist () ; 
               swaprec = rec ;
               while ( swaprec -> swapd && swaprec < recptr )  ++ swaprec ;
               -- swaprec ;
               return 0 ; }}
    return 0 ;
} 

void randomlist ( int num , int32 * tli )
{   int b , c , d , e ;
    if ( ranseed == 1 ) {
        for ( b = 0 ; b < num ; ++ b ) tli[b] = b ;
        return ; }
    for ( b = 0 ; b < num ; ++ b ) tli[b] = b ;
    for ( c = 0 ; c < num ; ++ c ) {
             d = 1 + ( rand () % ( num - 1 ) ) ;
             e = tli[d] ;
             tli[d] = tli[c] ;
             tli[c] = e ; }
    return ;
}

void prepare_evaluation ( void )
{
    int a , x ; int * lp ; int outnonadja ; int32 mb = 1 , sb , * sintpt , * bintpt ; int mc = 0 , sc , j , k , numar ;
    sintpt = smallarset ; bintpt = bigarset ; 
    for ( a = 0 ; a < spp ; ++ a ) {
        if ( ! ( ( * sintpt | * bintpt ) & mb ) ) {
            if ( mb == ( 1 << 31 ) ) {
                mb = 1 ;
                ++ mc ;  ++ sintpt ; ++ bintpt ; }
            else mb <<= 1 ;
            continue ; }
        /***    How many records on outermost sector? ********/
        outnonadja = 0 ;  mc = a / 32 ;
        if ( userextass != NULL )
             outnonadja = userextass [ a ] ; 
        for ( lp = faraway ; lp < farawaypt ; ++ lp ) {
            numar = * lp ; j = numar % cols ; k = numar / cols ;
            if ( ( assmatrix [ k ] [ j ] [ mc ] & mb ) ) ++ outnonadja ; }
        globnonadja [ a ] = outnonadja ; 
        if ( mb == ( 1 << 31 ) ) {
            mb = 1 ; ++ mc ; ++ sintpt ; ++ bintpt ; }
            else mb <<= 1 ; } 
    return ;
} 

double do_evaluation ( void )
{
    int a , x , isexo , skipit ;
    int * lp ;
    int * fare , * fato , b ; 
    int pres , out , ass , inf , outadja, outnonadja ;
    int32 mb , sb , * intpt ;
    int mc , sc , j , k , numar , jj , kk , snumar , atleastone , numemps ;
    int32 * areapt = currec.lst ;
    double spscore , myscore = 0 , dinf , dass , dout , dpres , dsize , dadja, dnadja ;
    double Eval ;
   
    scoring_spp = 0 ;
    intpt = curinters [ cursize ] ;
    mb = 1 ;
    mc = 0 ;
    Eval = ( double ) ( listadjapt - listadja ) ;
    for ( a = 0 ; a < spp ; ++ a ) {
        if ( species_tree != NULL ) 
             indspscore [ a ] = 0 ; 
        /****  Is species in (enlarged) intersection?  ********/
        if ( ! ( * intpt & mb ) ) {
            if ( mb == ( 1 << 31 ) ) {
                          mb = 1 ; ++ mc ; 
                          ++ intpt ; }
            else mb <<= 1 ;
            continue ; }
        /***    Is species also found outside?   ********/
        isexo = 0 ;
        outnonadja = globnonadja [ a ] ; 
        mc = a / 32 ;     
        for ( lp = listnonadja ; lp < listnonadjapt && !isexo ; ++ lp ) {
               numar = * lp ;
               j = numar % cols ;
               k = numar / cols ; 
               if ( ( matrix [ k ] [ j ] [ mc ] & mb ) ) isexo = 1 ;
               if ( ( assmatrix [ k ] [ j ] [ mc ] & mb ) ) ++ outnonadja ; 
               } 
        if ( isexo ) {             
            * intpt &= ~mb ; 
            if ( mb == ( 1 << 31 ) ) {
                          mb = 1 ; ++ mc ; 
                          ++ intpt ; }
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
                 atleastone = 0 ;
                 if ( !musthaveone ) atleastone = 1 ; 
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
                         if ( ( matrix [ kk ] [ jj ] [ mc ] & mb ) ) atleastone = 1 ;
                         else 
                             if ( ++ numemps > abslim ) { jj = j + 1 ; break ; }}}
                if ( atleastone && numemps <= abslim &&
                     ( ifac > afac || ( assmatrix [ k ] [ j ] [ mc ] & mb ) == 0 ) ) ++ inf ;
                else {
                    if ( ( assmatrix [ k ] [ j ] [ mc ] & mb ) == 0 ) skipit = 1 ;
                    else if ( musthaveone == 2 && !atleastone ) skipit = 1 ; 
                    ++ ass ; }}
        if ( skipit || (
             ( pres * 100 ) / cursize < min_pres_perc || 
             ( min_pres_perc && pres < 2 ) ) ) {
              * intpt &= ~mb ; 
              if ( mb == ( 1 << 31 ) ) {
                          mb = 1 ; ++ mc ; 
                          ++ intpt ; }
              else mb <<= 1 ; 
              continue ; } 
        for ( lp = listadja ; lp < listadjapt ; ++ lp ) {
                 numar = * lp ;
                 j = numar % cols ;
                 k = numar / cols ;
                 if ( ( matrix [ k ] [ j ] [ mc ] & mb ) ) ++ out ;
                 else if ( ( assmatrix [ k ] [ j ] [ mc ] & mb ) ) ++ outadja ; }
         /**** Calculating score ********/
         //++ scoring_spp ; 
         dout = out ;
         dass = ass ;
         dinf = inf ;
         dpres = pres ;
         dsize = cursize ;
         dadja = outadja ;
         dnadja = outnonadja ;

         if ( !use_edge_props ) 
           spscore  =
              ( dpres +
                ( ifac * dinf ) +
                ( afac * dass )  )
                                 /
              ( dsize +
                ( ( 1 / oufac ) * dout ) +
                ( ( 1 / oafac ) * dadja ) +
                ( ( 1 / ononafac ) * dnadja ) ) ;
         else {
           spscore  =
              ( ( dpres +
                ( ifac * dinf ) +
                ( afac * dass )  ) *
                ( 1 - ( ( ( dout / oufac ) + ( dadja / oafac ) ) / Eval ) ) )  
                                 /
              ( dsize + ( ( 1 / ononafac ) * dnadja ) ) ;
           if ( spscore < 0 ) spscore = 0 ; }

         if ( spscore >= minimum_sp_score ) {
             ++ scoring_spp ; 
             if ( !weight_species ) myscore += spscore ;
             else myscore += spscore * species_weight [ a ] ;
             if ( species_tree != NULL )
                indspscore [ a ] = spscore ; }
         else * intpt &= ~mb ; 
         if ( mb == ( 1 << 31 ) ) {
                          mb = 1 ; ++ mc ; 
                          ++ intpt ; }
         else mb <<= 1 ;

        }

    if ( species_tree != NULL ) {
        intpt = curinters [ cursize ] ;
        myscore = 0 ;
        scoring_spp = 0 ; 
        for ( a = number_of_groups - 1 ; a > 0 ; a -- ) {
            j = treelist [ a ] - 1 ;
            * ( fare = fato = innerlist ) = j + 1 ;
            if ( indspscore [ j ] == 0 ) continue ; 
            ++ fare ;
            Eval = 0 ;
            while ( fato < fare ) {
                if ( ( b = * fato ++ ) >= numterminals )
                  if ( ( b == j + 1 ) || ( indspscore [ b - 1 ] == 0 ) )
                     for ( x = treefirs [ b ]  ; x >= 0 ; x = treesis [ x ] ) * fare ++ = x ;
                if ( !weight_species ) 
                    if ( b < numterminals ) 
                         Eval += indspscore [ b ] ;
                    else if ( b != j + 1 ) Eval += indspscore [ b - 1 ] ;
                else 
                    if ( b < numterminals ) 
                         Eval += indspscore [ b ] * species_weight [ b ] ;
                    else if ( b != j + 1 ) Eval += indspscore [ b - 1 ] * species_weight [ b - 1 ] ; }
            if ( indspscore [ j ] <= Eval ) indspscore [ j ] = 0 ;  
            else {
                * ( fare = fato = innerlist ) = j + 1 ;
                ++ fare ;
                while ( fato < fare ) {
                    if ( ( b = * fato ++ ) >= numterminals )
                         for ( x = treefirs [ b ]  ; x >= 0 ; x = treesis [ x ] ) * fare ++ = x ;
                    if ( b < numterminals ) indspscore [ b ] = 0 ; 
                    else if ( b != j + 1 ) indspscore [ b - 1 ] = 0 ; }}}
         for ( a = 0 ; a < spp ; ++ a ) {
              if ( indspscore [ a ] == 0 ) 
                  intpt [ a / 32 ] &= ~ ( 1 << ( a % 32 ) ) ; 
              else ++ scoring_spp ;
              if ( !weight_species ) 
                    myscore += indspscore [ a ] ;
              else myscore += indspscore [ a ] * species_weight [ a ] ; }}

    if ( scoring_spp < minscore &&
         dump_suboptimal ) return -myscore ; 
    return myscore ;
} 

void init_combs ( void )
{ int32 a ;
  Artyp * ar ;
  int32 * havpt = ( int32 * ) havcomb ; 
  unsigned short int * sipt , x ; 
  for ( a = ( 65536 / 4 ) ; a -- ; ) * havpt ++ = 0 ;
  for ( ar = rec ; ar < recptr ; ++ ar ) {
      sipt = ( unsigned short int * ) ar -> lst ;
      sipt += 2 * arcells ; 
      x = 0 ; 
      for ( a = 2 * arcells ; a -- ; ) x ^= * -- sipt ;
      ++ havcomb [ x ] ; }
  return ; 
}       

int isduparea ( Artyp * nu , int chkscor )
{
    Artyp * ol ;
    Listyp * rl ; 
    int a , isid ;
    int32 * ap , * bp ;
    unsigned short int * sipt , x ; 
    sipt = (unsigned short int * ) nu -> lst ;
    x = 0 ; 
    for ( a = 2 * arcells ; a -- ; ) x ^= * sipt ++ ;
    if ( havcomb [ x ] == 0 ) return 0 ;
    rl = sizelist [ cursize ] ; 
    while ( rl != NULL ) {
        ol = rl -> toar ; 
        ap = nu -> lst ;
        bp = ol -> lst ;
        isid = 1 ;
        if ( chkscor ) isid = ( nu->score5 == ol->score5 ) ; 
        for ( a = arcells ; a -- && isid ; )
             if ( * ap ++ != * bp ++ ) isid = 0 ;
        if ( isid ) {
            ++ dups_found ; 
            return 1 ; } 
        rl = ( Listyp * ) rl -> tolist ; } 
    return 0 ;
} 


void reset_reclist ( void )
{
  int a ;
  Artyp * ar ; 
  for ( a = maxsize ; a -- ; ) sizelist [ a ] = NULL ;
  nexreclist = reclist ; 
  for ( a = maxrec ; a -- ; ) ( nexreclist ++ ) -> tolist = NULL ;
  nexreclist = reclist ; 
  for ( ar = rec ; ar < recptr ; ++ ar ) {
      nexreclist -> toar = ar ;
      nexreclist -> tolist = ( void * ) sizelist [ ar -> size ] ;
      sizelist [ ar -> size ] = nexreclist ;
      ++ nexreclist ; }
  return ; 
}     


void del_low_scores ( void )
{
    Artyp * ar ;
    int some = 0 ; 
    for ( ar = rec ; ar < recptr ; ++ ar ) { 
        ar -> erase = 0 ;
        if ( ar -> score5 < minrealscore ||
             ar -> numspp < minscore )  
             { ar -> erase = 1 ; some = 1 ; }}
    if ( some ) delete_marks ( 1 ) ;
    return ;
} 


void report_search_status ( void )
{
    int timediff , speed ; 
#ifndef LINUX 
    timediff = ( ( ( now = clock () ) - init_search ) / CLOCK_TICKS ) ;
    if ( timediff )
          speed = arsexd / ( ( now - init_search ) / CLOCK_TICKS ) ;
    else speed = 0 ;
#else 
    timediff = ( ( ( now = clock () ) - init_search ) / CLOCKS_PER_SEC ) ;
    if ( timediff )
          speed = arsexd / ( ( now - init_search ) / CLOCKS_PER_SEC ) ;
    else speed = 0 ;
#endif
    if ( speed ) fprintf ( stderr , "\r  %5i  %6i %7.3f %9i %6i              \n" , swaprec - rec , recptr - rec , bestscore , arsexd , speed ) ;  
    else fprintf ( stderr , "\r  %5i  %6i %7.3f %9i   ????            \n" , swaprec - rec , recptr - rec , bestscore , arsexd ) ;
#ifdef LINUX 
    if ( running_in_background ) 
      if ( ! ( timediff % 1 ) ) 
          if ( speed ) 
             fprintf ( bgroundfile , 
                 "  %5i  %6i %7.3f %9i %6i              \n" , 
                swaprec - rec , recptr - rec , bestscore , arsexd , speed ) ;  
#endif
    return ; 
}     



// int totnumvisits = 0 ; 

int previous_cleanup = 0 ; 

void storar ( void )
{
  int x , a = 0 , timediff , speed ;
  Artyp * ara ; 
  unsigned short int * sipt , y ;
  int myhi , mylo ; 
  static tried_to_clean = 0 ;


Listyp * lp ; Artyp * ap ; 


  if ( recptr - rec >= maxrec ) {
          if ( max_buffer_clean == num_buffer_cleans ) {
              previous_cleanup = 1 ;
              ++ num_buffer_cleans ;
              report_search_status () ;  
              if ( !saveall ) show_time () ; 
              clean_areas ( 1 , 1 ) ; 
              save_results () ;
              show_time () ;
              if ( query ) getch () ; 
              exit ( 0 ) ; } 
          fprintf ( stderr , "\r   Filled memory ... cleaning partial results\r" ) ;
          if ( swaprec - rec < recinit ) {
               for ( ara = rec ; ara < recptr ; ++ ara ) {
                   ara -> erase = 0 ;
                   if ( ara <= swaprec &&  
                       ( ara -> score5 < minrealscore || ara -> numspp < minscore ) )
                        ara -> erase = 1 ; }
               delete_marks ( 1 ) ; } 
          clean_areas ( 0 , 0 ) ;  
          if ( recptr - rec >= maxrec )
              {
                report_search_status () ;  
                del_low_scores () ; 
                fprintf ( stderr , "\nBuffer overflow (can't discard any area)\n" ) ;
                save_results () ;
                show_time () ; 
                if ( query ) getch () ;
                exit ( 0 ) ; }
          if ( recptr - rec == previous_cleanup ) {
              report_search_status () ;  
              del_low_scores () ; 
              fprintf ( stderr , "\nCycle of swapping produced no new areas...\n" ) ;
              save_results () ;
              show_time () ; 
              if ( query ) getch () ;
              exit ( 0 ) ; }
          reset_reclist () ; 
          init_combs () ; 
          ++ num_buffer_cleans ; 
          previous_cleanup = recptr - rec ;
          fprintf ( stderr , "                                                         \r" ) ; 
          swaprec = rec ;
          while ( swaprec -> swapd && swaprec < recptr )  ++ swaprec ;
          -- swaprec ; } 
  recptr->lst = ( int32 * ) mymem ( arcells * sizeof ( int32 ) ) ; 
  if ( recptr->lst == NULL ) { 
                maxrec = recptr - rec ; 
                fprintf ( stderr,"\nNot enough memory to store more than %i areas... continue checking\n" , maxrec ) ; 
                return ; }
  recptr->splist = ( int32 * ) mymem ( spcells * sizeof ( int32 ) ) ; 
  if ( recptr->splist == NULL ) { 
                maxrec = recptr - rec ; 
                fprintf ( stderr,"\nNot enough memory to store more than %i areas... continue checking\n" , maxrec ) ; 
                return ; }
  intersptr = curinters [ cursize ] ; 
  for ( x = spcells ; x -- ; ) currec.splist[x] = intersptr[x] ;
  copyar ( recptr , &currec ) ;
  recptr -> swapd = 0 ;
  sipt = ( unsigned short int * ) recptr -> lst ;
  sipt += 2 * arcells ; 
  y = 0 ;
  myhi = 0 ;
  mylo = 1000000 ; 
  for ( a = 2 * arcells ; a -- ; ) {
      -- sipt ; 
      if ( * sipt && a < mylo ) mylo = a ;
      if ( * sipt && a > myhi ) myhi = a ; 
      y ^= * sipt ; }
  recptr -> hicell = myhi ;
  recptr -> locell = mylo ;
  recptr -> key = key_combination = y ; 
  /***  This sorts the areas by size, to speed up checking of duplicates **/
  nexreclist -> toar = recptr ;
  nexreclist -> tolist = ( void * ) sizelist [ cursize ] ;
  sizelist [ cursize ] = nexreclist ;
  ++ nexreclist ;
  ++ recptr ; 

/*
totnumvisits ++ ; 
if ( ( Listyp * ) reclist[ 1286 ].tolist - reclist >= recptr - rec )
   fprintf ( stderr , "\raqui ta la madre del borrego ( size 1286: %i), %i visits !....\n" , rec[1286].size , totnumvisits ) ; 
if ( cursize == 6 && recptr - rec == 1287 ) {
 lp = sizelist [ cursize ] ;
 fprintf ( stderr , "\rAREA %i OF SIZE 6...\n" , recptr - rec - 1 ) ;
 while ( lp != NULL ) {
   ap = lp -> toar ;
   fprintf ( stderr , "   Entry at %i" , lp - reclist ) ;
   if ( lp->tolist == NULL )
        fprintf ( stderr , "-> area %i (STOP)\n" , ap - rec ) ;   
   else fprintf ( stderr , "-> area %i (->%i)\n" , ap - rec , ( Listyp * ) lp-> tolist - reclist ) ;
   lp = ( Listyp * ) lp -> tolist ; }}
*/


} 

int contig_to_bigar ( int j ) 
{   int32 mb , mc ; 
    int a , b , numar , x , y ; 
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
             if ( ( bigar[mc] & mb ) != 0 ) return 1 ; }} 
    return 0 ; 
} 
    
void spinitar ( int sp )
{
    int a , x , y ;
    int mysz = 0 , mc ;
    int32 * apt = currec.lst , mb , * conpt ;
    if ( spminmax[sp].minc > spminmax[sp].maxc ) return ;  // i.e. sp has no records
    for ( a = arcells ; a -- ; ) apt [ a ] = 0 ;
    mc = sp / 32 ;
    mb = 1 << ( sp % 32 ) ; 
    for ( a = totareas ; a -- ; ) {
        y = a / cols ;
        x = a % cols ;
        if ( !isdefd [ y ] [ x ] ) continue ; 
        if ( use_wide_init ) { 
             if ( ( fake_matrix [ y ] [ x ] [ mc ] & mb ) ) { 
                     apt [ a / 32 ] |= 1 << ( a % 32 ) ;
                      ++ mysz ; }}
        else 
            if ( ( assmatrix [ y ] [ x ] [ mc ] & mb ) ) { 
                     apt [ a / 32 ] |= 1 << ( a % 32 ) ;
                      ++ mysz ; }}
    if ( const_search ) {
        conpt = const_list ;
        apt = currec.lst ; 
        for ( a = arcells ; a -- ; ) {
           mb = * apt & ~ * conpt ;
           * apt &= * conpt ;
           ++ apt ;
           ++ conpt ; 
           if ( mb ) mysz -= onbits ( mb ) ; }
        if ( !mysz ) return ; } 
    currec.size = cursize = mysz ;
    smallest_cell = minframey = minframex = 0 ;
    largest_cell = totareas ;
    maxframey = rows ; 
    maxframex = cols ; 
    for ( a = arcells ; a -- ; ) farar [ a ] = 0 ; 
    if ( mysz > 1 && !isduparea ( &currec , 0 ) ) {
        prepare_all_lists () ;
        for ( a = 0 ; a < spcells ; ++ a ) curinters [ cursize ] [ a ] = ~0 ; 
        ++ arsexd ; 
        currec.score5 = dorule5 ( 0 ) ;
        curinters [ cursize ] [ spcells - 1 ] &= last_sp_filter ; 
        if ( currec.score5 < 0 ) currec.score5 = -currec.score5 ;
        if ( currec.score5 > bestscore ) bestscore = currec.score5 ; 
        currec.numspp = scoring_spp ; 
        storar ( ) ;
        havcomb [ key_combination ] ++ ; } 
    return ; 
} 

void prepare_all_lists ( void )
{
    int32 mb , * lst = currec.lst ;
    int i , mc , x , y ;
    listinpt = listin ;
    listadjapt = listadja ; 
    listnonadjapt = listnonadja ;
    arminc = arminr = 32767 ;
    armaxc = armaxr = 0 ; 
    for ( y = minframey ; y < maxframey ; ++ y ) {
      for ( x = minframex ; x < maxframex ; ++ x ) {
        if ( !isdefd[y][x] ) continue ;
        i = ( y * cols ) + x ;
        if ( i < smallest_cell || i >= largest_cell ) continue ; 
        mc = i / 32 ;
        mb = 1 << ( i % 32 ) ;
        if ( ( lst [ mc ] & mb ) ) {
            if ( x > armaxc ) armaxc = x ; 
            if ( x < arminc ) arminc = x ; 
            if ( y > armaxr ) armaxr = y ; 
            if ( y < arminr ) arminr = y ; 
            * listinpt ++ = i ; } 
        else 
          if ( iscontig ( i ) ) 
            * listadjapt ++ = i ; 
          else 
                if ( !( farar [ mc ] & mb ) ) 
                   * listnonadjapt ++ = i ; }}
    if ( arminc ) arminc -- ;
    if ( arminr ) arminr -- ;
    armaxc ++ ; 
    armaxr ++ ; 
    return ; 
}


void prepare_edgelist ( void )
{
    int32 mb , * lst = currec.lst ;
    int a , i , mc , x , y ;
    int foundar ; 
    listedgept = listedge ;
    for ( a = spcells ; a -- ; ) smallarset [ a ] = bigarset [ a ] = ~0 ;
    smallarset [ spcells - 1 ] &= last_sp_filter ;
    bigarset [ spcells - 1 ] &= last_sp_filter ;
    for ( a = arcells ; a -- ; ) bigar [ a ] = lst [ a ] ;
    for ( i = 0 ; i < totareas ; ++ i ) {
        mc = i / 32 ;
        mb = 1 << ( i % 32 ) ;
        y = i/cols ;
        x = i%cols ; 
        if ( !isdefd[y][x] ) continue ; 
        if ( ( lst [ mc ] & mb ) ) {
             for ( a = spcells ; a -- ; ) 
                bigarset [ a ] &= fake_matrix [ y ] [ x ] [ a ] ; 
             if ( isinedge ( i ) ) * listedgept ++ = i ;
             else { for ( a = spcells ; a -- ; )
                      smallarset [ a ] &= fake_matrix [ y ] [ x ] [ a ] ; }} 
        else
           if ( iscontig ( i ) ) {
                  if ( !dontadd ) { 
                       * listedgept ++ = i ;
                       bigar [ mc ] |= mb ; }}
           else { for ( a = spcells ; a -- ; )
                       smallarset [ a ] &= ~matrix [ y ] [ x ] [ a ] ; }}
    farawaypt = faraway ;
    for ( i = arcells ; i -- ; ) farar [ i ] = 0 ; 
    foundar = 0 ;
    smallest_cell = 0 ; 
    minframex = minframey = 100000000 ;
    maxframex = maxframey = 0 ; 
    for ( i = 0 ; i < totareas ; ++ i ) {
        mc = i / 32 ;
        mb = 1 << ( i % 32 ) ;
        y = i/cols ;
        x = i%cols ; 
        if ( !isdefd[y][x] ) continue ;
        if ( ( bigar [ mc ] & mb ) ) {
            if ( minframex > x ) minframex = x ;
            if ( minframey > y ) minframey = y ;
            if ( maxframex < x ) maxframex = x ;
            if ( maxframey < y ) maxframey = y ; 
            foundar = 1 ; continue ; } 
        if ( !contig_to_bigar ( i ) ) {
               if ( !foundar ) smallest_cell = i ;
               farar[ mc ] |= mb ;  
               * farawaypt ++ = i ; 
               for ( a = spcells ; a -- ; )
                    bigarset [ a ] &= ~matrix [ y ] [ x ] [ a ] ; }
        else {
               if ( minframex > x ) minframex = x ;
               if ( minframey > y ) minframey = y ;
               if ( maxframex < x ) maxframex = x ;
               if ( maxframey < y ) maxframey = y ;
               foundar = 1 ; }}
    largest_cell = totareas ; 
    for ( i = totareas ; i -- ; ) {
        mc = i / 32 ;
        mb = 1 << ( i % 32 ) ;
        y = i/cols ;
        x = i%cols ; 
        if ( !isdefd[y][x] ) continue ;
        if ( ( bigar [ mc ] & mb ) ) break ; 
        if ( !contig_to_bigar ( i ) ) largest_cell = i + 1 ;
        else break ; }

    bigarnumspp = smallarnumspp = 0 ;
    for ( a = spcells ; a -- ; ) {
        bigarnumspp += onbits ( bigarset [ a ] ) ;
        smallarnumspp += onbits ( smallarset [ a ] ) ; } 

    prepare_evaluation () ; 
    if ( ++ maxframey > rows ) maxframey = rows ; 
    if ( ++ maxframex > cols ) maxframex = cols ;
    return ; 
}     

double curscore ; 

void wipe_quad ( int quad )
{
    int cell , a ;
    double val ;
    int32 bit ;
    if ( smallarnumspp < minscore && dump_suboptimal ) { ++ arsexd ; return ; } 
    if ( cursize < 3 ) return ; 
    -- cursize ;
    cell = quad / 32 ;
    bit = 1 << ( quad % 32 ) ;
    currec.lst [ cell ] &= ~bit ;
    currec.size = cursize ;
    if ( !post_individuation ) 
      if ( isduparea ( &currec , 0 ) ) {
           ++ cursize ;
           currec.lst [ cell ] |= bit ;
           return ; }
    for ( a = spcells ; a -- ; ) curinters [ cursize ] [ a ] = smallarset [ a ] ; 
    prepare_all_lists () ;
    arsexd ++ ; 
    val = do_evaluation () ;
    if ( use_wide_init && val < minrealscore ) val = -1 ; 
    if ( val >= curscore * slopeval ) {
        currec.score5 = val ;
        if ( post_individuation ) 
          if ( isduparea ( &currec , 1 ) ) {
            ++ cursize ;
            currec.lst [ cell ] |= bit ;
            return ; }
        currec.numspp = scoring_spp ; 
        storar ( ) ;
        if ( ! new_is_superfluous () )
                 havcomb [ key_combination ] ++ ; 
        if ( val > bestscore ) bestscore = val ; } 
    ++ cursize ;
    currec.lst [ cell ] |= bit ;
    return ; 
}     

void add_quad ( int quad )
{
    int cell , a ;
    double val ; 
    int32 bit ;
    cell = quad / 32 ;
    bit = 1 << ( quad % 32 ) ;
    if ( const_search && ( const_list [ cell ] & bit ) == 0 ) return ;
    if ( bigarnumspp < minscore && dump_suboptimal ) { ++ arsexd ; return ; } 
    currec.lst [ cell ] |= bit ;
    ++ cursize ;
    currec.size = cursize ; 
    if ( !post_individuation ) 
       if ( isduparea ( &currec , 0 ) ) {
           -- cursize ;
           currec.lst [ cell ] &= ~bit ;
           return ; } 
    for ( a = spcells ; a -- ; ) curinters [ cursize ] [ a ] = bigarset [ a ] ; 
    prepare_all_lists () ;
    arsexd ++ ;
    val = do_evaluation () ; 
    if ( use_wide_init && val < minrealscore ) val = -1 ; 
    if ( val >= curscore * slopeval ) {
       currec.score5 = val ; 
       if ( post_individuation ) 
         if ( isduparea ( &currec , 1 ) ) {
           -- cursize ;
           currec.lst [ cell ] &= ~bit ;
           return ; } 
        currec.numspp = scoring_spp ; 
        storar ( ) ;  
        if ( ! new_is_superfluous () )
                 havcomb [ key_combination ] ++ ; 
        if ( val > bestscore ) bestscore = val ; } 
    -- cursize ;
    currec.lst [ cell ] &= ~bit ;
    return ; 
}     

void retouch_single_cell ( Artyp * recrd )
{
    int a , quad , arcell , x , y , j ;
    int lissize , atcell ; 
    int32 arbit ; 
    int * nex ;
    recrd -> swapd = 1 ; 
    if ( recrd -> size < 2 ) return ; 
    for ( a = arcells ; a -- ; ) currec.lst [ a ] = recrd -> lst [ a ] ;
    cursize = currec.size = recrd -> size ;
    curscore = recrd -> score5 ; 
    prepare_edgelist () ;
    reset_swapping = 0 ;
    lissize = listedgept - listedge ;
    randomlist ( lissize , ranswaplist ) ;
    for ( atcell = 0 ; atcell < lissize && !reset_swapping ; ++ atcell ) {
        chkbyebye () ; 
        quad = listedge [ ranswaplist [ atcell ] ] ;
        arcell = quad / 32 ;
        arbit = 1 << ( quad % 32 ) ;
        if ( ( currec.lst [ arcell ] & arbit ) ) wipe_quad ( quad ) ;
        else add_quad ( quad ) ; }
    return ; 
} 

void change_2_quads ( int quad1 , int quad2 )
{
    int cell1 , cell2 , a ;
    double val ;    
    int32 bit1 , bit2 , olcellval1 , olcellval2 ;
    int olsz = cursize ;
    int some_add = 0 ; 
    cell1 = quad1 / 32 ;
    bit1 = 1 << ( quad1 % 32 ) ;
    olcellval1 = currec.lst [ cell1 ] ; 
    cell2 = quad2 / 32 ;
    bit2 = 1 << ( quad2 % 32 ) ;
    olcellval2 = currec.lst [ cell2 ] ;
    if ( ! ( olcellval1 & bit1 ) ) {
        if ( const_search && ( const_list [ cell1 ] & bit1 ) == 0 ) return ; 
        currec.lst [ cell1 ] |= bit1 ;
        currec.size = ++ cursize ;
        some_add = 1 ; }
    else {
        if ( ( olcellval2 & bit2 ) && cursize < 4 ) return ; 
        currec.lst [ cell1 ] &= ~ bit1 ;
        currec.size = -- cursize ; } 
    if ( ! ( olcellval2 & bit2 ) ) {
        if ( const_search && ( const_list [ cell2 ] & bit2 ) == 0 ) {
            currec.lst [ cell1 ] = olcellval1 ;
            currec.size = cursize = olsz ;  
            return ; } 
        currec.lst [ cell2 ] |= bit2 ;
        currec.size = ++ cursize ;
        some_add = 1 ; }
    else {
        currec.lst [ cell2 ] &= ~ bit2 ;
        currec.size = -- cursize ; } 
    if ( isduparea ( &currec , 0 ) ) {
           cursize = olsz ;
           currec.lst [ cell1 ] = olcellval1 ; 
           currec.lst [ cell2 ] = olcellval2 ; 
           return ; }
    if ( some_add ) 
          for ( a = spcells ; a -- ; ) curinters [ cursize ] [ a ] = bigarset [ a ] ;
    else for ( a = spcells ; a -- ; ) curinters [ cursize ] [ a ] = smallarset [ a ] ;
    prepare_all_lists () ;
    arsexd ++ ; 
    val = do_evaluation () ; 
    if ( use_wide_init && val < minrealscore ) val = -1 ; 
    if ( val >= curscore * slopeval ) {
        currec.score5 = val ; 
        currec.numspp = scoring_spp ; 
        storar ( ) ;  
        if ( ! new_is_superfluous () )
                 havcomb [ key_combination ] ++ ; 
        if ( val > bestscore ) bestscore = val ; } 
    cursize = olsz ;
    currec.lst [ cell1 ] = olcellval1 ;
    currec.lst [ cell2 ] = olcellval2 ;
    return ; 
}     

/******
void retouch_double_cell ( Artyp * recrd )
{
    int a , quad1 , quad2 , arcell , x , y , j ;
    int32 arbit ; 
    int * nex , * nexnex ; 
    recrd -> swapd = 1 ; 
    if ( recrd -> size < 2 ) return ; 
    for ( a = arcells ; a -- ; ) currec.lst [ a ] = recrd -> lst [ a ] ;
    cursize = currec.size = recrd -> size ;
    curscore = recrd -> score5 ; 
    prepare_edgelist () ;
    reset_swapping = 0 ; 
    for ( nex = listedge ; nex < listedgept && !reset_swapping ; ++ nex ) {
        chkbyebye () ;
        quad1 = * nex ; 
        arcell = quad1 / 32 ;
        arbit = 1 << ( quad1 % 32 ) ; 
        if ( ( currec.lst [ arcell ] & arbit ) ) wipe_quad ( quad1 ) ;
        else add_quad ( quad1 ) ;
        for ( nexnex = nex + 1 ; nexnex < listedgept && !reset_swapping ; ++ nexnex ) {
            quad2 = * nexnex ;
            change_2_quads ( quad1 , quad2 ) ; }}
    return ; 
} *******/


void retouch_double_cell ( Artyp * recrd )
{
    int a , quad1 , quad2 , arcell , x , y , j ;
    int32 arbit ;
    int innow, outnow , lissize ; 
    int * nex , * nexnex ; 
    recrd -> swapd = 1 ; 
    if ( recrd -> size < 2 ) return ; 
    for ( a = arcells ; a -- ; ) currec.lst [ a ] = recrd -> lst [ a ] ;
    cursize = currec.size = recrd -> size ;
    curscore = recrd -> score5 ; 
    prepare_edgelist () ;
    reset_swapping = 0 ;
    lissize = listedgept - listedge ;
    randomlist ( lissize , ranswaplist ) ; 
    for ( outnow = 0 ; outnow < lissize && !reset_swapping ; ++ outnow ) {
        chkbyebye () ;
        quad1 = listedge [ ranswaplist [ outnow ] ] ; 
        arcell = quad1 / 32 ;
        arbit = 1 << ( quad1 % 32 ) ; 
        if ( ( currec.lst [ arcell ] & arbit ) ) wipe_quad ( quad1 ) ;
        else add_quad ( quad1 ) ;
        for ( innow = outnow + 1 ; innow < lissize && !reset_swapping ; ++ innow ) {
            quad2 = listedge [ ranswaplist [ innow ] ] ;
            change_2_quads ( quad1 , quad2 ) ; }}
    return ; 
} 


void read_areas ( void )
{
   int a , b ;
   int numrecs = 0 ;
   bestscore = 0 ; 
   bread_file = startfile ; 
   // bread ( sizeof ( int ) , 1 , ( char * ) &a ) ;
   fprintf ( stderr , "\nReading starting sets..." ) ;
   while ( 1 ) {
     a = 0 ; 
     a += bread ( sizeof ( int32 ) , arcells , ( char * ) currec.lst ) ; 
     a += bread ( sizeof ( double ) , 1 , ( char * ) &( currec.score5 ) ) ; 
     a += bread ( sizeof ( int ) , 1 , ( char * ) &( currec.size ) ) ;
     if ( !a ) break ; 
     smallest_cell = minframey = minframex = 0 ;
     largest_cell = totareas ;
     maxframey = rows ; 
     maxframex = cols ; 
     for ( a = arcells ; a -- ; ) farar [ a ] = 0 ; 
     if ( !isduparea ( &currec , 0 ) ) {
        cursize = currec.size ; 
        prepare_all_lists () ;
        for ( a = 0 ; a < spcells ; ++ a ) curinters [ cursize ] [ a ] = ~0 ; 
        ++ arsexd ;
        currec.score5 = dorule5 ( 0 ) ;
        if ( currec.score5 > bestscore ) bestscore = currec.score5 ;
        curinters [ cursize ] [ spcells - 1 ] &= last_sp_filter ; 
        if ( currec.score5 < 0 ) currec.score5 = -currec.score5 ;
        currec.numspp = scoring_spp ; 
        storar ( ) ;
        havcomb [ key_combination ] ++ ; }
     if ( feof ( startfile ) ) break ;
     else {
        if ( numrecs == maxrec ) {
           fprintf ( stderr , "\nCan't read more than %i records\n" , maxrec ) ;
           getch () ; 
           exit ( 0 ) ; }}}
   if ( recptr == rec ) {
       fprintf ( stderr , "\nNo areas in file.  Can't start swapping.\n" ) ;
       getch () ;
       exit ( 0 ) ; }    
   numrecs = recptr - rec ;
   fprintf( stderr , "\rRead %i sets (used to start search)\n" , numrecs ) ;
   fclose ( startfile ) ; 
}    

       
void heuristics ( void )
{
    int a , b , c ;
    int32 x ;
    int speed , timediff ;
    last_sp_filter = 0 ;
    x = spp % 32 ;
    if ( x ) 
      while ( x < 32 ) {
        last_sp_filter |= ( 1 << x ) ;
        x ++ ; }
    last_sp_filter = ~last_sp_filter ;
    init_search = last = clock () ; 
    init_combs () ;
    fill_distributions () ; 
    if ( startfile == NULL ) {
       fprintf ( stderr , "\nInitializing areas... " ) ;
       if ( !randomize_startpoint ) 
          for ( a = 0 ; a < spp ; a ++ ) {
             fprintf ( stderr , "%3i%%\b\b\b\b" , ( a * 100 ) / spp ) ; 
             spinitar ( a ) ; }
       else {
           for ( a = 0 ; a < spp ; ++ a ) daspranlist [ a ] = a ;
           for ( a = 0 ; a < spp ; ++ a ) {
               c = rand () % spp ;
               b = daspranlist [ c ] ;
               daspranlist [ c ] = daspranlist [ a ] ;
               daspranlist [ a ] = b ; }
            for ( a = 0 ; a < spp ; a ++ ) {
               fprintf ( stderr , "%3i%%\b\b\b\b" , ( a * 100 ) / spp ) ; 
               spinitar ( daspranlist [ a ] ) ; }}
       recinit = recptr - rec ;
       if ( const_search && !recinit ) 
           fprintf ( stderr , "\rNo species distribution matches constrain area!   \n" ) ; 
       fprintf ( stderr , "\rInitialized search with %i areas...\nSearching" , recinit ) ; }
    else {
        read_areas () ;
        recinit = recptr - rec ; }
    if ( cells_to_swap == 2 ) fprintf ( stderr , " (double swapping)" ) ; 
    if ( startfile == NULL ) fprintf ( stderr , ":" ) ;
    fprintf ( stderr , "\n   swap  stored    best   checked  speed(a/s)\n" ) ; 
    a = 0 ;
    for ( swaprec = rec ; swaprec < recptr ; ++ swaprec ) {
        if ( swaprec -> erase ) continue ;  
        ++ a ; 
        if ( a == 13 || cells_to_swap > 1 ) {
            timediff = ( ( ( now = clock () ) - last ) / CLOCK_TICKS ) ;
            a = 0 ; 
            if ( timediff ) {
                last = now ;
                speed = arsexd / ( ( now - init_search ) / CLOCK_TICKS ) ; 
                fprintf ( stderr , "  %5i  %6i %7.3f %9i %6i\r" ,  
                          swaprec - rec , recptr - rec , bestscore , arsexd , speed ) ; }} 
        if ( cells_to_swap == 1 ) retouch_single_cell ( swaprec ) ;
        else retouch_double_cell ( swaprec ) ; 
#ifdef LINUX 
        if ( swaprec > rec && running_in_background && ( ( ( swaprec - rec ) % 100 ) == 0 || swaprec == recptr - 1 ) ) 
          if ( swaprec == recptr - 1 ) 
            fprintf ( bgroundfile , "Swapped %6i (done)\n" , swaprec - rec ) ; 
          else 
            fprintf ( bgroundfile , "Swapped %6i (%i to go)\n" , swaprec - rec , recptr - swaprec - 1 ) ; 
#endif
    }
   timediff = ( ( ( now = clock () ) - init_search ) / CLOCK_TICKS ) ;
   if ( timediff )
         speed = arsexd / ( ( now - init_search ) / CLOCK_TICKS ) ;
   else speed = 0 ;
   if ( speed ) fprintf ( stderr , "  %5i  %6i %7.3f %9i %6i\r" , swaprec - rec , recptr - rec , bestscore , arsexd , speed ) ;  
   else fprintf ( stderr , "  %5i  %6i %7.3f %9i   ????\r" , swaprec - rec , recptr - rec , bestscore , arsexd ) ;  
   if ( !saveall ) show_time () ; 
   return ; 
}     

/**********  TMING FUNCTIONS  ***************/

void init_time ( void )
{ 
#ifdef LINUX
   time ( &linux_init ) ; 
   begin = clock () ;
#else
   begin = clock () ;
#endif
   return ; 
}

void show_time ( void )
{
#ifdef LINUX
   time ( &linux_end ) ; 
   fprintf ( stderr,"\n%.0f secs.\n" , ( float ) difftime ( linux_end, linux_init )) ;       
#else
   fprintf ( stderr,"\n%.2f secs.\n" , ( float ) ( clock () - begin ) / CLOCK_TICKS ) ;       
#endif
   return ;
}   


/********** READ AND HANDLE LIST OF CONSTRAINTS **************/
/*         Areas examined must be a subset of this           */
/*         The file with constraints is a binary file,       */
/*         which must have been created with VNDM            */

FILE * const_file = NULL ; 

void eliminate_outsiders ( void )  
{   // gets rid of species found outside constrain area (cannot give score)
    int x , y ;
    int a , b , cell , scell ;
    int32 bit , sbit ; 
    int32 * inpt = curinters [ 0 ] ; 
    for ( a = arcells ; a -- ; ) currec.lst[a] = const_list [ a ] ; 
    listoutpt = listout ;
    for ( a = 0 ; a < totareas ; ++ a ) {
        y = a / cols ;
        x = a % cols ; 
        if ( !isdefd [ y ] [ x ] ) continue ;
        cell = a / 32 ; 
        bit = 1 << ( a % 32 ) ; 
        if ( ( currec.lst[cell] & bit ) ) continue ; 
        if ( !iscontig ( a ) ) * listoutpt ++ = a ; } 
    while ( listoutpt > listout ) {
        a = * -- listoutpt ;
        y = a / cols ;
        x = a % cols ; 
        for ( b = spp ; b -- ; ) {
            scell = b / 32 ;
            sbit = 1 << ( b % 32 ) ;
            if ( ( matrix [ y ] [ x ] [ scell ] & sbit ) != 0 )
                     inpt [ scell ] &= ~ sbit ; }}
    for ( a = arcells ; a -- ; ) currec.lst[a] = 0 ; 
    return ; 
}             


void set_const ( char * fnam )
{
    const_file = fopen ( fnam , "rb" ) ;
    const_search = 1 ; 
    return ; 
}     


int bread ( int bys , int num , char * ptr ) 
{ int a = num * bys , x ;
  x = getc ( bread_file ) ; 
  if ( feof ( bread_file ) ) return 0 ;  
  ungetc ( x , bread_file ) ; 
  while ( a -- ) 
         * ptr ++ = getc ( bread_file ) ; 
  if ( feof ( bread_file ) ) { 
       if ( bread_file == const_file ) errout ( "Couldn't read constraints (unexpected EOF)") ; 
       else errout ( "Couldn't read starting areas (unexpected EOF)") ; 
       exit ( 0 ) ; } 
  return 1 ; 
} 
    
void read_constraints ( void )
{
    int a , b , z ;
    int const_sz = 0 ; 
    int32 x ; 
    if ( !const_search ) return ;
    bread_file = const_file ; 
    // bread ( sizeof ( int ) , 1 , ( char * ) &a ) ;
    // if ( a != 1 ) errout ( "Error reading constrain file.  File must contain ONE record" ) ; 
    const_list = mymem ( sizeof ( int32 ) * arcells ) ; 
    bread ( sizeof ( int32 ) , arcells , ( char * ) const_list ) ;
    for ( a = arcells ; a -- ; )
             const_sz += onbits ( const_list [ a ] ) ; 
    if ( const_sz < maxsize ) maxsize = const_sz ; 
    last_const_cell = 0 ; 
    for ( a = arcells ; a -- && last_const_cell == 0 ; ) {
        if ( const_list [ a ] ) {
               x = ( 1 << 31 ) ;
               z = 31 ;
               while ( !( const_list [ a ] & x ) ) {
                   x >>= 1 ;
                   z -- ; } 
               last_const_cell = a ;
               last_const_bit = 1 << z ; }}
    fprintf ( stderr , "\nRead constraints from file...\n" ) ; 
    return ; 
}     

/***************  LOGGING RESULTS TO FILE ****************/
/*     The resulting file will be readable by VNDM       */ 

int written = 0 ; 

void bsav ( int bys , int num , char * ptr ) 
{ int a = num * bys;
  written += a ; 
  while ( a -- ) putc ( * ptr ++ , logfile ) ; 
  return ; 
} 

char * logfilename ;

void logtofile ( void ) 
{ 
   int a , b , c ;
   if ( logfile == NULL ) return ;
   if ( also_save_data ) { 
      bsav ( sizeof ( int ) , 1 , ( char * ) &abslim ) ; 
      bsav ( sizeof ( int ) , 1 , ( char * ) &musthaveone ) ;
      a = use_edge_props ;
      if ( spname != NULL ) a |= 2 ; 
      bsav ( sizeof ( int ) , 1 , ( char * ) &a ) ; 
      bsav ( sizeof ( double ) , 1 , ( char * ) &ifac ) ; 
      bsav ( sizeof ( double ) , 1 , ( char * ) &afac ) ; 
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
      a = b = recptr - rec ; 
      bsav ( sizeof ( int ) , 1 , ( char * ) &a ) ; }

   a = b = recptr - rec ;       
   while ( a -- ) { 
           -- recptr ; 
           bsav ( sizeof ( int32 ) , arcells , ( char * ) recptr -> lst ) ; 
           bsav ( sizeof ( double ) , 1 , ( char * ) &( recptr -> score5 ) ) ; 
           bsav ( sizeof ( int ) , 1 , ( char * ) &( recptr -> size ) ) ; } 
   if ( output == stdout ) fprintf ( stderr,"\nResults (%i areas) saved to file %s (%i bytes)\n", b , logfilename , written ) ; 
   else fprintf ( stderr,"\nResults (%i areas) saved also to file %s\n", b , logfilename ) ;
   if ( overflow_warn )
       fprintf ( stderr , "\nWARNING:\n  buffer for areas overflowed during search;\n  this can cause erroneous results.\n  If possible, reset -n and retry.\n\n" ) ; 
   return ; 
} 

/**************** SAVING RESULTS TO OUTPUT FILE *******************/
/*       This outputs the results in a more graphical format.     */
/*       Given the existence of VNDM, this is rarely used.        */

void drawset ( Artyp * gp ) 
{ int a , b , numar , mc ; 
  int32 mb ; 
  if ( output == stdout ) { 
        chkfreq = 0 ; 
        chkbyebye () ; } 
  fprintf ( output , "\nSize: %i.  Score: %f." , 
            gp->size , gp->score5 ) ; 
  for ( a = 0 ; a < rows ; ++ a ) { 
        fprintf ( output,"\n" ) ; 
        for ( b = 0 ; b < cols ; ++ b ) { 
              numar = ( cols * a ) + b ; 
              if ( !isdefd[a][b] ) { fprintf ( output," " ) ; continue ; } 
              mb = 1 << ( numar % 32 ) ; 
              mc = numar / 32 ; 
              if ( ( gp->lst[mc] & mb ) ) 
                   fprintf ( output , "Û" ) ; 
              else fprintf ( output , "°" ) ; }}
  fprintf ( output, "\n" ) ; 
} 

void showall ( void ) 
{ Artyp * rc = rec ;
  if ( logfile != NULL && output == stdout ) return ; 
  if ( rc == recptr ) 
      fprintf ( output , "\nNo areas to show.\n" ) ;
  while ( rc < recptr ) drawset ( rc ++ ) ;
  if ( output != stdout ) fprintf ( stderr,"\n%i sets written to outfile\n" , recptr - rec ) ; 
  if ( overflow_warn )
       fprintf ( output , "\nWARNING:\n  buffer for areas overflowed during search;\n  this can cause erroneous results\n  If possible, reset -n and retry.\n\n" ) ; 

} 

void readableout( void ) 
{ 
   int a , b , c ;
   double score;
   if ( logfile == NULL ) return ;
   if ( also_save_data ) {
           fprintf (stdout, "abslim %d\n", abslim);
           fprintf (stdout, "musthaveone %d\n", musthaveone);
           fprintf (stdout, "use_edge_props %d\n", use_edge_props );
           fprintf (stdout, "ifac %f\n", ifac );
           fprintf (stdout, "afac %g\n", afac );
           fprintf (stdout, "outfac %f\n", oufac );
           fprintf (stdout, "oafac %f\n", oafac );
           fprintf (stdout, "ononafac %f\n", ononafac );
           fprintf (stdout, "min_pres_perc %d\n", min_pres_perc );
           fprintf (stdout, "compare_perc %d\n", compare_perc );
           fprintf (stdout, "rows %d\n", rows );
           fprintf (stdout, "cols %d\n", cols );
           fprintf (stdout, "spp %d\n", spp );

           if ( spname != NULL ) 
          for ( a = 0 ; a < spp ; ++ a )
                          fprintf (stdout, "Spnamesz: %s\n", spname[a] ) ; 

           fprintf (stdout, "grid_starty %d\n", grid_starty );
           fprintf (stdout, "grid_startx %d\n", grid_startx );
           fprintf (stdout, "grid_height %d\n", grid_height );
           fprintf (stdout, "grid_width %d\n", grid_width );
//         fprintf (stdout, "numentries %d\n", numentries );
//         fprintf (stdout, "numassentries %d\n", numassentries );

        }
        a = b = recptr - rec ; 
        while ( a -- ) {
                -- recptr ;
                fprintf (stdout, "record: %d\n", a );
                fprintf ( stdout, "lst: " );
                for ( c = 0 ; c < arcells ; ++ c )
                   fprintf ( stdout , "%u, " , recptr -> lst[c] );
                fprintf ( stdout, "\nscore: %f\n", recptr -> score5 );
                fprintf ( stdout, "size: %d\n", recptr -> size );
                smallest_cell = minframey = minframex = 0 ;
                largest_cell = totareas ;
                maxframey = rows ; 
                maxframex = cols ; 
                copyar ( &currec, recptr ) ;
                for ( b = arcells ; b -- ; ) farar [ b ] = 0 ; 
                //if ( !isduparea ( &currec , 0 ) ) {
                        cursize = currec.size ; 
                        prepare_all_lists () ;
                        for ( b = 0 ; b < spcells ; ++ b ) curinters [ cursize ] [ b ] = ~0 ; 
                        ++ arsexd ;
                        score = dorule5 ( 0 ) ;
                        //curinters [ cursize ] [ spcells - 1 ] &= last_sp_filter ; 
                        if ( score < 0 ) score = -score;
                        if ( score != currec.score5 ){
                                fprintf (stdout, "Warning.  Scores don't match! now is %.7f\n" , score );
                        }
                //}
        }
        getch () ; 
        return ;
} 


void save_results ( void )
{
   Artyp * recwas = recptr ;
   FILE * writeto = stderr ;
#ifdef LINUX 
   if ( running_in_background ) writeto = bgroundfile ; 
#endif   
   if ( !do_exact_search ) {
       if ( previous_cleanup ) fprintf ( writeto , "\nWarning: overflowed area buffer (%i times) during search\n(this decreases effectiveness of search)\n\n" , num_buffer_cleans ) ;
       fprintf ( writeto , "\n%i areas examined (plus %i duplicate areas)\n" , arsexd , dups_found ) ; } 
   showall () ;  
   logtofile () ;
   //recptr = recwas ; 
   //readableout () ;
   return ; 
}

/*************** BASIC CALCULATIONS ***********************/
/*     Support functions used during calculations         */
/*     and when cleaning sets of areas                    */

int islone ( int x , int y ) 
{   int32 mb , mc ; 
    int a , b , numar ; 
    for ( a = x - 1 ; a <= x + 1 ; ++ a ) { 
         if ( a < 0 || a >= cols ) continue ; 
         for ( b = y - 1 ; b <= y + 1 ; ++ b ) { 
             if ( b < 0 || b >= rows ) continue ; 
             if ( b == y && a == x ) continue ; 
             numar = ( cols * b ) + a ; 
             mb = 1 << ( numar % 32 ) ; 
             mc = numar / 32 ; 
             if ( ( currec.lst[mc] & mb ) != 0 ) 
                  return 0 ; }} 
    return 1 ; 
} 

int isinedge ( int j ) 
{   int32 mb , mc ; 
    int a , b , numar , x , y ; 
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
             if ( ( currec.lst[mc] & mb ) == 0 ) return 1 ; }} 
    return 0 ; 
} 

int iscontig ( int j ) 
{   int32 mb , mc ; 
    int a , b , numar , x , y ; 
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
             if ( ( currec.lst[mc] & mb ) != 0 ) return 1 ; }} 
    return 0 ; 
} 

int nubi , num , depth ; 

void calculin( void )   // this initializes the array numbits, for quick bit counting
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

int onbits ( int32 val ) 
{ unsigned short int * x , * y ; 
  x = ( unsigned short int * ) &val ; 
  y = x + 1 ; 
  return ( numbits [ * x ] + numbits [ * y ] ) ; 
}

int oneintwo ( Artyp * ara , Artyp * arb ) // is A inside B?
{  int32 * ca , * cb ; 
   int disj , anonb , bnona ; 
   int j , from , to ; 
   if ( ara->size == arb->size ) return 0 ; // assumes areas can't be equal!
   if ( ara -> hicell < arb -> locell || ara -> locell > arb -> hicell ) return 0 ;  // areas are disjunct!
   from = ( ara -> locell < arb -> locell ) ?  ara -> locell : arb -> locell ;
   to = ( ara -> hicell > arb -> hicell ) ?  ara -> hicell : arb -> hicell ;
   from = from / 2 ;
   to = 1 + ( to / 2 ) ; 
   ca = ara->lst + from ; 
   cb = arb->lst + from ; 
   disj = 1 ; 
   anonb = bnona = 0 ; 
   for ( j = ( to - from ) ; j -- ; ) { 
       if ( * ca & * cb ) disj = 0 ; 
       if ( * ca & ~ * cb ) anonb = 1 ; 
       if ( * cb & ~ * ca ) bnona = 1 ; 
       if ( !disj && anonb && bnona ) break ; 
       ++ ca ; ++ cb ; } 
   if ( !disj ) {
       if ( anonb && bnona ) return 2 ;          //  2 = contradictory
       if ( bnona && !anonb ) return 1 ;         //  1 = first is contained within second
       if ( anonb && !bnona ) return -1 ; }      // -1 = first contains second
   return 0 ;                                    //  0 = disjunct 
} 

int iscontra ( Artyp * ara , Artyp * arb ) 
{  int32 * ca , * cb ; 
   int disj , anonb , bnona ; 
   int j , from , to ;
   if ( ara -> hicell < arb -> locell || ara -> locell > arb -> hicell ) return 0 ;  // disjunct
   from = ( ara -> locell < arb -> locell ) ?
            ara -> locell : arb -> locell ;
   to = ( ara -> hicell > arb -> hicell ) ?
            ara -> hicell : arb -> hicell ;
   from = from / 2 ;
   to = 1 + ( to / 2 ) ; 
   ca = ara->lst + from ; 
   cb = arb->lst + from ; 
   disj = 1 ; 
   anonb = bnona = 0 ; 
   for ( j = ( to - from ) ; j -- ; ) { 
       if ( * ca & * cb ) disj = 0 ; 
       if ( * ca & ~ * cb ) anonb = 1 ; 
       if ( * cb & ~ * ca ) bnona = 1 ; 
       if ( !disj && anonb && bnona ) break ; 
       ++ ca ; ++ cb ; } 
   if ( !disj && anonb && bnona ) return 1 ; 
   return 0 ; 
} 

void copyar ( Artyp * ara , Artyp * arb ) 
{  int32 * pta , * ptb ; 
   int a ; 
   pta = ara -> lst ;  
   ptb = arb -> lst ; 
   for ( a = arcells ; a -- ; ) * pta ++ = * ptb ++ ;
   pta = ara -> splist ;  
   ptb = arb -> splist ; 
   for ( a = spcells ; a -- ; ) * pta ++ = * ptb ++ ; 
   ara -> score5 = arb -> score5 ; 
   ara -> size = arb -> size ; 
   ara -> erase = arb -> erase ;
   ara -> numspp = arb -> numspp ;
   ara -> swapd = arb -> swapd ;

   ara -> hicell = arb -> hicell ;
   ara -> locell = arb -> locell ;
   ara -> key = arb -> key ; 

   return ; 
} 

int one_vs_other ( Artyp * nu , Artyp * ara )
{
    int nuisbest = 0 , araisbest = 0 ;
    int a ;
    int nunotra , ranotnu , nura ; 
    int32 x , * ptnu , * ptra ; 
    if ( ara -> score5 < ( nu -> score5 + suboptimal ) ) nuisbest = 1 ; 
    if ( nu -> score5 < ( ara -> score5 + suboptimal ) ) araisbest = 1 ;
    nunotra = ranotnu = nura = 0 ;
    if ( nuisbest ) { 
        ptnu = nu->splist - 1 ;
        ptra = ara->splist - 1 ; 
        for ( a = spcells ; a -- ; ) {
            ++ ptnu ;
            ++ ptra ;
            if ( * ptra ) {
                x = * ptra & ~ * ptnu ; 
                if ( x ) ranotnu += onbits ( x ) ;
                if ( * ptnu ) {
                    x = * ptra & * ptnu ;
                    if ( x ) nura += onbits ( x ) ; }}}
        if ( ranotnu + nura == 0 ) return 1 ;  
        if ( ( ranotnu * 100 ) / ( ranotnu + nura ) <= compare_perc ) return 1 ; } 
    if ( araisbest ) {
        ptnu = nu->splist - 1 ;
        ptra = ara->splist - 1 ; 
        for ( a = spcells ; a -- ; ) {
            ++ ptnu ;
            ++ ptra ;
            if ( * ptnu ) {
                x = * ptnu & ~ * ptra ;
                if ( x ) nunotra += onbits ( x ) ;
                if ( * ptra ) {
                    x = * ptra & * ptnu ;
                    if ( x ) nura += onbits ( x ) ; }}}
        if ( nunotra + nura == 0 ) return -1 ;  
        if ( ( nunotra * 100 ) / ( nunotra + nura ) <= compare_perc ) return -1 ; } 
    return 0 ;
} 


void delete_marks ( int val )
{
   Artyp * ara , * arf ;
   int fly ;  
   ara = rec - 1 ; 
   while ( ++ ara < recptr )
               if ( ara -> erase == val ) {
                      -- havcomb [ ara -> key ] ; 
                      ara -> erase = 1 ; } 
               else ara -> erase = 0 ; 
   fly = 0 ;
   ara = rec - 1 ; 
   while ( ++ ara < recptr )  
      if ( ara -> erase ) { 
            if ( ara -> erase == 1 ) fly ++ ;  
            arf = ara + 1 ; 
            while ( arf -> erase && arf < recptr ) ++ arf ; 
            if ( arf < recptr ) { 
                   copyar ( ara , arf ) ; 
                   arf -> erase = 2 ; }}
   recptr -= fly ;
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
    if ( arsmall->score5 >= ( arbig->score5 + suboptimal ) ) {  
        for ( a = spcells ; a -- ; ) {
           ++ ptsmall ;
           ++ ptbig ;
           if ( * ptbig ) {
               x = * ptsmall & * ptbig ;
               if ( x ) biandsm += onbits ( x ) ;
               x = * ptbig & ~ * ptsmall ; 
               if ( x ) binotsm += onbits ( x ) ; }}
        if ( binotsm + biandsm == 0 ) arbig->erase = 1 ;
        else 
        if ( ( ( binotsm * 100 ) / ( binotsm + biandsm ) ) <= compare_perc )          
             arbig->erase = 1 ; } 
    if ( arbig->score5 >= ( arsmall->score5 + suboptimal ) ) { 
        ptsmall = arsmall->splist - 1 ;
        ptbig = arbig->splist - 1 ;
        for ( a = spcells ; a -- ; ) {
           ++ ptsmall ;
           ++ ptbig ;
           if ( * ptsmall & ~ * ptbig ) { smnotbi = 1 ; break ; }}
        if ( !smnotbi ) arsmall->erase = 1 ; } 
    return ; 
}         


void clean_areas ( int speak , int erase_init_areas )
{
  Artyp * ara , * nu , * arf ;
  Artyp * mxrec = rec ; 
  int keepit = 0 , a ;
  int this_perc , last_perc = -1 ; 
  int dumpit ; 
  int fly , numrecs = recptr - rec ;
  int atstep = 1 ; 
  if ( saveall ) return ;
  if ( speak ) fprintf ( stderr , "\n\n" ) ;
  if ( erase_init_areas && !do_exact_search && startfile == NULL ) { 
     for ( ara = rec ; ara < recptr ; ++ ara ) {
        ara -> erase = 0 ;
        if ( ara -> score5 < minrealscore ||
             ara -> numspp < minscore )  
             ara -> erase = 1 ; }
     delete_marks ( 1 ) ; } 
  while ( mxrec != recptr ) {
     mxrec = recptr ; 
     if ( speak ) fprintf ( stderr , "\rPurifying %5i areas (step %2i)... " , recptr - rec , atstep ++ ) ;  
     for ( nu = rec ; nu < recptr ; ++ nu ) nu -> erase = 0 ;
     for ( nu = rec ; nu < recptr ; ++ nu ) { 
         chkbyebye () ; 
         if ( speak ) {
             this_perc = ( ( nu - rec ) * 100 ) / ( 2 * ( recptr - rec ) ) ;
             if ( this_perc != last_perc ) {
                 last_perc = this_perc ; 
                 fprintf ( stderr , "%3i%%\b\b\b\b" , this_perc ) ; }}
         ara = nu ; 
         while ( ++ ara < recptr ) {
           if ( ara -> erase && nu -> erase ) continue ; 
           if ( iscontra ( ara , nu ) ) {
             dumpit = one_vs_other ( nu , ara ) ;
             if ( dumpit == 1 ) ara -> erase = 1 ;
             if ( dumpit == -1 ) nu -> erase = 1 ; }}}
     for ( nu = rec ; nu < recptr ; ++ nu ) { 
         chkbyebye () ; 
         if ( speak ) {
             this_perc = 50 + ( ( ( nu - rec ) * 100 ) / ( 2 * ( recptr - rec ) ) ) ;
             if ( this_perc != last_perc ) {
                 last_perc = this_perc ; 
                 fprintf ( stderr , "%3i%%\b\b\b\b" , this_perc ) ; }}
         ara = nu ; 
         while ( ++ ara < recptr ) {
             if ( !ara -> erase && !nu -> erase ) continue ;
             if ( ara -> erase && nu -> erase ) continue ; 
             if ( iscontra ( ara , nu ) ) {
                 dumpit = one_vs_other ( nu , ara ) ;
                 if ( dumpit == 1 ) ara -> erase = 2 ;
                 if ( dumpit == -1 ) nu -> erase = 2 ; }}}
      delete_marks ( 2 ) ;  
      /****  Get rid of superfluous sets ***/
      for ( nu = rec ; nu < recptr ; ++ nu ) nu -> erase = 0 ;
      for ( nu = rec ; nu < recptr ; ++ nu ) { 
         chkbyebye () ; 
         ara = nu ; 
         while ( ++ ara < recptr ) {
            if ( ara -> erase || nu -> erase ) continue ; 
            a = oneintwo ( ara , nu ) ;
            if ( a == 1 ) // i.e. ara is inside nu
                chk_superfluous ( ara , nu ) ;  
            if ( a == -1 ) //i.e. nu is inside ara
                chk_superfluous ( nu , ara ) ; }}
      delete_marks ( 1 ) ; } 
   if ( speak ) fprintf ( stderr , "     \r                                         \r" ) ; 
   return ; 
}


/************  ENLARGING DISTRIBUTIONS OF EACH SPECIES **************/
/*        This is done to check whether the number of members       */
/*        in the intersection of species in each cell added so      */
/*        far to the area is less than minscore.                    */
/*        If fill_abslim < 7 , the results may have errors          */

void fill_distributions ( void ) 
{ 
    int32 mb , kb ; 
    int mc , a , b , c , empys , atleastone ; 
    int j , k , l , jx , jy ; 
    int kc , numar , countit , added_some ;
    mc = 0 ; 
    mb = 1 ; 
    for ( a = 0 ; a < spp ; ++ a ) { 
        for ( b = arcells ; b -- ; ) tmplist [ b ] = 0 ; 
        added_some = 0 ; 
        for ( j = totareas ; j -- ; ) { 
          jx = j % cols ; 
          jy = j / cols ; 
          if ( ( fake_matrix [ jy ] [ jx ] [ mc ] & mb ) != 0 ) continue ; 
          if ( ( assmatrix [ jy ] [ jx ] [ mc ] & mb ) != 0 ) {
                   added_some = 1 ; 
                   tmplist [ j / 32 ] |= 1 << ( j % 32 ) ;
                   continue ; }
          if ( !isdefd [ jy ] [ jx] ) continue ; 
          empys = atleastone = 0 ; 
          if ( !musthaveone ) atleastone = 1 ; 
          countit = 1 ; 
          for ( k = jx - 1 ; k <= jx + 1 ; ++ k ) {  
              if ( k < 0 || k >= cols ) continue ; 
              for ( l = jy - 1 ; l <= jy + 1 ; ++ l ) { 
                   if ( l < 0 || l >= rows ) continue ; 
                   if ( !isdefd [ l ] [ k ] ) continue ; 
                   numar = ( cols * l ) + k ;
                   if ( numar == j ) continue ; 
                   kb = 1 << ( numar % 32 ) ; 
                   kc = numar / 32 ; 
                   if ( ( fake_matrix [ l ] [ k ] [ mc ] & mb ) == 0 ) 
                             ++ empys ; 
                   else atleastone = 1 ; }}
          if ( empys > fill_abslim ) continue ; 
          if ( !atleastone ) continue ; 
          added_some = 1 ; 
          tmplist [ j / 32 ] |= 1 << ( j % 32 ) ; }
        //  FILL IT IN !!
        if ( added_some ) 
         for ( k = rows ; k -- ; ) 
            for ( l = cols ; l -- ; ) { 
               numar = ( cols * k ) + l ; 
               kb = 1 << ( numar % 32 ) ; 
               kc = numar / 32 ; 
               if ( ( tmplist [ kc ] & kb ) ) { 
                       fake_matrix [ k ] [ l ] [ mc ] |= mb ; 
                       ++ fake_numentries [ a ] ; }} 
        if ( mb == BIT32 ) { mb = 1 ; ++ mc ; } 
        else mb <<= 1 ; } 
    return ; 
} 


/*********** USER BREAKS **************/
/*                                    */

#ifdef LINUX

int fhandle ; 
char bf [ 1 ] = { 0 } ; 

int kbhit ( void ) 
{ 
  static int prepared = 0 ; 
  int flg , nv ; 
  if ( running_in_background ) return 0 ; 
  if ( !prepared ) { 
      fhandle = fileno ( stdin ) ; 
      flg = fcntl ( fhandle , F_GETFL , 0 ) ; 
      flg |=  O_NONBLOCK ; 
      fcntl ( fhandle , F_SETFL , flg ) ; 
      prepared = 1 ; }
  nv = read ( fhandle , bf , 1 ) ; 
  if ( nv < 0 ) return 0 ; 
  return 1 ; 
}
  
int getch ( void ) 
{ int a ; 
  if ( running_in_background ) return 10 ; 
  if ( ! bf [ 0 ] ) bf [ 0 ] = getc ( stdin ) ; 
  a = tolower ( bf [ 0 ] ) ; 
  bf [ 0 ] = 0 ; 
  return a ; 
}

#endif

void chkbyebye ( void ) 
{     int a ; 
      if ( !breakable ) return ; 
      if ( ++ numcheks < chkfreq ) return ; 
      numcheks = 0 ; 
      if ( kbhit () && getch () == 27 ) { 
         fprintf ( stderr, "\n\nUser interrupt!                              \n") ;
         show_time () ; 
         if ( !chkfreq ) exit ( 0 ) ; 
         fprintf ( stderr,"Save current results?" ) ; 
         a = 0 ; 
         while ( a != 'y' && a != 'n' && a != 27 ) a = tolower ( getch () ) ; 
         if ( a == 'y' ) {
             clean_areas ( 1 , 1 ) ;
             save_results () ; }
         exit ( 0 ) ; } 
} 


/*************  EVALUATION OF AN AREA  ************************/
/*        functions that calculate the score (these           */
/*        need that listin and listout already contain        */
/*        a list of cells in and out)                         */

double dorule5 ( int dolists )
{
    int a , b , x , isexo , skipit ;
    int * lp ;
    int pres , out , ass , inf , outadja, outnonadja ;
    int32 mb , sb , * intpt ;
    int mc , sc , j , k , numar , jj , kk , snumar , atleastone , numemps ;
    int32 * areapt = currec.lst ;
    double Eval ; 
    double spscore , myscore = 0 , dinf , dass , dout , dpres , dsize , dadja, dnadja ;
    int * fare , * fato ;
    MinMaxtyp * mmpt ; 

#ifdef _DEBUGGING_
FILE * juju = NULL ; 
if ( areapt[0] == 216480192 && areapt[1] == 0 )  
    juju = fopen ( "talking.txt" , "w" ) ; 
#endif

    scoring_spp = 0 ;
    if ( dolists ) {
       arminc = arminr = 32767 ;
       armaxc = armaxr = 0 ; 
       listadjapt = listadja ;
       listnonadjapt = listnonadja ;
       for ( lp = listout ; lp < listoutpt ; ++ lp ) {
           x = iscontig ( a = * lp ) ; 
           if ( x < 0 ) continue ;
           if ( x ) {
                 j = a / cols ; 
                 k = a % cols ;
                 if ( arminc > k ) arminc = k ; 
                 if ( arminr > j ) arminr = j ; 
                 if ( armaxc < k ) armaxc = k ; 
                 if ( armaxr < j ) armaxr = j ; 
                 * listadjapt ++ = a ; } 
           else  * listnonadjapt ++ = a ; } 
       for ( a = totbits ; a < totareas ; ++ a ) {
             x = iscontig ( a ) ;
             if ( x < 0 ) continue ; 
             if ( x ) {
                   j = a / cols ; 
                   k = a % cols ;
                   if ( arminc > k ) arminc = k ; 
                   if ( arminr > j ) arminr = j ; 
                   if ( armaxc < k ) armaxc = k ; 
                   if ( armaxr < j ) armaxr = j ; 
                   * listadjapt ++ = a ; } 
             else  * listnonadjapt ++ = a ; }}
    Eval = ( double ) ( listadjapt - listadja ) ; 
    intpt = curinters [ cursize ] ;
    mb = 1 ;
    mc = 0 ; 
    mmpt = spminmax ; 
    for ( a = 0 ; a < spp ; ++ a , ++ mmpt ) {
        if ( species_tree != NULL ) 
             indspscore [ a ] = 0 ; 
        /****  Is species in (enlarged) intersection?  ********/
        if ( ! ( * intpt & mb ) ) {
            if ( mb == ( 1 << 31 ) ) {
                          mb = 1 ; ++ mc ; 
                          ++ intpt ; }
            else mb <<= 1 ;
            continue ; }
        if ( ( mmpt -> minc == 32767 && mmpt -> maxc == 0 )  || 
             ( mmpt -> minc < arminc ) || ( mmpt -> maxc > armaxc ) ||
             ( mmpt -> minr < arminr ) || ( mmpt -> maxr > armaxr ) ) { 
                if ( mb == ( 1 << 31 ) ) { 
                              mb = 1 ; ++ mc ;
                              ++ intpt ; }
                else mb <<= 1 ;
                continue ; }
        if ( ( mmpt -> maxc < arminc ) || ( mmpt -> minc > armaxc ) ||
             ( mmpt -> maxr < arminr ) || ( mmpt -> minr > armaxr ) ) { 
                if ( mb == ( 1 << 31 ) ) { 
                              mb = 1 ; ++ mc ;
                              ++ intpt ; }
                else mb <<= 1 ;
                continue ; }
        /***    Is species also found outside?   ********/
        isexo = outnonadja = 0 ; 
        mc = a / 32 ;     
        if ( userextass != NULL )
             outnonadja = userextass [ a ] ; 
        for ( lp = listnonadja ; lp < listnonadjapt && !isexo ; ++ lp ) {
               numar = * lp ;
               j = numar % cols ;
               k = numar / cols ; 
               if ( ( matrix [ k ] [ j ] [ mc ] & mb ) ) isexo = 1 ;
               if ( ( assmatrix [ k ] [ j ] [ mc ] & mb ) ) ++ outnonadja ; 
               } 
        if ( isexo ) {             
            * intpt &= ~mb ; 
            if ( mb == ( 1 << 31 ) ) {
                          mb = 1 ; ++ mc ; 
                          ++ intpt ; }
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
                 atleastone = 0 ;
                 if ( !musthaveone ) atleastone = 1 ; 
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
                         if ( ( matrix [ kk ] [ jj ] [ mc ] & mb ) ) atleastone = 1 ;
                         else 
                             if ( ++ numemps > abslim ) { jj = j + 1 ; break ; }}}

                if ( atleastone && numemps <= abslim &&
                     ( ifac > afac || ( assmatrix [ k ] [ j ] [ mc ] & mb ) == 0 ) )
                       ++ inf ;
                else {
                    if ( ( assmatrix [ k ] [ j ] [ mc ] & mb ) == 0 ) skipit = 1 ; 
                    else if ( musthaveone == 2 && !atleastone ) skipit = 1 ; 
                    ++ ass ;
                      }
                    }
        if ( skipit || (
             ( pres * 100 ) / cursize < min_pres_perc || 
             ( min_pres_perc && pres < 2 ) ) ) {
              * intpt &= ~mb ; 
              if ( mb == ( 1 << 31 ) ) {
                          mb = 1 ; ++ mc ; 
                          ++ intpt ; }
              else mb <<= 1 ; 
              continue ; } 
        for ( lp = listadja ; lp < listadjapt ; ++ lp ) {
                 numar = * lp ;
                 j = numar % cols ;
                 k = numar / cols ;
                 if ( ( matrix [ k ] [ j ] [ mc ] & mb ) ) ++ out ;
                 else if ( ( assmatrix [ k ] [ j ] [ mc ] & mb ) ) ++ outadja ; }
         /**** Calculating score ********/
         dout = out ;
         dass = ass ;
         dinf = inf ;
         dpres = pres ;
         dsize = cursize ;
         dadja = outadja ;
         dnadja = outnonadja ;

         if ( !use_edge_props ) 
           spscore  =
              ( dpres +
                ( ifac * dinf ) +
                ( afac * dass )  )
                                 /
              ( dsize +
                ( ( 1 / oufac ) * dout ) +
                ( ( 1 / oafac ) * dadja ) +
                ( ( 1 / ononafac ) * dnadja ) ) ;
         else {
           spscore  =
              ( ( dpres +
                ( ifac * dinf ) +
                ( afac * dass )  ) *
                ( 1 - ( ( ( dout / oufac ) + ( dadja / oafac ) ) / Eval ) ) )  
                                 /
              ( dsize + ( ( 1 / ononafac ) * dnadja ) ) ;
           if ( spscore < 0 ) spscore = 0 ; }

         if ( spscore >= minimum_sp_score ) {
              ++ scoring_spp ; 
              intersptr [ mc ] |= mb ;
              if ( !weight_species ) myscore += spscore ;
              else myscore += spscore * species_weight [ a ] ;
              if ( species_tree != NULL )
                  indspscore [ a ] = spscore ; }
         else * intpt &= ~mb ;   // unmark species as "scoring" !!
         if ( mb == ( 1 << 31 ) ) {
                          mb = 1 ; ++ mc ; 
                          ++ intpt ; }
         else mb <<= 1 ; }

    /***  If Higher Groups defined, eliminate redundant values ***********/
    if ( species_tree != NULL ) {
        intpt = curinters [ cursize ] ;
        myscore = 0 ;
        scoring_spp = 0 ; 
        for ( a = number_of_groups - 1 ; a > 0 ; a -- ) {
            j = treelist [ a ] - 1 ;
            * ( fare = fato = innerlist ) = j + 1 ;
            if ( indspscore [ j ] == 0 ) continue ; 
            ++ fare ;
            Eval = 0 ;
            while ( fato < fare ) {
                if ( ( b = * fato ++ ) >= numterminals )
                  if ( ( b == j + 1 ) || ( indspscore [ b - 1 ] == 0 ) )
                     for ( x = treefirs [ b ]  ; x >= 0 ; x = treesis [ x ] ) * fare ++ = x ;
                if ( !weight_species ) 
                    if ( b < numterminals ) 
                         Eval += indspscore [ b ] ;
                    else if ( b != j + 1 ) Eval += indspscore [ b - 1 ] ;
                else 
                    if ( b < numterminals ) 
                         Eval += indspscore [ b ] * species_weight [ b ] ;
                    else if ( b != j + 1 ) Eval += indspscore [ b - 1 ] * species_weight [ b - 1 ] ; }
            if ( indspscore [ j ] <= Eval ) indspscore [ j ] = 0 ;  
            else {
                * ( fare = fato = innerlist ) = j + 1 ;
                ++ fare ;
                while ( fato < fare ) {
                    if ( ( b = * fato ++ ) >= numterminals )
                         for ( x = treefirs [ b ]  ; x >= 0 ; x = treesis [ x ] ) * fare ++ = x ;
                    if ( b < numterminals ) indspscore [ b ] = 0 ;  
                    else if ( b != j + 1 ) indspscore [ b - 1 ] = 0 ; }}} 
         for ( a = 0 ; a < spp ; ++ a ) {
              if ( indspscore [ a ] == 0 ) 
                  intpt [ a / 32 ] &= ~ ( 1 << ( a % 32 ) ) ; 
              else {

#ifdef _DEBUGGING_
if ( juju != NULL ) fprintf ( juju , "   %i: %.6f\n" , a , indspscore[a] ) ; 
#endif
                  ++ scoring_spp ; } 
              if ( !weight_species ) 
                    myscore += indspscore [ a ] ;
              else myscore += indspscore [ a ] * species_weight [ a ] ; }}

#ifdef _DEBUGGING_
if ( juju != NULL ) fclose ( juju ) ; 
#endif

    if ( scoring_spp < minscore ) return -myscore ; 
    return myscore ;
} 


 int cycs = 0 , totdone = 0 ; 

void quepasa ( void ) 
{  int x ;
   double score5 ;
   unsigned short int * sipt ;
   int myhi , mylo ; 
   chkbyebye () ;
   score5 = dorule5 ( 1 ) ;
   if ( score5 < minrealscore ) return ; 
   if ( score5 == 0 ) return ; 
   currec.score5 = score5 ; 
   currec.erase = 0 ;
   currec.size = cursize ;
   currec.numspp = scoring_spp ; 
   // STORE IT !!!
   if( recptr-rec < maxrec ) { 
       if ( recptr->lst == NULL ) { 
            recptr->lst = ( int32 * ) mymem ( arcells * sizeof ( int32 ) ) ; 
            if ( recptr->lst == NULL ) { 
                maxrec = recptr - rec ; 
                fprintf ( stderr,"\nNot enough memory to store more than %i areas... continue checking\n" , maxrec ) ; 
                return ; }
            recptr->splist = ( int32 * ) mymem ( spcells * sizeof ( int32 ) ) ; 
            if ( recptr->splist == NULL ) { 
                maxrec = recptr - rec ; 
                fprintf ( stderr,"\nNot enough memory to store more than %i areas... continue checking\n" , maxrec ) ; 
                return ; }
            intersptr = curinters [ cursize ] ; 
            for ( x = spcells ; x -- ; )
                 currec.splist[x] = intersptr[x] ; }
       copyar ( recptr , &currec ) ; 
       sipt = ( unsigned short int * ) recptr -> lst ;
       sipt += 2 * arcells ; 
       myhi = 0 ;
       mylo = 1000000 ; 
       for ( x = 2 * arcells ; x -- ; ) {
          -- sipt ; 
          if ( * sipt && x < mylo ) mylo = x ;
          if ( * sipt && x > myhi ) myhi = x ; } 
       recptr -> hicell = myhi ;
       recptr -> locell = mylo ; 
       ++ recptr ; }
   else {
          if ( !overflow_warn ) 
             fprintf ( stderr,"\n\nOoops... partial memory buffer is full (%i tmp. areas saved)\n\n" , maxrec ) ;
          overflow_warn = 1 ;   
          clean_areas ( 0 , 0 ) ;
          if ( recptr - rec == maxrec ) {
                 fprintf ( stderr , "\nNo area can be discarded.  All areas are optimal.\n\nSave results (%i areas) to file ? (y/n) " , maxrec ) ; 
                 x = 0 ;
                 while ( x != 'y' && x != 'n' ) x = tolower ( getch () ) ;
                 if ( x == 'y' ) {
                    save_results () ;
                    show_time () ; } 
                 exit ( 0 ) ; }
            else fprintf ( stderr , "\r(retained %i of %i areas)\n" , recptr - rec , maxrec ) ; } 
   return ; 
} 


/****************   HEAVY CALCULATIONS   ***************/
/*     This is a recursive function, that generates    */
/*     all possible cell combinations                  */


int firsbit = 0 ;

void generar ( void ) 
{   char edge = 0 ; 
    int32 mask , x , y ; 
    int32 * ptdest , * pta , * ptb , * ptc , * ptd ; 
    int havsom , j , k ; 
    int cellwas ;
    int skip_it ;  // used for constraints
    if ( const_search ) 
         if ( atcell >= last_const_cell && atbit > last_const_bit ) return ;  
    mask = ~atbit ; 
    cellwas = atcell ; 
    if ( ++ totbits > totareas ) { 
          -- totbits ;
          return ; }
    x = ( totbits - 1 ) % cols ; 
    y = ( totbits - 1 ) / cols ;
    havsom = 0 ;
    if ( isdefd[y][x] && !empcell[y][x] ) {
        ptdest = curinters [ cursize + 1] - 1 ;  
        pta = fake_matrix [ y ] [ x ] - 1 ; 
        ptb = curinters [ cursize ] - 1 ; 
        for ( j = spcells ; j -- ; )   
              if ( ( * ++ ptdest = ( * ++ pta & * ++ ptb ) ) != 0 )
                       havsom += onbits ( * ptdest ) ;
        if ( havsom >= minscore && firsbit > ( cols + 3 ) ) {
                  j = firsbit - ( cols + 3 ) ;
                  ptdest = curinters [ cursize + 1 ] - 1 ;
                  pta = forsp [ j ] - 1 ; 
                  havsom = 0 ; 
                  for ( j = spcells ; j -- ; )
                     havsom += onbits ( * ++ ptdest &= * ++ pta ) ; }
        if ( havsom >= minscore ) {
              currec.lst[atcell] |= atbit ;
              * listinpt ++ = totbits - 1 ; 
              ++ cursize ; }}
    if ( !firsbit ) { 
           firsbit = totbits ;
           fprintf ( stderr , "\r%2i%% completed " , ( firsbit * 100 ) / totareas ) ; }
    if ( atbit == BIT32 ) { 
             atbit = 1 ; 
             edge = 1 ; 
             ++ atcell ; } 
    else atbit <<= 1 ; 
    if ( havsom >= minscore ) {
        skip_it = 0 ; 
        if ( const_search ) {
            pta = const_list ;
            ptb = currec.lst ; 
            for ( j = -1 ; j < atcell && !skip_it ; ++ j )
                  if ( ( * ptb ++ & ~ * pta ++ ) ) skip_it = 1 ; }
        if ( !skip_it ) {
           if ( cursize < maxsize ) generar () ;
           if ( cursize > 1 ) {
               if ( ( totbits + cols + 2 ) < totareas ) {
                      ptdest = curinters [ cursize ] - 1 ;  
                      ptb = curinters [ cursize - 1 ] - 1 ; 
                      pta = fake_matrix [ y ] [ x ] - 1 ;
                      ptc = backsp [ totbits + cols + 2 ] - 1 ;
                      havsom = 0 ; 
                      for ( j = spcells ; j -- ; )   
                         if ( ( * ++ ptdest = ( * ++ pta & * ++ ptb & * ++ ptc ) ) != 0 )
                                 havsom += onbits ( * ptdest ) ; } 
               if ( havsom >= minscore ) quepasa () ; }} 
        -- cursize ;
        -- listinpt ; } 
    if ( firsbit == totbits ) firsbit = 0 ;  
    currec.lst[cellwas] &= mask ;
    if ( isdefd[y][x] ) 
           * listoutpt ++ = totbits - 1 ; 
    chkbyebye () ; 
    ptdest = curinters [ cursize + 1 ] ; 
    pta = curinters [ cursize ] ;
    for ( j = spcells ; j -- ; ) * ptdest ++ = * pta ++ ;  
    generar () ;  
    if ( edge ) { 
         atbit = BIT32 ; 
         -- atcell ; } 
    else atbit >>= 1 ;
    if ( isdefd[y][x] ) 
         -- listoutpt ; 
    -- totbits ;
    return ; 
} 


/**********  GENERAL SEARCH FUNCTIONS  *******************/
/*    These are the functions that organize the          */
/*    search: call basic generator of areas, and         */
/*    function that eliminates redundant/suboptimal      */
/*    areas                                              */

void fill_widefilter ( void )
{
    int a , c , x , y , j , k , sc ;
    int32 sb ;
    int empys , countit , atleastone ;
    for ( a = spcells ; a -- ; ) widefilter [ a ] = ~0 ;
    if ( !ridofwides ) return ; 
    sc = 0 ;
    sb = 1 ; 
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
                  // NOTE: here, musthaveone=1 makes it less strict (i.e. more error-prone)
              if ( empys >= abslim ) { countit = 0 ; break ; }}
         if ( countit ) {
             fprintf ( stderr,"Species %i - not counted (widespread)\n" , a ) ;
             numentries [ a ] = 0 ; 
             widefilter [ sc ] ^= sb ; }
         if ( sb == BIT32 ) { ++ sc ; sb = 1 ; }
         else sb <<= 1 ; }
   for ( y = 0 ; y < rows ; ++ y )
      for ( x = 0 ; x < cols ; ++ x ) 
          if ( isdefd [ y ][ x ] ) 
             for ( c = 0 ; c < spcells ; ++ c )
                matrix [ y ][ x ][ c ] &= widefilter [ c ] ; 
   return ;
}


void fill_forsp ( void )
{
    int32 * pa , * pb , * pc ;
    int a , j , y , x ;
    int lastar = ( rows * cols ) - 1 ;
    if ( !do_exact_search ) return ; 
    pa = forsp [ 0 ] - 1 ;
    pb = matrix [ 0 ] [ 0 ] - 1 ;
    if ( isdefd [ 0 ] [ 0 ] )
         for ( j = spcells ; j -- ; ) * ++ pa = * ++ pb ;
    else for ( j = spcells ; j -- ; ) * ++ pa = 0 ;
    for ( a = 1 ; a < totareas ; ++ a ) {
        y = a / cols ;
        x = a % cols ;
        pa = forsp [ a ] - 1 ;
        pb = matrix [ y ] [ x ] - 1 ;
        pc = forsp [ a - 1 ] - 1 ; 
        if ( !isdefd [ y ] [ x ] ) pb = pc ; 
        for ( j = spcells ; j -- ; )
               * ++ pa = * ++ pb | * ++ pc ; }
    pa = backsp [ lastar ] - 1 ;
    pb = matrix [ lastar / cols ] [ lastar % cols ] - 1 ; 
    if ( isdefd [ lastar / cols ] [ lastar % cols ] )
         for ( j = spcells ; j -- ; ) * ++ pa = * ++ pb ;
    else for ( j = spcells ; j -- ; ) * ++ pa = 0 ;
    for ( a = lastar ; a -- ; ) {
        y = a / cols ;
        x = a % cols ;
        pa = backsp [ a ] - 1 ;
        pb = matrix [ y ] [ x ] - 1 ;
        pc = backsp [ ( a + 1 ) ] - 1 ; 
        if ( !isdefd [ y ] [ x ] ) pb = pc ;  
        for ( j = spcells ; j -- ; )
               * ++ pa = * ++ pb | * ++ pc ; }
    for ( a = totareas ; a -- ; ) {
        pa = forsp [ a ] ;
        pb = backsp [ a ] ;
        for ( j = spcells ; j -- ; ) {
            * pa = ~ * pa ;
            * pb = ~ * pb ;
            ++ pa ;
            ++ pb ; }} 
    return ; 
}        

void calculate ( int inited ) 
{  int32 * pt ; 
   int a ;
   int32 x ;

   if ( !inited ) {
      nubi = num = depth = 0 ;
      fill_widefilter () ;
      fill_distributions () ;
      fill_forsp () ; 
      pt = currec.lst ; 
      for ( a = arcells ; a -- ; ) * pt ++ = 0 ; 
      for ( a = spcells ; a -- ; )  
           curinters [ 0 ] [ a ] = ( ~0 ) & widefilter [ a ] ;  
      if ( const_search ) eliminate_outsiders ( ) ; }
      
   fprintf ( stderr,"\n" ) ;
   cursize = 0 ; 
   atcell = 0 ; 
   atbit = 1 ; 
   totbits = 0 ; 
   firsbit = 0 ;
   if ( do_exact_search ) {
       generar () ;
       fprintf ( stderr , "\r                                      \n" ) ; 
       clean_areas ( 1 , 0 ) ; } 
   else {
       heuristics () ;
       clean_areas ( 1 , 1 ) ; } 
   fprintf ( stderr,"\r                                         \nDone!" ) ;
   return ; 
} 


/*********************** DATA INPUT *************************/
/*       This part also handles memory allocation,          */
/*       and checks the arguments                           */

unsigned  int allocd = 0 ; 

void * mymem ( int siz )
{
    char * p ;
    p = ( char * ) malloc ( siz ) ;
    allocd += siz ;
    if ( p == NULL ) {
            fprintf ( stderr , "\nNot enough memory to run\n%i bytes already allocated" , allocd ) ;
            getch () ;
            exit ( 0 ) ; }             
    return ( char * ) p ;
} 

void errout ( char * msg ) 
{
    if ( msg != NULL ) fprintf ( stderr , "\n%s\n", msg ) ;
    getch () ; 
    exit ( 0 ) ; 
}

void errar ( void ) 
{ 
  errout ( "Each area must be indicated as Arow-col" ) ; 
} 

void nexar ( int * a , int * b ) 
{ int x = getc ( input ) ; 
  while ( isspace ( x ) ) x = getc ( input ) ; 
  if ( tolower ( x ) != 'a' ) errar () ; 
  if ( !fscanf ( input , " %i" , a ) ) errar () ;  
  x = getc ( input ) ; 
  if ( x != '-' ) errout ("Areas must be indicated with Ai-j" ) ; 
  if ( !fscanf ( input , " %i" , b ) ) errar () ; 
  return ; 
} 

int nexnu ( void ) 
{ 
   int x = getc ( input ) ; 
   while ( isspace ( x ) ) x = getc ( input ) ; 
   if ( x == ';' ) return -1 ; 
   if ( x == '1' ) return 1 ; 
   if ( x == '2' ) return 2 ; 
   if ( x == '0' ) return 0 ; 
   ungetc ( x , input ) ; 
   return 3 ; 
} 

void read_matrix ( void ) 
{
   int a , b , c , x , valsread , valstoread ; 
   int32 * ptr , * infptr ; 
   int atb , maxspp = spp ;
   MinMaxtyp * mmpt ; 
   spcells = ( ( spp + 31 ) / 32 ) + 1 ;
   listin = ( int * ) mymem ( rows * cols * sizeof ( int ) ) ; 
   listout = ( int * ) mymem ( rows * cols * sizeof ( int ) ) ;
   listadja = ( int * ) mymem ( rows * cols * sizeof ( int ) ) ;
   listnonadja = ( int * ) mymem ( rows * cols * sizeof ( int ) ) ;
   listedge = ( int * ) mymem ( rows * cols * sizeof ( int ) ) ; 
   listinpt = listin ;
   listoutpt = listout ; 
   matrix = ( int32 ***) mymem ( rows * sizeof ( int32 ** ) ) ;
   assmatrix = ( int32 ***) mymem ( rows * sizeof ( int32 ** ) ) ;
   isdefd = ( char **) mymem ( rows * sizeof ( char * ) ) ; 
   empcell = ( char **) mymem ( rows * sizeof ( char * ) ) ; 
   tmplist = ( int * ) mymem ( rows * cols * sizeof ( int ) ) ; 
   setlist = ( int * ) mymem ( rows * cols * sizeof ( int ) ) ; 
   nosetlist = ( int * ) mymem ( rows * cols * sizeof ( int ) ) ; 
   archeckd = ( int * ) mymem ( rows * cols * sizeof ( int ) ) ;
   sized = ( int ** ) mymem ( rows * sizeof ( int * ) ) ;
   widefilter = ( int32 * ) mymem ( spcells * sizeof ( int32 ) ) ;
   for ( a = rows ; a -- ; )
       sized [ a ] = ( int * ) mymem ( cols * sizeof ( int ) ) ; 
   numentries = ( int * ) mymem ( spp * sizeof ( int ) ) ; 
   numassentries = ( int * ) mymem ( spp * sizeof ( int ) ) ; 
   for ( a = spp ; a -- ; ) numentries [ a ] = numassentries [ a ] = 0 ; 
      for ( a = rows ; a -- ; ) {
         matrix [ a ] = ( int32 ** ) mymem ( cols * sizeof ( int32 * ) ) ; 
         assmatrix [ a ] = ( int32 ** ) mymem ( cols * sizeof ( int32 * ) ) ; 
         isdefd [ a ] = ( char * ) mymem ( cols * sizeof ( char ) ) ; 
         empcell [ a ] = ( char * ) mymem ( cols * sizeof ( char ) ) ; 
         for ( b = cols ; b -- ; ) { 
            matrix [ a ] [ b ] = ( int32 * ) mymem ( spcells * sizeof ( int32 ) ) ; 
            assmatrix [ a ] [ b ] = ( int32 * ) mymem ( spcells * sizeof ( int32 ) ) ; 
            empcell [ a ] [ b ] = 1 ; 
            isdefd [ a ] [ b ] = 0 ; }} 
   valstoread = 0 ;
   spminmax = ( MinMaxtyp * ) mymem ( spp * sizeof ( MinMaxtyp ) ) ; 
   mmpt = spminmax ;
   for ( a = 0 ; a < spp ; ++ a , ++ mmpt ) {
       mmpt -> minc = mmpt -> minr = 32767 ; 
       mmpt -> maxc = mmpt -> maxr = 0 ; } 
   while ( 1 ) { 
       nexar ( &a , &b ) ; 
       if ( a >= rows || b >= cols ) { 
              fprintf ( stderr,"Cannot read value for area %i-%i (maxrows=%i, maxcols=%i)\n" , b , a , rows, cols ) ; 
              errout ( NULL ) ; } 
       ptr = matrix [ a ] [ b ] ; 
       * ptr = 0 ;
       infptr = assmatrix [ a ] [ b ] ; 
       * infptr = 0 ;
       x = nexnu () ; 
       atb = valsread = 0 ;
       mmpt = spminmax ; 
       while ( ( x <= 2 && x >= 0 ) && !feof ( input ) ) { 
           if ( x == 1 ) { 
               empcell [ a ] [ b ] = 0 ;
               if ( mmpt -> minc > b ) mmpt -> minc = b ; 
               if ( mmpt -> maxc < b ) mmpt -> maxc = b ; 
               if ( mmpt -> minr > a ) mmpt -> minr = a ; 
               if ( mmpt -> maxr < a ) mmpt -> maxr = a ; 
               ++ numentries [ valsread ] ;
               ++ numassentries [ valsread ] ; 
               * ptr |= ( 1 << atb ) ;
               * infptr |= ( 1 << atb ) ; }
           if ( x == 2 ) { 
               empcell [ a ] [ b ] = 0 ;
               ++ numassentries [ valsread ] ; 
               * infptr |= ( 1 << atb ) ; }
           ++ valsread ;
           ++ mmpt ; 
           if ( valsread > spp ) {
                   fprintf ( stderr, "Too many species for area %i-%i" , a , b ) ; 
                   errout ( NULL ) ; }
           if ( ++ atb == 32 ) { 
              atb = 0 ; 
              * ++ ptr = 0 ;
              * ++ infptr = 0 ; 
              if ( ptr - matrix[a][b] > spcells ) { 
                   fprintf ( stderr, "Too many species for area %i-%i" , a , b ) ; 
                   errout ( NULL ) ; }}
           x = nexnu () ; } 
       isdefd [ a ] [ b ] = 1 ; 
       if ( valstoread ) { 
          if ( valsread != valstoread ) { 
               fprintf ( stderr , "Too many or too few species for area %i-%i", a , b ) ; 
               errout ( NULL ) ; }} 
       else {  valstoread = spp = valsread ;
               spcells = ( spp + 31 ) / 32 ; } 
       if ( feof ( input ) || x < 0 ) break ; }
   fscanf ( input , " %s" , &str ) ;
   if ( !strcmp ( str , "extass" ) ) {
       read_extass ( maxspp ) ;
       a = get_species_tree ( maxspp , 1 ) ; }
   else 
      if ( !strcmp ( str , "groups" ) ) 
          a = get_species_tree ( maxspp , 0 ) ;

   x = spcells ;
   spcells = ( ( maxspp + 31 ) / 32 ) + 1 ;
   fake_matrix = ( int32 ***) mymem ( rows * sizeof ( int32 ** ) ) ; 
   fake_numentries = ( int * ) mymem ( maxspp * sizeof ( int ) ) ; 
   for ( a = spp ; a -- ; ) fake_numentries [ a ] = numentries [ a ] ;
   for ( a = rows ; a -- ; ) {
       fake_matrix [ a ] = ( int32 ** ) mymem ( cols * sizeof ( int32 * ) ) ; 
       for ( b = cols ; b -- ; )  { 
          fake_matrix [ a ] [ b ] = ( int32 * ) mymem ( spcells * sizeof ( int32 ) ) ;
          for ( c = spcells ; c -- ; )
              fake_matrix [ a ] [ b ] [ c ] = matrix [ a ] [ b ] [ c ] ; }}
   spcells = x ; 

   add_species_groups () ; 
   if ( a ) fscanf ( input , " %s", &str ) ; 
   if ( !feof ( input ) ) 
     if ( !strcmp ( str , "spwts" ) ) {
       weight_species = 1 ; 
       species_weight = ( float * ) mymem ( spp * sizeof ( float ) ) ;
       for ( a = 0 ; a < spp ; ++ a ) {
            fscanf ( input , "%f" , &(species_weight[a]) ) ;
            if ( feof ( input ) ) errout ( "Found EOF while reading species weights" ) ; }
    fscanf ( input , " %s", &str ) ; 
    if ( !feof ( input ) )
       if ( !strcmp ( str , "groups" ) ) errout ( "Higher groups must be specified BEFORE species weights" ) ; }
   return ; 
}

void make_more_space ( void )
{  int a , b , c ;
   rec = ( Artyp *) mymem ( maxrec * sizeof ( Artyp ) ) ;
   recptr = rec ;
   arcells = ( ( rows * cols ) + 31 ) / 32 ;
   totareas = rows * cols ; 
   for ( a = maxrec ; a -- ; ) rec[a].lst = NULL ; 
   intersptr = (int32 *) mymem ( spcells * sizeof ( int32 ) ) ; 
   if ( maxsize > rows * cols || ( !do_exact_search && maxsize < rows * cols ))
        maxsize = rows * cols ;
   curinters  = ( int32 ** ) mymem ( ( maxsize + 2 ) * sizeof ( int32 * ) ) ; 
   curdabland = ( int32 ** ) mymem ( ( maxsize + 2 ) * sizeof ( int32 * ) ) ; 
   curdablor  = ( int32 ** ) mymem ( ( maxsize + 2 ) * sizeof ( int32 * ) ) ; 
   for ( a = maxsize + 2 ; a -- ; ) { 
       curdabland[a] = ( int32 * ) mymem ( spcells * sizeof ( int32 ) ) ; 
       curdablor [a] = ( int32 * ) mymem ( spcells * sizeof ( int32 ) ) ; 
       curinters [a] = ( int32 * ) mymem ( spcells * sizeof ( int32 ) ) ; } 
   currec.lst = ( int32 *) mymem ( arcells * sizeof ( int32 ) ) ;
   currec.splist = ( int32 *) mymem ( spcells * sizeof ( int32 ) ) ;
   upand = ( int32 ** ) mymem ( totareas * sizeof ( int32 * ) ) ;
   upor = ( int32 ** ) mymem ( totareas * sizeof ( int32 * ) ) ;
   for ( a = totareas ; a -- ; ) {
       upand [ a ] = ( int32 * ) mymem ( spcells * sizeof ( int32 ) ) ; 
       upor [ a ] = ( int32 * ) mymem ( spcells * sizeof ( int32 ) ) ; }
/*
   fake_matrix = ( int32 ***) mymem ( rows * sizeof ( int32 ** ) ) ; 
   fake_numentries = ( int * ) mymem ( spp * sizeof ( int ) ) ; 
   for ( a = spp ; a -- ; ) fake_numentries [ a ] = numentries [ a ] ;
   for ( a = rows ; a -- ; ) {
           fake_matrix [ a ] = ( int32 ** ) mymem ( cols * sizeof ( int32 * ) ) ; 
           for ( b = cols ; b -- ; )  { 
              fake_matrix [ a ] [ b ] = ( int32 * ) mymem ( spcells * sizeof ( int32 ) ) ;
              for ( c = spcells ; c -- ; )
                         fake_matrix [ a ] [ b ] [ c ] = matrix [ a ] [ b ] [ c ] ; }}
*/
   if ( do_exact_search ) { 
      forsp = ( int32 ** ) mymem ( totareas * sizeof ( int32 * ) ) ;
      backsp = ( int32 ** ) mymem ( totareas * sizeof ( int32 * ) ) ;
      for ( a = totareas ; a -- ; ) { 
           forsp [ a ] = ( int32 * ) mymem ( spcells * sizeof ( int32 ) ) ; 
           backsp [ a ] = ( int32 * ) mymem ( spcells * sizeof ( int32 ) ) ; }}
   else { 
      ranswaplist = ( int32 * ) mymem ( totareas * sizeof ( int32 ) ) ; 
      bigar = ( int32 * ) mymem ( arcells * sizeof ( int32 ) ) ;
      smallarset = ( int32 * ) mymem ( spcells * sizeof ( int32 ) ) ;
      bigarset = ( int32 * ) mymem ( spcells * sizeof ( int32 ) ) ;
      faraway = ( int * ) mymem ( totareas * sizeof ( int ) ) ;
      farar = ( int32 * ) mymem ( arcells * sizeof ( int32 ) ) ; 
      globnonadja = ( int * ) mymem ( spp * sizeof ( int ) ) ;
      sizelist = ( Listyp ** ) mymem ( maxsize * sizeof ( Listyp * ) ) ;
      for ( a = maxsize ; a -- ; ) sizelist [ a ] = NULL ;
      reclist = ( Listyp * ) mymem ( maxrec * sizeof ( Listyp ) ) ;
      nexreclist = reclist ; 
      for ( a = maxrec ; a -- ; ) ( nexreclist ++ ) -> tolist = NULL ; 
      nexreclist = reclist ; } 
   return ;
}

void chkword ( char * bs , int * nu ) 
{ 
  if ( !strcmp ( str , bs ) )  
      if ( !fscanf ( input, " %i", nu ) ) { 
           fprintf ( stderr, "Expected number after %s" , bs ) ; 
           errout ( NULL ) ; } 
  return ; 
}

void chkdouble ( char * bs , double * nua , double * nub )
{
  if ( strcmp ( str , bs ) ) return ; 
  if ( !fscanf ( input, " %f", nua ) )  {
      fprintf ( stderr, "Expected number after %s" , bs ) ; 
      errout ( NULL ) ; } 
  if ( !fscanf ( input, " %f", nub ) )  {
      fprintf ( stderr, "Expected TWO numbers after %s" , bs ) ; 
      errout ( NULL ) ; } 
  return ; 
}    

void read_data ( void ) 
{   int a ; 
    str[0]=0;
    while ( strcmp ( str , "data" ) && strcmp ( str , "xydata" ) ) {
       fscanf ( input , " %s", &str ) ; 
       if ( feof ( input ) ) errout ( "Found EOF before data appeared!" ) ; 
       chkword ( "rows" , &rows ) ; 
       chkword ( "cols" , &cols ) ; 
       chkword ( "spp" , &spp ) ;
       chkdouble ( "gridx" , &grid_startx , &grid_width ) ; 
       chkdouble ( "gridy" , &grid_starty , &grid_height ) ;
      }
   if ( !strcmp ( str , "data" ) ) read_matrix () ;
}

void doword ( char * wrd ) 
{ fprintf ( stdout,"%s N \n" , wrd ) ; } 


void argerr ( char * msg )
{
  fprintf ( stderr , "Argument error: must give value of %s" , msg ) ;
  errout ( NULL ) ;
}

int strmatch ( char * arg , char * txt )
{
    char * x = arg , * y = txt ;
    while ( * y && * x == * y ) { ++ x ; ++ y ; }
    if ( * y ) return 0 ;
    return 1 ; 
} 

void chkargs ( int argn , char ** args ) 
{  int i , x , a ; 
   char * pipi ;
   int mtch ; 
   i = 1 ;
   startfile = NULL ; 
   while ( ++ i < argn ) {
            if ( args [ i ] [ 0 ] != '-' && args [ i ] [ 0 ] != '+' ) continue ; 
            x  = args [ i ] [ 1 ] ;
            if ( args [ i ] [ 0 ] == '+' ) {
                      if ( x == 'r' ) { 
                         pipi = args [ i ] + 2 ;
                         xperc = atoi ( pipi ) ; 
                         if ( xperc < 0 ) argerr ( "radius" ) ;
                         yperc = xperc ; }
                 else if ( x == 'e' ) { 
                         pipi = args [ i ] + 2 ;
                         fill_abslim = atoi ( pipi ) ; 
                         if ( fill_abslim > 7 || fill_abslim < 1 ) argerr ( "Fill abs. lim." ) ; }
                 else if ( x == 's' ) {
                     x = args [ i ] [ 2 ] ;
                     if ( x != 'x' && x != 'y' ) argerr ( "coordinate shift" ) ;
                     pipi = args [ i ] + 3 ;
                     if ( x == 'x' ) xframeshift = ( double ) atof ( pipi ) ;
                     else yframeshift = ( double ) atof ( pipi ) ;
                     if ( xframeshift < 0 || xframeshift > 100 ||
                     yframeshift < 0 || yframeshift > 100 ) argerr ("coordinate shift, 0-100" ) ; } 
                 else if ( x == 'x' ) { 
                         pipi = args [ i ] + 2 ;
                         xperc = atoi ( pipi ) ; 
                         if ( xperc == 0 ) argerr ( "X-radius" ) ; }
                 else if ( x == 'y' ) { 
                         pipi = args [ i ] + 2 ;
                         yperc = atoi ( pipi ) ; 
                         if ( yperc == 0 ) argerr ( "Y-radius" ) ; }
                 else {
                    fprintf ( stderr,"\nWrong argument: %s\n" , args[i] ) ;
                    errout ( NULL ) ; }
                 continue ; }
            if ( !strcmp ( args [ i ] , "-add" ) ) dontadd = 1 ;
#ifdef LINUX 
            if ( !strcmp ( args[i] , "-bground" ) ) {
                 running_in_background = 1 ; 
                 bgroundfile = fopen ( "background.txt" , "w" ) ; }
#endif
            else if ( !strcmp ( args[i] , "-postchk" ) ) post_individuation = 0 ; 
            else if ( !strcmp ( args [ i ] , "-wide" ) ) use_wide_init = 1 ; 
            else if ( !strcmp ( args [ i ] , "-skip" ) ) skip_superfluous = 1 ;
            else if ( !strcmp ( args [ i ] , "-sskip" ) ) 
                       skip_superfluous = autoreplace = 1 ; 
            else if ( x == 'a' ) saveall = 1 ;
            else if ( !strcmp ( args [ i ] , "-dumpsub" ) ) dump_suboptimal = 0 ; 
            else if ( strmatch ( args [ i ] , "-swap" ) ) {
                    pipi = args [ i ] + 5 ;
                    cells_to_swap = atoi ( pipi ) ;
                    if ( cells_to_swap < 1 || cells_to_swap > 2 ) argerr ( "cells to swap" ) ; }
            else if ( strmatch ( args[i] , "-start" ) ) {
                   startfile = fopen ( args[i] + 6 , "rb" ) ;
                   if ( startfile == NULL ) 
                       argerr ( "Name of file with starting sets" ) ; }
            else if ( strmatch ( args[i] , "-clean" ) ) {
                      pipi = args [ i ] + 6 ;
                      max_buffer_clean = atoi ( pipi ) ;
                      if ( max_buffer_clean < 0 ) argerr ( "max. buffer cleans" ) ; }
            else if ( x == 'X' ) do_exact_search = 1 ; 
            else if ( x == 'p' ) use_edge_props = 1 ; 
            else if ( x == 37 ) { 
                         pipi = args [ i ] + 2 ;
                         compare_perc = atoi ( pipi ) ;
                         if ( compare_perc < 0 || compare_perc >= 99 ) argerr ( "compare percentage" ) ;  }
            else if ( x == 'f' ) {
                a = args[i][2] ;
                pipi = args[i]+3 ; 
                if ( a == 'o' ) oufac = ( double ) atof ( pipi ) ;
                if ( a == 'i' ) ifac = ( double ) atof ( pipi ) ;
                if ( a == 'a' ) afac = ( double ) atof ( pipi ) ;
                if ( a == 'd' ) oafac = ( double ) atof ( pipi ) ; 
                if ( a == 'n' ) ononafac = ( double ) atof ( pipi ) ; 
                if ( oufac <= 0 || oafac <= 0 || ononafac <= 0 || 
                     ifac < 0 || afac < 0 || ifac > 1 || afac > 1 )
                     argerr ( "factor for outside/inferred/assumed" ) ; }
            else if ( x == 'r' ) {
                     pipi = args [i] + 2 ;
                     slopeval = ( double ) atof ( pipi ) ;
                     if ( slopeval > 2 || slopeval <= 0 ) argerr ( "factor must be 0 < r <= 2" ) ; } 
            else if ( x == 'q' ) query = 1 ;
            else if ( x == '!' ) query = 2 ; 
            else if ( !strcmp ( args [i] + 1 , "tocoord" ) ) translate_to_coords = 1 ; 
            else if ( x == 'B' ) breakable = 0 ;
            else if ( x == 'b' ) {
                        pipi = args[ i ] + 2 ;
                        minimum_sp_score = atof ( pipi ) ;
                        if ( minimum_sp_score < 0 || minimum_sp_score > 1 ) argerr ( "minimum sp. score" ) ; }
            else if ( x == 'w' ) ridofwides = 1 ;
            else if ( x == 'l' ) {
                         logfilename = args [ i ] + 2 ;
                         logfile = fopen ( logfilename , "wb" ) ; 
                         if ( logfile == NULL ) errout ( "Argument error: cannot open log file" ) ; }
            else if ( x == 'x' ) { 
                         pipi = args [ i ] + 2 ;
                         cols = atoi ( pipi ) ; 
                         if ( cols == 0 ) argerr ( "cols." ) ; }
            else if ( x == 'y' ) { 
                         pipi = args [ i ] + 2 ;
                         rows = atoi ( pipi ) ; 
                         if ( rows == 0 ) argerr ( "rows" ) ; }
            else if ( x == 'n' ) { 
                         pipi = args [ i ] + 2 ;
                         maxrec = atoi ( pipi ) ; 
                         if ( maxrec == 0 ) argerr ( "areas to keep" ) ; }
            else if ( x == '#' ) { 
                         pipi = args [ i ] + 2 ;
                         num_replicates = atoi ( pipi ) ; 
                         if ( num_replicates == 0 ) argerr ( "number of replicates" ) ; }
            else if ( x == 'e' ) { 
                         pipi = args [ i ] + 2 ;
                         abslim = atoi ( pipi ) ; 
                         if ( abslim == 0 ) argerr ( "max. number of unoccupied cells" ) ; }
            else if ( x == 'h' ) {
                         pipi = args [ i ] + 2 ;
                         musthaveone = atoi ( pipi ) ;
                         if ( musthaveone < 0 || musthaveone > 2 )
                             argerr ( "requirement of a occupied cell must be\n   0 - no\n   1 - require it for cells (except if cell itself assumed)\n   2 - require it for all cells within area\n" ) ; }
            else if ( x == '1' ) retouch = 0 ;
            else if ( x == 'k' ) {
                     pipi = args [ i ] + 2 ;
                     set_const ( pipi ) ; } 
            else if ( x == 'T' ) { 
                         pipi = args [ i ] + 2 ;
                         min_pres_perc = atoi ( pipi ) ; 
                         if ( min_pres_perc < 0 ) argerr ( "minimum species occupancy (perc.)" ) ; }
            else if ( x == 'm' ) { 
                         pipi = args [ i ] + 2 ;
                         minscore = atoi ( pipi ) ; 
                         if ( minscore < 0 ) argerr ( "minscore" ) ; }
            else if ( x == 'M' ) {
                         pipi = args [ i ] + 2 ;
                         minrealscore = ( double ) atof ( pipi ) ;
                         if ( minrealscore <= 0 ) argerr ( "min. real score" ) ; } 
            else if ( x == 'j' ) { 
                         pipi = args [ i ] + 2 ;
                         make_random_data = 1 ; 
                         probone = atoi ( pipi ) ; 
                         if ( probone == 0 ) argerr ( "probability of 1 (=presence)" ) ; }
            else if ( x == 'd' ) {
                         pipi = args [ i ] + 1 ;
                         if ( !strcmp ( pipi , "data" ) ) also_save_data = 0 ;
                         else { 
                            pipi = args [ i ] + 2 ;
                            if ( !( isdigit ( * pipi ) ) ) argerr ( "random seed" ) ; 
                            ranseed = atoi ( pipi ) ; }}
            else if ( x == 'o' ) { 
                         pipi = args [ i ] + 2 ; 
                         suboptimal = ( double ) atof ( pipi ) ; 
                         if ( suboptimal == 0 ) argerr ("suboptimal" ) ; } 
            else if ( x == 's' ) {
                            pipi = args [ i ] + 2 ; 
                            maxsize = atoi ( pipi ) ; 
                            if ( maxsize == 0 ) argerr ("max. size" ) ; } 
            else { fprintf ( stderr,"\nWrong argument: %s\n" , args[i] ) ; errout ( NULL ) ; }} 
    if ( minrealscore > minscore ) minscore = ( int ) minrealscore ; 
    i = 1 ; 
    while ( ++ i < argn ) { 
         if ( args [ i ] [ 0 ] == '-' || args [ i ] [ 0 ] == '+' ) continue ; 
         if ( query ) { 
            output = fopen ( args [ i ] , "r" ) ; 
            if ( output != NULL ) { 
                fclose ( output ) ; 
                while ( x != 'y' && x != 'n' ) { 
                    fprintf ( stderr,"\rFile %s exists.  Overwrite? (y/n)", args [ i ] ) ; 
                    x = tolower ( getch () ) ; } 
                for ( a = 60 ; a -- ; ) fprintf ( stderr,"\b \b" ) ; 
                if ( x == 'n' ) exit ( 0 ) ; }}
         output = fopen ( args [ i ] , "w" ) ; 
         if ( output == NULL ) { 
                fprintf ( stderr, "Cannot open file %s for output" , args [ i ]  ) ; 
                errout ( NULL ) ; }
         break ; }
}    

void randomize_data ( void )
{ int a , b , c ; 
   srand ( ( int32 ) ranseed ) ;
   fprintf ( output , "\nrows %i\ncols %i\nspp %i\ndata\n" , rows , cols , spp ) ; 
   for ( a = rows ; a -- ; )
       for ( b = cols ; b -- ; ) {
          isdefd [ a ] [ b ] = 1 ;
          if ( output != stdout ) fprintf ( output , "\nA%i-%i  " , a , b ) ; 
          for ( c = spcells ; c -- ; ) matrix [ a ] [ b ] [ c ] = 0 ; 
          for ( c = spp ; c -- ; ) 
               if ( ( rand () % 100 ) < probone ) {
                    if ( output != stdout ) fprintf ( output , "1" ) ; 
                    numentries [ c ] ++ ; 
                    matrix [ a ] [ b ] [ c / 32 ] |= 1 << ( c % 32 ) ; }
               else if ( output != stdout ) fprintf ( output , "0" ) ; }
   fprintf ( output , "\n;\n" ) ; 
   return ;
}

void docomdlinehlp ( void )
{
       fprintf ( stdout, "\n" ) ; 
       doword ( "rows" ) ; 
       doword ( "cols" ) ; 
       doword ( "spp" ) ; 
       doword ( "maxsize" ) ;
       fprintf ( stderr, "\n\npress 'd' for data format" ) ; 
       if ( tolower ( getch () ) == 'd' ) system ( "cls" ) ;
       else exit ( 0 ) ; 
       fprintf ( stdout , "\nxydata\n   sp 0 [name for sp. 0]\n      9.1 2.3   3.4 5.6   6.7 8.9\n   sp 1 [name for sp. 1 ]\n      3.4 5.6   8.7 3.4\n   ...\n   ...\n   sp n [name for sp. n]\n   8.9 6.5   4.3 2.1   3.2 1.6   3.2 1.6\n(end of file)\n\nNote: species names are optional" ) ; 
       fprintf ( stdout, "\n\nor\n\n" ) ; 
       fprintf ( stdout,"\ndata\n  A0-0 0001\n  A0-1 0101\n  A0-2 1111\n  etc.\n\n" ) ;  
       fprintf ( stderr, "press 'm' for cell-numbering map" ) ; 
       if ( tolower ( getch () ) == 'm' ) { 
             system ( "cls" ) ; 
fprintf ( stdout, "\n\
\n\
cols 5\n\
rows 4 \n\
Area(row)-(col):\n\
  ÚÄÄÄÄÂÄÄÄÄÂÄÄÄÄÂÄÄÄÄÂÄÄÄÄ¿\n\
  ³0-0 ³0-1 ³0-2 ³0-3 ³0-4 ³\n\
  ÃÄÄÄÄÅÄÄÄÄÅÄÄÄÄÅÄÄÄÄÅÄÄÄÄ´\n\
  ³1-0 ³1-1 ³1-2 ³1-3 ³1-4 ³\n\
  ÃÄÄÄÄÅÄÄÄÄÅÄÄÄÄÅÄÄÄÄÅÄÄÄÄ´\n\
  ³2-0 ³2-1 ³2-2 ³2-3 ³2-4 ³\n\
  ÃÄÄÄÄÅÄÄÄÄÅÄÄÄÄÅÄÄÄÄÅÄÄÄÄ´\n\
  ³3-0 ³3-1 ³3-2 ³3-3 ³3-4 ³\n\
  ÀÄÄÄÄÁÄÄÄÄÁÄÄÄÄÁÄÄÄÄÁÄÄÄÄÙ\n\
\n" ) ; } 
       exit ( 0 ) ;
} 

void check_maxsize ( void )
{   int a = 0 , j , k ; 
    for ( j = 0 ; j < rows ; ++ j ) 
       for ( k = 0 ; k < cols ; ++ k ) 
           if ( isdefd [ j ] [ k ] ) ++ a;
    if ( a < maxsize ) maxsize = a ; 
    return ; 
} 

void showargs ( void )
{
  fprintf ( stderr , "\nPress 'c' for copyright notice,\nany other key for list of arguments " ) ; 
  if ( tolower ( getch () ) == 'c' ) { system ( "cls" ) ; show_copyright_notice () ; exit ( 0 ) ; } 
  system ( "cls" ) ; 
  fprintf ( stderr,"\n\
   NDM - vers. 3.1 - written by P. Goloboff (2004-2016)\n\
   Give name of input/output file as 1st/2nd argument\n"
"   Other args:                                                   defaults\n\
       -nN      hold up to N solutions                           [%i]\n\
       -sN      maxsize = N (exact solutions only)               [ none ] \n\
       -B       disable breaks (speed up?)                      [ enable ] \n\
       -jN      create random data matrix, p(1)=N             [ read data ] \n\
       -fxN     x-factor for records\n\   
                  x = i -> inferred records                      [ %5.3f ]\n\
                  x = a -> assumed records                       [ %5.3f ]\n\
                  x = o -> external (adjacent) records           [ %5.3f ]\n\
                  x = d -> external (ass,adj) recs               [ %5.3f ]\n\
                  x = n -> external (ass,nonadj) recs            [ %5.3f ]\n\
       -p       use proportion of edge with records              [ don't ]\n\
       -dN      random seed (-j option only)                       [ 1 ] \n\
       -lxxx    log results to file xxx (for VNDM)               [ don't ] \n\
       -data    if logging, save results only                     [ all ] \n\
       -mN      save only if N or more species have score          [ 2 ] \n\
       -kxxx    read constraints from xxx (bin, areas only)       [don't]\n\
       -oN      save contradictory sets if score up to N worse     [ 0 ] \n\
       -%%N      use N as percentage for area comparison            [ 0 ] \n\
       -q       query before exit                                 [don't]\n\
       -a       save all continuous sets, regardless of score     [don't]\n\
\n   (press key for more)" , maxrec , ifac , afac , oufac , oafac , ononafac ) ;
if ( getch () == 27 ) exit ( 0 ) ;
fprintf ( stderr , "\r                                    \r\
   Heuristics only:\n\
       -rN      use N as acceptance factor (heuristics only)       [ 1 ]\n\
       -cleanN  max. clean buffer N times (heuristic search)     [no max.]\n\
                (N=X is clean during search)\n\
       -skip    skip swapping for redundant/looser areas         [swap'em]\n\
       -sskip   as a set is improved by swapping, replace it     [ don't ]\n\
       -swapN   swap N cells at a time (1 or 2)                     [ 1 ]\n\
       -add     change areas by adding cells as well           [delete only]\n\
       -wide    use wide initialization of areas (heuristics)    [ narrow ]\n\
       -dumpsub keep suboptimal areas during search              [dump'em]\n\
       -postchk check whether areas are duplicate before\n\
                score evaluation                                 [ after ]\n\
       -#N      do N replicates                                  [   1   ]\n\
       -bN      use N as minimum species score                   [   0   ]\n\
\n   (press key for more)" ) ; 
   fprintf ( stderr,"\r                           \n\
   For basic inference of presences:  \n\
       -eN       ignore sp. if N surrounding cells unoccupied     [  3  ]\n\
       +eN       same, for filling distributions                  [  7  ]\n\
       -h        must have one occupied contiguous cell           [ not ]\n\
       -w        get rid of widespread species                    [don't]\n\
\n\
   XY-DATA only:\n\
       -x N     divide in N cols.                                 [ 10 ]\n\
       -y N     divide in N rows                                  [ 10 ]\n\
       +r N     radius N                                          [  0 ]\n\
       +x N     x-radius N                                        [  0 ]\n\
       +y N     y-radius N                                        [  0 ]\n\
       +sxN     shift frame on x by N percent                     [ 50 ]\n\
       +syN     shift frame on y by N percent                     [ 50 ]\n\
   Use \"ndm help\" or \"ndm ?\" for help on input format\n" ) ;
   fprintf ( stderr,"\nPress key to exit..." ) ; 
   getch() ;
   fprintf ( stderr,"\r                                \n\n" ) ; 
   exit ( 0 ) ;
} 


/**********   SAVE GRID DATA AS COORDINATES *****************/

void save_as_coords ( void )
{
   int a , b , c ;
   unsigned  int bt , cell ;
   double bpos , cpos , adx , ady ; 
   fprintf ( output , "\nspp %i\nxydata\n" , spp ) ;
   for ( a = 0 ; a < spp ; ++ a ) {
       fprintf ( output , "\nsp %i\n" , a ) ; 
       for ( b = 0 ; b < rows ; ++ b )
           for ( c = 0 ; c < cols ; ++ c ) {
               if ( !isdefd [ b ] [ c ] ) continue ;
               bt = 1 << ( a % 32 ) ;
               cell = a / 32 ;
               bpos = ( double ) b + 1 ;
               cpos = ( double ) c + 1 ;
               adx = ( double ) xperc / 100 ;
               ady = ( double ) xperc / 100 ;
               if ( ( matrix [ b ] [ c ] [ cell ] & bt ) ) {
                   fprintf ( output , "%.1f %.1f " , cpos , bpos ) ;
                   if ( adx > 0 ) { 
                      fprintf ( output , "%.1f %.1f " , cpos - adx , bpos - ady ) ; 
                      fprintf ( output , "%.1f %.1f " , cpos - adx , bpos + ady ) ;
                      fprintf ( output , "%.1f %.1f " , cpos + adx , bpos - ady ) ; 
                      fprintf ( output , "%.1f %.1f " , cpos + adx , bpos + ady ) ; } 
                   }}}
   return ;
} 
                   
/*****************   MAIN !!  ****************/

int main ( int argc , char ** argv ) 
{
   int a ;
   char tmpnam[ _MAX_PATH ] ; 
   if ( argc == 1 ) showargs () ; 
   if ( argc == 2 && ( !strcmp ( argv[1] , "help" ) || !strcmp ( argv[1] , "?" ) ) ) docomdlinehlp () ; 
   input = fopen ( argv[1] , "r" ) ; 
   if ( input == NULL ) errout ( "Cannot open data file for input" ) ; 
   output = stdout ; 
   chkargs ( argc , argv ) ;
   ++ maxrec ; 
   read_data () ;
   if ( translate_to_coords ) {
       save_as_coords () ;
       fprintf ( stderr , "\nSaved data as coordinates (radius=%i%%)\n" , xperc ) ;
       exit ( 0 ) ; } 
   make_more_space () ;
   -- maxrec ; 
   if ( minscore > spp ) errout ( "Minscore cannot be greater than nr. of spp." ) ;
   if ( make_random_data ) randomize_data () ; 
   init_time () ; 
   check_maxsize () ;
   calculin() ;
   read_constraints () ; 
   if ( !ranseed ) time ( &ranseed ) ; 
   srand ( ( unsigned  int ) ranseed ) ;

   randomize_startpoint = 0 ;
   if ( num_replicates > 1 ) daspranlist = mymem ( spp * sizeof ( int ) ) ; 

   for ( a = 0 ; a < num_replicates ; ++ a ) {
     if ( num_replicates > 1 ) {
           fprintf ( stderr , "\n-----------------------------\nREPLICATE NR. %i\n-----------------------------" , a + 1 ) ; 
#ifdef LINUX 
           if ( running_in_background ) {
             fprintf ( bgroundfile , "DOING REPLICATE nr. %i\n" , a + 1 ) ; fflush ( bgroundfile ) ; }
#endif
     }
       calculate ( a ) ;
       save_results () ;
       randomize_startpoint ++ ; 
       ranseed = rand () ;
       srand ( ( unsigned  int ) ranseed ) ; }
   show_time () ; 
   if ( query ) {
       if ( query == 1 ) fprintf ( stderr , "\nPress any key to exit program...\n" ) ;
       else fprintf ( stderr , "\nPress any key to go back to VNDM ...\n" ) ;
       getch () ; }
   exit ( 1 ) ;
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
    /**+ all sizes... */ 
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
    if ( trusz == acurl [ a ] ) errout ( "Cannot define duplicate groups!" ) ;
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
    
int get_species_tree ( int theospp , int chkstring ) 
{
    int x = 0 , a, b , c ;
    int32 bizin , bizout ;
    int cellin , cellout ;
    int * afare , * fatto ;
    int tot = 0 ; 
    numterminals = spp ;
    if ( chkstring ) {
       fscanf ( input , " %s", &str ) ; 
       if ( feof ( input ) ) { str[0] = '\0'; return 0 ; }
       if ( strcmp ( str , "groups" ) ) return 0 ; }
    indspscore = ( double * ) mymem ( spp * 2 * sizeof ( double ) ) ;
    species_tree = ( int * ) mymem ( spp * 2 * sizeof ( int ) ) ;
    treefirs = ( int * ) mymem ( spp * 2 * sizeof ( int ) ) ;
    treesis = ( int * ) mymem ( spp * 2 * sizeof ( int ) ) ;
    nodfork = ( int * ) mymem ( spp * 2 * sizeof ( int ) ) ;
    innerlist = ( int * ) mymem ( spp * 2 * sizeof ( int ) ) ;
    treelist = ( int * ) mymem ( spp * 2 * sizeof ( int ) ) ;
    acurl = ( int * ) mymem ( spp * 2 * sizeof ( int ) ) ;
    treeroot = spp ; 
    species_tree [ treeroot ] = spp + 1 ; 
    for ( a = spp ; a -- ; ) {
         species_tree [ a ] = treeroot ;
         treesis [ a ] = a + 1 ; }
    treefirs [ treeroot ] = 0 ;
    treesis [ spp - 1 ] = -1 ;
    while ( x != ';' && !feof ( input ) ) {
         x = getc ( input ) ;
         if ( isspace ( x ) ) continue ;
         if ( x == 123 /** open brace ***/ ) {
             ++ tot ;
             if ( ( spp + tot > theospp  ) ) errout ( "Cannot define so many groups --increase spp" ) ;
             if ( tot == spp - 1 ) errout ( "Cannot define so many groups" ) ; 
             a = 0 ;
             while ( x != 125  /** closing brace ***/  ) {
                 x = getc ( input ) ;
                 if ( isspace ( x ) ) continue ;
                 ungetc ( x , input ) ;
                 if ( isdigit ( x ) ) {
                     fscanf ( input , " %i" , &b ) ;
                     innerlist [ a ++ ] = b ; }}
             if ( a > numterminals ) errout ( "List of terminals in \"groups\" too long" ) ;
             if ( a < 2 ) errout ( "Groups must include 2 or more taxa" ) ; 
             add_node_to_species_tree ( innerlist , a ) ; }}
     number_of_groups = mkoptlist ( treelist , species_tree ) ;
     return 1 ; 
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
                fake_matrix [ a ] [ b ] [ cout ] = matrix [ a ] [ b ] [ cout ] ; 
                assmatrix [ a ] [ b ] [ cout ] &= ~bout ; }
        numentries [ spp ] = fake_numentries [ spp ] = numassentries [ spp ] = 0 ; 
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
                           matrix [ a ] [ b ] [ cout ] |= bout ;
                           if ( ! ( fake_matrix [ a ] [ b ] [ cout ] & bout ) ) ++ fake_numentries [ spp ] ;
                           fake_matrix [ a ] [ b ] [ cout ] = matrix [ a ] [ b ] [ cout ] ; }
                       if ( ( assmatrix [ a ] [ b ] [ cin ] & bin ) ) {
                           if ( ! ( assmatrix [ a ] [ b ] [ cout ] & bout ) ) ++ numassentries [ spp ] ;
                           assmatrix [ a ] [ b ] [ cout ] |= bout ; }}}}
        ++ spp ; }
    spcells = ( ( spp + 31 ) / 32 ) ;
    return ; 
}

void read_extass ( int maxspp )
{
    int a = 0 ;
    userextass = ( int * ) mymem ( maxspp * sizeof ( int ) ) ; 
    while ( !feof ( input ) ) {
        fscanf ( input , " %s" , &str ) ;
        if ( !strcmp ( str , ";" ) ) break ;
        userextass [ a ++ ] = atoi ( str ) ; }
    return ; 
}



