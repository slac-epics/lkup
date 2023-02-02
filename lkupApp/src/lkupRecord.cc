/* lkupRecord.c */
/* Record support module */

#include <algorithm>

#include <math.h>
#include <time.h>

#include <stddef.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>

#include "alarm.h"
#include "recGbl.h"
#include "dbScan.h"
#include "dbDefs.h"
#include "dbAccess.h"
#include "dbEvent.h"
#include "dbStaticLib.h"
#include "devSup.h"
#include "errMdef.h"
#include "recSup.h"
#include "special.h"

#define GEN_SIZE_OFFSET
#include "lkupRecord.h"
#undef  GEN_SIZE_OFFSET

#include "epicsExport.h"


/* Create RSET - Record Support Entry Table */
#define report             NULL
#define initialize         NULL

static long init_record( dbCommon *precord, int pass  );
static long process    ( dbCommon *precord            );
static long special    ( dbAddr   *pDbAddr, int after );
static long cvt_dbaddr ( dbAddr   *pDbAddr            );

#define get_value          NULL
#define get_array_info     NULL
#define put_array_info     NULL
#define get_units          NULL
#define get_precision      NULL
#define get_enum_str       NULL
#define get_enum_strs      NULL
#define put_enum_str       NULL
#define get_graphic_double NULL
#define get_control_double NULL
#define get_alarm_double   NULL

rset lkupRSET = {
	RSETNUMBER,
	report,
	initialize,
	(RECSUPFUN) init_record,
	(RECSUPFUN) process,
	(RECSUPFUN) special,
	get_value,
	(RECSUPFUN) cvt_dbaddr,
	get_array_info,
	put_array_info,
	get_units,
	get_precision,
	get_enum_str,
	get_enum_strs,
	put_enum_str,
	get_graphic_double,
	get_control_double,
	get_alarm_double
};

epicsExportAddress( rset, lkupRSET );


int lkupDebug = 0;

extern "C" { epicsExportAddress( int, lkupDebug ); }


using namespace std;



static long init_record( dbCommon *precord, int pass )
{
    lkupRecord *prec = (lkupRecord *)precord;
    long        status = 0;

    if ( pass == 1 ) return( status );

    prec->labl = (char         *)calloc( prec->nmax*40, sizeof(char        ) );
    prec->xval = (epicsFloat64 *)calloc( prec->nmax,    sizeof(epicsFloat64) );
    prec->yval = (epicsFloat64 *)calloc( prec->nmax,    sizeof(epicsFloat64) );
    prec->dval = (epicsFloat64 *)calloc( prec->nmax,    sizeof(epicsFloat64) );

    prec->irbv = -1;
    prec->udf  =  0;

    strncpy( prec->lrbv, "Unknown", 40 );

    recGblResetAlarms( prec );

    return( status );
}

static long process( dbCommon *precord )
{
    lkupRecord  *prec = (lkupRecord *)precord;
    double       inp, *xval=prec->xval, *yval=prec->yval, *dval=prec->dval;
    double       old_rbv  = prec->rbv;
    short        old_irbv = prec->irbv, ip;
    long         status = -1;

    if ( prec->pact ) return( 0 );

    prec->pact = TRUE;

    recGblGetTimeStamp( prec );

    prec->irbv = -1;
    strncpy( prec->orbv, prec->lrbv, 40 );
    strncpy( prec->lrbv, "Unknown",  40 );

    if ( (prec->npts > 1) && (prec->init > 0) &&
         (! dbGetLink(&prec->inp, DBR_DOUBLE, &inp, 0, 0)) )
    {
        if      ( inp <  xval[0]            ) ip = 0;
        else if ( inp >= xval[prec->npts-1] ) ip = prec->npts - 2;
        else
            for ( ip = 0; ip < prec->npts-1; ip++ )
                if ( (inp >= xval[ip]) && (inp < xval[ip+1]) ) break;

        prec->rbv = yval[ip] + (yval[ip+1] - yval[ip])*(inp        - xval[ip]) /
                                                       (xval[ip+1] - xval[ip]);

        if      ( fabs(inp - xval[ip  ]) <= dval[ip  ] )
        {
            prec->irbv = ip;
            strncpy( prec->lrbv, prec->labl+ip    *40, 40 );
        }
        else if ( fabs(inp - xval[ip+1]) <= dval[ip+1] )
        {
            prec->irbv = ip + 1;
            strncpy( prec->lrbv, prec->labl+(ip+1)*40, 40 );
        }
    }
    else
        recGblSetSevr( (dbCommon *)prec, STATE_ALARM, INVALID_ALARM );

    recGblResetAlarms( prec );

    if ( prec->rbv  != old_rbv  )
        db_post_events( prec, &prec->rbv,  DBE_VALUE | DBE_LOG );
    if ( prec->irbv != old_irbv )
        db_post_events( prec, &prec->irbv, DBE_VALUE | DBE_LOG );
    if ( strncmp(prec->lrbv, prec->orbv, 40) != 0 )
        db_post_events( prec,  prec->lrbv, DBE_VALUE | DBE_LOG );

    recGblFwdLink    ( prec );                  // process the forward scan link

    prec->proc = 0;
    prec->pact = FALSE;

    return( status );
}

static long special( dbAddr *pDbAddr, int after )
{
    lkupRecord  *prec = (lkupRecord *)pDbAddr->precord;
    int          ip, fieldIndex = dbGetFieldIndex( pDbAddr );
    double       out, *xval = prec->xval, *yval = prec->yval;
    long         status = 0;

    if ( after != TRUE )
    {
        if ( fieldIndex == lkupRecordIVAL ) prec->oval = prec->ival;

        return( status );
    }

    if      ( fieldIndex == lkupRecordNPTS )
    {
        if ( prec->npts > prec->nmax )
        {
            prec->npts = prec->nmax;
            db_post_events( prec, &prec->npts, DBE_VALUE | DBE_LOG );
        }
    }
    else if ( fieldIndex == lkupRecordVAL  )
    {
        if ( (prec->npts > 1) && (prec->init > 0) )
        {
            if      ( prec->val <  yval[0]            ) ip = 0;
            else if ( prec->val >= yval[prec->npts-1] ) ip = prec->npts - 2;
            else
                for ( ip = 0; ip < prec->npts-1; ip++ )
                    if ( (prec->val >= yval[ip  ]) &&
                         (prec->val <  yval[ip+1])    ) break;

            out = xval[ip] + (xval[ip+1] - xval[ip])*(prec->val  - yval[ip]) /
                                                     (yval[ip+1] - yval[ip]);
            if ( dbPutLink(&prec->out, DBR_DOUBLE, &out, 1) != 0 )
                recGblSetSevr( (dbCommon *)prec, COMM_ALARM, MAJOR_ALARM );
        }
    }
    else if ( fieldIndex == lkupRecordIVAL )
    {
        if ( (prec->npts > 0) && (prec->init > 0) )
        {
            if ( (prec->ival >= 0) && (prec->ival < prec->npts) )
            {
                out = xval[prec->ival];
                if ( dbPutLink(&prec->out, DBR_DOUBLE, &out, 1) != 0 )
                    recGblSetSevr( (dbCommon *)prec, COMM_ALARM, MAJOR_ALARM );
            }
            else
            {
                prec->ival = prec->oval;
                db_post_events( prec, &prec->ival, DBE_VALUE | DBE_LOG );
            }
        }
    }
    else if ( fieldIndex == lkupRecordLVAL )
    {
        if ( (prec->npts > 0) && (prec->init > 0) )
        {
            for ( ip = 0; ip < prec->npts; ip++ )
            {
                if ( strncmp(prec->labl+ip*40, prec->lval, 40) == 0 )
                {
                    out = xval[ip];
                    if ( dbPutLink(&prec->out, DBR_DOUBLE, &out, 1) != 0 )
                        recGblSetSevr( (dbCommon *)prec, COMM_ALARM,
                                                         MAJOR_ALARM );

                    break;
                }
            }
        }
    }
    else if ( fieldIndex == lkupRecordTWF  )
    {
        if ( (prec->npts > 1) && (prec->init > 0) )
        {
            if ( (prec->irbv >= 0) && (prec->irbv < prec->npts-1) )
            {
                prec->ival = prec->irbv + 1;
                strncpy( prec->lval, prec->labl+prec->ival*40, 40 );
                out        = xval[prec->ival];
                if ( dbPutLink(&prec->out, DBR_DOUBLE, &out, 1) != 0 )
                    recGblSetSevr( (dbCommon *)prec, COMM_ALARM, MAJOR_ALARM );

                db_post_events( prec, &prec->ival, DBE_VALUE | DBE_LOG );
                db_post_events( prec,  prec->lval, DBE_VALUE | DBE_LOG );
            }
        }
    }
    else if ( fieldIndex == lkupRecordTWR  )
    {
        if ( (prec->npts > 1) && (prec->init > 0) )
        {
            if ( (prec->irbv >  0) && (prec->irbv < prec->npts  ) )
            {
                prec->ival = prec->irbv - 1;
                strncpy( prec->lval, prec->labl+prec->ival*40, 40 );
                out        = xval[prec->ival];
                if ( dbPutLink(&prec->out, DBR_DOUBLE, &out, 1) != 0 )
                    recGblSetSevr( (dbCommon *)prec, COMM_ALARM, MAJOR_ALARM );

                db_post_events( prec, &prec->ival, DBE_VALUE | DBE_LOG );
                db_post_events( prec,  prec->lval, DBE_VALUE | DBE_LOG );
            }
        }
    }

    return( status );
}

static long cvt_dbaddr( dbAddr *pDbAddr )
{
    lkupRecord *prec = (lkupRecord *)pDbAddr->precord;
    int         fieldIndex = dbGetFieldIndex( pDbAddr );
    long        status = 0;

    switch ( fieldIndex )
    {
        case lkupRecordLABL:
        {
            pDbAddr->pfield         = prec->labl;
            pDbAddr->no_elements    = prec->npts;
            pDbAddr->field_type     = DBF_STRING;
            pDbAddr->field_size     = 40;
            pDbAddr->dbr_field_type = DBR_STRING;

            break;
        }
        case lkupRecordXVAL:
        {
            pDbAddr->pfield         = (epicsFloat64 *)prec->xval;
            pDbAddr->no_elements    = prec->npts;
            pDbAddr->field_type     = DBF_DOUBLE;
            pDbAddr->field_size     = sizeof(epicsFloat64);
            pDbAddr->dbr_field_type = DBR_DOUBLE;

            break;
        }
        case lkupRecordYVAL:
        {
            pDbAddr->pfield         = (epicsFloat64 *)prec->yval;
            pDbAddr->no_elements    = prec->npts;
            pDbAddr->field_type     = DBF_DOUBLE;
            pDbAddr->field_size     = sizeof(epicsFloat64);
            pDbAddr->dbr_field_type = DBR_DOUBLE;

            break;
        }
        case lkupRecordDVAL:
        {
            pDbAddr->pfield         = (epicsFloat64 *)prec->dval;
            pDbAddr->no_elements    = prec->npts;
            pDbAddr->field_type     = DBF_DOUBLE;
            pDbAddr->field_size     = sizeof(epicsFloat64);
            pDbAddr->dbr_field_type = DBR_DOUBLE;

            break;
        }
    }

    return( status );
}

