 #include <vecLib/vBLAS.h>
// #include "cblas.h"
// lets make it easy to just run this on macs
/* we assume we're given 3 nxn matrices*/
void simple_dgemm(double* c ,double* a,double* b, int n ){

    cblas_dgemm(CblasRowMajor,CblasNoTrans,CblasNoTrans,n,n,n, 1.0,a,n,b,n,1.0,c,n);
    
     ATLU_DestroyThreadMemory() ; // this is so that my benchmarks are more fair.
    }