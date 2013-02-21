#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>
#include <sched.h>
#include <unistd.h>
#include <sys/types.h>
#include <time.h>
#include <errno.h>

#ifdef PAPI
#include "pcounters.h"
#endif

#ifndef NULL
#define NULL   ((void *) 0)
#endif

#define ALG_BANKERS_DP 10
#define ALG_BANKERS_IDP 11
#define ALG_FSDP 12
#define ALG_FSIDP 13
#define ALG_PARALLELFSIDP 14

typedef struct  {
     int problemsize;
     long condition_evaluated;
     int result;	
} mstats;

/* GLOBAL VARIABLES */

int *values,n,datafromfile,datatofile=0,algorithm=ALG_FSIDP,reqthreads,nthreads;
char *filenameR,*filenameW;

/* HELPER FUNCTIONS FOR PRINTING, DEBUGGING & MEASURING */

void stringBM(int bm,int n, char *return_value) {
	int i,mask=1;
	int first=1;
	int len=0;

	sprintf(return_value,"%i {", bm);
	len=strlen(return_value);
	for (i=1;i<n+1;i++) {
		mask=1<<(i-1);
		if (mask & bm) {
			if (first) first=0;
			else sprintf(&return_value[len++],",");
			sprintf(&return_value[len],"%i",i);
			len=strlen(return_value);

		}
	}
	sprintf(&return_value[len++],"}");
}

void printBM(int bm, int n) {
	char ret[200];
	stringBM(bm,n,ret);
	printf("%s\n",ret);

}

double sampleTime()
{
	// Time in nanosec
        struct timespec tv;
        clock_gettime(CLOCK_REALTIME, &tv);
        return((tv.tv_sec+tv.tv_nsec/1000000000.0));
}
inline void Sample_SetCPU (int cpu_id)
{
    cpu_set_t   cpu_set;
    CPU_ZERO (&cpu_set);
    CPU_SET  (cpu_id, &cpu_set);
    sched_setaffinity (0, sizeof (cpu_set), &cpu_set);
}

int atoi_comment(char * line) {
	int i=0;
	while ((line[i]>='0') && (line[i]<='9')) i++;
	line[i]='\0';
	return atoi(line);

}

void IDPprintCoalition(int C, int n){
		printf("[ ");
		int i;
		for(i=0; i<n; i++)
			if((C & (1<<i)) != 0)
				printf("%i ",(i+1));
		printf("]");
}




/* HELPER FUNCTIONS TO PERFORM BINARY OPERATIONS AND ENUMERATIONS */

#define LOOKBIT(Word,bit) ((1<<(bit-1)) & Word)

inline unsigned int msbvalue(unsigned int a) {
	return LOOKBIT(a,((sizeof(unsigned int)<<3)-__builtin_clz(a)));
}

inline unsigned int removeHighBits(unsigned int p) {
/**** Remove the first 1's sequence 0001110010 -> 0000000010  */
	return ((msbvalue(~((~((msbvalue(p)<<1)-1)) | p))<<1) -1) & p;
}

inline unsigned int addOneBit(unsigned int mask, unsigned int p) {
/*****	Adds adds one bit from the left accoriding to a mask
        mask : 00111001    p: 00000001    -> 00001001 */
	return ((p | ~mask) + (msbvalue(p)<<1)) & mask;
}

inline unsigned int shiftHighestBit(unsigned int mask, int p) {
	return ((p | ~mask) + (msbvalue(p))) & mask;
}

inline unsigned int bankersFirstOne(unsigned int mask) {
	return (~mask+1) & mask; 
}

inline unsigned int removelsb(unsigned int bitMask) {
	return bitMask-(((~bitMask)+1) & bitMask);
}

unsigned int __BA_Mask;

inline unsigned int bankersFirstN(unsigned int mask, int n) {
	__BA_Mask=mask;
	int a=bankersFirstOne(mask);
	n--;
	while (n--) a=addOneBit(mask,a);
	return a;
}



inline unsigned int bankersNext(unsigned int p) {
	unsigned int m1 = msbvalue(__BA_Mask);
	unsigned int ret;
	if (m1&p) {
			int c=__builtin_popcount(p);
			ret=removeHighBits(p | ~__BA_Mask) & __BA_Mask;
			int c2=__builtin_popcount(p-ret);
			ret=shiftHighestBit(__BA_Mask,ret);
			while (c2--) ret=addOneBit(__BA_Mask,ret);
			if (c>__builtin_popcount(ret)) ret=0;
	} else ret= ((p | ~__BA_Mask) + msbvalue(p)) & __BA_Mask;
	return ret; 
}

unsigned int __FS_twoscomplement;
unsigned int __FS_Mask;

inline unsigned int FSFirst(unsigned int mask) {
	__FS_twoscomplement=~mask+1;
	__FS_Mask=mask;
    return __FS_twoscomplement & mask;
}

inline unsigned int FSNext(unsigned int p) {
	return (__FS_twoscomplement + p) & __FS_Mask;
}

inline getIDPBounds(int n, int i, int *lower_bound, int *upper_bound) {
	if ((i<((n/2)+1)) || (i==n)){
			*lower_bound=1;
			*upper_bound=i;
	} else {
			*lower_bound=2*i-n;
			*upper_bound=n-i+1;
	}
}


// This fuctions works good for a<30, it can be improved for bigger numbers
// In particular there exists an overflow error when performing operations on ret
long long binom(int a, int b) {
	int dif=((a-b)>b)?b:a-b;
	int i;
	long long ret=1;
	for (i=1;i<=dif;i++) {
			ret=ret*(a--)/i;
	}
	return ret;
}

unsigned int getComb(int n,int s,int item) {

	int n2;
	int highb;
	unsigned int BM=0;
	int bitsleft=s;

	if (item>binom(n,s)) return -1;
	for (n2=1;n2<=n;n2++) {
		highb = binom(n-n2,bitsleft-1);
		if (bitsleft)
			if ((item <= highb)) {
				BM+= (1<<(n2-1));
				bitsleft--;
			} else item-=highb;
		else return BM;
	}
	return BM;
}

unsigned int getNext(int n, int s, unsigned int current) {
    int int_size= sizeof(unsigned int) << 3;
    unsigned int pos = (int_size -  __builtin_clz (current));
    if (pos==n) {

    	int a=~((current | (~0)<<n));
        int b=int_size - __builtin_clz(~(((~0)<<int_size-__builtin_clz(a))+a));
        unsigned int m = ((1<<(b))-1) & current;
        int p=__builtin_popcount(m);
        if (p==0) return -1;
        return m-(1<<(b-1))+(((2<<s-p)-1) << b);
    }
	return current +  (1 << (pos-1));
}



#define INT_MAX_VALUE 2147483648

int *GenerateProblem(int *problem, int n) {
	int i,end = (1<<n);
	int max = INT_MAX_VALUE/n;
	for (i=1;i<end;i++) {
		problem[i]= rand()%(max*__builtin_popcount(i));
	}
	return problem;
}

int ProblemWrite(int *problem,int n,char *outputFile) {
	FILE *fp;
	char BM[200];
	int i=0;
	int limit=(1<<n);
	fp = fopen(outputFile,"r");
	if( fp ) {
		fclose(fp);
		return 0; // File aready exists
	} else {
		fp = fopen(outputFile,"w");
		for (i=0;i<limit;i++) {
	    	stringBM(i,n,BM);
			fprintf(fp,"%i #%s\n",problem[i],BM);
		}
		fclose(fp);
		return 1; // OK
	}
}

int ProblemRead(int *problem,int n, char *inputFile) {
	FILE *fp;
	char line[500],*fg;
	int limit=(1<<n);
	int i=0;
	printf("Reading file %s\n",inputFile);
	fp = fopen(inputFile,"r");
	if (fp==NULL) {
		printf("%s\n",strerror(errno));
		return 0; // File doesn't exists
	}
	for(i=0;i<limit;i++) {
		fg=fgets(line,500,fp);
		
		problem[i]=atoi_comment(line);
	}
	fclose(fp);
	return 1;
}


int findCS_DP(int *OptimalCS,int mask) {
	unsigned int ca2, set1, set2,j,found;
	ca2=~mask+1;
	set1=0;

	int topvalue=values[mask];

	int combinations=(1<<(__builtin_popcount(mask)-1))-1;
	for (j=1;j<=combinations;j++) {

		set1=(ca2 + set1) & mask;
		set2=mask-set1;
		if (values[set1]+values[set2]==topvalue) {
			found=1;
			int subset1,subset2;
			subset1=findCS_DP(OptimalCS,set1);
			subset2=findCS_DP(&OptimalCS[subset1],set2);
			return subset1+subset2;
		}
	}
	if (!found) {
		*OptimalCS=mask;
		return 1;
	}
	return -1; 

}

int findSolution(int *values,int n) {
	int full = (1 << n) -1;
	int OptimalValue = ((int) values[full]);
	int *OptimalCS = (int*) malloc(sizeof(int)*(n));
	int numCoalitions = findCS_DP(OptimalCS, full);
	int i; 
	for(i = numCoalitions; i<n; i++) OptimalCS[i] = -1;
	
	printf("%i %i ",n , OptimalValue);
	for(i=0; (i<n) && (OptimalCS[i]>0); i++){
		printf(" ");
		IDPprintCoalition(OptimalCS[i],n);
	}
	printf("\n");
	return OptimalValue;
}

mstats* bankersDP() {
    int i,l;
    int c,tmp,max,ini;
    unsigned int bitMask,set1,set2;
    long totcombinations;

    mstats *a=malloc(sizeof(mstats));
    a->problemsize=n;
    a->condition_evaluated=0;
    a->result=0;

    for (i=2; i<=n; i++) {
        totcombinations=binom(n,i);
        bitMask=getComb(n,i,1);
        for (c=0; c<totcombinations; c++) {
            ini=values[bitMask];
            max=ini;
 			for (l=1;l<i;l++) {
				set1=bankersFirstN(removelsb(bitMask),l); 
            	do {
                    #ifdef STATS_ON
		            	a->condition_evaluated++;
					#endif	
                	set2=bitMask-set1;
                	tmp=values[set1]+values[set2];
                	if (tmp>max) max=tmp;
					set1=bankersNext(set1);
				} while (set1);
            	if (max>ini) values[bitMask]=max;
       		}
            bitMask=getNext(n,i,bitMask);
        }
    }
    a->result=findSolution(values,n);
    return a;

}


mstats* bankersIDP() {
    int lower_bound,upper_bound,i,l;
    int c,tmp,max,ini;
    unsigned int bitMask,set1,set2;
    long totcombinations;

    mstats *a=malloc(sizeof(mstats));
    a->problemsize=n;
    a->condition_evaluated=0;
    a->result=0;

    for (i=2; i<=n; i++) { 	     
        totcombinations=binom(n,i);
        bitMask=getComb(n,i,1);
		getIDPBounds(n,i,&lower_bound, &upper_bound);
      	for (c=0; c<totcombinations; c++) {
            max=values[bitMask];
            ini=max;
			for (l=lower_bound;l<upper_bound;l++) {
				set1=bankersFirstN(removelsb(bitMask),l);
				while (set1) {
					#ifdef STATS_ON
		            	a->condition_evaluated++;
					#endif
	                set2=bitMask-set1;
	                tmp=values[set1]+values[set2];
	                if (tmp>max) max=tmp;
					set1=bankersNext(set1);
				}
		    }
            if (max>ini) values[bitMask]=max;
            bitMask=getNext(n,i,bitMask);
        }
    }
    a->result=findSolution(values,n);
    return a;
}


mstats* FSDP() {
    int i,c,tmp,max,ini;
    unsigned int ca2,bitMask,set1,set2;
    long totcombinations;

    mstats *a=malloc(sizeof(mstats));
    a->problemsize=n;
    a->condition_evaluated=0;
    a->result=0;

    for (i=2; i<=n; i++) {
        totcombinations=binom(n,i);
        bitMask=getComb(n,i,1);
        for (c=0; c<totcombinations; c++) {
            ini=values[bitMask];
            max=ini;
			set1=FSFirst(removelsb(bitMask));
            do {
		        #ifdef STATS_ON
		           	a->condition_evaluated++;
				#endif
                set2=bitMask-set1;
                tmp=values[set1]+values[set2];
                if (tmp>max) max=tmp;
				set1=FSNext(set1);				
			} while (set1);
            if (max>ini) values[bitMask]=max;
            bitMask=getNext(n,i,bitMask);
        }
    }
    a->result=findSolution(values,n);
    return a;

}

mstats* FSIDP() {
    int i,s1,lower_bound,upper_bound;
    int c,tmp,max,ini;
    unsigned int ca2,bitMask,set1,set2;
    long totcombinations;

    mstats *a=malloc(sizeof(mstats));
    a->problemsize=n;
    a->condition_evaluated=0;
    a->result=0;

    for (i=2; i<=n; i++) {
        totcombinations=binom(n,i);
        bitMask=getComb(n,i,1);
	    getIDPBounds(n,i,&lower_bound, &upper_bound);
        for (c=0; c<totcombinations; c++) {
            ini=values[bitMask];
            max=ini;
			set1=FSFirst(removelsb(bitMask));
            do {
                s1=__builtin_popcount(set1);
				if ((s1>=lower_bound) && (s1<upper_bound))   {
                    #ifdef STATS_ON
		            	a->condition_evaluated++;
					#endif
					set2=bitMask-set1;
					tmp=values[set1]+values[set2];
                    if (tmp>max) max=tmp;
                } 
				set1=FSNext(set1);                    
			} while (set1);
            if (max>ini) values[bitMask]=max;
            bitMask=getNext(n,i,bitMask);
        }
    }
    a->result=findSolution(values,n);
    return a;
}


mstats* ParalelFSIDP(int reqthreads) {
    int i,s1,lower_bound,upper_bound,c;
    long totcombinations,threadcombinations;

    mstats *a=malloc(sizeof(mstats));
    a->problemsize=n;
    a->condition_evaluated=0;
    a->result=0;

    nthreads=omp_get_max_threads();
    if ((reqthreads<nthreads) && (reqthreads!=0)) nthreads=reqthreads;
    omp_set_num_threads(nthreads);

    for (i=2; i<=n; i++) {
        totcombinations=binom(n,i);
        threadcombinations=(totcombinations/nthreads)+1;
        getIDPBounds(n,i,&lower_bound, &upper_bound);
        #pragma omp parallel if (i>5) 
        {
			unsigned int bitMask,set1,set2,twoscomplement,subMask;
			int ini,tmp,max,threadidx,s1,firstiteration=1;
            threadidx=omp_get_thread_num();
            bitMask=getComb(n,i,1);
            #pragma omp for schedule (static,threadcombinations)
            for (c=0; c<totcombinations; c++) {
                threadidx=omp_get_thread_num();
                if (firstiteration) {
                    firstiteration=0;
                    bitMask=getComb(n,i,c+1);
                } else bitMask=getNext(n,i,bitMask);
	            ini=values[bitMask];
	            max=ini;
				subMask=removelsb(bitMask);
				twoscomplement=~subMask+1;
                set1=twoscomplement & subMask;
				do {
					s1=__builtin_popcount(set1);
	                if ((s1<upper_bound) && (s1>=lower_bound)) {
						#ifdef STATS_ON			           
							#pragma omp atomic
			   		    	a->condition_evaluated++;
                    	#endif
						set2=bitMask-set1;
                    	tmp=values[set1]+values[set2];
                    	if (tmp>max) max=tmp;
					}
				    set1=(twoscomplement + set1) & subMask;
				} while (set1);
                if (max>ini) values[bitMask]=max;
            }
        }
    }
  //  a->result=findSolution(values,n);
	findSolution(values,n);
    return a;
}
int check_params(int argc, char *argv[]) {
    int i,ret=0;
    int optn,optg,optr,optw,opta,opto,opth;
    optn=optg=optr=optw=opto=opta=opth=0;
    for (i=1; i<argc; i++) {
        if (argv[i][0] == '-') {
            switch (argv[i][1]) {
            case 'n':
                optn=1;
                n=atoi(&argv[i][2]);
                if ((n>1) && (n<31)) ret=1;
                else {
                    printf("Invalid n\n",&argv[i][2]);
                    return 0;
                }
                break;
            case 'g':
                optg=1;
                datafromfile=0;
                ret=1;
                break;
            case 'r':
                optr=1;
                datafromfile=1;
                FILE *fr;
                filenameR=&argv[i][2];

                fr=fopen(filenameR,"r");
                if (!fr) {
                    printf("File not found\n");
                    return 0;
                } else {
                    fclose(fr);
                    ret=1;
                }
                break;
            case 'w':
                optw=1;
                datatofile=1;
                datafromfile=0;
                FILE *fw;
                filenameW=&argv[i][2];
                fw=fopen(filenameW,"r");
                if (fw) {
                    printf("Error creating file: file exists\n");
                    return 0;
                    fclose(fw);

                } else {
                    ret=1;
                }
                break;
		    case 'a':
	             opta=1;
				 int alg;
	             alg=atoi(&argv[i][2]);
	             if ((alg>0) && (alg<5)) {
					ret=1;
					switch (alg) {
						case 1: algorithm=ALG_BANKERS_DP;  break;
						case 2: algorithm=ALG_BANKERS_IDP; break;
						case 3: algorithm=ALG_FSDP;  break;
						case 4: algorithm=ALG_FSIDP; break;												
					}
	             } else {
	                 printf("Invalid algorithm\n");
	                 return 0;
	             }
	             break;	
           case 'o':
                opto=1;

                if (strlen(&argv[i][1])==1) reqthreads=0;
                else reqthreads=atoi(&argv[i][2]);
                algorithm=ALG_PARALLELFSIDP;
                ret=1;
                break;


            case 'h' :
                opth=1;
            default:
                printf("%s -n<agents> [-g|-r<file>] [-a[1|2|3|4] | -o<threads>]\n",argv[0]);
                printf("%s -n<agents> -w<file>\n",argv[0]);
                printf("%s -h\n",argv[0]);
                printf("\nOptions\n");
                printf("-h       : This help\n");
                printf("-w<file> : just generate date and write it to a file.\n");
                printf("\nRUNNING ALGORITHMS\n");
                printf("-n<number> : number of combinatorial agents\n");
                printf("-g         : Generate random data\n");
                printf("-r<file>   : read data from file\n");
				printf("\n");	
                printf("AVAILABLE ALGORITHMS\n");
                printf("-a1 : Run DP using banker's sequence\n");
                printf("-a2 : Run IDP using banker's sequence\n");
                printf("-a3 : Run DP using Fast Split\n");
				printf("-a4 : Run IDP using Fast Split\n");
                printf("-o<threads>  : Run Paralel IDP using Fast Split.  \n");
				printf("             : 0 threads = autodetect. \n");



                ret=0;
                exit(0);
                break;
            }
        } else {
            printf("invalid option: %s\n",argv[i]);
            ret=0;
        }
    }


    if ((optg) && (optr)) {
        printf("Options -g and -r are incompatible\n");
        ret=0;
    }
    if (optn==0) {
        printf("Must specify number of elements (-h for help)\n");
        ret=0;
    }
    if (opta + opto  > 1) {
        printf("You can only select one running algorithm\n");
        ret=0;
    }

    return ret;
}


int main(int argc, char *argv[]) {
    double t0,t1;

   
    srand(time(NULL));
    if (check_params(argc,argv)) {
        values=(int *) malloc(sizeof(int)*((1<<n)));
        if (datafromfile) {
            if (!ProblemRead(values,n,filenameR)) {
                printf("File read error\n");
                return;
            }
        } else values=GenerateProblem(values,n);
        if (datatofile) {
            ProblemWrite(values,n,filenameW);
        } else {
			#ifdef PAPI
            	PAPI_Init();
            	if (algorithm==ALG_PARALLELFSIDP) PAPI_OMP_Init(omp_get_max_threads());
			#endif
            printf("Size %i\n",n);
			#ifdef PAPI
            	if (algorithm)
                	PAPI_On();

			#endif
			t0=sampleTime();
			mstats *results;
            switch (algorithm) {
            case ALG_BANKERS_DP:
                printf("Running DP using banker's sequence\n");
                results=bankersDP();
                break;
            case ALG_BANKERS_IDP:
                printf("Running IDP using banker's sequence\n");
				results=bankersIDP();
                break;
            case ALG_FSDP:
                printf("Running DP using Fast Split\n");
                results=FSDP();
                break;
            case ALG_FSIDP:
                printf("Running IDP using Fast Split\n");
                results=FSIDP();
                break;
            case ALG_PARALLELFSIDP:
                printf("Running Paralel IDP using Fast Split\n");
                results=ParalelFSIDP(reqthreads);
                break;

            }

			#ifdef PAPI
            	PAPI_Off();
            	char * papi_results=PAPI_results();
			#else
            	char papi_results[1];
            	papi_results[0]='\0';
			#endif

            t1=sampleTime();
            printf("Execution time : %f\n",t1-t0);
            FILE *fstats=fopen("stats.txt","a");
            if (algorithm==ALG_PARALLELFSIDP)
                fprintf(fstats,"%i,%i,%i,%f%s\n",n,algorithm,nthreads,t1-t0,papi_results);
            else fprintf(fstats,"%i,%i,-,%f%s\n",n,algorithm,t1-t0,papi_results);
            fclose(fstats);	
		

        }
    }

    return EXIT_SUCCESS;
}

