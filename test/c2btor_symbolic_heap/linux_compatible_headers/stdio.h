#ifndef C2BTOR_AIOB_STDIO_H
#define C2BTOR_AIOB_STDIO_H
/* Linux/i386 declarations for the preprocessed aiob_4 inputs.
   _IO_FILE below is copied verbatim from aiob_4.c, so the separate CBMC
   library translation unit sees the same complete FILE layout. */
#define NULL ((void *)0)
#define EOF (-1)
typedef long __off_t;
typedef long long __off64_t;
typedef void _IO_lock_t;
typedef unsigned int size_t;
struct _IO_FILE{
int  Id_MCDC_0;
char * Id_MCDC_1;
char * Id_MCDC_2;
char * Id_MCDC_3;
char * Id_MCDC_4;
char * Id_MCDC_5;
char * Id_MCDC_6;
char * Id_MCDC_7;
char * Id_MCDC_8;
char * Id_MCDC_9;
char * Id_MCDC_10;
char * Id_MCDC_11;
struct _IO_marker* Id_MCDC_12;
struct _IO_FILE* Id_MCDC_13;
int  Id_MCDC_14;
int  Id_MCDC_15;
__off_t Id_MCDC_16;
unsigned short  Id_MCDC_17;
signed char  Id_MCDC_18;
char  Id_MCDC_19 [1];
_IO_lock_t* Id_MCDC_20;
__off64_t Id_MCDC_21;
void * Id_MCDC_22;
void * Id_MCDC_23;
void * Id_MCDC_24;
void * Id_MCDC_25;
size_t Id_MCDC_26;
int  Id_MCDC_27;
char  Id_MCDC_28 [40];
} ;
typedef struct _IO_FILE FILE;
extern FILE *fopen(const char *, const char *);
extern int fclose(FILE *);
extern int printf(const char *, ...);
extern int fprintf(FILE *, const char *, ...);
extern int fflush(FILE *);
#endif
