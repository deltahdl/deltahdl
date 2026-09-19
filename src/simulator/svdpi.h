/*
 * svdpi.h
 *
 * SystemVerilog Direct Programming Interface (DPI).
 *
 * This file contains the constant definitions, structure definitions,
 * and routine declarations used by SystemVerilog DPI.
 */

#ifndef INCLUDED_SVDPI
#define INCLUDED_SVDPI

#ifdef __cplusplus
extern "C" {
#endif

/* Define size-critical types on all OS platforms. */
/* Annex I.2 has an implementation define uint8_t and uint32_t by a method
 * of its own, the platform selection Annex I.3 prints here being suggested
 * and not prescribed; this implementation takes both from <stdint.h>. */
#include <stdint.h>

/* Use to import a symbol into dll */
#if (defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__))
#define DPI_DLLISPEC __declspec(dllimport)
#else
#define DPI_DLLISPEC
#endif

/* Use to export a symbol from dll */
#if (defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__))
#define DPI_DLLESPEC __declspec(dllexport)
#else
#define DPI_DLLESPEC
#endif

/* Use to mark a function as external */
#ifndef DPI_EXTERN
#define DPI_EXTERN
#endif

#ifndef DPI_PROTOTYPES
#define DPI_PROTOTYPES
/* object is defined imported by the application */
#define XXTERN DPI_EXTERN DPI_DLLISPEC
/* object is exported by the application */
#define EETERN DPI_EXTERN DPI_DLLESPEC
#endif

/* canonical representation */
#define sv_0 0
#define sv_1 1
#define sv_z 2
#define sv_x 3

/* common type for 'bit' and 'logic' scalars. */
typedef uint8_t svScalar;
typedef svScalar svBit;   /* scalar */
typedef svScalar svLogic; /* scalar */

/*
 * DPI representation of packed arrays.
 * 2-state and 4-state vectors, exactly the same as PLI's avalue/bvalue.
 */
#ifndef VPI_VECVAL
#define VPI_VECVAL
typedef struct t_vpi_vecval {
  uint32_t aval;
  uint32_t bval;
} s_vpi_vecval, *p_vpi_vecval;
#endif

/* (a chunk of) packed logic array */
typedef s_vpi_vecval svLogicVecVal;

/* (a chunk of) packed bit array */
typedef uint32_t svBitVecVal;

/* Number of chunks required to represent the given width packed array */
#define SV_PACKED_DATA_NELEMS(WIDTH) (((WIDTH) + 31) >> 5)

/*
 * Because the contents of the unused bits is undetermined,
 * the following macros can be handy.
 */
#define SV_MASK(N) (~(-1 << (N)))
#define SV_GET_UNSIGNED_BITS(VALUE, N) \
  ((N) == 32 ? (VALUE) : ((VALUE) & SV_MASK(N)))
#define SV_GET_SIGNED_BITS(VALUE, N)                             \
  ((N) == 32 ? (VALUE)                                           \
             : (((VALUE) & (1 << (N))) ? ((VALUE) | ~SV_MASK(N)) \
                                       : ((VALUE) & SV_MASK(N))))

#ifndef VPI_TIME
#define VPI_TIME
typedef struct t_vpi_time {
  int32_t type;
  uint32_t high;
  uint32_t low;
  double real;
} s_vpi_time, *p_vpi_time;
#define vpiScaledRealTime 1
#define vpiSimTime 2
#define vpiSuppressTime 3
#endif

/* time value */
typedef s_vpi_time svTimeVal;

/* time value types */
#define sv_scaled_real_time vpiScaledRealTime
#define sv_sim_time vpiSimTime

/*
 * Implementation-dependent representation.
 */
/*
 * Return implementation version information string ("1800-2005" or "SV3.1a").
 */
XXTERN const char* svDpiVersion(void);

/* a handle to a scope (an instance of a module or interface) */
XXTERN typedef void* svScope;

/* a handle to a generic object (actually, unsized array) */
XXTERN typedef void* svOpenArrayHandle;

/*
 * Bit-select utility functions.
 *
 * Packed arrays are assumed to be indexed n-1:0,
 * where 0 is the index of LSB
 */

/* s=source, i=bit-index */
XXTERN svBit svGetBitselBit(const svBitVecVal* s, int i);
XXTERN svLogic svGetBitselLogic(const svLogicVecVal* s, int i);

/* d=destination, i=bit-index, s=scalar */
XXTERN void svPutBitselBit(svBitVecVal* d, int i, svBit s);
XXTERN void svPutBitselLogic(svLogicVecVal* d, int i, svLogic s);

/*
 * Part-select utility functions.
 *
 * A narrow (<=32 bits) part-select is extracted from the
 * source representation and written into the destination word.
 *
 * Normalized ranges and indexing [n-1:0] are used for both arrays.
 *
 * s=source, d=destination, i=starting bit index, w=width
 * like for variable part-selects; limitations: w <= 32
 */
XXTERN void svGetPartselBit(svBitVecVal* d, const svBitVecVal* s, int i, int w);
XXTERN void svGetPartselLogic(svLogicVecVal* d, const svLogicVecVal* s, int i,
                              int w);

XXTERN void svPutPartselBit(svBitVecVal* d, const svBitVecVal s, int i, int w);
XXTERN void svPutPartselLogic(svLogicVecVal* d, const svLogicVecVal s, int i,
                              int w);

/*
 * Open array querying functions
 * These functions are modeled upon the SystemVerilog array
 * querying functions and use the same semantics.
 *
 * If the dimension is 0, then the query refers to the
 * packed part of an array (which is one-dimensional).
 * Dimensions > 0 refer to the unpacked part of an array.
 */
/* h= handle to open array, d=dimension */
XXTERN int svLeft(const svOpenArrayHandle h, int d);
XXTERN int svRight(const svOpenArrayHandle h, int d);
XXTERN int svLow(const svOpenArrayHandle h, int d);
XXTERN int svHigh(const svOpenArrayHandle h, int d);
XXTERN int svIncrement(const svOpenArrayHandle h, int d);
XXTERN int svSize(const svOpenArrayHandle h, int d);
XXTERN int svDimensions(const svOpenArrayHandle h);

/*
 * Pointer to the actual representation of the whole array of any type
 * NULL if not in C layout
 */
XXTERN void* svGetArrayPtr(const svOpenArrayHandle);

/* total size in bytes or 0 if not in C layout */
XXTERN int svSizeOfArray(const svOpenArrayHandle);

/*
 * Return a pointer to an element of the array
 * or NULL if index outside the range or null pointer
 */
XXTERN void* svGetArrElemPtr(const svOpenArrayHandle, int indx1, ...);

/* specialized versions for 1-, 2- and 3-dimensional arrays: */
XXTERN void* svGetArrElemPtr1(const svOpenArrayHandle, int indx1);
XXTERN void* svGetArrElemPtr2(const svOpenArrayHandle, int indx1, int indx2);
XXTERN void* svGetArrElemPtr3(const svOpenArrayHandle, int indx1, int indx2,
                              int indx3);

/*
 * Functions for copying between simulator storage and user space.
 * These functions copy the whole packed array in either direction.
 * The user is responsible for allocating an array to hold the
 * canonical representation.
 */

/* s=source, d=destination */
/* From user space into simulator storage */
XXTERN void svPutBitArrElemVecVal(const svOpenArrayHandle d,
                                  const svBitVecVal* s, int indx1, ...);
XXTERN void svPutBitArrElem1VecVal(const svOpenArrayHandle d,
                                   const svBitVecVal* s, int indx1);
XXTERN void svPutBitArrElem2VecVal(const svOpenArrayHandle d,
                                   const svBitVecVal* s, int indx1, int indx2);
XXTERN void svPutBitArrElem3VecVal(const svOpenArrayHandle d,
                                   const svBitVecVal* s, int indx1, int indx2,
                                   int indx3);

XXTERN void svPutLogicArrElemVecVal(const svOpenArrayHandle d,
                                    const svLogicVecVal* s, int indx1, ...);
XXTERN void svPutLogicArrElem1VecVal(const svOpenArrayHandle d,
                                     const svLogicVecVal* s, int indx1);
XXTERN void svPutLogicArrElem2VecVal(const svOpenArrayHandle d,
                                     const svLogicVecVal* s, int indx1,
                                     int indx2);
XXTERN void svPutLogicArrElem3VecVal(const svOpenArrayHandle d,
                                     const svLogicVecVal* s, int indx1,
                                     int indx2, int indx3);

/* From simulator storage into user space */
XXTERN void svGetBitArrElemVecVal(svBitVecVal* d, const svOpenArrayHandle s,
                                  int indx1, ...);
XXTERN void svGetBitArrElem1VecVal(svBitVecVal* d, const svOpenArrayHandle s,
                                   int indx1);
XXTERN void svGetBitArrElem2VecVal(svBitVecVal* d, const svOpenArrayHandle s,
                                   int indx1, int indx2);
XXTERN void svGetBitArrElem3VecVal(svBitVecVal* d, const svOpenArrayHandle s,
                                   int indx1, int indx2, int indx3);

XXTERN void svGetLogicArrElemVecVal(svLogicVecVal* d, const svOpenArrayHandle s,
                                    int indx1, ...);
XXTERN void svGetLogicArrElem1VecVal(svLogicVecVal* d,
                                     const svOpenArrayHandle s, int indx1);
XXTERN void svGetLogicArrElem2VecVal(svLogicVecVal* d,
                                     const svOpenArrayHandle s, int indx1,
                                     int indx2);
XXTERN void svGetLogicArrElem3VecVal(svLogicVecVal* d,
                                     const svOpenArrayHandle s, int indx1,
                                     int indx2, int indx3);

XXTERN svBit svGetBitArrElem(const svOpenArrayHandle s, int indx1, ...);
XXTERN svBit svGetBitArrElem1(const svOpenArrayHandle s, int indx1);
XXTERN svBit svGetBitArrElem2(const svOpenArrayHandle s, int indx1, int indx2);
XXTERN svBit svGetBitArrElem3(const svOpenArrayHandle s, int indx1, int indx2,
                              int indx3);

XXTERN svLogic svGetLogicArrElem(const svOpenArrayHandle s, int indx1, ...);
XXTERN svLogic svGetLogicArrElem1(const svOpenArrayHandle s, int indx1);
XXTERN svLogic svGetLogicArrElem2(const svOpenArrayHandle s, int indx1,
                                  int indx2);
XXTERN svLogic svGetLogicArrElem3(const svOpenArrayHandle s, int indx1,
                                  int indx2, int indx3);

XXTERN void svPutLogicArrElem(const svOpenArrayHandle d, svLogic value,
                              int indx1, ...);
XXTERN void svPutLogicArrElem1(const svOpenArrayHandle d, svLogic value,
                               int indx1);
XXTERN void svPutLogicArrElem2(const svOpenArrayHandle d, svLogic value,
                               int indx1, int indx2);
XXTERN void svPutLogicArrElem3(const svOpenArrayHandle d, svLogic value,
                               int indx1, int indx2, int indx3);

XXTERN void svPutBitArrElem(const svOpenArrayHandle d, svBit value, int indx1,
                            ...);
XXTERN void svPutBitArrElem1(const svOpenArrayHandle d, svBit value, int indx1);
XXTERN void svPutBitArrElem2(const svOpenArrayHandle d, svBit value, int indx1,
                             int indx2);
XXTERN void svPutBitArrElem3(const svOpenArrayHandle d, svBit value, int indx1,
                             int indx2, int indx3);

/* Functions for working with DPI context */

/* The comments Annex I.3 prints on the eleven functions below are
 * paraphrased here; §H.9.2 through §H.9.4 are where the standard states
 * their semantics. */

/* The instance scope of the executing imported function: its declaration
 * site's scope unless svSetScope was called first, and NULL from C code that
 * is not an imported function. */
XXTERN svScope svGetScope(void);

/* Sets the scope for the export functions called next; an export function
 * called while an import executes inherits that import's scope, the
 * "default scope", without a call. Returns the scope that was active. */
XXTERN svScope svSetScope(const svScope scope);

/* The fully qualified name of a scope handle. */
XXTERN const char* svGetNameFromScope(const svScope);

/* The scope of an arbitrary function declaration (module, program,
 * interface or generate scope); NULL for a name not recognized. */
XXTERN svScope svGetScopeFromName(const char* scopeName);

/* Store a user data pointer under a key the user makes unique, the address
 * of a static function or variable being the recommended key; NULL is not
 * a valid scope, key or data, and 0 is a data value to avoid, since
 * svGetUserData cannot then tell it from an error. Returns 0 on success
 * and -1 on error, an invalid scope being one. */
XXTERN int svPutUserData(const svScope scope, void* userKey, void* userData);

/* Retrieve what svPutUserData stored under the key, subject to the same
 * rules on scope and key; NULL when nothing was stored or on error. */
XXTERN void* svGetUserData(const svScope scope, void* userKey);

/* The SV file and line the import was called from, when the implementation
 * makes them available: returns TRUE and sets both, or FALSE and sets
 * neither. The string is the implementation's, valid until the next call
 * into SV, and not the application's to modify or free. */
XXTERN int svGetCallerInfo(const char** fileName, int* lineNumber);

/* 1 while the executing thread is in the disabled state, in which the
 * disable protocol is to be followed. */
XXTERN int svIsDisabledState(void);

/* Called by an imported function before it returns while in the disabled
 * state, to acknowledge that it took part in the protocol. */
XXTERN void svAckDisabledState(void);

/* The current simulation time scaled to the scope's time unit, or to the
 * simulation time unit when scope is NULL; an invalid scope is an error.
 * Returns 0 on success and -1 on error. */
XXTERN int svGetTime(const svScope scope, svTimeVal* time);

/* The scope's time unit, or the simulation time unit when scope is NULL;
 * an invalid scope is an error. Returns 0 on success and -1 on error. */
XXTERN int svGetTimeUnit(const svScope scope, int32_t* time_unit);

/* The scope's time precision, or the simulation time unit when scope is
 * NULL; an invalid scope is an error. Returns 0 on success and -1 on
 * error. */
XXTERN int svGetTimePrecision(const svScope scope, int32_t* time_precision);

/* Annex I.3 ends the file with a deprecated portion, the SV3.1a-compatible
 * packed data access of §H.14, delimited by comments; Annex I.2 has a
 * simulator provide the file without that portion, and this one does,
 * offering those definitions beside the file in svdpi_sv31a.h instead. */

#undef DPI_EXTERN
#ifdef DPI_PROTOTYPES
#undef DPI_PROTOTYPES
#undef XXTERN
#undef EETERN
#endif

#ifdef __cplusplus
}
#endif

#endif
