// IEEE 1800-2023 Annex I — svdpi.h
// DPI C-layer include file (normative).
//
// All type names, function names, and constants in this file are MANDATED
// by the IEEE 1800-2023 standard and cannot be renamed.

#ifndef INCLUDED_SVDPI
#define INCLUDED_SVDPI

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>

// =============================================================================
// DLL import/export macros
// =============================================================================

#if (defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__))
#define DPI_DLLISPEC __declspec(dllimport)
#else
#define DPI_DLLISPEC
#endif

#if (defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__))
#define DPI_DLLESPEC __declspec(dllexport)
#else
#define DPI_DLLESPEC
#endif

#ifndef DPI_EXTERN
#define DPI_EXTERN
#endif

#ifndef DPI_PROTOTYPES
#define DPI_PROTOTYPES
#define XXTERN DPI_EXTERN DPI_DLLISPEC
#define EETERN DPI_EXTERN DPI_DLLESPEC
#endif

// =============================================================================
// Canonical representation of 4-state (logic) values
// =============================================================================

#define sv_0 0
#define sv_1 1
#define sv_z 2
#define sv_x 3

// =============================================================================
// Scalar types
// =============================================================================

typedef uint8_t svScalar;
typedef svScalar svBit;
typedef svScalar svLogic;

// =============================================================================
// Packed array element types
// =============================================================================

#ifndef VPI_VECVAL
#define VPI_VECVAL
typedef struct t_vpi_vecval {
  uint32_t aval;
  uint32_t bval;
} s_vpi_vecval, *p_vpi_vecval;
#endif

typedef s_vpi_vecval svLogicVecVal;
typedef uint32_t svBitVecVal;

// =============================================================================
// Packed array utility macros
// =============================================================================

#define SV_PACKED_DATA_NELEMS(WIDTH) (((WIDTH) + 31) >> 5)
#define SV_MASK(N) (~(~0u << (N)))
#define SV_GET_UNSIGNED_BITS(VALUE, N) \
  ((N) == 32 ? (VALUE) : ((VALUE) & SV_MASK(N)))
#define SV_GET_SIGNED_BITS(VALUE, N)                             \
  ((N) == 32 ? (VALUE)                                           \
             : (((VALUE) & (1 << (N))) ? ((VALUE) | ~SV_MASK(N)) \
                                       : ((VALUE) & SV_MASK(N))))

// =============================================================================
// VPI time structure (shared with VPI, guarded)
// =============================================================================

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
#endif

typedef s_vpi_time svTimeVal;
#define sv_scaled_real_time vpiScaledRealTime
#define sv_sim_time vpiSimTime

// =============================================================================
// Opaque handle types
// =============================================================================

typedef void* svScope;
typedef void* svOpenArrayHandle;

// =============================================================================
// Version query
// =============================================================================

XXTERN const char* svDpiVersion(void);

// =============================================================================
// Bit-select utility functions
// =============================================================================

XXTERN svBit svGetBitselBit(const svBitVecVal* s, int i);
XXTERN svLogic svGetBitselLogic(const svLogicVecVal* s, int i);
XXTERN void svPutBitselBit(svBitVecVal* d, int i, svBit s);
XXTERN void svPutBitselLogic(svLogicVecVal* d, int i, svLogic s);

// =============================================================================
// Part-select utility functions (w <= 32)
// =============================================================================

XXTERN void svGetPartselBit(svBitVecVal* d, const svBitVecVal* s, int i, int w);
XXTERN void svGetPartselLogic(svLogicVecVal* d, const svLogicVecVal* s, int i,
                              int w);
XXTERN void svPutPartselBit(svBitVecVal* d, svBitVecVal s, int i, int w);
XXTERN void svPutPartselLogic(svLogicVecVal* d, svLogicVecVal s, int i, int w);

// =============================================================================
// Open array querying functions
// =============================================================================

XXTERN int svLeft(svOpenArrayHandle h, int d);
XXTERN int svRight(svOpenArrayHandle h, int d);
XXTERN int svLow(svOpenArrayHandle h, int d);
XXTERN int svHigh(svOpenArrayHandle h, int d);
XXTERN int svIncrement(svOpenArrayHandle h, int d);
XXTERN int svSize(svOpenArrayHandle h, int d);
XXTERN int svDimensions(svOpenArrayHandle h);
XXTERN void* svGetArrayPtr(svOpenArrayHandle h);
XXTERN int svSizeOfArray(svOpenArrayHandle h);

// =============================================================================
// Open array element pointer access
// =============================================================================

XXTERN void* svGetArrElemPtr1(svOpenArrayHandle h, int indx1);
XXTERN void* svGetArrElemPtr2(svOpenArrayHandle h, int indx1, int indx2);
XXTERN void* svGetArrElemPtr3(svOpenArrayHandle h, int indx1, int indx2,
                              int indx3);

// =============================================================================
// Open array packed VecVal put/get
// =============================================================================

XXTERN void svPutBitArrElem1VecVal(svOpenArrayHandle d, const svBitVecVal* s,
                                   int indx1);
XXTERN void svPutBitArrElem2VecVal(svOpenArrayHandle d, const svBitVecVal* s,
                                   int indx1, int indx2);
XXTERN void svPutBitArrElem3VecVal(svOpenArrayHandle d, const svBitVecVal* s,
                                   int indx1, int indx2, int indx3);

XXTERN void svPutLogicArrElem1VecVal(svOpenArrayHandle d,
                                     const svLogicVecVal* s, int indx1);
XXTERN void svPutLogicArrElem2VecVal(svOpenArrayHandle d,
                                     const svLogicVecVal* s, int indx1,
                                     int indx2);
XXTERN void svPutLogicArrElem3VecVal(svOpenArrayHandle d,
                                     const svLogicVecVal* s, int indx1,
                                     int indx2, int indx3);

XXTERN void svGetBitArrElem1VecVal(svBitVecVal* d, svOpenArrayHandle s,
                                   int indx1);
XXTERN void svGetBitArrElem2VecVal(svBitVecVal* d, svOpenArrayHandle s,
                                   int indx1, int indx2);
XXTERN void svGetBitArrElem3VecVal(svBitVecVal* d, svOpenArrayHandle s,
                                   int indx1, int indx2, int indx3);

XXTERN void svGetLogicArrElem1VecVal(svLogicVecVal* d, svOpenArrayHandle s,
                                     int indx1);
XXTERN void svGetLogicArrElem2VecVal(svLogicVecVal* d, svOpenArrayHandle s,
                                     int indx1, int indx2);
XXTERN void svGetLogicArrElem3VecVal(svLogicVecVal* d, svOpenArrayHandle s,
                                     int indx1, int indx2, int indx3);

// =============================================================================
// Open array scalar element get/put
// =============================================================================

XXTERN svBit svGetBitArrElem1(svOpenArrayHandle s, int indx1);
XXTERN svBit svGetBitArrElem2(svOpenArrayHandle s, int indx1, int indx2);
XXTERN svBit svGetBitArrElem3(svOpenArrayHandle s, int indx1, int indx2,
                              int indx3);

XXTERN svLogic svGetLogicArrElem1(svOpenArrayHandle s, int indx1);
XXTERN svLogic svGetLogicArrElem2(svOpenArrayHandle s, int indx1, int indx2);
XXTERN svLogic svGetLogicArrElem3(svOpenArrayHandle s, int indx1, int indx2,
                                  int indx3);

XXTERN void svPutLogicArrElem1(svOpenArrayHandle d, svLogic value, int indx1);
XXTERN void svPutLogicArrElem2(svOpenArrayHandle d, svLogic value, int indx1,
                               int indx2);
XXTERN void svPutLogicArrElem3(svOpenArrayHandle d, svLogic value, int indx1,
                               int indx2, int indx3);

XXTERN void svPutBitArrElem1(svOpenArrayHandle d, svBit value, int indx1);
XXTERN void svPutBitArrElem2(svOpenArrayHandle d, svBit value, int indx1,
                             int indx2);
XXTERN void svPutBitArrElem3(svOpenArrayHandle d, svBit value, int indx1,
                             int indx2, int indx3);

// =============================================================================
// DPI context functions
// =============================================================================

XXTERN svScope svGetScope(void);
XXTERN svScope svSetScope(svScope scope);
XXTERN const char* svGetNameFromScope(svScope scope);
XXTERN svScope svGetScopeFromName(const char* scope_name);
XXTERN int svPutUserData(svScope scope, void* user_key, void* user_data);
XXTERN void* svGetUserData(svScope scope, void* user_key);
XXTERN int svGetCallerInfo(const char** file_name, int* line_number);
XXTERN int svIsDisabledState(void);
XXTERN void svAckDisabledState(void);

// =============================================================================
// Cleanup macros
// =============================================================================

#undef DPI_EXTERN
#ifdef DPI_PROTOTYPES
#undef DPI_PROTOTYPES
#undef XXTERN
#undef EETERN
#endif

#ifdef __cplusplus
}
#endif

#endif  // INCLUDED_SVDPI
