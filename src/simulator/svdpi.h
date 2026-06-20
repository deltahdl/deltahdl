

#ifndef INCLUDED_SVDPI
#define INCLUDED_SVDPI

#ifdef __cplusplus
extern "C" {
#endif

#include <stddef.h>
#include <stdint.h>

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

#define sv_0 0
#define sv_1 1
#define sv_z 2
#define sv_x 3

typedef uint8_t svScalar;
typedef svScalar svBit;
typedef svScalar svLogic;

#ifndef VPI_VECVAL
#define VPI_VECVAL
typedef struct t_vpi_vecval {
  uint32_t aval;
  uint32_t bval;
} s_vpi_vecval, *p_vpi_vecval;
#endif

typedef s_vpi_vecval svLogicVecVal;
typedef uint32_t svBitVecVal;

#define SV_PACKED_DATA_NELEMS(WIDTH) (((WIDTH) + 31) >> 5)
#define SV_MASK(N) (~(~0u << (N)))
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
#endif

typedef s_vpi_time svTimeVal;
#define sv_scaled_real_time vpiScaledRealTime
#define sv_sim_time vpiSimTime

typedef void* svScope;
typedef void* svOpenArrayHandle;

// Backing representation an svOpenArrayHandle points to. The array querying
// functions of Annex H.12.2 are modeled on the SystemVerilog array querying
// functions (20.7), so each dimension is described by its declared left and
// right bounds; low/high/size/increment are then derived exactly as 20.7
// defines them. The dimension at index 0 describes the single packed part of
// the array and the dimensions at indices greater than 0 describe the unpacked
// part, following H.12.2's dimension-numbering convention.
typedef struct svOpenArrayDimRange {
  int left;
  int right;
} svOpenArrayDimRange;

// elem_size is the byte stride of one array element within the actual
// representation that data points at. Annex H.12.4's element-address functions
// use it to step between consecutive elements. A value of 0 marks an element
// representation that differs from that of an individual value of the same
// type, for which H.12.4 requires those functions to return a null pointer.
typedef struct svOpenArrayDesc {
  void* data;
  int n_dims;
  const svOpenArrayDimRange* ranges;
  size_t elem_size;
} svOpenArrayDesc;

XXTERN const char* svDpiVersion(void);

XXTERN svBit svGetBitselBit(const svBitVecVal* s, int i);
XXTERN svLogic svGetBitselLogic(const svLogicVecVal* s, int i);
XXTERN void svPutBitselBit(svBitVecVal* d, int i, svBit s);
XXTERN void svPutBitselLogic(svLogicVecVal* d, int i, svLogic s);

XXTERN void svGetPartselBit(svBitVecVal* d, const svBitVecVal* s, int i, int w);
XXTERN void svGetPartselLogic(svLogicVecVal* d, const svLogicVecVal* s, int i,
                              int w);
XXTERN void svPutPartselBit(svBitVecVal* d, svBitVecVal s, int i, int w);
XXTERN void svPutPartselLogic(svLogicVecVal* d, svLogicVecVal s, int i, int w);

XXTERN int svLeft(svOpenArrayHandle h, int d);
XXTERN int svRight(svOpenArrayHandle h, int d);
XXTERN int svLow(svOpenArrayHandle h, int d);
XXTERN int svHigh(svOpenArrayHandle h, int d);
XXTERN int svIncrement(svOpenArrayHandle h, int d);
XXTERN int svSize(svOpenArrayHandle h, int d);
XXTERN int svDimensions(svOpenArrayHandle h);
XXTERN void* svGetArrayPtr(svOpenArrayHandle h);
XXTERN int svSizeOfArray(svOpenArrayHandle h);

XXTERN void* svGetArrElemPtr(svOpenArrayHandle h, int indx1, ...);
XXTERN void* svGetArrElemPtr1(svOpenArrayHandle h, int indx1);
XXTERN void* svGetArrElemPtr2(svOpenArrayHandle h, int indx1, int indx2);
XXTERN void* svGetArrElemPtr3(svOpenArrayHandle h, int indx1, int indx2,
                              int indx3);

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

XXTERN svBit svGetBitArrElem(svOpenArrayHandle s, int indx1, ...);
XXTERN svBit svGetBitArrElem1(svOpenArrayHandle s, int indx1);
XXTERN svBit svGetBitArrElem2(svOpenArrayHandle s, int indx1, int indx2);
XXTERN svBit svGetBitArrElem3(svOpenArrayHandle s, int indx1, int indx2,
                              int indx3);

XXTERN svLogic svGetLogicArrElem(svOpenArrayHandle s, int indx1, ...);
XXTERN svLogic svGetLogicArrElem1(svOpenArrayHandle s, int indx1);
XXTERN svLogic svGetLogicArrElem2(svOpenArrayHandle s, int indx1, int indx2);
XXTERN svLogic svGetLogicArrElem3(svOpenArrayHandle s, int indx1, int indx2,
                                  int indx3);

XXTERN void svPutLogicArrElem(svOpenArrayHandle d, svLogic value, int indx1,
                              ...);
XXTERN void svPutLogicArrElem1(svOpenArrayHandle d, svLogic value, int indx1);
XXTERN void svPutLogicArrElem2(svOpenArrayHandle d, svLogic value, int indx1,
                               int indx2);
XXTERN void svPutLogicArrElem3(svOpenArrayHandle d, svLogic value, int indx1,
                               int indx2, int indx3);

XXTERN void svPutBitArrElem(svOpenArrayHandle d, svBit value, int indx1, ...);
XXTERN void svPutBitArrElem1(svOpenArrayHandle d, svBit value, int indx1);
XXTERN void svPutBitArrElem2(svOpenArrayHandle d, svBit value, int indx1,
                             int indx2);
XXTERN void svPutBitArrElem3(svOpenArrayHandle d, svBit value, int indx1,
                             int indx2, int indx3);

XXTERN svScope svGetScope(void);
XXTERN svScope svSetScope(svScope scope);
XXTERN const char* svGetNameFromScope(svScope scope);
XXTERN svScope svGetScopeFromName(const char* scope_name);
XXTERN int svPutUserData(svScope scope, void* user_key, void* user_data);
XXTERN void* svGetUserData(svScope scope, void* user_key);
XXTERN int svGetCallerInfo(const char** file_name, int* line_number);
XXTERN int svIsDisabledState(void);
XXTERN void svAckDisabledState(void);

/* Annex H.13: time and timescale. svGetTime retrieves the current simulation
 * time, scaled to the time unit of the scope (the simulation time unit for a
 * NULL scope); the caller's svTimeVal.type selects a scaled real or the raw
 * simulation-time count. svGetTimeUnit and svGetTimePrecision retrieve the time
 * unit and precision of the scope (the simulation time unit for a NULL scope).
 * Each returns 0 on success and -1 on error. */
XXTERN int svGetTime(const svScope scope, svTimeVal* time);
XXTERN int svGetTimeUnit(const svScope scope, int32_t* time_unit);
XXTERN int svGetTimePrecision(const svScope scope, int32_t* time_precision);

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
