// IEEE 1800-2023 Annex I — svdpi.h implementation.
//
// All function names are MANDATED by the IEEE standard.

#include "vpi/svdpi.h"

// Thread-local DPI scope.
static thread_local svScope g_current_scope = nullptr;

const char* svDpiVersion(void) { return "IEEE 1800-2023"; }

// =============================================================================
// Bit-select functions
// =============================================================================

svBit svGetBitselBit(const svBitVecVal* s, int i) {
  int word = i / 32;
  int bit = i % 32;
  return (s[word] >> bit) & 1u;
}

svLogic svGetBitselLogic(const svLogicVecVal* s, int i) {
  int word = i / 32;
  int bit = i % 32;
  uint32_t a_bit = (s[word].aval >> bit) & 1u;
  uint32_t b_bit = (s[word].bval >> bit) & 1u;
  if (b_bit == 0) return a_bit ? sv_1 : sv_0;
  return a_bit ? sv_x : sv_z;
}

void svPutBitselBit(svBitVecVal* d, int i, svBit s) {
  int word = i / 32;
  int bit = i % 32;
  if (s) {
    d[word] |= (1u << bit);
  } else {
    d[word] &= ~(1u << bit);
  }
}

void svPutBitselLogic(svLogicVecVal* d, int i, svLogic s) {
  int word = i / 32;
  int bit = i % 32;
  uint32_t mask = 1u << bit;
  switch (s) {
    case sv_0:
      d[word].aval &= ~mask;
      d[word].bval &= ~mask;
      break;
    case sv_1:
      d[word].aval |= mask;
      d[word].bval &= ~mask;
      break;
    case sv_z:
      d[word].aval &= ~mask;
      d[word].bval |= mask;
      break;
    default:  // sv_x
      d[word].aval |= mask;
      d[word].bval |= mask;
      break;
  }
}

// =============================================================================
// Part-select functions (w <= 32)
// =============================================================================

void svGetPartselBit(svBitVecVal* d, const svBitVecVal* s, int i, int w) {
  if (w <= 0 || w > 32) return;
  int word = i / 32;
  int bit = i % 32;
  uint32_t result = s[word] >> bit;
  if (bit + w > 32) {
    result |= s[word + 1] << (32 - bit);
  }
  uint32_t wmask = (w == 32) ? 0xFFFFFFFFu : ((1u << w) - 1u);
  *d = result & wmask;
}

void svGetPartselLogic(svLogicVecVal* d, const svLogicVecVal* s, int i, int w) {
  if (w <= 0 || w > 32) return;
  int word = i / 32;
  int bit = i % 32;
  uint32_t wmask = (w == 32) ? 0xFFFFFFFFu : ((1u << w) - 1u);
  d->aval = (s[word].aval >> bit) & wmask;
  d->bval = (s[word].bval >> bit) & wmask;
}

void svPutPartselBit(svBitVecVal* d, svBitVecVal s, int i, int w) {
  if (w <= 0 || w > 32) return;
  uint32_t wmask = (w == 32) ? 0xFFFFFFFFu : ((1u << w) - 1u);
  uint32_t value = s & wmask;
  int word = i / 32;
  int bit = i % 32;
  d[word] &= ~(wmask << bit);
  d[word] |= value << bit;
  if (bit + w > 32) {
    int overflow = bit + w - 32;
    uint32_t hi_mask = (1u << overflow) - 1u;
    d[word + 1] &= ~hi_mask;
    d[word + 1] |= value >> (32 - bit);
  }
}

void svPutPartselLogic(svLogicVecVal* d, svLogicVecVal s, int i, int w) {
  if (w <= 0 || w > 32) return;
  uint32_t wmask = (w == 32) ? 0xFFFFFFFFu : ((1u << w) - 1u);
  int word = i / 32;
  int bit = i % 32;
  d[word].aval &= ~(wmask << bit);
  d[word].aval |= (s.aval & wmask) << bit;
  d[word].bval &= ~(wmask << bit);
  d[word].bval |= (s.bval & wmask) << bit;
}

// =============================================================================
// Open array functions (stubs — full impl requires simulator integration)
// =============================================================================

int svLeft(svOpenArrayHandle h, int d) {
  (void)h;
  (void)d;
  return 0;
}
int svRight(svOpenArrayHandle h, int d) {
  (void)h;
  (void)d;
  return 0;
}
int svLow(svOpenArrayHandle h, int d) {
  (void)h;
  (void)d;
  return 0;
}
int svHigh(svOpenArrayHandle h, int d) {
  (void)h;
  (void)d;
  return 0;
}
int svIncrement(svOpenArrayHandle h, int d) {
  (void)h;
  (void)d;
  return 1;
}
int svSize(svOpenArrayHandle h, int d) {
  (void)h;
  (void)d;
  return 0;
}
int svDimensions(svOpenArrayHandle h) {
  (void)h;
  return 0;
}
void* svGetArrayPtr(svOpenArrayHandle h) {
  (void)h;
  return nullptr;
}
int svSizeOfArray(svOpenArrayHandle h) {
  (void)h;
  return 0;
}

void* svGetArrElemPtr1(svOpenArrayHandle h, int indx1) {
  (void)h;
  (void)indx1;
  return nullptr;
}
void* svGetArrElemPtr2(svOpenArrayHandle h, int indx1, int indx2) {
  (void)h;
  (void)indx1;
  (void)indx2;
  return nullptr;
}
void* svGetArrElemPtr3(svOpenArrayHandle h, int indx1, int indx2, int indx3) {
  (void)h;
  (void)indx1;
  (void)indx2;
  (void)indx3;
  return nullptr;
}

// Open array VecVal stubs.
void svPutBitArrElem1VecVal(svOpenArrayHandle d, const svBitVecVal* s,
                            int indx1) {
  (void)d;
  (void)s;
  (void)indx1;
}
void svPutBitArrElem2VecVal(svOpenArrayHandle d, const svBitVecVal* s,
                            int indx1, int indx2) {
  (void)d;
  (void)s;
  (void)indx1;
  (void)indx2;
}
void svPutBitArrElem3VecVal(svOpenArrayHandle d, const svBitVecVal* s,
                            int indx1, int indx2, int indx3) {
  (void)d;
  (void)s;
  (void)indx1;
  (void)indx2;
  (void)indx3;
}
void svPutLogicArrElem1VecVal(svOpenArrayHandle d, const svLogicVecVal* s,
                              int indx1) {
  (void)d;
  (void)s;
  (void)indx1;
}
void svPutLogicArrElem2VecVal(svOpenArrayHandle d, const svLogicVecVal* s,
                              int indx1, int indx2) {
  (void)d;
  (void)s;
  (void)indx1;
  (void)indx2;
}
void svPutLogicArrElem3VecVal(svOpenArrayHandle d, const svLogicVecVal* s,
                              int indx1, int indx2, int indx3) {
  (void)d;
  (void)s;
  (void)indx1;
  (void)indx2;
  (void)indx3;
}
void svGetBitArrElem1VecVal(svBitVecVal* d, svOpenArrayHandle s, int indx1) {
  (void)d;
  (void)s;
  (void)indx1;
}
void svGetBitArrElem2VecVal(svBitVecVal* d, svOpenArrayHandle s, int indx1,
                            int indx2) {
  (void)d;
  (void)s;
  (void)indx1;
  (void)indx2;
}
void svGetBitArrElem3VecVal(svBitVecVal* d, svOpenArrayHandle s, int indx1,
                            int indx2, int indx3) {
  (void)d;
  (void)s;
  (void)indx1;
  (void)indx2;
  (void)indx3;
}
void svGetLogicArrElem1VecVal(svLogicVecVal* d, svOpenArrayHandle s,
                              int indx1) {
  (void)d;
  (void)s;
  (void)indx1;
}
void svGetLogicArrElem2VecVal(svLogicVecVal* d, svOpenArrayHandle s, int indx1,
                              int indx2) {
  (void)d;
  (void)s;
  (void)indx1;
  (void)indx2;
}
void svGetLogicArrElem3VecVal(svLogicVecVal* d, svOpenArrayHandle s, int indx1,
                              int indx2, int indx3) {
  (void)d;
  (void)s;
  (void)indx1;
  (void)indx2;
  (void)indx3;
}

// Open array scalar element stubs.
svBit svGetBitArrElem1(svOpenArrayHandle s, int indx1) {
  (void)s;
  (void)indx1;
  return 0;
}
svBit svGetBitArrElem2(svOpenArrayHandle s, int indx1, int indx2) {
  (void)s;
  (void)indx1;
  (void)indx2;
  return 0;
}
svBit svGetBitArrElem3(svOpenArrayHandle s, int indx1, int indx2, int indx3) {
  (void)s;
  (void)indx1;
  (void)indx2;
  (void)indx3;
  return 0;
}
svLogic svGetLogicArrElem1(svOpenArrayHandle s, int indx1) {
  (void)s;
  (void)indx1;
  return 0;
}
svLogic svGetLogicArrElem2(svOpenArrayHandle s, int indx1, int indx2) {
  (void)s;
  (void)indx1;
  (void)indx2;
  return 0;
}
svLogic svGetLogicArrElem3(svOpenArrayHandle s, int indx1, int indx2,
                           int indx3) {
  (void)s;
  (void)indx1;
  (void)indx2;
  (void)indx3;
  return 0;
}
void svPutLogicArrElem1(svOpenArrayHandle d, svLogic value, int indx1) {
  (void)d;
  (void)value;
  (void)indx1;
}
void svPutLogicArrElem2(svOpenArrayHandle d, svLogic value, int indx1,
                        int indx2) {
  (void)d;
  (void)value;
  (void)indx1;
  (void)indx2;
}
void svPutLogicArrElem3(svOpenArrayHandle d, svLogic value, int indx1,
                        int indx2, int indx3) {
  (void)d;
  (void)value;
  (void)indx1;
  (void)indx2;
  (void)indx3;
}
void svPutBitArrElem1(svOpenArrayHandle d, svBit value, int indx1) {
  (void)d;
  (void)value;
  (void)indx1;
}
void svPutBitArrElem2(svOpenArrayHandle d, svBit value, int indx1, int indx2) {
  (void)d;
  (void)value;
  (void)indx1;
  (void)indx2;
}
void svPutBitArrElem3(svOpenArrayHandle d, svBit value, int indx1, int indx2,
                      int indx3) {
  (void)d;
  (void)value;
  (void)indx1;
  (void)indx2;
  (void)indx3;
}

// =============================================================================
// DPI context functions
// =============================================================================

svScope svGetScope(void) { return g_current_scope; }

svScope svSetScope(svScope scope) {
  svScope prev = g_current_scope;
  g_current_scope = scope;
  return prev;
}

const char* svGetNameFromScope(svScope scope) {
  (void)scope;
  return "";
}

svScope svGetScopeFromName(const char* scope_name) {
  (void)scope_name;
  return nullptr;
}

int svPutUserData(svScope scope, void* user_key, void* user_data) {
  (void)scope;
  (void)user_key;
  (void)user_data;
  return 0;
}

void* svGetUserData(svScope scope, void* user_key) {
  (void)scope;
  (void)user_key;
  return nullptr;
}

int svGetCallerInfo(const char** file_name, int* line_number) {
  (void)file_name;
  (void)line_number;
  return 0;
}

int svIsDisabledState(void) { return 0; }

void svAckDisabledState(void) {}
