

#include "simulator/svdpi.h"

#include "simulator/dpi_runtime.h"

static thread_local svScope g_current_scope = nullptr;

// Per Annex H.10.1.3, the returned string names the canonical value
// representation in use rather than the language revision. This simulator uses
// the VPI-based canonical value (s_vpi_vecval), so it reports "1800-2005". The
// alternative "SV3.1a" is reserved for the legacy svLogicVec32 representation.
const char* svDpiVersion(void) { return "1800-2005"; }

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
    default:
      d[word].aval |= mask;
      d[word].bval |= mask;
      break;
  }
}

void svGetPartselBit(svBitVecVal* d, const svBitVecVal* s, int i, int w) {
  if (w <= 0 || w > 32) return;
  int word = i / 32;
  int bit = i % 32;
  uint32_t result = s[word] >> bit;
  if (bit + w > 32) {
    result |= s[word + 1] << (32 - bit);
  }
  uint32_t wmask = (w == 32) ? 0xFFFFFFFFu : ((1u << w) - 1u);
  // Per Annex H.11.5, a get part-select copies the source slice into
  // destination bits [w-1:0]; when w < 32 the surrounding destination bits
  // [31:w] shall be left unchanged, so merge instead of overwriting the word.
  *d = (*d & ~wmask) | (result & wmask);
}

void svGetPartselLogic(svLogicVecVal* d, const svLogicVecVal* s, int i, int w) {
  if (w <= 0 || w > 32) return;
  int word = i / 32;
  int bit = i % 32;
  uint32_t aval = s[word].aval >> bit;
  uint32_t bval = s[word].bval >> bit;
  if (bit + w > 32) {
    aval |= s[word + 1].aval << (32 - bit);
    bval |= s[word + 1].bval << (32 - bit);
  }
  uint32_t wmask = (w == 32) ? 0xFFFFFFFFu : ((1u << w) - 1u);
  // Per Annex H.11.5, preserve destination bits [31:w] for w < 32.
  d->aval = (d->aval & ~wmask) | (aval & wmask);
  d->bval = (d->bval & ~wmask) | (bval & wmask);
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
  uint32_t aval = s.aval & wmask;
  uint32_t bval = s.bval & wmask;
  int word = i / 32;
  int bit = i % 32;
  d[word].aval &= ~(wmask << bit);
  d[word].aval |= aval << bit;
  d[word].bval &= ~(wmask << bit);
  d[word].bval |= bval << bit;
  // Per Annex H.11.5, the destination range [(i+w-1):i] can straddle a 32-bit
  // canonical word; write the spillover into the next word, mirroring the bit
  // variant, while leaving the surrounding destination bits unchanged.
  if (bit + w > 32) {
    int overflow = bit + w - 32;
    uint32_t hi_mask = (1u << overflow) - 1u;
    d[word + 1].aval &= ~hi_mask;
    d[word + 1].aval |= aval >> (32 - bit);
    d[word + 1].bval &= ~hi_mask;
    d[word + 1].bval |= bval >> (32 - bit);
  }
}

// The Annex H.12.2 array querying functions are modeled on the SystemVerilog
// array querying functions (20.7) and share their semantics. Dimension 0 names
// the packed part of the array (which is one-dimensional) and dimensions
// greater than 0 name the unpacked part. Each function resolves the requested
// dimension's declared bounds from the handle's descriptor and then derives the
// queried quantity exactly as 20.7 prescribes.
static const svOpenArrayDimRange* svResolveDim(svOpenArrayHandle h, int d) {
  if (h == nullptr) return nullptr;
  const svOpenArrayDesc* desc = static_cast<const svOpenArrayDesc*>(h);
  if (desc->ranges == nullptr || d < 0 || d >= desc->n_dims) return nullptr;
  return &desc->ranges[d];
}

int svLeft(svOpenArrayHandle h, int d) {
  const svOpenArrayDimRange* r = svResolveDim(h, d);
  return r ? r->left : 0;
}
int svRight(svOpenArrayHandle h, int d) {
  const svOpenArrayDimRange* r = svResolveDim(h, d);
  return r ? r->right : 0;
}
int svLow(svOpenArrayHandle h, int d) {
  const svOpenArrayDimRange* r = svResolveDim(h, d);
  if (!r) return 0;
  return r->left < r->right ? r->left : r->right;
}
int svHigh(svOpenArrayHandle h, int d) {
  const svOpenArrayDimRange* r = svResolveDim(h, d);
  if (!r) return 0;
  return r->left > r->right ? r->left : r->right;
}
int svIncrement(svOpenArrayHandle h, int d) {
  const svOpenArrayDimRange* r = svResolveDim(h, d);
  if (!r) return 0;
  // 20.7: $increment is 1 when the left bound is greater than or equal to the
  // right bound, and -1 otherwise.
  return r->left >= r->right ? 1 : -1;
}
int svSize(svOpenArrayHandle h, int d) {
  const svOpenArrayDimRange* r = svResolveDim(h, d);
  if (!r) return 0;
  int low = r->left < r->right ? r->left : r->right;
  int high = r->left > r->right ? r->left : r->right;
  return high - low + 1;
}
int svDimensions(svOpenArrayHandle h) {
  if (h == nullptr) return 0;
  return static_cast<const svOpenArrayDesc*>(h)->n_dims;
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

// §35.9: a subroutine determines whether it is in the disabled state by calling
// this function. It reports the current thread's disabled state — set by the
// runtime when a disable propagates through an exported subroutine into the
// calling import.
int svIsDisabledState(void) { return delta::DpiCurrentDisabledState() ? 1 : 0; }

// §35.9 item c): an imported function shall call this to acknowledge it is
// returning due to a disable. It records the acknowledgement for the current
// disable episode so the simulator's protocol check can confirm it occurred.
void svAckDisabledState(void) { delta::DpiAckCurrentDisable(); }
