

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

// Annex H.12.5 element copy support. These functions copy a whole packed array
// (a single canonical vector) between user space and one element of an open
// array, in either direction. The actual argument's original SystemVerilog
// ranges index the open array, and the canonical representation of each element
// is the one defined in H.10.1.2. The helpers below turn the per-call unpacked
// indices into a location inside the descriptor's backing store and report how
// many canonical words an element spans.
namespace {

// Number of canonical 32-bit words occupied by one packed element. Dimension 0
// of the descriptor describes the array's single packed part (H.12.2); its bit
// width fixes the per-element word count for both bit and logic arrays.
int svPackedElemWords(const svOpenArrayDesc* desc) {
  const svOpenArrayDimRange& p = desc->ranges[0];
  int width = (p.left > p.right ? p.left - p.right : p.right - p.left) + 1;
  return (width + 31) / 32;
}

int svUnpackedExtent(const svOpenArrayDimRange& r) {
  int low = r.left < r.right ? r.left : r.right;
  int high = r.left > r.right ? r.left : r.right;
  return high - low + 1;
}

// Map one unpacked index, expressed in the actual argument's original
// SystemVerilog coordinates, to its zero-based position along that dimension.
// The element at the left bound occupies position 0 and positions advance
// toward the right bound, independent of range direction. Returns false when the
// index falls outside the dimension's original range.
bool svUnpackedPos(const svOpenArrayDimRange& r, int idx, int* pos) {
  int low = r.left < r.right ? r.left : r.right;
  int high = r.left > r.right ? r.left : r.right;
  if (idx < low || idx > high) return false;
  *pos = r.right >= r.left ? idx - r.left : r.left - idx;
  return true;
}

// Resolve up to three unpacked indices to the address of the addressed element's
// first canonical word, row-major over the unpacked dimensions
// (ranges[1..n_dims-1]), and report the element's word count via *words. Returns
// nullptr when the handle is unusable, the index count does not match the
// unpacked dimensionality, or any index is out of its original range, so callers
// leave both operands untouched in those cases.
void* svElemBase(svOpenArrayHandle h, const int* idx, int n_idx,
                 size_t word_size, int* words) {
  if (h == nullptr) return nullptr;
  const svOpenArrayDesc* desc = static_cast<const svOpenArrayDesc*>(h);
  if (desc->data == nullptr || desc->ranges == nullptr) return nullptr;
  if (n_idx != desc->n_dims - 1) return nullptr;
  long linear = 0;
  for (int k = 0; k < n_idx; ++k) {
    const svOpenArrayDimRange& r = desc->ranges[k + 1];
    int pos;
    if (!svUnpackedPos(r, idx[k], &pos)) return nullptr;
    linear = linear * svUnpackedExtent(r) + pos;
  }
  *words = svPackedElemWords(desc);
  return static_cast<char*>(desc->data) + (linear * *words) * word_size;
}

void svPutBitElem(svOpenArrayHandle d, const svBitVecVal* s, const int* idx,
                  int n) {
  int words;
  void* base = svElemBase(d, idx, n, sizeof(svBitVecVal), &words);
  if (base == nullptr) return;
  svBitVecVal* dst = static_cast<svBitVecVal*>(base);
  for (int w = 0; w < words; ++w) dst[w] = s[w];
}

void svGetBitElem(svBitVecVal* d, svOpenArrayHandle s, const int* idx, int n) {
  int words;
  void* base = svElemBase(s, idx, n, sizeof(svBitVecVal), &words);
  if (base == nullptr) return;
  const svBitVecVal* src = static_cast<const svBitVecVal*>(base);
  for (int w = 0; w < words; ++w) d[w] = src[w];
}

void svPutLogicElem(svOpenArrayHandle d, const svLogicVecVal* s, const int* idx,
                    int n) {
  int words;
  void* base = svElemBase(d, idx, n, sizeof(svLogicVecVal), &words);
  if (base == nullptr) return;
  svLogicVecVal* dst = static_cast<svLogicVecVal*>(base);
  for (int w = 0; w < words; ++w) dst[w] = s[w];
}

void svGetLogicElem(svLogicVecVal* d, svOpenArrayHandle s, const int* idx,
                    int n) {
  int words;
  void* base = svElemBase(s, idx, n, sizeof(svLogicVecVal), &words);
  if (base == nullptr) return;
  const svLogicVecVal* src = static_cast<const svLogicVecVal*>(base);
  for (int w = 0; w < words; ++w) d[w] = src[w];
}

}  // namespace

void svPutBitArrElem1VecVal(svOpenArrayHandle d, const svBitVecVal* s,
                            int indx1) {
  int idx[1] = {indx1};
  svPutBitElem(d, s, idx, 1);
}
void svPutBitArrElem2VecVal(svOpenArrayHandle d, const svBitVecVal* s,
                            int indx1, int indx2) {
  int idx[2] = {indx1, indx2};
  svPutBitElem(d, s, idx, 2);
}
void svPutBitArrElem3VecVal(svOpenArrayHandle d, const svBitVecVal* s,
                            int indx1, int indx2, int indx3) {
  int idx[3] = {indx1, indx2, indx3};
  svPutBitElem(d, s, idx, 3);
}
void svPutLogicArrElem1VecVal(svOpenArrayHandle d, const svLogicVecVal* s,
                              int indx1) {
  int idx[1] = {indx1};
  svPutLogicElem(d, s, idx, 1);
}
void svPutLogicArrElem2VecVal(svOpenArrayHandle d, const svLogicVecVal* s,
                              int indx1, int indx2) {
  int idx[2] = {indx1, indx2};
  svPutLogicElem(d, s, idx, 2);
}
void svPutLogicArrElem3VecVal(svOpenArrayHandle d, const svLogicVecVal* s,
                              int indx1, int indx2, int indx3) {
  int idx[3] = {indx1, indx2, indx3};
  svPutLogicElem(d, s, idx, 3);
}
void svGetBitArrElem1VecVal(svBitVecVal* d, svOpenArrayHandle s, int indx1) {
  int idx[1] = {indx1};
  svGetBitElem(d, s, idx, 1);
}
void svGetBitArrElem2VecVal(svBitVecVal* d, svOpenArrayHandle s, int indx1,
                            int indx2) {
  int idx[2] = {indx1, indx2};
  svGetBitElem(d, s, idx, 2);
}
void svGetBitArrElem3VecVal(svBitVecVal* d, svOpenArrayHandle s, int indx1,
                            int indx2, int indx3) {
  int idx[3] = {indx1, indx2, indx3};
  svGetBitElem(d, s, idx, 3);
}
void svGetLogicArrElem1VecVal(svLogicVecVal* d, svOpenArrayHandle s,
                              int indx1) {
  int idx[1] = {indx1};
  svGetLogicElem(d, s, idx, 1);
}
void svGetLogicArrElem2VecVal(svLogicVecVal* d, svOpenArrayHandle s, int indx1,
                              int indx2) {
  int idx[2] = {indx1, indx2};
  svGetLogicElem(d, s, idx, 2);
}
void svGetLogicArrElem3VecVal(svLogicVecVal* d, svOpenArrayHandle s, int indx1,
                              int indx2, int indx3) {
  int idx[3] = {indx1, indx2, indx3};
  svGetLogicElem(d, s, idx, 3);
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
