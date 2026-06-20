

#include "simulator/svdpi.h"

#include <cstdarg>
#include <map>
#include <utility>
#include <vector>

#include "simulator/dpi_runtime.h"

static thread_local svScope g_current_scope = nullptr;

// §H.9.3 user data storage: a pointer the user associates with a (scope, key)
// pair via svPutUserData and later retrieves with svGetUserData. The key is
// chosen and kept unique by the user's C code; entries are kept distinct per
// scope so the same key under different scopes never collides.
static std::map<std::pair<svScope, void*>, void*>& DpiUserDataStore() {
  static std::map<std::pair<svScope, void*>, void*> store;
  return store;
}

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
// §H.12.4: svGetArrayPtr/svSizeOfArray expose the actual address and byte size
// of an open array as a whole, but only when the SystemVerilog layout matches
// the C layout. This simulator keeps open arrays in the canonical word form of
// H.10.1.2 rather than a plain C array, so the whole-array layout never matches
// C; H.12.4 then requires the address and size to be undefined, which it pins
// to 0. Individual elements remain reachable through svGetArrElemPtr* below.
void* svGetArrayPtr(svOpenArrayHandle h) {
  (void)h;
  return nullptr;
}
int svSizeOfArray(svOpenArrayHandle h) {
  (void)h;
  return 0;
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
// toward the right bound, independent of range direction. Returns false when
// the index falls outside the dimension's original range.
bool svUnpackedPos(const svOpenArrayDimRange& r, int idx, int* pos) {
  int low = r.left < r.right ? r.left : r.right;
  int high = r.left > r.right ? r.left : r.right;
  if (idx < low || idx > high) return false;
  *pos = r.right >= r.left ? idx - r.left : r.left - idx;
  return true;
}

// Resolve up to three unpacked indices to the address of the addressed
// element's first canonical word, row-major over the unpacked dimensions
// (ranges[1..n_dims-1]), and report the element's word count via *words.
// Returns nullptr when the handle is unusable, the index count does not match
// the unpacked dimensionality, or any index is out of its original range, so
// callers leave both operands untouched in those cases.
void* svElemBase(svOpenArrayHandle h, const int* idx, int n_idx,
                 size_t word_size, int* words) {
  if (h == nullptr) return nullptr;
  const svOpenArrayDesc* desc = static_cast<const svOpenArrayDesc*>(h);
  if (desc->data == nullptr || desc->ranges == nullptr) return nullptr;
  if (n_idx != desc->n_dims - 1) return nullptr;
  long linear = 0;
  for (int k = 0; k < n_idx; ++k) {
    const svOpenArrayDimRange& r = desc->ranges[k + 1];
    int pos = 0;
    if (!svUnpackedPos(r, idx[k], &pos)) return nullptr;
    linear = linear * svUnpackedExtent(r) + pos;
  }
  *words = svPackedElemWords(desc);
  return static_cast<char*>(desc->data) + (linear * *words) * word_size;
}

// §H.12.4 element-address resolution shared by the svGetArrElemPtr family. The
// element at the left bound of each unpacked dimension occupies position 0 and
// positions advance toward the right bound, row-major over the unpacked
// dimensions (ranges[1..n_dims-1]) — the same coordinate mapping the copy
// helpers use. Consecutive elements are desc->elem_size bytes apart, the
// representation stride recorded when the handle was built. Returns nullptr
// when the handle or its storage is unusable, when the index count does not
// match the unpacked dimensionality, or when any index is outside its original
// range — the listing's "null if index outside the range or null pointer"
// contract. A zero elem_size signals that an element's representation differs
// from that of an individual value of the same type, for which H.12.4 also
// requires nullptr.
void* svElemAddr(svOpenArrayHandle h, const int* idx, int n_idx) {
  if (h == nullptr) return nullptr;
  const svOpenArrayDesc* desc = static_cast<const svOpenArrayDesc*>(h);
  if (desc->data == nullptr || desc->ranges == nullptr) return nullptr;
  if (desc->elem_size == 0) return nullptr;
  if (n_idx != desc->n_dims - 1) return nullptr;
  long linear = 0;
  for (int k = 0; k < n_idx; ++k) {
    const svOpenArrayDimRange& r = desc->ranges[k + 1];
    int pos = 0;
    if (!svUnpackedPos(r, idx[k], &pos)) return nullptr;
    linear = linear * svUnpackedExtent(r) + pos;
  }
  return static_cast<char*>(desc->data) + linear * desc->elem_size;
}

void svPutBitElem(svOpenArrayHandle d, const svBitVecVal* s, const int* idx,
                  int n) {
  int words = 0;
  void* base = svElemBase(d, idx, n, sizeof(svBitVecVal), &words);
  if (base == nullptr) return;
  svBitVecVal* dst = static_cast<svBitVecVal*>(base);
  for (int w = 0; w < words; ++w) dst[w] = s[w];
}

void svGetBitElem(svBitVecVal* d, svOpenArrayHandle s, const int* idx, int n) {
  int words = 0;
  void* base = svElemBase(s, idx, n, sizeof(svBitVecVal), &words);
  if (base == nullptr) return;
  const svBitVecVal* src = static_cast<const svBitVecVal*>(base);
  for (int w = 0; w < words; ++w) d[w] = src[w];
}

void svPutLogicElem(svOpenArrayHandle d, const svLogicVecVal* s, const int* idx,
                    int n) {
  int words = 0;
  void* base = svElemBase(d, idx, n, sizeof(svLogicVecVal), &words);
  if (base == nullptr) return;
  svLogicVecVal* dst = static_cast<svLogicVecVal*>(base);
  for (int w = 0; w < words; ++w) dst[w] = s[w];
}

void svGetLogicElem(svLogicVecVal* d, svOpenArrayHandle s, const int* idx,
                    int n) {
  int words = 0;
  void* base = svElemBase(s, idx, n, sizeof(svLogicVecVal), &words);
  if (base == nullptr) return;
  const svLogicVecVal* src = static_cast<const svLogicVecVal*>(base);
  for (int w = 0; w < words; ++w) d[w] = src[w];
}

// Annex H.12.6 scalar element access support. When an open array's element is a
// simple scalar (a single bit or logic), that element occupies one canonical
// word whose bit 0 carries the value; the surrounding bits are not part of the
// scalar. These helpers reuse the same element resolver as the wider copy
// functions to locate that word from the per-call unpacked indices, then read
// or write only bit 0. An unusable handle, a mismatched index count, or an
// index outside its original range resolves no element, so a read returns
// sv_0/0 and a write is a no-op, matching the guard the H.12.5 helpers apply.
svBit svGetBitScalarElem(svOpenArrayHandle s, const int* idx, int n) {
  int words = 0;
  void* base = svElemBase(s, idx, n, sizeof(svBitVecVal), &words);
  (void)words;
  if (base == nullptr) return 0;
  return static_cast<const svBitVecVal*>(base)[0] & 1u;
}

void svPutBitScalarElem(svOpenArrayHandle d, svBit value, const int* idx,
                        int n) {
  int words = 0;
  void* base = svElemBase(d, idx, n, sizeof(svBitVecVal), &words);
  (void)words;
  if (base == nullptr) return;
  svBitVecVal* dst = static_cast<svBitVecVal*>(base);
  if (value & 1u) {
    dst[0] |= 1u;
  } else {
    dst[0] &= ~1u;
  }
}

svLogic svGetLogicScalarElem(svOpenArrayHandle s, const int* idx, int n) {
  int words = 0;
  void* base = svElemBase(s, idx, n, sizeof(svLogicVecVal), &words);
  (void)words;
  if (base == nullptr) return 0;
  const svLogicVecVal* src = static_cast<const svLogicVecVal*>(base);
  uint32_t a_bit = src[0].aval & 1u;
  uint32_t b_bit = src[0].bval & 1u;
  // Decode bit 0 of the canonical aval/bval pair to a four-state scalar, the
  // same encoding svGetBitselLogic uses: bval clear selects 0/1, bval set
  // selects z/x.
  if (b_bit == 0) return a_bit ? sv_1 : sv_0;
  return a_bit ? sv_x : sv_z;
}

void svPutLogicScalarElem(svOpenArrayHandle d, svLogic value, const int* idx,
                          int n) {
  int words = 0;
  void* base = svElemBase(d, idx, n, sizeof(svLogicVecVal), &words);
  (void)words;
  if (base == nullptr) return;
  svLogicVecVal* dst = static_cast<svLogicVecVal*>(base);
  switch (value) {
    case sv_0:
      dst[0].aval &= ~1u;
      dst[0].bval &= ~1u;
      break;
    case sv_1:
      dst[0].aval |= 1u;
      dst[0].bval &= ~1u;
      break;
    case sv_z:
      dst[0].aval &= ~1u;
      dst[0].bval |= 1u;
      break;
    default:
      dst[0].aval |= 1u;
      dst[0].bval |= 1u;
      break;
  }
}

}  // namespace

// §H.12.4: the addresses of individual elements are always supported,
// regardless of whether the whole array exposes a C-compatible layout. The
// specialized 1-, 2-, and 3-dimensional entry points forward to the shared
// resolver, which returns a null pointer for an out-of-range index, an unusable
// handle, a mismatched index count, or an element representation that differs
// from an individual value of the same type.
void* svGetArrElemPtr1(svOpenArrayHandle h, int indx1) {
  int idx[1] = {indx1};
  return svElemAddr(h, idx, 1);
}
void* svGetArrElemPtr2(svOpenArrayHandle h, int indx1, int indx2) {
  int idx[2] = {indx1, indx2};
  return svElemAddr(h, idx, 2);
}
void* svGetArrElemPtr3(svOpenArrayHandle h, int indx1, int indx2, int indx3) {
  int idx[3] = {indx1, indx2, indx3};
  return svElemAddr(h, idx, 3);
}

// General element-address function for an arbitrary number of unpacked indices.
// One index is supplied per unpacked dimension, so the count is svDimensions
// minus the single packed dimension; the indices are gathered and handed to the
// same resolver the specialized versions use.
void* svGetArrElemPtr(svOpenArrayHandle h, int indx1, ...) {
  int n = svDimensions(h) - 1;
  if (n < 1) return nullptr;
  std::vector<int> idx;
  idx.reserve(n);
  idx.push_back(indx1);
  va_list ap;
  va_start(ap, indx1);
  for (int k = 1; k < n; ++k) idx.push_back(va_arg(ap, int));
  va_end(ap);
  return svElemAddr(h, idx.data(), n);
}

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

// Annex H.12.6: read or write a single scalar (bit or logic) element of an open
// array, selected by one unpacked index per unpacked dimension. The specialized
// 1-, 2-, and 3-index entry points forward to the shared scalar helpers; the
// variadic forms gather svDimensions-1 indices (one per unpacked dimension, the
// packed dimension 0 excepted) before forwarding, mirroring svGetArrElemPtr.
svBit svGetBitArrElem1(svOpenArrayHandle s, int indx1) {
  int idx[1] = {indx1};
  return svGetBitScalarElem(s, idx, 1);
}
svBit svGetBitArrElem2(svOpenArrayHandle s, int indx1, int indx2) {
  int idx[2] = {indx1, indx2};
  return svGetBitScalarElem(s, idx, 2);
}
svBit svGetBitArrElem3(svOpenArrayHandle s, int indx1, int indx2, int indx3) {
  int idx[3] = {indx1, indx2, indx3};
  return svGetBitScalarElem(s, idx, 3);
}
svBit svGetBitArrElem(svOpenArrayHandle s, int indx1, ...) {
  int n = svDimensions(s) - 1;
  if (n < 1) return 0;
  std::vector<int> idx;
  idx.reserve(n);
  idx.push_back(indx1);
  va_list ap;
  va_start(ap, indx1);
  for (int k = 1; k < n; ++k) idx.push_back(va_arg(ap, int));
  va_end(ap);
  return svGetBitScalarElem(s, idx.data(), n);
}
svLogic svGetLogicArrElem1(svOpenArrayHandle s, int indx1) {
  int idx[1] = {indx1};
  return svGetLogicScalarElem(s, idx, 1);
}
svLogic svGetLogicArrElem2(svOpenArrayHandle s, int indx1, int indx2) {
  int idx[2] = {indx1, indx2};
  return svGetLogicScalarElem(s, idx, 2);
}
svLogic svGetLogicArrElem3(svOpenArrayHandle s, int indx1, int indx2,
                           int indx3) {
  int idx[3] = {indx1, indx2, indx3};
  return svGetLogicScalarElem(s, idx, 3);
}
svLogic svGetLogicArrElem(svOpenArrayHandle s, int indx1, ...) {
  int n = svDimensions(s) - 1;
  if (n < 1) return 0;
  std::vector<int> idx;
  idx.reserve(n);
  idx.push_back(indx1);
  va_list ap;
  va_start(ap, indx1);
  for (int k = 1; k < n; ++k) idx.push_back(va_arg(ap, int));
  va_end(ap);
  return svGetLogicScalarElem(s, idx.data(), n);
}
void svPutLogicArrElem1(svOpenArrayHandle d, svLogic value, int indx1) {
  int idx[1] = {indx1};
  svPutLogicScalarElem(d, value, idx, 1);
}
void svPutLogicArrElem2(svOpenArrayHandle d, svLogic value, int indx1,
                        int indx2) {
  int idx[2] = {indx1, indx2};
  svPutLogicScalarElem(d, value, idx, 2);
}
void svPutLogicArrElem3(svOpenArrayHandle d, svLogic value, int indx1,
                        int indx2, int indx3) {
  int idx[3] = {indx1, indx2, indx3};
  svPutLogicScalarElem(d, value, idx, 3);
}
void svPutLogicArrElem(svOpenArrayHandle d, svLogic value, int indx1, ...) {
  int n = svDimensions(d) - 1;
  if (n < 1) return;
  std::vector<int> idx;
  idx.reserve(n);
  idx.push_back(indx1);
  va_list ap;
  va_start(ap, indx1);
  for (int k = 1; k < n; ++k) idx.push_back(va_arg(ap, int));
  va_end(ap);
  svPutLogicScalarElem(d, value, idx.data(), n);
}
void svPutBitArrElem1(svOpenArrayHandle d, svBit value, int indx1) {
  int idx[1] = {indx1};
  svPutBitScalarElem(d, value, idx, 1);
}
void svPutBitArrElem2(svOpenArrayHandle d, svBit value, int indx1, int indx2) {
  int idx[2] = {indx1, indx2};
  svPutBitScalarElem(d, value, idx, 2);
}
void svPutBitArrElem3(svOpenArrayHandle d, svBit value, int indx1, int indx2,
                      int indx3) {
  int idx[3] = {indx1, indx2, indx3};
  svPutBitScalarElem(d, value, idx, 3);
}
void svPutBitArrElem(svOpenArrayHandle d, svBit value, int indx1, ...) {
  int n = svDimensions(d) - 1;
  if (n < 1) return;
  std::vector<int> idx;
  idx.reserve(n);
  idx.push_back(indx1);
  va_list ap;
  va_start(ap, indx1);
  for (int k = 1; k < n; ++k) idx.push_back(va_arg(ap, int));
  va_end(ap);
  svPutBitScalarElem(d, value, idx.data(), n);
}

svScope svGetScope(void) { return g_current_scope; }

svScope svSetScope(svScope scope) {
  svScope prev = g_current_scope;
  g_current_scope = scope;
  return prev;
}

const char* svGetNameFromScope(svScope scope) {
  // §H.9.3: report the fully qualified name of a scope handle. Handles come
  // from svGetScopeFromName(); an unrecognized handle resolves to an empty name
  // rather than dereferencing an unknown pointer.
  return delta::DpiNameFromScope(static_cast<const delta::DpiScope*>(scope));
}

svScope svGetScopeFromName(const char* scope_name) {
  // §H.9.3: retrieve the handle for a fully qualified instance-scope name (a
  // module, program, interface, or generate scope). A null query or any name
  // that is not a recognized scope resolves to NULL.
  if (scope_name == nullptr) return nullptr;
  return const_cast<delta::DpiScope*>(delta::DpiScopeFromName(scope_name));
}

int svPutUserData(svScope scope, void* user_key, void* user_data) {
  // §H.9.3: a null scope or null payload is an error. Report failure (-1)
  // without recording anything; success returns 0.
  if (scope == nullptr || user_data == nullptr) {
    return -1;
  }
  DpiUserDataStore()[std::make_pair(scope, user_key)] = user_data;
  return 0;
}

void* svGetUserData(svScope scope, void* user_key) {
  // §H.9.3: error cases and lookups that were never stored both surface as a
  // null pointer; a successful retrieval returns the previously stored pointer.
  if (scope == nullptr) {
    return nullptr;
  }
  auto& store = DpiUserDataStore();
  auto it = store.find(std::make_pair(scope, user_key));
  return it == store.end() ? nullptr : it->second;
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

// §H.13: retrieve the current simulation time. The caller sets time->type to
// request the form it wants — sv_scaled_real_time for a real scaled to the time
// unit, otherwise sv_sim_time for the 64-bit count — and this function honors
// that selection, writing the result into the same svTimeVal. A NULL scope
// means the time is scaled to the simulation time unit; this simulator binds no
// per-scope timescale to an svScope, so a non-NULL scope reports the same
// design-wide simulation time. The value comes from the shared time source the
// VPI time routines read, so svGetTime and vpi_get_time() always agree. Returns
// -1 when there is nowhere to write the result, 0 otherwise.
int svGetTime(const svScope scope, svTimeVal* time) {
  (void)scope;
  if (time == nullptr) return -1;
  bool want_scaled_real = (time->type == sv_scaled_real_time);
  delta::DpiGetSimTime(want_scaled_real, &time->high, &time->low, &time->real);
  return 0;
}

// §H.13: retrieve the time unit for the scope. A NULL scope retrieves the
// simulation time unit; with no per-scope timescale binding a non-NULL scope
// reports that same unit. The value matches vpi_get(vpiTimeUnit) for the
// design. Returns -1 when there is nowhere to write the result, 0 otherwise.
int svGetTimeUnit(const svScope scope, int32_t* time_unit) {
  (void)scope;
  if (time_unit == nullptr) return -1;
  *time_unit = delta::DpiGetSimTimeUnit();
  return 0;
}

// §H.13: retrieve the time precision for the scope, mirroring svGetTimeUnit. A
// NULL scope retrieves the simulation time unit; the value matches
// vpi_get(vpiTimePrecision) for the design. Returns -1 when there is nowhere to
// write the result, 0 otherwise.
int svGetTimePrecision(const svScope scope, int32_t* time_precision) {
  (void)scope;
  if (time_precision == nullptr) return -1;
  *time_precision = delta::DpiGetSimTimePrecision();
  return 0;
}
