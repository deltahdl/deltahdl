#include "simulator/svdpi.h"

#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <map>
#include <utility>
#include <vector>

#include "simulator/dpi.h"
#include "simulator/dpi_runtime.h"
#include "simulator/svdpi_open_array.h"

static thread_local svScope g_current_scope = nullptr;

static std::map<std::pair<svScope, void*>, void*>& DpiUserDataStore() {
  static std::map<std::pair<svScope, void*>, void*> store;
  return store;
}

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
  if (bit + w > 32) {
    int overflow = bit + w - 32;
    uint32_t hi_mask = (1u << overflow) - 1u;
    d[word + 1].aval &= ~hi_mask;
    d[word + 1].aval |= aval >> (32 - bit);
    d[word + 1].bval &= ~hi_mask;
    d[word + 1].bval |= bval >> (32 - bit);
  }
}

static const SvOpenArrayDimRange* ResolveDim(svOpenArrayHandle h, int d) {
  if (h == nullptr) return nullptr;
  const auto* desc = static_cast<const SvOpenArrayDesc*>(h);
  const int kFirst = desc->has_packed_part != 0 ? 0 : 1;
  if (desc->ranges == nullptr || d < kFirst || d >= desc->n_dims) {
    return nullptr;
  }
  return &desc->ranges[d];
}

int svLeft(svOpenArrayHandle h, int d) {
  const SvOpenArrayDimRange* r = ResolveDim(h, d);
  return r ? r->left : 0;
}
int svRight(svOpenArrayHandle h, int d) {
  const SvOpenArrayDimRange* r = ResolveDim(h, d);
  return r ? r->right : 0;
}
int svLow(svOpenArrayHandle h, int d) {
  const SvOpenArrayDimRange* r = ResolveDim(h, d);
  if (!r) return 0;
  return r->left < r->right ? r->left : r->right;
}
int svHigh(svOpenArrayHandle h, int d) {
  const SvOpenArrayDimRange* r = ResolveDim(h, d);
  if (!r) return 0;
  return r->left > r->right ? r->left : r->right;
}
int svIncrement(svOpenArrayHandle h, int d) {
  const SvOpenArrayDimRange* r = ResolveDim(h, d);
  if (!r) return 0;
  return r->left >= r->right ? 1 : -1;
}
int svSize(svOpenArrayHandle h, int d) {
  const SvOpenArrayDimRange* r = ResolveDim(h, d);
  if (!r) return 0;
  int low = r->left < r->right ? r->left : r->right;
  int high = r->left > r->right ? r->left : r->right;
  return high - low + 1;
}
int svDimensions(svOpenArrayHandle h) {
  if (h == nullptr) return 0;
  const auto* desc = static_cast<const SvOpenArrayDesc*>(h);
  return desc->has_packed_part != 0 ? desc->n_dims : desc->n_dims - 1;
}

static int UnpackedDimensions(svOpenArrayHandle h) {
  if (h == nullptr) return 0;
  return static_cast<const SvOpenArrayDesc*>(h)->n_dims - 1;
}
void* svGetArrayPtr(svOpenArrayHandle h) {
  (void)h;
  return nullptr;
}
int svSizeOfArray(svOpenArrayHandle h) {
  (void)h;
  return 0;
}

namespace {

int PackedElemWords(const SvOpenArrayDesc* desc) {
  const SvOpenArrayDimRange& p = desc->ranges[0];
  int width = (p.left > p.right ? p.left - p.right : p.right - p.left) + 1;
  return (width + 31) / 32;
}

int UnpackedExtent(const SvOpenArrayDimRange& r) {
  int low = r.left < r.right ? r.left : r.right;
  int high = r.left > r.right ? r.left : r.right;
  return high - low + 1;
}

bool UnpackedPos(const SvOpenArrayDimRange& r, int idx, int* pos) {
  int low = r.left < r.right ? r.left : r.right;
  int high = r.left > r.right ? r.left : r.right;
  if (idx < low || idx > high) return false;
  *pos = r.right >= r.left ? idx - r.left : r.left - idx;
  return true;
}

void* ElemBase(svOpenArrayHandle h, const int* idx, int n_idx, size_t word_size,
               int* words) {
  if (h == nullptr) return nullptr;
  const auto* desc = static_cast<const SvOpenArrayDesc*>(h);
  if (desc->data == nullptr || desc->ranges == nullptr) return nullptr;
  if (n_idx != desc->n_dims - 1) return nullptr;
  long linear = 0;
  for (int k = 0; k < n_idx; ++k) {
    const SvOpenArrayDimRange& r = desc->ranges[k + 1];
    int pos = 0;
    if (!UnpackedPos(r, idx[k], &pos)) return nullptr;
    linear = linear * UnpackedExtent(r) + pos;
  }
  *words = PackedElemWords(desc);
  return static_cast<char*>(desc->data) + (linear * *words) * word_size;
}

void* ElemAddr(svOpenArrayHandle h, const int* idx, int n_idx) {
  if (h == nullptr) return nullptr;
  const auto* desc = static_cast<const SvOpenArrayDesc*>(h);
  if (desc->data == nullptr || desc->ranges == nullptr) return nullptr;
  if (desc->elem_size == 0) return nullptr;
  if (n_idx != desc->n_dims - 1) return nullptr;
  long linear = 0;
  for (int k = 0; k < n_idx; ++k) {
    const SvOpenArrayDimRange& r = desc->ranges[k + 1];
    int pos = 0;
    if (!UnpackedPos(r, idx[k], &pos)) return nullptr;
    linear = linear * UnpackedExtent(r) + pos;
  }
  return static_cast<char*>(desc->data) + linear * desc->elem_size;
}

void PutBitElem(svOpenArrayHandle d, const svBitVecVal* s, const int* idx,
                int n) {
  int words = 0;
  void* base = ElemBase(d, idx, n, sizeof(svBitVecVal), &words);
  if (base == nullptr) return;
  auto* dst = static_cast<svBitVecVal*>(base);
  for (int w = 0; w < words; ++w) dst[w] = s[w];
}

void GetBitElem(svBitVecVal* d, svOpenArrayHandle s, const int* idx, int n) {
  int words = 0;
  void* base = ElemBase(s, idx, n, sizeof(svBitVecVal), &words);
  if (base == nullptr) return;
  const auto* src = static_cast<const svBitVecVal*>(base);
  for (int w = 0; w < words; ++w) d[w] = src[w];
}

void PutLogicElem(svOpenArrayHandle d, const svLogicVecVal* s, const int* idx,
                  int n) {
  int words = 0;
  void* base = ElemBase(d, idx, n, sizeof(svLogicVecVal), &words);
  if (base == nullptr) return;
  auto* dst = static_cast<svLogicVecVal*>(base);
  for (int w = 0; w < words; ++w) dst[w] = s[w];
}

void GetLogicElem(svLogicVecVal* d, svOpenArrayHandle s, const int* idx,
                  int n) {
  int words = 0;
  void* base = ElemBase(s, idx, n, sizeof(svLogicVecVal), &words);
  if (base == nullptr) return;
  const auto* src = static_cast<const svLogicVecVal*>(base);
  for (int w = 0; w < words; ++w) d[w] = src[w];
}

svBit GetBitScalarElem(svOpenArrayHandle s, const int* idx, int n) {
  int words = 0;
  void* base = ElemBase(s, idx, n, sizeof(svBitVecVal), &words);
  (void)words;
  if (base == nullptr) return 0;
  return static_cast<const svBitVecVal*>(base)[0] & 1u;
}

void PutBitScalarElem(svOpenArrayHandle d, svBit value, const int* idx, int n) {
  int words = 0;
  void* base = ElemBase(d, idx, n, sizeof(svBitVecVal), &words);
  (void)words;
  if (base == nullptr) return;
  auto* dst = static_cast<svBitVecVal*>(base);
  if (value & 1u) {
    dst[0] |= 1u;
  } else {
    dst[0] &= ~1u;
  }
}

svLogic GetLogicScalarElem(svOpenArrayHandle s, const int* idx, int n) {
  int words = 0;
  void* base = ElemBase(s, idx, n, sizeof(svLogicVecVal), &words);
  (void)words;
  if (base == nullptr) return 0;
  const auto* src = static_cast<const svLogicVecVal*>(base);
  uint32_t a_bit = src[0].aval & 1u;
  uint32_t b_bit = src[0].bval & 1u;
  if (b_bit == 0) return a_bit ? sv_1 : sv_0;
  return a_bit ? sv_x : sv_z;
}

void PutLogicScalarElem(svOpenArrayHandle d, svLogic value, const int* idx,
                        int n) {
  int words = 0;
  void* base = ElemBase(d, idx, n, sizeof(svLogicVecVal), &words);
  (void)words;
  if (base == nullptr) return;
  auto* dst = static_cast<svLogicVecVal*>(base);
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

void* svGetArrElemPtr1(svOpenArrayHandle h, int indx1) {
  int idx[1] = {indx1};
  return ElemAddr(h, idx, 1);
}
void* svGetArrElemPtr2(svOpenArrayHandle h, int indx1, int indx2) {
  int idx[2] = {indx1, indx2};
  return ElemAddr(h, idx, 2);
}
void* svGetArrElemPtr3(svOpenArrayHandle h, int indx1, int indx2, int indx3) {
  int idx[3] = {indx1, indx2, indx3};
  return ElemAddr(h, idx, 3);
}

void* svGetArrElemPtr(svOpenArrayHandle h, int indx1, ...) {
  int n = UnpackedDimensions(h);
  if (n < 1) return nullptr;
  std::vector<int> idx;
  idx.reserve(n);
  idx.push_back(indx1);
  va_list ap;
  va_start(ap, indx1);
  for (int k = 1; k < n; ++k) idx.push_back(va_arg(ap, int));
  va_end(ap);
  return ElemAddr(h, idx.data(), n);
}

static std::vector<int> IndicesOfVariadicCall(svOpenArrayHandle h, int indx1,
                                              va_list ap) {
  std::vector<int> idx;
  int n = UnpackedDimensions(h);
  if (n < 1) return idx;
  idx.reserve(n);
  idx.push_back(indx1);
  for (int k = 1; k < n; ++k) idx.push_back(va_arg(ap, int));
  return idx;
}

void svPutBitArrElemVecVal(svOpenArrayHandle d, const svBitVecVal* s, int indx1,
                           ...) {
  va_list ap;
  va_start(ap, indx1);
  const std::vector<int> kIdx = IndicesOfVariadicCall(d, indx1, ap);
  va_end(ap);
  if (kIdx.empty()) return;
  PutBitElem(d, s, kIdx.data(), static_cast<int>(kIdx.size()));
}
void svPutBitArrElem1VecVal(svOpenArrayHandle d, const svBitVecVal* s,
                            int indx1) {
  int idx[1] = {indx1};
  PutBitElem(d, s, idx, 1);
}
void svPutBitArrElem2VecVal(svOpenArrayHandle d, const svBitVecVal* s,
                            int indx1, int indx2) {
  int idx[2] = {indx1, indx2};
  PutBitElem(d, s, idx, 2);
}
void svPutBitArrElem3VecVal(svOpenArrayHandle d, const svBitVecVal* s,
                            int indx1, int indx2, int indx3) {
  int idx[3] = {indx1, indx2, indx3};
  PutBitElem(d, s, idx, 3);
}
void svPutLogicArrElemVecVal(svOpenArrayHandle d, const svLogicVecVal* s,
                             int indx1, ...) {
  va_list ap;
  va_start(ap, indx1);
  const std::vector<int> kIdx = IndicesOfVariadicCall(d, indx1, ap);
  va_end(ap);
  if (kIdx.empty()) return;
  PutLogicElem(d, s, kIdx.data(), static_cast<int>(kIdx.size()));
}
void svPutLogicArrElem1VecVal(svOpenArrayHandle d, const svLogicVecVal* s,
                              int indx1) {
  int idx[1] = {indx1};
  PutLogicElem(d, s, idx, 1);
}
void svPutLogicArrElem2VecVal(svOpenArrayHandle d, const svLogicVecVal* s,
                              int indx1, int indx2) {
  int idx[2] = {indx1, indx2};
  PutLogicElem(d, s, idx, 2);
}
void svPutLogicArrElem3VecVal(svOpenArrayHandle d, const svLogicVecVal* s,
                              int indx1, int indx2, int indx3) {
  int idx[3] = {indx1, indx2, indx3};
  PutLogicElem(d, s, idx, 3);
}
void svGetBitArrElemVecVal(svBitVecVal* d, svOpenArrayHandle s, int indx1,
                           ...) {
  va_list ap;
  va_start(ap, indx1);
  const std::vector<int> kIdx = IndicesOfVariadicCall(s, indx1, ap);
  va_end(ap);
  if (kIdx.empty()) return;
  GetBitElem(d, s, kIdx.data(), static_cast<int>(kIdx.size()));
}
void svGetBitArrElem1VecVal(svBitVecVal* d, svOpenArrayHandle s, int indx1) {
  int idx[1] = {indx1};
  GetBitElem(d, s, idx, 1);
}
void svGetBitArrElem2VecVal(svBitVecVal* d, svOpenArrayHandle s, int indx1,
                            int indx2) {
  int idx[2] = {indx1, indx2};
  GetBitElem(d, s, idx, 2);
}
void svGetBitArrElem3VecVal(svBitVecVal* d, svOpenArrayHandle s, int indx1,
                            int indx2, int indx3) {
  int idx[3] = {indx1, indx2, indx3};
  GetBitElem(d, s, idx, 3);
}
void svGetLogicArrElemVecVal(svLogicVecVal* d, svOpenArrayHandle s, int indx1,
                             ...) {
  va_list ap;
  va_start(ap, indx1);
  const std::vector<int> kIdx = IndicesOfVariadicCall(s, indx1, ap);
  va_end(ap);
  if (kIdx.empty()) return;
  GetLogicElem(d, s, kIdx.data(), static_cast<int>(kIdx.size()));
}
void svGetLogicArrElem1VecVal(svLogicVecVal* d, svOpenArrayHandle s,
                              int indx1) {
  int idx[1] = {indx1};
  GetLogicElem(d, s, idx, 1);
}
void svGetLogicArrElem2VecVal(svLogicVecVal* d, svOpenArrayHandle s, int indx1,
                              int indx2) {
  int idx[2] = {indx1, indx2};
  GetLogicElem(d, s, idx, 2);
}
void svGetLogicArrElem3VecVal(svLogicVecVal* d, svOpenArrayHandle s, int indx1,
                              int indx2, int indx3) {
  int idx[3] = {indx1, indx2, indx3};
  GetLogicElem(d, s, idx, 3);
}

svBit svGetBitArrElem1(svOpenArrayHandle s, int indx1) {
  int idx[1] = {indx1};
  return GetBitScalarElem(s, idx, 1);
}
svBit svGetBitArrElem2(svOpenArrayHandle s, int indx1, int indx2) {
  int idx[2] = {indx1, indx2};
  return GetBitScalarElem(s, idx, 2);
}
svBit svGetBitArrElem3(svOpenArrayHandle s, int indx1, int indx2, int indx3) {
  int idx[3] = {indx1, indx2, indx3};
  return GetBitScalarElem(s, idx, 3);
}
svBit svGetBitArrElem(svOpenArrayHandle s, int indx1, ...) {
  int n = UnpackedDimensions(s);
  if (n < 1) return 0;
  std::vector<int> idx;
  idx.reserve(n);
  idx.push_back(indx1);
  va_list ap;
  va_start(ap, indx1);
  for (int k = 1; k < n; ++k) idx.push_back(va_arg(ap, int));
  va_end(ap);
  return GetBitScalarElem(s, idx.data(), n);
}
svLogic svGetLogicArrElem1(svOpenArrayHandle s, int indx1) {
  int idx[1] = {indx1};
  return GetLogicScalarElem(s, idx, 1);
}
svLogic svGetLogicArrElem2(svOpenArrayHandle s, int indx1, int indx2) {
  int idx[2] = {indx1, indx2};
  return GetLogicScalarElem(s, idx, 2);
}
svLogic svGetLogicArrElem3(svOpenArrayHandle s, int indx1, int indx2,
                           int indx3) {
  int idx[3] = {indx1, indx2, indx3};
  return GetLogicScalarElem(s, idx, 3);
}
svLogic svGetLogicArrElem(svOpenArrayHandle s, int indx1, ...) {
  int n = UnpackedDimensions(s);
  if (n < 1) return 0;
  std::vector<int> idx;
  idx.reserve(n);
  idx.push_back(indx1);
  va_list ap;
  va_start(ap, indx1);
  for (int k = 1; k < n; ++k) idx.push_back(va_arg(ap, int));
  va_end(ap);
  return GetLogicScalarElem(s, idx.data(), n);
}
void svPutLogicArrElem1(svOpenArrayHandle d, svLogic value, int indx1) {
  int idx[1] = {indx1};
  PutLogicScalarElem(d, value, idx, 1);
}
void svPutLogicArrElem2(svOpenArrayHandle d, svLogic value, int indx1,
                        int indx2) {
  int idx[2] = {indx1, indx2};
  PutLogicScalarElem(d, value, idx, 2);
}
void svPutLogicArrElem3(svOpenArrayHandle d, svLogic value, int indx1,
                        int indx2, int indx3) {
  int idx[3] = {indx1, indx2, indx3};
  PutLogicScalarElem(d, value, idx, 3);
}
void svPutLogicArrElem(svOpenArrayHandle d, svLogic value, int indx1, ...) {
  int n = UnpackedDimensions(d);
  if (n < 1) return;
  std::vector<int> idx;
  idx.reserve(n);
  idx.push_back(indx1);
  va_list ap;
  va_start(ap, indx1);
  for (int k = 1; k < n; ++k) idx.push_back(va_arg(ap, int));
  va_end(ap);
  PutLogicScalarElem(d, value, idx.data(), n);
}
void svPutBitArrElem1(svOpenArrayHandle d, svBit value, int indx1) {
  int idx[1] = {indx1};
  PutBitScalarElem(d, value, idx, 1);
}
void svPutBitArrElem2(svOpenArrayHandle d, svBit value, int indx1, int indx2) {
  int idx[2] = {indx1, indx2};
  PutBitScalarElem(d, value, idx, 2);
}
void svPutBitArrElem3(svOpenArrayHandle d, svBit value, int indx1, int indx2,
                      int indx3) {
  int idx[3] = {indx1, indx2, indx3};
  PutBitScalarElem(d, value, idx, 3);
}
void svPutBitArrElem(svOpenArrayHandle d, svBit value, int indx1, ...) {
  int n = UnpackedDimensions(d);
  if (n < 1) return;
  std::vector<int> idx;
  idx.reserve(n);
  idx.push_back(indx1);
  va_list ap;
  va_start(ap, indx1);
  for (int k = 1; k < n; ++k) idx.push_back(va_arg(ap, int));
  va_end(ap);
  PutBitScalarElem(d, value, idx.data(), n);
}

svScope svGetScope(void) {
  if (auto* runtime = delta::DpiForeignRuntime()) {
    return const_cast<delta::DpiScope*>(runtime->CurrentScope());
  }
  return g_current_scope;
}

svScope svSetScope(svScope scope) {
  if (auto* runtime = delta::DpiForeignRuntime()) {
    auto* prev = const_cast<delta::DpiScope*>(runtime->CurrentScope());
    runtime->SetScope(static_cast<const delta::DpiScope*>(scope));
    return prev;
  }
  svScope prev = g_current_scope;
  g_current_scope = scope;
  return prev;
}

const char* svGetNameFromScope(svScope scope) {
  return delta::DpiNameFromScope(static_cast<const delta::DpiScope*>(scope));
}

svScope svGetScopeFromName(const char* scope_name) {
  if (scope_name == nullptr) return nullptr;
  return const_cast<delta::DpiScope*>(delta::DpiScopeFromName(scope_name));
}

int svPutUserData(svScope scope, void* user_key, void* user_data) {
  if (!delta::DpiScopeIsValid(static_cast<const delta::DpiScope*>(scope)) ||
      user_data == nullptr) {
    return -1;
  }
  DpiUserDataStore()[std::make_pair(scope, user_key)] = user_data;
  return 0;
}

void* svGetUserData(svScope scope, void* user_key) {
  if (!delta::DpiScopeIsValid(static_cast<const delta::DpiScope*>(scope))) {
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

int svIsDisabledState(void) { return delta::DpiCurrentDisabledState() ? 1 : 0; }

void svAckDisabledState(void) { delta::DpiAckCurrentDisable(); }

static bool InvalidTimeScope(svScope scope) {
  return scope != nullptr &&
         !delta::DpiScopeIsValid(static_cast<const delta::DpiScope*>(scope));
}

int svGetTime(svScope scope, svTimeVal* time) {
  if (time == nullptr || InvalidTimeScope(scope)) return -1;
  bool want_scaled_real = (time->type == sv_scaled_real_time);
  int32_t scope_unit = 0;
  if (want_scaled_real &&
      delta::DpiScopeTimescale(static_cast<const delta::DpiScope*>(scope),
                               &scope_unit, nullptr)) {
    time->real = delta::DpiGetSimTimeScaledTo(scope_unit);
    return 0;
  }
  delta::DpiGetSimTime(want_scaled_real, &time->high, &time->low, &time->real);
  return 0;
}

int svGetTimeUnit(svScope scope, int32_t* time_unit) {
  if (time_unit == nullptr || InvalidTimeScope(scope)) return -1;
  if (delta::DpiScopeTimescale(static_cast<const delta::DpiScope*>(scope),
                               time_unit, nullptr)) {
    return 0;
  }
  *time_unit = delta::DpiGetSimTimeUnit();
  return 0;
}

int svGetTimePrecision(svScope scope, int32_t* time_precision) {
  if (time_precision == nullptr || InvalidTimeScope(scope)) return -1;
  if (delta::DpiScopeTimescale(static_cast<const delta::DpiScope*>(scope),
                               nullptr, time_precision)) {
    return 0;
  }
  *time_precision = delta::DpiGetSimTimePrecision();
  return 0;
}
