// Annex H.14.2: the SV3.1a-style packed data functions svdpi_sv31a.h declares.
// This simulator's actual representation of a packed array is the canonical
// one, so the translation functions copy chunks as they are and the select
// functions delegate to the canonical utilities of §H.11.5 over the same
// layout, an svLogicVec32's c and d being the aval and bval of a chunk.
#include "simulator/svdpi_sv31a.h"

#include <cstdint>

namespace {

int Chunks(int width) { return width <= 0 ? 0 : SV_CANONICAL_SIZE(width); }

}  // namespace

int svSizeOfBitPackedArr(int width) {
  return Chunks(width) * static_cast<int>(sizeof(svBitVecVal));
}

int svSizeOfLogicPackedArr(int width) {
  return Chunks(width) * static_cast<int>(sizeof(svLogicVecVal));
}

void svPutBitVec32(svBitPackedArrRef d, const svBitVec32* s, int w) {
  if (d == nullptr || s == nullptr) return;
  auto* dst = static_cast<svBitVecVal*>(d);
  for (int k = 0; k < Chunks(w); ++k) dst[k] = s[k];
}

void svPutLogicVec32(svLogicPackedArrRef d, const svLogicVec32* s, int w) {
  if (d == nullptr || s == nullptr) return;
  auto* dst = static_cast<svLogicVecVal*>(d);
  for (int k = 0; k < Chunks(w); ++k) {
    dst[k].aval = s[k].c;
    dst[k].bval = s[k].d;
  }
}

void svGetBitVec32(svBitVec32* d, svBitPackedArrRef s, int w) {
  if (d == nullptr || s == nullptr) return;
  const auto* src = static_cast<const svBitVecVal*>(s);
  for (int k = 0; k < Chunks(w); ++k) d[k] = src[k];
}

void svGetLogicVec32(svLogicVec32* d, svLogicPackedArrRef s, int w) {
  if (d == nullptr || s == nullptr) return;
  const auto* src = static_cast<const svLogicVecVal*>(s);
  for (int k = 0; k < Chunks(w); ++k) {
    d[k].c = src[k].aval;
    d[k].d = src[k].bval;
  }
}

svBit svGetSelectBit(svBitPackedArrRef s, int i) {
  if (s == nullptr || i < 0) return sv_0;
  return svGetBitselBit(static_cast<const svBitVecVal*>(s), i);
}

svLogic svGetSelectLogic(svLogicPackedArrRef s, int i) {
  if (s == nullptr || i < 0) return sv_x;
  return svGetBitselLogic(static_cast<const svLogicVecVal*>(s), i);
}

void svPutSelectBit(svBitPackedArrRef d, int i, svBit s) {
  if (d == nullptr || i < 0) return;
  svPutBitselBit(static_cast<svBitVecVal*>(d), i, s);
}

void svPutSelectLogic(svLogicPackedArrRef d, int i, svLogic s) {
  if (d == nullptr || i < 0) return;
  svPutBitselLogic(static_cast<svLogicVecVal*>(d), i, s);
}

void svGetPartSelectBit(svBitVec32* d, svBitPackedArrRef s, int i, int w) {
  if (d == nullptr || s == nullptr || i < 0) return;
  svGetPartselBit(d, static_cast<const svBitVecVal*>(s), i, w);
}

svBitVec32 svGetBits(svBitPackedArrRef s, int i, int w) {
  svBitVec32 bits = 0;
  svGetPartSelectBit(&bits, s, i, w);
  return bits;
}

svBitVec32 svGet32Bits(svBitPackedArrRef s, int i) {
  return svGetBits(s, i, 32);
}

uint64_t svGet64Bits(svBitPackedArrRef s, int i) {
  // Two 32-bit part-selects, the upper one starting 32 bits above the lower.
  const uint64_t kLow = svGetBits(s, i, 32);
  const uint64_t kHigh = svGetBits(s, i + 32, 32);
  return (kHigh << 32) | kLow;
}

void svGetPartSelectLogic(svLogicVec32* d, svLogicPackedArrRef s, int i,
                          int w) {
  if (d == nullptr || s == nullptr || i < 0) return;
  svLogicVecVal chunk = {d->c, d->d};
  svGetPartselLogic(&chunk, static_cast<const svLogicVecVal*>(s), i, w);
  d->c = chunk.aval;
  d->d = chunk.bval;
}

void svPutPartSelectBit(svBitPackedArrRef d, svBitVec32 s, int i, int w) {
  if (d == nullptr || i < 0) return;
  svPutPartselBit(static_cast<svBitVecVal*>(d), s, i, w);
}

void svPutPartSelectLogic(svLogicPackedArrRef d, svLogicVec32 s, int i, int w) {
  if (d == nullptr || i < 0) return;
  const svLogicVecVal kChunk = {s.c, s.d};
  svPutPartselLogic(static_cast<svLogicVecVal*>(d), kChunk, i, w);
}
