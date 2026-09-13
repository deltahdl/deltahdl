#include "simulator/dpi_c_type.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <string>
#include <string_view>
#include <vector>

#include "parser/ast.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/svdpi_open_array.h"

namespace delta {

namespace {

// The C type a small SystemVerilog type maps to, the one an input of it is
// passed by value as and a pointer to which an output or inout of it is
// passed by reference as: Table H.1's row, a scalar bit or logic under the
// svBit and svLogic names svdpi.h gives its unsigned char.
std::string SmallCType(DataTypeKind kind, bool is_unsigned) {
  switch (kind) {
    case DataTypeKind::kBit:
      return "svBit";
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return "svLogic";
    default:
      return DpiCTypeOfBasicType(kind, is_unsigned);
  }
}

// A formal of bit, logic or reg whose declaration gave it a width is a packed
// array; one without is the scalar.
bool IsPackedArray(const DpiArg& formal) {
  switch (formal.type) {
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return formal.width > 1;
    case DataTypeKind::kInteger:
    case DataTypeKind::kTime:
      return true;
    default:
      return false;
  }
}

// §H.7.3: the width of a packed formal, which integer and time carry in
// their type and a bit, logic or reg array in its declaration.
uint32_t PackedWidth(const DpiArg& formal) {
  switch (formal.type) {
    case DataTypeKind::kInteger:
      return 32;
    case DataTypeKind::kTime:
      return 64;
    default:
      return formal.width;
  }
}

// Table H.1: sizeof the C type a small type maps to.
std::size_t SmallCTypeBytes(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kByte:
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return 1;
    case DataTypeKind::kShortint:
      return sizeof(short int);
    case DataTypeKind::kInt:
      return sizeof(int);
    case DataTypeKind::kLongint:
      return sizeof(long long);
    case DataTypeKind::kReal:
    case DataTypeKind::kRealtime:
      return sizeof(double);
    case DataTypeKind::kShortreal:
      return sizeof(float);
    case DataTypeKind::kChandle:
    case DataTypeKind::kString:
      return sizeof(void*);
    default:
      return 0;
  }
}

// The count of a dimension's range, however it runs.
uint32_t SizeOfDimension(const SvActualDimension& dim) {
  return static_cast<uint32_t>(std::abs(dim.high - dim.low)) + 1U;
}

// §H.7.1: the range of the one-dimensional packed array equivalent to the
// actual's packed dimensions, one element per combination of their indices,
// normalized to [size-1:0].
SvActualDimension LinearizedNormalizedRange(
    const std::vector<SvActualDimension>& actual_packed) {
  int32_t size = actual_packed.empty() ? 0 : 1;
  for (const SvActualDimension& dim : actual_packed) {
    size *= static_cast<int32_t>(SizeOfDimension(dim));
  }
  return SvActualDimension{size > 0 ? size - 1 : 0, 0};
}

}  // namespace

bool DpiTypeIsSmall(DataTypeKind kind) {
  // §H.8.7: byte, shortint, int, longint, real, shortreal; scalar bit and
  // logic; chandle and string.
  return !SmallCType(kind, false).empty();
}

std::string DpiCTypeOfFormal(const DpiArg& formal, bool open_array) {
  // §H.8.6: an open array is passed by handle whatever the direction, and the
  // handle always carries the const qualifier.
  if (open_array) return "const svOpenArrayHandle";
  const bool kInput = formal.direction == Direction::kInput;
  if (IsPackedArray(formal)) {
    // §H.8.4 and §H.8.8: a packed array is passed by reference to its
    // canonical representation, const for an input.
    const std::string kChunk = DpiCanonicalElementType(formal.type);
    if (kChunk.empty()) return "";
    return (kInput ? "const " : "") + kChunk + "*";
  }
  const std::string kSmall = SmallCType(formal.type, formal.is_unsigned);
  if (kSmall.empty()) return "";
  // §H.8.7: an input of a small type is passed by value with the const
  // qualifier, which a string's table type const char* already carries
  // (§H.8.10); §H.8.8: an inout or output is passed by reference.
  if (!kInput) return kSmall + "*";
  return kSmall.starts_with("const ") ? kSmall : "const " + kSmall;
}

std::size_t DpiCElementBytes(const DpiArg& formal) {
  if (IsPackedArray(formal)) {
    // §H.7.7: the canonical representation, one chunk per 32 bits, a
    // 2-state chunk being one word and a 4-state one an aval/bval pair.
    const std::size_t kChunk = formal.type == DataTypeKind::kBit
                                   ? sizeof(SvBitVecVal)
                                   : sizeof(SvLogicVecVal);
    return DpiCanonicalWordCount(PackedWidth(formal)) * kChunk;
  }
  return SmallCTypeBytes(formal.type);
}

std::string DpiCDeclarationOfUnpackedFormal(
    const DpiArg& formal, const std::vector<SvActualDimension>& unpacked_dims) {
  const bool kPacked = IsPackedArray(formal);
  const std::string kElement =
      kPacked ? DpiCanonicalElementType(formal.type)
              : SmallCType(formal.type, formal.is_unsigned);
  if (kElement.empty()) return "";
  std::string decl = formal.direction == Direction::kInput ? "const " : "";
  decl += kElement + " " + std::string(formal.name);
  for (const SvActualDimension& dim : unpacked_dims) {
    decl += "[" + std::to_string(SizeOfDimension(dim)) + "]";
  }
  if (kPacked) {
    decl +=
        "[" + std::to_string(DpiCanonicalWordCount(PackedWidth(formal))) + "]";
  }
  return decl;
}

std::vector<uint32_t> DpiCIndicesOfUnpackedElement(
    const std::vector<SvActualDimension>& unpacked_dims,
    const std::vector<int32_t>& sv_indices) {
  std::vector<uint32_t> c_indices;
  for (std::size_t k = 0; k < unpacked_dims.size() && k < sv_indices.size();
       ++k) {
    const int32_t kLow = std::min(unpacked_dims[k].low, unpacked_dims[k].high);
    c_indices.push_back(static_cast<uint32_t>(sv_indices[k] - kLow));
  }
  return c_indices;
}

std::size_t DpiCOffsetOfUnpackedElement(
    const DpiArg& formal, const std::vector<SvActualDimension>& unpacked_dims,
    const std::vector<int32_t>& sv_indices) {
  const std::vector<uint32_t> kIndices =
      DpiCIndicesOfUnpackedElement(unpacked_dims, sv_indices);
  // Row-major: each dimension's index is scaled by the count of elements
  // under one step of it, the product of the sizes of the dimensions after.
  std::size_t linear = 0;
  for (std::size_t k = 0; k < kIndices.size(); ++k) {
    linear = linear * SizeOfDimension(unpacked_dims[k]) + kIndices[k];
  }
  return linear * DpiCElementBytes(formal);
}

bool DpiPartSelectAppliesTo(const DpiArg& formal) {
  // §H.11.5: a slice of a packed array of bit or logic, which is what has a
  // canonical representation to slice.
  return IsPackedArray(formal);
}

bool DpiPartSelectIsDetermined(uint32_t width, int i, int w) {
  if (w < 1 || w > kDpiPartSelectMaxWidth || i < 0) return false;
  // [(i+w-1):i] within [width-1:0]: the bit past the top of the select is
  // no further than the bit past the top of the array.
  return static_cast<uint64_t>(i) + static_cast<uint64_t>(w) <= width;
}

int DpiNormalizedBitIndex(SvActualDimension packed, int32_t sv_index) {
  // §H.7.6 b): [L:R] is normalized to [abs(L-R):0], the LSB at R index 0.
  return std::abs(sv_index - packed.high);
}

uint64_t DpiOpenArrayElementCount(const SvOpenArrayDesc& desc) {
  // §H.12: the actual's size, over the unpacked dimensions the handle
  // records after the packed part at dimension 0; a dimension is counted
  // however its range runs.
  if (desc.ranges == nullptr) return 0;
  uint64_t count = 1;
  for (int d = 1; d < desc.n_dims; ++d) {
    const SvOpenArrayDimRange& r = desc.ranges[d];
    count *= static_cast<uint64_t>(
        std::abs(static_cast<int64_t>(r.left) - r.right) + 1);
  }
  return count;
}

uint64_t DpiOpenArrayCapacityBytes(const SvOpenArrayDesc& desc) {
  return DpiOpenArrayElementCount(desc) * desc.elem_size;
}

bool DpiOpenArrayWriteIsDefined(const SvOpenArrayDesc& desc, uint64_t bytes) {
  return bytes <= DpiOpenArrayCapacityBytes(desc);
}

std::string DpiCanonicalElementType(DataTypeKind kind) {
  // §H.7.3 and §H.7.7: 2-state for bit, 4-state for logic and reg and for
  // integer and time.
  switch (kind) {
    case DataTypeKind::kBit:
      return "svBitVecVal";
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kInteger:
    case DataTypeKind::kTime:
      return "svLogicVecVal";
    default:
      return "";
  }
}

DpiCanonicalBitPosition DpiCanonicalPositionOfBit(uint32_t bit) {
  // §H.7.7: element 0 holds bits 0 to 31, element 1 the 32 more significant
  // bits, and so on.
  return DpiCanonicalBitPosition{bit / kDpiCanonicalElementBits,
                                 bit % kDpiCanonicalElementBits};
}

uint32_t DpiCanonicalUnusedBits(uint32_t width) {
  // §H.7.7: the last element holds width mod 32 bits when the width is not
  // a multiple of 32, and the rest of it is unused.
  const uint32_t kUsed = width % kDpiCanonicalElementBits;
  return kUsed == 0 ? 0 : kDpiCanonicalElementBits - kUsed;
}

uint32_t DpiCanonicalLastElementWithUnusedBits(uint32_t last, uint32_t width,
                                               bool is_signed) {
  const uint32_t kUnused = DpiCanonicalUnusedBits(width);
  if (kUnused == 0) return last;
  const uint32_t kUsed = kDpiCanonicalElementBits - kUnused;
  const uint32_t kUsedMask = (1U << kUsed) - 1U;
  // §H.7.7: masking for an unsigned array, sign extension for a signed one
  // from the array's most significant bit, bit kUsed-1 of the element.
  const bool kNegative = is_signed && ((last >> (kUsed - 1)) & 1U) != 0;
  return kNegative ? (last | ~kUsedMask) : (last & kUsedMask);
}

std::string DpiCTypeOfBasicType(DataTypeKind kind, bool is_unsigned) {
  switch (kind) {
    case DataTypeKind::kByte:
      return is_unsigned ? "unsigned char" : "char";
    case DataTypeKind::kShortint:
      return is_unsigned ? "unsigned short" : "short int";
    case DataTypeKind::kInt:
      return is_unsigned ? "unsigned int" : "int";
    case DataTypeKind::kLongint:
      return is_unsigned ? "unsigned long long" : "long long";
    case DataTypeKind::kReal:
    case DataTypeKind::kRealtime:
      return "double";
    case DataTypeKind::kShortreal:
      return "float";
    case DataTypeKind::kChandle:
      return "void*";
    case DataTypeKind::kString:
      return "const char*";
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return "unsigned char";
    default:
      return "";
  }
}

DpiActualCoercion DpiCoercionOfPackedActual(uint32_t actual_width,
                                            uint32_t formal_width) {
  if (actual_width > formal_width) return DpiActualCoercion::kTruncate;
  if (actual_width < formal_width) return DpiActualCoercion::kExtend;
  return DpiActualCoercion::kNone;
}

bool DpiCTypeMatchesFormal(const DpiArg& formal, bool open_array,
                           std::string_view c_type) {
  // The spelling DpiCTypeOfFormal gives puts the * against the type, so the
  // prototype's spaces around a * are dropped before the comparison.
  std::string spelled;
  for (std::size_t i = 0; i < c_type.size(); ++i) {
    if (c_type[i] == ' ' && (i + 1 == c_type.size() || c_type[i + 1] == '*' ||
                             (!spelled.empty() && spelled.back() == '*'))) {
      continue;
    }
    spelled += c_type[i];
  }
  return spelled == DpiCTypeOfFormal(formal, open_array);
}

std::vector<SvActualDimension> DpiFormalRangesAtCall(
    const DpiFormalDimension& packed,
    const std::vector<DpiFormalDimension>& unpacked,
    const std::vector<SvActualDimension>& actual_packed,
    const std::vector<SvActualDimension>& actual_unpacked) {
  std::vector<SvActualDimension> ranges;
  ranges.push_back(packed.sized ? packed.range
                                : LinearizedNormalizedRange(actual_packed));
  for (std::size_t k = 0; k < unpacked.size(); ++k) {
    if (unpacked[k].sized) {
      ranges.push_back(unpacked[k].range);
    } else if (k < actual_unpacked.size()) {
      ranges.push_back(actual_unpacked[k]);
    }
  }
  return ranges;
}

bool DpiForeignCodeMayModifyFormal(Direction direction) {
  return direction != Direction::kInput;
}

bool DpiFormalIsDeterminedOnEntry(Direction direction) {
  return direction != Direction::kOutput;
}

bool DpiSimulatorDetectsChangesOf(Direction direction) {
  return direction == Direction::kOutput || direction == Direction::kInout;
}

DpiImportAccess DpiAccessOfImport(bool is_context) {
  return is_context ? DpiImportAccess::kAnyDataObject
                    : DpiImportAccess::kActualArgumentsOnly;
}

bool DpiImportMaySafelyCallOtherApis(bool is_context) { return is_context; }

bool DpiImportCallIsOptimizationBarrier(bool is_context) { return is_context; }

bool DpiSideMayFree(DpiMemorySide allocated_by, DpiMemorySide freed_by) {
  return allocated_by == freed_by;
}

DpiMemorySide DpiSideOwningBlockBehindChandle() { return DpiMemorySide::kC; }

DpiMemorySide DpiSideOfImportedCall() { return DpiMemorySide::kC; }

}  // namespace delta
