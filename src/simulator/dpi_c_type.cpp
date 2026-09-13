#include "simulator/dpi_c_type.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <string>
#include <vector>

#include "parser/ast.h"
#include "simulator/dpi_arg_value.h"

namespace delta {

namespace {

// Table H.1: the C type a small SystemVerilog type maps to, the one an input
// of it is passed by value as and a pointer to which an output or inout of
// it is passed by reference as.
const char* SmallCType(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kByte:
      return "char";
    case DataTypeKind::kShortint:
      return "short int";
    case DataTypeKind::kInt:
      return "int";
    case DataTypeKind::kLongint:
      return "long long";
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
      return "svBit";
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return "svLogic";
    default:
      return "";
  }
}

// §H.7.3 and §H.7.7: the canonical chunk type of a packed type -- 2-state
// for bit, 4-state for logic, reg, integer and time.
const char* CanonicalChunkType(DataTypeKind kind) {
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

}  // namespace

bool DpiTypeIsSmall(DataTypeKind kind) {
  // §H.8.7: byte, shortint, int, longint, real, shortreal; scalar bit and
  // logic; chandle and string.
  return SmallCType(kind)[0] != '\0';
}

std::string DpiCTypeOfFormal(const DpiArg& formal, bool open_array) {
  // §H.8.6: an open array is passed by handle whatever the direction, and the
  // handle always carries the const qualifier.
  if (open_array) return "const svOpenArrayHandle";
  const bool kInput = formal.direction == Direction::kInput;
  if (IsPackedArray(formal)) {
    // §H.8.4 and §H.8.8: a packed array is passed by reference to its
    // canonical representation, const for an input.
    const std::string kChunk = CanonicalChunkType(formal.type);
    if (kChunk.empty()) return "";
    return (kInput ? "const " : "") + kChunk + "*";
  }
  const std::string kSmall = SmallCType(formal.type);
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
      kPacked ? CanonicalChunkType(formal.type) : SmallCType(formal.type);
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

}  // namespace delta
