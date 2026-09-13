#include "simulator/dpi_c_type.h"

#include <string>

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

}  // namespace delta
