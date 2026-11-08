#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <vector>

#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

using SvBit = uint8_t;
using SvScalar = uint8_t;

using SvLogic = uint8_t;

using SvBitVecVal = uint32_t;

struct SvLogicVecVal {
  uint32_t aval;
  uint32_t bval;
};

using SvChandle = void*;

inline constexpr uint32_t kDpiInlineValueBits = 64;

inline uint32_t DpiInlineValueBits(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return 1;
    case DataTypeKind::kInteger:
      return 32;
    default:
      return kDpiInlineValueBits;
  }
}

inline uint32_t DpiCanonicalWordCount(uint32_t width) {
  return (width + 31U) / 32U;
}

struct SvActualDimension {
  int32_t low = 0;
  int32_t high = 0;
};

struct DpiArrayRange {
  int32_t left = 0;
  int32_t right = 0;
};

struct SvOpenArrayHandle {
  void* data = nullptr;
  uint32_t size = 0;
  uint32_t elem_width = 0;
  int32_t low = 0;
  int32_t high = 0;
};

struct DpiArg {
  std::string_view name;
  DataTypeKind type = DataTypeKind::kInt;
  Direction direction = Direction::kInput;
  const Expr* default_value = nullptr;
  uint32_t width = 0;
  bool is_packed_array = false;
  bool is_unsigned = false;
  std::string_view type_name = {};
  bool has_unpacked_dimensions = false;
  std::vector<SvActualDimension> unpacked_dims = {};
  std::vector<DpiArg> members = {};
  bool is_open_array = false;
  const FunctionArg* declaration = nullptr;
};

struct DpiArgValue {
  DataTypeKind type = DataTypeKind::kInt;
  union {
    int32_t int_val;
    int64_t longint_val;
    double real_val;
    SvChandle chandle_val;
    SvBit bit_val;
    SvLogic logic_val;
    SvLogicVecVal logic_vec_val;
  } data = {};
  std::string string_val;
  std::vector<SvLogicVecVal> vec_words;
  uint32_t vec_width = 0;
  std::vector<DpiArgValue> elements;
  std::vector<DpiArrayRange> ranges;

  static DpiArgValue FromInt(int32_t v);
  static DpiArgValue FromLongint(int64_t v);
  static DpiArgValue FromReal(double v);
  static DpiArgValue FromString(std::string v);
  static DpiArgValue FromChandle(SvChandle v);
  static DpiArgValue FromBit(SvBit v);
  static DpiArgValue FromLogic(SvLogic v);
  static DpiArgValue FromLogicVec(SvLogicVecVal v);
  static DpiArgValue FromLogicVecWords(std::vector<SvLogicVecVal> words,
                                       uint32_t width, DataTypeKind type);

  int32_t AsInt() const;
  int64_t AsLongint() const;
  double AsReal() const;
  const std::string& AsString() const;
  SvChandle AsChandle() const;
  SvBit AsBit() const;
  SvLogic AsLogic() const;
  SvLogicVecVal AsLogicVec() const;
  bool IsWideVec() const { return !vec_words.empty(); }
  const std::vector<SvLogicVecVal>& AsLogicVecWords() const {
    return vec_words;
  }
  uint32_t VecWidth() const { return vec_width; }
  bool IsArray() const { return !elements.empty(); }
};

struct DpiArgValueChange {
  size_t index = 0;
  DpiArgValue old_value;
  DpiArgValue new_value;
};

using DpiRtCallback =
    std::function<DpiArgValue(const std::vector<DpiArgValue>&)>;

using DpiRtArgCallback = std::function<DpiArgValue(std::vector<DpiArgValue>&)>;

DpiArgValue CoerceArgValue(const DpiArgValue& v, DataTypeKind target);

}  // namespace delta
