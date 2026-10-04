#include "simulator/dpi_arg_value.h"

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "parser/ast_type.h"

namespace delta {

DpiArgValue DpiArgValue::FromInt(int32_t v) {
  DpiArgValue a;
  a.type = DataTypeKind::kInt;
  a.data.int_val = v;
  return a;
}

DpiArgValue DpiArgValue::FromLongint(int64_t v) {
  DpiArgValue a;
  a.type = DataTypeKind::kLongint;
  a.data.longint_val = v;
  return a;
}

DpiArgValue DpiArgValue::FromReal(double v) {
  DpiArgValue a;
  a.type = DataTypeKind::kReal;
  a.data.real_val = v;
  return a;
}

DpiArgValue DpiArgValue::FromString(std::string v) {
  DpiArgValue a;
  a.type = DataTypeKind::kString;
  a.string_val = std::move(v);
  return a;
}

DpiArgValue DpiArgValue::FromChandle(SvChandle v) {
  DpiArgValue a;
  a.type = DataTypeKind::kChandle;
  a.data.chandle_val = v;
  return a;
}

DpiArgValue DpiArgValue::FromBit(SvBit v) {
  DpiArgValue a;
  a.type = DataTypeKind::kBit;
  a.data.bit_val = v;
  return a;
}

DpiArgValue DpiArgValue::FromLogic(SvLogic v) {
  DpiArgValue a;
  a.type = DataTypeKind::kLogic;
  a.data.logic_val = v;
  return a;
}

DpiArgValue DpiArgValue::FromLogicVec(SvLogicVecVal v) {
  DpiArgValue a;
  a.type = DataTypeKind::kInteger;
  a.data.logic_vec_val = v;
  return a;
}

DpiArgValue DpiArgValue::FromLogicVecWords(std::vector<SvLogicVecVal> words,
                                           uint32_t width, DataTypeKind type) {
  DpiArgValue a;
  a.type = type;
  a.vec_words = std::move(words);
  a.vec_width = width;
  return a;
}

int32_t DpiArgValue::AsInt() const { return data.int_val; }
int64_t DpiArgValue::AsLongint() const { return data.longint_val; }
double DpiArgValue::AsReal() const { return data.real_val; }
const std::string& DpiArgValue::AsString() const { return string_val; }
SvChandle DpiArgValue::AsChandle() const { return data.chandle_val; }
SvBit DpiArgValue::AsBit() const { return data.bit_val; }
SvLogic DpiArgValue::AsLogic() const { return data.logic_val; }
SvLogicVecVal DpiArgValue::AsLogicVec() const { return data.logic_vec_val; }

}  // namespace delta
