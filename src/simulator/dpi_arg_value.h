#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"

namespace delta {

using SvBit = uint8_t;
using SvScalar = uint8_t;

using SvLogic = uint8_t;

using SvBitVecVal = uint32_t;

// §H.10.1.2 / svdpi.h's s_vpi_vecval: the canonical representation of a
// four-state value, carried as this pair rather than as one word because a
// 4-state bit needs two bits to say it is x or z. The members carry no default
// member initializer, as the standard's own declaration of the type does not:
// a variant member of DpiArgValue's union is written here, and a member type
// with a non-trivial default constructor deletes the union's.
struct SvLogicVecVal {
  uint32_t aval;
  uint32_t bval;
};

using SvChandle = void*;

struct SvOpenArrayHandle {
  void* data = nullptr;
  uint32_t size = 0;
  uint32_t elem_width = 0;
};

// §35.5.6: one formal argument of an imported or exported subroutine, as the
// declaration writes it -- the name a call site can bind the actual to by
// §35.6, the SystemVerilog data type the value crosses as, and the direction
// §35.5.1.2 reads to decide which way it crosses.
struct DpiArg {
  std::string_view name;
  DataTypeKind type = DataTypeKind::kInt;
  Direction direction = Direction::kInput;
  // §35.6: the default value expression the declaration gave this formal,
  // supplied where the call site omits the argument.
  const Expr* default_value = nullptr;
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
    // §35.2.2.1: the aval/bval pair a four-state integral value crosses as.
    // "The implementation (representation and layout) of 4-state values ... is
    // irrelevant for SystemVerilog semantics and can only impact the foreign
    // side of the interface", so an x or a z has to survive the crossing; a
    // single word says a bit is 0 or 1 and cannot say it is x or z.
    SvLogicVecVal logic_vec_val;
  } data = {};
  std::string string_val;

  static DpiArgValue FromInt(int32_t v);
  static DpiArgValue FromLongint(int64_t v);
  static DpiArgValue FromReal(double v);
  static DpiArgValue FromString(std::string v);
  static DpiArgValue FromChandle(SvChandle v);
  static DpiArgValue FromBit(SvBit v);
  static DpiArgValue FromLogic(SvLogic v);
  // §35.2.2.1: a four-state integral value of type `integer`, carried as the
  // canonical aval/bval pair rather than as a plain word.
  static DpiArgValue FromLogicVec(SvLogicVecVal v);

  int32_t AsInt() const;
  int64_t AsLongint() const;
  double AsReal() const;
  const std::string& AsString() const;
  SvChandle AsChandle() const;
  SvBit AsBit() const;
  SvLogic AsLogic() const;
  SvLogicVecVal AsLogicVec() const;
};

// §35.6.2: a value-change event the SystemVerilog simulator raises for an
// output or inout actual after an imported function returns. `index` is the
// argument's position in the call; `old_value` and `new_value` bracket the
// change. The simulator is responsible for detecting and handling these
// changes once control has returned from the import, never while it runs.
struct DpiArgValueChange {
  size_t index = 0;
  DpiArgValue old_value;
  DpiArgValue new_value;
};

using DpiRtCallback =
    std::function<DpiArgValue(const std::vector<DpiArgValue>&)>;

// §35.5.1.2: an import implementation that participates in output and inout
// argument passing. The argument vector is mutable so the foreign function can
// deposit values into its output and inout formals; the return value is the
// function result. Unlike DpiRtCallback (input-only), values written here to
// output/inout positions become visible outside the call.
using DpiRtArgCallback = std::function<DpiArgValue(std::vector<DpiArgValue>&)>;

// §35.6.1: `v` converted to `target`, unchanged when already of that type.
DpiArgValue CoerceArgValue(const DpiArgValue& v, DataTypeKind target);

}  // namespace delta
