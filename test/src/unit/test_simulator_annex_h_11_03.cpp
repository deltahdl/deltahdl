#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "parser/ast.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

// A formal of Example 5's import, an input declared under the named type.
DpiArg Formal(const char* name, DataTypeKind kind, const char* type_name) {
  DpiArg formal;
  formal.name = name;
  formal.type = kind;
  formal.direction = Direction::kInput;
  formal.type_name = type_name;
  return formal;
}

// §H.11.3: a packed struct or union argument corresponds to a
// one-dimensional packed array argument -- the three-bit S and U are the
// same const svBitVecVal* formal the three-bit array A is.
TEST(DpiPackedAggregateArguments, APackedStructOrUnionIsAPackedArrayFormal) {
  const DpiArg kA = DpiPackedAggregateAsPackedArrayFormal(
      Formal("fa", DataTypeKind::kBit, "A"), false, 3);
  const DpiArg kS = DpiPackedAggregateAsPackedArrayFormal(
      Formal("fs", DataTypeKind::kStruct, "S"), false, 3);
  const DpiArg kU = DpiPackedAggregateAsPackedArrayFormal(
      Formal("fu", DataTypeKind::kUnion, "U"), false, 3);
  EXPECT_EQ(kS.type, DataTypeKind::kBit);
  EXPECT_EQ(kU.type, DataTypeKind::kBit);
  EXPECT_EQ(kS.width, 3u);
  EXPECT_EQ(DpiCTypeOfFormal(kA, false), "const svBitVecVal*");
  EXPECT_EQ(DpiCTypeOfFormal(kS, false), "const svBitVecVal*");
  EXPECT_EQ(DpiCTypeOfFormal(kU, false), "const svBitVecVal*");
  EXPECT_EQ(DpiCFunctionHeader("f8", DataTypeKind::kVoid, {kA, kS, kU}),
            "void f8(const svBitVecVal* fa, const svBitVecVal* fs, const "
            "svBitVecVal* fu)");
}

// §H.11.3: a packed struct or union of 4-state members corresponds to a
// packed logic array, the const svLogicVecVal* formal.
TEST(DpiPackedAggregateArguments, AFourStatePackedAggregateIsALogicArray) {
  const DpiArg kFourState = DpiPackedAggregateAsPackedArrayFormal(
      Formal("fs", DataTypeKind::kStruct, "S4"), true, 3);
  EXPECT_EQ(kFourState.type, DataTypeKind::kLogic);
  EXPECT_EQ(DpiCTypeOfFormal(kFourState, false), "const svLogicVecVal*");
}

// The value the example's initial block builds: the packed struct S with a
// set and b and c clear is 3'b100, its first member being its most
// significant bit (§7.2.1), which is the 4 the array a and the union's array
// member u.a are assigned.
uint32_t PackedS(bool a, bool b, bool c) {
  return (a ? 4u : 0u) | (b ? 2u : 0u) | (c ? 1u : 0u);
}

// §H.11.3 under the runtime: f8 registered with the three packed array
// formals and called with a, s and u as the initial block does -- each
// arriving as one canonical chunk whose value is 4, so that the example's
// printf reads "fa is 4, fs is 4, fu is 4".
TEST(DpiPackedAggregateArguments, F8ReceivesFourFromTheArrayStructAndUnion) {
  DpiRuntime rt;
  DpiRtFunction f8;
  f8.sv_name = "f8";
  f8.c_name = "f8";
  f8.return_type = DataTypeKind::kVoid;
  f8.args = {DpiPackedAggregateAsPackedArrayFormal(
                 Formal("fa", DataTypeKind::kBit, "A"), false, 3),
             DpiPackedAggregateAsPackedArrayFormal(
                 Formal("fs", DataTypeKind::kStruct, "S"), false, 3),
             DpiPackedAggregateAsPackedArrayFormal(
                 Formal("fu", DataTypeKind::kUnion, "U"), false, 3)};
  static std::string s_printed;
  f8.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    s_printed = "fa is " + std::to_string(args[0].AsLogicVecWords()[0].aval) +
                ", fs is " + std::to_string(args[1].AsLogicVecWords()[0].aval) +
                ", fu is " + std::to_string(args[2].AsLogicVecWords()[0].aval);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(f8);

  auto three_bits = [](uint32_t value) {
    return DpiArgValue::FromLogicVecWords({SvLogicVecVal{value, 0}}, 3,
                                          DataTypeKind::kBit);
  };
  const uint32_t kA = 4;
  const uint32_t kS = PackedS(true, false, false);
  const uint32_t kU = 4;
  rt.CallImport("f8", {three_bits(kA), three_bits(kS), three_bits(kU)});
  EXPECT_EQ(s_printed, "fa is 4, fs is 4, fu is 4");
}

}  // namespace
