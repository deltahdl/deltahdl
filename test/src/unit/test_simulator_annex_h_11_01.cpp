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

// A formal of Example 4's import, named, typed and, for the vector, sized.
DpiArg Formal(const char* name, DataTypeKind type, bool is_unsigned,
              uint32_t width = 0) {
  DpiArg formal;
  formal.name = name;
  formal.type = type;
  formal.direction = Direction::kInput;
  formal.is_unsigned = is_unsigned;
  formal.width = width;
  return formal;
}

// §H.11.1: the C prototype of Example 4's f7 -- the two int unsigned formals
// as unsigned int by value, the classical correspondence of Table H.1, and
// the [W-1:0] formal as the canonical const svBitVecVal*.
TEST(DpiTwoStateArguments, TheCHeaderOfF7IsTheExamples) {
  EXPECT_EQ(DpiCFunctionHeader("f7", DataTypeKind::kVoid,
                               {Formal("fbv1", DataTypeKind::kInt, true),
                                Formal("fbv2", DataTypeKind::kInt, true),
                                Formal("fbv3", DataTypeKind::kBit, true, 33)}),
            "void f7(const unsigned int fbv1, const unsigned int fbv2, const "
            "svBitVecVal* fbv3)");
}

// §H.11.1: a DPI formal can be of a C-compatible type with an arbitrary
// 2-state bit vector actual associated with it -- the 30-bit abv2 bound to
// the int unsigned fbv2 is extended to the formal's 32 bits by the caller's
// coercion, and the int abv1 bound to fbv1 needs none.
TEST(DpiTwoStateArguments, AnArbitraryTwoStateVectorIsCoercedToTheCFormal) {
  EXPECT_EQ(DpiCoercionOfPackedActual(30, 32), DpiActualCoercion::kExtend);
  EXPECT_EQ(DpiCoercionOfPackedActual(32, 32), DpiActualCoercion::kNone);
}

// §H.11.1: the C-compatible technique holds a 2-state vector of up to 64
// bits; a vector exceeding 64 bits requires the canonical technique, and
// the 33-bit abv3 may take either, the C-compatible one being the more
// efficient.
TEST(DpiTwoStateArguments, TheCanonicalTechniqueIsRequiredBeyondSixtyFourBits) {
  EXPECT_TRUE(DpiCCompatibleFormalCanHoldTwoStateVector(33));
  EXPECT_TRUE(DpiCCompatibleFormalCanHoldTwoStateVector(64));
  EXPECT_FALSE(DpiCCompatibleFormalCanHoldTwoStateVector(65));
  EXPECT_EQ(DpiTechniqueRequiredForTwoStateVector(65),
            DpiTwoStateTechnique::kCanonical);
  EXPECT_EQ(DpiTechniqueRequiredForTwoStateVector(33),
            DpiTwoStateTechnique::kCCompatibleFormal);
  EXPECT_TRUE(
      DpiTechniqueIsMoreEfficient(DpiTwoStateTechnique::kCCompatibleFormal,
                                  DpiTwoStateTechnique::kCanonical));
  EXPECT_FALSE(
      DpiTechniqueIsMoreEfficient(DpiTwoStateTechnique::kCanonical,
                                  DpiTwoStateTechnique::kCCompatibleFormal));
}

// §H.11.1 under the runtime: f7 registered with the example's formals and
// called with abv1, abv2 and abv3 -- the first two arriving as the C ints
// the formals name and the 33-bit abv3 as two canonical chunks whose second
// holds its top bit, which the 2-state svdpi utilities read.
TEST(DpiTwoStateArguments, F7ReceivesTwoIntsAndACanonicalVector) {
  DpiRuntime rt;
  DpiRtFunction f7;
  f7.sv_name = "f7";
  f7.c_name = "f7";
  f7.return_type = DataTypeKind::kVoid;
  f7.args = {Formal("fbv1", DataTypeKind::kInt, true),
             Formal("fbv2", DataTypeKind::kInt, true),
             Formal("fbv3", DataTypeKind::kBit, true, 33)};
  static uint32_t s_fbv1 = 0;
  static uint32_t s_fbv2 = 0;
  static std::vector<SvLogicVecVal> s_fbv3;
  f7.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    s_fbv1 = static_cast<uint32_t>(args[0].AsInt());
    s_fbv2 = static_cast<uint32_t>(args[1].AsInt());
    s_fbv3 = args[2].AsLogicVecWords();
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(f7);

  const DpiArgValue kAbv1 = DpiArgValue::FromInt(-1);
  const DpiArgValue kAbv2 = DpiArgValue::FromInt(0x2ABCDEF0);
  const DpiArgValue kAbv3 = DpiArgValue::FromLogicVecWords(
      {SvLogicVecVal{0x80000001u, 0}, SvLogicVecVal{1u, 0}}, 33,
      DataTypeKind::kBit);
  rt.CallImport("f7", {kAbv1, kAbv2, kAbv3});
  EXPECT_EQ(s_fbv1, 0xFFFFFFFFu);
  EXPECT_EQ(s_fbv2, 0x2ABCDEF0u);
  ASSERT_EQ(s_fbv3.size(), DpiCanonicalWordCount(33));
  EXPECT_EQ(s_fbv3[0].aval, 0x80000001u);
  EXPECT_EQ(s_fbv3[1].aval, 1u);
}

}  // namespace
