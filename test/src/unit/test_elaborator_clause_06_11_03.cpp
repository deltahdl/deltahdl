// §6.11.3: Signed and unsigned integer types

#include <gtest/gtest.h>

#include "elaborator/type_eval.h"
#include "fixture_simulator.h"
#include "parser/ast.h"

using namespace delta;

namespace {

TEST(TypeEval, ImplicitlySignedTypes) {
  // §6.8: integer, int, shortint, longint, byte are implicitly signed.
  // logic, reg, bit are NOT implicitly signed.
  struct Case {
    DataTypeKind kind;
    bool expected;
    const char* label;
  };
  const Case kCases[] = {
      {DataTypeKind::kInteger, true, "integer"},
      {DataTypeKind::kInt, true, "int"},
      {DataTypeKind::kShortint, true, "shortint"},
      {DataTypeKind::kLongint, true, "longint"},
      {DataTypeKind::kByte, true, "byte"},
      {DataTypeKind::kLogic, false, "logic"},
      {DataTypeKind::kReg, false, "reg"},
      {DataTypeKind::kBit, false, "bit"},
  };
  for (const auto& c : kCases) {
    EXPECT_EQ(IsImplicitlySigned(c.kind), c.expected) << c.label;
  }
}

// 23. type() with byte, verify unsigned flag is not set (byte is signed).
TEST(SimCh6b, TypeOpByteIsSigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  var type(a) result;\n"
      "  initial result = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->is_signed);
  EXPECT_EQ(var->value.width, 8u);
}

}  // namespace
