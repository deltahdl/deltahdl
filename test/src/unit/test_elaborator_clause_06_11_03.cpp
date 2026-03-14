#include <gtest/gtest.h>

#include "elaborator/type_eval.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(TypeEval, ImplicitlySignedTypes) {
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
      {DataTypeKind::kTime, false, "time"},
  };
  for (const auto& c : kCases) {
    EXPECT_EQ(IsImplicitlySigned(c.kind), c.expected) << c.label;
  }
}

TEST(TypeOperatorSim, TypeOpByteIsSigned) {
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

TEST(TypeOperatorSim, IntDefaultSignedVsUnsignedOverride) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int s;\n"
      "  int unsigned u;\n"
      "  initial begin s = 0; u = 0; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vs = f.ctx.FindVariable("s");
  auto* vu = f.ctx.FindVariable("u");
  ASSERT_NE(vs, nullptr);
  ASSERT_NE(vu, nullptr);
  EXPECT_TRUE(vs->is_signed) << "int defaults to signed";
  EXPECT_FALSE(vu->is_signed) << "int unsigned is unsigned";
}

}  // namespace
