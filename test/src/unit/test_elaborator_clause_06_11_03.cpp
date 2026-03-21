#include <gtest/gtest.h>

#include "elaborator/type_eval.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(SignedAndUnsigned, ImplicitlySignedTypes) {
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

TEST(SignedAndUnsigned, TypeOpByteIsSigned) {
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

TEST(SignedAndUnsigned, DefaultSignedTypesElaborateAsSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  shortint b;\n"
      "  int c;\n"
      "  longint d;\n"
      "  integer e;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 5u);
  EXPECT_TRUE(mod->variables[0].is_signed) << "byte";
  EXPECT_TRUE(mod->variables[1].is_signed) << "shortint";
  EXPECT_TRUE(mod->variables[2].is_signed) << "int";
  EXPECT_TRUE(mod->variables[3].is_signed) << "longint";
  EXPECT_TRUE(mod->variables[4].is_signed) << "integer";
}

TEST(SignedAndUnsigned, DefaultUnsignedTypesElaborateAsUnsigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  time a;\n"
      "  bit b;\n"
      "  logic c;\n"
      "  reg d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 4u);
  EXPECT_FALSE(mod->variables[0].is_signed) << "time";
  EXPECT_FALSE(mod->variables[1].is_signed) << "bit";
  EXPECT_FALSE(mod->variables[2].is_signed) << "logic";
  EXPECT_FALSE(mod->variables[3].is_signed) << "reg";
}

TEST(SignedAndUnsigned, SignedOverrideOnDefaultUnsigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  time signed a;\n"
      "  bit signed b;\n"
      "  logic signed c;\n"
      "  reg signed d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 4u);
  EXPECT_TRUE(mod->variables[0].is_signed) << "time signed";
  EXPECT_TRUE(mod->variables[1].is_signed) << "bit signed";
  EXPECT_TRUE(mod->variables[2].is_signed) << "logic signed";
  EXPECT_TRUE(mod->variables[3].is_signed) << "reg signed";
}

TEST(SignedAndUnsigned, UnsignedOverrideOnDefaultSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte unsigned a;\n"
      "  shortint unsigned b;\n"
      "  int unsigned c;\n"
      "  longint unsigned d;\n"
      "  integer unsigned e;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 5u);
  EXPECT_FALSE(mod->variables[0].is_signed) << "byte unsigned";
  EXPECT_FALSE(mod->variables[1].is_signed) << "shortint unsigned";
  EXPECT_FALSE(mod->variables[2].is_signed) << "int unsigned";
  EXPECT_FALSE(mod->variables[3].is_signed) << "longint unsigned";
  EXPECT_FALSE(mod->variables[4].is_signed) << "integer unsigned";
}

TEST(SignedAndUnsigned, IntDefaultSignedVsUnsignedOverride) {
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
