#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(Elaboration, ParameterizedType_Basic) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C #(type T = int);\n"
      "  typedef T my_type;\n"
      "endclass\n"
      "module top;\n"
      "  C#(logic)::my_type x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1);
  EXPECT_EQ(mod->variables[0].name, "x");
  EXPECT_EQ(mod->variables[0].width, 1);
}

TEST(Elaboration, ParameterizedType_ValueParam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "virtual class bus_def #(parameter WIDTH = 8);\n"
      "  typedef logic [WIDTH-1:0] data_t;\n"
      "endclass\n"
      "module top;\n"
      "  bus_def#(16)::data_t wide;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1);
  EXPECT_EQ(mod->variables[0].name, "wide");
  EXPECT_EQ(mod->variables[0].width, 16);
}

TEST(Elaboration, ParameterizedType_DefaultType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C #(type T = int);\n"
      "  typedef T my_type;\n"
      "endclass\n"
      "module top;\n"
      "  C::my_type x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1);
  EXPECT_EQ(mod->variables[0].name, "x");
  EXPECT_EQ(mod->variables[0].width, 32);
}

TEST(Elaboration, ParameterizedType_MultipleWidths) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "virtual class bus_def #(parameter WIDTH = 8);\n"
      "  typedef logic [WIDTH-1:0] data_t;\n"
      "endclass\n"
      "module top;\n"
      "  bus_def#(8)::data_t narrow;\n"
      "  bus_def#(32)::data_t wide;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 2);
  EXPECT_EQ(mod->variables[0].width, 8);
  EXPECT_EQ(mod->variables[1].width, 32);
}

TEST(Elaboration, ParameterizedType_Vector) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C #(type T = int);\n"
      "  typedef T my_type;\n"
      "endclass\n"
      "module top;\n"
      "  C#(logic [7:0])::my_type x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1);
  EXPECT_EQ(mod->variables[0].name, "x");
  EXPECT_EQ(mod->variables[0].width, 8);
}

TEST(Elaboration, DefaultSpecializationScopeOk) {
  EXPECT_TRUE(
      ElabOk("class C #(type T = int);\n"
             "  typedef T my_type;\n"
             "endclass\n"
             "module m;\n"
             "  C#()::my_type x;\n"
             "endmodule\n"));
}

TEST(Elaboration, ParameterizedType_TypeAndValueParams) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "virtual class C #(parameter type T = logic, parameter SIZE = 1);\n"
      "  typedef T my_type;\n"
      "endclass\n"
      "module top;\n"
      "  C#(logic [7:0], 3)::my_type x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1);
  EXPECT_EQ(mod->variables[0].name, "x");
  EXPECT_EQ(mod->variables[0].width, 8);
}

TEST(Elaboration, ParameterizedType_BitTypeParam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C #(type T = int);\n"
      "  typedef T my_type;\n"
      "endclass\n"
      "module top;\n"
      "  C#(bit [3:0])::my_type x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1);
  EXPECT_EQ(mod->variables[0].width, 4);
}

TEST(Elaboration, ParameterizedType_SignedTypeParam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C #(type T = int);\n"
      "  typedef T my_type;\n"
      "endclass\n"
      "module top;\n"
      "  C#(logic signed [7:0])::my_type x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1);
  EXPECT_EQ(mod->variables[0].width, 8);
  EXPECT_TRUE(mod->variables[0].is_signed);
}

TEST(Elaboration, ParameterizedType_DistinctSpecializationsInSameModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C #(type T = int);\n"
      "  typedef T my_type;\n"
      "endclass\n"
      "module top;\n"
      "  C#(logic [7:0])::my_type a;\n"
      "  C#(logic [15:0])::my_type b;\n"
      "  C#(bit)::my_type c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 3);
  EXPECT_EQ(mod->variables[0].width, 8);
  EXPECT_EQ(mod->variables[1].width, 16);
  EXPECT_EQ(mod->variables[2].width, 1);
}

}  // namespace
