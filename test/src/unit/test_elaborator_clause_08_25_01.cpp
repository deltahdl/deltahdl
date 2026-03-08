#include "fixture_elaborator.h"

using namespace delta;

namespace {

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

// §8.25.1: Default specialization C#()::member — elaborates OK.
TEST(ElabA8251, DefaultSpecializationScopeOk) {
  EXPECT_TRUE(
      ElabOk("class C #(type T = int);\n"
             "  typedef T my_type;\n"
             "endclass\n"
             "module m;\n"
             "  C#()::my_type x;\n"
             "endmodule\n"));
}

// §8.25.1: Parameterized scope with value parameter — elaborates OK.
TEST(ElabA8251, ValueParamScopeOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
