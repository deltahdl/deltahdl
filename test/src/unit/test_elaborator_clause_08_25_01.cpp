// §8.25.1: Class scope resolution operator for parameterized classes


#include "common/types.h"
#include "elaboration/sensitivity.h"
#include "elaboration/type_eval.h"
#include "lexer/token.h"

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaboration, ParameterizedType_Vector) {
  // §6.25: C#(logic [7:0])::my_type resolves to logic [7:0] (width 8).
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

}  // namespace
