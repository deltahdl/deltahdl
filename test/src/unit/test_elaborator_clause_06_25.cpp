// §6.25: Parameterized data types


#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- §6.25: Parameterized data types ---
TEST(Elaboration, ParameterizedType_Basic) {
  // §6.25: C#(logic)::my_type resolves to logic (width 1).
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

}  // namespace
