// §6.20.1

#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

// §11.2.1: Elaborator rejects non-constant in parameter default.
TEST(ConstExprElab, NonConstantParamDefaultWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  // Non-constant param default: param not resolved.
  EXPECT_FALSE(design->top_modules[0]->params[0].is_resolved);
}

}  // namespace
