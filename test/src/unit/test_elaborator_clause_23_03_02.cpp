// §23.3.2: Module instantiation syntax


#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaboration, PortBinding_UnknownModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic x;\n"
      "  nonexistent u0(.a(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  EXPECT_EQ(mod->children[0].resolved, nullptr);
}

}  // namespace
