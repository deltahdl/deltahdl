// §6.19.3: Type checking


#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- §6.19.3: Enum strict type checking ---
TEST(Elaboration, EnumStrictTypeCheck_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
