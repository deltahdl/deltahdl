// §6.19: Enumerations


#include "common/types.h"
#include "elaboration/sensitivity.h"
#include "elaboration/type_eval.h"
#include "lexer/token.h"

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- §6.19: Enum validation ---
TEST(Elaboration, EnumSizedLiteralMismatch_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  enum logic [2:0] {\n"
      "    Global = 4'h2,\n"
      "    Local = 4'h3\n"
      "  } myenum;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, EnumXZin2State_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  enum bit [1:0] {a=0, b=2'bxx, c=1} val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
