#include "fixture_elaborator.h"

namespace {

TEST(LexicalConventionElaboration, AllFourAreasElaborate) {
  EXPECT_TRUE(
      ElabOk("(* optimize *) module t;\n"
             "  logic [7:0] data = 8'hAB;\n"
             "  real pi = 3.14;\n"
             "  initial $display(\"all areas: %d\", data);\n"
             "endmodule\n"));
}

}  // namespace
