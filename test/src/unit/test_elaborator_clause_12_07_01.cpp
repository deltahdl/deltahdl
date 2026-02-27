// §12.7.1: The for-loop

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// =============================================================================
// A.6.8 Looping statements — Elaboration
// =============================================================================
// §12.7.1: for loop with typed init elaborates without error
TEST(ElabA608, ForLoopTypedInit) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) x = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.7.1: for loop without typed init elaborates without error
TEST(ElabA608, ForLoopUntypedInit) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    for (i = 0; i < 10; i = i + 1) x = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Nested loops elaborate without error
TEST(ElabA608, NestedLoops) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 4; i++) begin\n"
      "      for (int j = 0; j < 4; j++) begin\n"
      "        x = i[7:0] + j[7:0];\n"
      "      end\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
