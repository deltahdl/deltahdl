#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DisableForkElaboration, DisableForkAfterJoinAnyElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      #10 a = 1;\n"
      "      #20 b = 1;\n"
      "    join_any\n"
      "    disable fork;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DisableForkElaboration, DisableForkAfterJoinNoneElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    fork\n"
      "      #100 a = 1;\n"
      "    join_none\n"
      "    #50;\n"
      "    disable fork;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DisableForkElaboration, DisableForkStandaloneElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    disable fork;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DisableForkElaboration, DisableForkInTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task get_first;\n"
      "    fork\n"
      "      #10;\n"
      "      #20;\n"
      "    join_any\n"
      "    disable fork;\n"
      "  endtask\n"
      "  initial get_first;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
