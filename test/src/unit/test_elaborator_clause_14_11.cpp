#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(CycleDelayElab, WithDefaultClockingElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  default clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    ##5;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(CycleDelayElab, WithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(CycleDelayElab, ParenthesizedExprWithDefaultClocking) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  default clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    ##(3 + 2);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(CycleDelayElab, ZeroCycleDelayWithDefaultClocking) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  default clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    ##0;\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
