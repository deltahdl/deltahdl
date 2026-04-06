#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(QualifiedIfElaboration, UniqueIfInAlwaysComb) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] x;\n"
      "  always_comb begin\n"
      "    unique if (sel == 2'd0) x = 8'd0;\n"
      "    else if (sel == 2'd1) x = 8'd1;\n"
      "    else x = 8'd2;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(QualifiedIfElaboration, Unique0IfElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  logic a, x;\n"
      "  always_comb begin\n"
      "    unique0 if (a) x = 1;\n"
      "    else x = 0;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(QualifiedIfElaboration, PriorityIfElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] x;\n"
      "  always_comb begin\n"
      "    priority if (sel == 2'd0) x = 8'd0;\n"
      "    else if (sel == 2'd1) x = 8'd1;\n"
      "    else x = 8'd2;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(QualifiedIfElaboration, QualifiedIfInInitialElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    unique if (a == 8'd0) x = 8'd10;\n"
      "    else x = 8'd20;\n"
      "  end\n"
      "endmodule\n"));
}

}  // namespace
