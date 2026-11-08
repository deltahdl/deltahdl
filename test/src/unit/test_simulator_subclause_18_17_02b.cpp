#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(IfElseProductionRun, TheClausesPpOpPushesToTwoThenAlternates) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int depth = 0;\n"
      "  task do_push();\n"
      "    $write(\"push \");\n"
      "  endtask\n"
      "  task do_pop();\n"
      "    $write(\"pop \");\n"
      "  endtask\n"
      "  initial begin\n"
      "    randsequence( main )\n"
      "      main  : PP_OP PP_OP PP_OP PP_OP PP_OP ;\n"
      "      PP_OP : if ( depth < 2 ) PUSH else POP ;\n"
      "      PUSH  : { ++depth; do_push(); } ;\n"
      "      POP   : { --depth; do_pop(); } ;\n"
      "    endsequence\n"
      "    $display(\"depth %0d\", depth);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "push push pop push pop depth 1\n");
}

TEST(IfElseProductionRun, WithoutElseAFalseExpressionGeneratesNothing) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int depth = 1, nothing = 1, generated = 0;\n"
      "  initial begin\n"
      "    randsequence( main )\n"
      "      main : if ( depth > 5 ) MARK ;\n"
      "      MARK : { nothing = 0; } ;\n"
      "    endsequence\n"
      "    randsequence( main )\n"
      "      main : if ( depth == 1 && nothing ) MARK ;\n"
      "      MARK : { generated = 1; } ;\n"
      "    endsequence\n"
      "    $display(\"%0d %0d\", nothing, generated);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1\n");
}

}  // namespace
