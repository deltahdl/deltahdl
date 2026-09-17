#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// 18.17.2: when the expression of an if-else production is true the
// production after it is generated and otherwise the one after else, so the
// clause's PP_OP, generating PUSH while depth is below 2 and POP otherwise
// with the code blocks moving depth, generates push, push, pop, push, pop
// from a depth of 0 and leaves depth at 1, as the design
// test/src/e2e/if_else_production.sv runs it.
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

// 18.17.2: the else is optional and the expression may be any expression
// evaluating to a Boolean value, so with no else a false expression
// generates nothing and a true expression of two operands generates its
// production, as the design test/src/e2e/if_else_production.sv runs it.
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
