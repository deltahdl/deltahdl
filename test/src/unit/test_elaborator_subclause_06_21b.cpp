#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §6.21's top_illegal example: in a static procedural block, a variable
// declared with an initializer states whether it is static or automatic, and
// `int loop3 = 0;` in a loop body states neither, so it is reported where it is
// declared and nothing else is.
TEST(LifetimeIntentElaboration, InitializedLoopLocalInAnInitialReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top_illegal;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 3; i++) begin\n"
      "      int loop3 = 0;\n"
      "      for (int j = 0; j < 3; j++) begin\n"
      "        loop3++;\n"
      "        $display(loop3);\n"
      "      end\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'loop3' declared with an initializer in "
                            "a loop of a static block, task or function must "
                            "be declared static or automatic",
                            4, "6.21"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

// §6.21's top_legal example: the same loop bodies with `automatic`, run on
// each iteration, and with `static`, run once, state the intent.
TEST(LifetimeIntentElaboration, LoopLocalsWithAStatedLifetimeAccepted) {
  EXPECT_TRUE(
      ElabOk("module top_legal;\n"
             "  initial begin\n"
             "    for (int i = 0; i < 3; i++) begin\n"
             "      automatic int loop3 = 0;\n"
             "      loop3++;\n"
             "    end\n"
             "    for (int i = 0; i < 3; i++) begin\n"
             "      static int loop2 = 0;\n"
             "      loop2++;\n"
             "    end\n"
             "  end\n"
             "endmodule\n"));
}

// A loop local without an initializer has no initialization whose timing is
// in question, so the rule does not reach it.
TEST(LifetimeIntentElaboration, UninitializedLoopLocalAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial begin\n"
             "    repeat (3) begin\n"
             "      int n;\n"
             "      n = 1;\n"
             "    end\n"
             "  end\n"
             "endmodule\n"));
}

// A while loop's body is a loop body as a for loop's is, and a task written
// with no lifetime in a module that writes none is static, so its loop local
// with an initializer is reported too.
TEST(LifetimeIntentElaboration, InitializedLocalInAStaticTaskLoopReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  task tk;\n"
      "    while (1) begin\n"
      "      int k = 2;\n"
      "      break;\n"
      "    end\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'k' declared with an initializer in a "
                            "loop of a static block, task or function must be "
                            "declared static or automatic",
                            4, "6.21"));
}

// An automatic task's variables are automatic by default (§6.21), and so are
// a `module automatic`'s blocks', so neither loop local needs a keyword.
TEST(LifetimeIntentElaboration,
     InitializedLoopLocalInAnAutomaticScopeAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  task automatic tk;\n"
             "    forever begin\n"
             "      int k = 2;\n"
             "      break;\n"
             "    end\n"
             "  endtask\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("module automatic m;\n"
             "  initial begin\n"
             "    do begin\n"
             "      int k = 2;\n"
             "    end while (0);\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
