#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(FunctionsInConstraints, InputArgumentFunctionAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a); return a; endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(FunctionsInConstraints, OutputArgumentFunctionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(output int a); a = 1; return a; endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'f' is called in a constraint, so each "
                            "of its arguments must be an input or a const ref",
                            5, "18.5.11"));
}

TEST(FunctionsInConstraints, InoutArgumentFunctionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(inout int a); return a; endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'f' is called in a constraint, so each "
                            "of its arguments must be an input or a const ref",
                            5, "18.5.11"));
}

TEST(FunctionsInConstraints, NonConstRefArgumentFunctionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(ref int a); return a; endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'f' is called in a constraint, so each "
                            "of its arguments must be an input or a const ref",
                            5, "18.5.11"));
}

TEST(FunctionsInConstraints, ConstRefArgumentFunctionAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(const ref int a); return a; endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(FunctionsInConstraints, RefArgumentFunctionNotInConstraintAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function int f(ref int a); return a; endfunction\n"
             "  constraint c1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(FunctionsInConstraints, ConstraintFunctionCallingRandModeRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a); this.rand_mode(0); return a; "
             "endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    5, "18.5.11"));
}

TEST(FunctionsInConstraints, ConstraintFunctionCallingConstraintModeRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a); this.constraint_mode(0); return a; "
             "endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    5, "18.5.11"));
}

TEST(FunctionsInConstraints, ConstraintFunctionWithBenignBodyAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int g(int a); return a + 1; endfunction\n"
             "  function int f(int a); return g(a); endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(FunctionsInConstraints, BaseClassFunctionWithOutputArgRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  function int f(output int a); a = 0; return a; endfunction\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'f' is called in a constraint, so each "
                            "of its arguments must be an input or a const ref",
                            7, "18.5.11"));
}

TEST(FunctionsInConstraints, LaterArgumentBadDirectionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a, output int b); b = 0; return a; "
             "endfunction\n"
             "  constraint c1 { x == f(y, x); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'f' is called in a constraint, so each "
                            "of its arguments must be an input or a const ref",
                            5, "18.5.11"));
}

TEST(FunctionsInConstraints, NoArgumentFunctionAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function int f(); return 7; endfunction\n"
             "  constraint c1 { x == f(); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(FunctionsInConstraints, ModeMethodCallNestedInControlFlowRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    if (a > 0) this.rand_mode(0);\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    8, "18.5.11"));
}

TEST(FunctionsInConstraints, NestedConstraintCallInnerFunctionChecked) {
  ElabFixture f;
  EXPECT_FALSE(ElabOk(
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  function int inner(output int a); a = 0; return a; endfunction\n"
      "  function int outer(int a); return a; endfunction\n"
      "  constraint c1 { x == outer(inner(y)); }\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'inner' is called in a constraint, so each of "
                    "its arguments must be an input or a const ref",
                    6, "18.5.11"));
}

TEST(FunctionsInConstraints, ModeMethodCallInAssertionPassStatementRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    assert (a > 0) this.rand_mode(0);\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    8, "18.5.11"));
}

TEST(FunctionsInConstraints, ModeMethodCallInAssertionFailStatementRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    assert (a > 0) else this.constraint_mode(0);\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    8, "18.5.11"));
}

TEST(FunctionsInConstraints, ModeMethodCallInRandsequenceCodeBlockRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    randsequence(main)\n"
             "      main : { this.rand_mode(0); };\n"
             "    endsequence\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    10, "18.5.11"));
}

TEST(FunctionsInConstraints, ModeMethodCallInRandsequenceWeightBlockRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    randsequence(main)\n"
             "      main : a := 5 { this.constraint_mode(0); };\n"
             "      a : { ; };\n"
             "    endsequence\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    11, "18.5.11"));
}

TEST(FunctionsInConstraints, ModeMethodCallInDelayControlRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    #(this.rand_mode(0)) ;\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    8, "18.5.11"));
}

TEST(FunctionsInConstraints, ModeMethodCallInCycleDelayRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    ##(this.constraint_mode(0)) ;\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    8, "18.5.11"));
}

TEST(FunctionsInConstraints, ModeMethodCallInAssertedExpressionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    assert (this.rand_mode(0));\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    8, "18.5.11"));
}

TEST(FunctionsInConstraints, ModeMethodCallInRepeatEventCountRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    int b;\n"
             "    b = repeat (this.rand_mode(0)) @(x) a;\n"
             "    return b;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    9, "18.5.11"));
}

TEST(FunctionsInConstraints, ModeMethodCallInEventControlSignalRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    @(this.rand_mode(0)) ;\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    8, "18.5.11"));
}

TEST(FunctionsInConstraints, ModeMethodCallInEventControlIffConditionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    @(x iff this.constraint_mode(0)) ;\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    8, "18.5.11"));
}

TEST(FunctionsInConstraints, ModeMethodCallInUnpackedDimensionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    int arr[this.rand_mode(0)];\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    8, "18.5.11"));
}

TEST(FunctionsInConstraints, ModeMethodCallInCaseItemExpressionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    case (a)\n"
             "      this.rand_mode(0) : ;\n"
             "    endcase\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    10, "18.5.11"));
}

TEST(FunctionsInConstraints, ModeMethodCallInRandcaseWeightRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    randcase\n"
             "      this.rand_mode(0) : ;\n"
             "    endcase\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    10, "18.5.11"));
}

TEST(FunctionsInConstraints, ModeMethodCallInRandsequenceWeightExprRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    randsequence(main)\n"
             "      main : a := (this.rand_mode(0));\n"
             "      a : { ; };\n"
             "    endsequence\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    11, "18.5.11"));
}

TEST(FunctionsInConstraints, ModeMethodCallInRandJoinExpressionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    randsequence(main)\n"
             "      main : rand join (this.constraint_mode(0)) a b;\n"
             "      a : { ; };\n"
             "      b : { ; };\n"
             "    endsequence\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    12, "18.5.11"));
}

TEST(FunctionsInConstraints, ModeMethodCallInRandsequenceIfConditionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    randsequence(main)\n"
             "      main : if (this.rand_mode(0)) a;\n"
             "      a : { ; };\n"
             "    endsequence\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    11, "18.5.11"));
}

TEST(FunctionsInConstraints, ModeMethodCallInRandsequenceRepeatCountRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    randsequence(main)\n"
             "      main : repeat (this.constraint_mode(0)) a;\n"
             "      a : { ; };\n"
             "    endsequence\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    11, "18.5.11"));
}

TEST(FunctionsInConstraints, ModeMethodCallInRandsequenceCaseExprRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    randsequence(main)\n"
             "      main : case (this.rand_mode(0)) 0 : a; endcase;\n"
             "      a : { ; };\n"
             "    endsequence\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    11, "18.5.11"));
}

TEST(FunctionsInConstraints, ModeMethodCallInRandsequenceCaseItemExprRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    randsequence(main)\n"
             "      main : case (a) this.constraint_mode(0) : b; endcase;\n"
             "      b : { ; };\n"
             "    endsequence\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    11, "18.5.11"));
}

TEST(FunctionsInConstraints, ModeMethodCallInRandsequenceProdArgRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    randsequence(main)\n"
             "      main : a(this.rand_mode(0));\n"
             "      a(int q) : { ; };\n"
             "    endsequence\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    11, "18.5.11"));
}

}  // namespace
