#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(RandModeBuiltin, OverrideRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function void rand_mode(bit on);\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'rand_mode' is a built-in method and cannot be overridden", 3, "18.8"));
}

TEST(RandModeBuiltin, OverrideViaNonvoidSignatureRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function int rand_mode();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'rand_mode' is a built-in method and cannot be overridden", 3, "18.8"));
}

TEST(RandModeBuiltin, NonOverridingClassAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function void toggle(bit on);\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(RandModeNamedVariable, MissingVariableRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.missing.rand_mode(0);\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random variable 'missing' does not exist in the "
                            "hierarchy of class 'Packet'",
                            8, "18.8"));
}

TEST(RandModeNamedVariable, NonRandVariableRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  int y;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.y.rand_mode(0);\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'y' is not declared rand or randc, so rand_mode() "
                            "cannot be applied to it",
                            9, "18.8"));
}

TEST(RandModeNamedVariable, CalledOnANonRandomMemberNames18_8) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  int y;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.y.rand_mode(0);\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'y' is not declared rand or randc", 9, "18.8"));
}

TEST(RandModeNamedVariable, RandVariableAccepted) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.x.rand_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(RandModeNamedVariable, RandcVariableAccepted) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  randc bit [3:0] x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.x.rand_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(RandModeNamedVariable, InheritedRandVariableAccepted) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  rand int y;\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "  initial begin\n"
             "    d = new;\n"
             "    d.x.rand_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(RandModeNamedVariable, UnnamedFormAccepted) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.rand_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(RandModeNamedVariable, UnnamedQueryWithoutArgumentRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.rand_mode();\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "rand_mode() called with no variable name requires "
                            "an on/off argument",
                            8, "18.8"));
}

TEST(RandModeNamedVariable, UnnamedRandModeQueryInAForkArmIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    fork\n"
             "      p.rand_mode();\n"
             "    join\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "rand_mode() called with no variable name requires "
                            "an on/off argument",
                            9, "18.8"));
}

TEST(RandModeNamedVariable,
     UnnamedRandModeQueryInAForInitializationIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    for (q = p.rand_mode(); q < 2; q = q + 1) ;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "rand_mode() called with no variable name requires "
                            "an on/off argument",
                            9, "18.8"));
}

TEST(RandModeNamedVariable, UnnamedRandModeQueryInAForStepIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    for (q = 0; q < 2; q = p.rand_mode()) ;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "rand_mode() called with no variable name requires "
                            "an on/off argument",
                            9, "18.8"));
}

TEST(RandModeNamedVariable,
     UnnamedRandModeQueryInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    assert (1) p.rand_mode();\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "rand_mode() called with no variable name requires "
                            "an on/off argument",
                            8, "18.8"));
}

TEST(RandModeNamedVariable,
     UnnamedRandModeQueryInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    assert (1) else p.rand_mode();\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "rand_mode() called with no variable name requires "
                            "an on/off argument",
                            8, "18.8"));
}

TEST(RandModeNamedVariable, UnnamedRandModeQueryInARandcaseItemIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    randcase\n"
             "      1 : p.rand_mode();\n"
             "    endcase\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "rand_mode() called with no variable name requires "
                            "an on/off argument",
                            9, "18.8"));
}

TEST(RandModeNamedVariable,
     UnnamedRandModeQueryInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    randsequence(main)\n"
             "      main : { p.rand_mode(); };\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "rand_mode() called with no variable name requires "
                            "an on/off argument",
                            9, "18.8"));
}

TEST(RandModeNamedVariable, MissingRandModeVariableInAForkArmIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    fork\n"
             "      p.missing.rand_mode(0);\n"
             "    join\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random variable 'missing' does not exist in the "
                            "hierarchy of class 'Packet'",
                            9, "18.8"));
}

TEST(RandModeNamedVariable,
     MissingRandModeVariableInAForInitializationIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    for (q = p.missing.rand_mode(); q < 2; q = q + 1) ;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random variable 'missing' does not exist in the "
                            "hierarchy of class 'Packet'",
                            9, "18.8"));
}

TEST(RandModeNamedVariable, MissingRandModeVariableInAForStepIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    for (q = 0; q < 2; q = p.missing.rand_mode()) ;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random variable 'missing' does not exist in the "
                            "hierarchy of class 'Packet'",
                            9, "18.8"));
}

TEST(RandModeNamedVariable,
     MissingRandModeVariableInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    assert (1) p.missing.rand_mode(0);\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random variable 'missing' does not exist in the "
                            "hierarchy of class 'Packet'",
                            8, "18.8"));
}

TEST(RandModeNamedVariable,
     MissingRandModeVariableInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    assert (1) else p.missing.rand_mode(0);\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random variable 'missing' does not exist in the "
                            "hierarchy of class 'Packet'",
                            8, "18.8"));
}

TEST(RandModeNamedVariable, MissingRandModeVariableInARandcaseItemIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    randcase\n"
             "      1 : p.missing.rand_mode(0);\n"
             "    endcase\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random variable 'missing' does not exist in the "
                            "hierarchy of class 'Packet'",
                            9, "18.8"));
}

TEST(RandModeNamedVariable,
     MissingRandModeVariableInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    randsequence(main)\n"
             "      main : { p.missing.rand_mode(0); };\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random variable 'missing' does not exist in the "
                            "hierarchy of class 'Packet'",
                            9, "18.8"));
}

TEST(RandModeNamedVariable, QueryOnAWholeUnpackedArrayRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand bit [3:0] arr[4];\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int r;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    r = p.arr.rand_mode();\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "rand_mode() with no argument queries one "
                            "variable, so the unpacked array 'arr' needs one "
                            "element selected by its index",
                            9, "18.8"));
}

TEST(RandModeNamedVariable, QueryOnAScalarOrAnElementAccepted) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  rand bit [3:0] x;\n"
             "  rand bit [3:0] arr[4];\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int r;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.arr.rand_mode(0);\n"
             "    r = p.x.rand_mode();\n"
             "    r = p.arr[1].rand_mode();\n"
             "  end\n"
             "endmodule\n"));
}

TEST(RandModeNamedVariable, AStructureMemberTheStructureLacksIsRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand struct { rand bit [3:0] a; } s;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.s.nosuch.rand_mode(0);\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the structure 's' has no member 'nosuch'", 8,
                            "18.8"));
}

TEST(RandModeNamedVariable, ANonRandStructureMemberIsRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand struct { rand bit [3:0] a; bit [3:0] b; } s;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.s.b.rand_mode(0);\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "member 'b' of the structure 's' is not declared "
                            "rand or randc, so rand_mode() cannot be applied "
                            "to it",
                            8, "18.8"));
}

TEST(RandModeNamedVariable, ARandStructureMemberIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  rand struct { rand bit [3:0] a; randc bit [1:0] c; } s;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int r;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.s.a.rand_mode(0);\n"
             "    r = p.s.c.rand_mode();\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
