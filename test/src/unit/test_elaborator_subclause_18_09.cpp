#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConstraintModeBuiltin, OverrideRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "  function void constraint_mode(bit on);\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'constraint_mode' is a built-in method and cannot be overridden", 4,
      "18.9"));
}

TEST(ConstraintModeBuiltin, OverrideViaNonvoidSignatureRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "  function int constraint_mode();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'constraint_mode' is a built-in method and cannot be overridden", 4,
      "18.9"));
}

TEST(ConstraintModeBuiltin, NonOverridingClassAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "  function void toggle(bit on);\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(ConstraintModeNamedBlock, MissingConstraintRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.missing.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "constraint 'missing' does not exist in the hierarchy "
                    "of class 'Packet'",
                    9, "18.9"));
}

TEST(ConstraintModeNamedBlock, ExistingConstraintAccepted) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.filter1.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ConstraintModeNamedBlock, InheritedConstraintAccepted) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint base_c { x > 0; }\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  rand int y;\n"
             "  constraint deriv_c { y > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "  initial begin\n"
             "    d = new;\n"
             "    d.base_c.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ConstraintModeNamedBlock, MissingConstraintAcrossHierarchyRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  rand int x;\n"
             "  constraint base_c { x > 0; }\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  rand int y;\n"
             "  constraint deriv_c { y > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "  initial begin\n"
             "    d = new;\n"
             "    d.nonexistent.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint 'nonexistent' does not exist in the "
                            "hierarchy of class 'Derived'",
                            13, "18.9"));
}

TEST(ConstraintModeNamedBlock, UnnamedFormNotTreatedAsMissingBlock) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ConstraintModeNamedBlock, UnnamedNoArgQueryRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    q = p.constraint_mode();\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint_mode() called with no constraint name "
                            "requires an on/off argument",
                            10, "18.9"));
}

TEST(ConstraintModeNamedBlock, NamedNoArgQueryAccepted) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    q = p.filter1.constraint_mode();\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ConstraintModeNamedBlock, UnnamedConstraintModeQueryInAForkArmIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    fork\n"
             "      p.constraint_mode();\n"
             "    join\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint_mode() called with no constraint name "
                            "requires an on/off argument",
                            10, "18.9"));
}

TEST(ConstraintModeNamedBlock,
     UnnamedConstraintModeQueryInAForInitializationIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    for (q = p.constraint_mode(); q < 2; q = q + 1) ;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint_mode() called with no constraint name "
                            "requires an on/off argument",
                            10, "18.9"));
}

TEST(ConstraintModeNamedBlock, UnnamedConstraintModeQueryInAForStepIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    for (q = 0; q < 2; q = p.constraint_mode()) ;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint_mode() called with no constraint name "
                            "requires an on/off argument",
                            10, "18.9"));
}

TEST(ConstraintModeNamedBlock,
     UnnamedConstraintModeQueryInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    assert (1) p.constraint_mode();\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint_mode() called with no constraint name "
                            "requires an on/off argument",
                            9, "18.9"));
}

TEST(ConstraintModeNamedBlock,
     UnnamedConstraintModeQueryInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    assert (1) else p.constraint_mode();\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint_mode() called with no constraint name "
                            "requires an on/off argument",
                            9, "18.9"));
}

TEST(ConstraintModeNamedBlock,
     UnnamedConstraintModeQueryInARandcaseItemIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    randcase\n"
             "      1 : p.constraint_mode();\n"
             "    endcase\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint_mode() called with no constraint name "
                            "requires an on/off argument",
                            10, "18.9"));
}

TEST(ConstraintModeNamedBlock,
     UnnamedConstraintModeQueryInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    randsequence(main)\n"
             "      main : { p.constraint_mode(); };\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constraint_mode() called with no constraint name "
                            "requires an on/off argument",
                            10, "18.9"));
}

TEST(ConstraintModeNamedBlock, MissingConstraintModeBlockInAForkArmIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    fork\n"
             "      p.missing.constraint_mode(0);\n"
             "    join\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "constraint 'missing' does not exist in the hierarchy "
                    "of class 'Packet'",
                    10, "18.9"));
}

TEST(ConstraintModeNamedBlock,
     MissingConstraintModeBlockInAForInitializationIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    for (q = p.missing.constraint_mode(); q < 2; q = q + 1) ;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "constraint 'missing' does not exist in the hierarchy "
                    "of class 'Packet'",
                    10, "18.9"));
}

TEST(ConstraintModeNamedBlock, MissingConstraintModeBlockInAForStepIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  int q;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    for (q = 0; q < 2; q = p.missing.constraint_mode()) ;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "constraint 'missing' does not exist in the hierarchy "
                    "of class 'Packet'",
                    10, "18.9"));
}

TEST(ConstraintModeNamedBlock,
     MissingConstraintModeBlockInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    assert (1) p.missing.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "constraint 'missing' does not exist in the hierarchy "
                    "of class 'Packet'",
                    9, "18.9"));
}

TEST(ConstraintModeNamedBlock,
     MissingConstraintModeBlockInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    assert (1) else p.missing.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "constraint 'missing' does not exist in the hierarchy "
                    "of class 'Packet'",
                    9, "18.9"));
}

TEST(ConstraintModeNamedBlock,
     MissingConstraintModeBlockInARandcaseItemIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    randcase\n"
             "      1 : p.missing.constraint_mode(0);\n"
             "    endcase\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "constraint 'missing' does not exist in the hierarchy "
                    "of class 'Packet'",
                    10, "18.9"));
}

TEST(ConstraintModeNamedBlock,
     MissingConstraintModeBlockInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  rand int x;\n"
             "  constraint filter1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    randsequence(main)\n"
             "      main : { p.missing.constraint_mode(0); };\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "constraint 'missing' does not exist in the hierarchy "
                    "of class 'Packet'",
                    10, "18.9"));
}

}  // namespace
