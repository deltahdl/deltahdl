#include <gtest/gtest.h>

#include <cstdint>
#include <string>

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

void ExpectModeError(const std::string& src, const std::string& msg,
                     uint32_t line) {
  ElabFixture f;
  EXPECT_FALSE(ElabOk(src, f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, line, "18.9"));
}

const char kModeBuiltin[] =
    "'constraint_mode' is a built-in method and cannot be overridden";
const char kModeVoidValue[] =
    "constraint_mode() with an argument is a void function and yields no "
    "value";
const char kModeOneArgument[] = "constraint_mode() takes at most one argument";

std::string MissingIn(const std::string& name) {
  return "constraint '" + name +
         "' does not exist in the hierarchy of class 'P'";
}

const char kClassP[] =
    "class P;\n"
    "  rand int x;\n"
    "  constraint c { x > 0; }\n"
    "endclass\n";

std::string PUse(const std::string& stmt) {
  return std::string(kClassP) +
         "module m;\n"
         "  P p = new;\n"
         "  int r;\n"
         "  initial begin\n"
         "    " +
         stmt +
         "\n"
         "  end\n"
         "endmodule\n";
}

TEST(ConstraintModeBuiltin, ATaskNamedConstraintModeRejected) {
  ExpectModeError(
      "class C;\n"
      "  rand int x;\n"
      "  task constraint_mode(bit on);\n"
      "  endtask\n"
      "endclass\n"
      "module m; endmodule\n",
      kModeBuiltin, 3);
}

TEST(ConstraintModeBuiltin, ADerivedClassMethodNamedConstraintModeRejected) {
  ExpectModeError(
      "class B;\n"
      "  rand int x;\n"
      "endclass\n"
      "class D extends B;\n"
      "  function void constraint_mode(bit on);\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      kModeBuiltin, 5);
}

TEST(ConstraintModeBuiltin, ADerivedClassMethodOfAnotherNameAccepted) {
  EXPECT_TRUE(
      ElabOk("class B;\n"
             "  rand int x;\n"
             "endclass\n"
             "class D extends B;\n"
             "  task toggle(bit on);\n"
             "  endtask\n"
             "endclass\n"
             "module m; endmodule\n"));
}

std::string PMethod(const std::string& stmt) {
  return "class P;\n"
         "  rand int x;\n"
         "  constraint c { x > 0; }\n"
         "  function void f();\n"
         "    " +
         stmt +
         "\n"
         "  endfunction\n"
         "endclass\n"
         "module m; endmodule\n";
}

TEST(ConstraintModeNamedBlock,
     DISABLED_AThisQualifiedMissingBlockInAMethodRejected) {
  ExpectModeError(PMethod("this.missing.constraint_mode(0);"),
                  MissingIn("missing"), 5);
}

TEST(ConstraintModeNamedBlock,
     DISABLED_AnUnqualifiedMissingBlockInAMethodRejected) {
  ExpectModeError(PMethod("missing.constraint_mode(0);"), MissingIn("missing"),
                  5);
}

TEST(ConstraintModeNamedBlock, AnExistingBlockInAMethodAccepted) {
  EXPECT_TRUE(ElabOk(
      PMethod("begin c.constraint_mode(0); this.c.constraint_mode(1); end")));
}

TEST(ConstraintModeNamedBlock,
     DISABLED_AMissingBlockInAPackageFunctionRejected) {
  ExpectModeError(
      "package q;\n"
      "  class P;\n"
      "    rand int x;\n"
      "    constraint c { x > 0; }\n"
      "  endclass\n"
      "  function void f(P p);\n"
      "    p.missing.constraint_mode(0);\n"
      "  endfunction\n"
      "endpackage\n"
      "module m; endmodule\n",
      MissingIn("missing"), 7);
}

TEST(ConstraintModeNamedBlock, AMissingBlockInAUnitFunctionRejected) {
  ExpectModeError(std::string(kClassP) +
                      "function void f(P p);\n"
                      "  p.missing.constraint_mode(0);\n"
                      "endfunction\n"
                      "module m; endmodule\n",
                  MissingIn("missing"), 6);
}

TEST(ConstraintModeNamedBlock, AMissingBlockInAProgramRejected) {
  ExpectModeError(std::string(kClassP) +
                      "program pr;\n"
                      "  initial begin\n"
                      "    automatic P p = new;\n"
                      "    p.missing.constraint_mode(0);\n"
                      "  end\n"
                      "endprogram\n",
                  MissingIn("missing"), 8);
}

TEST(ConstraintModeNamedBlock, AnExistingBlockInEachOfThosePlacesAccepted) {
  EXPECT_TRUE(ElabOk(std::string(kClassP) + "function void f(P p);\n"
                                            "  p.c.constraint_mode(0);\n"
                                            "endfunction\n"
                                            "program pr;\n"
                                            "  initial begin\n"
                                            "    automatic P p = new;\n"
                                            "    p.c.constraint_mode(0);\n"
                                            "  end\n"
                                            "endprogram\n"
                                            "module m; endmodule\n"));
}

TEST(ConstraintModeNamedBlock, ARandomVariableNamedAsABlockRejected) {
  ExpectModeError(PUse("p.x.constraint_mode(0);"), MissingIn("x"), 9);
}

TEST(ConstraintModeNamedBlock, ADerivedOnlyBlockThroughABaseHandleRejected) {
  ExpectModeError(
      "class B;\n"
      "  rand int x;\n"
      "endclass\n"
      "class D extends B;\n"
      "  constraint dc { x > 0; }\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    automatic D d = new;\n"
      "    automatic B b = d;\n"
      "    b.dc.constraint_mode(0);\n"
      "  end\n"
      "endmodule\n",
      "constraint 'dc' does not exist in the hierarchy of class 'B'", 11);
}

TEST(ConstraintModeForms, DISABLED_TwoArgumentsToABlockRejected) {
  ExpectModeError(PUse("p.c.constraint_mode(0, 1);"), kModeOneArgument, 9);
}

TEST(ConstraintModeForms, OneArgumentToABlockAccepted) {
  EXPECT_TRUE(ElabOk(PUse("p.c.constraint_mode(0);")));
}

TEST(ConstraintModeForms, DISABLED_ASetterUsedAsAValueRejected) {
  ExpectModeError(PUse("r = p.c.constraint_mode(0);"), kModeVoidValue, 9);
}

TEST(ConstraintModeForms, TheQueryUsedAsAValueAccepted) {
  EXPECT_TRUE(ElabOk(PUse("r = p.c.constraint_mode();")));
}

TEST(ConstraintModeForms, DISABLED_AnInnerObjectPropertyAsTheObjectAccepted) {
  EXPECT_TRUE(
      ElabOk("class In;\n"
             "  rand int y;\n"
             "  constraint ci { y > 0; }\n"
             "endclass\n"
             "class P;\n"
             "  In inner = new;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    automatic P p = new;\n"
             "    p.inner.constraint_mode(0);\n"
             "    p.inner.ci.constraint_mode(0);\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
