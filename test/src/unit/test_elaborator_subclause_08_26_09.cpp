#include <gtest/gtest.h>

#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(InterfaceClassAllowedContent, NoConstraintsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassAllowedContent, ConstraintBlockError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "  constraint c { }\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not contain constraint blocks", 1,
                            "8.26.9"));
}

TEST(InterfaceClassAllowedContent, CovergroupError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "  covergroup cg; endgroup\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not contain covergroups", 1, "8.26.9"));
}

TEST(InterfaceClassAllowedContent, ConstraintBlockInExtendedInterfaceError) {
  ElabFixture f;
  ElabOk(
      "interface class Base;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "interface class Derived extends Base;\n"
      "  constraint c { }\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not contain constraint blocks", 4,
                            "8.26.9"));
}

TEST(InterfaceClassAllowedContent, CovergroupInExtendedInterfaceError) {
  ElabFixture f;
  ElabOk(
      "interface class Base;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "interface class Derived extends Base;\n"
      "  covergroup cg; endgroup\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not contain covergroups", 4, "8.26.9"));
}

TEST(InterfaceClassRandomize, RandomizeOnInterfaceHandleOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  rand int x;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    static C obj = new;\n"
             "    static IC iref = obj;\n"
             "    void'(iref.randomize());\n"
             "  end\n"
             "endmodule\n"));
}

TEST(InterfaceClassRandomize,
     RandomizeWithInlineConstraintOnInterfaceHandleOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  rand int x;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    static C obj = new;\n"
             "    static IC iref = obj;\n"
             "    void'(iref.randomize() with { });\n"
             "  end\n"
             "endmodule\n"));
}

TEST(InterfaceClassRandomize, RandModeOnInterfaceHandleError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  rand int x;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    static C obj = new;\n"
      "    static IC iref = obj;\n"
      "    iref.rand_mode(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not legal on interface class handle", 13,
                            "8.26.9"));
}

TEST(InterfaceClassRandomize, ConstraintModeOnInterfaceHandleError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  rand int x;\n"
      "  constraint c { x > 0; }\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    static C obj = new;\n"
      "    static IC iref = obj;\n"
      "    iref.constraint_mode(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not legal on interface class handle", 14,
                            "8.26.9"));
}

TEST(InterfaceClassPrePostRandomize, OverridePreRandomizeInImplementor) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  int count;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "  function void pre_randomize();\n"
             "    count = count + 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassPrePostRandomize, OverridePostRandomizeInImplementor) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  int count;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "  function void post_randomize();\n"
             "    count = count + 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassPrePostRandomize,
     BuiltinRandomizeMethodsAcrossInterfacesNoConflict) {
  EXPECT_TRUE(
      ElabOk("interface class A;\n"
             "  pure virtual function void fa();\n"
             "  pure virtual function void pre_randomize();\n"
             "  pure virtual function void post_randomize();\n"
             "endclass\n"
             "interface class B;\n"
             "  pure virtual function void fb();\n"
             "  pure virtual function void pre_randomize();\n"
             "  pure virtual function void post_randomize();\n"
             "endclass\n"
             "class C implements A, B;\n"
             "  virtual function void fa(); endfunction\n"
             "  virtual function void fb(); endfunction\n"
             "  virtual function void pre_randomize(); endfunction\n"
             "  virtual function void post_randomize(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassPrePostRandomize,
     PrePostRandomizeDeclaredInTwoExtendedInterfacesNoConflict) {
  EXPECT_TRUE(
      ElabOk("interface class A;\n"
             "  pure virtual function void fa();\n"
             "  pure virtual function void pre_randomize();\n"
             "  pure virtual function void post_randomize();\n"
             "endclass\n"
             "interface class B;\n"
             "  pure virtual function void fb();\n"
             "  pure virtual function void pre_randomize();\n"
             "  pure virtual function void post_randomize();\n"
             "endclass\n"
             "interface class D extends A, B;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassPrePostRandomize,
     OrdinaryMethodIncompatibleSignaturesAcrossExtendedInterfacesConflicts) {
  ElabFixture f;
  ElabOk(
      "interface class A;\n"
      "  pure virtual function void fa();\n"
      "  pure virtual function void bar();\n"
      "endclass\n"
      "interface class B;\n"
      "  pure virtual function void fb();\n"
      "  pure virtual function bit bar();\n"
      "endclass\n"
      "interface class D extends A, B;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "incompatible signatures in interface", 9,
                            "8.26.6.1"));
}

TEST(InterfaceClassPrePostRandomize,
     PrePostRandomizeNoConflictMultipleInterfaces) {
  EXPECT_TRUE(
      ElabOk("interface class A;\n"
             "  pure virtual function void fa();\n"
             "endclass\n"
             "interface class B;\n"
             "  pure virtual function void fb();\n"
             "endclass\n"
             "interface class C;\n"
             "  pure virtual function void fc();\n"
             "endclass\n"
             "class D implements A, B, C;\n"
             "  virtual function void fa(); endfunction\n"
             "  virtual function void fb(); endfunction\n"
             "  virtual function void fc(); endfunction\n"
             "  function void pre_randomize(); endfunction\n"
             "  function void post_randomize(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassRandomize, RandModeOnAnInterfaceHandleInAForkArmIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC iref;\n"
      "  initial begin\n"
      "    fork\n"
      "      iref.rand_mode(0);\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not legal on interface class handle", 8,
                            "8.26.9"));
}

TEST(InterfaceClassRandomize,
     RandModeOnAnInterfaceHandleInAForInitializationIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC iref;\n"
      "  int q;\n"
      "  initial begin\n"
      "    for (q = iref.rand_mode(); q < 2; q = q + 1) ;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not legal on interface class handle", 8,
                            "8.26.9"));
}

TEST(InterfaceClassRandomize, RandModeOnAnInterfaceHandleInAForStepIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC iref;\n"
      "  int q;\n"
      "  initial begin\n"
      "    for (q = 0; q < 2; q = iref.rand_mode()) ;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not legal on interface class handle", 8,
                            "8.26.9"));
}

TEST(InterfaceClassRandomize,
     RandModeOnAnInterfaceHandleInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC iref;\n"
      "  initial begin\n"
      "    assert (1) iref.rand_mode(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not legal on interface class handle", 7,
                            "8.26.9"));
}

TEST(InterfaceClassRandomize,
     RandModeOnAnInterfaceHandleInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC iref;\n"
      "  initial begin\n"
      "    assert (1) else iref.rand_mode(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not legal on interface class handle", 7,
                            "8.26.9"));
}

TEST(InterfaceClassRandomize,
     RandModeOnAnInterfaceHandleInARandcaseItemIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC iref;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1 : iref.rand_mode(0);\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not legal on interface class handle", 8,
                            "8.26.9"));
}

TEST(InterfaceClassRandomize,
     RandModeOnAnInterfaceHandleInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC iref;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { iref.rand_mode(0); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not legal on interface class handle", 8,
                            "8.26.9"));
}

TEST(InterfaceClassRandomizeElaboration,
     ModeMethodsThroughAnInterfaceHandleAreReported) {
  ElabFixture f;
  ElaborateSrc(
      "interface class IR; pure virtual function int get(); endclass\n"
      "class CR implements IR;\n"
      "  rand int v;\n"
      "  virtual function int get(); return v; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  IR ih;\n"
      "  initial begin\n"
      "    CR c;\n"
      "    c = new;\n"
      "    ih = c;\n"
      "    ih.rand_mode(0);\n"
      "    ih.constraint_mode(0);\n"
      "    void'(ih.randomize());\n"
      "    c.rand_mode(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {12}) {
    EXPECT_TRUE(ReportedError(
        diags, "'rand_mode' is not legal on interface class handle", kLine,
        "8.26.9"))
        << kLine;
  }
  for (const int kLine : {13}) {
    EXPECT_TRUE(ReportedError(
        diags, "'constraint_mode' is not legal on interface class handle",
        kLine, "8.26.9"))
        << kLine;
  }
  for (const int kLine : {14, 15}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

}  // namespace
