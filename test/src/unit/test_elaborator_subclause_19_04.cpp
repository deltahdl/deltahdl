#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(EmbeddedCovergroup, AssignInNewMethodOk) {
  EXPECT_TRUE(
      ElabOk("class C; logic clk;\n"
             "  int x;\n"
             "  covergroup cg @(posedge clk);\n"
             "    coverpoint x;\n"
             "  endgroup\n"
             "  function new();\n"
             "    cg = new;\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(EmbeddedCovergroup, ParameterizedInstantiatedInNewOk) {
  EXPECT_TRUE(
      ElabOk("class C1;\n"
             "  bit [7:0] x;\n"
             "  bit clk;\n"
             "  covergroup cv (int arg) @(posedge clk);\n"
             "    option.at_least = arg;\n"
             "    coverpoint x;\n"
             "  endgroup\n"
             "  function new();\n"
             "    cv = new(4);\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(EmbeddedCovergroup, AssignOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C; logic clk;\n"
      "  int x;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void build();\n"
      "    cg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            7, "19.4"));
}

TEST(EmbeddedCovergroup, NestedAssignOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C; logic clk;\n"
      "  int x;\n"
      "  bit en;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void reconfig();\n"
      "    if (en) cg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            8, "19.4"));
}

TEST(EmbeddedCovergroup, NoInstantiationOk) {
  EXPECT_TRUE(
      ElabOk("class C; logic clk;\n"
             "  int x;\n"
             "  covergroup cg @(posedge clk);\n"
             "    coverpoint x;\n"
             "  endgroup\n"
             "  function new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(EmbeddedCovergroup, AssignInSecondMethodAlongsideNewError) {
  ElabFixture f;
  ElabOk(
      "class C; logic clk;\n"
      "  int x;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function new();\n"
      "    cg = new;\n"
      "  endfunction\n"
      "  function void reconfig();\n"
      "    cg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            10, "19.4"));
}

TEST(EmbeddedCovergroup, AssignInLoopOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C; logic clk;\n"
      "  int x;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void setup();\n"
      "    for (int i = 0; i < 2; i = i + 1) cg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            7, "19.4"));
}

TEST(EmbeddedCovergroup, AssignInElseBranchOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C; logic clk;\n"
      "  int x;\n"
      "  bit en;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void reconfig();\n"
      "    if (en) x = 0; else cg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            8, "19.4"));
}

TEST(EmbeddedCovergroup, AssignInWhileLoopOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C; logic clk;\n"
      "  int x;\n"
      "  bit en;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void setup();\n"
      "    while (en) cg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            8, "19.4"));
}

TEST(EmbeddedCovergroup, AssignInCaseItemOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C; logic clk;\n"
      "  int x;\n"
      "  int mode;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void reconfig();\n"
      "    case (mode)\n"
      "      0: cg = new;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            9, "19.4"));
}

TEST(EmbeddedCovergroup, AssignViaThisHandleOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C; logic clk;\n"
      "  int x;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void reconfig();\n"
      "    this.cg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            7, "19.4"));
}

TEST(EmbeddedCovergroup, CoversLocalAndProtectedPropertiesOk) {
  EXPECT_TRUE(
      ElabOk("class C; logic clk;\n"
             "  local int x;\n"
             "  protected bit en;\n"
             "  covergroup cg @(posedge clk);\n"
             "    coverpoint x iff (en);\n"
             "  endgroup\n"
             "  function new();\n"
             "    cg = new;\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(EmbeddedCovergroup, AssignInAForkArmOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C; logic clk;\n"
      "  int x;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void reconfig();\n"
      "    fork\n"
      "      cg = new;\n"
      "    join_none\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            8, "19.4"));
}

TEST(EmbeddedCovergroup, AssignInAnAssertionPassStmtOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C; logic clk;\n"
      "  int x;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void reconfig();\n"
      "    assert (1) cg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            7, "19.4"));
}
TEST(EmbeddedCovergroup, AssignInAnAssertionFailStmtOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C; logic clk;\n"
      "  int x;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void reconfig();\n"
      "    assert (1) else cg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            7, "19.4"));
}

TEST(EmbeddedCovergroup, AssignInARandcaseItemOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C; logic clk;\n"
      "  int x;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void reconfig();\n"
      "    randcase\n"
      "      1 : cg = new;\n"
      "    endcase\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            8, "19.4"));
}

TEST(EmbeddedCovergroup, AssignInARandsequenceCodeBlockOutsideNewMethodError) {
  ElabFixture f;
  ElabOk(
      "class C; logic clk;\n"
      "  int x;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function void reconfig();\n"
      "    randsequence(main)\n"
      "      main : { cg = new; };\n"
      "    endsequence\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            8, "19.4"));
}

TEST(EmbeddedCovergroup, AssignOutsideNewInScopedClassError) {
  ElabFixture f;
  ElabOk(
      "package p;\n"
      "  class D;\n"
      "    bit w;\n"
      "    covergroup dg; coverpoint w; endgroup\n"
      "    function new(); endfunction\n"
      "    function void make(); dg = new; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "  class C;\n"
      "    bit v;\n"
      "    covergroup cg; coverpoint v; endgroup\n"
      "    function new(); cg = new; endfunction\n"
      "    function void make(); cg = new; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'dg' shall only be assigned "
                            "inside the new() method of its class",
                            6, "19.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "embedded covergroup 'cg' shall only be assigned "
                            "inside the new() method of its class",
                            14, "19.4"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(EmbeddedCovergroup, CoveringABaseLocalPropertyInASubclassIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class base;\n"
      "  local bit [1:0] m_z;\n"
      "  protected bit [1:0] m_p;\n"
      "  covergroup g;\n"
      "    coverpoint m_z;\n"
      "  endgroup\n"
      "  function new(); g = new; endfunction\n"
      "endclass\n"
      "class derived extends base;\n"
      "  covergroup extends g;\n"
      "    coverpoint m_z;\n"
      "  endgroup\n"
      "  covergroup h;\n"
      "    coverpoint m_z;\n"
      "    coverpoint m_p;\n"
      "  endgroup\n"
      "  function new(); super.new(); h = new; endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "covergroup 'g' of class 'derived' cannot cover "
                            "'m_z', a property local to its base class 'base'",
                            11, "19.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "covergroup 'h' of class 'derived' cannot cover "
                            "'m_z', a property local to its base class 'base'",
                            14, "19.4"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(EmbeddedCovergroup, NewWithoutActualForAFormalIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  bit [3:0] x;\n"
      "  covergroup cv (int arg);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  function new();\n"
      "    cv = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "new of covergroup 'cv' gives no actual to formal "
                            "'arg', which has no default",
                            7, "19.3"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
