#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(HierarchicalNameElaboration, ModuleInstanceCreatesHierarchyBranch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  logic sig;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  EXPECT_EQ(mod->children[0].inst_name, "c1");
  EXPECT_NE(mod->children[0].resolved, nullptr);
}

TEST(HierarchicalNameElaboration, ArrayedInstanceCreatesHierarchyBranch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  logic sig;\n"
      "endmodule\n"
      "module top;\n"
      "  child c [3:0] ();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->children.empty());
}

TEST(HierarchicalNameElaboration, MultiLevelHierarchyBranches) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf;\n"
      "  logic data;\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf l1();\n"
      "endmodule\n"
      "module top;\n"
      "  mid m1();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  EXPECT_EQ(mod->children[0].inst_name, "m1");
  auto* mid = mod->children[0].resolved;
  ASSERT_NE(mid, nullptr);
  ASSERT_EQ(mid->children.size(), 1u);
  EXPECT_EQ(mid->children[0].inst_name, "l1");
}

TEST(HierarchicalNameElaboration, TaskCreatesHierarchyBranch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task my_task;\n"
      "    logic local_var;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(HierarchicalNameElaboration, FunctionCreatesHierarchyBranch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int my_func(int x);\n"
      "    return x + 1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(HierarchicalNameElaboration, SameNameInDifferentScopesAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  logic data;\n"
      "endmodule\n"
      "module top;\n"
      "  logic data;\n"
      "  child c1();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(HierarchicalNameElaboration,
     AutomaticTaskVarInaccessibleByHierarchicalRef) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  task automatic my_task;\n"
      "    logic local_var;\n"
      "    local_var = 1;\n"
      "  endtask\n"
      "  logic x;\n"
      "  assign x = m.my_task.local_var;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic task is not permitted", 7,
      "13.3.1"));
}

TEST(HierarchicalNameElaboration,
     AutomaticFuncVarInaccessibleByHierarchicalRef) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  function automatic int my_func(int a);\n"
      "    int tmp;\n"
      "    tmp = a + 1;\n"
      "    return tmp;\n"
      "  endfunction\n"
      "  logic [31:0] x;\n"
      "  assign x = m.my_func.tmp;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to object in automatic "
                            "function is not permitted",
                            8, "13.4.2"));
}

TEST(HierarchicalNameElaboration, HierarchicalReferenceIntoCheckerProhibited) {
  ElabFixture f;
  ElabOk(
      "checker my_chk;\n"
      "  logic captured;\n"
      "endchecker\n"
      "module m;\n"
      "  my_chk chk_inst();\n"
      "  logic x;\n"
      "  assign x = chk_inst.captured;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference into a checker is not "
                            "permitted",
                            7, "23.6"));
}

TEST(HierarchicalNameElaboration, NamedBeginEndBlockCreatesBranch) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial begin : blk\n"
             "    logic [7:0] x;\n"
             "    x = 8'h11;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(HierarchicalNameElaboration, NamedForkJoinBlockCreatesBranch) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial fork : blk\n"
             "    logic [7:0] x;\n"
             "  join\n"
             "endmodule\n"));
}

TEST(HierarchicalNameElaboration, NestedNamedBlocksCreateNestedBranches) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial begin : outer\n"
             "    begin : inner\n"
             "      logic [7:0] x;\n"
             "      x = 8'h22;\n"
             "    end\n"
             "  end\n"
             "endmodule\n"));
}

TEST(HierarchicalNameElaboration, NamedAssertionActionBlockCreatesBranch) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a;\n"
             "  initial begin\n"
             "    assert (a)\n"
             "      else begin : fail_blk\n"
             "        $display(\"a low\");\n"
             "      end\n"
             "  end\n"
             "endmodule\n"));
}

TEST(HierarchicalNameElaboration, NamedGenerateBlockCreatesBranch) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  for (genvar i = 0; i < 2; i = i + 1) begin : g\n"
             "    logic v;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(HierarchicalNameElaboration, UnnamedGenerateBlockCreatesBranch) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  if (1) begin\n"
             "    logic v;\n"
             "    initial v = 1'b1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(HierarchicalNameElaboration, InstanceSelectOutOfRangeError) {
  ElabFixture f;
  ElabOk(
      "module child;\n"
      "  logic sig;\n"
      "endmodule\n"
      "module top;\n"
      "  child c [3:0] ();\n"
      "  logic x;\n"
      "  assign x = c[5].sig;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "instance select [5] is out of range for instance array 'c' [3:0]", 7,
      "23.6"));
}

TEST(HierarchicalNameElaboration, InstanceArrayRefMissingSelectError) {
  ElabFixture f;
  ElabOk(
      "module child;\n"
      "  logic sig;\n"
      "endmodule\n"
      "module top;\n"
      "  child c [3:0] ();\n"
      "  logic x;\n"
      "  assign x = c.sig;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to instance array 'c' "
                            "requires an instance select",
                            7, "23.6"));
}

TEST(HierarchicalNameElaboration, InstanceSelectInRangeElaboratesOk) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  logic sig;\n"
             "endmodule\n"
             "module top;\n"
             "  child c [3:0] ();\n"
             "  logic x;\n"
             "  assign x = c[2].sig;\n"
             "endmodule\n"));
}

TEST(HierarchicalNameElaboration, InstanceSelectViaParameterInRangeOk) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  logic sig;\n"
             "endmodule\n"
             "module top;\n"
             "  parameter P = 2;\n"
             "  child c [3:0] ();\n"
             "  logic x;\n"
             "  assign x = c[P].sig;\n"
             "endmodule\n"));
}

TEST(HierarchicalNameElaboration, InstanceSelectViaParameterOutOfRangeError) {
  ElabFixture f;
  ElabOk(
      "module child;\n"
      "  logic sig;\n"
      "endmodule\n"
      "module top;\n"
      "  parameter P = 5;\n"
      "  child c [3:0] ();\n"
      "  logic x;\n"
      "  assign x = c[P].sig;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "instance select [5] is out of range for instance array 'c' [3:0]", 8,
      "23.6"));
}

TEST(HierarchicalNameElaboration,
     InstanceSelectViaConstantExpressionOutOfRangeError) {
  ElabFixture f;
  ElabOk(
      "module child;\n"
      "  logic sig;\n"
      "endmodule\n"
      "module top;\n"
      "  child c [3:0] ();\n"
      "  logic x;\n"
      "  assign x = c[2 + 3].sig;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "instance select [5] is out of range for instance array 'c' [3:0]", 7,
      "23.6"));
}

TEST(HierarchicalNameElaboration,
     UnresolvedMemberInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module sub; endmodule\n"
      "module top;\n"
      "  int y;\n"
      "  sub u();\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { y = u.nonexistent; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference 'u.nonexistent' is "
                            "unresolved: 'nonexistent' is not declared in "
                            "module 'sub'",
                            7, "23.6"));
}

TEST(HierarchicalNameElaboration,
     UnresolvedMemberInARandsequenceWeightCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module sub; endmodule\n"
      "module top;\n"
      "  int y;\n"
      "  sub u();\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { y = u.nonexistent; };\n"
      "      alt : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference 'u.nonexistent' is "
                            "unresolved: 'nonexistent' is not declared in "
                            "module 'sub'",
                            7, "23.6"));
}

TEST(HierarchicalNameElaboration,
     InstanceArrayRefMissingSelectInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module child;\n"
      "  logic sig;\n"
      "endmodule\n"
      "module top;\n"
      "  child c [3:0] ();\n"
      "  logic x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = c.sig; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to instance array 'c' "
                            "requires an instance select",
                            9, "23.6"));
}

TEST(HierarchicalNameElaboration,
     InstanceArrayRefMissingSelectInARandsequenceWeightCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module child;\n"
      "  logic sig;\n"
      "endmodule\n"
      "module top;\n"
      "  child c [3:0] ();\n"
      "  logic x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { x = c.sig; };\n"
      "      alt : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to instance array 'c' "
                            "requires an instance select",
                            9, "23.6"));
}

TEST(HierarchicalNameElaboration,
     CheckerRefInAnAssertionPassStatementIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "checker cap_chk;\n"
      "  logic captured;\n"
      "endchecker\n"
      "module m;\n"
      "  cap_chk cap_inst();\n"
      "  logic x;\n"
      "  logic ok;\n"
      "  initial assert (ok) x = cap_inst.captured;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference into a checker is not "
                            "permitted",
                            8, "23.6"));
}

TEST(HierarchicalNameElaboration,
     CheckerRefInAnAssertionFailStatementIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "checker flag_chk;\n"
      "  logic flagged;\n"
      "endchecker\n"
      "module m;\n"
      "  flag_chk flag_inst();\n"
      "  logic y;\n"
      "  logic armed;\n"
      "  initial assert (armed) else y = flag_inst.flagged;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference into a checker is not "
                            "permitted",
                            8, "23.6"));
}

TEST(HierarchicalNameElaboration, CheckerRefInARandcaseItemIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "checker pick_chk;\n"
      "  logic chosen;\n"
      "endchecker\n"
      "module m;\n"
      "  pick_chk pick_inst();\n"
      "  logic z;\n"
      "  initial randcase 1: z = pick_inst.chosen; endcase\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference into a checker is not "
                            "permitted",
                            7, "23.6"));
}

TEST(HierarchicalNameElaboration,
     CheckerRefInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "checker samp_chk;\n"
      "  logic sampled;\n"
      "endchecker\n"
      "module m;\n"
      "  samp_chk samp_inst();\n"
      "  logic w;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { w = samp_inst.sampled; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference into a checker is not "
                            "permitted",
                            9, "23.6"));
}

TEST(HierarchicalNameElaboration,
     ABlockLocalOfACheckerInstanceNameIsNotAHierRefIntoTheChecker) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker my_chk;\n"
      "  logic captured;\n"
      "endchecker\n"
      "module m;\n"
      "  my_chk chk_inst();\n"
      "  typedef struct { int a; } s_t;\n"
      "  int q;\n"
      "  initial begin\n"
      "    s_t chk_inst;\n"
      "    q = chk_inst.a;\n"
      "  end\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(HierarchicalNameElaboration,
     ACheckerRefInABlockWithNoShadowingDeclarationIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "checker my_chk;\n"
      "  logic captured;\n"
      "endchecker\n"
      "module m;\n"
      "  my_chk chk_inst();\n"
      "  int q;\n"
      "  initial begin\n"
      "    q = chk_inst.captured;\n"
      "  end\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference into a checker is not "
                            "permitted",
                            8, "23.6"));
}

TEST(HierarchicalNameElaboration, AssertionScopesTakeModuleLevelNames) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic clk = 0, a = 0, b = 0;\n"
      "  assert property (@(posedge clk) a |-> b) else begin : B3\n"
      "    static bit d;\n"
      "  end\n"
      "  initial begin : B3\n"
      "  end\n"
      "  A1: assert property (@(posedge clk) a);\n"
      "  logic A1;\n"
      "  A2: assert property (@(posedge clk) a) else begin : B4\n"
      "  end\n"
      "  initial begin : B4\n"
      "  end\n"
      "  cover property (@(posedge clk) a) begin : B5\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'B3'", 3, "23.9"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'A1'", 8, "23.9"));
  for (uint32_t line : {10u, 12u, 14u}) {
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), "redeclaration", line, "23.9"))
        << line;
  }
}

TEST(HierarchicalNameElaboration, InstanceSelectNotConstantIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf; logic v; endmodule\n"
      "module top;\n"
      "  parameter int P = 1;\n"
      "  leaf u [0:3] ();\n"
      "  leaf s ();\n"
      "  for (genvar g = 0; g < 4; g++) begin : blk\n"
      "    logic w;\n"
      "  end\n"
      "  int i;\n"
      "  logic x;\n"
      "  initial begin\n"
      "    x = u[i].v;\n"
      "    x = blk[i].w;\n"
      "    x = u[P + 1].v;\n"
      "    x = blk[3].w;\n"
      "    x = s.v;\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instance select of 'u' is not a constant "
                            "expression",
                            12, "23.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instance select of 'blk' is not a constant "
                            "expression",
                            13, "23.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(HierarchicalNameElaboration, InstanceSelectRangeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf; logic v; endmodule\n"
      "module top;\n"
      "  leaf u [0:3] ();\n"
      "  for (genvar g = 0; g < 4; g++) begin : blk\n"
      "    logic w;\n"
      "  end\n"
      "  logic x;\n"
      "  initial begin\n"
      "    x = u[5:4].v;\n"
      "    x = u[0+:2].v;\n"
      "    x = blk[3-:2].w;\n"
      "    x = u[1].v;\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  for (uint32_t line : {9u, 10u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "instance select of 'u' is a range; an instance "
                              "select names one instance",
                              line, "23.6"))
        << line;
  }
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instance select of 'blk' is a range; an instance "
                            "select names one instance",
                            11, "23.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(HierarchicalNameElaboration, InstanceSelectNamesBlockLocalParam) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf; logic v; endmodule\n"
      "module top;\n"
      "  leaf u [0:3] ();\n"
      "  for (genvar g = 0; g < 4; g++) begin : blk\n"
      "    logic w;\n"
      "  end\n"
      "  int K;\n"
      "  logic x;\n"
      "  initial begin\n"
      "    begin\n"
      "      localparam int K = 1;\n"
      "      localparam int L = 7;\n"
      "      x = u[K].v;\n"
      "      x = blk[K].w;\n"
      "      x = u[L].v;\n"
      "    end\n"
      "    x = u[K].v;\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "instance select [7] is out of range for instance array 'u' [3:0]", 15,
      "23.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instance select of 'u' is not a constant "
                            "expression",
                            17, "23.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

}  // namespace
