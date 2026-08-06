#include "fixture_elaborator.h"

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
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  task automatic my_task;\n"
             "    logic local_var;\n"
             "    local_var = 1;\n"
             "  endtask\n"
             "  logic x;\n"
             "  assign x = m.my_task.local_var;\n"
             "endmodule\n"));
}

TEST(HierarchicalNameElaboration,
     AutomaticFuncVarInaccessibleByHierarchicalRef) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  function automatic int my_func(int a);\n"
             "    int tmp;\n"
             "    tmp = a + 1;\n"
             "    return tmp;\n"
             "  endfunction\n"
             "  logic [31:0] x;\n"
             "  assign x = m.my_func.tmp;\n"
             "endmodule\n"));
}

TEST(HierarchicalNameElaboration, HierarchicalReferenceIntoCheckerProhibited) {
  EXPECT_FALSE(
      ElabOk("checker my_chk;\n"
             "  logic captured;\n"
             "endchecker\n"
             "module m;\n"
             "  my_chk chk_inst();\n"
             "  logic x;\n"
             "  assign x = chk_inst.captured;\n"
             "endmodule\n"));
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

// §23.6: a named fork-join block defines a new hierarchy branch, just like a
// named begin-end block. This is the fork-join input form of the branch rule
// (the begin-end form is covered separately).
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
  EXPECT_FALSE(
      ElabOk("module child;\n"
             "  logic sig;\n"
             "endmodule\n"
             "module top;\n"
             "  child c [3:0] ();\n"
             "  logic x;\n"
             "  assign x = c[5].sig;\n"
             "endmodule\n"));
}

TEST(HierarchicalNameElaboration, InstanceArrayRefMissingSelectError) {
  EXPECT_FALSE(
      ElabOk("module child;\n"
             "  logic sig;\n"
             "endmodule\n"
             "module top;\n"
             "  child c [3:0] ();\n"
             "  logic x;\n"
             "  assign x = c.sig;\n"
             "endmodule\n"));
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

// §23.6: the instance select is a constant expression, not just a literal. A
// parameter is one of the constant forms of 11.2.1, so a parameter-valued
// select that lands inside the array bounds is accepted.
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

// §23.6: the constant expression shall evaluate to a legal index value. The
// out-of-range check applies to a parameter-valued select exactly as it does to
// a literal one -- the select is resolved against the module's parameter scope.
TEST(HierarchicalNameElaboration, InstanceSelectViaParameterOutOfRangeError) {
  EXPECT_FALSE(
      ElabOk("module child;\n"
             "  logic sig;\n"
             "endmodule\n"
             "module top;\n"
             "  parameter P = 5;\n"
             "  child c [3:0] ();\n"
             "  logic x;\n"
             "  assign x = c[P].sig;\n"
             "endmodule\n"));
}

// §23.6: the select is a constant expression, not just a single literal token.
// A folded arithmetic expression that lands outside the array bounds is
// likewise rejected -- exercising the expression-evaluation path rather than a
// bare literal read.
TEST(HierarchicalNameElaboration,
     InstanceSelectViaConstantExpressionOutOfRangeError) {
  EXPECT_FALSE(
      ElabOk("module child;\n"
             "  logic sig;\n"
             "endmodule\n"
             "module top;\n"
             "  child c [3:0] ();\n"
             "  logic x;\n"
             "  assign x = c[2 + 3].sig;\n"
             "endmodule\n"));
}

}  // namespace
