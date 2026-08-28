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
  // §13.3.1 is the clause that states the rule for a task, and it is what the
  // report names; §23.6 governs the hierarchical name itself, which is
  // well-formed here.
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
  // §13.4.2 states the rule for a function, and names itself on the report.
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

// §23.6: the select is a constant expression, not just a single literal token.
// A folded arithmetic expression that lands outside the array bounds is
// likewise rejected -- exercising the expression-evaluation path rather than a
// bare literal read.
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

// §23.6 says a hierarchical name reference names its object "by concatenating
// the names of the modules, module instance names, generate blocks, tasks,
// functions ... that contain it", and puts no condition on where the reference
// is written. Every position a statement holds a statement in is therefore one
// the two rules below reach: the unresolved-member report, and the instance
// select §23.6 requires when an instance array name is not the last path
// element. CollectMemberAccessInStmt in
// src/elaborator/elaborator_scope_rules_hier.cpp, which gathers the accesses
// both checks read, had written out twelve of the thirteen child-statement
// links Stmt declares and now takes the list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. The missing link was
// Stmt::rs_productions; the cases below cover the two statement lists a
// randsequence production holds, once for each of the two rules.

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
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

// §18.17.1's Syntax 18-14 gives `rs_rule ::= rs_production_list [ :=
// rs_weight_specification [ rs_code_block ] ]`, putting a second code block
// after the weight. The parser keeps it in RsRule::weight_code, a list a walk
// reaches without reaching RsProd::code_stmts, so the case above does not
// answer for it.
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

// §23.6: "If the array name is not the last path element in the hierarchical
// name, the instance select expression is required." A reference written in a
// randsequence production's code block is subject to that as one written in a
// continuous assignment is.
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

// The same rule in the weight code block RsRule::weight_code holds, which the
// case above does not reach. The instance-array check reads the same collected
// accesses as the unresolved-member check, so each position is covered once for
// each rule.
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

}  // namespace
