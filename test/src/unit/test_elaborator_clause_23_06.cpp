#include "fixture_elaborator.h"

namespace {

// --- R3: Module instance creates a new branch of the hierarchy ---

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

// --- R3: Arrayed module instance creates hierarchy branches ---

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

// --- R3: Nested hierarchy creates multiple levels of branches ---

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

// --- R3: Task definition creates a new hierarchy branch ---

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

// --- R3: Function definition creates a new hierarchy branch ---

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

// --- R6: Same identifier name in different hierarchy scopes is allowed ---

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

// --- R12: Objects in automatic tasks cannot be accessed by hierarchical
//     name references ---

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

// --- R12: Objects in automatic functions cannot be accessed by hierarchical
//     name references ---

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

// --- R15: Hierarchical references into checkers shall not be permitted ---

TEST(HierarchicalNameElaboration,
     HierarchicalReferenceIntoCheckerProhibited) {
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

// §23.6: "Inside any module, each module instance ..., generate block
// instance, task definition, function definition, and named begin-end or
// fork-join block shall define a new branch of the hierarchy."  A named
// begin-end block holding its own local declaration must elaborate
// cleanly as its own branch of the hierarchy tree.
TEST(HierarchicalNameElaboration, NamedBeginEndBlockCreatesBranch) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial begin : blk\n"
             "    logic [7:0] x;\n"
             "    x = 8'h11;\n"
             "  end\n"
             "endmodule\n"));
}

// §23.6: "Named blocks within named blocks and within tasks and functions
// shall create new branches."  Two levels of named-block nesting — an
// outer named begin-end with an inner named begin-end carrying its own
// declaration — must elaborate cleanly, since each block produces its own
// hierarchy branch.
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

// §23.6: "Similarly, named action blocks of assertions shall create new
// branches."  An immediate assertion with a labeled fail-action block must
// elaborate cleanly — the labeled block contributes a named scope in the
// module's hierarchy tree alongside other named-block branches.
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

// §23.6 R3: a generate block instance shall define a new branch of the
// hierarchy.  A named for-generate block must elaborate and its inner
// declarations must be reachable through the loop-index instance select
// (linking the §23.6 R3 rule with the §23.6 instance-select syntax).
TEST(HierarchicalNameElaboration, NamedGenerateBlockCreatesBranch) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  for (genvar i = 0; i < 2; i = i + 1) begin : g\n"
             "    logic v;\n"
             "  end\n"
             "endmodule\n"));
}

// §23.6: "Unnamed generate blocks are exceptions.  They create branches
// that are visible only from within the block and within any hierarchy
// instantiated by the block."  An unnamed if-generate must elaborate
// cleanly — the elaborator assigns it an automatic external name and
// items inside the block are usable within the block.
TEST(HierarchicalNameElaboration, UnnamedGenerateBlockCreatesBranch) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  if (1) begin\n"
             "    logic v;\n"
             "    initial v = 1'b1;\n"
             "  end\n"
             "endmodule\n"));
}

// §23.6: "The expression shall evaluate to one of the legal index values
// of the array."  An instance-select index outside the declared range of
// an arrayed module instance must be rejected by the elaborator.
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

// §23.6: "If the array name is not the last path element in the
// hierarchical name, the instance select expression is required."  A
// hierarchical reference that traverses an arrayed instance without a
// select must be rejected.
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

// §23.6: An in-range instance select on an arrayed instance must
// elaborate cleanly.  Complements the out-of-range error case.
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

}  // namespace
