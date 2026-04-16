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

}  // namespace
