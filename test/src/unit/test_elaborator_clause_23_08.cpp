#include "fixture_elaborator.h"

namespace {

// Upward reference using enclosing module's name resolves to an item in it.

TEST(UpwardNameReferenceElaboration, UpwardVariableReferenceResolves) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  initial parent.v = 1;\n"
             "endmodule\n"
             "module parent;\n"
             "  integer v;\n"
             "  child c1();\n"
             "endmodule\n"));
}

TEST(UpwardNameReferenceElaboration, UpwardNetReferenceResolves) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  wire w;\n"
             "  assign w = parent.n;\n"
             "endmodule\n"
             "module parent;\n"
             "  wire n;\n"
             "  child c1();\n"
             "endmodule\n"));
}

TEST(UpwardNameReferenceElaboration, UpwardParameterReferenceResolves) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  localparam int K = parent.P;\n"
             "endmodule\n"
             "module parent;\n"
             "  parameter int P = 8;\n"
             "  child c1();\n"
             "endmodule\n"));
}

TEST(UpwardNameReferenceElaboration, UpwardTaskReferenceResolves) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  initial parent.t();\n"
             "endmodule\n"
             "module parent;\n"
             "  task t;\n"
             "  endtask\n"
             "  child c1();\n"
             "endmodule\n"));
}

TEST(UpwardNameReferenceElaboration, UpwardFunctionReferenceResolves) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  integer x;\n"
             "  initial x = parent.f(1);\n"
             "endmodule\n"
             "module parent;\n"
             "  function int f(int y);\n"
             "    return y + 1;\n"
             "  endfunction\n"
             "  child c1();\n"
             "endmodule\n"));
}

TEST(UpwardNameReferenceElaboration, UpwardNamedBlockReferenceResolves) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  integer r;\n"
             "  initial r = parent.blk.v;\n"
             "endmodule\n"
             "module parent;\n"
             "  initial begin : blk\n"
             "    integer v;\n"
             "    v = 7;\n"
             "  end\n"
             "  child c1();\n"
             "endmodule\n"));
}

// LRM canonical example: a.a_b1 / d.d_b1 with module c referencing b.i upward.

TEST(UpwardNameReferenceElaboration, CanonicalFourModuleExampleElaborates) {
  EXPECT_TRUE(
      ElabOk("module c;\n"
             "  integer i;\n"
             "  initial begin\n"
             "    i = 1;\n"
             "    b.i = 1;\n"
             "  end\n"
             "endmodule\n"
             "module b;\n"
             "  integer i;\n"
             "  c b_c1();\n"
             "  c b_c2();\n"
             "endmodule\n"
             "module a;\n"
             "  integer i;\n"
             "  b a_b1();\n"
             "endmodule\n"));
}

// scope_name.item_name step (a): scope_name found in current scope walk.

TEST(UpwardNameReferenceElaboration,
     ScopeNameFoundInCurrentScopeResolvesDownward) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  integer r;\n"
             "  initial begin : blk\n"
             "    integer v;\n"
             "    v = 5;\n"
             "    r = blk.v;\n"
             "  end\n"
             "endmodule\n"));
}

// scope_name.item_name step (b)/(c): search instantiation's parent scope upward.

TEST(UpwardNameReferenceElaboration,
     ScopeNameFoundInInstantiationParentScope) {
  EXPECT_TRUE(
      ElabOk("module leaf;\n"
             "  integer r;\n"
             "  initial r = sib.v;\n"
             "endmodule\n"
             "module parent;\n"
             "  integer v;\n"
             "  leaf sib();\n"
             "  leaf ref_src();\n"
             "endmodule\n"));
}

// Task/function/named-block/generate-block names search enclosing modules,
// not instances.

TEST(UpwardNameReferenceElaboration,
     TaskLookupSearchesEnclosingModulesNotInstances) {
  EXPECT_TRUE(
      ElabOk("module leaf;\n"
             "  initial t();\n"
             "endmodule\n"
             "module parent;\n"
             "  task t;\n"
             "  endtask\n"
             "  leaf l1();\n"
             "endmodule\n"));
}

TEST(UpwardNameReferenceElaboration,
     FunctionLookupSearchesEnclosingModulesNotInstances) {
  EXPECT_TRUE(
      ElabOk("module leaf;\n"
             "  integer x;\n"
             "  initial x = f(1);\n"
             "endmodule\n"
             "module parent;\n"
             "  function int f(int y);\n"
             "    return y + 1;\n"
             "  endfunction\n"
             "  leaf l1();\n"
             "endmodule\n"));
}

}  // namespace
