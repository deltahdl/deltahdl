#include "fixture_elaborator.h"

namespace {

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

// §23.8: the upward reference is read in a procedural assignment rather than in
// a localparam initializer, because §6.20.2 rules that a value parameter "can
// only be set to an expression of literals, value parameters or local
// parameters, genvars, enumerated names, or a constant function of these" and
// states that "Hierarchical names are not allowed". The vehicle a §23.8 case
// uses has to be one the vehicle's own clause permits, and every other case in
// this file reads its upward name the same way.
TEST(UpwardNameReferenceElaboration, UpwardParameterReferenceResolves) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  integer k;\n"
             "  initial k = parent.P;\n"
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

TEST(UpwardNameReferenceElaboration, UpwardPortReferenceResolves) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  integer x;\n"
             "  initial x = parent.p;\n"
             "endmodule\n"
             "module parent(input logic p);\n"
             "  child c1();\n"
             "endmodule\n"));
}

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

TEST(UpwardNameReferenceElaboration, ScopeNameFoundInInstantiationParentScope) {
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

}  // namespace
