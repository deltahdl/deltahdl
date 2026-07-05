#include "helpers_scheduler.h"

using namespace delta;

// §A.2.3 end-to-end coverage. The declaration-list productions of §A.2.3 are
// syntactic comma-separated wrappers `element { , element }`; their observable
// outcome at runtime is that ONE list yields N independent entities, each
// carrying its own per-element initializer correctly associated across the
// commas. §A.2.4's simulator file exercises a single element in isolation and
// so cannot observe that association; these tests build a multi-element list
// from real source syntax and run it, checking every element's value
// independently.
//
// The list initializers are also driven from each constant-value form (a
// literal, a parameter, a localparam), which reach the value through distinct
// constant-evaluation code paths, and from a multi-element parameter list whose
// members are read back at runtime.

namespace {

// list_of_variable_decl_assignments: three variable_decl_assignments in one
// comma list, each with a distinct literal initializer. Reading each back shows
// the list built three separate variables and bound the right value to each.
TEST(DeclarationListSim, MultipleVarDeclInitializersApplyIndependently) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a = 8'd11, b = 8'd22, c = 8'd33;\n"
      "  logic [7:0] ra, rb, rc;\n"
      "  initial begin\n"
      "    ra = a; rb = b; rc = c;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"ra", 11u}, {"rb", 22u}, {"rc", 33u}});
}

// The same list where each element's initializer is a parameter reference. The
// parameter is declared with real §A.2.1.1 syntax; its constant value reaches
// each list element through the parameter constant-evaluation path (distinct
// from a plain literal), and both elements resolve independently.
TEST(DeclarationListSim, VarDeclListInitializedFromParameter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int P = 5;\n"
      "  logic [7:0] a = P, b = P + 8'd10;\n"
      "  logic [7:0] ra, rb;\n"
      "  initial begin\n"
      "    ra = a; rb = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"ra", 5u}, {"rb", 15u}});
}

// The same list initialized from a localparam. A localparam takes a separate
// declaration path from a parameter, so it exercises a third constant-value
// source feeding the per-element initializers of the list.
TEST(DeclarationListSim, VarDeclListInitializedFromLocalparam) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int Q = 7;\n"
      "  logic [7:0] a = Q, b = Q + 8'd1;\n"
      "  logic [7:0] ra, rb;\n"
      "  initial begin\n"
      "    ra = a; rb = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"ra", 7u}, {"rb", 8u}});
}

// list_of_param_assignments: three param_assignments in one comma list. All
// three parameters are usable at runtime, confirming the list produced three
// distinct constant bindings rather than collapsing them. 3 + 4 + 5 == 12.
TEST(DeclarationListSim, MultipleParamAssignmentsUsableAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter A = 3, B = 4, C = 5;\n"
      "  logic [7:0] r;\n"
      "  initial r = A + B + C;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 12u}});
}

}  // namespace
