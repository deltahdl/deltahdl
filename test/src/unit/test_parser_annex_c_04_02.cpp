// Annex C.4.2: procedural assign and deassign statements.
//
// C.4.2 puts the procedural assign and deassign statements on the deprecation
// list and has "this current standard still requires tools to support" them,
// which §10.6.1 specifies and its tests observe. What C.4.2 states of its own
// is where the two forms of the assign statement are placed: "continuous
// assignments, placed outside any procedures" and "procedural continuous
// assignments, placed within a procedure". A.6.2 has deassign, and the force
// and release C.4.2 offers in place of assign and deassign, in the
// procedural_continuous_assignment alone, a statement_item, so one of the
// three written where a module item stands is a statement outside any
// procedure: the parser reports it under C.4.2 at its keyword and reads on to
// the ';' so that the items behind it are still read.

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The two forms C.4.2 names, each in its place: the continuous assign outside
// any procedure is a module item and the procedural assign within an initial
// procedure is a statement, and a source writing both is accepted.
TEST(ProceduralAssignDeassignPlacement, BothFormsInTheirPlacesAreAccepted) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b;\n"
      "  wire w;\n"
      "  assign w = a;\n"
      "  initial begin\n"
      "    assign b = a;\n"
      "    deassign b;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kContAssign));
}

// A deassign outside any procedure is the procedural statement misplaced, and
// the item behind it is still the module's.
TEST(ProceduralAssignDeassignPlacement, DeassignOutsideAProcedureIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  deassign a;\n"
      "  int x;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "'deassign' is a procedural continuous assignment "
                            "statement and is placed within a procedure",
                            3, "C.4.2"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kVarDecl));
}

// The force and release C.4.2 offers as the alternative are statements of the
// same production, and are reported the same way outside a procedure, each
// named by its own keyword.
TEST(ProceduralAssignDeassignPlacement, ForceOutsideAProcedureIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  force a = 1'b1;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "'force' is a procedural continuous assignment "
                            "statement and is placed within a procedure",
                            3, "C.4.2"));
}

TEST(ProceduralAssignDeassignPlacement, ReleaseOutsideAProcedureIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  release a;\n"
      "  int x;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "'release' is a procedural continuous assignment "
                            "statement and is placed within a procedure",
                            3, "C.4.2"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kVarDecl));
}

// The same misplacement in an interface body, which reads its items through
// the module item parser as well.
TEST(ProceduralAssignDeassignPlacement,
     DeassignOutsideAProcedureInAnInterface) {
  auto r = Parse(
      "interface i;\n"
      "  logic a;\n"
      "  deassign a;\n"
      "endinterface\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "'deassign' is a procedural continuous assignment "
                            "statement and is placed within a procedure",
                            3, "C.4.2"));
}

}  // namespace
