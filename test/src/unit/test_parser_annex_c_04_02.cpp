#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

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
