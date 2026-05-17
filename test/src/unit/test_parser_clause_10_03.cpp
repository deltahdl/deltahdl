#include "fixture_parser.h"

using namespace delta;

namespace {

static ModuleItem* FindFirst(ParseResult& r, ModuleItemKind kind) {
  for (auto* it : r.cu->modules[0]->items) {
    if (it->kind == kind) return it;
  }
  return nullptr;
}

static int CountKind(ParseResult& r, ModuleItemKind kind) {
  int count = 0;
  for (auto* it : r.cu->modules[0]->items) {
    if (it->kind == kind) ++count;
  }
  return count;
}

// §10.3 Syntax 10-1: continuous_assign ::= assign [drive_strength] [delay3]
//   list_of_net_assignments ;
//   | assign [delay_control] list_of_variable_assignments ;
TEST(ContinuousAssignSyntax, NetForm) {
  auto r = Parse(
      "module m;\n"
      "  wire y;\n"
      "  assign y = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_NE(FindFirst(r, ModuleItemKind::kContAssign), nullptr);
}

TEST(ContinuousAssignSyntax, NetFormWithDriveStrength) {
  auto r = Parse(
      "module m;\n"
      "  wire y;\n"
      "  assign (strong1, pull0) y = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FindFirst(r, ModuleItemKind::kContAssign);
  ASSERT_NE(ca, nullptr);
  EXPECT_NE(ca->drive_strength1, 0);
  EXPECT_NE(ca->drive_strength0, 0);
}

TEST(ContinuousAssignSyntax, NetFormWithDelay3) {
  auto r = Parse(
      "module m;\n"
      "  wire y;\n"
      "  assign #(1, 2, 3) y = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FindFirst(r, ModuleItemKind::kContAssign);
  ASSERT_NE(ca, nullptr);
  EXPECT_NE(ca->assign_delay, nullptr);
  EXPECT_NE(ca->assign_delay_fall, nullptr);
  EXPECT_NE(ca->assign_delay_decay, nullptr);
}

TEST(ContinuousAssignSyntax, VariableFormWithDelayControl) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] v;\n"
      "  assign #5 v = 8'd1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FindFirst(r, ModuleItemKind::kContAssign);
  ASSERT_NE(ca, nullptr);
  EXPECT_NE(ca->assign_delay, nullptr);
}

// §10.3 Syntax 10-1 net form: both optional fields present together —
// `assign [drive_strength] [delay3] list_of_net_assignments ;`
TEST(ContinuousAssignSyntax, NetFormWithDriveStrengthAndDelay3) {
  auto r = Parse(
      "module m;\n"
      "  wire y;\n"
      "  assign (strong1, pull0) #(1, 2, 3) y = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FindFirst(r, ModuleItemKind::kContAssign);
  ASSERT_NE(ca, nullptr);
  EXPECT_NE(ca->drive_strength1, 0);
  EXPECT_NE(ca->drive_strength0, 0);
  EXPECT_NE(ca->assign_delay, nullptr);
  EXPECT_NE(ca->assign_delay_fall, nullptr);
  EXPECT_NE(ca->assign_delay_decay, nullptr);
}

// §10.3 Syntax 10-1 variable form: delay_control is optional —
// `assign [delay_control] list_of_variable_assignments ;`
TEST(ContinuousAssignSyntax, VariableFormBasic) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] v;\n"
      "  assign v = 8'd1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FindFirst(r, ModuleItemKind::kContAssign);
  ASSERT_NE(ca, nullptr);
  EXPECT_EQ(ca->assign_delay, nullptr);
}

// §10.3 Syntax 10-1:
//   list_of_net_assignments ::= net_assignment { , net_assignment }
TEST(ContinuousAssignSyntax, ListOfNetAssignments) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, d;\n"
      "  assign a = 1'b0, b = 1'b1, c = 1'b1, d = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(CountKind(r, ModuleItemKind::kContAssign), 4);
}

// §10.3 Syntax 10-1: net_assignment ::= net_lvalue = expression
TEST(ContinuousAssignSyntax, NetAssignmentLvalueAndRhs) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] y;\n"
      "  wire [7:0] a, b;\n"
      "  assign y = a + b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FindFirst(r, ModuleItemKind::kContAssign);
  ASSERT_NE(ca, nullptr);
  EXPECT_NE(ca->assign_lhs, nullptr);
  EXPECT_NE(ca->assign_rhs, nullptr);
}

// §10.3 Syntax 10-1: net_declaration ::=
//   net_type [drive_strength | charge_strength] [vectored | scalared]
//   data_type_or_implicit [delay3] list_of_net_decl_assignments ;
TEST(NetDeclarationSyntax, VectoredQualifier) {
  auto r = Parse(
      "module m;\n"
      "  wire vectored [7:0] w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nd = FindFirst(r, ModuleItemKind::kNetDecl);
  ASSERT_NE(nd, nullptr);
  EXPECT_TRUE(nd->data_type.is_vectored);
}

TEST(NetDeclarationSyntax, ScalaredQualifier) {
  auto r = Parse(
      "module m;\n"
      "  wire scalared [7:0] w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nd = FindFirst(r, ModuleItemKind::kNetDecl);
  ASSERT_NE(nd, nullptr);
  EXPECT_TRUE(nd->data_type.is_scalared);
}

// §10.3 Syntax 10-1 footnote 16: a charge strength shall only be used with the
// trireg keyword. The parser only sets charge_strength when the net type is
// trireg; on any other net the same `(small)` sequence has no syntactic
// landing spot.
TEST(NetDeclarationSyntax, ChargeStrengthOnTrireg) {
  auto r = Parse(
      "module m;\n"
      "  trireg (small) [7:0] cap;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nd = FindFirst(r, ModuleItemKind::kNetDecl);
  ASSERT_NE(nd, nullptr);
  EXPECT_NE(nd->data_type.charge_strength, 0);
}

TEST(NetDeclarationSyntax, ChargeStrengthOnWireIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire (small) [7:0] w;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §10.3 Syntax 10-1 alt 1 combines two optional fields: a trireg may carry
// both a charge_strength and a vectored qualifier in the same declaration.
TEST(NetDeclarationSyntax, TriregWithChargeStrengthAndVectored) {
  auto r = Parse(
      "module m;\n"
      "  trireg (small) vectored [7:0] cap;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nd = FindFirst(r, ModuleItemKind::kNetDecl);
  ASSERT_NE(nd, nullptr);
  EXPECT_NE(nd->data_type.charge_strength, 0);
  EXPECT_TRUE(nd->data_type.is_vectored);
}

// §10.3 Syntax 10-1: second alternative —
//   nettype_identifier [ delay_control ] list_of_net_decl_assignments ;
TEST(NetDeclarationSyntax, NettypeIdentifierForm) {
  auto r = Parse(
      "module m;\n"
      "  nettype real my_nt;\n"
      "  my_nt foo;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §10.3 Syntax 10-1: third alternative — interconnect form.
TEST(NetDeclarationSyntax, InterconnectForm) {
  auto r = Parse(
      "module m;\n"
      "  interconnect ic1, ic2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §10.3 Syntax 10-1:
//   list_of_net_decl_assignments ::= net_decl_assignment { , net_decl_assignment }
TEST(NetDeclarationSyntax, ListOfNetDeclAssignmentsMulti) {
  auto r = Parse(
      "module m;\n"
      "  wire a = 1'b0, b = 1'b1, c = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(CountKind(r, ModuleItemKind::kNetDecl), 3);
}

// §10.3 Syntax 10-1:
//   net_decl_assignment ::= net_identifier { unpacked_dimension } [ = expression ]
TEST(NetDeclarationSyntax, NetDeclAssignmentWithUnpackedDimAndInit) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] mem [0:3] = '{0, 1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nd = FindFirst(r, ModuleItemKind::kNetDecl);
  ASSERT_NE(nd, nullptr);
  EXPECT_FALSE(nd->unpacked_dims.empty());
  EXPECT_NE(nd->init_expr, nullptr);
}

// §10.3 Syntax 10-1:
//   list_of_variable_assignments ::=
//       variable_assignment { , variable_assignment }
// reached via `assign [delay_control] list_of_variable_assignments ;`.
TEST(ContinuousAssignSyntax, ListOfVariableAssignments) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] v1, v2, v3;\n"
      "  logic [7:0] a, b, c;\n"
      "  assign #5 v1 = a, v2 = b, v3 = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(CountKind(r, ModuleItemKind::kContAssign), 3);
}

}  // namespace
