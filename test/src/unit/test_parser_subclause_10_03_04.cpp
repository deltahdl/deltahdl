#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DriveStrengthParsing, DriveStrengthContinuousAssign) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, pull1) w = 1'b1;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kContAssign);
  EXPECT_EQ(item->drive_strength0, 4u);
  EXPECT_EQ(item->drive_strength1, 3u);
}
TEST(DriveStrengthParsing, ContinuousAssignStrengthWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign (pull0, pull1) #5 a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_NE(cas[0]->drive_strength0, 0u);
  EXPECT_NE(cas[0]->drive_strength1, 0u);
  EXPECT_NE(cas[0]->assign_delay, nullptr);
}

TEST(DriveStrengthParsing, NetDeclDriveStrength) {
  auto r = Parse(
      "module m;\n"
      "  wire (weak0, strong1) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);

  EXPECT_EQ(item->drive_strength0, 2u);
  EXPECT_EQ(item->drive_strength1, 4u);
}

TEST(DriveStrengthParsing, NetDeclAssignmentWithDriveStrength) {
  auto r = Parse("module m; wire (strong1, pull0) mynet = 1'b1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "mynet");
  EXPECT_NE(item->init_expr, nullptr);
  EXPECT_NE(item->data_type.drive_strength0, 0);
  EXPECT_NE(item->data_type.drive_strength1, 0);
}

TEST(DriveStrengthParsing, Highz0Highz1PairParsesWithoutError) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz0, highz1) w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->drive_strength0, 1u);
  EXPECT_EQ(cas[0]->drive_strength1, 1u);
}

TEST(DriveStrengthParsing, NoStrengthEncodesAsZero) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->drive_strength0, 0u);
  EXPECT_EQ(cas[0]->drive_strength1, 0u);
}

TEST(DriveStrengthParsing, NetDeclReversedStrengthOrder) {
  auto r = Parse(
      "module m;\n"
      "  wire (strong1, weak0) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->drive_strength0, 2u);
  EXPECT_EQ(item->drive_strength1, 4u);
}

// §10.3.4: a drive strength specification must pair one strength-for-1 keyword
// with one strength-for-0 keyword. Two strength-0 keywords leave the
// strength-1 slot unfilled, which the parser rejects.
TEST(DriveStrengthParsing, TwoStrength0KeywordsIsError) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, weak0) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags,
      "drive_strength on a continuous assignment requires one strength0", 3,
      "10.3.4"));
}

// The mirror case: two strength-1 keywords leave the strength-0 slot unfilled.
TEST(DriveStrengthParsing, TwoStrength1KeywordsIsError) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong1, pull1) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags,
      "drive_strength on a continuous assignment requires one strength0", 3,
      "10.3.4"));
}

// §10.3.4: on a net declaration the strength follows the net-type keyword and
// precedes any delay. Both the drive strength and the net delay are captured.
TEST(DriveStrengthParsing, NetDeclStrengthBeforeDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire (strong1, strong0) #5 w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->drive_strength0, 4u);
  EXPECT_EQ(item->drive_strength1, 4u);
  EXPECT_NE(item->net_delay, nullptr);
}

// §10.3.4: the strength specification "shall immediately follow the keyword
// (either the keyword for the net type or `assign`) and precede any delay
// specified", which §A.6.1 writes as `assign [ drive_strength ] [ delay3 ]
// list_of_net_assignments ;`. The report stands at the strength's own opening
// parenthesis on line 3, which is the token in the wrong place.
TEST(DriveStrengthParsing, StrengthAfterDelayIsError) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign #5 (pull0, pull1) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "drive strength shall precede any delay specified",
                            3, "10.3.4"));
}

// §10.3.4 names the net-type keyword alongside `assign`, and §A.2.1.3 writes
// the same order into `net_declaration ::= net_type [ drive_strength |
// charge_strength ] [ vectored | scalared ] data_type_or_implicit [ delay3 ]
// list_of_net_decl_assignments ;`. This case reaches the rule through
// Parser::ParseVarDeclList, where the net delay is read, rather than through
// Parser::ParseContinuousAssign, so it is not redundant with the case above.
TEST(DriveStrengthParsing, NetDeclDelayBeforeStrengthIsError) {
  auto r = Parse(
      "module m;\n"
      "  wire #5 (strong1, strong0) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "drive strength shall precede any delay specified",
                            2, "10.3.4"));
}

}  // namespace
