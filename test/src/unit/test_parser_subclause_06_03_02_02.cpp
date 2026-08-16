// §6.3.2.2 Drive strength: "The drive strength specification allows a
// continuous assignment to be placed on a net in the same statement that
// declares that net." What the parser owes that sentence is the pairing --
// the strength and the assignment reaching one declaration together, with the
// strength0 and strength1 keywords landing on their own fields whichever order
// they were written in.
//
// Every source below drives strength0 and strength1 to different values
// (weak0 is 2, pull1 is 3), so a reading that swapped the two fields, or
// filled both from one keyword, is a failure rather than a coincidence.

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(NetDeclDriveStrengthParsing, StrengthAndAssignmentReachOneDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  wire (pull1, weak0) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->drive_strength0, 2);
  EXPECT_EQ(item->drive_strength1, 3);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(NetDeclDriveStrengthParsing, StrengthKeywordsMayBeWrittenInEitherOrder) {
  auto r = Parse(
      "module m;\n"
      "  wire (weak0, pull1) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 2);
  EXPECT_EQ(item->drive_strength1, 3);
}

TEST(NetDeclDriveStrengthParsing, DeclarationWithNoStrengthLeavesBothUnset) {
  auto r = Parse(
      "module m;\n"
      "  wire w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 0);
  EXPECT_EQ(item->drive_strength1, 0);
  EXPECT_NE(item->init_expr, nullptr);
}

// One strength, written once, heads a list whose declarators each decide for
// themselves whether an assignment is placed on them. The strength reaches
// both nets and only the first carries an assignment, which is the shape
// §6.3.2.2's rule has to be able to tell apart -- a check reading the
// statement rather than the declaration would see an assignment here and stop.
TEST(NetDeclDriveStrengthParsing, StrengthHeadsAListOfSeparateDeclarators) {
  auto r = Parse(
      "module m;\n"
      "  wire (pull1, weak0) a = 1'b1, b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[1]->name, "b");
  EXPECT_EQ(items[1]->drive_strength0, 2);
  EXPECT_EQ(items[1]->drive_strength1, 3);
  EXPECT_NE(items[0]->init_expr, nullptr);
  EXPECT_EQ(items[1]->init_expr, nullptr);
}

// §6.3.2 attaches one condition to a drive strength -- "Drive strength shall
// only be used when placing a continuous assignment on a net in the same
// statement that declares the net" -- and says nothing about which net type
// carries it. §A.2.1.3 gives `net_declaration ::= net_type [ drive_strength |
// charge_strength ] [ vectored | scalared ] data_type_or_implicit [ delay3 ]
// list_of_net_decl_assignments ;` and §A.2.2.1 lists `trireg` among the
// alternatives of `net_type`, so the strength is available here exactly as it
// is on a `wire`. The two strengths differ, as everywhere else in this file.
TEST(NetDeclDriveStrengthParsing, TriregCarriesAStrengthWithItsAssignment) {
  auto r = Parse(
      "module m;\n"
      "  trireg (pull1, weak0) t = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->drive_strength0, 2);
  EXPECT_EQ(item->drive_strength1, 3);
  EXPECT_NE(item->init_expr, nullptr);
}

// §A.2.1.3 puts `delay3` after the strength, so a `trireg` may write both. The
// delay is what pins that the strength parse left the position where the rest
// of the declaration expects it: a parse consuming one token too few or too
// many shows up here as the delay going missing, where the case above would
// still pass on the two strength fields alone.
TEST(NetDeclDriveStrengthParsing, TriregStrengthPrecedesItsDelay) {
  auto r = Parse(
      "module m;\n"
      "  trireg (pull1, weak0) #5 t = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 2);
  EXPECT_EQ(item->drive_strength1, 3);
  EXPECT_NE(item->net_delay, nullptr);
}

}  // namespace
