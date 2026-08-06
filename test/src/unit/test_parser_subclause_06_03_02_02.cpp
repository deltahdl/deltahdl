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

}  // namespace
