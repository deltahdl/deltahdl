// §10.3.2: The continuous assignment statement

#include "fixture_parser.h"

using namespace delta;

static ModuleItem* FindItemByKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

namespace {

// §3.3 Continuous assignments
TEST(ParserClause03, Cl3_3_ContinuousAssignment) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  logic a, b, y;\n"
      "  assign y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FindItemByKind(r, ModuleItemKind::kContAssign);
  ASSERT_NE(ca, nullptr);
}

TEST(Lexical, ContAssign_NoDelay) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  wire a, b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kContAssign) continue;
    EXPECT_EQ(item->assign_delay, nullptr);
  }
}

TEST(Parser, ContinuousAssignment) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  logic a, b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found_assign = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      found_assign = true;
    }
  }
  EXPECT_TRUE(found_assign);
}

}  // namespace
