#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ContAssignStatementPreprocessor, ContinuousAssignment) {
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

TEST(ContAssignStatementPreprocessor, NoDelayByDefault) {
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

TEST(ContAssignStatementPreprocessor, ContinuousAssignBasic) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a, b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  auto* ca = FindItemByKind(mod->items, ModuleItemKind::kContAssign);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  ASSERT_NE(ca->assign_rhs, nullptr);
}

}  // namespace
