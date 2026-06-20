#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ContAssignDelayPreprocessor, SingleDelay) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  wire out, in;\n"
      "  assign #5 out = in;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  const auto* assign_item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kContAssign);
  ASSERT_NE(assign_item, nullptr) << "no continuous assignment found";
  ASSERT_NE(assign_item->assign_delay, nullptr);
  EXPECT_EQ(assign_item->assign_delay->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(assign_item->assign_delay->int_val, 5);
}

TEST(ContAssignDelayPreprocessor, ParenthesizedSingleDelay) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  wire out, in;\n"
      "  assign #(10) out = in;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kContAssign) continue;
    found = true;
    ASSERT_NE(item->assign_delay, nullptr);
    EXPECT_EQ(item->assign_delay->int_val, 10);
  }
  EXPECT_TRUE(found);
}

TEST(ContAssignDelayPreprocessor, ThreeValueDelay) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  wire out, in;\n"
      "  assign #(5, 10, 15) out = in;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  const auto* assign_item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kContAssign);
  ASSERT_NE(assign_item, nullptr);
  ASSERT_NE(assign_item->assign_delay, nullptr);
  EXPECT_EQ(assign_item->assign_delay->int_val, 5);
  ASSERT_NE(assign_item->assign_delay_fall, nullptr);
  EXPECT_EQ(assign_item->assign_delay_fall->int_val, 10);
  ASSERT_NE(assign_item->assign_delay_decay, nullptr);
  EXPECT_EQ(assign_item->assign_delay_decay->int_val, 15);
}

TEST(ContAssignDelayPreprocessor, RiseFallDelay) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  wire out, in;\n"
      "  assign #(5, 10) out = in;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  const auto* assign_item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kContAssign);
  ASSERT_NE(assign_item, nullptr);
  ASSERT_NE(assign_item->assign_delay, nullptr);
  EXPECT_EQ(assign_item->assign_delay->int_val, 5);
  ASSERT_NE(assign_item->assign_delay_fall, nullptr);
  EXPECT_EQ(assign_item->assign_delay_fall->int_val, 10);
  EXPECT_EQ(assign_item->assign_delay_decay, nullptr);
}

TEST(ContAssignDelayPreprocessor, NetDeclDelayWithInit) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  wire #5 w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 5);
}

}  // namespace
