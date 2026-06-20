#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(CheckerItemsParsing, AssertionsInChecker) {
  auto r = ParseWithPreprocessor(
      "checker req_ack_chk(logic clk, req, ack);\n"
      "  property req_followed_by_ack;\n"
      "    @(posedge clk) req |-> ##[1:3] ack;\n"
      "  endproperty\n"
      "  assert property (req_followed_by_ack);\n"
      "  cover property (req_followed_by_ack);\n"
      "endchecker : req_ack_chk\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "req_ack_chk");
  ASSERT_GE(r.cu->checkers[0]->ports.size(), 3u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kPropertyDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kAssertProperty));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kCoverProperty));
}

TEST(CheckerItemsParsing, ModelingCodeInChecker) {
  auto r = ParseWithPreprocessor(
      "checker model_chk;\n"
      "  logic flag;\n"
      "  initial flag = 0;\n"
      "  always @(flag) flag <= ~flag;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kAlwaysBlock));
  EXPECT_GE(r.cu->checkers[0]->items.size(), 3u);
}

TEST(CheckerItemsParsing, IfdefSelectsCheckerItem) {
  auto r = ParseWithPreprocessor(
      "`define HAS_INIT\n"
      "checker chk;\n"
      "`ifdef HAS_INIT\n"
      "  initial $display(\"yes\");\n"
      "`endif\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(CheckerItemsParsing, IfndefOmitsCheckerItem) {
  auto r = ParseWithPreprocessor(
      "`define HAS_FINAL\n"
      "checker chk;\n"
      "`ifndef HAS_FINAL\n"
      "  final $display(\"no\");\n"
      "`endif\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_FALSE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kFinalBlock));
}

TEST(CheckerItemsParsing, MacroExpandsToCheckerItem) {
  auto r = ParseWithPreprocessor(
      "`define CHK_BODY initial $display(\"macro\");\n"
      "checker chk;\n"
      "  `CHK_BODY\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kInitialBlock));
}

}  // namespace
