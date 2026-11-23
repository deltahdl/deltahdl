#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(OptionalDirectiveExtendedParsing, DelayModeDistributed) {
  auto r = ParseWithPreprocessor(
      "`delay_mode_distributed\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->delay_mode_directive, DelayModeDirective::kDistributed);
}

TEST(OptionalDirectiveExtendedParsing, DelayMode_NoDirective) {
  auto r = ParseWithPreprocessor("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->delay_mode_directive, DelayModeDirective::kNone);
}

TEST(OptionalDirectiveExtendedParsing,
     DISABLED_DelayModeDistributed_AnIdentifierAfterItStaysSourceText) {
  auto r = ParseWithPreprocessor(
      "`delay_mode_distributed extra\n"
      "module m; endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected top-level declaration", 1, "3.12.1"));
}

TEST(OptionalDirectiveExtendedParsing,
     DISABLED_DelayModeDistributed_ADeclarationAfterItStaysSourceText) {
  auto r = ParseWithPreprocessor(
      "`delay_mode_distributed wire w;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->delay_mode_directive, DelayModeDirective::kDistributed);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "w");
}

}  // namespace
