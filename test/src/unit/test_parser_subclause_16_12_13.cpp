#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(EventuallyRangeParsing, WeakRangedEventuallyWithBoundedRangeParses) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    eventually[2:5] a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

TEST(EventuallyRangeParsing, WeakUnboundedEventuallyDollarMaximumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    eventually[2:$] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "weak eventually needs a finite range, so its maximum cannot be `$`", 3,
      "16.12.13"));
}

TEST(EventuallyRangeParsing, StrongUnboundedEventuallyDollarMaximumParses) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_eventually[2:$] a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

TEST(EventuallyRangeParsing, StrongRangedEventuallyWithBoundedRangeParses) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_eventually[2:5] a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

TEST(EventuallyRangeParsing, NonRangedStrongEventuallyParses) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_eventually a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

TEST(EventuallyRangeParsing, NegativeWeakEventuallyMinimumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    eventually[-1:3] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "eventually range bounds must be non-negative "
                            "integer constant expressions",
                            3, "16.12.13"));
}

TEST(EventuallyRangeParsing, NegativeWeakEventuallyMaximumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    eventually[0:-2] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "eventually range bounds must be non-negative "
                            "integer constant expressions",
                            3, "16.12.13"));
}

TEST(EventuallyRangeParsing, NegativeStrongEventuallyMinimumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_eventually[-1:3] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "eventually range bounds must be non-negative "
                            "integer constant expressions",
                            3, "16.12.13"));
}

TEST(EventuallyRangeParsing, NegativeStrongEventuallyMaximumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_eventually[0:-2] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "eventually range bounds must be non-negative "
                            "integer constant expressions",
                            3, "16.12.13"));
}

TEST(EventuallyRangeParsing, WeakLiteralMinimumGreaterThanMaximumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    eventually[5:2] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "eventually range minimum must not exceed the maximum", 3,
      "16.12.13"));
}

TEST(EventuallyRangeParsing, StrongLiteralMinimumGreaterThanMaximumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_eventually[5:2] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "eventually range minimum must not exceed the maximum", 3,
      "16.12.13"));
}

TEST(EventuallyRangeParsing, EqualLiteralBoundsParse) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    eventually[3:3] a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

TEST(EventuallyRangeParsing, WeakSymbolicParameterBoundIsDeferred) {
  auto r = Parse(
      "module m;\n"
      "  parameter int N = 4;\n"
      "  property p;\n"
      "    eventually[0:N] a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

TEST(EventuallyRangeParsing, WeakLocalparamBoundIsDeferred) {
  auto r = Parse(
      "module m;\n"
      "  localparam int LP = 4;\n"
      "  property p;\n"
      "    eventually[0:LP] a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

TEST(EventuallyRangeParsing, StrongSymbolicParameterBoundIsDeferred) {
  auto r = Parse(
      "module m;\n"
      "  parameter int N = 4;\n"
      "  property p;\n"
      "    s_eventually[0:N] a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

}  // namespace
