#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(AlwaysRangeParsing, WeakRangedAlwaysWithNonNegativeBoundsParses) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    always[0:3] a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

TEST(AlwaysRangeParsing, NonRangedWeakAlwaysParses) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    always a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

TEST(AlwaysRangeParsing, WeakUnboundedAlwaysDollarMaximumParses) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    always[1:$] a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

TEST(AlwaysRangeParsing, NegativeWeakAlwaysBoundIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    always[-1:3] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "always range bounds must be non-negative "
                            "integer constant expressions",
                            3, "16.12.11"));
}

TEST(AlwaysRangeParsing, NegativeWeakAlwaysMaximumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    always[0:-2] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "always range bounds must be non-negative "
                            "integer constant expressions",
                            3, "16.12.11"));
}

TEST(AlwaysRangeParsing, StrongAlwaysUnboundedMaximumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_always[1:$] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "s_always needs a finite range, so its maximum cannot be `$`", 3,
      "16.12.11"));
}

TEST(AlwaysRangeParsing, StrongAlwaysBoundedRangeParses) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_always[0:4] a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

TEST(AlwaysRangeParsing, NegativeStrongAlwaysMaximumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_always[0:-2] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "always range bounds must be non-negative "
                            "integer constant expressions",
                            3, "16.12.11"));
}

TEST(AlwaysRangeParsing, NegativeStrongAlwaysMinimumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_always[-1:4] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "always range bounds must be non-negative "
                            "integer constant expressions",
                            3, "16.12.11"));
}

TEST(AlwaysRangeParsing, LiteralMinimumGreaterThanMaximumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    always[3:1] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "always range minimum must not exceed the maximum",
                            3, "16.12.11"));
}

TEST(AlwaysRangeParsing, StrongLiteralMinimumGreaterThanMaximumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_always[5:2] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "always range minimum must not exceed the maximum",
                            3, "16.12.11"));
}

TEST(AlwaysRangeParsing, EqualLiteralBoundsParse) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    always[2:2] a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

TEST(AlwaysRangeParsing, SymbolicParameterBoundIsDeferred) {
  auto r = Parse(
      "module m;\n"
      "  parameter int N = 4;\n"
      "  property p;\n"
      "    always[0:N] a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

TEST(AlwaysRangeParsing, LocalparamBoundIsDeferred) {
  auto r = Parse(
      "module m;\n"
      "  localparam int LP = 4;\n"
      "  property p;\n"
      "    always[0:LP] a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

TEST(AlwaysRangeParsing, StrongSymbolicParameterBoundIsDeferred) {
  auto r = Parse(
      "module m;\n"
      "  parameter int N = 4;\n"
      "  property p;\n"
      "    s_always[0:N] a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

}  // namespace
