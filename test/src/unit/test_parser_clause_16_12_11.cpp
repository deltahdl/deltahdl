#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §16.12.11: the ranged weak always carries a
// cycle_delay_const_range_expression whose bounds are non-negative integer
// constant expressions. A bounded non-negative range is accepted and the
// property declaration parses cleanly.
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

// §16.12.11: the non-ranged weak always is a distinct form with no bracketed
// range, so `always property_expr` parses cleanly — the weak-always operator
// path does not require a range and raises no spurious diagnostic.
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

// §16.12.11: the range for a weak always may be unbounded, so a `$` maximum is
// accepted.
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

// §16.12.11: a negative integer literal bound violates the non-negative integer
// constant expression requirement, so the weak ranged form is rejected.
TEST(AlwaysRangeParsing, NegativeWeakAlwaysBoundIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    always[-1:3] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.11: the non-negative requirement applies to the weak form's maximum
// bound as well as its minimum, so a negative literal maximum in a weak
// `always` range is rejected. This covers the maximum-operand position on the
// weak code path (the minimum-position case is checked above).
TEST(AlwaysRangeParsing, NegativeWeakAlwaysMaximumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    always[0:-2] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.11: the range for a strong always shall be bounded, so `s_always` with
// a `$` maximum is rejected even though the same range is legal for a weak
// always. This also exercises the separate operator-group code path that
// consumes the `s_always` keyword.
TEST(AlwaysRangeParsing, StrongAlwaysUnboundedMaximumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_always[1:$] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.11: a bounded non-negative range remains legal for a strong always.
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

// §16.12.11: the non-negative requirement applies to the strong form's maximum
// bound as well, so a negative literal maximum in `s_always` is rejected.
TEST(AlwaysRangeParsing, NegativeStrongAlwaysMaximumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_always[0:-2] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.11: the non-negative requirement applies to the strong form's minimum
// bound as well as its maximum, so a negative literal minimum in an `s_always`
// range is rejected. This covers the minimum-operand position on the strong
// code path (the maximum-position case is checked above).
TEST(AlwaysRangeParsing, NegativeStrongAlwaysMinimumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_always[-1:4] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.11: when both bounds are non-negative integer constant literals the
// minimum shall not exceed the maximum, so an inverted weak range is rejected
// at parse time.
TEST(AlwaysRangeParsing, LiteralMinimumGreaterThanMaximumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    always[3:1] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.11: the same minimum-not-exceeding-maximum requirement applies to the
// strong form, so an inverted `s_always` literal range is rejected.
TEST(AlwaysRangeParsing, StrongLiteralMinimumGreaterThanMaximumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_always[5:2] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.11: the relation is less-than-or-equal, so equal literal bounds are a
// legal single-tick range and parse cleanly.
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

// §16.12.11: a symbolic bound — here a module parameter — takes a different
// code path than an integer literal. The literal-only parse check leaves
// symbolic bounds for the later constant-folding stages, so a parameter bound
// parses without a parse-stage error rather than being misreported.
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

// §16.12.11: a localparam is another non-negative integer constant expression
// form admitted for a range bound (§11.2.1). Like a parameter it is a symbolic
// reference rather than an integer literal, so the literal-only parse check
// defers it and the property parses without a parse-stage error.
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

// §16.12.11: the strong operator takes its own keyword-consuming code path, so
// a symbolic (parameter) bound on `s_always` is likewise deferred rather than
// misreported — the strong-form counterpart of the weak deferral above.
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
