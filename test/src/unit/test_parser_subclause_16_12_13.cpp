#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §16.12.13: the ranged weak `eventually` carries a constant_range whose bounds
// are non-negative integer constant expressions. A bounded non-negative range
// is accepted and the property declaration parses cleanly.
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

// §16.12.13: the range for a weak `eventually` shall be bounded, so a `$`
// maximum is illegal — the `eventually [2:$]` form is the LRM's explicit
// illegal example (p6).
TEST(EventuallyRangeParsing, WeakUnboundedEventuallyDollarMaximumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    eventually[2:$] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.13: the range for a strong `s_eventually` may be unbounded, so a `$`
// maximum is accepted even though the same bound is illegal for the weak form.
// This is the legal p7 counterpart of the illegal weak p6 example, and it also
// exercises the separate operator-group code path that consumes the
// `s_eventually` keyword.
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

// §16.12.13: a bounded non-negative range is also legal for the strong form.
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

// §16.12.13: the non-ranged `s_eventually property_expr` is a distinct form
// with no bracketed range, so it parses cleanly — the strong-eventually
// operator path does not require a range and raises no spurious diagnostic.
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

// §16.12.13: a negative integer literal minimum violates the non-negative
// integer constant expression requirement, so the weak ranged form is rejected.
TEST(EventuallyRangeParsing, NegativeWeakEventuallyMinimumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    eventually[-1:3] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.13: the non-negative requirement applies to the maximum bound as well,
// so a negative literal maximum in a weak `eventually` range is rejected. This
// covers the maximum-operand position on the weak code path.
TEST(EventuallyRangeParsing, NegativeWeakEventuallyMaximumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    eventually[0:-2] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.13: the non-negative requirement applies to the strong form's minimum
// bound as well, and the strong operator takes its own keyword-consuming code
// path, so a negative literal minimum in `s_eventually` is rejected.
TEST(EventuallyRangeParsing, NegativeStrongEventuallyMinimumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_eventually[-1:3] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.13: the non-negative requirement also applies to the strong form's
// maximum bound, so a negative literal maximum in `s_eventually` is rejected.
// This is the strong-path counterpart of the weak maximum case above, covering
// the maximum-operand position reached through the strong operator's own
// keyword-consuming dispatch (the minimum-position case is checked above).
TEST(EventuallyRangeParsing, NegativeStrongEventuallyMaximumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_eventually[0:-2] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.13: when both bounds are non-negative integer constant literals the
// minimum shall not exceed the maximum, so an inverted weak range is rejected
// at parse time.
TEST(EventuallyRangeParsing, WeakLiteralMinimumGreaterThanMaximumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    eventually[5:2] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.13: the same minimum-not-exceeding-maximum requirement applies to the
// strong form, so an inverted `s_eventually` literal range is rejected.
TEST(EventuallyRangeParsing, StrongLiteralMinimumGreaterThanMaximumIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_eventually[5:2] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.13: the relation is less-than-or-equal, so equal literal bounds are a
// legal single-tick range and parse cleanly.
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

// §16.12.13: a symbolic bound — here a module parameter (§11.2.1) — takes a
// different code path than an integer literal. The literal-only parse check
// leaves symbolic bounds for the later constant-folding stages, so a parameter
// bound on the weak form parses without a parse-stage error rather than being
// misreported.
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

// §16.12.13: a localparam is another non-negative integer constant expression
// form admitted for a range bound (§11.2.1). Like a parameter it is a symbolic
// reference rather than an integer literal, so the literal-only parse check
// defers it and the weak `eventually` property parses without a parse-stage
// error, built from a real localparam declaration.
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

// §16.12.13: the strong operator takes its own keyword-consuming code path, so
// a symbolic (parameter) bound on `s_eventually` is likewise deferred rather
// than misreported — the strong-form counterpart of the weak deferral above.
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
