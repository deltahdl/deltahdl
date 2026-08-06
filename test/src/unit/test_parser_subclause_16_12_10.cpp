#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §16.12.10: the indexed nexttime forms carry a tick count that shall be a
// non-negative integer constant expression. A non-negative integer literal
// index — including zero, the alignment-operator case — is accepted, and the
// property declaration parses cleanly.
TEST(NexttimeIndexParsing, LiteralNonNegativeIndexParses) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    nexttime[2] a;\n"
      "  endproperty\n"
      "  property q;\n"
      "    nexttime[0] a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

// §16.12.10: a negative integer literal tick count violates the non-negative
// requirement, so the weak indexed form `nexttime[-1]` is rejected during
// parsing.
TEST(NexttimeIndexParsing, NegativeLiteralIndexIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    nexttime[-1] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.10: the same non-negative requirement applies to the strong indexed
// form, so `s_nexttime[-1]` is likewise rejected. This exercises the separate
// operator-group code path that consumes the `s_nexttime` keyword.
TEST(NexttimeIndexParsing, StrongNegativeLiteralIndexIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_nexttime[-1] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.10: a symbolic index — here a module parameter — takes a different
// code path than an integer literal. The literal-only parse check leaves
// symbolic tick counts for the later constant-folding stages, so a parameter
// index parses without a parse-stage error rather than being misreported as
// negative.
TEST(NexttimeIndexParsing, SymbolicParameterIndexIsDeferred) {
  auto r = Parse(
      "module m;\n"
      "  parameter int N = 3;\n"
      "  property p;\n"
      "    nexttime[N] a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

}  // namespace
