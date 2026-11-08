#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

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

TEST(NexttimeIndexParsing, NegativeLiteralIndexIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    nexttime[-1] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "nexttime index must be a non-negative integer constant", 3,
      "16.12.10"));
}

TEST(NexttimeIndexParsing, StrongNegativeLiteralIndexIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_nexttime[-1] a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "nexttime index must be a non-negative integer constant", 3,
      "16.12.10"));
}

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

TEST(NexttimeIndexParsing, ASourceEndingInTheStrongFormsIndexEndsTheBody) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    s_nexttime [1");
  EXPECT_TRUE(
      ReportedError(r.diags, "is not one the grammar admits", 3, "A.2.10"));
}

}  // namespace
