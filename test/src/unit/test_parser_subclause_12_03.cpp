#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(StatementLabelSyntaxParsing, ASecondLabelOnAStatementIsReported) {
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    a: b: x = 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got ':'", 4, "12.3"));
}

TEST(StatementLabelSyntaxParsing, AnAttributeAheadOfTheLabelIsReported) {
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    (* k *) a: x = 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got ':'", 4, "12.3"));
}

TEST(StatementLabelSyntaxParsing, OneLabelAheadOfTheAttributesIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    a: (* k *) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s = FirstInitialStmt(r);
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s->label, "a");
  ASSERT_EQ(s->attrs.size(), 1u);
  EXPECT_EQ(s->attrs[0].name, "k");
}

}  // namespace
