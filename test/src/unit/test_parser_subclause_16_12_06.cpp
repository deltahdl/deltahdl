#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

TEST(AssertionSemanticsParsing, PropertyIfElse) {
  auto r = Parse(
      "module m;\n"
      "  property p_cond;\n"
      "    @(posedge clk) if (mode) a |-> b else c |-> d;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kPropertyDecl));
}

TEST(AssertionSemanticsParsing, PropertyIfWithoutElse) {
  auto r = Parse(
      "module m;\n"
      "  property p_cond;\n"
      "    @(posedge clk) if (mode) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kPropertyDecl));
}

TEST(AssertionSemanticsParsing, PropertyIfElseIfChain) {
  auto r = Parse(
      "module m;\n"
      "  property p_cond;\n"
      "    @(posedge clk) if (s == 0) a |-> b\n"
      "    else if (s == 1) c |-> d\n"
      "    else e |-> f;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kPropertyDecl));
}

TEST(AssertionSemanticsParsing, ASequenceWrittenAsAnIfConditionIsReported) {
  for (const char* body :
       {"if (a ##1 b) c", "if (a ##1 b) c else a", "if (a[*2]) c",
        "if ((a ##1 b)) c", "if (first_match(a ##1 b)) c"}) {
    SCOPED_TRACE(body);
    auto r = Parse(std::string("module m;\n  logic clk; bit a, b, c;\n"
                               "  a1: assert property (@(posedge clk) ") +
                   body + ");\nendmodule\n");
    EXPECT_TRUE(ReportedError(r.diags, "the grammar admits", 3, "A.2.10"));
  }
}

TEST(AssertionSemanticsParsing, AnExpressionWrittenAsAnIfConditionIsRead) {
  for (const char* body : {"if (a) c", "if ((a)) c else b", "if (a && !b) c",
                           "if (a dist {1 := 1}) c", "if ($rose(a)) c"}) {
    SCOPED_TRACE(body);
    auto r = Parse(std::string("module m;\n  logic clk; bit a, b, c;\n"
                               "  a1: assert property (@(posedge clk) ") +
                   body + ");\nendmodule\n");
    EXPECT_FALSE(r.has_errors);
  }
}

}  // namespace
