#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_parser.h"
#include "helpers_nested_assertions.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(RestrictStatementParsing, FormWithoutActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  logic ctr;\n"
      "  restrict property (@(posedge clk) ctr == '0);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kRestrictProperty) {
      found = true;
      EXPECT_NE(item->assert_expr, nullptr);
      EXPECT_EQ(item->assert_pass_stmt, nullptr);
      EXPECT_EQ(item->assert_fail_stmt, nullptr);
    }
  }
  EXPECT_TRUE(found);
  EXPECT_FALSE(r.has_errors);
}

TEST(RestrictStatementParsing, RejectsActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  logic ctr;\n"
      "  restrict property (@(posedge clk) ctr == '0) $display(\"x\");\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got system identifier", 4,
                            "16.14.4"));
}

TEST(RestrictStatementParsing, RejectsElseClause) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  logic ctr;\n"
      "  restrict property (@(posedge clk) ctr == '0) else $error(\"x\");\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got 'else'", 4, "16.14.4"));
}

struct RestrictEnding {
  const char* tail;
  const char* report;
};

constexpr RestrictEnding kActionBlockEndings[] = {
    {" $display(\"x\");", "expected ';', got system identifier"},
    {" else $error(\"x\");", "expected ';', got 'else'"},
    {" begin end else $error(\"x\");", "expected ';', got 'begin'"}};

std::vector<std::string> RestrictPrefixes(const std::string& place) {
  return {"", NestingProcedureIn(place), "initial "};
}

std::string RestrictSource(const std::string& place, const std::string& prefix,
                           const std::string& tail) {
  return NestingSource(
      place, prefix + "x1: restrict property (@(posedge clk) a)" + tail);
}

TEST(RestrictStatementParsing, AnActionBlockIsRefusedInEachPlace) {
  for (const char* place : kNestingPlaces) {
    for (const std::string& prefix : RestrictPrefixes(place)) {
      if (std::string(place) == "checker" && prefix == "initial ") continue;
      for (const RestrictEnding& ending : kActionBlockEndings) {
        std::string src = RestrictSource(place, prefix, ending.tail);
        SCOPED_TRACE(src);
        auto r = Parse(src);
        EXPECT_TRUE(ReportedError(r.diags, ending.report,
                                  LineHolding(src, "x1:"), "16.14.4"));
      }
    }
  }
}

TEST(RestrictStatementParsing,
     TheStatementEndingAtItsSemicolonIsAcceptedInEachPlace) {
  for (const char* place : kNestingPlaces) {
    for (const std::string& prefix : RestrictPrefixes(place)) {
      if (std::string(place) == "checker" && prefix == "initial ") continue;
      std::string src = RestrictSource(place, prefix, ";");
      SCOPED_TRACE(src);
      EXPECT_FALSE(Parse(src).has_errors);
    }
  }
}

}  // namespace
