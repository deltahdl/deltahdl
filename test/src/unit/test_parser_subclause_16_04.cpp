#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(DeferredAssertionParsing, Hash0AssertObservedNotFinal) {
  auto r = Parse(
      "module m;\n"
      "  initial assert #0 (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_FALSE(stmt->is_final_deferred);
}

TEST(DeferredAssertionParsing, FinalAssertMarksFinalDeferred) {
  auto r = Parse(
      "module m;\n"
      "  initial assert final (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_TRUE(stmt->is_final_deferred);
}

TEST(DeferredAssertionParsing, Hash0AssumeObservedNotFinal) {
  auto r = Parse(
      "module m;\n"
      "  initial assume #0 (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_FALSE(stmt->is_final_deferred);
}

TEST(DeferredAssertionParsing, FinalAssumeMarksFinalDeferred) {
  auto r = Parse(
      "module m;\n"
      "  initial assume final (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_TRUE(stmt->is_final_deferred);
}

TEST(DeferredAssertionParsing, Hash0CoverObservedNotFinal) {
  auto r = Parse(
      "module m;\n"
      "  initial cover #0 (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_FALSE(stmt->is_final_deferred);
}

TEST(DeferredAssertionParsing, FinalCoverMarksFinalDeferred) {
  auto r = Parse(
      "module m;\n"
      "  initial cover final (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_TRUE(stmt->is_final_deferred);
}

TEST(DeferredAssertionParsing, ModuleLevelFinalAssertParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic c;\n"
              "  chk: assert final (c);\n"
              "endmodule\n"));
}

TEST(DeferredAssertionParsing, ModuleLevelHash0CoverParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic c;\n"
              "  hit: cover #0 (c);\n"
              "endmodule\n"));
}

TEST(DeferredAssertionParsing, FinalAssertMissingExpressionRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial assert final;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected '(', got ';'", 2, "16.3"));
}

TEST(DeferredAssertionParsing, Hash0PrecludesFinalKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial assert #0 final (1);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected '(', got 'final'", 2, "16.3"));
}

TEST(DeferredAssertionParsing, FinalAssertWithPassAndFailActions) {
  auto r = Parse(
      "module m;\n"
      "  initial assert final (1) $info(\"ok\"); else $error(\"bad\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->is_final_deferred);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

TEST(DeferredAssertionParsing, ProceduralAssertNonZeroHashRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial assert #5 (1);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "deferred immediate assertion requires #0, got #5", 2, "16.4"));
}

TEST(DeferredAssertionParsing, ProceduralAssumeNonZeroHashRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial assume #3 (1);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "deferred immediate assertion requires #0, got #3", 2, "16.4"));
}

TEST(DeferredAssertionParsing, ProceduralCoverNonZeroHashRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial cover #7 (1);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "deferred immediate assertion requires #0, got #7", 2, "16.4"));
}

TEST(DeferredAssertionParsing, ModuleLevelAssertNonZeroHashRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic c;\n"
      "  chk: assert #2 (c);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "deferred immediate assertion requires #0, got #2", 3, "16.4"));
}

TEST(DeferredAssertionParsing, ModuleLevelCoverNonZeroHashRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic c;\n"
      "  hit: cover #4 (c);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "deferred immediate assertion requires #0, got #4", 3, "16.4"));
}

TEST(DeferredAssertionParsing, DeferredCoverModuleItemWithElseRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic c, hit, miss;\n"
      "  cover #0 (c) hit = 1;\n"
      "  else miss = 1;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "cover has no fail statement", 4, "16.3"));
}

TEST(DeferredAssertionParsing, ModuleLevelHash0CoverWithPassStatementParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic c, hit;\n"
              "  cover #0 (c) hit = 1;\n"
              "endmodule\n"));
}

const Stmt* FirstDeferredItemBody(const ParseResult& r) {
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAssertProperty) return item->body;
  }
  return nullptr;
}

TEST(DeferredAssertionParsing, SpacedHashZeroIsAnObservedDeferredAssertion) {
  auto r = Parse(
      "module m;\n"
      "  logic c;\n"
      "  initial assert # 0 (c);\n"
      "  a1: assert # 0 (c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_FALSE(stmt->is_final_deferred);
  auto* body = FirstDeferredItemBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(body->is_deferred);
  EXPECT_FALSE(body->is_final_deferred);
}

TEST(DeferredAssertionParsing, ModuleLevelAssumeNonZeroHashRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic c;\n"
      "  assume #3 (c);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "deferred immediate assertion requires #0, got #3", 3, "16.4"));
}

TEST(DeferredAssertionParsing, ModuleLevelAssumeHash0Parses) {
  auto r = Parse(
      "module m;\n"
      "  logic c;\n"
      "  assume #0 (c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstDeferredItemBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kAssumeImmediate);
  EXPECT_TRUE(body->is_deferred);
  EXPECT_FALSE(body->is_final_deferred);
}

ParseResult ParseDeferredForm(const std::string& line) {
  return Parse("module m;\n  logic c;\n  parameter P = 0;\n" + line +
               "\nendmodule\n");
}

TEST(DeferredAssertionParsing, Hash0WithFinalRejectedForEachDirective) {
  const char* const kLines[] = {
      "  initial assume #0 final (c);", "  initial cover #0 final (c);",
      "  assert #0 final (c);", "  assume #0 final (c);"};
  for (const char* line : kLines) {
    auto r = ParseDeferredForm(line);
    EXPECT_TRUE(ReportedError(r.diags, "expected '(', got 'final'", 4, "16.3"))
        << line;
  }
}

TEST(DeferredAssertionParsing,
     DISABLED_ModuleLevelCoverHash0WithFinalRejected) {
  auto r = ParseDeferredForm("  cover #0 final (c);");
  EXPECT_TRUE(ReportedError(r.diags, "expected '(', got 'final'", 4, "16.3"));
}

TEST(DeferredAssertionParsing, FinalWithHash0RejectedForEachDirective) {
  const char* const kLines[] = {
      "  initial assert final #0 (c);", "  initial assume final #0 (c);",
      "  initial cover final #0 (c);", "  assert final #0 (c);",
      "  assume final #0 (c);"};
  for (const char* line : kLines) {
    auto r = ParseDeferredForm(line);
    EXPECT_TRUE(ReportedError(r.diags, "expected '(', got '#'", 4, "16.3"))
        << line;
  }
}

TEST(DeferredAssertionParsing,
     DISABLED_ModuleLevelCoverFinalWithHash0Rejected) {
  auto r = ParseDeferredForm("  cover final #0 (c);");
  EXPECT_TRUE(ReportedError(r.diags, "expected '(', got '#'", 4, "16.3"));
}

TEST(DeferredAssertionParsing, FinalWithoutHash0ParsesForEachDirective) {
  const char* const kLines[] = {
      "  initial assert final (c);", "  initial assume final (c);",
      "  initial cover final (c);",  "  assert final (c);",
      "  assume final (c);",         "  cover final (c);"};
  for (const char* line : kLines) {
    auto r = ParseDeferredForm(line);
    EXPECT_FALSE(r.has_errors) << line;
  }
}

struct DelayForm {
  const char* delay;
  const char* got;
};

constexpr DelayForm kNonLiteralDelays[] = {{"#(0)", "'('"},
                                           {"#0.0", "real literal"},
                                           {"#1ns", "time literal"},
                                           {"#P", "identifier"},
                                           {"#'0", "unbased unsized literal"}};

TEST(DeferredAssertionParsing, ProceduralNonLiteralZeroDelaysRejected) {
  for (const auto& form : kNonLiteralDelays) {
    auto r = ParseDeferredForm(std::string("  initial assert ") + form.delay +
                               " (c);");
    EXPECT_TRUE(ReportedError(
        r.diags, std::string("expected integer literal, got ") + form.got, 4,
        "16.4"))
        << form.delay;
  }
}

TEST(DeferredAssertionParsing, ModuleLevelNonLiteralZeroDelaysRejected) {
  const char* const kDirectives[] = {"assert", "assume", "cover"};
  for (const char* directive : kDirectives) {
    for (const auto& form : kNonLiteralDelays) {
      auto r = ParseDeferredForm(std::string("  ") + directive + " " +
                                 form.delay + " (c);");
      EXPECT_TRUE(ReportedError(
          r.diags, std::string("expected integer literal, got ") + form.got, 4,
          "16.4"))
          << directive << " " << form.delay;
    }
  }
}

TEST(DeferredAssertionParsing, ModuleLevelHash0ParsesForEachDirective) {
  const char* const kDirectives[] = {"assert", "assume", "cover"};
  for (const char* directive : kDirectives) {
    auto r = ParseDeferredForm(std::string("  ") + directive + " #0 (c);");
    EXPECT_FALSE(r.has_errors) << directive;
  }
}

TEST(DeferredAssertionParsing, ModuleLevelFinalCoverWithElseRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic c, hit, miss;\n"
      "  cover final (c) hit = 1;\n"
      "  else miss = 1;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "cover has no fail statement", 4, "16.3"));
}

TEST(DeferredAssertionParsing, ModuleLevelFinalCoverWithPassStatementParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic c, hit;\n"
              "  cover final (c) hit = 1;\n"
              "endmodule\n"));
}

size_t ErrorCount(const std::vector<Diagnostic>& diags) {
  size_t n = 0;
  for (const auto& d : diags) n += d.severity == DiagSeverity::kError;
  return n;
}

TEST(DeferredAssertionParsing, AProgramsGenerateBlockRefusesAStaticForm) {
  auto r = Parse(
      "program p;\n"
      "  if (1) begin : g\n"
      "    a1: assert #0 (1);\n"
      "  end\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a deferred immediate assertion is not an item of a program", 3,
      "A.1.7"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  if (1) begin : g\n"
              "    a1: assert #0 (1);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(DeferredAssertionParsing, APackageRefusesEveryStaticForm) {
  for (const char* item :
       {"a1: assert #0 (1);", "a1: assume final (1);", "a1: cover #0 (1);"}) {
    auto r = Parse(std::string("package p;\n  ") + item + "\nendpackage\n");
    EXPECT_TRUE(ReportedError(
        r.diags, "an assertion statement is not an item of a package", 2,
        "A.1.11"))
        << item;
    EXPECT_TRUE(ParseOk(std::string("module m;\n  ") + item + "\nendmodule\n"))
        << item;
  }
}

TEST(DeferredAssertionParsing, DISABLED_AClassBodyRefusesAStaticForm) {
  auto r = Parse(
      "class C;\n"
      "  a1: assert #0 (1);\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "an assertion statement is not an item of a class", 2, "A.1.9"));
  EXPECT_EQ(ErrorCount(r.diags), 1u);
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  function void f;\n"
              "    a1: assert #0 (1);\n"
              "  endfunction\n"
              "endclass\n"));
}

TEST(DeferredAssertionParsing, DISABLED_TheCompilationUnitRefusesAStaticForm) {
  auto r = Parse(
      "a1: assert #0 (1);\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "an assertion statement is not an item of the compilation unit",
      1, "A.1.2"));
  EXPECT_EQ(ErrorCount(r.diags), 1u);
}

}  // namespace
