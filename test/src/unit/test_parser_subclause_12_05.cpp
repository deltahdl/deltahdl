#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

using namespace delta;
namespace {

TEST(CaseSyntaxParsing, CaseInInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (mode)\n"
      "      0: a = 1;\n"
      "      1: a = 2;\n"
      "      default: a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_GE(stmt->case_items.size(), 3u);
}

TEST(CaseSyntaxParsing, CaseWithNonblockingAssigns) {
  auto r = Parse(
      "module m;\n"
      "  reg [1:0] sel;\n"
      "  reg [7:0] q;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      2'b00: q <= 8'h00;\n"
      "      2'b01: q <= 8'h01;\n"
      "      2'b10: q <= 8'h10;\n"
      "      default: q <= 8'hFF;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_GE(stmt->case_items.size(), 4u);
  EXPECT_EQ(stmt->case_items[0].body->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(stmt->case_items[1].body->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(stmt->case_items[2].body->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(stmt->case_items[3].body->kind, StmtKind::kNonblockingAssign);
}

TEST(CaseSyntaxParsing, CaseInsideForLoop) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    for (int i = 0; i < 4; i = i + 1) begin\n"
              "      case (mode)\n"
              "        0: data[i] = 0;\n"
              "        1: data[i] = i;\n"
              "        default: data[i] = 8'hFF;\n"
              "      endcase\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}

TEST(CaseSyntaxParsing, CaseInAlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] y;\n"
      "  always_comb begin\n"
      "    case (sel)\n"
      "      2'b00: y = 4'h0;\n"
      "      2'b01: y = 4'h1;\n"
      "      2'b10: y = 4'h2;\n"
      "      default: y = 4'hF;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* block = FirstAlwaysCombStmt(r);
  ASSERT_NE(block, nullptr);
  ASSERT_EQ(block->kind, StmtKind::kBlock);
  ASSERT_GE(block->stmts.size(), 1u);
  auto* stmt = block->stmts[0];
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCase);
  ASSERT_EQ(stmt->case_items.size(), 4u);
  EXPECT_TRUE(stmt->case_items[3].is_default);
}

TEST(CaseSyntaxParsing, CaseItemsWithBlockingAssigns) {
  auto r = Parse(
      "module m;\n"
      "  reg [1:0] sel;\n"
      "  reg [7:0] out;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      2'b00: out = 8'h00;\n"
      "      2'b01: out = 8'h11;\n"
      "      2'b10: out = 8'h22;\n"
      "      default: out = 8'hFF;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_GE(stmt->case_items.size(), 4u);
  EXPECT_EQ(stmt->case_items[0].body->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->case_items[1].body->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->case_items[2].body->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->case_items[3].body->kind, StmtKind::kBlockingAssign);
}

TEST(CaseSyntaxParsing, CaseBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      2'b00: a = 1;\n"
      "      2'b01: a = 2;\n"
      "      default: a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCase);
  ASSERT_GE(stmt->case_items.size(), 3u);
  EXPECT_TRUE(stmt->case_items[2].is_default);
}

TEST(CaseSyntaxParsing, CaseDefaultNoColon) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      1: a = 1;\n"
      "      default a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(HasDefaultCaseItem(stmt));
}

TEST(CaseSyntaxParsing, CaseWithBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      1: begin a = 1; b = 2; end\n"
      "      default: begin a = 0; end\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->case_items[0].body->kind, StmtKind::kBlock);
}

TEST(CaseSyntaxParsing, CaseWithOnlyDefault) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_EQ(stmt->case_items.size(), 1u);
  EXPECT_TRUE(stmt->case_items[0].is_default);
}

TEST(CaseSyntaxParsing, CaseMultipleItemExprs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(sel)\n"
      "      0, 1: x = 8'd10;\n"
      "      2, 3, 4: x = 8'd20;\n"
      "      default: x = 8'd30;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->case_items.size(), 3u);
  EXPECT_EQ(stmt->case_items[0].patterns.size(), 2u);
  EXPECT_EQ(stmt->case_items[1].patterns.size(), 3u);
  EXPECT_TRUE(stmt->case_items[2].is_default);
}

TEST(CaseSyntaxParsing, CaseNoDefault) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) 0: y = 1; 1: y = 2; endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->case_items.size(), 2u);
  EXPECT_FALSE(stmt->case_items[0].is_default);
  EXPECT_FALSE(stmt->case_items[1].is_default);
}

TEST(CaseSyntaxParsing, PlainCaseHasNoQualifier) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      0: x = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kNone);
}

TEST(CaseSyntaxParsing, PlainCaseIsNotInside) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (val)\n"
      "      0: x = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_FALSE(stmt->case_inside);
}

TEST(CaseSyntaxParsing, NestedCaseStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(a)\n"
      "      0: case(b)\n"
      "           0: x = 1;\n"
      "           1: x = 2;\n"
      "         endcase\n"
      "      1: x = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_items[0].body->kind, StmtKind::kCase);
}

TEST(CaseSyntaxParsing, CaseItemNullBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x)\n"
      "      0: ;\n"
      "      1: y = 1;\n"
      "      default: ;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->case_items.size(), 3u);
}

TEST(CaseSyntaxParsing, CaseComplexExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(a + b)\n"
      "      0: y = 1;\n"
      "      1: y = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
}

TEST(CaseSyntaxParsing, ConstExprCaseExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(1)\n"
      "      a: y = 1;\n"
      "      b: y = 2;\n"
      "      default: y = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_NE(stmt->condition, nullptr);
}

TEST(CaseSyntaxParsing, CaseWithNoItemsRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) endcase\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "case statement shall have at least one case item", 3, "12.5"));
}

TEST(CaseSyntaxParsing, CaseDefaultInMiddle) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(sel)\n"
      "      0: x = 1;\n"
      "      default: x = 99;\n"
      "      1: x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->case_items.size(), 3u);
  EXPECT_FALSE(stmt->case_items[0].is_default);
  EXPECT_TRUE(stmt->case_items[1].is_default);
  EXPECT_FALSE(stmt->case_items[2].is_default);
}

TEST(CaseSyntaxParsing, TwoDefaultItemsIsIllegal) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (x)\n"
      "      0: y = 1;\n"
      "      default: y = 2;\n"
      "      default: y = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "case statement shall have at most one 'default' item", 6,
      "12.5"));
}

TEST(CaseSyntaxParsing, SingleDefaultItemAccepted) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (x)\n"
      "      0: y = 1;\n"
      "      default: y = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CaseSyntaxParsing, MissingEndcaseNames12_5) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (x)\n"
      "      0: y = 1;");
  EXPECT_TRUE(ReportedError(r.diags, "expected 'endcase'", 4, "12.5"));
}

constexpr const char* kSecondDefault =
    "case statement shall have at most one 'default' item";

constexpr const char* kCaseHeads[] = {
    "case (x)",          "casez (x)",          "casex (x)",
    "case (x) inside",   "case (x) matches",   "unique case (x)",
    "unique0 casez (x)", "priority casex (x)", "priority case (x) inside"};

constexpr const char* kTwoDefaultItems[] = {
    "      0: y = 1;\n      default: y = 2;\n      default: y = 3;\n",
    "      0: y = 1;\n      default y = 2;\n      default: y = 3;\n",
    "      0: y = 1;\n      default: y = 2;\n      default y = 3;\n",
    "      default: y = 1;\n      0: y = 2;\n      default y = 3;\n"};

struct PlacedCase {
  const char* src;
  int second_default_line;
};

constexpr PlacedCase kTwoDefaultsInPlaces[] = {
    {"module m;\n  function int f(int x);\n    case (x)\n"
     "      default: return 1;\n      default return 2;\n    endcase\n"
     "  endfunction\nendmodule\n",
     5},
    {"module m;\n  task t(int x);\n    casez (x)\n      default: ;\n"
     "      1: ;\n      default: ;\n    endcase\n  endtask\nendmodule\n",
     6},
    {"class C;\n  function void f(int x);\n    case (x) inside\n"
     "      [0:1]: ;\n      default ;\n      default: ;\n    endcase\n"
     "  endfunction\nendclass\n",
     6},
    {"package p;\n  function int f(int x);\n    unique casex (x)\n"
     "      default: return 1;\n      1: return 2;\n      default: return 3;\n"
     "    endcase\n  endfunction\nendpackage\n",
     6},
    {"interface i;\n  int x, y;\n  always_comb\n    priority case (x)\n"
     "      default y = 1;\n      default y = 2;\n    endcase\nendinterface\n",
     6},
    {"program p;\n  int x, y;\n  initial\n    unique0 case (x)\n"
     "      0: y = 0;\n      default: y = 1;\n      default: y = 2;\n"
     "    endcase\nendprogram\n",
     7},
    {"function int f(int x);\n  case (x) matches\n    default: return 1;\n"
     "    default: return 2;\n  endcase\nendfunction\n",
     4}};

std::string CaseInInitial(const char* head, const char* items) {
  return std::string("module m;\n  initial begin\n    ") + head + "\n" + items +
         "    endcase\n  end\nendmodule\n";
}

std::string WithoutLine(const std::string& src, int line) {
  std::string::size_type begin = 0;
  for (int i = 1; i < line; ++i) begin = src.find('\n', begin) + 1;
  return src.substr(0, begin) + src.substr(src.find('\n', begin) + 1);
}

TEST(CaseSyntaxParsing, ASecondDefaultIsReportedInEveryFormOfCase) {
  for (const char* head : kCaseHeads) {
    for (const char* items : kTwoDefaultItems) {
      auto r = Parse(CaseInInitial(head, items));
      EXPECT_TRUE(ReportedError(r.diags, kSecondDefault, 6, "12.5"))
          << head << "\n"
          << items;
    }
  }
}

TEST(CaseSyntaxParsing, OneDefaultIsAcceptedInEveryFormOfCase) {
  for (const char* head : kCaseHeads) {
    for (const char* items : kTwoDefaultItems) {
      auto r = Parse(WithoutLine(CaseInInitial(head, items), 6));
      EXPECT_FALSE(r.has_errors) << head << "\n" << items;
    }
  }
}

TEST(CaseSyntaxParsing, ASecondDefaultIsReportedInEveryPlace) {
  for (const auto& placed : kTwoDefaultsInPlaces) {
    auto r = Parse(placed.src);
    EXPECT_TRUE(ReportedError(r.diags, kSecondDefault,
                              placed.second_default_line, "12.5"))
        << placed.src;
  }
}

TEST(CaseSyntaxParsing, OneDefaultIsAcceptedInEveryPlace) {
  for (const auto& placed : kTwoDefaultsInPlaces) {
    auto r = Parse(WithoutLine(placed.src, placed.second_default_line));
    EXPECT_FALSE(r.has_errors) << placed.src;
  }
}

}  // namespace
