#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- §5.12 Attributes ---

struct ParseResult512 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult512 Parse(const std::string &src) {
  ParseResult512 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt *FirstInitialStmt(ParseResult512 &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem *FirstItem(ParseResult512 &r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto &items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

static void VerifyAttrNames(const ModuleItem *item,
                            const std::string expected_names[], size_t count) {
  ASSERT_EQ(item->attrs.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(item->attrs[i].name, expected_names[i]) << "attr " << i;
  }
}

// From test_parser_clause_05.cpp

TEST(ParserCh512, AttributeOnModuleItem) {
  auto r = Parse(
      "module t;\n"
      "  (* full_case *)\n"
      "  logic [7:0] x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->attrs.size(), 1u);
  EXPECT_EQ(item->attrs[0].name, "full_case");
  EXPECT_EQ(item->attrs[0].value, nullptr);
}

TEST(ParserCh512, AttributeWithValue_Names) {
  auto r = Parse(
      "module t;\n"
      "  (* synthesis, optimize_power = 1 *)\n"
      "  logic y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  std::string expected_names[] = {"synthesis", "optimize_power"};
  VerifyAttrNames(r.cu->modules[0]->items[0], expected_names,
                  std::size(expected_names));
}

TEST(ParserCh512, AttributeWithValue_Values) {
  auto r = Parse(
      "module t;\n"
      "  (* synthesis, optimize_power = 1 *)\n"
      "  logic y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->attrs.size(), 2u);
  EXPECT_EQ(item->attrs[0].value, nullptr);
  ASSERT_NE(item->attrs[1].value, nullptr);
}

TEST(ParserCh512, TopLevel_AttributeBeforeModule) {
  EXPECT_TRUE(ParseOk("(* optimize_power *) module m; endmodule"));
}

TEST(ParserCh512, TopLevel_TrailingSemicolonAfterEndmodule) {
  EXPECT_TRUE(ParseOk("module m; endmodule;"));
}

TEST(ParserCh512, Expr_AttributeOnOperator) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, c;\n"
              "  assign a = b + (* mode = \"cla\" *) c;\n"
              "endmodule"));
}

TEST(ParserCh512, Expr_AttributeOnTernary) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, c, d;\n"
              "  assign a = b ? (* no_glitch *) c : d;\n"
              "endmodule"));
}

TEST(ParserCh512, PostfixFunctionAttribute) {
  // §5.12 Example 7: a = add (* mode = "cla" *) (b, c);
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic a, b, c;\n"
              "  initial a = add (* mode = \"cla\" *) (b, c);\n"
              "endmodule\n"));
}

TEST(ParserCh512, PostfixFunctionAttribute_NoArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic a;\n"
              "  initial a = foo (* bar *) ();\n"
              "endmodule\n"));
}

TEST(ParserCh512, NestedAttribute_Error) {
  // §5.12: Nesting of attribute instances is disallowed.
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  (* foo = 1 + (* bar *) 2 *) logic x;\n"
              "endmodule\n"));
}

TEST(ParserCh512, AttributeValue_NoNesting_Ok) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  (* foo = 1 + 2 *) logic x;\n"
              "endmodule\n"));
}

// From test_parser_clause_05b.cpp

TEST(ParserCh512, Attribute_OnCaseStatement) {
  // Section 5.12 Example 1: full_case, parallel_case on a case statement.
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* full_case, parallel_case *)\n"
      "    case (a)\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_EQ(stmt->attrs.size(), 2u);
  EXPECT_EQ(stmt->attrs[0].name, "full_case");
  EXPECT_EQ(stmt->attrs[1].name, "parallel_case");
}

TEST(ParserCh512, Attribute_MultipleInstances) {
  // Multiple separate attribute instances before the same item.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  (* full_case=1 *)\n"
              "  (* parallel_case=1 *)\n"
              "  logic x;\n"
              "endmodule"));
}

TEST(ParserCh512, Attribute_OnModuleInstantiation) {
  // Section 5.12 Example 4: attribute on a module instantiation.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  (* optimize_power=0 *)\n"
              "  sub u1(.a(x));\n"
              "endmodule"));
}

TEST(ParserCh512, Attribute_OnIfStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* synthesis_off *)\n"
      "    if (a) x = 1;\n"
      "  end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_EQ(stmt->attrs.size(), 1u);
  EXPECT_EQ(stmt->attrs[0].name, "synthesis_off");
}

TEST(ParserCh512, Attribute_OnForLoop) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    (* unroll *)\n"
              "    for (int i = 0; i < 4; i++) x = i;\n"
              "  end\n"
              "endmodule"));
}

TEST(ParserCh512, Attribute_OnAssignment) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    (* mark *) x = 1;\n"
              "  end\n"
              "endmodule"));
}

TEST(ParserCh512, Attribute_OnPortConnection) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sub u1(.a(x), (* no_connect *) .b(y));\n"
              "endmodule"));
}

TEST(ParserCh512, Attribute_OnContAssign) {
  // Attribute on a continuous assignment statement.
  auto r = Parse(
      "module m;\n"
      "  logic a, b;\n"
      "  (* synthesis_on *)\n"
      "  assign a = b;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
  auto *item = r.cu->modules[0]->items[2];
  EXPECT_EQ(item->kind, ModuleItemKind::kContAssign);
  ASSERT_EQ(item->attrs.size(), 1u);
  EXPECT_EQ(item->attrs[0].name, "synthesis_on");
}

TEST(ParserCh512, AttributeValue_ConstExpr) {
  // The attribute value can be an arbitrary constant expression.
  auto r = Parse(
      "module m;\n"
      "  (* depth = 3 + 1 *)\n"
      "  logic [7:0] mem;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->attrs.size(), 1u);
  EXPECT_EQ(item->attrs[0].name, "depth");
  ASSERT_NE(item->attrs[0].value, nullptr);
  EXPECT_EQ(item->attrs[0].value->kind, ExprKind::kBinary);
}

TEST(ParserCh512, AttributeValue_String) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  (* tool_purpose = \"synthesis\" *)\n"
              "  logic x;\n"
              "endmodule"));
}

TEST(ParserCh512, Attribute_MultipleSeparateInstances) {
  // Multiple attribute instances are merged.
  auto r = Parse(
      "module m;\n"
      "  (* first *)\n"
      "  (* second *)\n"
      "  logic x;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->attrs.size(), 2u);
  EXPECT_EQ(item->attrs[0].name, "first");
  EXPECT_EQ(item->attrs[1].name, "second");
}
