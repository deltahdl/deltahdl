#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct LetParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static LetParseResult Parse(const std::string &src) {
  LetParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// Helper: find the first kLetDecl item in the first module.
static ModuleItem *FirstLetDecl(LetParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kLetDecl)
      return item;
  }
  return nullptr;
}

// ==========================================================================
// §11.12: Let declaration parsing
// ==========================================================================

TEST(ParserLet, DeclNoArgsParse) {
  auto r = Parse("module t;\n"
                 "  let addr = top.block1.base + top.block1.displ;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  EXPECT_EQ(let_item->name, "addr");
}

TEST(ParserLet, DeclNoArgsBody) {
  auto r = Parse("module t;\n"
                 "  let addr = top.block1.base + top.block1.displ;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  EXPECT_TRUE(let_item->func_args.empty());
  ASSERT_NE(let_item->init_expr, nullptr);
}

TEST(ParserLet, DeclWithArgsParse) {
  auto r = Parse("module t;\n"
                 "  let op(x, y, z) = |((x | y) & z);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  EXPECT_EQ(let_item->name, "op");
}

TEST(ParserLet, DeclWithArgsNames) {
  auto r = Parse("module t;\n"
                 "  let op(x, y, z) = |((x | y) & z);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  ASSERT_EQ(let_item->func_args.size(), 3u);
  const char *const kExpected[] = {"x", "y", "z"};
  for (size_t i = 0; i < 3; i++) {
    EXPECT_EQ(let_item->func_args[i].name, kExpected[i]);
  }
  ASSERT_NE(let_item->init_expr, nullptr);
}

TEST(ParserLet, DeclWithDefaultsParse) {
  auto r = Parse("module t;\n"
                 "  let at_least_two(sig, rst = 1'b0) = rst || sig;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  EXPECT_EQ(let_item->name, "at_least_two");
  ASSERT_EQ(let_item->func_args.size(), 2u);
}

TEST(ParserLet, DeclWithDefaultsArgs) {
  auto r = Parse("module t;\n"
                 "  let at_least_two(sig, rst = 1'b0) = rst || sig;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  EXPECT_EQ(let_item->func_args[0].name, "sig");
  EXPECT_EQ(let_item->func_args[0].default_value, nullptr);
  EXPECT_EQ(let_item->func_args[1].name, "rst");
  EXPECT_NE(let_item->func_args[1].default_value, nullptr);
}

TEST(ParserLet, DeclTypedArgsParse) {
  auto r = Parse("module t;\n"
                 "  let mult(logic [15:0] x, logic [15:0] y) = x * y;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  EXPECT_EQ(let_item->name, "mult");
}

TEST(ParserLet, DeclTypedArgsNames) {
  auto r = Parse("module t;\n"
                 "  let mult(logic [15:0] x, logic [15:0] y) = x * y;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  ASSERT_EQ(let_item->func_args.size(), 2u);
  EXPECT_EQ(let_item->func_args[0].name, "x");
  EXPECT_EQ(let_item->func_args[1].name, "y");
}

TEST(ParserLet, DeclUntypedArg) {
  auto r = Parse("module t;\n"
                 "  let check(untyped a) = a;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  ASSERT_EQ(let_item->func_args.size(), 1u);
  EXPECT_EQ(let_item->func_args[0].name, "a");
}

TEST(ParserLet, DeclEmptyParens) {
  auto r = Parse("module t;\n"
                 "  let empty_let() = 42;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  EXPECT_EQ(let_item->name, "empty_let");
  EXPECT_TRUE(let_item->func_args.empty());
}

// ==========================================================================
// §11.12: Let instantiation parsing (calls parsed as kCall expressions)
// ==========================================================================

TEST(ParserLet, InstantiationParsed) {
  // Let calls look syntactically like function calls — verify parsing.
  auto r = Parse("module t;\n"
                 "  let op(x, y) = x + y;\n"
                 "  initial begin\n"
                 "    int z;\n"
                 "    z = op(3, 4);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserLet, InstantiationNamedArgs) {
  auto r = Parse("module t;\n"
                 "  let valid_arb(request, valid, override) = "
                 "|(request & valid) || override;\n"
                 "  initial begin\n"
                 "    logic result;\n"
                 "    result = valid_arb(.request(2'b11), .valid(2'b10),"
                 " .override(1'b0));\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserLet, InstantiationDefaultArgs) {
  auto r = Parse("module t;\n"
                 "  let at_least_two(sig, rst = 1'b0) = rst || sig;\n"
                 "  initial begin\n"
                 "    logic [15:0] sig1;\n"
                 "    logic q;\n"
                 "    q = at_least_two(sig1);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ==========================================================================
// §11.12: Let in package scope
// ==========================================================================

TEST(ParserLet, DeclInPackage) {
  auto r = Parse("package pkg;\n"
                 "  let my_op(x, y) = x & y;\n"
                 "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
