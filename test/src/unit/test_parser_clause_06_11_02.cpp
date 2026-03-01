// §6.11.2: 2-state (two-value) and 4-state (four-value) data types

#include "fixture_parser.h"

using namespace delta;

struct ParseResult6j {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult6j Parse(const std::string& src) {
  ParseResult6j result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstItem(ParseResult6j& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

namespace {

// 3. Reg variable declaration produces kVarDecl.
TEST(ParserSection6, Sec6_5_RegVarDeclKind) {
  auto r = Parse(
      "module t;\n"
      "  reg r;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_FALSE(item->data_type.is_net);
}

struct ParseResult616 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult616 Parse(const std::string& src) {
  ParseResult616 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstItem(ParseResult616& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

TEST(ParserSection6, IntegerTypeShortintDecl) {
  auto r = Parse(
      "module m;\n"
      "  shortint si;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortint);
  EXPECT_EQ(item->name, "si");
}

TEST(ParserSection6, IntegerTypeIntDecl) {
  auto r = Parse(
      "module m;\n"
      "  int i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->name, "i");
}

TEST(ParserSection6, IntegerTypeLongintDecl) {
  auto r = Parse(
      "module m;\n"
      "  longint li;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLongint);
  EXPECT_EQ(item->name, "li");
}

// --- 4-state integer types ---
TEST(ParserSection6, IntegerTypeIntegerDecl) {
  // 'integer' is 4-state, 32-bit signed (LRM 6.11)
  auto r = Parse(
      "module m;\n"
      "  integer x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInteger);
  EXPECT_EQ(item->name, "x");
}

TEST(ParserSection6, IntegerTypeLogicDecl) {
  // 'logic' is 4-state, user-defined width, unsigned (LRM 6.11)
  auto r = Parse(
      "module m;\n"
      "  logic [15:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->name, "data");
}

TEST(ParserSection6, IntegerTypeRegDecl) {
  // 'reg' is identical to 'logic' (LRM 6.11.2)
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] r;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_EQ(item->name, "r");
}

TEST(ParserSection6, IntegerTypeBitDecl) {
  // 'bit' is 2-state, user-defined width, unsigned (LRM 6.11)
  auto r = Parse(
      "module m;\n"
      "  bit [31:0] val;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_EQ(item->name, "val");
}

struct ParseResult6h {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult6h Parse(const std::string& src) {
  ParseResult6h result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstItem(ParseResult6h& r) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.empty())
    return nullptr;
  return r.cu->modules[0]->items[0];
}

// 14b. shortint with negative initializer.
TEST(ParserSection6, Sec6_11_ShortintWithNegativeInit) {
  auto r = Parse(
      "module t;\n"
      "  shortint s = -1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortint);
  ASSERT_NE(item->init_expr, nullptr);
}

// 16b. shortint as function return type.
TEST(ParserSection6, Sec6_11_ShortintFunctionReturnType) {
  auto r = Parse(
      "module t;\n"
      "  function shortint get_short();\n"
      "    return 16'd100;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kShortint);
}

TEST(ParserSection6, All2StateTypes) {
  // Verify all 2-state types parse correctly together
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  byte b;\n"
              "  shortint si;\n"
              "  int i;\n"
              "  longint li;\n"
              "  bit bv;\n"
              "endmodule\n"));
}

TEST(ParserSection6, All4StateTypes) {
  // Verify all 4-state types parse correctly together
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic l;\n"
              "  reg r;\n"
              "  integer ig;\n"
              "  time t;\n"
              "endmodule\n"));
}

}  // namespace
