#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult611 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult611 Parse(const std::string &src) {
  ParseResult611 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
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

static ModuleItem *FirstItem(ParseResult611 &r) {
  if (!r.cu || r.cu->modules.empty())
    return nullptr;
  auto &items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

// =============================================================================
// LRM section 6.11 -- Integer data types
// =============================================================================

// --- 2-state integer types ---

TEST(ParserSection6, IntegerTypeByteDecl) {
  auto r = Parse("module m;\n"
                 "  byte b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(item->name, "b");
}

TEST(ParserSection6, IntegerTypeShortintDecl) {
  auto r = Parse("module m;\n"
                 "  shortint si;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortint);
  EXPECT_EQ(item->name, "si");
}

TEST(ParserSection6, IntegerTypeIntDecl) {
  auto r = Parse("module m;\n"
                 "  int i;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->name, "i");
}

TEST(ParserSection6, IntegerTypeLongintDecl) {
  auto r = Parse("module m;\n"
                 "  longint li;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLongint);
  EXPECT_EQ(item->name, "li");
}

// --- 4-state integer types ---

TEST(ParserSection6, IntegerTypeIntegerDecl) {
  // 'integer' is 4-state, 32-bit signed (LRM 6.11)
  auto r = Parse("module m;\n"
                 "  integer x;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInteger);
  EXPECT_EQ(item->name, "x");
}

TEST(ParserSection6, IntegerTypeLogicDecl) {
  // 'logic' is 4-state, user-defined width, unsigned (LRM 6.11)
  auto r = Parse("module m;\n"
                 "  logic [15:0] data;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->name, "data");
}

TEST(ParserSection6, IntegerTypeRegDecl) {
  // 'reg' is identical to 'logic' (LRM 6.11.2)
  auto r = Parse("module m;\n"
                 "  reg [7:0] r;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_EQ(item->name, "r");
}

TEST(ParserSection6, IntegerTypeBitDecl) {
  // 'bit' is 2-state, user-defined width, unsigned (LRM 6.11)
  auto r = Parse("module m;\n"
                 "  bit [31:0] val;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_EQ(item->name, "val");
}

TEST(ParserSection6, IntegerTypeTimeDecl) {
  // 'time' is 4-state, 64-bit unsigned (LRM 6.11)
  auto r = Parse("module m;\n"
                 "  time t;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTime);
  EXPECT_EQ(item->name, "t");
}

// --- Signed and unsigned qualifiers (LRM 6.11.3) ---

TEST(ParserSection6, IntUnsignedDecl) {
  // int unsigned -- explicit unsigned override (LRM 6.11.3)
  auto r = Parse("module m;\n"
                 "  int unsigned ui;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_FALSE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "ui");
}

TEST(ParserSection6, IntSignedDecl) {
  // int signed -- explicit signed (default for int)
  auto r = Parse("module m;\n"
                 "  int signed si;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_TRUE(item->data_type.is_signed);
}

TEST(ParserSection6, LogicSignedDecl) {
  // logic signed -- unsigned by default, override to signed
  auto r = Parse("module m;\n"
                 "  logic signed [7:0] sv;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(item->data_type.is_signed);
}

TEST(ParserSection6, RegUnsignedDecl) {
  auto r = Parse("module m;\n"
                 "  reg unsigned [3:0] ru;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_FALSE(item->data_type.is_signed);
}

// --- Multiple integer declarations ---

TEST(ParserSection6, MultipleIntDeclsCommaSeparated) {
  auto r = Parse("module m;\n"
                 "  int a, b, c;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
}

TEST(ParserSection6, IntWithInitializer) {
  auto r = Parse("module m;\n"
                 "  int x = 42;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserSection6, All2StateTypes) {
  // Verify all 2-state types parse correctly together
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  byte b;\n"
                      "  shortint si;\n"
                      "  int i;\n"
                      "  longint li;\n"
                      "  bit bv;\n"
                      "endmodule\n"));
}

TEST(ParserSection6, All4StateTypes) {
  // Verify all 4-state types parse correctly together
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  logic l;\n"
                      "  reg r;\n"
                      "  integer ig;\n"
                      "  time t;\n"
                      "endmodule\n"));
}

// --- Mixed types in one module ---

TEST(ParserSection6, MixedIntegerRealStringTypes) {
  // All major type families coexisting
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  int i;\n"
                      "  real r;\n"
                      "  shortreal sr;\n"
                      "  string s;\n"
                      "  byte b;\n"
                      "  logic [7:0] l;\n"
                      "  integer ig;\n"
                      "  realtime rt;\n"
                      "endmodule\n"));
}

TEST(ParserSection6, IntegerTypesInProcedural) {
  // All integer types declared inside initial block
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  initial begin\n"
                      "    byte b;\n"
                      "    shortint si;\n"
                      "    int i;\n"
                      "    longint li;\n"
                      "    integer ig;\n"
                      "    bit bv;\n"
                      "    logic l;\n"
                      "    reg r;\n"
                      "    time t;\n"
                      "  end\n"
                      "endmodule\n"));
}

TEST(ParserSection6, RealTypesInProcedural) {
  // All real types declared inside initial block
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  initial begin\n"
                      "    real r;\n"
                      "    shortreal sr;\n"
                      "    realtime rt;\n"
                      "  end\n"
                      "endmodule\n"));
}

TEST(ParserSection6, StringInProcedural) {
  // String declared inside procedural block
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  initial begin\n"
                      "    string s = \"test\";\n"
                      "    $display(s);\n"
                      "  end\n"
                      "endmodule\n"));
}
