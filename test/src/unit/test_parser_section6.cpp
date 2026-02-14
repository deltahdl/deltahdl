#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/type_eval.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult6 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult6 Parse(const std::string& src) {
  ParseResult6 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static ModuleItem* FirstItem(ParseResult6& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

static Stmt* FirstInitialStmt(ParseResult6& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
}

// =========================================================================
// §6.5-6.7: Net declarations
// =========================================================================

TEST(ParserSection6, WireDeclaration_Kind) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kWire);
}

TEST(ParserSection6, WireDeclaration_Props) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "w");
}

TEST(ParserSection6, TriDeclaration) {
  auto r = Parse(
      "module t;\n"
      "  tri [3:0] t1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
}

// =========================================================================
// §6.8: Variable declarations
// =========================================================================

TEST(ParserSection6, LogicVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  logic [15:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->name, "data");
}

TEST(ParserSection6, IntVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  int count;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->name, "count");
}

TEST(ParserSection6, ByteVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  byte b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kByte);
}

TEST(ParserSection6, LongintVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  longint li;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLongint);
}

// =========================================================================
// §6.9: Vector declarations
// =========================================================================

TEST(ParserSection6, SignedVector) {
  auto r = Parse(
      "module t;\n"
      "  logic signed [7:0] sv;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(item->data_type.is_signed);
}

// =========================================================================
// §6.11.3: Default signedness per Table 6-8
// =========================================================================

TEST(ParserSection6, IntDefaultSigned) {
  auto r = Parse(
      "module t;\n"
      "  int x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_TRUE(item->data_type.is_signed) << "int is signed by default";
}

TEST(ParserSection6, IntExplicitUnsigned) {
  auto r = Parse(
      "module t;\n"
      "  int unsigned x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_FALSE(item->data_type.is_signed) << "int unsigned is unsigned";
}

TEST(ParserSection6, ByteDefaultSigned) {
  auto r = Parse(
      "module t;\n"
      "  byte b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kByte);
  EXPECT_TRUE(item->data_type.is_signed) << "byte is signed by default";
}

TEST(ParserSection6, ShortintDefaultSigned) {
  auto r = Parse(
      "module t;\n"
      "  shortint s;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortint);
  EXPECT_TRUE(item->data_type.is_signed) << "shortint is signed by default";
}

TEST(ParserSection6, LongintDefaultSigned) {
  auto r = Parse(
      "module t;\n"
      "  longint l;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLongint);
  EXPECT_TRUE(item->data_type.is_signed) << "longint is signed by default";
}

TEST(ParserSection6, IntegerDefaultSigned) {
  auto r = Parse(
      "module t;\n"
      "  integer i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInteger);
  EXPECT_TRUE(item->data_type.is_signed) << "integer is signed by default";
}

TEST(ParserSection6, TimeDefaultUnsigned) {
  auto r = Parse(
      "module t;\n"
      "  time t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTime);
  EXPECT_FALSE(item->data_type.is_signed) << "time is unsigned by default";
}

TEST(ParserSection6, LogicDefaultUnsigned) {
  auto r = Parse(
      "module t;\n"
      "  logic l;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_FALSE(item->data_type.is_signed) << "logic is unsigned by default";
}

TEST(ParserSection6, BitDefaultUnsigned) {
  auto r = Parse(
      "module t;\n"
      "  bit b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_FALSE(item->data_type.is_signed) << "bit is unsigned by default";
}

TEST(ParserSection6, RegDefaultUnsigned) {
  auto r = Parse(
      "module t;\n"
      "  reg r;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_FALSE(item->data_type.is_signed) << "reg is unsigned by default";
}

// =========================================================================
// §6.12: Real, shortreal, and realtime data types
// =========================================================================

TEST(ParserSection6, RealVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  real r;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReal);
}

TEST(ParserSection6, ShortrealVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  shortreal sr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortreal);
}

TEST(ParserSection6, RealtimeVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  realtime rt;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kRealtime);
}

// =========================================================================
// §6.13: Void data type
// =========================================================================

TEST(ParserSection6, VoidFunctionReturn) {
  auto r = Parse(
      "module t;\n"
      "  function void do_nothing();\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

// =========================================================================
// §6.14: Chandle data type
// =========================================================================

TEST(ParserSection6, ChandleVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  chandle ch;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kChandle);
  EXPECT_EQ(item->name, "ch");
}

// =========================================================================
// §6.17: Event data type
// =========================================================================

TEST(ParserSection6, EventVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  event e;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEvent);
}

// =========================================================================
// §6.18: User-defined types (typedef)
// =========================================================================

TEST(ParserSection6, TypedefInt) {
  auto r = Parse(
      "module t;\n"
      "  typedef int myint;\n"
      "  myint x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(item->data_type.type_name, "myint");
}

// =========================================================================
// §6.19: Enumerations
// =========================================================================

TEST(ParserSection6, EnumBasic) {
  auto r = Parse(
      "module t;\n"
      "  typedef enum { RED, GREEN, BLUE } color_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kEnum);
  EXPECT_EQ(item->typedef_type.enum_members.size(), 3u);
}

// =========================================================================
// §6.20: Constants
// =========================================================================

TEST(ParserSection6, ConstVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  const logic [7:0] MAX = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(item->data_type.is_const);
}

TEST(ParserSection6, ConstVarDecl_NameAndInit) {
  auto r = Parse(
      "module t;\n"
      "  const logic [7:0] MAX = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "MAX");
  ASSERT_NE(item->init_expr, nullptr);
}

TEST(ParserSection6, ConstIntDecl) {
  auto r = Parse(
      "module t;\n"
      "  const int LIMIT = 100;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_TRUE(item->data_type.is_const);
}

// =========================================================================
// §6.21: Scope and lifetime
// =========================================================================

TEST(ParserSection6, AutomaticVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  function automatic int get_val();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_automatic);
}

TEST(ParserSection6, StaticFunction) {
  auto r = Parse(
      "module t;\n"
      "  function static int counter();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_static);
}

// =========================================================================
// §6.24: Casting
// =========================================================================

TEST(ParserSection6, IntCast) {
  auto r = Parse(
      "module t;\n"
      "  initial x = int'(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
}

TEST(ParserSection6, IntCast_Details) {
  auto r = Parse(
      "module t;\n"
      "  initial x = int'(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->text, "int");
  ASSERT_NE(rhs->lhs, nullptr);
}

TEST(ParserSection6, SignedCast) {
  auto r = Parse(
      "module t;\n"
      "  initial x = signed'(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
  EXPECT_EQ(rhs->text, "signed");
}

TEST(ParserSection6, ConstCast) {
  auto r = Parse(
      "module t;\n"
      "  initial x = const'(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
  EXPECT_EQ(rhs->text, "const");
}

// =========================================================================
// §6.15: Class
// =========================================================================

TEST(ParserSection6, ClassVarDecl_ClassParsed) {
  // Class declared at top-level, then used as a type inside a module.
  auto r = Parse(
      "class MyClass;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  MyClass obj;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->classes.empty());
  EXPECT_EQ(r.cu->classes[0]->name, "MyClass");
  ASSERT_FALSE(r.cu->modules.empty());
}

TEST(ParserSection6, ClassVarDecl_VarType) {
  auto r = Parse(
      "class MyClass;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  MyClass obj;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  auto& items = r.cu->modules[0]->items;
  ModuleItem* var_item = nullptr;
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kVarDecl && it->name == "obj") {
      var_item = it;
      break;
    }
  }
  ASSERT_NE(var_item, nullptr);
  EXPECT_EQ(var_item->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(var_item->data_type.type_name, "MyClass");
}
