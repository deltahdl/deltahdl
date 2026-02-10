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

TEST(ParserSection6, WireDeclaration) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kWire);
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

TEST(ParserSection6, ClassVarDecl) {
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

// =========================================================================
// §6.22: Type compatibility
// =========================================================================

TEST(ParserSection6, TypesMatchBuiltin) {
  // Two identical built-in types should match.
  DataType a;
  a.kind = DataTypeKind::kInt;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesMatchDifferent) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  DataType b;
  b.kind = DataTypeKind::kReal;
  EXPECT_FALSE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesMatchSignedness) {
  // Same kind but different signedness should not match.
  DataType a;
  a.kind = DataTypeKind::kLogic;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  b.is_signed = false;
  EXPECT_FALSE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesEquivalentPackedSameWidth) {
  // bit [7:0] and logic [7:0] are equivalent (same width, same signing).
  DataType a;
  a.kind = DataTypeKind::kBit;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  // Both default unsigned, same base width (1 bit without dims).
  EXPECT_TRUE(TypesEquivalent(a, b));
}

// =========================================================================
// §6.23: Type operator
// =========================================================================

TEST(ParserSection6, TypeOperatorExpr) {
  auto r = Parse(
      "module t;\n"
      "  initial x = type(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTypeRef);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->lhs->text, "y");
}

TEST(ParserSection6, TypeOperatorInDataType) {
  auto r = Parse(
      "module t;\n"
      "  parameter type T = type(int);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  // The init_expr should be a type reference.
  ASSERT_NE(item->init_expr, nullptr);
  EXPECT_EQ(item->init_expr->kind, ExprKind::kTypeRef);
}

// =========================================================================
// §6.25: Parameterized data types
// =========================================================================

TEST(ParserSection6, ScopeResolutionType) {
  auto r = Parse(
      "module t;\n"
      "  import pkg::mytype;\n"
      "  pkg::mytype x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  // Find the variable declaration.
  auto& items = r.cu->modules[0]->items;
  ModuleItem* var_item = nullptr;
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kVarDecl && it->name == "x") {
      var_item = it;
      break;
    }
  }
  ASSERT_NE(var_item, nullptr);
  EXPECT_EQ(var_item->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(var_item->data_type.scope_name, "pkg");
  EXPECT_EQ(var_item->data_type.type_name, "mytype");
}

// =========================================================================
// §6 — TDD tests for remaining sv-tests
// =========================================================================

// Helper: check parse succeeds with no errors.
static bool ParseOk6(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

// Step 1a: string type in block-level declarations (fixes 6.19.5.6)
TEST(ParserSection6, BlockVarDecl_StringType) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    string s;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->var_decl_type.kind, DataTypeKind::kString);
  EXPECT_EQ(stmt->var_name, "s");
}

// Step 1b: implicit port types (fixes 6.10)
TEST(ParserSection6, ParsePortDecl_ImplicitType) {
  auto r = Parse("module m(input [3:0] a, output [7:0] b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].name, "a");
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(ports[1].name, "b");
  EXPECT_EQ(ports[1].data_type.kind, DataTypeKind::kLogic);
}

// Step 1c: localparam implicit type (fixes 6.20.4)
TEST(ParserSection6, ParamDecl_ImplicitType) {
  EXPECT_TRUE(
      ParseOk6("module t;\n"
               "  localparam [10:0] p = 1 << 5;\n"
               "  localparam logic [10:0] q = 1 << 5;\n"
               "endmodule\n"));
}

// Step 1c: parameter unpacked dims (fixes 6.20.2)
TEST(ParserSection6, ParamDecl_UnpackedDims) {
  EXPECT_TRUE(
      ParseOk6("module t;\n"
               "  parameter logic [31:0] p [3:0] = '{1, 2, 3, 4};\n"
               "endmodule\n"));
}

// Step 1d: type parameter in module header (fixes 6.20.3)
TEST(ParserSection6, TypeParamPort) {
  EXPECT_TRUE(ParseOk6("module top #(type T = real); endmodule\n"));
}

// Step 1d: localparam type declaration (fixes 6.23-localparam_type_decl)
TEST(ParserSection6, LocalparamTypeDecl) {
  EXPECT_TRUE(
      ParseOk6("module t;\n"
               "  localparam type testtype = logic;\n"
               "  testtype x;\n"
               "endmodule\n"));
}

// Step 2a: user-defined type cast (fixes 6.19.4-cast)
TEST(ParserSection6, TypeCast_UserDefined) {
  EXPECT_TRUE(
      ParseOk6("module t;\n"
               "  typedef enum {a, b, c, d} e;\n"
               "  initial begin\n"
               "    e val;\n"
               "    val = a;\n"
               "    val = e'(val + 1);\n"
               "  end\n"
               "endmodule\n"));
}

// Step 2b: interconnect (fixes 6.6.8)
TEST(ParserSection6, Interconnect_Basic) {
  EXPECT_TRUE(
      ParseOk6("module t;\n"
               "  interconnect bus;\n"
               "endmodule\n"));
}

// Step 3a: var type(expr) declarations (fixes 6.23-type_op)
TEST(ParserSection6, VarTypeOp_Basic) {
  EXPECT_TRUE(
      ParseOk6("module t;\n"
               "  real a = 4.76;\n"
               "  real b = 0.74;\n"
               "  var type(a+b) c;\n"
               "endmodule\n"));
}

// Step 3b: type(data_type) in expressions (fixes 6.23-type_op_compare)
TEST(ParserSection6, TypeRef_DataType) {
  EXPECT_TRUE(
      ParseOk6("module top #(parameter type T = type(logic[11:0]))\n"
               "  ();\n"
               "  initial begin\n"
               "    case (type(T))\n"
               "      type(logic[11:0]) : ;\n"
               "      default : $stop;\n"
               "    endcase\n"
               "    if (type(T) == type(logic[12:0])) $stop;\n"
               "    if (type(T) != type(logic[11:0])) $stop;\n"
               "    if (type(T) === type(logic[12:0])) $stop;\n"
               "    if (type(T) !== type(logic[11:0])) $stop;\n"
               "    $finish;\n"
               "  end\n"
               "endmodule\n"));
}
