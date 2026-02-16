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

TEST(ParserSection6, UnsignedVector) {
  auto r = Parse(
      "module t;\n"
      "  logic unsigned [15:0] uv;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_FALSE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "uv");
}

TEST(ParserSection6, VectorWithMultipleDims) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] mem [0:255];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->name, "mem");
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
// §6.24.1 -- Static casting (additional tests)
// =========================================================================

// =========================================================================
// §6.24.2 -- Dynamic casting ($cast)
// =========================================================================

TEST(ParserSection6, DynamicCastCall) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    $cast(d, b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$cast");
}

TEST(ParserSection6, DynamicCastInCondition) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if ($cast(d, b))\n"
      "      $display(\"cast ok\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
}

TEST(ParserSection6, DynamicCastAssignResult) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    int ok;\n"
      "    ok = $cast(d, b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// =========================================================================
// §6.24.3 -- Bit-stream casting
// =========================================================================

TEST(ParserSection6, BitStreamCastToType) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { logic [3:0] a; logic [3:0] b; } pair_t;\n"
      "  initial begin\n"
      "    pair_t p;\n"
      "    p = pair_t'(8'hAB);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection6, BitStreamCastFromStruct) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { logic [3:0] a; logic [3:0] b; } pair_t;\n"
      "  initial begin\n"
      "    pair_t p;\n"
      "    logic [7:0] flat;\n"
      "    flat = logic [7:0]'(p);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection6, BitStreamCastStreaming) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    byte a;\n"
      "    int b;\n"
      "    b = int'({<< byte {a}});\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
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

// =========================================================================
// §6.5: Nets and variables
// =========================================================================

TEST(ParserSection6, NetsCantBeProcAssigned) {
  // Nets are driven by continuous assignments, variables by procedural.
  // This test verifies both constructs parse correctly.
  auto r = Parse(
      "module t;\n"
      "  wire a;\n"
      "  assign a = 1'b1;\n"
      "  logic b;\n"
      "  initial b = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_GE(r.cu->modules[0]->items.size(), 4u);
}

TEST(ParserSection6, VariableContinuousAssign) {
  // §6.5: Variables can be written by one continuous assignment.
  auto r = Parse(
      "module t;\n"
      "  logic vw;\n"
      "  assign vw = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  bool found_ca = false;
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kContAssign) found_ca = true;
  }
  EXPECT_TRUE(found_ca);
}

TEST(ParserSection6, NetWithImplicitContAssign) {
  // §6.5: Unlike nets, a variable cannot have an implicit continuous
  // assignment. Wire with inline assignment is a net continuous assign.
  auto r = Parse(
      "module t;\n"
      "  wire w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserSection6, VariableInitialization) {
  // §6.5: Assignment as part of variable declaration is an initialization,
  // not a continuous assignment.
  auto r = Parse(
      "module t;\n"
      "  logic v = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserSection6, RealVariableContinuousAssign) {
  auto r = Parse(
      "module t;\n"
      "  real circ;\n"
      "  assign circ = 2.0 * 3.14;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  bool found_ca = false;
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kContAssign) found_ca = true;
  }
  EXPECT_TRUE(found_ca);
}

// =========================================================================
// §6.6.7: User-defined nettypes
// =========================================================================

TEST(ParserSection6, NettypeDeclBasic) {
  // nettype data_type nettype_identifier ;
  auto r = Parse(
      "module t;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  nettype T wT;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  ModuleItem* nt = nullptr;
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kNettypeDecl) {
      nt = it;
      break;
    }
  }
  ASSERT_NE(nt, nullptr);
  EXPECT_EQ(nt->name, "wT");
}

TEST(ParserSection6, NettypeDeclWithResolveFunc) {
  // nettype data_type nettype_identifier with tf_identifier ;
  auto r = Parse(
      "module t;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  nettype T wTsum with Tsum;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  ModuleItem* nt = nullptr;
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kNettypeDecl) {
      nt = it;
      break;
    }
  }
  ASSERT_NE(nt, nullptr);
  EXPECT_EQ(nt->name, "wTsum");
  EXPECT_EQ(nt->nettype_resolve_func, "Tsum");
}

TEST(ParserSection6, NettypeDeclAlias) {
  // nettype nettype_identifier nettype_identifier ;  (alias form)
  auto r = Parse(
      "module t;\n"
      "  typedef real TR[5];\n"
      "  nettype TR wTR;\n"
      "  nettype wTR nettypeid2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  int nettype_count = 0;
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kNettypeDecl) nettype_count++;
  }
  EXPECT_GE(nettype_count, 2);
}

// =========================================================================
// §6.7.1: Net declarations with built-in net types
// =========================================================================

TEST(ParserSection6, WireImplicitLogic) {
  // §6.7.1: If no data type specified, net is implicitly logic.
  auto r = Parse(
      "module t;\n"
      "  wire w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
}

TEST(ParserSection6, WireWithRange) {
  // wire [15:0] ww; — equivalent to "wire logic [15:0] ww;"
  auto r = Parse(
      "module t;\n"
      "  wire [15:0] ww;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
}

TEST(ParserSection6, WireExplicitLogicType) {
  auto r = Parse(
      "module t;\n"
      "  wire logic [7:0] w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
}

TEST(ParserSection6, TriregDefaultInit) {
  // §6.7.1: trireg defaults to value x.
  auto r = Parse(
      "module t;\n"
      "  trireg t1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
}

TEST(ParserSection6, InterconnectNet) {
  // §6.7.1: interconnect net has no data type, optional packed/unpacked dims.
  auto r = Parse(
      "module t;\n"
      "  interconnect w1;\n"
      "  interconnect [3:0] w2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(ParserSection6, AllBuiltinNetTypes) {
  auto r = Parse(
      "module t;\n"
      "  wire w;\n"
      "  tri t;\n"
      "  wand wa;\n"
      "  wor wo;\n"
      "  triand ta;\n"
      "  trior to_;\n"
      "  tri0 t0;\n"
      "  tri1 t1;\n"
      "  supply0 s0;\n"
      "  supply1 s1;\n"
      "  uwire uw;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_GE(r.cu->modules[0]->items.size(), 11u);
}

TEST(ParserSection6, WireWithPackedStruct) {
  // §6.7.1 example: wire struct packed {logic ecc; ...} memsig;
  auto r = Parse(
      "module t;\n"
      "  wire struct packed { logic ecc; logic [7:0] data; } memsig;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "memsig");
}

TEST(ParserSection6, WireWithTypedef) {
  // §6.7.1 example: typedef logic [31:0] addressT; wire addressT w1;
  auto r = Parse(
      "module t;\n"
      "  typedef logic [31:0] addressT;\n"
      "  wire addressT w1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[1]->name, "w1");
}
