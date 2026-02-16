#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/type_eval.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult6b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult6b Parse(const std::string& src) {
  ParseResult6b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static ModuleItem* FirstItem(ParseResult6b& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

static Stmt* FirstInitialStmt(ParseResult6b& r) {
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
  // §6.22.2c: same width+signing+state-ness → equivalent.
  // byte (8-bit, 2-state) and shortint differ in width → not equivalent.
  // int and integer: same 32-bit width, but int is 2-state, integer is
  // 4-state → not equivalent.
  DataType a;
  a.kind = DataTypeKind::kByte;
  DataType b;
  b.kind = DataTypeKind::kByte;
  b.is_signed = true;  // byte defaults to signed, make both agree.
  a.is_signed = true;
  EXPECT_TRUE(TypesEquivalent(a, b));  // Same kind → match → equivalent.
}

TEST(ParserSection6, TypesNotEquivalentDifferentState) {
  // §6.22.2c: bit (2-state) and logic (4-state) are NOT equivalent.
  DataType a;
  a.kind = DataTypeKind::kBit;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

TEST(ParserSection6, AssignmentCompatibleIntegral) {
  // §6.22.3: All integral types are assignment compatible.
  DataType a;
  a.kind = DataTypeKind::kInt;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(ParserSection6, AssignmentCompatibleEnumToInt) {
  // §6.22.3: enum → integral is assignment compatible.
  DataType a;
  a.kind = DataTypeKind::kEnum;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(ParserSection6, NotAssignmentCompatibleStringInt) {
  // string and int are not assignment compatible.
  DataType a;
  a.kind = DataTypeKind::kString;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_FALSE(IsAssignmentCompatible(a, b));
}

TEST(ParserSection6, CastCompatibleIntToEnum) {
  // §6.22.4: integral → enum requires cast (cast compatible).
  DataType a;
  a.kind = DataTypeKind::kInt;
  DataType b;
  b.kind = DataTypeKind::kEnum;
  EXPECT_TRUE(IsCastCompatible(a, b));
}

// =========================================================================
// §6.23: Type operator
// =========================================================================

TEST(ParserSection6, TypeOperatorExpr_Kind) {
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
}

TEST(ParserSection6, TypeOperatorExpr_Inner) {
  auto r = Parse(
      "module t;\n"
      "  initial x = type(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->lhs->text, "y");
}

TEST(ParserSection6, TypeRefInferWidth) {
  // §6.23: InferExprWidth on type(expr) returns inner expression's width.
  Arena arena;
  auto* inner = arena.Create<Expr>();
  inner->kind = ExprKind::kIntegerLiteral;  // 32-bit default.
  auto* ref = arena.Create<Expr>();
  ref->kind = ExprKind::kTypeRef;
  ref->lhs = inner;
  TypedefMap typedefs;
  EXPECT_EQ(InferExprWidth(ref, typedefs), 32u);
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
  std::string expected_names[] = {"a", "b"};
  ASSERT_EQ(ports.size(), std::size(expected_names));
  for (size_t i = 0; i < std::size(expected_names); ++i) {
    EXPECT_EQ(ports[i].name, expected_names[i]) << "port " << i;
    EXPECT_EQ(ports[i].data_type.kind, DataTypeKind::kLogic) << "port " << i;
  }
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

// =========================================================================
// §6.21: Scope and lifetime — block-level automatic/static qualifiers
// =========================================================================

TEST(ParserSection6, BlockVarDecl_Automatic) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    automatic int auto1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->var_is_automatic);
}

TEST(ParserSection6, BlockVarDecl_Automatic_Props) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    automatic int auto1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_FALSE(stmt->var_is_static);
  EXPECT_EQ(stmt->var_name, "auto1");
}

TEST(ParserSection6, BlockVarDecl_Static) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    static int st2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->var_is_static);
}

TEST(ParserSection6, BlockVarDecl_Static_Props) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    static int st2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_FALSE(stmt->var_is_automatic);
  EXPECT_EQ(stmt->var_name, "st2");
}

TEST(ParserSection6, BlockVarDecl_AutomaticWithInit) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    automatic int loop3 = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->var_is_automatic);
  ASSERT_NE(stmt->var_init, nullptr);
}

TEST(ParserSection6, BlockVarDecl_StaticVar) {
  EXPECT_TRUE(
      ParseOk6("module t;\n"
               "  initial begin\n"
               "    static var logic x;\n"
               "  end\n"
               "endmodule\n"));
}

// =========================================================================
// §6.20.7: $ as a constant
// =========================================================================

TEST(ParserSection6, DollarConstant_ParamAssign) {
  EXPECT_TRUE(
      ParseOk6("module t;\n"
               "  parameter p = $;\n"
               "endmodule\n"));
}

// =========================================================================
// §6.6.4: Trireg charge strength and net delays
// =========================================================================

TEST(ParserSection6, TriregChargeStrengthSmall) {
  auto r = Parse(
      "module t;\n"
      "  trireg (small) s1;\n"
      "endmodule\n");
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(item->data_type.charge_strength, 1);
}

TEST(ParserSection6, TriregChargeStrengthLarge) {
  auto r = Parse(
      "module t;\n"
      "  trireg (large) l1;\n"
      "endmodule\n");
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.charge_strength, 4);
}

TEST(ParserSection6, TriregThreeDelay_Strength) {
  auto r = Parse(
      "module t;\n"
      "  trireg (large) #(10, 20, 50) cap1;\n"
      "endmodule\n");
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.charge_strength, 4);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 10u);
}

TEST(ParserSection6, TriregThreeDelay_FallAndDecay) {
  auto r = Parse(
      "module t;\n"
      "  trireg (large) #(10, 20, 50) cap1;\n"
      "endmodule\n");
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->int_val, 20u);
  ASSERT_NE(item->net_delay_decay, nullptr);
  EXPECT_EQ(item->net_delay_decay->int_val, 50u);
}

TEST(ParserSection6, TriregSingleDelay) {
  auto r = Parse(
      "module t;\n"
      "  trireg #5 t1;\n"
      "endmodule\n");
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 5u);
}

TEST(ParserSection6, TriregSingleDelay_NoFallDecay) {
  auto r = Parse(
      "module t;\n"
      "  trireg #5 t1;\n"
      "endmodule\n");
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

// §6.20.1 — block-level parameter declaration
TEST(ParserSection6, BlockLevelParameter) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    parameter int P = 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// §6.20.1 — block-level localparam declaration
TEST(ParserSection6, BlockLevelLocalparam) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    localparam int LP = 10;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// §20.6 — Bare type keyword in expression context ($typename(logic))
TEST(ParserSection6, BareTypeKeywordInExpr) {
  auto r = Parse(
      "module t;\n"
      "  initial $display($typename(logic));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// §6.3.2.2: Drive strength on net declaration with inline assignment.
TEST(ParserSection6, NetDeclDriveStrength) {
  auto r = Parse(
      "module m;\n"
      "  wire (weak0, strong1) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  // 2=weak, 4=strong (parser encoding)
  EXPECT_EQ(item->drive_strength0, 2u);
  EXPECT_EQ(item->drive_strength1, 4u);
}

// =========================================================================
// §6.6.8: Void data type (additional tests)
// =========================================================================

TEST(ParserSection6, VoidCastExpression) {
  auto r = Parse(
      "module t;\n"
      "  function int foo(); return 1; endfunction\n"
      "  initial void'(foo());\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(ParserSection6, VoidFunctionInClass) {
  auto r = Parse(
      "class C;\n"
      "  function void setup();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection6, VoidTaskReturnType) {
  // Tasks implicitly return void; verify parse is correct.
  auto r = Parse(
      "module t;\n"
      "  task do_nothing();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
}

// =========================================================================
// §6.20.3: Type parameters (additional tests)
// =========================================================================

TEST(ParserSection6, TypeParameterWithMultipleParams) {
  EXPECT_TRUE(
      ParseOk6("module m #(parameter type T = int, parameter type U = real)\n"
               "  ();\n"
               "  T x;\n"
               "  U y;\n"
               "endmodule\n"));
}

TEST(ParserSection6, TypeParameterDefaultShortint) {
  EXPECT_TRUE(
      ParseOk6("module ma #(parameter p1 = 1, parameter type p2 = shortint)\n"
               "  (input logic [p1:0] i, output logic [p1:0] o);\n"
               "  p2 j = 0;\n"
               "endmodule\n"));
}

// =========================================================================
// §6.21: Scope and lifetime (additional tests)
// =========================================================================

TEST(ParserSection6, AutomaticTaskDecl) {
  auto r = Parse(
      "module t;\n"
      "  task automatic my_task();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_automatic);
}

TEST(ParserSection6, StaticTaskDecl) {
  auto r = Parse(
      "module t;\n"
      "  task static my_task();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_static);
}

TEST(ParserSection6, ModuleLifetimeAutomatic) {
  auto r = Parse("module automatic t; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "t");
}

// =========================================================================
// §6.22.1 -- Matching types
// =========================================================================

TEST(ParserSection6, MatchingTypesBuiltinTypedef) {
  auto r = Parse(
      "module m;\n"
      "  typedef bit node;\n"
      "  node n1;\n"
      "  bit n2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(ParserSection6, MatchingTypesAnonymousStruct) {
  auto r = Parse(
      "module m;\n"
      "  struct packed {int A; int B;} AB1, AB2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
}

TEST(ParserSection6, MatchingTypesNamedTypedefStruct) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed {int A; int B;} AB_t;\n"
      "  AB_t x1;\n"
      "  AB_t x2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(ParserSection6, MatchingTypesSignedBitVector) {
  auto r = Parse(
      "module m;\n"
      "  typedef bit signed [7:0] BYTE;\n"
      "  BYTE b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(ParserSection6, MatchingTypesArrayTypedef) {
  auto r = Parse(
      "module m;\n"
      "  typedef byte MEM_BYTES [256];\n"
      "  MEM_BYTES mem;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

// =========================================================================
// §6.22: Type compatibility — additional tests
// =========================================================================

TEST(ParserSection6, TypesMatchNamedSame) {
  // Two named types with the same name should match.
  DataType a;
  a.kind = DataTypeKind::kNamed;
  a.type_name = "mytype";
  DataType b;
  b.kind = DataTypeKind::kNamed;
  b.type_name = "mytype";
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesMatchNamedDifferent) {
  // Two named types with different names should not match.
  DataType a;
  a.kind = DataTypeKind::kNamed;
  a.type_name = "type_a";
  DataType b;
  b.kind = DataTypeKind::kNamed;
  b.type_name = "type_b";
  EXPECT_FALSE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesEquivalentSameKind) {
  // §6.22.2: Same kind, same signedness, same state-ness -> equivalent.
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = true;
  EXPECT_TRUE(TypesEquivalent(a, b));
}

TEST(ParserSection6, TypesNotEquivalentDifferentSign) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = false;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

TEST(ParserSection6, AssignmentCompatibleRealToReal) {
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kShortreal;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(ParserSection6, CastCompatibleRealToInt) {
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_TRUE(IsCastCompatible(a, b));
}

TEST(ParserSection6, MatchingTypesSameSigningModifier) {
  // §6.22.1g: Explicitly adding signed to a type that is already signed
  // creates a matching type.
  DataType a;
  a.kind = DataTypeKind::kByte;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kByte;
  b.is_signed = true;
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(ParserSection6, TypeCompatibilityTypedefParsing) {
  // §6.22.1b: A simple typedef that renames a built-in type matches it.
  auto r = Parse(
      "module m;\n"
      "  typedef bit node;\n"
      "  typedef int type1;\n"
      "  typedef type1 type2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_GE(r.cu->modules[0]->items.size(), 3u);
}

TEST(ParserSection6, TypeCompatibilityAnonymousStruct) {
  // §6.22.1c: Anonymous struct matches itself within same declaration.
  auto r = Parse(
      "module m;\n"
      "  struct packed { int A; int B; } AB1, AB2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  // AB1 and AB2 should both be declared
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}
