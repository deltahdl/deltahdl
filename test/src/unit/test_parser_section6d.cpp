#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/type_eval.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ParseResult6d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult6d Parse(const std::string& src) {
  ParseResult6d result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static ModuleItem* FirstItem(ParseResult6d& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

static Stmt* FirstInitialStmt(ParseResult6d& r) {
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

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

// =========================================================================
// §6.3: Value set — 4-state vs 2-state data types
// =========================================================================

TEST(ParserSection6, ValueSet_4StateLogicDecl) {
  // §6.3: logic is the basic 4-state data type.
  auto r = Parse(
      "module t;\n"
      "  logic [3:0] val;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(Is4stateType(DataTypeKind::kLogic));
}

TEST(ParserSection6, ValueSet_2StateBitDecl) {
  // §6.3: bit is a 2-state type (only 0 and 1).
  auto r = Parse(
      "module t;\n"
      "  bit [7:0] val;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_FALSE(Is4stateType(DataTypeKind::kBit));
}

// =========================================================================
// §6.6.8: Generic interconnect
// =========================================================================

TEST(ParserSection6, InterconnectDeclFlag) {
  // §6.6.8: interconnect declares a typeless generic net.
  auto r = Parse(
      "module t;\n"
      "  interconnect ibus;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->data_type.is_interconnect);
  EXPECT_EQ(item->name, "ibus");
}

TEST(ParserSection6, InterconnectWithPackedDim) {
  // §6.6.8: interconnect may have packed dimensions.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  interconnect [7:0] ibus;\n"
              "endmodule\n"));
}

// =========================================================================
// §6.8: Variable declarations
// =========================================================================

TEST(ParserSection6, VarKeywordLogicDecl) {
  // §6.8: "var" keyword can precede an explicit data type.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  var logic [7:0] data;\n"
              "endmodule\n"));
}

TEST(ParserSection6, VarKeywordImplicitType) {
  // §6.8: "var" without explicit type implies logic.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  var [3:0] nibble;\n"
              "endmodule\n"));
}

// =========================================================================
// §6.9: Vector declarations
// =========================================================================

TEST(ParserSection6, VectorBigEndian) {
  // §6.9: Vector [msb:lsb] with msb > lsb (big-endian).
  auto r = Parse(
      "module t;\n"
      "  logic [31:0] wide;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 31u);
  EXPECT_EQ(item->data_type.packed_dim_right->int_val, 0u);
}

TEST(ParserSection6, VectorLittleEndian) {
  // §6.9: Vector [lsb:msb] with lsb < msb (little-endian).
  auto r = Parse(
      "module t;\n"
      "  logic [0:7] le;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 0u);
  EXPECT_EQ(item->data_type.packed_dim_right->int_val, 7u);
}

// =========================================================================
// §6.10: Implicit declarations — `default_nettype directive
// =========================================================================

TEST(ParserSection6, DefaultNettypeWire) {
  // §6.10: Default nettype is wire; implicit nets are wire.
  auto r = Parse(
      "`default_nettype wire\n"
      "module t;\n"
      "  assign out = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->default_nettype, NetType::kWire);
}

TEST(ParserSection6, DefaultNettypeNone) {
  // §6.10: `default_nettype none disables implicit declarations.
  auto r = Parse(
      "`default_nettype none\n"
      "module t;\n"
      "  wire explicit_w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
}

// =========================================================================
// §6.11.1: Integral types — automatic variables in functions
// =========================================================================

TEST(ParserSection6, AutomaticFunctionLocalVar) {
  // §6.11.1: Automatic function has automatic local variables.
  auto r = Parse(
      "module t;\n"
      "  function automatic int factorial(int n);\n"
      "    if (n <= 1) return 1;\n"
      "    return n * factorial(n - 1);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_automatic);
}

TEST(ParserSection6, AutomaticFunctionReturnType) {
  // §6.11.1: Function return type is an integral type.
  auto r = Parse(
      "module t;\n"
      "  function automatic int get_value();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
}

// =========================================================================
// §6.12: Real, shortreal, and realtime types
// =========================================================================

TEST(ParserSection6, RealWithInitializer) {
  // §6.12: real is a 64-bit IEEE double.
  auto r = Parse(
      "module t;\n"
      "  real pi = 3.14159;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReal);
  ASSERT_NE(item->init_expr, nullptr);
}

TEST(ParserSection6, ShortrealInit) {
  // §6.12: shortreal is a 32-bit IEEE float.
  auto r = Parse(
      "module t;\n"
      "  shortreal sr = 1.5;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortreal);
  ASSERT_NE(item->init_expr, nullptr);
}

// =========================================================================
// §6.16: String data type
// =========================================================================

TEST(ParserSection6, StringDeclModule) {
  // §6.16: String data type is a dynamic ordered collection of characters.
  auto r = Parse(
      "module t;\n"
      "  string name;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kString);
  EXPECT_EQ(item->name, "name");
}

TEST(ParserSection6, StringDeclWithInit) {
  // §6.16: String variable with initializer.
  auto r = Parse(
      "module t;\n"
      "  string msg = \"hello\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kString);
  ASSERT_NE(item->init_expr, nullptr);
}

// =========================================================================
// §6.18: User-defined types (typedef)
// =========================================================================

TEST(ParserSection6, TypedefLogicVector) {
  // §6.18: typedef creates a user-defined type from a built-in type.
  auto r = Parse(
      "module t;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "byte_t");
}

TEST(ParserSection6, TypedefUsedInVarDecl) {
  // §6.18: A typedef-defined name appears as kNamed in subsequent decls.
  auto r = Parse(
      "module t;\n"
      "  typedef int counter_t;\n"
      "  counter_t cnt;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* var = r.cu->modules[0]->items[1];
  EXPECT_EQ(var->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(var->data_type.type_name, "counter_t");
}

// =========================================================================
// §6.20: Constants — parameter and localparam
// =========================================================================

TEST(ParserSection6, ParameterWithExplicitType) {
  // §6.20: parameter with explicit type.
  auto r = Parse(
      "module t;\n"
      "  parameter int WIDTH = 8;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  ASSERT_NE(item->init_expr, nullptr);
}

TEST(ParserSection6, LocalparamConstant) {
  // §6.20: localparam cannot be overridden.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  localparam int DEPTH = 16;\n"
              "endmodule\n"));
}

// =========================================================================
// §6.20.3: Local parameters (localparam) and type parameters
// =========================================================================

TEST(ParserSection6, LocalparamInHeaderPort) {
  // §6.20.3: localparam in module parameter port list.
  EXPECT_TRUE(
      ParseOk("module m #(parameter int W = 8, localparam int W2 = W * 2)\n"
              "  (input logic [W-1:0] d);\n"
              "endmodule\n"));
}

TEST(ParserSection6, TypeParamDefaultLogicVector) {
  // §6.20.3: Type parameter with a vector default.
  EXPECT_TRUE(
      ParseOk("module m #(parameter type DATA_T = logic [15:0])\n"
              "  ();\n"
              "  DATA_T data;\n"
              "endmodule\n"));
}

// =========================================================================
// §6.21: Scope and lifetime
// =========================================================================

TEST(ParserSection6, ModuleLifetimeStatic) {
  // §6.21: module with static (default) lifetime.
  auto r = Parse("module static t; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "t");
}

TEST(ParserSection6, ProgramLifetimeAutomatic) {
  // §6.21: program blocks may be declared automatic.
  auto r = Parse("program automatic test_prog; endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "test_prog");
}

// =========================================================================
// §6.22: Type compatibility — TypesMatch on named types
// =========================================================================

TEST(ParserSection6, TypesMatchNamedSameType) {
  // §6.22: Two kNamed types with the same type_name match.
  DataType a;
  a.kind = DataTypeKind::kNamed;
  a.type_name = "mytype";
  DataType b;
  b.kind = DataTypeKind::kNamed;
  b.type_name = "mytype";
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesMatchNamedDifferentType) {
  // §6.22: Two kNamed types with different type_names do not match.
  DataType a;
  a.kind = DataTypeKind::kNamed;
  a.type_name = "type_a";
  DataType b;
  b.kind = DataTypeKind::kNamed;
  b.type_name = "type_b";
  EXPECT_FALSE(TypesMatch(a, b));
}

// =========================================================================
// §6.22.1: Type equivalence — matching built-in types
// =========================================================================

TEST(ParserSection6, TypesEquivalentSameSignedInt) {
  // §6.22.1/2: Two int types (both signed by default) are equivalent.
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = true;
  EXPECT_TRUE(TypesEquivalent(a, b));
}

TEST(ParserSection6, TypesEquivalentDiffSignedness) {
  // §6.22.1: Same kind but different signedness is not equivalent.
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = false;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

// =========================================================================
// §6.22.2: Type compatibility rules — packed width comparison
// =========================================================================

TEST(ParserSection6, AssignCompatibleByteToShortint) {
  // §6.22.2: byte (8-bit 2-state) and shortint (16-bit 2-state) differ
  // in width, but both are integral so assignment compatible.
  DataType a;
  a.kind = DataTypeKind::kByte;
  DataType b;
  b.kind = DataTypeKind::kShortint;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(ParserSection6, NotEquivalentDiffWidth) {
  // §6.22.2: byte (8-bit) and shortint (16-bit) are NOT equivalent.
  DataType a;
  a.kind = DataTypeKind::kByte;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kShortint;
  b.is_signed = true;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

// =========================================================================
// §6.22.3: Type assignment compatibility
// =========================================================================

TEST(ParserSection6, AssignCompatibleRealToReal) {
  // §6.22.3: real to real is assignment compatible.
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kReal;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(ParserSection6, AssignCompatibleEnumToLogic) {
  // §6.22.3: enum base type is integral, so enum to integral is compatible.
  DataType a;
  a.kind = DataTypeKind::kEnum;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

// =========================================================================
// §6.23: Type operator — type() in declarations
// =========================================================================

TEST(ParserSection6, VarTypeOpDecl) {
  // §6.23: var type(expr) creates a variable with the type of expr.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  int a;\n"
              "  var type(a) b;\n"
              "endmodule\n"));
}

TEST(ParserSection6, TypeOpInParamDefault) {
  // §6.23: type(data_type) as parameter default.
  EXPECT_TRUE(
      ParseOk("module t #(parameter type T = type(logic [7:0]));\n"
              "  T data;\n"
              "endmodule\n"));
}

// =========================================================================
// §6.24: Casting — general
// =========================================================================

TEST(ParserSection6, CastSizeBitWidth) {
  // §6.24/6.24.1: Size cast with integer constant.
  auto r = Parse(
      "module t;\n"
      "  initial x = 16'(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
}

TEST(ParserSection6, CastUnsigned) {
  // §6.24: unsigned'(expr) changes signedness.
  auto r = Parse(
      "module t;\n"
      "  initial x = unsigned'(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
  EXPECT_EQ(rhs->text, "unsigned");
}

// =========================================================================
// §6.24.1: Static casting — type and size casts
// =========================================================================

TEST(ParserSection6, StaticCastRealToInt) {
  // §6.24.1: int'(2.0 * 3.0) casts real to int.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    int result;\n"
              "    result = int'(2.0 * 3.0);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection6, StaticCastStringType) {
  // §6.24.1: string'(expr) cast is valid per grammar.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    string s;\n"
              "    s = string'(8'h41);\n"
              "  end\n"
              "endmodule\n"));
}

// =========================================================================
// §6.24.2: Dynamic casting — $cast
// =========================================================================

TEST(ParserSection6, DynamicCastTask) {
  // §6.24.2: $cast as a task call.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef enum { A, B, C } abc_t;\n"
              "  initial begin\n"
              "    abc_t e;\n"
              "    $cast(e, 1);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection6, DynamicCastFunction) {
  // §6.24.2: $cast as a function returns int.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef enum { X, Y, Z } xyz_t;\n"
              "  initial begin\n"
              "    xyz_t e;\n"
              "    int ok;\n"
              "    ok = $cast(e, 2);\n"
              "  end\n"
              "endmodule\n"));
}

// =========================================================================
// §6.24.3: Bit-stream casting
// =========================================================================

TEST(ParserSection6, BitstreamCastStructToInt) {
  // §6.24.3: Cast between bit-stream types (struct to int).
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  typedef struct packed { logic [15:0] hi; logic [15:0] lo; } pair_t;\n"
      "  initial begin\n"
      "    pair_t p;\n"
      "    int x;\n"
      "    x = int'(p);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection6, BitstreamCastIntToStruct) {
  // §6.24.3: Cast from int to packed struct (bit-stream).
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  initial begin\n"
      "    ab_t s;\n"
      "    s = ab_t'(16'hABCD);\n"
      "  end\n"
      "endmodule\n"));
}

// =========================================================================
// §6.3: Value set — 4-state vs 2-state type queries
// =========================================================================

TEST(ParserSection6, ValueSet_IntegerIs4State) {
  // §6.3: integer is a 4-state type.
  EXPECT_TRUE(Is4stateType(DataTypeKind::kInteger));
}

TEST(ParserSection6, ValueSet_IntIs2State) {
  // §6.3: int is a 2-state type.
  EXPECT_FALSE(Is4stateType(DataTypeKind::kInt));
}

// =========================================================================
// §6.6.8: Chandle data type
// =========================================================================

TEST(ParserSection6, ChandleInClass) {
  // §6.6.8: chandle used in a class for DPI handle.
  auto r = Parse(
      "class Wrapper;\n"
      "  chandle ptr;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_GE(r.cu->classes[0]->members.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[0]->data_type.kind,
            DataTypeKind::kChandle);
}

TEST(ParserSection6, ChandleMultipleDecls) {
  // chandle with multiple variables in a module.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  chandle h1, h2;\n"
              "endmodule\n"));
}

// =========================================================================
// §6.9: Vector declarations — signed vectors
// =========================================================================

TEST(ParserSection6, VectorUnsignedExplicit) {
  // §6.9: Explicit unsigned qualifier on a vector.
  auto r = Parse(
      "module t;\n"
      "  logic unsigned [7:0] uv;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_FALSE(item->data_type.is_signed);
}

TEST(ParserSection6, VectorSignedBitType) {
  // §6.9: bit type with signed qualifier.
  auto r = Parse(
      "module t;\n"
      "  bit signed [15:0] sb;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_TRUE(item->data_type.is_signed);
}

// =========================================================================
// §6.12: Realtime type — alias for real
// =========================================================================

TEST(ParserSection6, RealtimeWithInit) {
  // §6.12: realtime is equivalent to real for simulation.
  auto r = Parse(
      "module t;\n"
      "  realtime ts = 100.0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kRealtime);
  ASSERT_NE(item->init_expr, nullptr);
}

TEST(ParserSection6, RealInFunction) {
  // §6.12: real used as function return type.
  auto r = Parse(
      "module t;\n"
      "  function real compute();\n"
      "    return 1.5;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kReal);
}

// =========================================================================
// §6.16: String in block scope
// =========================================================================

TEST(ParserSection6, StringBlockDecl) {
  // §6.16: string declared inside an initial block.
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    string msg;\n"
      "    msg = \"test\";\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->var_decl_type.kind, DataTypeKind::kString);
}

TEST(ParserSection6, StringFunctionArg) {
  // §6.16: string as a function argument type.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  function void print_msg(string s);\n"
              "  endfunction\n"
              "endmodule\n"));
}

// =========================================================================
// §6.20: Constants — const variable
// =========================================================================

TEST(ParserSection6, ConstRealDecl) {
  // §6.20.6: const can qualify a real variable.
  auto r = Parse(
      "module t;\n"
      "  const real PI = 3.14159;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReal);
  EXPECT_TRUE(item->data_type.is_const);
}

TEST(ParserSection6, ConstStringDecl) {
  // §6.20.6: const string declaration.
  auto r = Parse(
      "module t;\n"
      "  const string GREETING = \"Hi\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kString);
  EXPECT_TRUE(item->data_type.is_const);
}

// =========================================================================
// §6.22: Cast compatibility
// =========================================================================

TEST(ParserSection6, CastCompatibleRealToIntType) {
  // §6.22.4: real and int are cast compatible.
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_TRUE(IsCastCompatible(a, b));
}

TEST(ParserSection6, CastCompatibleEnumToInt) {
  // §6.22.4: enum and int are cast compatible.
  DataType a;
  a.kind = DataTypeKind::kEnum;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_TRUE(IsCastCompatible(a, b));
}
