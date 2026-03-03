// Non-LRM tests

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

static ModuleItem* FirstItem(ParseResult& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

static Stmt* FirstInitialStmt(ParseResult& r) {
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

namespace {

// =========================================================================
// §6.20: Constants — parameter and localparam
// =========================================================================
TEST(ParserSection6, ParameterWithExplicitType) {
  // §6.20: parameter with explicit type.
  auto r = ParseWithPreprocessor(
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
  auto r = ParseWithPreprocessor("module static t; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "t");
}

TEST(ParserSection6, ProgramLifetimeAutomatic) {
  // §6.21: program blocks may be declared automatic.
  auto r = ParseWithPreprocessor("program automatic test_prog; endprogram\n");
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
TEST(ParserSection6, CastUnsigned) {
  // §6.24: unsigned'(expr) changes signedness.
  auto r = ParseWithPreprocessor(
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
  auto r = ParseWithPreprocessor(
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
  auto r = ParseWithPreprocessor(
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
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  bit signed [15:0] sb;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_TRUE(item->data_type.is_signed);
}

}  // namespace
