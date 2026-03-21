#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TypeOperatorParsing, TypeOperatorInVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  int a;\n"
      "  type(a) b;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_NE(item->data_type.type_ref_expr, nullptr);
}

TEST(TypeOperatorParsing, TypeRefExpression) {
  auto r = Parse(
      "module m;\n"
      "  int a;\n"
      "  initial begin $display(\"%s\", $typename(type(a))); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TypeOperatorParsing, TypeRefDataType) {
  auto r = Parse(
      "module m;\n"
      "  initial begin $display(\"%s\", $typename(type(logic [7:0]))); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TypeOperatorParsing, TypeOperatorOnClassScopedType) {
  auto r = Parse(
      "class outer;\n"
      "  typedef int inner_t;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin $display(\"%s\", $typename(type(outer::inner_t))); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TypeOperatorParsing, TypeRefVarDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real a = 1.0;\n"
              "  real b = 2.0;\n"
              "  var type(a + b) c;\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, TypeRefDataTypeParam) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter type T = type(logic [11:0]));\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, TypeRefComparison) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter type T = int)\n"
              "  ();\n"
              "  initial begin\n"
              "    if (type(T) == type(int)) $display(\"int\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, TypeOperatorExprKind) {
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

TEST(TypeOperatorParsing, TypeOperatorInDataType) {
  auto r = Parse(
      "module t;\n"
      "  parameter type T = type(int);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);

  ASSERT_NE(item->init_expr, nullptr);
  EXPECT_EQ(item->init_expr->kind, ExprKind::kTypeRef);
}

TEST(PrimaryParsing, PrimaryTypeRef) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    automatic int w;\n"
      "    w = $bits(x);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TypeOperatorParsing, TypeRefInnerIdent) {
  auto r = Parse(
      "module t;\n"
      "  initial x = type(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTypeRef);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->lhs->text, "y");
}

TEST(TypeOperatorParsing, TypeRefDataTypeText) {
  auto r = Parse(
      "module t;\n"
      "  initial x = type(int);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTypeRef);
}

TEST(TypeOperatorParsing, VarTypeRefDeclKind) {
  auto r = Parse(
      "module t;\n"
      "  int a;\n"
      "  var type(a) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kVarDecl);
  ASSERT_NE(items[1]->data_type.type_ref_expr, nullptr);
  EXPECT_EQ(items[1]->name, "b");
}

TEST(TypeOperatorParsing, VarTypeRefExprIdent) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  var type(x) y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  auto* ref = items[1]->data_type.type_ref_expr;
  ASSERT_NE(ref, nullptr);
  EXPECT_EQ(ref->kind, ExprKind::kIdentifier);
  EXPECT_EQ(ref->text, "x");
}

TEST(TypeOperatorParsing, VarTypeRefBinaryExpr) {
  auto r = Parse(
      "module t;\n"
      "  real a, b;\n"
      "  var type(a + b) c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;

  ModuleItem* c_item = nullptr;
  for (auto* item : items) {
    if (item->name == "c") {
      c_item = item;
      break;
    }
  }
  ASSERT_NE(c_item, nullptr);
  EXPECT_EQ(c_item->kind, ModuleItemKind::kVarDecl);
  auto* ref = c_item->data_type.type_ref_expr;
  ASSERT_NE(ref, nullptr);
  EXPECT_EQ(ref->kind, ExprKind::kBinary);
}

TEST(TypeOperatorParsing, TypeRefParamDefault) {
  auto r = Parse(
      "module t #(parameter type T = type(logic));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TypeOperatorParsing, TypeRefParamPackedDim) {
  EXPECT_TRUE(
      ParseOk("module t #(parameter type T = type(logic [7:0]));\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, TypeRefNeqComparison) {
  EXPECT_TRUE(
      ParseOk("module t #(parameter type T = int)\n"
              "  ();\n"
              "  initial begin\n"
              "    if (type(T) != type(real)) $display(\"differ\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, TypeRefCaseEq) {
  EXPECT_TRUE(
      ParseOk("module t #(parameter type T = int)\n"
              "  ();\n"
              "  initial begin\n"
              "    if (type(T) === type(int)) $display(\"exact\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, TypeRefCaseNeq) {
  EXPECT_TRUE(
      ParseOk("module t #(parameter type T = int)\n"
              "  ();\n"
              "  initial begin\n"
              "    if (type(T) !== type(real)) $display(\"not exact\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, TypeRefInCaseExpr) {
  EXPECT_TRUE(
      ParseOk("module t #(parameter type T = int)\n"
              "  ();\n"
              "  initial begin\n"
              "    case (type(T))\n"
              "      type(int) : $display(\"int\");\n"
              "      type(real) : $display(\"real\");\n"
              "      default : $display(\"other\");\n"
              "    endcase\n"
              "  end\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, TypeRefOnLogic) {
  auto r = Parse(
      "module t;\n"
      "  initial x = type(logic);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTypeRef);
}

TEST(TypeOperatorParsing, TypeRefOnBit) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = type(bit);\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, TypeRefOnByte) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = type(byte);\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, TypeRefOnShortint) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = type(shortint);\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, TypeRefOnLongint) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = type(longint);\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, TypeRefOnReal) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = type(real);\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, TypeRefOnString) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = type(string);\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, TypeRefPackedArray) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = type(logic [15:0]);\n"
              "endmodule\n"));
}

static ModuleItem* FindItemByName(ParseResult& r, std::string_view name) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->name == name) return item;
  }
  return nullptr;
}

TEST(TypeOperatorParsing, VarTypeRefTernary) {
  auto r = Parse(
      "module t;\n"
      "  int a;\n"
      "  real b;\n"
      "  var type(1 ? a : b) c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* c_item = FindItemByName(r, "c");
  ASSERT_NE(c_item, nullptr);
  EXPECT_EQ(c_item->kind, ModuleItemKind::kVarDecl);
  auto* ref = c_item->data_type.type_ref_expr;
  ASSERT_NE(ref, nullptr);
  EXPECT_EQ(ref->kind, ExprKind::kTernary);
}

TEST(TypeOperatorParsing, TypeRefCaseLogicPacked) {
  EXPECT_TRUE(
      ParseOk("module t #(parameter type T = type(logic [11:0]))\n"
              "  ();\n"
              "  initial begin\n"
              "    case (type(T))\n"
              "      type(logic [11:0]) : $display(\"12-bit\");\n"
              "      default : $stop;\n"
              "    endcase\n"
              "  end\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, MultipleVarTypeRefDecls) {
  auto r = Parse(
      "module t;\n"
      "  int x;\n"
      "  real y;\n"
      "  var type(x) a;\n"
      "  var type(y) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  int type_ref_count = 0;
  for (auto* item : items) {
    if (item->data_type.type_ref_expr != nullptr) {
      ++type_ref_count;
    }
  }
  EXPECT_EQ(type_ref_count, 2);
}

TEST(TypeOperatorParsing, TypeRefOnLiteral) {
  auto r = Parse(
      "module t;\n"
      "  initial x = type(42);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTypeRef);

  ASSERT_NE(stmt->rhs->lhs, nullptr);
  EXPECT_EQ(stmt->rhs->lhs->kind, ExprKind::kIntegerLiteral);
}

TEST(TypeOperatorParsing, VarTypeRefConcat) {
  auto r = Parse(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  var type({a, b}) c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* c_item = FindItemByName(r, "c");
  ASSERT_NE(c_item, nullptr);
  EXPECT_EQ(c_item->kind, ModuleItemKind::kVarDecl);
  auto* ref = c_item->data_type.type_ref_expr;
  ASSERT_NE(ref, nullptr);
  EXPECT_EQ(ref->kind, ExprKind::kConcatenation);
}

TEST(TypeOperatorParsing, TypeRefOnShortreal) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = type(shortreal);\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, VarTypeRefMemberAccess) {
  auto r = Parse(
      "module t;\n"
      "  var type(pkg.field) x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  ASSERT_NE(item->data_type.type_ref_expr, nullptr);
}

TEST(TypeOperatorParsing, TypeRefOnTime) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = type(time);\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, TypeOpInParamDefault) {
  EXPECT_TRUE(
      ParseOk("module t #(parameter type T = type(logic [7:0]));\n"
              "  T data;\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, TypeRefInferWidth) {
  Arena arena;
  auto* inner = arena.Create<Expr>();
  inner->kind = ExprKind::kIntegerLiteral;
  auto* ref = arena.Create<Expr>();
  ref->kind = ExprKind::kTypeRef;
  ref->lhs = inner;
  TypedefMap typedefs;
  EXPECT_EQ(InferExprWidth(ref, typedefs), 32u);
}

TEST(TypeOperatorParsing, TypeRefDataTypeCaseAndComparison) {
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

TEST(TypeOperatorParsing, TypeRefThis) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  static function type(this) get();\n"
              "    return null;\n"
              "  endfunction\n"
              "endclass\n"));
}

TEST(TypeOperatorParsing, LocalparamTypeFromTypeOp) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  localparam type T = type(bit [12:0]);\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, TypeRefSimpleExprNoHier) {
  auto r = Parse(
      "module t;\n"
      "  int i;\n"
      "  var type(i + 3) j;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* j_item = FindItemByName(r, "j");
  ASSERT_NE(j_item, nullptr);
  ASSERT_NE(j_item->data_type.type_ref_expr, nullptr);
  EXPECT_EQ(j_item->data_type.type_ref_expr->kind, ExprKind::kBinary);
}

TEST(TypeOperatorParsing, TypeRefInWireNetDecl) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  wire x;\n"
              "  wire type(x) y;\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, TypeRefInTriNetDecl) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  tri x;\n"
              "  tri type(x) y;\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, TypeRefAssignmentPatternCast) {
  auto r = Parse(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    x = type(x)'{8'd1, 8'd2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TypeOperatorParsing, TypeRefSelfDeterminedBinaryExpr) {
  auto r = Parse(
      "module t;\n"
      "  byte a;\n"
      "  int b;\n"
      "  var type(a + b) c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* c_item = FindItemByName(r, "c");
  ASSERT_NE(c_item, nullptr);
  ASSERT_NE(c_item->data_type.type_ref_expr, nullptr);
  EXPECT_EQ(c_item->data_type.type_ref_expr->kind, ExprKind::kBinary);
}

}  // namespace
