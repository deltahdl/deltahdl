#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

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

TEST(TypeOperatorParsing, TypeRefInWandNetDecl) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  wand x;\n"
              "  wand type(x) y;\n"
              "endmodule\n"));
}

TEST(TypeOperatorParsing, TypeRefInWorNetDecl) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  wor x;\n"
              "  wor type(x) y;\n"
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

// §8.23 lists the type operator among the contexts in which a class scope
// resolution may prefix a type name, so `type(Frame::payload_t)` names the
// typedef of class Frame. This pins both halves of that name on the kTypeRef
// node: text holds payload_t and scope_prefix holds Frame, so dropping the
// prefix no longer leaves `type(Frame::payload_t)` and `type(payload_t)`
// indistinguishable in the AST.
TEST(TypeOperatorParsing, TypeRefScopedTypeRetainsClassPrefix) {
  auto r = Parse(
      "class Frame;\n"
      "  typedef int payload_t;\n"
      "endclass\n"
      "module t;\n"
      "  initial x = type(Frame::payload_t);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTypeRef);
  EXPECT_EQ(rhs->text, "payload_t");
  EXPECT_EQ(rhs->scope_prefix, "Frame");
}

// §6.23 — a type reference used as the data type of a variable declaration
// shall be preceded by the `var` keyword. This is the rejecting counterpart to
// the accepting `var type(a) b;` forms above: a bare `type(a) b;` omits the
// required keyword and the parser reports an error.
TEST(TypeOperatorParsing, VarTypeRefWithoutVarKeywordRejected) {
  auto r = Parse(
      "module t;\n"
      "  int a;\n"
      "  type(a) b;\n"
      "endmodule\n");
  // §6.8 states the data_declaration the `var` keyword belongs to, and that is
  // where Parser::ParseTypedItemOrInst files the report.
  EXPECT_TRUE(ReportedError(r.diags,
                            "type_reference in a variable declaration must be "
                            "preceded by the 'var' keyword",
                            3, "6.8"));
}

// §6.23's first example declares two names of one type reference, `var
// type(a+b) c, d;`, and A.2.1.3 follows the data_type with a whole
// list_of_variable_decl_assignments, so each name, and an initializer, is read
// with the type reference as its data type.
TEST(TypeOperatorParsing, VarTypeRefDeclaresEveryNameOfItsList) {
  auto r = Parse(
      "module t;\n"
      "  bit [31:0] a, b;\n"
      "  var type(a+b) c, d;\n"
      "  var type(a) e = 5;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 5u);
  for (size_t i = 2; i < 5; ++i) {
    EXPECT_EQ(items[i]->kind, ModuleItemKind::kVarDecl);
    ASSERT_NE(items[i]->data_type.type_ref_expr, nullptr);
  }
  EXPECT_EQ(items[2]->name, "c");
  EXPECT_EQ(items[3]->name, "d");
  EXPECT_EQ(items[3]->data_type.type_ref_expr->kind, ExprKind::kBinary);
  EXPECT_EQ(items[4]->name, "e");
  ASSERT_NE(items[4]->init_expr, nullptr);
  EXPECT_EQ(items[4]->init_expr->kind, ExprKind::kIntegerLiteral);
}

// §6.23 lists casts among the uses of a type reference, `c = type(i+3)'(v);`,
// so the `'(` after the reference opens a cast whose casting type is the
// reference and whose operand is the parenthesized expression.
TEST(TypeOperatorParsing, TypeRefCastTakesAParenthesizedOperand) {
  auto r = Parse(
      "module t;\n"
      "  int i, c;\n"
      "  logic [15:0] v;\n"
      "  initial c = type(i+3)'(v[15:0]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* cast = stmt->rhs;
  ASSERT_NE(cast, nullptr);
  EXPECT_EQ(cast->kind, ExprKind::kCast);
  ASSERT_NE(cast->rhs, nullptr);
  EXPECT_EQ(cast->rhs->kind, ExprKind::kTypeRef);
  ASSERT_NE(cast->rhs->lhs, nullptr);
  EXPECT_EQ(cast->rhs->lhs->kind, ExprKind::kBinary);
  ASSERT_NE(cast->lhs, nullptr);
  EXPECT_EQ(cast->lhs->kind, ExprKind::kSelect);
}

// A.2.8 admits a data_declaration as a block item, and A.2.2.1 makes a
// type_reference one of its data types, so `var type(a) v = 7;` in an initial
// block and §6.23's `static type(this) m_inst;`, written with the `var` the
// clause requires, each declare a variable whose type is the reference.
TEST(TypeOperatorParsing, BlockItemVarTypeRefDeclarations) {
  auto r = Parse(
      "class registry;\n"
      "  static function registry get();\n"
      "    var static type(this) m_inst;\n"
      "    return m_inst;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int a;\n"
      "  initial begin\n"
      "    var type(a) v = 7, w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* get = r.cu->classes[0]->members[0]->method;
  ASSERT_NE(get, nullptr);
  ASSERT_FALSE(get->func_body_stmts.empty());
  auto* inst = get->func_body_stmts[0];
  EXPECT_EQ(inst->kind, StmtKind::kVarDecl);
  EXPECT_EQ(inst->var_name, "m_inst");
  EXPECT_TRUE(inst->var_is_static);
  ASSERT_NE(inst->var_decl_type.type_ref_expr, nullptr);
  EXPECT_EQ(inst->var_decl_type.type_ref_expr->text, "this");
  auto& body = r.cu->modules[0]->items[1]->body->stmts;
  ASSERT_EQ(body.size(), 2u);
  EXPECT_EQ(body[0]->var_name, "v");
  ASSERT_NE(body[0]->var_init, nullptr);
  EXPECT_EQ(body[1]->var_name, "w");
  for (auto* s : body) {
    EXPECT_EQ(s->kind, StmtKind::kVarDecl);
    ASSERT_NE(s->var_decl_type.type_ref_expr, nullptr);
    EXPECT_EQ(s->var_decl_type.type_ref_expr->text, "a");
  }
}

// The block-item counterpart of VarTypeRefWithoutVarKeywordRejected: a type
// reference without `var`, as §6.23's registry example writes `static
// type(this) m_inst;`, breaks footnote 18 of §6.8's Syntax 6-3, and the
// declaration draws that one report and nothing else.
TEST(TypeOperatorParsing, BlockItemTypeRefWithoutVarReportsOnce) {
  auto r = Parse(
      "class registry;\n"
      "  static function registry get();\n"
      "    static type(this) m_inst;\n"
      "    return m_inst;\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "type_reference in a variable declaration must be "
                            "preceded by the 'var' keyword",
                            3, "6.8"));
  EXPECT_EQ(std::count_if(r.diags.begin(), r.diags.end(),
                          [](const Diagnostic& d) {
                            return d.severity == DiagSeverity::kError;
                          }),
            1);
}

}  // namespace
