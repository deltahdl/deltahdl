#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult5b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult5b Parse(const std::string& src) {
  ParseResult5b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
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

static Stmt* FirstInitialStmt(ParseResult5b& r) {
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

static ModuleItem* FirstItem(ParseResult5b& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

// =========================================================================
// Section 5.6: Identifiers, keywords, and system names
// =========================================================================

// Section 5.6 -- Simple identifiers: letters, digits, _, $
TEST(ParserSection5, Ident_SimpleWithUnderscore) {
  auto r = Parse("module m; logic _bus3; endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "_bus3");
}

TEST(ParserSection5, Ident_SimpleWithDollarSign) {
  EXPECT_TRUE(ParseOk("module m; logic n$657; endmodule"));
}

TEST(ParserSection5, Ident_CaseSensitive) {
  // Identifiers are case sensitive: X and x are different.
  auto r = Parse(
      "module m;\n"
      "  logic X;\n"
      "  logic x;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "X");
  EXPECT_EQ(r.cu->modules[0]->items[1]->name, "x");
}

// =========================================================================
// Section 5.6.1: Escaped identifiers
// =========================================================================

TEST(ParserSection5, EscapedIdent_Basic) {
  EXPECT_TRUE(ParseOk("module m; wire \\busa+index ; endmodule"));
}

TEST(ParserSection5, EscapedIdent_Keyword) {
  // An escaped keyword is treated as a user-defined identifier, not as a
  // keyword. \net is a valid user-defined wire name.
  EXPECT_TRUE(ParseOk("module m; wire \\net ; endmodule"));
}

TEST(ParserSection5, EscapedIdent_SpecialChars) {
  // Escaped identifiers can contain any printable ASCII character.
  EXPECT_TRUE(
      ParseOk("module m; wire \\***error-condition*** ; endmodule"));
}

// =========================================================================
// Section 5.6.3: System tasks and system functions
// =========================================================================

TEST(ParserSection5, SystemTask_Display) {
  // $display is a system task call (Section 5.6.3, Section 21.2).
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"hello\");\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
}

TEST(ParserSection5, SystemTask_FinishNoArgs) {
  // $finish with no arguments and no parentheses.
  EXPECT_TRUE(ParseOk("module m; initial $finish; endmodule"));
}

TEST(ParserSection5, SystemFunction_InExpression) {
  // A system function like $clog2 used inside an expression.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter W = $clog2(256);\n"
              "endmodule"));
}

// =========================================================================
// Section 5.5: Operators
// =========================================================================

TEST(ParserSection5, Operator_UnaryBitwiseNegate) {
  auto r = Parse(
      "module m;\n"
      "  initial x = ~y;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
}

TEST(ParserSection5, Operator_BinaryAdd) {
  auto r = Parse(
      "module m;\n"
      "  initial x = a + b;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}

TEST(ParserSection5, Operator_Ternary) {
  auto r = Parse(
      "module m;\n"
      "  initial x = sel ? a : b;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  ASSERT_NE(rhs->true_expr, nullptr);
  ASSERT_NE(rhs->false_expr, nullptr);
}

// =========================================================================
// Section 5.6/5.12: Attributes on declarations
// =========================================================================

TEST(ParserSection5, Attribute_OnCaseStatement) {
  // Section 5.12 Example 1: full_case, parallel_case on a case statement.
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* full_case, parallel_case *)\n"
      "    case (a)\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_EQ(stmt->attrs.size(), 2u);
  EXPECT_EQ(stmt->attrs[0].name, "full_case");
  EXPECT_EQ(stmt->attrs[1].name, "parallel_case");
}

TEST(ParserSection5, Attribute_MultipleInstances) {
  // Multiple separate attribute instances before the same item.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  (* full_case=1 *)\n"
              "  (* parallel_case=1 *)\n"
              "  logic x;\n"
              "endmodule"));
}

TEST(ParserSection5, Attribute_OnModuleInstantiation) {
  // Section 5.12 Example 4: attribute on a module instantiation.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  (* optimize_power=0 *)\n"
              "  sub u1(.a(x));\n"
              "endmodule"));
}

// =========================================================================
// Section 5.6.2: Keywords - escaped keyword as identifier
// =========================================================================

TEST(ParserSection5, Keyword_EscapedAsIdentifier) {
  // An escaped keyword should be treated as a user-defined identifier.
  EXPECT_TRUE(ParseOk("module m; logic \\begin ; endmodule"));
}

TEST(ParserSection5, Keyword_AllLowercase) {
  // Keywords are lowercase only; MODULE is not a keyword, so this fails.
  EXPECT_FALSE(ParseOk("MODULE m; endmodule"));
}

// =========================================================================
// Section 5.7.1: Integer literal constants
// =========================================================================

TEST(ParserSection5, IntLiteral_UnsizedDecimal) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 659;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 659u);
}

TEST(ParserSection5, IntLiteral_SizedBinary) {
  // 4'b1001 is a 4-bit binary number.
  auto r = Parse(
      "module m;\n"
      "  initial x = 4'b1001;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0b1001u);
}

TEST(ParserSection5, IntLiteral_SizedHex) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 8'hFF;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0xFFu);
}

TEST(ParserSection5, IntLiteral_UnsizedHex) {
  // 'h 837FF -- unsized hexadecimal.
  EXPECT_TRUE(
      ParseOk("module m; initial x = 'h837FF; endmodule"));
}

TEST(ParserSection5, IntLiteral_SizedOctal) {
  EXPECT_TRUE(
      ParseOk("module m; initial x = 8'o77; endmodule"));
}

TEST(ParserSection5, IntLiteral_SignedLiteral) {
  // 4'shf is a signed 4-bit number (value -1 in two's complement).
  EXPECT_TRUE(
      ParseOk("module m; initial x = 4'shf; endmodule"));
}

TEST(ParserSection5, IntLiteral_UnbasedUnsized_One) {
  // '1 sets all bits to 1.
  auto r = Parse(
      "module m;\n"
      "  initial x = '1;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(ParserSection5, IntLiteral_UnbasedUnsized_Zero) {
  // '0 sets all bits to 0.
  EXPECT_TRUE(ParseOk("module m; initial x = '0; endmodule"));
}

TEST(ParserSection5, IntLiteral_Underscore) {
  // Underscores are legal anywhere except as first character.
  EXPECT_TRUE(
      ParseOk("module m; initial x = 16'b0011_0101_0001_1111; endmodule"));
}

TEST(ParserSection5, IntLiteral_XValue) {
  // 12'hx -- 12-bit unknown.
  EXPECT_TRUE(ParseOk("module m; initial x = 12'hx; endmodule"));
}

TEST(ParserSection5, IntLiteral_ZValue) {
  // 16'hz -- 16-bit high-impedance.
  EXPECT_TRUE(ParseOk("module m; initial x = 16'hz; endmodule"));
}

TEST(ParserSection5, IntLiteral_QuestionMark) {
  // ? is an alternative for z in literal constants.
  EXPECT_TRUE(
      ParseOk("module m; initial x = 16'sd?; endmodule"));
}

// =========================================================================
// Section 5.7.2: Real literal constants
// =========================================================================

TEST(ParserSection5, RealLiteral_DecimalNotation) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 14.72;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
  EXPECT_DOUBLE_EQ(rhs->real_val, 14.72);
}

TEST(ParserSection5, RealLiteral_ScientificNotation) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 1.30e-2;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
  EXPECT_DOUBLE_EQ(rhs->real_val, 0.013);
}

TEST(ParserSection5, RealLiteral_ExponentOnly) {
  // 39e8 is a valid real constant (exponent notation without decimal point).
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r;\n"
              "  initial r = 39e8;\n"
              "endmodule"));
}

// =========================================================================
// Section 5.8: Time literals
// =========================================================================

TEST(ParserSection5, TimeLiteral_IntegerNs) {
  auto r = Parse(
      "module m;\n"
      "  initial #40ns;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
}

TEST(ParserSection5, TimeLiteral_FixedPointNs) {
  // 2.1ns -- a time literal with a fixed-point value.
  EXPECT_TRUE(
      ParseOk("module m; initial #2.1ns; endmodule"));
}

TEST(ParserSection5, TimeLiteral_Ps) {
  EXPECT_TRUE(
      ParseOk("module m; initial #40ps; endmodule"));
}

// =========================================================================
// Section 5.9: String literals
// =========================================================================

TEST(ParserSection5, StringLiteral_Basic) {
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"hello world\");\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  ASSERT_GE(stmt->expr->args.size(), 1u);
  EXPECT_EQ(stmt->expr->args[0]->kind, ExprKind::kStringLiteral);
}

TEST(ParserSection5, StringLiteral_Assignment) {
  // A string literal can be assigned to an integral type.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  byte c1;\n"
              "  initial c1 = \"A\";\n"
              "endmodule"));
}

TEST(ParserSection5, StringLiteral_PackedArray) {
  // Storing a string in a packed array, per LRM Section 5.9.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  bit [8*12:1] stringvar = \"Hello world\\n\";\n"
              "endmodule"));
}

// =========================================================================
// Section 5.9.1: Special characters in strings
// =========================================================================

TEST(ParserSection5, StringEscape_Newline) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"line1\\nline2\");\n"
              "endmodule"));
}

TEST(ParserSection5, StringEscape_Tab) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"col1\\tcol2\");\n"
              "endmodule"));
}

TEST(ParserSection5, StringEscape_Quote) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"say \\\"hello\\\"\");\n"
              "endmodule"));
}

// =========================================================================
// Section 5.10: Structure literals
// =========================================================================

TEST(ParserSection5, StructLiteral_Positional) {
  // c = '{0, 0.0}; -- positional structure literal.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; shortreal b;} ab;\n"
              "  ab c;\n"
              "  initial c = '{0, 0.0};\n"
              "endmodule"));
}

TEST(ParserSection5, StructLiteral_NestedBraces) {
  // ab abarr[1:0] = '{'{1, 1.0}, '{2, 2.0}};
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; shortreal b;} ab;\n"
              "  ab abarr[1:0] = '{'{1, 1.0}, '{2, 2.0}};\n"
              "endmodule"));
}

TEST(ParserSection5, StructLiteral_MemberNameAndValue) {
  // c = '{a:0, b:0.0}; -- member name and value.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; shortreal b;} ab;\n"
              "  ab c;\n"
              "  initial c = '{a:0, b:0.0};\n"
              "endmodule"));
}

// =========================================================================
// Section 5.11: Array literals
// =========================================================================

TEST(ParserSection5, ArrayLiteral_Nested) {
  // int n[1:2][1:3] = '{'{0,1,2},'{3{4}}};
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int n[1:2][1:3] = '{'{0,1,2},'{3{4}}};\n"
              "endmodule"));
}

TEST(ParserSection5, ArrayLiteral_Simple) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int arr[0:2] = '{10, 20, 30};\n"
              "endmodule"));
}

TEST(ParserSection5, ArrayLiteral_DefaultValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int arr[0:3] = '{default:0};\n"
              "endmodule"));
}

// =========================================================================
// Section 5.12: Attributes on statements (Section 5.6.3)
// =========================================================================

TEST(ParserSection5, Attribute_OnIfStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* synthesis_off *)\n"
      "    if (a) x = 1;\n"
      "  end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_EQ(stmt->attrs.size(), 1u);
  EXPECT_EQ(stmt->attrs[0].name, "synthesis_off");
}

TEST(ParserSection5, Attribute_OnForLoop) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    (* unroll *)\n"
              "    for (int i = 0; i < 4; i++) x = i;\n"
              "  end\n"
              "endmodule"));
}

TEST(ParserSection5, Attribute_OnAssignment) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    (* mark *) x = 1;\n"
              "  end\n"
              "endmodule"));
}

// =========================================================================
// Section 5.12: Attributes on port connections (Section 5.6.4)
// =========================================================================

TEST(ParserSection5, Attribute_OnPortConnection) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sub u1(.a(x), (* no_connect *) .b(y));\n"
              "endmodule"));
}

TEST(ParserSection5, Attribute_OnContAssign) {
  // Attribute on a continuous assignment statement.
  auto r = Parse(
      "module m;\n"
      "  logic a, b;\n"
      "  (* synthesis_on *)\n"
      "  assign a = b;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
  auto* item = r.cu->modules[0]->items[2];
  EXPECT_EQ(item->kind, ModuleItemKind::kContAssign);
  ASSERT_EQ(item->attrs.size(), 1u);
  EXPECT_EQ(item->attrs[0].name, "synthesis_on");
}

// =========================================================================
// Section 5.13: Built-in methods
// =========================================================================

TEST(ParserSection5, BuiltInMethod_NoParens) {
  // When a method has no arguments the parentheses are optional.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial x = q.size;\n"
              "endmodule"));
}

TEST(ParserSection5, BuiltInMethod_ChainedAccess) {
  // Chained member accesses: a.b.c().
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial x = obj.sub.method();\n"
              "endmodule"));
}

TEST(ParserSection5, BuiltInMethod_WithArgs) {
  // Built-in method with arguments: arr.find with (item > 3).
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial q.sort();\n"
              "endmodule"));
}

// =========================================================================
// Section 5.5: Triple-character operators
// =========================================================================

TEST(ParserSection5, Operator_LogicalShiftLeft) {
  EXPECT_TRUE(
      ParseOk("module m; initial x = a <<< 2; endmodule"));
}

TEST(ParserSection5, Operator_ArithShiftRight) {
  EXPECT_TRUE(
      ParseOk("module m; initial x = a >>> 1; endmodule"));
}

TEST(ParserSection5, Operator_CaseEquality) {
  // === is the case equality operator.
  auto r = Parse(
      "module m;\n"
      "  initial x = (a === b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kEqEqEq);
}

TEST(ParserSection5, Operator_CaseInequality) {
  // !== is the case inequality operator.
  EXPECT_TRUE(
      ParseOk("module m; initial x = (a !== b); endmodule"));
}

// =========================================================================
// Additional Section 5.7.1: Negative integer literals
// =========================================================================

TEST(ParserSection5, IntLiteral_NegativeUnsized) {
  // -8'd6 defines the two's-complement of 6 held in 8 bits.
  EXPECT_TRUE(
      ParseOk("module m; initial x = -8'd6; endmodule"));
}

TEST(ParserSection5, IntLiteral_SizedDecimal) {
  // 5'D 3 is a 5-bit decimal number.
  EXPECT_TRUE(
      ParseOk("module m; initial x = 5'D3; endmodule"));
}

// =========================================================================
// Section 5.12: Attribute value is a constant expression
// =========================================================================

TEST(ParserSection5, AttributeValue_ConstExpr) {
  // The attribute value can be an arbitrary constant expression.
  auto r = Parse(
      "module m;\n"
      "  (* depth = 3 + 1 *)\n"
      "  logic [7:0] mem;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->attrs.size(), 1u);
  EXPECT_EQ(item->attrs[0].name, "depth");
  ASSERT_NE(item->attrs[0].value, nullptr);
  EXPECT_EQ(item->attrs[0].value->kind, ExprKind::kBinary);
}

TEST(ParserSection5, AttributeValue_String) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  (* tool_purpose = \"synthesis\" *)\n"
              "  logic x;\n"
              "endmodule"));
}

// =========================================================================
// Section 5.10/5.11: Assignment pattern with type-cast prefix
// =========================================================================

TEST(ParserSection5, AssignmentPattern_TypeCastPrefix) {
  // d = ab'{int:1, shortreal:1.0};
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; shortreal b;} ab;\n"
              "  ab d;\n"
              "  initial d = ab'{int:1, shortreal:1.0};\n"
              "endmodule"));
}

TEST(ParserSection5, AssignmentPattern_EmptyRejected) {
  // An empty assignment pattern should be rejected.
  EXPECT_FALSE(ParseOk("module m; initial x = '{}; endmodule"));
}

// =========================================================================
// Section 5.5: Unary reduction operators
// =========================================================================

TEST(ParserSection5, Operator_ReductionAnd) {
  auto r = Parse(
      "module m;\n"
      "  initial x = &y;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
}

TEST(ParserSection5, Operator_ReductionXnor) {
  EXPECT_TRUE(
      ParseOk("module m; initial x = ~^y; endmodule"));
}

// =========================================================================
// Section 5.8: Time literals with all units
// =========================================================================

TEST(ParserSection5, TimeLiteral_Us) {
  EXPECT_TRUE(ParseOk("module m; initial #100us; endmodule"));
}

TEST(ParserSection5, TimeLiteral_Ms) {
  EXPECT_TRUE(ParseOk("module m; initial #1ms; endmodule"));
}

TEST(ParserSection5, TimeLiteral_Fs) {
  EXPECT_TRUE(ParseOk("module m; initial #500fs; endmodule"));
}

// =========================================================================
// Section 5.9: String literal as parameter value
// =========================================================================

TEST(ParserSection5, StringLiteral_AsParameter) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter string MSG = \"default message\";\n"
              "endmodule"));
}

TEST(ParserSection5, StringLiteral_InConcatenation) {
  // String concatenation using system task.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display({\"A\", \"B\"});\n"
              "endmodule"));
}

// =========================================================================
// Section 5.12: Multiple attribute instances on same element
// =========================================================================

TEST(ParserSection5, Attribute_MultipleSeparateInstances) {
  // Multiple attribute instances are merged.
  auto r = Parse(
      "module m;\n"
      "  (* first *)\n"
      "  (* second *)\n"
      "  logic x;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->attrs.size(), 2u);
  EXPECT_EQ(item->attrs[0].name, "first");
  EXPECT_EQ(item->attrs[1].name, "second");
}

// =========================================================================
// Section 5.6.1: Escaped identifier with forward slash
// =========================================================================

TEST(ParserSection5, EscapedIdent_ForwardSlash) {
  // \net1/\net2 is a valid escaped identifier containing a slash.
  EXPECT_TRUE(
      ParseOk("module m; wire \\net1/\\net2 ; endmodule"));
}

TEST(ParserSection5, EscapedIdent_Braces) {
  // \{a,b} is a valid escaped identifier containing braces.
  EXPECT_TRUE(
      ParseOk("module m; wire \\{a,b} ; endmodule"));
}

// =========================================================================
// Section 5.13: Built-in method on dynamic array
// =========================================================================

TEST(ParserSection5, BuiltInMethod_Delete) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial q.delete();\n"
              "endmodule"));
}

TEST(ParserSection5, BuiltInMethod_PushBack) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial q.push_back(42);\n"
              "endmodule"));
}

// =========================================================================
// Section 5.5: Power operator **
// =========================================================================

TEST(ParserSection5, Operator_Power) {
  EXPECT_TRUE(
      ParseOk("module m; initial x = 2 ** 10; endmodule"));
}

TEST(ParserSection5, Operator_WildcardEquality) {
  // ==? is the wildcard equality operator.
  EXPECT_TRUE(
      ParseOk("module m; initial x = (a ==? b); endmodule"));
}

// =========================================================================
// Section 5.7.1: Hex literal with whitespace between base and digits
// =========================================================================

TEST(ParserSection5, IntLiteral_SpaceBetweenBaseAndDigits) {
  // Space between base format and unsigned number is legal.
  EXPECT_TRUE(
      ParseOk("module m; initial x = 32 'h 12ab_f001; endmodule"));
}

TEST(ParserSection5, IntLiteral_LargeUnsized) {
  // 'h7_0000_0000 requires at least 35 bits.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [63:0] big;\n"
              "  initial big = 'h7_0000_0000;\n"
              "endmodule"));
}
