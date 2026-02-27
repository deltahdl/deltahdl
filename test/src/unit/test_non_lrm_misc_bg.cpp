// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserCh50603, SystemTask_FinishNoArgs) {
  // $finish with no arguments and no parentheses.
  EXPECT_TRUE(ParseOk("module m; initial $finish; endmodule"));
}

TEST(ParserCh50603, SystemFunction_InExpression) {
  // A system function like $clog2 used inside an expression.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter W = $clog2(256);\n"
              "endmodule"));
}

// --- §5.7.1 Integer literal constants ---
struct ParseResult50701 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult50701 Parse(const std::string& src) {
  ParseResult50701 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult50701& r) {
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

struct ParseDiag50701 {
  SourceManager mgr;
  Arena arena;
  DiagEngine* diag = nullptr;
  CompilationUnit* cu = nullptr;
};

static ParseDiag50701 ParseWithDiag(const std::string& src) {
  ParseDiag50701 result;
  auto fid = result.mgr.AddFile("<test>", src);
  result.diag = new DiagEngine(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, *result.diag);
  Parser parser(lexer, result.arena, *result.diag);
  result.cu = parser.Parse();
  return result;
}

// From test_parser_clause_05.cpp
TEST(ParserCh50701, SizedLiteral_NoOverflow) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 4'hF;\n"
      "endmodule\n");
  EXPECT_EQ(r.diag->WarningCount(), 0u);
  delete r.diag;
}

TEST(ParserCh50701, SizedLiteral_Overflow_Warning) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 4'hFF;\n"
      "endmodule\n");
  EXPECT_GE(r.diag->WarningCount(), 1u);
  delete r.diag;
}

TEST(ParserCh50701, SizedLiteral_ExactFit) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 8'hFF;\n"
      "endmodule\n");
  EXPECT_EQ(r.diag->WarningCount(), 0u);
  delete r.diag;
}

TEST(ParserCh50701, SizedLiteral_OneBitOverflow) {
  auto r = ParseWithDiag(
      "module t;\n"
      "  initial x = 3'b1111;\n"
      "endmodule\n");
  EXPECT_GE(r.diag->WarningCount(), 1u);
  delete r.diag;
}

// From test_parser_clause_05b.cpp
TEST(ParserCh50701, IntLiteral_UnsizedDecimal) {
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

TEST(ParserCh50701, IntLiteral_SizedBinary) {
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

TEST(ParserCh50701, IntLiteral_SizedHex) {
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

TEST(ParserCh50701, IntLiteral_UnsizedHex) {
  // 'h 837FF -- unsized hexadecimal.
  EXPECT_TRUE(ParseOk("module m; initial x = 'h837FF; endmodule"));
}

TEST(ParserCh50701, IntLiteral_SizedOctal) {
  EXPECT_TRUE(ParseOk("module m; initial x = 8'o77; endmodule"));
}

TEST(ParserCh50701, IntLiteral_SignedLiteral) {
  // 4'shf is a signed 4-bit number (value -1 in two's complement).
  EXPECT_TRUE(ParseOk("module m; initial x = 4'shf; endmodule"));
}

TEST(ParserCh50701, IntLiteral_UnbasedUnsized_One) {
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

TEST(ParserCh50701, IntLiteral_UnbasedUnsized_Zero) {
  // '0 sets all bits to 0.
  EXPECT_TRUE(ParseOk("module m; initial x = '0; endmodule"));
}

TEST(ParserCh50701, IntLiteral_Underscore) {
  // Underscores are legal anywhere except as first character.
  EXPECT_TRUE(
      ParseOk("module m; initial x = 16'b0011_0101_0001_1111; endmodule"));
}

TEST(ParserCh50701, IntLiteral_XValue) {
  // 12'hx -- 12-bit unknown.
  EXPECT_TRUE(ParseOk("module m; initial x = 12'hx; endmodule"));
}

TEST(ParserCh50701, IntLiteral_ZValue) {
  // 16'hz -- 16-bit high-impedance.
  EXPECT_TRUE(ParseOk("module m; initial x = 16'hz; endmodule"));
}

TEST(ParserCh50701, IntLiteral_QuestionMark) {
  // ? is an alternative for z in literal constants.
  EXPECT_TRUE(ParseOk("module m; initial x = 16'sd?; endmodule"));
}

TEST(ParserCh50701, IntLiteral_NegativeUnsized) {
  // -8'd6 defines the two's-complement of 6 held in 8 bits.
  EXPECT_TRUE(ParseOk("module m; initial x = -8'd6; endmodule"));
}

TEST(ParserCh50701, IntLiteral_SizedDecimal) {
  // 5'D 3 is a 5-bit decimal number.
  EXPECT_TRUE(ParseOk("module m; initial x = 5'D3; endmodule"));
}

TEST(ParserCh50701, IntLiteral_SpaceBetweenBaseAndDigits) {
  // Space between base format and unsigned number is legal.
  EXPECT_TRUE(ParseOk("module m; initial x = 32 'h 12ab_f001; endmodule"));
}

TEST(ParserCh50701, IntLiteral_LargeUnsized) {
  // 'h7_0000_0000 requires at least 35 bits.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [63:0] big;\n"
              "  initial big = 'h7_0000_0000;\n"
              "endmodule"));
}

// =========================================================================
// Section 5.7.2: Real literal constants
// =========================================================================
struct ParseResult50702 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult50702 Parse(const std::string& src) {
  ParseResult50702 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult50702& r) {
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

TEST(ParserCh50702, RealLiteral_DecimalNotation) {
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

TEST(ParserCh50702, RealLiteral_ScientificNotation) {
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

TEST(ParserCh50702, RealLiteral_ExponentOnly) {
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
struct ParseResult508 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult508 Parse(const std::string& src) {
  ParseResult508 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult508& r) {
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

TEST(ParserCh508, TimeLiteral_IntegerNs) {
  auto r = Parse(
      "module m;\n"
      "  initial #40ns;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
}

TEST(ParserCh508, TimeLiteral_FixedPointNs) {
  // 2.1ns -- a time literal with a fixed-point value.
  EXPECT_TRUE(ParseOk("module m; initial #2.1ns; endmodule"));
}

TEST(ParserCh508, TimeLiteral_Ps) {
  EXPECT_TRUE(ParseOk("module m; initial #40ps; endmodule"));
}

TEST(ParserCh508, TimeLiteral_Us) {
  EXPECT_TRUE(ParseOk("module m; initial #100us; endmodule"));
}

TEST(ParserCh508, TimeLiteral_Ms) {
  EXPECT_TRUE(ParseOk("module m; initial #1ms; endmodule"));
}

TEST(ParserCh508, TimeLiteral_Fs) {
  EXPECT_TRUE(ParseOk("module m; initial #500fs; endmodule"));
}

// delay_value: time_literal — time literal (e.g. 10ns) as delay.
TEST(ParserA223, DelayValueTimeLiteral) {
  auto r = Parse(
      "module m;\n"
      "  wire #10ns w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->kind, ExprKind::kTimeLiteral);
}

// Time literal variants in delay: fs, ps, ns, us, ms, s.
TEST(ParserA223, DelayValueAllTimeLiterals) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire #1fs w1;\n"
              "  wire #2ps w2;\n"
              "  wire #3ns w3;\n"
              "  wire #4us w4;\n"
              "  wire #5ms w5;\n"
              "  wire #6s w6;\n"
              "endmodule"));
}

// =========================================================================
// Section 5.9: String literals
// =========================================================================
struct ParseResult509 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult509 Parse(const std::string& src) {
  ParseResult509 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult509& r) {
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

TEST(ParserCh509, StringLiteral_Basic) {
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

TEST(ParserCh509, StringLiteral_Assignment) {
  // A string literal can be assigned to an integral type.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  byte c1;\n"
              "  initial c1 = \"A\";\n"
              "endmodule"));
}

TEST(ParserCh509, StringLiteral_PackedArray) {
  // Storing a string in a packed array, per LRM Section 5.9.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  bit [8*12:1] stringvar = \"Hello world\\n\";\n"
              "endmodule"));
}

TEST(ParserCh509, StringLiteral_AsParameter) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter string MSG = \"default message\";\n"
              "endmodule"));
}

TEST(ParserCh509, StringLiteral_InConcatenation) {
  // String concatenation using system task.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display({\"A\", \"B\"});\n"
              "endmodule"));
}

TEST(ParserCh50901, StringEscape_Newline) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"line1\\nline2\");\n"
              "endmodule"));
}

TEST(ParserCh50901, StringEscape_Tab) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"col1\\tcol2\");\n"
              "endmodule"));
}

TEST(ParserCh50901, StringEscape_Quote) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"say \\\"hello\\\"\");\n"
              "endmodule"));
}

// --- §5.10 Structure literals ---
struct ParseResult510 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult510 Parse(const std::string& src) {
  ParseResult510 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult510& r) {
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

static void VerifyPatternKeys(const Expr* rhs,
                              const std::string expected_keys[], size_t count) {
  ASSERT_EQ(rhs->pattern_keys.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(rhs->pattern_keys[i], expected_keys[i]) << "key " << i;
  }
}

// From test_parser_clause_05.cpp
TEST(ParserCh510, AssignmentPatternPositional_Parse) {
  auto r = Parse(
      "module t;\n"
      "  initial x = '{1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
}

TEST(ParserCh510, AssignmentPatternPositional_Elements) {
  auto r = Parse(
      "module t;\n"
      "  initial x = '{1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->elements.size(), 3u);
  EXPECT_TRUE(rhs->pattern_keys.empty());
}

TEST(ParserCh510, AssignmentPatternNamed) {
  auto r = Parse(
      "module t;\n"
      "  initial x = '{a: 0, b: 1};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements.size(), 2u);
  std::string expected_keys[] = {"a", "b"};
  VerifyPatternKeys(rhs, expected_keys, std::size(expected_keys));
}

TEST(ParserCh510, AssignmentPatternDefault) {
  auto r = Parse(
      "module t;\n"
      "  initial x = '{default: 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  std::string expected_keys[] = {"default"};
  VerifyPatternKeys(rhs, expected_keys, std::size(expected_keys));
}

TEST(ParserCh510, AssignmentPattern_TypeKey) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { int x; int y; } ms_t;\n"
              "  ms_t ms = '{int:0, int:1};\n"
              "endmodule"));
}

TEST(ParserCh510, AssignmentPattern_DefaultKey) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { int x; int y; } ms_t;\n"
              "  ms_t ms = '{default:1};\n"
              "endmodule"));
}

TEST(ParserCh510, AssignmentPattern_IntKey) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef int triple[1:3];\n"
              "  triple t = '{1:1, default:0};\n"
              "endmodule"));
}

TEST(ParserCh510, AssignmentPattern_Replication) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int a[1:3] = '{3{1}};\n"
              "endmodule"));
}

TEST(ParserCh510, AssignmentPattern_NestedReplication) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int n[1:2][1:6] = '{2{'{3{4, 5}}}};\n"
              "endmodule"));
}

// From test_parser_clause_05b.cpp
TEST(ParserCh510, StructLiteral_Positional) {
  // c = '{0, 0.0}; -- positional structure literal.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; shortreal b;} ab;\n"
              "  ab c;\n"
              "  initial c = '{0, 0.0};\n"
              "endmodule"));
}

TEST(ParserCh510, StructLiteral_NestedBraces) {
  // ab abarr[1:0] = '{'{1, 1.0}, '{2, 2.0}};
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; shortreal b;} ab;\n"
              "  ab abarr[1:0] = '{'{1, 1.0}, '{2, 2.0}};\n"
              "endmodule"));
}

TEST(ParserCh510, StructLiteral_MemberNameAndValue) {
  // c = '{a:0, b:0.0}; -- member name and value.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; shortreal b;} ab;\n"
              "  ab c;\n"
              "  initial c = '{a:0, b:0.0};\n"
              "endmodule"));
}

TEST(ParserCh511, ArrayLiteral_Nested) {
  // int n[1:2][1:3] = '{'{0,1,2},'{3{4}}};
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int n[1:2][1:3] = '{'{0,1,2},'{3{4}}};\n"
              "endmodule"));
}

TEST(ParserCh511, ArrayLiteral_Simple) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int arr[0:2] = '{10, 20, 30};\n"
              "endmodule"));
}

TEST(ParserCh511, ArrayLiteral_DefaultValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int arr[0:3] = '{default:0};\n"
              "endmodule"));
}

// --- §5.12 Attributes ---
struct ParseResult512 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult512 Parse(const std::string& src) {
  ParseResult512 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult512& r) {
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

static ModuleItem* FirstItem(ParseResult512& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

static void VerifyAttrNames(const ModuleItem* item,
                            const std::string expected_names[], size_t count) {
  ASSERT_EQ(item->attrs.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(item->attrs[i].name, expected_names[i]) << "attr " << i;
  }
}

// From test_parser_clause_05.cpp
TEST(ParserCh512, AttributeOnModuleItem) {
  auto r = Parse(
      "module t;\n"
      "  (* full_case *)\n"
      "  logic [7:0] x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->attrs.size(), 1u);
  EXPECT_EQ(item->attrs[0].name, "full_case");
  EXPECT_EQ(item->attrs[0].value, nullptr);
}

TEST(ParserCh512, AttributeWithValue_Names) {
  auto r = Parse(
      "module t;\n"
      "  (* synthesis, optimize_power = 1 *)\n"
      "  logic y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  std::string expected_names[] = {"synthesis", "optimize_power"};
  VerifyAttrNames(r.cu->modules[0]->items[0], expected_names,
                  std::size(expected_names));
}

TEST(ParserCh512, AttributeWithValue_Values) {
  auto r = Parse(
      "module t;\n"
      "  (* synthesis, optimize_power = 1 *)\n"
      "  logic y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->attrs.size(), 2u);
  EXPECT_EQ(item->attrs[0].value, nullptr);
  ASSERT_NE(item->attrs[1].value, nullptr);
}

TEST(ParserCh512, TopLevel_AttributeBeforeModule) {
  EXPECT_TRUE(ParseOk("(* optimize_power *) module m; endmodule"));
}

TEST(ParserCh512, TopLevel_TrailingSemicolonAfterEndmodule) {
  EXPECT_TRUE(ParseOk("module m; endmodule;"));
}

TEST(ParserCh512, Expr_AttributeOnOperator) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, c;\n"
              "  assign a = b + (* mode = \"cla\" *) c;\n"
              "endmodule"));
}

TEST(ParserCh512, Expr_AttributeOnTernary) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, c, d;\n"
              "  assign a = b ? (* no_glitch *) c : d;\n"
              "endmodule"));
}

TEST(ParserCh512, PostfixFunctionAttribute) {
  // §5.12 Example 7: a = add (* mode = "cla" *) (b, c);
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic a, b, c;\n"
              "  initial a = add (* mode = \"cla\" *) (b, c);\n"
              "endmodule\n"));
}

TEST(ParserCh512, PostfixFunctionAttribute_NoArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic a;\n"
              "  initial a = foo (* bar *) ();\n"
              "endmodule\n"));
}

TEST(ParserCh512, NestedAttribute_Error) {
  // §5.12: Nesting of attribute instances is disallowed.
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  (* foo = 1 + (* bar *) 2 *) logic x;\n"
              "endmodule\n"));
}

TEST(ParserCh512, AttributeValue_NoNesting_Ok) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  (* foo = 1 + 2 *) logic x;\n"
              "endmodule\n"));
}

// From test_parser_clause_05b.cpp
TEST(ParserCh512, Attribute_OnCaseStatement) {
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

TEST(ParserCh512, Attribute_MultipleInstances) {
  // Multiple separate attribute instances before the same item.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  (* full_case=1 *)\n"
              "  (* parallel_case=1 *)\n"
              "  logic x;\n"
              "endmodule"));
}

TEST(ParserCh512, Attribute_OnModuleInstantiation) {
  // Section 5.12 Example 4: attribute on a module instantiation.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  (* optimize_power=0 *)\n"
              "  sub u1(.a(x));\n"
              "endmodule"));
}

TEST(ParserCh512, Attribute_OnIfStatement) {
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

TEST(ParserCh512, Attribute_OnForLoop) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    (* unroll *)\n"
              "    for (int i = 0; i < 4; i++) x = i;\n"
              "  end\n"
              "endmodule"));
}

TEST(ParserCh512, Attribute_OnAssignment) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    (* mark *) x = 1;\n"
              "  end\n"
              "endmodule"));
}

TEST(ParserCh512, Attribute_OnPortConnection) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sub u1(.a(x), (* no_connect *) .b(y));\n"
              "endmodule"));
}

TEST(ParserCh512, Attribute_OnContAssign) {
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

TEST(ParserCh512, AttributeValue_ConstExpr) {
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

TEST(ParserCh512, AttributeValue_String) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  (* tool_purpose = \"synthesis\" *)\n"
              "  logic x;\n"
              "endmodule"));
}

TEST(ParserCh512, Attribute_MultipleSeparateInstances) {
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

}  // namespace
