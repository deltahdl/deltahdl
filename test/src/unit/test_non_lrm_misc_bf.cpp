// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

static bool ParseOk5(const std::string& src) {
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
// Section 5.6: Identifiers, keywords, and system names
// =========================================================================
struct ParseResult506 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ModuleItem* FirstItem(ParseResult506& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

// =========================================================================
// Section 5.6.3: System tasks and system functions
// =========================================================================
struct ParseResult50603 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult50603 Parse(const std::string& src) {
  ParseResult50603 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult50603& r) {
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

// =============================================================================
// 28. Function without explicit lifetime (default — static in module)
// =============================================================================
TEST(ParserSection4, Sec4_9_4_FuncNoExplicitLifetime) {
  auto r = Parse(
      "module m;\n"
      "  function int adder(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FirstFuncOrTask(r);
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(fn->kind, ModuleItemKind::kFunctionDecl);
  // No explicit lifetime — both flags should be false.
  EXPECT_FALSE(fn->is_static);
  EXPECT_FALSE(fn->is_automatic);
  EXPECT_EQ(fn->name, "adder");
}

// =============================================================================
// 29. Block-level var decl without explicit lifetime (plain int in block)
// =============================================================================
TEST(ParserSection4, Sec4_9_4_BlockVarDeclNoLifetime) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int plain_var = 99;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_FALSE(stmt->var_is_static);
  EXPECT_FALSE(stmt->var_is_automatic);
  EXPECT_EQ(stmt->var_decl_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(stmt->var_name, "plain_var");
  EXPECT_NE(stmt->var_init, nullptr);
}

// =============================================================================
// 30. Program block with function parses
// =============================================================================
TEST(ParserSection4, Sec4_9_4_ProgramWithFunction) {
  EXPECT_TRUE(
      ParseOk("program p;\n"
              "  function automatic int get_val();\n"
              "    automatic int v = 10;\n"
              "    return v;\n"
              "  endfunction\n"
              "  initial begin\n"
              "    $display(get_val());\n"
              "  end\n"
              "endprogram\n"));
}

// --- Unpacked range dimensions [M:N] ---
TEST(ParserCh5, UnpackedDim_Range) {
  EXPECT_TRUE(ParseOk5("module m; int a[1:0]; endmodule"));
}

TEST(ParserCh5, UnpackedDim_MultiRange) {
  EXPECT_TRUE(ParseOk5("module m; int a[1:2][1:3]; endmodule"));
}

TEST(ParserCh5, UnpackedDim_Typedef) {
  EXPECT_TRUE(ParseOk5("module m; typedef int triple[1:3]; endmodule"));
}

// --- Comma-separated struct members ---
TEST(ParserCh5, StructMembers_CommaSeparated) {
  auto r = Parse(
      "module m;\n"
      "  struct { int X, Y, Z; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.struct_members.size(), 3u);
}

TEST(ParserCh5, StructMembers_Single) {
  EXPECT_TRUE(ParseOk5("module m; struct { int X; } s; endmodule"));
}

// --- Null module items ---
TEST(ParserCh5, ModuleBody_NullItem) {
  EXPECT_TRUE(ParseOk5("module m; ; endmodule"));
}

TEST(ParserCh5, ModuleBody_SemicolonAfterEnd) {
  EXPECT_TRUE(ParseOk5("module m; initial begin end; endmodule"));
}

// =========================================================================
// White space as token delimiter
// =========================================================================
// Tab, newline, and space are all equivalent token delimiters.
TEST(ParserCh501, Sec5_1_WhitespaceTabDelimiter) {
  // Tabs instead of spaces between all tokens.
  EXPECT_TRUE(ParseOk("module\tt;\tlogic\ta;\tendmodule"));
}

TEST(ParserCh501, Sec5_1_WhitespaceNewlineDelimiter) {
  // Every token on its own line.
  EXPECT_TRUE(
      ParseOk("module\n"
              "t\n"
              ";\n"
              "logic\n"
              "a\n"
              ";\n"
              "endmodule\n"));
}

TEST(ParserCh501, Sec5_1_WhitespaceSpaceDelimiter) {
  // Single spaces between every token.
  EXPECT_TRUE(ParseOk("module t ; logic a ; endmodule"));
}

// =========================================================================
// White space inside string literals is preserved
// =========================================================================
TEST(ParserCh501, Sec5_1_WhitespaceInsideStringPreserved) {
  // Whitespace within a string literal must be preserved, not collapsed.
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"  hello   world  \");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  ASSERT_GE(stmt->expr->args.size(), 1u);
  EXPECT_EQ(stmt->expr->args[0]->kind, ExprKind::kStringLiteral);
  // The string text should contain the original whitespace.
  EXPECT_NE(stmt->expr->args[0]->text.find("  hello   world  "),
            std::string_view::npos);
}

// =========================================================================
// Multiple consecutive white space characters
// =========================================================================
TEST(ParserCh501, Sec5_1_MultipleConsecutiveWhitespace) {
  // Multiple spaces, tabs, and newlines between tokens are equivalent to one.
  EXPECT_TRUE(
      ParseOk("module   \t\t   t  \n\n\n ;   logic   a  ;   endmodule"));
}

// =========================================================================
// Empty module with different whitespace patterns
// =========================================================================
TEST(ParserCh501, Sec5_1_EmptyModuleMinimalWhitespace) {
  // Minimal whitespace: only where required to separate keywords.
  EXPECT_TRUE(ParseOk("module t;endmodule"));
}

TEST(ParserCh501, Sec5_1_EmptyModuleExcessiveWhitespace) {
  // Excessive whitespace everywhere around an empty module body.
  EXPECT_TRUE(
      ParseOk("  \t\n  module  \t  t  \n  ;  \n\n\t  endmodule  \n\n  "));
}

// =========================================================================
// Comments do NOT produce tokens
// =========================================================================
TEST(ParserCh501, Sec5_1_CommentDoesNotProduceTokens) {
  // A module containing only comments and no actual items parses cleanly.
  auto r = Parse(
      "module m;\n"
      "  // line comment\n"
      "  /* block comment */\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

// =========================================================================
// Line comment at end of file (no trailing newline)
// =========================================================================
TEST(ParserCh501, Sec5_1_LineCommentAtEofNoNewline) {
  // A line comment at EOF without a trailing newline must still parse.
  EXPECT_TRUE(ParseOk("module t; endmodule // trailing comment"));
}

// =========================================================================
// Block comment between tokens
// =========================================================================
TEST(ParserCh501, Sec5_1_BlockCommentBetweenTokens) {
  // Block comment placed between keyword tokens acts as whitespace.
  EXPECT_TRUE(ParseOk("module/* comment */t;/* another */endmodule"));
}

// =========================================================================
// Block comment inside expression (splitting operator from operand)
// =========================================================================
TEST(ParserCh501, Sec5_1_BlockCommentInsideExpression) {
  // Block comment between operands in a continuous assignment expression.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, c;\n"
              "  assign a = b /* comment */ + c;\n"
              "endmodule\n"));
}

// =========================================================================
// Nested /* inside line comment (not special)
// =========================================================================
TEST(ParserCh501, Sec5_1_NestedBlockCommentStartInsideLineComment) {
  // A /* inside a // comment is not treated as the start of a block comment.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  // this /* is not special\n"
              "  logic a;\n"
              "endmodule\n"));
}

// =========================================================================
// Adjacent line comments
// =========================================================================
TEST(ParserCh501, Sec5_1_AdjacentLineComments) {
  // Multiple consecutive line comments behave as whitespace.
  auto r = Parse(
      "module m;\n"
      "  // first comment\n"
      "  // second comment\n"
      "  // third comment\n"
      "  logic a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "a");
}

// =========================================================================
// All single-char operators parse correctly
// =========================================================================
TEST(ParserCh501, Sec5_1_SingleCharOperators) {
  // Exercise +, -, *, /, %, &, |, ^, ~ as single-character operators.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = a + b;\n"
              "    x = a - b;\n"
              "    x = a * b;\n"
              "    x = a / b;\n"
              "    x = a % b;\n"
              "    x = a & b;\n"
              "    x = a | b;\n"
              "    x = a ^ b;\n"
              "    x = ~a;\n"
              "  end\n"
              "endmodule\n"));
}

// =========================================================================
// All two-char operators
// =========================================================================
TEST(ParserCh501, Sec5_1_TwoCharOperators) {
  // Exercise ==, !=, <=, >=, &&, ||, <<, >>, +=, -=, *=, /=, etc.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = (a == b);\n"
              "    x = (a != b);\n"
              "    x = (a <= b);\n"
              "    x = (a >= b);\n"
              "    x = (a && b);\n"
              "    x = (a || b);\n"
              "    x = a << 1;\n"
              "    x = a >> 1;\n"
              "    a += 1;\n"
              "    a -= 1;\n"
              "    a *= 2;\n"
              "    a /= 2;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserCh501, Sec5_1_TwoCharOperatorTokenKinds) {
  // Verify the specific TokenKind for == in an expression.
  auto r = Parse(
      "module m;\n"
      "  initial x = (a == b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kEqEq);
}

// =========================================================================
// All three-char operators
// =========================================================================
TEST(ParserCh501, Sec5_1_ThreeCharOperators) {
  // ===, !==, <<<, >>>, ==?, !=?
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = (a === b);\n"
              "    x = (a !== b);\n"
              "    x = a <<< 2;\n"
              "    x = a >>> 2;\n"
              "    x = (a ==? b);\n"
              "    x = (a !=? b);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserCh501, Sec5_1_ThreeCharOperatorWildcardInequality) {
  // Verify !=? parses to the correct token kind.
  auto r = Parse(
      "module m;\n"
      "  initial x = (a !=? b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kBangEqQuestion);
}

// =========================================================================
// Keywords are reserved words
// =========================================================================
TEST(ParserCh501, Sec5_1_KeywordsAreReserved) {
  // module, endmodule, wire, logic, assign, initial, begin, end, if, else
  // are all reserved keywords that parse correctly.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire w;\n"
              "  logic l;\n"
              "  assign w = 0;\n"
              "  initial begin\n"
              "    if (l) w = 1;\n"
              "    else w = 0;\n"
              "  end\n"
              "endmodule\n"));
}

// =========================================================================
// Identifiers with all legal characters: letters, digits, _, $
// =========================================================================
TEST(ParserCh501, Sec5_1_IdentifierAllLegalChars) {
  // An identifier may contain letters, digits, underscore, and dollar sign.
  auto r = Parse("module m; logic abc_123$xyz; endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "abc_123$xyz");
}

// =========================================================================
// Simple identifiers starting with underscore
// =========================================================================
TEST(ParserCh501, Sec5_1_IdentifierStartsWithUnderscore) {
  auto r = Parse("module m; logic _start_val; endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "_start_val");
}

// =========================================================================
// Identifiers starting with letter
// =========================================================================
TEST(ParserCh501, Sec5_1_IdentifierStartsWithLetter) {
  auto r = Parse("module m; logic Data0; endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "Data0");
}

// =========================================================================
// Number followed by identifier (separate tokens)
// =========================================================================
TEST(ParserCh501, Sec5_1_NumberFollowedByIdentifier) {
  // "42" and "abc" are separate tokens even without whitespace between the
  // numeric literal and an identifier in expression context.
  auto r = Parse(
      "module m;\n"
      "  initial x = 42 + abc;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
  // LHS should be integer literal 42.
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->lhs->int_val, 42u);
  // RHS should be identifier abc.
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

// =========================================================================
// Operator followed immediately by number
// =========================================================================
TEST(ParserCh501, Sec5_1_OperatorFollowedByNumber) {
  // No space between operator and number: "a+1" must tokenize correctly.
  auto r = Parse(
      "module m;\n"
      "  initial x = a+1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->rhs->int_val, 1u);
}

// =========================================================================
// Mixed tokens without whitespace where unambiguous
// =========================================================================
TEST(ParserCh501, Sec5_1_MixedTokensNoWhitespace) {
  // Whitespace is only required where absence would create ambiguity.
  // Operators and punctuation are self-delimiting.
  EXPECT_TRUE(ParseOk("module m;logic a;assign a=1'b0;endmodule"));
}

// =========================================================================
// Multiple statements on one line
// =========================================================================
TEST(ParserCh501, Sec5_1_MultipleStatementsOnOneLine) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = 1; y = 2; z = 3; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->kind, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 3u);
}

// =========================================================================
// Statement spanning many lines
// =========================================================================
TEST(ParserCh501, Sec5_1_StatementSpanningManyLines) {
  // A single continuous assignment split across many lines.
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c, d;\n"
      "  assign\n"
      "    a\n"
      "    =\n"
      "    b\n"
      "    +\n"
      "    c\n"
      "    +\n"
      "    d\n"
      "    ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  // The declarations produce 4 items (a,b,c,d) and the assign produces 1.
  ASSERT_GE(r.cu->modules[0]->items.size(), 5u);
  auto* assign_item = r.cu->modules[0]->items[4];
  EXPECT_EQ(assign_item->kind, ModuleItemKind::kContAssign);
}

// =========================================================================
// Tab characters as whitespace
// =========================================================================
TEST(ParserCh501, Sec5_1_TabCharactersAsWhitespace) {
  // Tabs used throughout instead of spaces.
  EXPECT_TRUE(
      ParseOk("module\tm;\n"
              "\tlogic\ta;\n"
              "\tassign\ta\t=\t1'b1;\n"
              "endmodule\n"));
}

// =========================================================================
// Carriage return + line feed
// =========================================================================
TEST(ParserCh501, Sec5_1_CarriageReturnLineFeed) {
  // Windows-style \r\n line endings must parse identically to \n.
  EXPECT_TRUE(
      ParseOk("module t;\r\n"
              "  logic a;\r\n"
              "endmodule\r\n"));
}

// =========================================================================
// Compilation-unit with only whitespace/comments (empty CU)
// =========================================================================
TEST(ParserCh501, Sec5_1_EmptyCuWhitespaceOnly) {
  // A compilation unit containing only whitespace parses to an empty CU.
  auto r = Parse("   \t\n\n  \t  ");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->modules.empty());
  EXPECT_TRUE(r.cu->packages.empty());
}

TEST(ParserCh501, Sec5_1_EmptyCuCommentsOnly) {
  // A compilation unit containing only comments parses to an empty CU.
  auto r = Parse(
      "// line comment\n"
      "/* block\n"
      "   comment */\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->modules.empty());
  EXPECT_TRUE(r.cu->packages.empty());
}

TEST(ParserCh501, Sec5_1_EmptyCuCompletelyEmpty) {
  // An entirely empty source file parses to an empty CU.
  auto r = Parse("");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->modules.empty());
}

// =========================================================================
// From test_parser_clause_05.cpp — §5.1 General
// =========================================================================
TEST(ParserCh501, FreeFormatLayout) {
  // Spaces and newlines are not syntactically significant (except in
  // escaped identifiers and string literals). Tokens can be on one line.
  EXPECT_TRUE(ParseOk("module t; logic a; endmodule"));
}

TEST(ParserCh501, FreeFormatMultiline) {
  // Same construct spread over many lines.
  EXPECT_TRUE(
      ParseOk("module\n"
              "  t\n"
              ";\n"
              "  logic\n"
              "    a\n"
              ";\n"
              "endmodule\n"));
}

TEST(ParserCh501, AllTokenTypesPresent) {
  // §5.1 lists: white space, comments, operators, numbers, string
  // literals, identifiers, keywords. This test exercises them all.
  EXPECT_TRUE(
      ParseOk("module t; // one-line comment\n"
              "  /* block comment */\n"
              "  logic [7:0] data = 8'hAB;\n"
              "  initial $display(\"hello\");\n"
              "endmodule\n"));
}

TEST(ParserCh503, BlockCommentSpanningLines) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  /* this comment\n"
              "     spans multiple\n"
              "     lines */\n"
              "  logic a;\n"
              "endmodule\n"));
}

TEST(ParserCh503, OneLineCommentEndsAtNewline) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic a; // comment\n"
              "  logic b;\n"
              "endmodule\n"));
}

TEST(ParserCh505, Operator_UnaryBitwiseNegate) {
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

TEST(ParserCh505, Operator_BinaryAdd) {
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

TEST(ParserCh505, Operator_Ternary) {
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

TEST(ParserCh505, Operator_LogicalShiftLeft) {
  EXPECT_TRUE(ParseOk("module m; initial x = a <<< 2; endmodule"));
}

TEST(ParserCh505, Operator_ArithShiftRight) {
  EXPECT_TRUE(ParseOk("module m; initial x = a >>> 1; endmodule"));
}

TEST(ParserCh505, Operator_CaseEquality) {
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

TEST(ParserCh505, Operator_CaseInequality) {
  // !== is the case inequality operator.
  EXPECT_TRUE(ParseOk("module m; initial x = (a !== b); endmodule"));
}

TEST(ParserCh505, Operator_ReductionAnd) {
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

TEST(ParserCh505, Operator_ReductionXnor) {
  EXPECT_TRUE(ParseOk("module m; initial x = ~^y; endmodule"));
}

TEST(ParserCh505, Operator_Power) {
  EXPECT_TRUE(ParseOk("module m; initial x = 2 ** 10; endmodule"));
}

TEST(ParserCh505, Operator_WildcardEquality) {
  // ==? is the wildcard equality operator.
  EXPECT_TRUE(ParseOk("module m; initial x = (a ==? b); endmodule"));
}

TEST(ParserCh506, Ident_SimpleWithUnderscore) {
  auto r = Parse("module m; logic _bus3; endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "_bus3");
}

TEST(ParserCh506, Ident_SimpleWithDollarSign) {
  EXPECT_TRUE(ParseOk("module m; logic n$657; endmodule"));
}

TEST(ParserCh506, Ident_CaseSensitive) {
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

// From test_parser_clause_05.cpp
TEST(ParserCh50601, EscapedIdentifierAsName) {
  // §5.6.1: escaped identifiers include special characters.
  EXPECT_TRUE(ParseOk("module t; wire \\bus+index ; endmodule"));
}

TEST(ParserCh50601, EscapedKeywordAsIdentifier) {
  // §5.6.1: escaped keyword is treated as a user-defined identifier.
  EXPECT_TRUE(ParseOk("module t; wire \\module ; endmodule"));
}

// From test_parser_clause_05b.cpp
TEST(ParserCh50601, EscapedIdent_Basic) {
  EXPECT_TRUE(ParseOk("module m; wire \\busa+index ; endmodule"));
}

TEST(ParserCh50601, EscapedIdent_Keyword) {
  // An escaped keyword is treated as a user-defined identifier, not as a
  // keyword. \net is a valid user-defined wire name.
  EXPECT_TRUE(ParseOk("module m; wire \\net ; endmodule"));
}

TEST(ParserCh50601, EscapedIdent_SpecialChars) {
  // Escaped identifiers can contain any printable ASCII character.
  EXPECT_TRUE(ParseOk("module m; wire \\***error-condition*** ; endmodule"));
}

TEST(ParserCh50601, EscapedIdent_ForwardSlash) {
  // \net1/\net2 is a valid escaped identifier containing a slash.
  EXPECT_TRUE(ParseOk("module m; wire \\net1/\\net2 ; endmodule"));
}

TEST(ParserCh50601, EscapedIdent_Braces) {
  // \{a,b} is a valid escaped identifier containing braces.
  EXPECT_TRUE(ParseOk("module m; wire \\{a,b} ; endmodule"));
}

// From test_parser_clause_05b.cpp
TEST(ParserCh50602, Keyword_EscapedAsIdentifier) {
  // An escaped keyword should be treated as a user-defined identifier.
  EXPECT_TRUE(ParseOk("module m; logic \\begin ; endmodule"));
}

TEST(ParserCh50602, Keyword_AllLowercase) {
  // Keywords are lowercase only; MODULE is not a keyword, so this fails.
  EXPECT_FALSE(ParseOk("MODULE m; endmodule"));
}

TEST(ParserCh50603, SystemTask_Display) {
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

}  // namespace
