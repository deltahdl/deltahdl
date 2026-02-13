#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

static std::vector<Token> Lex(const std::string &src) {
  static SourceManager mgr;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  return lexer.LexAll();
}

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

struct PreprocFixture {
  SourceManager mgr;
  DiagEngine diag{mgr};
};

static std::string Preprocess(const std::string &src, PreprocFixture &f,
                              PreprocConfig config = {}) {
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor pp(f.mgr, f.diag, std::move(config));
  return pp.Preprocess(fid);
}

// ===========================================================================
// 1. Escaped identifiers (LRM SS5.6.1)
// ===========================================================================

TEST(Lexical, EscapedIdentifier_Basic) {
  // \escaped_id followed by a space terminates the identifier.
  auto tokens = Lex("\\my+name ");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\my+name");
}

TEST(Lexical, EscapedIdentifier_WithSpecialChars) {
  auto tokens = Lex("\\abc!@#$% ");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\abc!@#$%");
}

TEST(Lexical, EscapedIdentifier_InModulePort) {
  // Escaped identifiers should work as port/signal names in a module.
  auto r = Parse(
      "module top(input logic \\clk.in );\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1);
  // The port name should be the escaped identifier text.
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "\\clk.in");
}

TEST(Lexical, EscapedIdentifier_TerminatedByNewline) {
  auto tokens = Lex("\\esc_id\n");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

TEST(Lexical, EscapedIdentifier_TerminatedByTab) {
  auto tokens = Lex("\\esc_id\t");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

// ===========================================================================
// 2. Integer literal edge cases (LRM SS5.7.1)
// ===========================================================================

TEST(Lexical, IntLiteral_UnderscoreSeparators) {
  auto tokens = Lex("32'hDEAD_BEEF");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "32'hDEAD_BEEF");
}

TEST(Lexical, IntLiteral_DecimalUnderscores) {
  auto tokens = Lex("1_000_000");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "1_000_000");
}

TEST(Lexical, IntLiteral_BinaryWithUnderscore) {
  auto tokens = Lex("8'b1010_0101");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "8'b1010_0101");
}

TEST(Lexical, IntLiteral_XFill) {
  // x fill in a based literal: 8'hxx
  auto tokens = Lex("8'hxx");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "8'hxx");
}

TEST(Lexical, IntLiteral_ZFill) {
  auto tokens = Lex("8'bzzzz_zzzz");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "8'bzzzz_zzzz");
}

TEST(Lexical, IntLiteral_UnsizedDecimal) {
  // Unsized decimal literal
  auto tokens = Lex("'d42");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "'d42");
}

TEST(Lexical, IntLiteral_UnsizedHex) {
  auto tokens = Lex("'hFF");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "'hFF");
}

TEST(Lexical, IntLiteral_SignedBase) {
  auto tokens = Lex("8'shFF");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "8'shFF");
}

TEST(Lexical, UnbasedUnsized_AllValues) {
  // '0, '1, 'x, 'z are unbased unsized literals
  auto tokens = Lex("'0 '1 'x 'z 'X 'Z");
  ASSERT_GE(tokens.size(), 7);
  for (int i = 0; i < 6; ++i) {
    EXPECT_EQ(tokens[i].kind, TokenKind::kUnbasedUnsizedLiteral)
        << "token " << i;
  }
}

TEST(Lexical, IntLiteral_LargeHex) {
  // 64-bit hex literal
  auto tokens = Lex("64'hFFFF_FFFF_FFFF_FFFF");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "64'hFFFF_FFFF_FFFF_FFFF");
}

TEST(Lexical, IntLiteral_QuestionMarkInBased) {
  // ? is equivalent to z in based literals
  auto tokens = Lex("8'b1010_????");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "8'b1010_????");
}

// ===========================================================================
// 3. Timeunit/timeprecision parsing (LRM SS3.14)
// ===========================================================================

TEST(Lexical, Timeunit_BasicParse) {
  auto r = Parse(
      "module top;\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  // Should parse without error. The timeunit decl is consumed.
  EXPECT_EQ(r.cu->modules[0]->name, "top");
}

TEST(Lexical, Timeprecision_BasicParse) {
  auto r = Parse(
      "module top;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, Timeunit_WithSlash) {
  // timeunit 1ns / 1ps;  (combined form)
  auto r = Parse(
      "module top;\n"
      "  timeunit 1ns / 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, Timeunit_DifferentValues) {
  // Various time unit values
  auto r = Parse(
      "module top;\n"
      "  timeunit 100us;\n"
      "  timeprecision 10ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, Timeunit_StoredInModuleDecl_Values) {
  // The timeunit/timeprecision values should be stored in ModuleDecl.
  auto r = Parse(
      "module top;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto *mod = r.cu->modules[0];
  EXPECT_EQ(mod->time_unit, TimeUnit::kNs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kPs);
}

TEST(Lexical, Timeunit_StoredInModuleDecl_Flags) {
  auto r = Parse(
      "module top;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto *mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
}

// ===========================================================================
// 4. `define with arguments (LRM SS22.5.1)
// ===========================================================================

TEST(Lexical, Define_WithDefaultArgs) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define ASSERT(cond, msg=\"error\") if (!(cond)) $error(msg)\n"
      "`ASSERT(x)\n",
      f);
  EXPECT_NE(result.find("if (!(x)) $error(\"error\")"), std::string::npos);
}

TEST(Lexical, Define_Stringification) {
  // `` (double backtick) concatenation in macros
  PreprocFixture f;
  auto result = Preprocess(
      "`define CONCAT(a, b) a``b\n"
      "`CONCAT(foo, bar)\n",
      f);
  EXPECT_NE(result.find("foobar"), std::string::npos);
}

TEST(Lexical, Define_EmptyArgUsesDefault) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M(a, b=99) a + b\n"
      "`M(1,)\n",
      f);
  EXPECT_NE(result.find("1 + 99"), std::string::npos);
}

// ===========================================================================
// 5. Continuous assignment with delay (LRM SS10.3.3)
// ===========================================================================

TEST(Lexical, ContAssign_WithDelay) {
  auto r = Parse(
      "module top;\n"
      "  wire out, in;\n"
      "  assign #5 out = in;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  const ModuleItem *assign_item = nullptr;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      assign_item = item;
      break;
    }
  }
  ASSERT_NE(assign_item, nullptr) << "no continuous assignment found";
  ASSERT_NE(assign_item->assign_delay, nullptr);
  EXPECT_EQ(assign_item->assign_delay->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(assign_item->assign_delay->int_val, 5);
}

TEST(Lexical, ContAssign_WithParenDelay) {
  auto r = Parse(
      "module top;\n"
      "  wire out, in;\n"
      "  assign #(10) out = in;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kContAssign) continue;
    found = true;
    ASSERT_NE(item->assign_delay, nullptr);
    EXPECT_EQ(item->assign_delay->int_val, 10);
  }
  EXPECT_TRUE(found);
}

TEST(Lexical, ContAssign_NoDelay) {
  auto r = Parse(
      "module top;\n"
      "  wire a, b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kContAssign) continue;
    EXPECT_EQ(item->assign_delay, nullptr);
  }
}

// ===========================================================================
// 6. Assignment pattern evaluation (LRM SS10.9-10.10)
// ===========================================================================

TEST(Lexical, AssignmentPattern_DefaultZero) {
  auto r = Parse(
      "module top;\n"
      "  logic [7:0] a;\n"
      "  initial a = '{default: 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  // Should parse without error.
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, AssignmentPattern_Positional) {
  auto r = Parse(
      "module top;\n"
      "  logic [3:0] a;\n"
      "  initial a = '{1, 0, 1, 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, AssignmentPattern_Named) {
  auto r = Parse(
      "module top;\n"
      "  initial begin\n"
      "    logic [7:0] x;\n"
      "    x = '{default: 'x};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// ===========================================================================
// 7. Compilation unit scope (LRM SS3.12.1)
// ===========================================================================

TEST(Lexical, CompilationUnit_MultipleModules) {
  // Multiple modules should each become separate entries in the CU.
  auto r = Parse(
      "module a; endmodule\n"
      "module b; endmodule\n"
      "module c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 3);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
  EXPECT_EQ(r.cu->modules[2]->name, "c");
}

TEST(Lexical, CompilationUnit_MixedTopLevel) {
  // Mixed modules and packages in a single compilation unit.
  auto r = Parse(
      "package pkg;\n"
      "endpackage\n"
      "module top;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, CompilationUnit_WithInterface) {
  // §3.12.1: interfaces are visible across all CUs
  auto r = Parse(
      "interface bus_if;\n"
      "endinterface\n"
      "module top;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, CompilationUnit_WithProgram) {
  // §3.12.1: programs are visible across all CUs
  auto r = Parse(
      "program test;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->programs.size(), 1);
}

TEST(Lexical, CompilationUnit_TopLevelFunction) {
  // §3.12.1: CU scope can contain items that a package can (functions)
  auto r = Parse(
      "function int add(int a, int b);\n"
      "  return a + b;\n"
      "endfunction\n"
      "module top;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->cu_items.size(), 1);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, CompilationUnit_AllDesignElements) {
  // §3.12.1: CU can hold modules, packages, interfaces, programs
  auto r = Parse(
      "package pkg; endpackage\n"
      "interface intf; endinterface\n"
      "program prog; endprogram\n"
      "module mod; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->packages.size(), 1);
  EXPECT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->programs.size(), 1);
  EXPECT_EQ(r.cu->modules.size(), 1);
}

// ===========================================================================
// 8. Escaped identifier in parser contexts
// ===========================================================================

TEST(Lexical, EscapedIdentifier_InVarDecl) {
  auto r = Parse(
      "module top;\n"
      "  logic \\data+bus ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  bool found = false;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    if (item->name == "\\data+bus") {
      found = true;
      break;
    }
  }
  EXPECT_TRUE(found) << "variable with escaped identifier not found";
}

// ===========================================================================
// 9. begin_keywords / end_keywords (IEEE 1800-2023 §22.14)
// ===========================================================================

TEST(Lexical, BeginKeywords_LogicAsIdentifier) {
  PreprocFixture f;
  auto preprocessed = Preprocess(
      "`begin_keywords \"1364-2001\"\n"
      "module m; reg logic; endmodule\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  DiagEngine diag2(f.mgr);
  Lexer lexer(preprocessed, 0, diag2);
  auto tokens = lexer.LexAll();
  // Find the token after "reg" — should be kIdentifier ("logic"), not kKwLogic.
  for (size_t i = 0; i + 1 < tokens.size(); ++i) {
    if (tokens[i].kind == TokenKind::kKwReg) {
      EXPECT_EQ(tokens[i + 1].kind, TokenKind::kIdentifier);
      EXPECT_EQ(tokens[i + 1].text, "logic");
      return;
    }
  }
  FAIL() << "did not find 'reg' token in lexed output";
}

TEST(Lexical, BeginKeywords_RestoresAfterEnd) {
  PreprocFixture f;
  auto preprocessed = Preprocess(
      "`begin_keywords \"1364-2001\"\n"
      "logic\n"
      "`end_keywords\n"
      "logic\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  DiagEngine diag2(f.mgr);
  Lexer lexer(preprocessed, 0, diag2);
  auto tokens = lexer.LexAll();
  // First "logic" should be identifier (under 1364-2001).
  // Second "logic" should be keyword (restored to 1800-2023).
  ASSERT_GE(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "logic");
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwLogic);
}
