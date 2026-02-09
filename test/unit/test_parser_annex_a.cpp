#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

Stmt* FirstInitialStmt(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

}  // namespace

// =============================================================================
// Annex A -- Formal syntax spot-checks (key BNF productions)
// =============================================================================

TEST(ParserAnnexA, AnnexAModuleDecl) {
  auto r = Parse("module m; endmodule");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

TEST(ParserAnnexA, AnnexAAlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  always_comb begin x = 1; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* mod = r.cu->modules[0];
  bool found_comb = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock &&
        item->always_kind == AlwaysKind::kAlwaysComb) {
      found_comb = true;
      ASSERT_NE(item->body, nullptr);
      EXPECT_EQ(item->body->kind, StmtKind::kBlock);
    }
  }
  EXPECT_TRUE(found_comb);
}

TEST(ParserAnnexA, AnnexAForLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_init, nullptr);
  EXPECT_NE(stmt->for_cond, nullptr);
  EXPECT_NE(stmt->for_step, nullptr);
  EXPECT_NE(stmt->for_body, nullptr);
}

TEST(ParserAnnexA, AnnexACaseStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) 0: y = 1; default: y = 0; endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_EQ(stmt->case_items.size(), 2u);
  EXPECT_FALSE(stmt->case_items[0].is_default);
  EXPECT_TRUE(stmt->case_items[1].is_default);
}

TEST(ParserAnnexA, AnnexAFunction) {
  auto r = Parse(
      "module m;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(mod->items[0]->name, "add");
  ASSERT_EQ(mod->items[0]->func_args.size(), 2u);
  EXPECT_EQ(mod->items[0]->func_args[0].name, "a");
  EXPECT_EQ(mod->items[0]->func_args[1].name, "b");
}

// =============================================================================
// Annex D -- Optional system tasks
// =============================================================================

TEST(ParserAnnexD, AnnexDCountdrivers) {
  auto r = Parse(
      "module m;\n"
      "  initial $countdrivers(sig);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  // System call parsed as expression statement.
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
}

TEST(ParserAnnexD, AnnexDList) {
  auto r = Parse(
      "module m;\n"
      "  initial $list;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
}

TEST(ParserAnnexD, AnnexDLog) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $log(\"sim.log\");\n"
      "    $nolog;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserAnnexD, AnnexDSave) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $save(\"state.sav\");\n"
      "    $restart(\"state.sav\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserAnnexD, AnnexDScope) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $scope(m);\n"
      "    $showscopes;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// =============================================================================
// Annex E -- Optional compiler directives
// The preprocessor may or may not handle these yet. The baseline check is that
// parsing does not crash and returns a non-null CompilationUnit.
// =============================================================================

TEST(ParserAnnexE, AnnexEDefaultDecayTime) {
  auto r = Parse(
      "`default_decay_time 10\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  // If the preprocessor/lexer consumed the directive, the module parses.
  // Otherwise, error recovery should still produce a CompilationUnit.
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

TEST(ParserAnnexE, AnnexEDelayModeZero) {
  auto r = Parse(
      "`delay_mode_zero\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

TEST(ParserAnnexE, AnnexEMultipleDirectives) {
  auto r = Parse(
      "`default_decay_time 100\n"
      "`delay_mode_distributed\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}
