#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ParseResult3_08 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult3_08 Parse(const std::string& src) {
  ParseResult3_08 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FindItemByKind(ParseResult3_08& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

// =============================================================================
// LRM §3.8 — Subroutines
// =============================================================================

// §3.8: "A task is called as a statement. A task can have any number of
//        input, output, inout, and ref arguments, but does not return a
//        value. Tasks can block simulation time during execution."
TEST(ParserClause03, Cl3_8_TaskAllDirectionsAndBlocking) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int a, output int b, inout int c, ref int d);\n"
      "    #10;\n"
      "    b = a + c;\n"
      "    c = d;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* task = FindItemByKind(r, ModuleItemKind::kTaskDecl);
  ASSERT_NE(task, nullptr);
  EXPECT_EQ(task->name, "my_task");
  ASSERT_EQ(task->func_args.size(), 4u);
  EXPECT_EQ(task->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(task->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(task->func_args[2].direction, Direction::kInout);
  EXPECT_EQ(task->func_args[3].direction, Direction::kRef);
  // Task has a body with delay (#10 blocks time) + assignments
  EXPECT_GE(task->func_body_stmts.size(), 1u);
}

// §3.8: Function returning value, void function, all 4 argument directions.
TEST(ParserClause03, Cl3_8_FunctionReturnAndVoidAndDirections) {
  auto r = Parse(
      "module m;\n"
      "  function int compute(input int a, output int b,\n"
      "                       inout int c, ref int d);\n"
      "    b = a;\n"
      "    return a + c + d;\n"
      "  endfunction\n"
      "  function void show(input int val);\n"
      "    $display(\"%d\", val);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int func_count = 0;
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl) {
      ++func_count;
      if (item->name == "compute") {
        ASSERT_EQ(item->func_args.size(), 4u);
        EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
        EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
        EXPECT_EQ(item->func_args[2].direction, Direction::kInout);
        EXPECT_EQ(item->func_args[3].direction, Direction::kRef);
      }
    }
  }
  EXPECT_EQ(func_count, 2);
}
