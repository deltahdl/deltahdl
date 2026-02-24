// §13.5.2: Pass by reference

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

RtlirDesign *Elaborate(const std::string &src, ElabFixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

namespace {

TEST(ParserA26, FuncBodyNewStyleConstRef) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(const ref int x);\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

TEST(ParserA27, TaskBodyNewStyleConstRef) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(const ref int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

TEST(ParserA27, TfPortDirectionConstRefStatic) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(const ref static int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

// ---------------------------------------------------------------------------
// tf_port_declaration (old-style): const ref and var
// ---------------------------------------------------------------------------
TEST(ParserA27, TfPortDeclOldStyleConstRef) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    const ref int x;\n"
      "    $display(\"%0d\", x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

}  // namespace
