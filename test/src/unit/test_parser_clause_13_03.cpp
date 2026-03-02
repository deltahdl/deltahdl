// §13.3: Tasks

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult14 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult14 Parse(const std::string& src) {
  ParseResult14 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

// Task with inout port direction.
TEST(ParserSection13, TaskWithInoutPort) {
  auto r = Parse(
      "module m;\n"
      "  task transform(inout logic [7:0] data);\n"
      "    data = data ^ 8'hFF;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "transform");
  ASSERT_NE(tk, nullptr);
  ASSERT_EQ(tk->func_args.size(), 1u);
  EXPECT_EQ(tk->func_args[0].direction, Direction::kInout);
}

// Task with no ports.
TEST(ParserSection13, TaskWithNoPorts) {
  auto r = Parse(
      "module m;\n"
      "  task idle();\n"
      "    #10;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "idle");
  ASSERT_NE(tk, nullptr);
  EXPECT_EQ(tk->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(tk->func_args.empty());
}

TEST(ParserA27, TfPortItemVarWithDirection) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input var int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[0].name, "x");
}

// ---------------------------------------------------------------------------
// tf_port_item clarification 28: name omitted in prototype
// ---------------------------------------------------------------------------
TEST(ParserA27, TfPortItemNoNameInPrototype) {
  auto r = Parse(
      "module m;\n"
      "  extern task my_task(input int, output int);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
}

// block_item_declaration in task body (§13.3)
TEST(ParserA28, BlockItemInTask) {
  auto r = Parse(
      "module m;\n"
      "  task my_task();\n"
      "    int x;\n"
      "    x = 5;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  ASSERT_GE(item->func_body_stmts.size(), 1u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kVarDecl);
}

struct ParseResult12b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult12b Parse(const std::string& src) {
  ParseResult12b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

TEST(Parser, TaskDecl) {
  auto r = Parse(
      "module t;\n"
      "  task my_task(input int x);\n"
      "    $display(\"%d\", x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(mod->items[0]->name, "my_task");
  ASSERT_EQ(mod->items[0]->func_args.size(), 1);
}

// ---------------------------------------------------------------------------
// tf_item_declaration: block_item_declaration and tf_port_declaration mixed
// ---------------------------------------------------------------------------
TEST(ParserA27, TfItemDeclMixed) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    input int a;\n"
      "    output int b;\n"
      "    int temp;\n"
      "    temp = a + 1;\n"
      "    b = temp;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_GE(item->func_body_stmts.size(), 1u);
}

static ModuleItem* FindFunc(ParseResult& r, std::string_view name) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kFunctionDecl &&
        item->kind != ModuleItemKind::kTaskDecl) {
      continue;
    }
    if (item->name == name) return item;
  }
  return nullptr;
}

TEST(ParserSection13, MultipleDimsOnFuncArg) {
  auto r = Parse(
      "module m;\n"
      "  task bar(logic mem[16][8]);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "bar");
  ASSERT_NE(tk, nullptr);
  ASSERT_EQ(tk->func_args.size(), 1u);
  EXPECT_EQ(tk->func_args[0].unpacked_dims.size(), 2u);
}

TEST(ParserSection13, OldStyleTask) {
  auto r = Parse(
      "module m;\n"
      "  task mytask;\n"
      "    input a;\n"
      "    output b;\n"
      "    b = a;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "mytask");
  ASSERT_NE(tk, nullptr);
  ASSERT_EQ(tk->func_args.size(), 2u);
  EXPECT_EQ(tk->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(tk->func_args[1].direction, Direction::kOutput);
}

// =============================================================================
// LRM section 13.3-13.4 -- Old-style (non-ANSI) task/function declarations
// =============================================================================
TEST(ParserSection13, OldStyleTaskMultipleInputs) {
  auto r = Parse(
      "module m;\n"
      "  task add;\n"
      "    input a;\n"
      "    input b;\n"
      "    output c;\n"
      "    c = a + b;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "add");
  ASSERT_NE(tk, nullptr);
  ASSERT_EQ(tk->func_args.size(), 3u);
  const Direction kExpected[] = {Direction::kInput, Direction::kInput,
                                 Direction::kOutput};
  for (size_t i = 0; i < 3u; ++i) {
    EXPECT_EQ(tk->func_args[i].direction, kExpected[i]);
  }
}

// Task with end label matching the task name (LRM section 13.3).
TEST(ParserSection13, TaskEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  task do_work(int x);\n"
      "    $display(\"%d\", x);\n"
      "  endtask : do_work\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "do_work");
  ASSERT_NE(tk, nullptr);
  EXPECT_EQ(tk->kind, ModuleItemKind::kTaskDecl);
}

// =============================================================================
// LRM section 13.3 -- Tasks (additional tests)
// =============================================================================
// Task with timing control in body (tasks may have time-controlling stmts).
TEST(ParserSection13, TaskWithTimingControl) {
  auto r = Parse(
      "module m;\n"
      "  task wait_clk(input int n);\n"
      "    repeat (n) @(posedge clk);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "wait_clk");
  ASSERT_NE(tk, nullptr);
  EXPECT_EQ(tk->kind, ModuleItemKind::kTaskDecl);
  ASSERT_EQ(tk->func_args.size(), 1u);
  EXPECT_EQ(tk->func_args[0].direction, Direction::kInput);
}

}  // namespace
