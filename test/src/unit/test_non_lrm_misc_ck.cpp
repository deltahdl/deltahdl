// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

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

namespace {

// Function with empty body.
TEST(ParserSection13, FunctionEmptyBody) {
  auto r = Parse(
      "module m;\n"
      "  function void nop();\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "nop");
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(fn->return_type.kind, DataTypeKind::kVoid);
  EXPECT_TRUE(fn->func_body_stmts.empty());
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
