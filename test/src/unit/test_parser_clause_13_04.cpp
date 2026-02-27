// §13.4: Functions

#include "fixture_parser.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// function_body_declaration (old-style ports)
// ---------------------------------------------------------------------------
TEST(ParserA26, FuncBodyOldStylePorts) {
  auto r = Parse(
      "module m;\n"
      "  function int foo;\n"
      "    input int a;\n"
      "    input int b;\n"
      "    foo = a + b;\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].name, "b");
}

}  // namespace
