// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, FunctionWithAllArgDirections) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function int compute(input int a, output int b,\n"
              "                       inout int c, ref int d);\n"
              "    b = a;\n"
              "    c = c + 1;\n"
              "    return a + d;\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, TaskAndFunctionCoexist) {
  auto r = Parse(
      "module m;\n"
      "  function int add(int a, int b); return a + b; endfunction\n"
      "  task do_nothing; endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kFunctionDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kTaskDecl));
}

}  // namespace
