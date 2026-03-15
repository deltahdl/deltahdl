// §13.2

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(Subroutines, TaskAndFunctionCoexist) {
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
