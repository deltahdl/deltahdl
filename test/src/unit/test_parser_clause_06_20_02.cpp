// §6.20.2: Value parameters

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParserA23, ListOfParamAssignmentsWithDims) {
  auto r = Parse(
      "module m;\n"
      "  parameter int A [2] = '{1, 2}, B [3] = '{3, 4, 5};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) count++;
  }
  EXPECT_GE(count, 2);
}

}  // namespace
