#include "fixture_parser.h"
#include "helpers_assoc_array_index_dim.h"

using namespace delta;

namespace {

TEST(ClassIndexAssocArrayParsing, AssocArrayClassIndex_DimExpr) {
  ExpectAssocArrayIdentifierIndexDim(
      "module t;\n"
      "  class MyClass;\n"
      "    int x;\n"
      "  endclass\n"
      "  int aa[MyClass];\n"
      "endmodule\n",
      "aa", "MyClass");
}

TEST(ClassIndexAssocArrayParsing, AssocArrayClassIndex_MultipleVars) {
  auto r = Parse(
      "module t;\n"
      "  class Key;\n"
      "    int id;\n"
      "  endclass\n"
      "  int aa[Key];\n"
      "  int bb[Key];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassIndexAssocArrayParsing, AssocArrayClassIndex_DifferentElemTypes) {
  auto r = Parse(
      "module t;\n"
      "  class Idx;\n"
      "    int x;\n"
      "  endclass\n"
      "  logic [7:0] data[Idx];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
