// §6.18: User-defined types

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

namespace {

TEST(ParserSection6, TypedefForwardClass) {
  auto r = ParseWithPreprocessor(
      "typedef class MyClass;\n"
      "class MyClass;\n"
      "  int x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->classes.size(), 1u);
}

TEST(ParserSection6, TypedefForwardStruct) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  typedef struct my_struct;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
