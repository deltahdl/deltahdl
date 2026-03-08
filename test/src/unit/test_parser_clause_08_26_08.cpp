#include "fixture_parser.h"

using namespace delta;

namespace {

// §8.26.8: Interface class method with default argument values.
TEST(ParserSection8, InterfaceMethodDefaultArgs) {
  EXPECT_TRUE(
      ParseOk("interface class IC;\n"
              "  pure virtual function void foo(int a = 5);\n"
              "endclass\n"));
}

// §8.26.8: Interface class method with multiple default args.
TEST(ParserSection8, InterfaceMethodMultipleDefaultArgs) {
  EXPECT_TRUE(
      ParseOk("interface class IC;\n"
              "  pure virtual function int calc(int a = 0, int b = 1);\n"
              "endclass\n"));
}

}  // namespace
