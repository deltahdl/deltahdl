#include "fixture_parser.h"

using namespace delta;

namespace {

// §8.7: constructor shall not be static or virtual

TEST(ClassItemsParsing, ConstructorStaticError) {
  auto r = Parse(
      "class C;\n"
      "  static function new();\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ClassItemsParsing, ConstructorVirtualError) {
  auto r = Parse(
      "class C;\n"
      "  virtual function new();\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
