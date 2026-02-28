// §6.22.1: Matching types

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

namespace {

TEST(ParserSection6, TypeCompatibilityAnonymousStruct) {
  // §6.22.1c: Anonymous struct matches itself within same declaration.
  auto r = Parse(
      "module m;\n"
      "  struct packed { int A; int B; } AB1, AB2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  // AB1 and AB2 should both be declared
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

}  // namespace
