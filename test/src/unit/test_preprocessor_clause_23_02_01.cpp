// §23.2.1: Module header definition

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection22, ModuleWithoutBeginKeywords) {
  auto r = ParseWithPreprocessor(
      "module m1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m1");
}

}  // namespace
