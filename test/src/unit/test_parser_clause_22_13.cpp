// §22.13: `__FILE__ and `__LINE__

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection22, FileAndLineInErrorMessage) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"Error at %s, line %d.\",\n"
              "    `__FILE__, `__LINE__);\n"
              "endmodule\n"));
}

}  // namespace
