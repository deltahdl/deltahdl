#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Annex D.14 (C1): $sreadmemh parses as an ordinary system task call taking the
// memory_name, the start and finish addresses, and a data string.
TEST(OptionalSreadmemParser, SreadmemhBasicForm) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial $sreadmemh(mem, 0, 3, \"0A 14 1E\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Annex D.14 (C1): $sreadmemb has the same argument shape.
TEST(OptionalSreadmemParser, SreadmembBasicForm) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial $sreadmemb(mem, 0, 3, \"1010 0110\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Annex D.14 (C1): the syntax admits more than one data string after the
// addresses.
TEST(OptionalSreadmemParser, MultipleDataStrings) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial $sreadmemh(mem, 0, 3, \"0A 14\", \"1E 28\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
