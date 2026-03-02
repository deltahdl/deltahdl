// §6.19.3: Type checking

#include "fixture_parser.h"

using namespace delta;

namespace {

// § constant_primary — enum_identifier
TEST(ParserA84, ConstantPrimaryEnumIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  parameter color_t C = RED;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
