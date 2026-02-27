// §6.3.2.2: Drive strength

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA222, DriveStrengthStr1Highz0) {
  // ( strength1 , highz0 ): (strong1, highz0)
  auto r = Parse(
      "module m;\n"
      "  wire (strong1, highz0) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 1u);  // highz0 = 1
  EXPECT_EQ(item->drive_strength1, 4u);  // strong1 = 4
}

}  // namespace
