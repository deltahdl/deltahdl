#include "fixture_parser.h"

using namespace delta;

namespace {

// A UDP instantiation may carry at most two delays (rise and fall). A third
// delay is meaningful only for primitives that can drive z, and UDPs cannot,
// so the three-delay form shall be rejected.
TEST(UdpInstantiation, RejectsThreeDelays) {
  auto r = Parse(
      "primitive my_udp(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top;\n"
      "  wire y;\n"
      "  wire a;\n"
      "  my_udp #(1, 2, 3) u1 (y, a);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
