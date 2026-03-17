#include "fixture_parser.h"
#include "fixture_program.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct UdpSpotCheck {
  size_t row;
  char input0;
  char output;
};

static void VerifyUdpTableSpotChecks(const UdpDecl* udp,
                                     const UdpSpotCheck checks[],
                                     size_t count) {
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(udp->table[checks[i].row].inputs[0], checks[i].input0);
    EXPECT_EQ(udp->table[checks[i].row].output, checks[i].output);
  }
}

namespace {

TEST(UdpBodyGrammar, MixedLevelEdgeSensitive) {
  auto r = Parse(
      "primitive jk_edge_ff(output reg q, input clock, j, k, preset, clear);\n"
      "  table\n"
      "    ? ? ? 0 1 : ? : 1;\n"
      "    ? ? ? 1 0 : ? : 0;\n"
      "    r 0 0 0 0 : 0 : 1;\n"
      "    r 0 0 1 1 : ? : -;\n"
      "    f ? ? ? ? : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 5);
  UdpSpotCheck checks[] = {
      {0, '?', '1'},
      {2, 'r', '1'},
      {4, 'f', '-'},
  };
  VerifyUdpTableSpotChecks(udp, checks, std::size(checks));
}

}  // namespace
