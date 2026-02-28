// Annex A.7.3: Specify block terminals

#include "fixture_parser.h"

using namespace delta;

namespace {

// list_of_path_outputs — multiple simple output terminals (full path)
TEST(ParserA703, ListOfPathOutputsMultiple) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a *> x, y, z) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.dst_ports.size(), 3u);
  EXPECT_EQ(si->path.dst_ports[0].name, "x");
  EXPECT_EQ(si->path.dst_ports[1].name, "y");
  EXPECT_EQ(si->path.dst_ports[2].name, "z");
}

// Input terminal with part-select range
TEST(ParserA703, InputTerminalPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a[7:0] => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  EXPECT_EQ(si->path.src_ports[0].range_kind, SpecifyRangeKind::kPartSelect);
  EXPECT_NE(si->path.src_ports[0].range_left, nullptr);
  EXPECT_NE(si->path.src_ports[0].range_right, nullptr);
}

}  // namespace
