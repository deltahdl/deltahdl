#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SpecifyInterfaceTerminalParsing,
     InterfaceSignalSplitsIntoInterfaceAndName) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (intf.sig => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].interface_name, "intf");
  EXPECT_EQ(si->path.src_ports[0].name, "sig");
}

TEST(SpecifyInterfaceTerminalParsing,
     InterfaceSignalSplitsInDestinationPosition) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => intf.sig) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0].interface_name, "intf");
  EXPECT_EQ(si->path.dst_ports[0].name, "sig");
}

TEST(SpecifyInterfaceTerminalParsing,
     InterfaceSignalSplitsInTimingCheckPosition) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    $setup(intf.data, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_terminal.interface_name, "intf");
  EXPECT_EQ(tc->data_terminal.name, "data");
}

}  // namespace
