#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §25.6: an interface signal is named with its interface instance qualifier and
// is available as a specify terminal. The parser splits the qualified terminal
// into interface name and signal name. The same terminal parse serves source,
// destination, and timing-check positions, so one observer covers the rule.
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

// §25.6: an interface signal is equally available as a module path
// destination. The destination is a distinct syntactic position, so observe the
// qualifier split there too.
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

// §25.6: an interface signal is equally available as a timing-check terminal,
// another distinct syntactic position for the qualified terminal.
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
  EXPECT_EQ(tc->ref_terminal.interface_name, "intf");
  EXPECT_EQ(tc->ref_terminal.name, "data");
}

}  // namespace
