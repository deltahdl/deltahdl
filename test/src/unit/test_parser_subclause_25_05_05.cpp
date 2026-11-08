#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClockingModportParsing, ModportClockingDecl) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic clk;\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "  modport mp(clocking cb);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_clocking);
  EXPECT_EQ(mp->ports[0].name, "cb");
}

TEST(ClockingModportParsing, AttrOnClockingPort) {
  EXPECT_TRUE(
      ParseOk("interface bus(input logic clk);\n"
              "  clocking sb @(posedge clk);\n"
              "  endclocking\n"
              "  modport target((* synthesis *) clocking sb);\n"
              "endinterface\n"));
}

TEST(ClockingModportParsing, ClockingMixedWithSimplePort) {
  auto r = Parse(
      "interface ifc(input logic clk);\n"
      "  logic a;\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "  modport mp(input a, clocking cb);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 2u);
  EXPECT_FALSE(mp->ports[0].is_clocking);
  EXPECT_EQ(mp->ports[0].name, "a");
  EXPECT_TRUE(mp->ports[1].is_clocking);
  EXPECT_EQ(mp->ports[1].name, "cb");
}

TEST(ClockingModportParsing, ClockingWithoutIdentifierRejected) {
  auto r = Parse(
      "interface ifc(input logic clk);\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "  modport mp(clocking);\n"
      "endinterface\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ')'", 3, "25.5.5"));
}

}  // namespace
