#include <gtest/gtest.h>

#include <cstddef>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(GenericInterfaceReference, SinglePort) {
  auto r = Parse("module m(interface bus); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_TRUE(port.is_interface_port);
  EXPECT_EQ(port.name, "bus");
}

TEST(GenericInterfaceReference, MultiplePorts) {
  auto r = Parse("module cpuMod(interface d, interface j); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_TRUE(r.cu->modules[0]->ports[0].is_interface_port);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "d");
  EXPECT_TRUE(r.cu->modules[0]->ports[1].is_interface_port);
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "j");
}

TEST(GenericInterfaceReference, MixedWithScalarPorts) {
  auto r = Parse("module memMod(interface a, input logic clk); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_TRUE(r.cu->modules[0]->ports[0].is_interface_port);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_FALSE(r.cu->modules[0]->ports[1].is_interface_port);
  EXPECT_EQ(r.cu->modules[0]->ports[1].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "clk");
}

TEST(GenericInterfaceReference, NonAnsiDeclarationIsError) {
  auto r = Parse(
      "module memMod(a, clk);\n"
      "  input interface a;\n"
      "  input logic clk;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "generic interface port must be declared with "
                            "ANSI-style port declarations, not the non-ANSI "
                            "port style",
                            2, "25.3.3"));
}

TEST(GenericInterfaceReference, NonAnsiBareReferenceIsError) {
  auto r = Parse(
      "module memMod(a);\n"
      "  interface a;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "generic interface port must be declared with "
                            "ANSI-style port declarations, not the non-ANSI "
                            "port style",
                            2, "25.3.3"));
  size_t errors = 0;
  for (const auto& d : r.diags) errors += d.severity == DiagSeverity::kError;
  EXPECT_EQ(errors, 1u);
}

TEST(GenericInterfaceReference, NestedInterfaceInNonAnsiModuleIsNotAPort) {
  auto r = Parse(
      "module memMod(a);\n"
      "  input a;\n"
      "  interface inner; endinterface\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
