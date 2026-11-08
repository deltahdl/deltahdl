#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(UdpTopLevelParsing, PrimitiveInsideModuleRejected) {
  auto r = Parse(
      "module m;\n"
      "  primitive inv(output out, input in);\n"
      "    table 0 : 1; 1 : 0; endtable\n"
      "  endprimitive\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "unexpected token in module body", 2, "23.2.4"));
}

TEST(UdpTopLevelParsing, PrimitiveBetweenModulesAccepted) {
  auto r = Parse(
      "module a; endmodule\n"
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->udps.size(), 1u);
}

TEST(UdpTopLevelParsing, PrimitiveDefinedAfterInstantiationSiteParses) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a;\n"
      "  my_udp u1(y, a);\n"
      "endmodule\n"
      "primitive my_udp(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->udps.size(), 1u);
}

TEST(UdpTopLevelParsing, AtLeast256UdpsAccepted) {
  std::string src;
  src.reserve(256UL * 96);
  for (int i = 0; i < 300; ++i) {
    src += "primitive p";
    src += std::to_string(i);
    src +=
        "(output out, input in);\n  table 0 : 1; 1 : 0; "
        "endtable\nendprimitive\n";
  }
  auto r = Parse(src);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->udps.size(), 300u);
}

TEST(UdpTopLevelParsing, ExternAnsiPrototypeAccepted) {
  auto r = Parse("extern primitive inv(output out, input in);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "inv");
  EXPECT_EQ(r.cu->udps[0]->output_name, "out");
  ASSERT_EQ(r.cu->udps[0]->input_names.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->input_names[0], "in");
  EXPECT_TRUE(r.cu->udps[0]->table.empty());
}

TEST(UdpTopLevelParsing, ExternNonAnsiPrototypeAccepted) {
  auto r = Parse("extern primitive inv(out, in);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->output_name, "out");
  ASSERT_EQ(r.cu->udps[0]->input_names.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->input_names[0], "in");
}

TEST(UdpTopLevelParsing, ExternAnsiSequentialPrototypeAccepted) {
  auto r = Parse("extern primitive dff(output reg q, input clk, input d);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->output_name, "q");
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);
  ASSERT_EQ(r.cu->udps[0]->input_names.size(), 2u);
  EXPECT_EQ(r.cu->udps[0]->input_names[0], "clk");
  EXPECT_EQ(r.cu->udps[0]->input_names[1], "d");
}

TEST(UdpTopLevelParsing, WildcardPortListHeaderAccepted) {
  auto r = Parse(
      "primitive inv(.*);\n"
      "  output out;\n"
      "  input in;\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->output_name, "out");
  ASSERT_EQ(r.cu->udps[0]->input_names.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->input_names[0], "in");
}

TEST(UdpTopLevelParsing, MatchingEndprimitiveLabelAccepted) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive : inv\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->udps.size(), 1u);
}

TEST(UdpTopLevelParsing, MismatchedEndprimitiveLabelRejected) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive : wrong\n");
  EXPECT_TRUE(ReportedError(r.diags, "end label 'wrong' does not match 'inv'",
                            3, "9.3.4"));
}

TEST(UdpTopLevelParsing, PrimitiveInsideProgramRejected) {
  auto r = Parse(
      "program p;\n"
      "  primitive inv(output out, input in);\n"
      "    table 0 : 1; 1 : 0; endtable\n"
      "  endprimitive\n"
      "endprogram\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "unexpected token in module body", 2, "23.2.4"));
}

TEST(UdpTopLevelParsing, PrimitiveInsideInterfaceRejected) {
  auto r = Parse(
      "interface intf;\n"
      "  primitive inv(output out, input in);\n"
      "    table 0 : 1; 1 : 0; endtable\n"
      "  endprimitive\n"
      "endinterface\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "unexpected token in module body", 2, "23.2.4"));
}

TEST(UdpTopLevelParsing, PrimitiveInsidePackageRejected) {
  auto r = Parse(
      "package pkg;\n"
      "  primitive inv(output out, input in);\n"
      "    table 0 : 1; 1 : 0; endtable\n"
      "  endprimitive\n"
      "endpackage\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "unexpected token in module body", 2, "23.2.4"));
}

}  // namespace
