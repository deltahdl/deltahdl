#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(PropertyLocalLvarArgumentParsing, LocalInoutInPropertyIsError) {
  auto r = Parse(
      "module m;\n"
      "  property p(local inout logic a);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "property port direction must be 'input'",
                            2, "16.12.19"));
}

TEST(PropertyLocalLvarArgumentParsing, LocalOutputInPropertyIsError) {
  auto r = Parse(
      "module m;\n"
      "  property p(local output bit a);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "property port direction must be 'input'",
                            2, "16.12.19"));
}

TEST(PropertyLocalLvarArgumentParsing, ExplicitInputInPropertyParses) {
  auto r = Parse(
      "module m;\n"
      "  property p(local input logic a);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formals.size(), 1u);
  EXPECT_EQ(item->prop_formals[0], "a");
}

TEST(PropertyLocalLvarArgumentParsing, InferredInputInPropertyParses) {
  auto r = Parse(
      "module m;\n"
      "  property p(local logic a);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formals.size(), 1u);
  EXPECT_EQ(item->prop_formals[0], "a");
}

TEST(PropertyLocalLvarArgumentParsing, InoutOnNonFirstLocalIsError) {
  auto r = Parse(
      "module m;\n"
      "  property p(local input logic a, local inout int b);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "property port direction must be 'input'",
                            2, "16.12.19"));
}

TEST(PropertyLocalLvarArgumentParsing, OutputOnNonFirstLocalIsError) {
  auto r = Parse(
      "module m;\n"
      "  property p(local input logic a, local output bit b);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "property port direction must be 'input'",
                            2, "16.12.19"));
}

TEST(PropertyLocalLvarArgumentParsing, MultipleInputLocalsParse) {
  auto r = Parse(
      "module m;\n"
      "  property p(local input logic a, local bit b);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formals.size(), 2u);
  EXPECT_EQ(item->prop_formals[0], "a");
  EXPECT_EQ(item->prop_formals[1], "b");
}

TEST(PropertyLocalLvarArgumentParsing, AUserDefinedTypeEndsALocalRun) {
  auto r = Parse(
      "module m;\n"
      "  typedef logic [1:0] my_t;\n"
      "  property p(local int a, my_t x, local my_t y);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formal_is_local.size(), 3u);
  EXPECT_TRUE(item->prop_formal_is_local[0]);
  EXPECT_FALSE(item->prop_formal_is_local[1]);
  EXPECT_TRUE(item->prop_formal_is_local[2]);
}

constexpr const char* kLocalFormalPlaces[] = {
    "module",  "interface",      "program",        "checker",
    "package", "generate block", "clocking block", "compilation unit"};

std::string LocalFormalIn(const std::string& place,
                          const std::string& declaration) {
  const std::string kSignals = "  logic clk; bit a, b;\n";
  const std::string kLine = "  " + declaration + "\n";
  if (place == "interface" || place == "program" || place == "checker" ||
      place == "package") {
    return place + " m;\n" + kSignals + kLine + "end" + place + "\n";
  }
  if (place == "generate block") {
    return "module m;\n" + kSignals + "  if (1) begin : g " + declaration +
           " end\nendmodule\n";
  }
  if (place == "clocking block") {
    return "module m;\n" + kSignals + "  clocking cb @(posedge clk); " +
           declaration + " endclocking\nendmodule\n";
  }
  if (place == "compilation unit") return "\n" + kSignals + kLine;
  return "module m;\n" + kSignals + kLine + "endmodule\n";
}

std::string PropertyWithPorts(const std::string& ports) {
  return "property p(" + ports + "); a |-> b; endproperty";
}

constexpr const char* kForbiddenLocalDirections[] = {
    "local inout logic x",
    "local output bit x",
    "local inout int x [2]",
    "local output logic [3:0] x",
    "local output int x = 0",
    "local input int y, local inout int x",
    "local input int y, local output bit x",
    "local int y, local output int x",
    "bit y, local inout int x",
    "local inout int x, local input int y"};

TEST(PropertyLocalLvarArgumentParsing,
     AnInoutOrOutputLocalFormalIsReportedInEachPlace) {
  for (const char* place : kLocalFormalPlaces) {
    for (const char* ports : kForbiddenLocalDirections) {
      SCOPED_TRACE(std::string(place) + ": " + ports);
      auto r = Parse(LocalFormalIn(place, PropertyWithPorts(ports)));
      EXPECT_TRUE(ReportedError(
          r.diags, "property port direction must be 'input'", 3, "16.12.19"));
    }
  }
}

TEST(PropertyLocalLvarArgumentParsing,
     DISABLED_ARefLocalFormalIsReportedInEachPlace) {
  for (const char* place : kLocalFormalPlaces) {
    for (const char* ports : {"local ref int x", "local const ref int x",
                              "local input int y, local ref bit x"}) {
      SCOPED_TRACE(std::string(place) + ": " + ports);
      auto r = Parse(LocalFormalIn(place, PropertyWithPorts(ports)));
      EXPECT_TRUE(ReportedError(
          r.diags, "property port direction must be 'input'", 3, "16.12.19"));
    }
  }
}

constexpr const char* kAllowedLocalDirections[] = {
    "local input logic x",
    "local bit x",
    "local input int x [2]",
    "local logic [3:0] x",
    "local input int x = 0",
    "local int x = 1",
    "local input int y, x",
    "local input int y, local bit x",
    "local int y, local input bit x",
    "bit y, local input int x",
    "local input int x, bit y",
    "local input byte x, local shortint y, local input real z"};

TEST(PropertyLocalLvarArgumentParsing,
     AnInputLocalFormalIsAcceptedInEachPlace) {
  for (const char* place : kLocalFormalPlaces) {
    for (const char* ports : kAllowedLocalDirections) {
      SCOPED_TRACE(std::string(place) + ": " + ports);
      auto r = Parse(LocalFormalIn(place, PropertyWithPorts(ports)));
      EXPECT_FALSE(r.has_errors);
    }
  }
}

constexpr const char* kSequenceLocalDirections[] = {
    "sequence s(local inout int x); (a, x = x + 1); endsequence",
    "sequence s(local output bit x); (a, x = 1); endsequence",
    ("sequence s(local input int y, local output int x); (a, x = y); "
     "endsequence")};

TEST(PropertyLocalLvarArgumentParsing,
     AnInoutOrOutputLocalFormalOfASequenceIsAcceptedInEachPlace) {
  for (const char* place : kLocalFormalPlaces) {
    for (const char* declaration : kSequenceLocalDirections) {
      SCOPED_TRACE(std::string(place) + ": " + declaration);
      auto r = Parse(LocalFormalIn(place, declaration));
      EXPECT_FALSE(r.has_errors);
    }
  }
}

constexpr const char* kDirectionsWithoutLocal[] = {
    "input int x", "inout int x", "output int x", "bit y, input int x"};

TEST(PropertyLocalLvarArgumentParsing,
     ADirectionWithoutLocalIsReportedInEachPlace) {
  for (const char* place : kLocalFormalPlaces) {
    for (const char* ports : kDirectionsWithoutLocal) {
      SCOPED_TRACE(std::string(place) + ": " + ports);
      auto r = Parse(LocalFormalIn(place, PropertyWithPorts(ports)));
      EXPECT_TRUE(
          ReportedError(r.diags, "property port direction", 3, "16.12.19"));
    }
  }
}

}  // namespace
