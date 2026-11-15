#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

std::string OutputFormalReport(const std::string& name,
                               const std::string& type) {
  return "checker output formal '" + name + "' is declared '" + type +
         "', a type only an input formal can take";
}

TEST(CheckerOutputFormalType, AnExplicitOutputUntypedIsReported) {
  auto r = Parse("checker c(output untyped u); endchecker\n");
  EXPECT_TRUE(
      ReportedError(r.diags, OutputFormalReport("u", "untyped"), 1, "17.2"));
}

TEST(CheckerOutputFormalType, AnExplicitOutputPropertyIsReported) {
  auto r = Parse("checker c(output property p); endchecker\n");
  EXPECT_TRUE(
      ReportedError(r.diags, OutputFormalReport("p", "property"), 1, "17.2"));
}

TEST(CheckerOutputFormalType, DirectedInputsOfTheKeywordTypesAreAccepted) {
  auto r = Parse(
      "checker c(input sequence s, input property p, input untyped u,\n"
      "          output bit y);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerOutputFormalType, AnInheritedOutputSequenceIsReported) {
  auto r = Parse("checker c(output bit x, sequence s); endchecker\n");
  EXPECT_TRUE(
      ReportedError(r.diags, OutputFormalReport("s", "sequence"), 1, "17.2"));
}

TEST(CheckerOutputFormalType, AnInheritedOutputPropertyIsReported) {
  auto r = Parse("checker c(output bit x, property p); endchecker\n");
  EXPECT_TRUE(
      ReportedError(r.diags, OutputFormalReport("p", "property"), 1, "17.2"));
}

TEST(CheckerOutputFormalType, ABareFormalAfterAnOutputSequenceIsReported) {
  auto r = Parse("checker c(output sequence s, t); endchecker\n");
  EXPECT_TRUE(
      ReportedError(r.diags, OutputFormalReport("s", "sequence"), 1, "17.2"));
}

struct CheckerHome {
  const char* open;
  const char* close;
};

const CheckerHome kCheckerHomes[] = {
    {"module m;\n", "endmodule\n"},
    {"interface ifc;\n", "endinterface\n"},
    {"program prog;\n", "endprogram\n"},
    {"package pkg;\n", "endpackage\n"},
    {"module m;\n  if (1) begin : g\n", "  end\nendmodule\n"},
    {"checker o;\n", "endchecker\n"},
};

TEST(CheckerOutputFormalType, AnOutputPropertyIsReportedWhereverDeclared) {
  for (const auto& home : kCheckerHomes) {
    std::string src = std::string(home.open) +
                      "  checker c(output property p,\n"
                      "            output bit y);\n"
                      "  endchecker\n" +
                      home.close;
    auto r = Parse(src);
    EXPECT_TRUE(ReportedError(r.diags, OutputFormalReport("p", "property"),
                              LineHolding(src, "output property p"), "17.2"))
        << src;
    EXPECT_FALSE(ReportedError(r.diags, "checker output formal 'y'",
                               LineHolding(src, "output bit y"), "17.2"))
        << src;
  }
}

TEST(CheckerOutputFormalType, ATypedOutputIsAcceptedWhereverDeclared) {
  for (const auto& home : kCheckerHomes) {
    std::string src = std::string(home.open) +
                      "  checker c(output bit y); endchecker\n" + home.close;
    auto r = Parse(src);
    ASSERT_NE(r.cu, nullptr);
    EXPECT_FALSE(r.has_errors) << src;
  }
}

const ModuleDecl* OnlyChecker(const ParseResult& r) {
  if (r.cu == nullptr || r.cu->checkers.size() != 1) return nullptr;
  return r.cu->checkers[0];
}

TEST(CheckerFormalTypeInheritance, AWrittenUntypedCarriesOver) {
  auto r = Parse("checker c(logic clk, untyped u, v); endchecker\n");
  const auto* chk = OnlyChecker(r);
  ASSERT_NE(chk, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(chk->ports.size(), 3u);
  EXPECT_EQ(chk->ports[2].name, "v");
  EXPECT_EQ(chk->ports[2].formal_type, PropertyFormalType::kUntyped);
  EXPECT_EQ(chk->ports[0].formal_type, PropertyFormalType::kData);
}

TEST(CheckerFormalTypeInheritance, APropertyTypeCarriesOver) {
  auto r = Parse("checker c(logic clk, property p, q); endchecker\n");
  const auto* chk = OnlyChecker(r);
  ASSERT_NE(chk, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(chk->ports.size(), 3u);
  EXPECT_EQ(chk->ports[2].name, "q");
  EXPECT_EQ(chk->ports[2].formal_type, PropertyFormalType::kProperty);
  EXPECT_EQ(chk->ports[2].direction, Direction::kInput);
}

}  // namespace
