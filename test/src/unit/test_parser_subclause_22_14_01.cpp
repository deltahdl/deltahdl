#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_keyword_version.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kM2Module =
    "module m2 (input wire clk, output wire q);\n"
    "  reg [63:0] logic;\n"
    "endmodule\n";

constexpr const char* kInterface =
    "interface if1 (input wire clk);\n"
    "  wire [7:0] data;\n"
    "endinterface\n";

std::string Guarded(const std::string& specifier, const std::string& body) {
  return "`begin_keywords \"" + specifier + "\"\n" + body + "`end_keywords\n";
}

TEST(KeywordVersionExampleParsing, ModuleWithNoDirectiveUsesTheDefaultList) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m1;\n"
                              "  reg [63:0] v;\n"
                              "endmodule\n"));

  auto r = ParseWithPreprocessor(kM2Module);
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got 'logic'", 2, "6.8"));
}

TEST(KeywordVersionExampleParsing, DefaultListGovernsOutsideEveryPair) {
  const std::string kBefore =
      "module m1;\n"
      "  logic [63:0] v;\n"
      "endmodule\n" +
      Guarded("1364-2001", kM2Module);
  EXPECT_TRUE(ParseWithPreprocessorOk(kBefore));

  const std::string kAfter = Guarded("1364-2001", kM2Module) +
                             "module m1;\n"
                             "  logic [63:0] v;\n"
                             "endmodule\n";
  EXPECT_TRUE(ParseWithPreprocessorOk(kAfter));

  auto ahead =
      ParseWithPreprocessor(std::string(kM2Module) +
                            Guarded("1364-2001", "module other;\nendmodule\n"));
  EXPECT_TRUE(
      ReportedError(ahead.diags, "expected identifier, got 'logic'", 2, "6.8"));

  auto behind =
      ParseWithPreprocessor(Guarded("1364-2001", "module other;\nendmodule\n") +
                            std::string(kM2Module));
  EXPECT_TRUE(ReportedError(behind.diags, "expected identifier, got 'logic'", 6,
                            "6.8"));
}

TEST(KeywordVersionExampleParsing, VerilogRegionAcceptsLogicAsAVariableName) {
  for (const char* specifier : {"1364-2001", "1364-1995", "1364-2005"}) {
    EXPECT_TRUE(ParseWithPreprocessorOk(Guarded(specifier, kM2Module)))
        << specifier;
  }
}

TEST(KeywordVersionExampleParsing,
     SystemVerilogRegionRejectsLogicAsAVariableName) {
  for (const char* specifier :
       {"1800-2005", "1800-2009", "1800-2012", "1800-2017", "1800-2023"}) {
    auto r = ParseWithPreprocessor(Guarded(specifier, kM2Module));
    EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got 'logic'",
                              LineInRegion(2), "6.8"))
        << specifier;
  }
}

TEST(KeywordVersionExampleParsing,
     VerilogRegionAcceptsLogicAsEveryVariableType) {
  const char* const kDeclarations[] = {
      "reg [63:0] logic;", "reg logic;",  "integer logic;",
      "real logic;",       "time logic;",
  };
  for (const char* decl : kDeclarations) {
    const std::string kBody =
        std::string("module t;\n  ") + decl + "\nendmodule\n";
    EXPECT_TRUE(ParseWithPreprocessorOk(Guarded("1364-2001", kBody))) << decl;
    auto r = ParseWithPreprocessor(Guarded("1800-2005", kBody));
    EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got 'logic'",
                              LineInRegion(2), "6.8"))
        << decl;
  }
}

TEST(KeywordVersionExampleParsing, SystemVerilogRegionAcceptsTheInterface) {
  EXPECT_TRUE(ParseWithPreprocessorOk(Guarded("1800-2005", kInterface)));
}

TEST(KeywordVersionExampleParsing, VerilogRegionRejectsTheInterface) {
  for (const char* specifier : {"1364-2005", "1364-2001", "1364-1995"}) {
    auto r = ParseWithPreprocessor(Guarded(specifier, kInterface));
    EXPECT_TRUE(ReportedError(r.diags, "expected top-level declaration",
                              LineInRegion(1), "3.12.1"))
        << specifier;
  }
}

TEST(KeywordVersionExampleParsing, VerilogRegionAcceptsInterfaceWordsAsNames) {
  for (const char* word : {"interface", "endinterface"}) {
    const std::string kBody =
        std::string("module t;\n  wire ") + word + ";\nendmodule\n";
    EXPECT_TRUE(ParseWithPreprocessorOk(Guarded("1364-2005", kBody))) << word;
    auto r = ParseWithPreprocessor(Guarded("1800-2005", kBody));
    EXPECT_TRUE(ReportedError(
        r.diags, std::string("expected identifier, got '") + word + "'",
        LineInRegion(2), "6.7"))
        << word;
  }
}

}  // namespace
