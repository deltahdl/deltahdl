#include "fixture_parser.h"
#include "helpers_keyword_version.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The line each rejection below is reported at is counted in the
// preprocessor's output rather than in the source Guarded built. The two agree
// line for line, because `begin_keywords and `end_keywords each occupy one
// line of that output just as they occupy one line of the source.
//
// A rejection inside the region takes its line from LineInRegion in
// lib/cpp/test_helpers/helpers_keyword_version.h rather than writing it, so a
// change to what the builder puts above the body moves every such test at
// once. LineInRegion answers for a Guarded source because Guarded writes the
// same single directive line above its body that In writes.

// The module of §22.14.1's second and third examples, with the port list and
// body the LRM elides written out. The 64-bit variable is named `logic`, which
// is what makes acceptance depend on the reserved word list in effect.
constexpr const char* kM2Module =
    "module m2 (input wire clk, output wire q);\n"
    "  reg [63:0] logic;\n"
    "endmodule\n";

// The interface of §22.14.1's fourth and fifth examples, likewise filled in.
constexpr const char* kInterface =
    "interface if1 (input wire clk);\n"
    "  wire [7:0] data;\n"
    "endinterface\n";

std::string Guarded(const std::string& specifier, const std::string& body) {
  return "`begin_keywords \"" + specifier + "\"\n" + body + "`end_keywords\n";
}

// §22.14.1's first example: a module with no `begin_keywords directive in
// effect is read under the implementation's default reserved word list. The
// module parses; and because this implementation defaults to 1800-2023, the
// same module body spelled with `logic` as a variable name — legal under the
// older lists — is rejected when nothing selects one of them.
TEST(KeywordVersionExampleParsing, ModuleWithNoDirectiveUsesTheDefaultList) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m1;\n"
                              "  reg [63:0] v;\n"
                              "endmodule\n"));

  // §6.8 owns the report: `logic` stands where Parser::ParseVarDeclList reads
  // the declared name of a variable, and the default list makes a keyword of
  // it. No directive stands above the declaration, so it is reported on the
  // line it is written on.
  auto r = ParseWithPreprocessor(kM2Module);
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got 'logic'", 2, "6.8"));
}

// The same claim from the two other positions a module can occupy relative to
// a pair: ahead of the first `begin_keywords, and after a pair has closed. In
// both, no directive is in effect over the module, so the default list governs
// it — the region in the middle of the source does not reach it either way.
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

  // The negative in both positions: the older list's spelling of the module is
  // not readable outside the pair that selects that list.
  auto ahead =
      ParseWithPreprocessor(std::string(kM2Module) +
                            Guarded("1364-2001", "module other;\nendmodule\n"));
  EXPECT_TRUE(
      ReportedError(ahead.diags, "expected identifier, got 'logic'", 2, "6.8"));

  // Behind the pair the declaration is written on line 6 and reported on line
  // 6, each of the two directives above it occupying one output line. The line
  // is written out rather than taken from LineInRegion, which answers only for
  // a line inside the region.
  auto behind =
      ParseWithPreprocessor(Guarded("1364-2001", "module other;\nendmodule\n") +
                            std::string(kM2Module));
  EXPECT_TRUE(ReportedError(behind.diags, "expected identifier, got 'logic'", 6,
                            "6.8"));
}

// §22.14.1's second example. Under a version_specifier naming 1364-2001,
// `logic` is not a reserved word, so it is available as the declared name of
// the module's variable. The LRM adds that "1364-1995" and "1364-2005" would
// serve the example just as well, so all three specifiers are exercised on the
// one module text.
TEST(KeywordVersionExampleParsing, VerilogRegionAcceptsLogicAsAVariableName) {
  for (const char* specifier : {"1364-2001", "1364-1995", "1364-2005"}) {
    EXPECT_TRUE(ParseWithPreprocessorOk(Guarded(specifier, kM2Module)))
        << specifier;
  }
}

// §22.14.1's third example: the same source under "1800-2005", where `logic`
// is reserved, is an error. Every later SystemVerilog list reserves it too, so
// the example fails the same way under each of them.
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

// The example declares its variable as a packed 64-bit `reg`, but what the
// region frees is the identifier, not one declaration form — so the word is
// available for a variable of every type a module in that era could declare.
// Each spelling below is a separate declaration path through the parser, and
// each is paired with its rejection under a list that does reserve the word.
TEST(KeywordVersionExampleParsing,
     VerilogRegionAcceptsLogicAsEveryVariableType) {
  const char* const kDeclarations[] = {
      "reg [63:0] logic;",  // the example's own form: a packed vector
      "reg logic;",         // the same type unpacked, a single bit
      "integer logic;",    "real logic;", "time logic;",
  };
  for (const char* decl : kDeclarations) {
    const std::string kBody =
        std::string("module t;\n  ") + decl + "\nendmodule\n";
    EXPECT_TRUE(ParseWithPreprocessorOk(Guarded("1364-2001", kBody))) << decl;
    // Every spelling heads its declaration with a variable type, so all five
    // reach the same §6.8 report on the name that follows it.
    auto r = ParseWithPreprocessor(Guarded("1800-2005", kBody));
    EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got 'logic'",
                              LineInRegion(2), "6.8"))
        << decl;
  }
}

// §22.14.1's fourth example: with "1800-2005" selected, the implementation
// uses the reserved word list of this standard, under which `interface` and
// `endinterface` are keywords — so an interface declaration, a design element
// of a kind other than a module, parses inside the region.
TEST(KeywordVersionExampleParsing, SystemVerilogRegionAcceptsTheInterface) {
  EXPECT_TRUE(ParseWithPreprocessorOk(Guarded("1800-2005", kInterface)));
}

// §22.14.1's fifth example, which differs from the fourth only in naming
// "1364-2005": neither word that delimits the interface is reserved by that
// list, so the declaration no longer parses. The same holds for the older
// 1364 lists, none of which reserves either word.
TEST(KeywordVersionExampleParsing, VerilogRegionRejectsTheInterface) {
  for (const char* specifier : {"1364-2005", "1364-2001", "1364-1995"}) {
    // §3.12.1 owns the report: with `interface` an ordinary identifier again,
    // the declaration heads nothing the compilation unit admits and
    // Parser::ReportUnexpectedTopLevelToken says so in src/parser/parser.cpp.
    auto r = ParseWithPreprocessor(Guarded(specifier, kInterface));
    EXPECT_TRUE(ReportedError(r.diags, "expected top-level declaration",
                              LineInRegion(1), "3.12.1"))
        << specifier;
  }
}

// The positive reading of the same fact, which the fifth example's failure
// only shows indirectly: what makes that example fail is that 1364-2005
// reserves neither word, and an unreserved word is an ordinary identifier. So
// in a position where an identifier belongs, both spellings are usable names
// under that list — and both stop being usable once a list that reserves them
// is selected. This reaches the closing word on its own, which the failing
// interface declaration cannot isolate.
TEST(KeywordVersionExampleParsing, VerilogRegionAcceptsInterfaceWordsAsNames) {
  for (const char* word : {"interface", "endinterface"}) {
    const std::string kBody =
        std::string("module t;\n  wire ") + word + ";\nendmodule\n";
    EXPECT_TRUE(ParseWithPreprocessorOk(Guarded("1364-2005", kBody))) << word;
    // §6.7 owns the report rather than §6.8, because `wire` heads the
    // declaration and Parser::ParseVarDeclList files a net declaration's name
    // under §6.7.
    auto r = ParseWithPreprocessor(Guarded("1800-2005", kBody));
    EXPECT_TRUE(ReportedError(
        r.diags, std::string("expected identifier, got '") + word + "'",
        LineInRegion(2), "6.7"))
        << word;
  }
}

}  // namespace
