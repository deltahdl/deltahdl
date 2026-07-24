#include "fixture_parser.h"

using namespace delta;

namespace {

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

  EXPECT_FALSE(ParseWithPreprocessorOk(kM2Module));
}

// The same claim from the two other positions a module can occupy relative to
// a pair: ahead of the first `begin_keywords, and after a pair has closed. In
// both, no directive is in effect over the module, so the default list governs
// it — the region in the middle of the source does not reach it either way.
TEST(KeywordVersionExampleParsing, DefaultListGovernsOutsideEveryPair) {
  const std::string before =
      "module m1;\n"
      "  logic [63:0] v;\n"
      "endmodule\n" +
      Guarded("1364-2001", kM2Module);
  EXPECT_TRUE(ParseWithPreprocessorOk(before));

  const std::string after = Guarded("1364-2001", kM2Module) +
                            "module m1;\n"
                            "  logic [63:0] v;\n"
                            "endmodule\n";
  EXPECT_TRUE(ParseWithPreprocessorOk(after));

  // The negative in both positions: the older list's spelling of the module is
  // not readable outside the pair that selects that list.
  EXPECT_FALSE(ParseWithPreprocessorOk(
      std::string(kM2Module) +
      Guarded("1364-2001", "module other;\nendmodule\n")));
  EXPECT_FALSE(ParseWithPreprocessorOk(
      Guarded("1364-2001", "module other;\nendmodule\n") +
      std::string(kM2Module)));
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
    EXPECT_FALSE(ParseWithPreprocessorOk(Guarded(specifier, kM2Module)))
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
  const char* kDeclarations[] = {
      "reg [63:0] logic;",  // the example's own form: a packed vector
      "reg logic;",         // the same type unpacked, a single bit
      "integer logic;",    "real logic;", "time logic;",
  };
  for (const char* decl : kDeclarations) {
    const std::string body =
        std::string("module t;\n  ") + decl + "\nendmodule\n";
    EXPECT_TRUE(ParseWithPreprocessorOk(Guarded("1364-2001", body))) << decl;
    EXPECT_FALSE(ParseWithPreprocessorOk(Guarded("1800-2005", body))) << decl;
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
    EXPECT_FALSE(ParseWithPreprocessorOk(Guarded(specifier, kInterface)))
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
    const std::string body =
        std::string("module t;\n  wire ") + word + ";\nendmodule\n";
    EXPECT_TRUE(ParseWithPreprocessorOk(Guarded("1364-2005", body))) << word;
    EXPECT_FALSE(ParseWithPreprocessorOk(Guarded("1800-2005", body))) << word;
  }
}

}  // namespace
