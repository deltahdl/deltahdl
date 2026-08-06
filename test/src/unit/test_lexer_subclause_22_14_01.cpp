#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "lexer/lexer.h"

using namespace delta;

namespace {

// Drives the real directive through the preprocessor, lexes what comes out,
// and reports the kind each of `words` lexed with — so the token kinds
// observed below are the ones the version marker produced rather than ones a
// hand-built marker was asked for. A word the lexer never produced comes back
// as kError, which no expectation below accepts.
std::vector<TokenKind> PreprocessAndLexKinds(
    const std::string& src, const std::vector<std::string_view>& words) {
  PreprocFixture f;
  auto out = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());

  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<preprocessed>", out);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tokens = lexer.LexAll();

  std::vector<TokenKind> kinds(words.size(), TokenKind::kError);
  for (size_t i = 0; i < words.size(); ++i) {
    for (const auto& tok : tokens) {
      if (tok.text == words[i]) {
        kinds[i] = tok.kind;
        break;
      }
    }
  }
  return kinds;
}

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

// §22.14.1's second example, driven through the directive that produces it.
// The LRM names "1364-2001" and says "1364-1995" or "1364-2005" would serve
// the example just as well, none of them reserving `logic`; under each, the
// declaration's `logic` really does come out of the lexer as an ordinary
// identifier, while every word those lists do reserve — `module`, `reg`,
// `wire`, `endmodule` — still lexes as its keyword. The region picks the
// reserved word list and touches nothing else.
TEST(KeywordVersionExampleLexing, VerilogRegionLexesLogicAsAnIdentifier) {
  for (const char* specifier : {"1364-2001", "1364-1995", "1364-2005"}) {
    auto kinds =
        PreprocessAndLexKinds(Guarded(specifier, kM2Module),
                              {"logic", "module", "reg", "wire", "endmodule"});
    EXPECT_EQ(kinds[0], TokenKind::kIdentifier) << specifier;
    EXPECT_EQ(kinds[1], TokenKind::kKwModule) << specifier;
    EXPECT_EQ(kinds[2], TokenKind::kKwReg) << specifier;
    EXPECT_EQ(kinds[3], TokenKind::kKwWire) << specifier;
    EXPECT_EQ(kinds[4], TokenKind::kKwEndmodule) << specifier;
  }
}

// §22.14.1's third example, and the reason the second one needs its directive
// at all: `logic` is a reserved word in SystemVerilog, so under "1800-2005" —
// and under every later list of this standard's line — the identical source
// hands the parser the type keyword where the variable's name belongs. That is
// the token-level cause of the error the LRM predicts.
TEST(KeywordVersionExampleLexing, SystemVerilogRegionLexesLogicAsAKeyword) {
  for (const char* specifier :
       {"1800-2005", "1800-2009", "1800-2012", "1800-2017", "1800-2023"}) {
    auto kinds =
        PreprocessAndLexKinds(Guarded(specifier, kM2Module), {"logic"});
    EXPECT_EQ(kinds[0], TokenKind::kKwLogic) << specifier;
  }
}

// The fourth example end to end: under the reserved word list of this standard
// the words that open and close the interface are keywords, so the declaration
// reaches the parser as a design element rather than as loose identifiers.
TEST(KeywordVersionExampleLexing, SystemVerilog2005RegionLexesTheInterface) {
  auto kinds = PreprocessAndLexKinds(Guarded("1800-2005", kInterface),
                                     {"interface", "endinterface"});
  EXPECT_EQ(kinds[0], TokenKind::kKwInterface);
  EXPECT_EQ(kinds[1], TokenKind::kKwEndinterface);
}

// The fifth example end to end, and the reason it produces errors: "1364-2005"
// reserves neither word, and neither do the older Verilog lists §22.14.1
// names, so both arrive as ordinary identifiers.
TEST(KeywordVersionExampleLexing, VerilogRegionLexesInterfaceAsIdentifiers) {
  for (const char* specifier : {"1364-2005", "1364-2001", "1364-1995"}) {
    auto kinds = PreprocessAndLexKinds(Guarded(specifier, kInterface),
                                       {"interface", "endinterface"});
    EXPECT_EQ(kinds[0], TokenKind::kIdentifier) << specifier;
    EXPECT_EQ(kinds[1], TokenKind::kIdentifier) << specifier;
  }
}

// §22.14.1's first example: with no directive governing the module, the
// reserved word list is the implementation's default set. This implementation
// defaults to 1800-2023, so the very declaration the 1364-2001 region above
// accepts as a name arrives here as the type keyword instead.
TEST(KeywordVersionExampleLexing, ModuleWithNoDirectiveUsesTheDefaultList) {
  auto kinds = PreprocessAndLexKinds(
      "module m1;\n"
      "  reg [63:0] logic;\n"
      "endmodule\n",
      {"logic", "module"});
  EXPECT_EQ(kinds[0], TokenKind::kKwLogic);
  EXPECT_EQ(kinds[1], TokenKind::kKwModule);
}

// The other half of that first example's condition — the directive is absent
// *before* the module, not absent from the file. A region opened further down
// governs only what follows it, so the earlier occurrence of the word is still
// classified under the default list while the later one, inside the region, is
// not. One source, one word, two kinds, decided by position.
TEST(KeywordVersionExampleLexing, RegionDoesNotReachBackOverEarlierSource) {
  PreprocFixture f;
  auto out = Preprocess(
      "module m1;\n"
      "  reg [63:0] logic;\n"
      "endmodule\n"
      "`begin_keywords \"1364-2001\"\n"
      "module m2;\n"
      "  reg [63:0] logic;\n"
      "endmodule\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<preprocessed>", out);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tokens = lexer.LexAll();

  std::vector<TokenKind> logic_kinds;
  for (const auto& tok : tokens) {
    if (tok.text == "logic") logic_kinds.push_back(tok.kind);
  }
  ASSERT_EQ(logic_kinds.size(), 2u);
  EXPECT_EQ(logic_kinds[0], TokenKind::kKwLogic);
  EXPECT_EQ(logic_kinds[1], TokenKind::kIdentifier);
}

}  // namespace
