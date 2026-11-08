#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "lexer/lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

std::vector<TokenKind> PreprocessAndLexKinds(
    const std::string& src, const std::vector<std::string_view>& words) {
  PreprocFixture f;
  auto out = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());

  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<preprocessed>", out);
  Lexer lexer(mgr.FileContent(fid), fid, diag, TextOrigin::kPreprocessorOutput);
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

TEST(KeywordVersionExampleLexing, SystemVerilogRegionLexesLogicAsAKeyword) {
  for (const char* specifier :
       {"1800-2005", "1800-2009", "1800-2012", "1800-2017", "1800-2023"}) {
    auto kinds =
        PreprocessAndLexKinds(Guarded(specifier, kM2Module), {"logic"});
    EXPECT_EQ(kinds[0], TokenKind::kKwLogic) << specifier;
  }
}

TEST(KeywordVersionExampleLexing, SystemVerilog2005RegionLexesTheInterface) {
  auto kinds = PreprocessAndLexKinds(Guarded("1800-2005", kInterface),
                                     {"interface", "endinterface"});
  EXPECT_EQ(kinds[0], TokenKind::kKwInterface);
  EXPECT_EQ(kinds[1], TokenKind::kKwEndinterface);
}

TEST(KeywordVersionExampleLexing, VerilogRegionLexesInterfaceAsIdentifiers) {
  for (const char* specifier : {"1364-2005", "1364-2001", "1364-1995"}) {
    auto kinds = PreprocessAndLexKinds(Guarded(specifier, kInterface),
                                       {"interface", "endinterface"});
    EXPECT_EQ(kinds[0], TokenKind::kIdentifier) << specifier;
    EXPECT_EQ(kinds[1], TokenKind::kIdentifier) << specifier;
  }
}

TEST(KeywordVersionExampleLexing, ModuleWithNoDirectiveUsesTheDefaultList) {
  auto kinds = PreprocessAndLexKinds(
      "module m1;\n"
      "  reg [63:0] logic;\n"
      "endmodule\n",
      {"logic", "module"});
  EXPECT_EQ(kinds[0], TokenKind::kKwLogic);
  EXPECT_EQ(kinds[1], TokenKind::kKwModule);
}

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
  Lexer lexer(mgr.FileContent(fid), fid, diag, TextOrigin::kPreprocessorOutput);
  auto tokens = lexer.LexAll();

  std::vector<TokenKind> logic_kinds;
  for (const auto& tok : tokens) {
    if (tok.text == "logic") logic_kinds.push_back(tok.kind);
  }
  ASSERT_EQ(logic_kinds.size(), 2u);
  EXPECT_EQ(logic_kinds[0], TokenKind::kKwLogic);
  EXPECT_EQ(logic_kinds[1], TokenKind::kIdentifier);
}

TEST(KeywordVersionExampleLexing, DeclarationsKeepTheLineTheyWereWrittenOn) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-2001\" reg [63:0] first;\n"
      "reg [63:0] second;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<preprocessed>", out);
  Lexer lexer(mgr.FileContent(fid), fid, diag, TextOrigin::kPreprocessorOutput);
  auto tokens = lexer.LexAll();

  uint32_t first_line = 0;
  uint32_t second_line = 0;
  for (const auto& tok : tokens) {
    if (tok.text == "first") first_line = tok.loc.line;
    if (tok.text == "second") second_line = tok.loc.line;
  }
  EXPECT_EQ(first_line, 1u);
  EXPECT_EQ(second_line, 2u);
}

}  // namespace
