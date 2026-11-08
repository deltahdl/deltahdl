#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kExchangeKey = "globex-exchange-key";

constexpr std::string_view kAgentName = "Globex Sealer 7";

constexpr std::string_view kAgentDirective =
    "`pragma protect encrypt_agent=\"Globex Sealer 7\"\n";

constexpr std::string_view kAnyAgentExpression =
    "`pragma protect encrypt_agent=";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

constexpr std::string_view kBeginProtected =
    "`pragma protect begin_protected\n";
constexpr std::string_view kEndProtected = "`pragma protect end_protected\n";

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

size_t TimesWritten(std::string_view text, std::string_view needle) {
  size_t count = 0;
  for (size_t at = text.find(needle); at != std::string_view::npos;
       at = text.find(needle, at + needle.size())) {
    ++count;
  }
  return count;
}

std::string GeneratedExpression() {
  return std::string("`pragma protect encrypt_agent=\"")
      .append(kEncryptAgent)
      .append("\"\n");
}

std::string RegionAround(std::string_view written) {
  std::string text = "`pragma protect begin\n";
  text.append(written).append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

std::string Encrypted(const std::string& src) {
  return EncryptEnvelopes(src, kExchangeKey);
}

struct ReadBack {
  static PreprocConfig Configured(std::string_view key) {
    PreprocConfig config;
    config.protect_key = std::string(key);
    return config;
  }

  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  explicit ReadBack(const std::string& src, std::string_view key = {}) {
    Preprocessor pp(mgr, diag, Configured(key));
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  bool Holds(std::string_view needle) const {
    return text.find(needle) != std::string::npos;
  }
};

TEST(ProtectEncryptAgentSyntax, TheToolWritesTheKeywordWithAStringAgainstIt) {
  std::string envelope = Encrypted(RegionAround(""));
  EXPECT_FALSE(Holds(envelope, kSealedDesign));
  EXPECT_TRUE(Holds(envelope, GeneratedExpression()));
}

TEST(ProtectEncryptAgentSyntax, TheGeneratedValueIsNotWrittenAsABareName) {
  std::string envelope = Encrypted(RegionAround(""));
  std::string unquoted(kAnyAgentExpression);
  unquoted.append(kEncryptAgent);
  EXPECT_TRUE(Holds(envelope, GeneratedExpression()));
  EXPECT_FALSE(Holds(envelope, unquoted));
}

TEST(ProtectEncryptAgentSyntax, TheToolNeverWritesTheKeywordStandingAlone) {
  std::string envelope = Encrypted(RegionAround(""));
  EXPECT_EQ(TimesWritten(envelope, kAnyAgentExpression), 1U);
  EXPECT_FALSE(Holds(envelope, "`pragma protect encrypt_agent\n"));
}

TEST(ProtectEncryptAgentSyntax, TheGeneratedExpressionIsReadBackAsWritten) {
  ReadBack read(Encrypted(RegionAround("")), kExchangeKey);
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.Holds(kEncryptAgent));
}

TEST(ProtectEncryptAgentSyntax, AParenthesizedListIsNotTheGeneratedValue) {
  std::string listed =
      "`pragma protect encrypt_agent=(name=\"Globex\", version=\"7\")\n";
  std::string envelope = Encrypted(RegionAround(listed));
  EXPECT_TRUE(Holds(envelope, kBeginProtected));
  EXPECT_TRUE(Holds(envelope, GeneratedExpression()));
  EXPECT_EQ(TimesWritten(envelope, kAnyAgentExpression), 1U);
}

TEST(ProtectEncryptAgentSyntax, TheKeywordWithAStringContributesNoText) {
  ReadBack read("module m;\n" + std::string(kAgentDirective) + "endmodule\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAgentName));
  EXPECT_TRUE(read.Holds("module m;"));
  EXPECT_TRUE(read.Holds("endmodule"));
}

TEST(ProtectEncryptAgentSyntax, PaddingAroundTheEqualsLeavesTheExpression) {
  ReadBack read("`pragma  protect  encrypt_agent  =  \"Globex Sealer 7\"\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAgentName));
}

TEST(ProtectEncryptAgentSyntax, TheExpressionFirstInAListIsRead) {
  ReadBack read(
      "`pragma protect encrypt_agent=\"Globex Sealer 7\", comment=\"rev 3\"\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAgentName));
}

TEST(ProtectEncryptAgentSyntax, TheExpressionLastInAListIsRead) {
  ReadBack read(
      "`pragma protect comment=\"rev 3\", encrypt_agent=\"Globex Sealer 7\"\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAgentName));
}

TEST(ProtectEncryptAgentSyntax, TheExpressionInTheMiddleOfAListIsRead) {
  std::string listed = "`pragma protect comment=\"rev 3\", ";
  listed.append("encrypt_agent=\"Globex Sealer 7\", comment=\"rev 4\"\n");
  ReadBack read(listed);
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAgentName));
}

TEST(ProtectEncryptAgentSyntax, ABlockCommentInsideTheExpressionIsStepped) {
  ReadBack read(
      "`pragma protect encrypt_agent /* the sealer */ = \"Globex Sealer 7\"\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAgentName));
}

TEST(ProtectEncryptAgentSyntax, ACommentAfterTheStringLeavesTheExpression) {
  ReadBack read(
      "`pragma protect encrypt_agent=\"Globex Sealer 7\" // who sealed it\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAgentName));
}

TEST(ProtectEncryptAgentSyntax, AMacroExpandingToTheWholeExpressionIsRead) {
  ReadBack read(
      "`define NAMES_THE_AGENT encrypt_agent = \"Globex Sealer 7\"\n"
      "`pragma protect `NAMES_THE_AGENT\n"
      "module m;\nendmodule\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAgentName));
  EXPECT_TRUE(read.Holds("module m;"));
}

TEST(ProtectEncryptAgentSyntax, TheExpressionInsideASealedModelIsRead) {
  std::string envelope(kBeginProtected);
  envelope.append(kAgentDirective).append(kEndProtected);
  ReadBack read("module m;\n" + envelope + "endmodule\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAgentName));
  EXPECT_TRUE(read.Holds("module m;"));
  EXPECT_TRUE(read.Holds("endmodule"));
}

TEST(ProtectEncryptAgentSyntax, AStringHoldingACommaIsOneValue) {
  ReadBack read("`pragma protect encrypt_agent=\"Globex, Sealer 7\"\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds("Globex"));
}

TEST(ProtectEncryptAgentSyntax, AStringHoldingCommentPunctuationIsOneValue) {
  ReadBack read("`pragma protect encrypt_agent=\"Globex // Sealer 7\"\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds("Globex"));
}

TEST(ProtectEncryptAgentSyntax, AStringHoldingAnEscapedQuoteIsOneValue) {
  ReadBack read(
      "`pragma protect encrypt_agent=\"Globex \\\"the Sealer\\\" 7\"\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds("Globex"));
}

TEST(ProtectEncryptAgentSyntax, ATripleQuotedStringHoldingAQuoteIsOneValue) {
  ReadBack read(
      "`pragma protect encrypt_agent=\"\"\"Globex \"Sealer\" 7\"\"\"\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds("Globex"));
}

TEST(ProtectEncryptAgentSyntax, AnEmptyStringIsAString) {
  ReadBack read("module m;\n`pragma protect encrypt_agent=\"\"\nendmodule\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds("pragma"));
  EXPECT_TRUE(read.Holds("module m;"));
}

TEST(ProtectEncryptAgentSyntax, AStringSpellingTheExpressionIsOneValue) {
  ReadBack read("`pragma protect encrypt_agent=\"encrypt_agent=globex\"\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds("encrypt_agent"));
}

struct AgentInEffect {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, PreprocConfig{}};
  std::string text;

  explicit AgentInEffect(const std::string& src) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  ProtectKeywordValue Named() const {
    return pp.ProtectKeywords().ValueOf(kEncryptAgentKeyword);
  }
};

TEST(ProtectEncryptAgentSyntax, AListLeavesTheToolAlreadyNamedStanding) {
  std::string src(kAgentDirective);
  src.append(kAnyAgentExpression);
  src.append("(vendor=\"Ogdenville\", release=\"11\")\n");
  AgentInEffect run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.Named().defaulted);
  EXPECT_EQ(run.Named().value, kAgentName);
}

TEST(ProtectEncryptAgentSyntax, AListOnItsOwnNamesNoTool) {
  std::string src(kAnyAgentExpression);
  src.append("(vendor=\"Ogdenville\", release=\"11\")\n");
  AgentInEffect run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Named().defaulted);
  EXPECT_TRUE(run.Named().value.empty());
}

TEST(ProtectEncryptAgentSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  ReadBack read("`pragma protect encrypt_agent =\n");
  EXPECT_TRUE(ReportedError(read.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectEncryptAgentSyntax, AnEmptyParenthesizedValueIsNoExpression) {
  ReadBack read("`pragma protect encrypt_agent=()\n");
  EXPECT_TRUE(ReportedError(read.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectEncryptAgentSyntax, AnUnclosedStringIsNoString) {
  ReadBack read("`pragma protect encrypt_agent=\"Globex Sealer 7\n");
  EXPECT_TRUE(ReportedError(read.diag.Diagnostics(),
                            "`pragma directive contains an illegal token", 1,
                            "22.11"));
}

TEST(ProtectEncryptAgentSyntax, AnUnclosedTripleQuotedStringIsNoString) {
  ReadBack read("`pragma protect encrypt_agent=\"\"\"Globex Sealer 7\"\n");
  EXPECT_TRUE(ReportedError(read.diag.Diagnostics(),
                            "`pragma directive contains an illegal token", 1,
                            "22.11"));
}

TEST(ProtectEncryptAgentSyntax, TheKeywordAndAStringWithNoEqualsIsRejected) {
  ReadBack read("`pragma protect encrypt_agent \"Globex Sealer 7\"\n");
  EXPECT_TRUE(ReportedError(read.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectEncryptAgentSyntax, TheKeywordAsAnEscapedIdentifierIsRejected) {
  ReadBack read("`pragma protect \\encrypt_agent = \"Globex Sealer 7\"\n");
  EXPECT_TRUE(ReportedError(read.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectEncryptAgentSyntax, ARegionUnderAStatedEncodingCarriesIt) {
  std::string stated = "`pragma protect encoding=(enctype=\"base64\")\n";
  std::string envelope = Encrypted(RegionAround(stated));
  ASSERT_TRUE(Holds(envelope, "enctype=\"base64\""));
  EXPECT_TRUE(Holds(envelope, GeneratedExpression()));
  EXPECT_EQ(TimesWritten(envelope, kAnyAgentExpression), 1U);
  ReadBack read(envelope, kExchangeKey);
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_TRUE(read.Holds("module sealed_m"));
}

}  // namespace
