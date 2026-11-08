#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kExchangeKey = "globex-exchange-key";

constexpr std::string_view kFurtherWord = "assembled in Springfield";

constexpr std::string_view kAnyOffering = "`pragma protect encrypt_agent_info=";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

constexpr std::string_view kBeginProtected =
    "`pragma protect begin_protected\n";
constexpr std::string_view kEndProtected = "`pragma protect end_protected\n";

bool Carries(std::string_view text, std::string_view written) {
  return text.find(written) != std::string_view::npos;
}

std::string OffersFurther(std::string_view word) {
  std::string directive(kAnyOffering);
  directive.append("\"").append(word).append("\"\n");
  return directive;
}

std::string RegionHolding(std::string_view inside) {
  std::string region = "`pragma protect begin\n";
  region.append(inside).append(kSealedDesign);
  region.append("`pragma protect end\n");
  return region;
}

PreprocConfig HoldingTheKey() {
  PreprocConfig config;
  config.protect_key = std::string(kExchangeKey);
  return config;
}

TEST(ProtectEncryptAgentInfoSyntax, TheKeywordWithAStringContributesNoText) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append(OffersFurther(kFurtherWord)).append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kFurtherWord));
  EXPECT_TRUE(Carries(read, "module m;"));
  EXPECT_TRUE(Carries(read, "endmodule"));
}

TEST(ProtectEncryptAgentInfoSyntax, PaddingAroundTheEqualsLeavesTheExpression) {
  PreprocFixture f;
  std::string src = "`pragma  protect  encrypt_agent_info  =  ";
  src.append("\"assembled in Springfield\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kFurtherWord));
}

TEST(ProtectEncryptAgentInfoSyntax, TheExpressionFirstInAListIsRead) {
  PreprocFixture f;
  std::string src(kAnyOffering);
  src.append("\"assembled in Springfield\", comment=\"rev 3\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kFurtherWord));
}

TEST(ProtectEncryptAgentInfoSyntax, TheExpressionLastInAListIsRead) {
  PreprocFixture f;
  std::string src = "`pragma protect comment=\"rev 3\", ";
  src.append("encrypt_agent_info=\"assembled in Springfield\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kFurtherWord));
}

TEST(ProtectEncryptAgentInfoSyntax, TheExpressionInTheMiddleOfAListIsRead) {
  PreprocFixture f;
  std::string src = "`pragma protect comment=\"rev 3\", ";
  src.append("encrypt_agent_info=\"assembled in Springfield\", ");
  src.append("comment=\"rev 4\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kFurtherWord));
}

TEST(ProtectEncryptAgentInfoSyntax, ABlockCommentInsideTheExpressionIsStepped) {
  PreprocFixture f;
  std::string src = "`pragma protect encrypt_agent_info ";
  src.append("/* what the sealer offered */ = ");
  src.append("\"assembled in Springfield\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kFurtherWord));
}

TEST(ProtectEncryptAgentInfoSyntax, ACommentAfterTheStringLeavesTheExpression) {
  PreprocFixture f;
  std::string src(kAnyOffering);
  src.append("\"assembled in Springfield\" // where it was sealed\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kFurtherWord));
}

TEST(ProtectEncryptAgentInfoSyntax, AMacroExpandingToTheWholeExpressionIsRead) {
  PreprocFixture f;
  std::string src = "`define OFFERS_MORE encrypt_agent_info = ";
  src.append("\"assembled in Springfield\"\n");
  src.append("`pragma protect `OFFERS_MORE\nmodule m;\nendmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kFurtherWord));
  EXPECT_TRUE(Carries(read, "module m;"));
}

TEST(ProtectEncryptAgentInfoSyntax, TheExpressionInsideASealedModelIsRead) {
  PreprocFixture f;
  std::string sealed(kBeginProtected);
  sealed.append(OffersFurther(kFurtherWord)).append(kEndProtected);
  std::string read = Preprocess("module m;\n" + sealed + "endmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kFurtherWord));
  EXPECT_TRUE(Carries(read, "module m;"));
  EXPECT_TRUE(Carries(read, "endmodule"));
}

TEST(ProtectEncryptAgentInfoSyntax, TheNameBrokenAtItsUnderscoreIsRejected) {
  PreprocFixture f;
  std::string src = "`pragma protect encrypt_agent _info=";
  src.append("\"assembled in Springfield\"\n");
  Preprocess(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectEncryptAgentInfoSyntax, AStringHoldingACommaIsOneValue) {
  PreprocFixture f;
  std::string src(kAnyOffering);
  src.append("\"assembled, in Springfield\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "Springfield"));
}

TEST(ProtectEncryptAgentInfoSyntax, AStringHoldingCommentMarksIsOneValue) {
  PreprocFixture f;
  std::string src(kAnyOffering);
  src.append("\"assembled // in Springfield\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "Springfield"));
}

TEST(ProtectEncryptAgentInfoSyntax, AStringHoldingAnEscapedQuoteIsOneValue) {
  PreprocFixture f;
  std::string src(kAnyOffering);
  src.append("\"assembled in \\\"Springfield\\\"\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "Springfield"));
}

TEST(ProtectEncryptAgentInfoSyntax, ATripleQuotedStringWithAQuoteIsOneValue) {
  PreprocFixture f;
  std::string src(kAnyOffering);
  src.append("\"\"\"assembled in \"Springfield\"\"\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "Springfield"));
}

TEST(ProtectEncryptAgentInfoSyntax, AnEmptyStringIsAString) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append(OffersFurther("")).append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "pragma"));
  EXPECT_TRUE(Carries(read, "module m;"));
}

TEST(ProtectEncryptAgentInfoSyntax, AStringSpellingTheExpressionIsOneValue) {
  PreprocFixture f;
  std::string src(kAnyOffering);
  src.append("\"encrypt_agent_info=globex\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "encrypt_agent_info"));
}

TEST(ProtectEncryptAgentInfoSyntax, TheKeywordStandingAloneWritesNoString) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append("`pragma protect encrypt_agent_info\n").append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "pragma"));
  EXPECT_TRUE(Carries(read, "module m;"));
  EXPECT_TRUE(Carries(read, "endmodule"));
}

TEST(ProtectEncryptAgentInfoSyntax, ANumberAgainstTheKeywordIsNotAString) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append(kAnyOffering).append("7\n").append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "pragma"));
  EXPECT_TRUE(Carries(read, "module m;"));
}

TEST(ProtectEncryptAgentInfoSyntax, AnIdentifierAgainstTheKeywordIsNotAString) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append(kAnyOffering).append("globex_sealer_7\n");
  src.append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "globex_sealer_7"));
  EXPECT_TRUE(Carries(read, "module m;"));
}

TEST(ProtectEncryptAgentInfoSyntax, AParenthesizedListIsNotOneWrittenThing) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append(kAnyOffering);
  src.append("(name=\"Globex\", version=\"7\")\n");
  src.append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "Globex"));
  EXPECT_TRUE(Carries(read, "module m;"));
}

struct OfferingInEffect {
  SourceManager sources;
  DiagEngine diag{sources};
  Preprocessor reader{sources, diag, PreprocConfig{}};
  std::string produced;

  explicit OfferingInEffect(const std::string& src) {
    produced = reader.Preprocess(sources.AddFile("<test>", src));
  }

  ProtectKeywordValue Offered() const {
    return reader.ProtectKeywords().ValueOf(kEncryptAgentInfoKeyword);
  }
};

TEST(ProtectEncryptAgentInfoSyntax, AListLeavesTheOfferingAlreadyMadeStanding) {
  std::string src = OffersFurther(kFurtherWord);
  src.append(kAnyOffering);
  src.append("(site=\"North Haverbrook\", batch=\"42\")\n");
  OfferingInEffect run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.Offered().defaulted);
  EXPECT_EQ(run.Offered().value, kFurtherWord);
}

TEST(ProtectEncryptAgentInfoSyntax, AListOnItsOwnOffersNothingFurther) {
  std::string src(kAnyOffering);
  src.append("(site=\"North Haverbrook\", batch=\"42\")\n");
  OfferingInEffect run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Offered().defaulted);
  EXPECT_TRUE(run.Offered().value.empty());
}

TEST(ProtectEncryptAgentInfoSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect encrypt_agent_info =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectEncryptAgentInfoSyntax, AnEmptyParenthesizedValueIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect encrypt_agent_info=()\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectEncryptAgentInfoSyntax, AnUnclosedStringIsNoString) {
  PreprocFixture f;
  std::string src(kAnyOffering);
  src.append("\"assembled in Springfield\n");
  Preprocess(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma directive contains an illegal token", 1,
                            "22.11"));
}

TEST(ProtectEncryptAgentInfoSyntax, AnUnclosedTripleQuotedStringIsNoString) {
  PreprocFixture f;
  std::string src(kAnyOffering);
  src.append("\"\"\"assembled in Springfield\"\n");
  Preprocess(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma directive contains an illegal token", 1,
                            "22.11"));
}

TEST(ProtectEncryptAgentInfoSyntax, AKeywordAndStringWithNoEqualsIsRejected) {
  PreprocFixture f;
  std::string src = "`pragma protect encrypt_agent_info ";
  src.append("\"assembled in Springfield\"\n");
  Preprocess(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectEncryptAgentInfoSyntax, TheKeywordAsAnEscapedIdentifierIsRejected) {
  PreprocFixture f;
  std::string src = "`pragma protect \\encrypt_agent_info = ";
  src.append("\"assembled in Springfield\"\n");
  Preprocess(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectEncryptAgentInfoSyntax, TheExpressionSealedIntoABlockIsReadBack) {
  std::string region = RegionHolding(OffersFurther(kFurtherWord));
  std::string envelope = EncryptEnvelopes(region, kExchangeKey);
  ASSERT_FALSE(Carries(envelope, kSealedDesign));
  ASSERT_FALSE(Carries(envelope, kFurtherWord));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Carries(read, "module sealed_m"));
  EXPECT_FALSE(Carries(read, kFurtherWord));
}

}  // namespace
