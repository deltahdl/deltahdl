#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kExchangeKey = "globex-exchange-key";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

constexpr std::string_view kBeginProtected =
    "`pragma protect begin_protected\n";
constexpr std::string_view kEndProtected = "`pragma protect end_protected\n";

constexpr std::string_view kBlockDirective = "`pragma protect data_block\n";

constexpr std::string_view kNamedScheme = "base64";

bool Carries(std::string_view text, std::string_view written) {
  return text.find(written) != std::string_view::npos;
}

std::string StatesEncoding(std::string_view list) {
  std::string directive = "`pragma protect encoding=";
  directive.append(list).append("\n");
  return directive;
}

std::string EncodingList(std::string_view enctype, std::string_view after) {
  std::string list = "(enctype=\"";
  list.append(enctype).append("\"").append(after).append(")");
  return list;
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

std::string EnvelopeAround(std::string_view inside) {
  std::string envelope = EncryptEnvelopes(RegionHolding(inside), kExchangeKey);
  EXPECT_FALSE(Carries(envelope, kSealedDesign));
  return envelope;
}

std::string EnvelopeReadUnder(std::string_view directive) {
  std::string envelope = EnvelopeAround("");
  size_t block = envelope.find(kBlockDirective);
  EXPECT_NE(block, std::string::npos);
  return envelope.insert(block, std::string(directive));
}

uint32_t WhereTheEncodedBlockStands(std::string_view envelope) {
  return LineHolding(envelope, kBlockDirective) + 1;
}

TEST(ProtectEncodingSyntax, TheListWithBothOptionalNamesIsRead) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append(StatesEncoding(
      EncodingList(kNamedScheme, ", line_length=64, bytes=128")));
  src.append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "pragma"));
  EXPECT_FALSE(Carries(read, kNamedScheme));
  EXPECT_TRUE(Carries(read, "module m;"));
  EXPECT_TRUE(Carries(read, "endmodule"));
}

TEST(ProtectEncodingSyntax, TheListNamingOnlyASchemeIsRead) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append(StatesEncoding(EncodingList("uuencode", "")));
  src.append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "uuencode"));
  EXPECT_TRUE(Carries(read, "module m;"));
}

TEST(ProtectEncodingSyntax, TheListWithALengthAndNoCountIsRead) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append(StatesEncoding(EncodingList(kNamedScheme, ", line_length=72")));
  src.append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "line_length"));
  EXPECT_TRUE(Carries(read, "module m;"));
}

TEST(ProtectEncodingSyntax, TheListWithACountAndNoLengthIsRead) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append(StatesEncoding(EncodingList(kNamedScheme, ", bytes=256")));
  src.append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "bytes"));
  EXPECT_TRUE(Carries(read, "module m;"));
}

TEST(ProtectEncodingSyntax, PaddingAroundThePunctuationLeavesTheValue) {
  PreprocFixture f;
  std::string src = "`pragma protect encoding = ( enctype = \"base64\" , ";
  src.append("line_length = 64 , bytes = 128 )\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "enctype"));
}

TEST(ProtectEncodingSyntax, TheExpressionFirstInADirectiveListIsRead) {
  PreprocFixture f;
  std::string src = "`pragma protect encoding=";
  src.append(EncodingList(kNamedScheme, ", bytes=128"));
  src.append(", comment=\"rev 3\"\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "rev 3"));
  EXPECT_FALSE(Carries(read, kNamedScheme));
}

TEST(ProtectEncodingSyntax, TheExpressionLastInADirectiveListIsRead) {
  PreprocFixture f;
  std::string src = "`pragma protect comment=\"rev 3\", encoding=";
  src.append(EncodingList(kNamedScheme, ", line_length=64")).append("\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kNamedScheme));
}

TEST(ProtectEncodingSyntax, TheExpressionInsideASealedModelIsRead) {
  PreprocFixture f;
  std::string sealed(kBeginProtected);
  sealed.append(StatesEncoding(EncodingList(kNamedScheme, ", bytes=128")));
  sealed.append(kEndProtected);
  std::string read = Preprocess("module m;\n" + sealed + "endmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kNamedScheme));
  EXPECT_TRUE(Carries(read, "module m;"));
  EXPECT_TRUE(Carries(read, "endmodule"));
}

TEST(ProtectEncodingSyntax, AMacroExpandingToTheWholeListIsRead) {
  PreprocFixture f;
  std::string src = "`define HOW_WRITTEN encoding=";
  src.append(EncodingList(kNamedScheme, ", line_length=64, bytes=128"));
  src.append("\n`pragma protect `HOW_WRITTEN\nmodule m;\nendmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, kNamedScheme));
  EXPECT_TRUE(Carries(read, "module m;"));
}

TEST(ProtectEncodingSyntax, ASchemeNameHoldingACommaIsOneValue) {
  PreprocFixture f;
  std::string read =
      Preprocess(StatesEncoding("(enctype=\"x-acme,scheme\")"), f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "x-acme"));
}

TEST(ProtectEncodingSyntax, ASchemeNameHoldingACloseParenIsOneValue) {
  PreprocFixture f;
  std::string read =
      Preprocess(StatesEncoding("(enctype=\"x-acme)scheme\")"), f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "x-acme"));
}

TEST(ProtectEncodingSyntax, ASchemeNameInTheTripleQuotedSpellingIsOneValue) {
  PreprocFixture f;
  std::string read =
      Preprocess(StatesEncoding("(enctype=\"\"\"x-acme\"scheme\"\"\")"), f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "x-acme"));
}

TEST(ProtectEncodingSyntax, AnEmptySchemeNameIsAString) {
  PreprocFixture f;
  std::string src = "module m;\n";
  src.append(StatesEncoding("(enctype=\"\")")).append("endmodule\n");
  std::string read = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Carries(read, "pragma"));
  EXPECT_TRUE(Carries(read, "module m;"));
}

TEST(ProtectEncodingSyntax, TheSchemeNamedInARegionIsTheEnvelopesOwn) {
  std::string envelope =
      EnvelopeAround(StatesEncoding(EncodingList(kNamedScheme, "")));
  ASSERT_TRUE(Carries(envelope, "enctype=\"base64\""));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Carries(read, "module sealed_m"));
}

TEST(ProtectEncodingSyntax, AValueNamingNoSchemeLeavesTheOneAlreadyNamed) {
  std::string inside(StatesEncoding(EncodingList(kNamedScheme, "")));
  inside.append(StatesEncoding("(bytes=190)"));
  std::string envelope = EnvelopeAround(inside);
  ASSERT_TRUE(Carries(envelope, "enctype=\"base64\""));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Carries(read, "module sealed_m"));
}

TEST(ProtectEncodingSyntax, ASchemeWrittenAsABareWordNamesNothing) {
  std::string envelope = EnvelopeAround(StatesEncoding("(enctype=base64)"));
  EXPECT_FALSE(Carries(envelope, "enctype=\"base64\""));
  EXPECT_TRUE(Carries(envelope, "enctype=\""));
}

TEST(ProtectEncodingSyntax, AStringAgainstTheKeywordNamesNoScheme) {
  std::string envelope =
      EnvelopeAround("`pragma protect encoding=\"base64\"\n");
  EXPECT_FALSE(Carries(envelope, "enctype=\"base64\""));
  EXPECT_TRUE(Carries(envelope, "enctype=\""));
}

TEST(ProtectEncodingSyntax, TheCountAnEnvelopeStatesFitsItsOwnBlock) {
  std::string envelope = EnvelopeAround("");
  ASSERT_TRUE(Carries(envelope, "bytes="));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Carries(read, "module sealed_m"));
}

TEST(ProtectEncodingSyntax, ACountDisagreeingWithTheBlockIsReported) {
  std::string list =
      EncodingList(DefaultProtectEncoding().enctype, ", bytes=1");
  PreprocFixture f;
  std::string src = EnvelopeReadUnder(StatesEncoding(list));
  Preprocess(src, f, HoldingTheKey());
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma value stands for a different number of bytes from the "
      "one the encoding in effect states",
      WhereTheEncodedBlockStands(src), "34.5.9.2"));
}

TEST(ProtectEncodingSyntax, ALengthBetweenTheSchemeAndCountLeavesBoth) {
  std::string list = EncodingList(DefaultProtectEncoding().enctype,
                                  ", line_length=8, bytes=1");
  PreprocFixture f;
  std::string src = EnvelopeReadUnder(StatesEncoding(list));
  Preprocess(src, f, HoldingTheKey());
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma value stands for a different number of bytes from the "
      "one the encoding in effect states",
      WhereTheEncodedBlockStands(src), "34.5.9.2"));
}

TEST(ProtectEncodingSyntax, ALengthWrittenAsAStringLeavesTheCountBeyondIt) {
  std::string list = EncodingList(DefaultProtectEncoding().enctype,
                                  ", line_length=\"wide\", bytes=1");
  PreprocFixture f;
  std::string src = EnvelopeReadUnder(StatesEncoding(list));
  Preprocess(src, f, HoldingTheKey());
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma value stands for a different number of bytes from the "
      "one the encoding in effect states",
      WhereTheEncodedBlockStands(src), "34.5.9.2"));
}

TEST(ProtectEncodingSyntax, TheNamesAreReadForThemselvesWhateverTheOrder) {
  std::string list = "(bytes=1, line_length=8, enctype=\"";
  list.append(DefaultProtectEncoding().enctype).append("\")");
  PreprocFixture f;
  std::string src = EnvelopeReadUnder(StatesEncoding(list));
  Preprocess(src, f, HoldingTheKey());
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma value stands for a different number of bytes from the "
      "one the encoding in effect states",
      WhereTheEncodedBlockStands(src), "34.5.9.2"));
}

TEST(ProtectEncodingSyntax, ACountWrittenAsAStringIsNoCount) {
  std::string list =
      EncodingList(DefaultProtectEncoding().enctype, ", bytes=\"1\"");
  PreprocFixture f;
  std::string read =
      Preprocess(EnvelopeReadUnder(StatesEncoding(list)), f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Carries(read, "module sealed_m"));
}

TEST(ProtectEncodingSyntax, ACountInAListNamingNoSchemeStatesNothing) {
  PreprocFixture f;
  std::string read = Preprocess(EnvelopeReadUnder(StatesEncoding("(bytes=1)")),
                                f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Carries(read, "module sealed_m"));
}

TEST(ProtectEncodingSyntax, TheKeywordStandingAloneStatesNoScheme) {
  PreprocFixture f;
  std::string read = Preprocess(EnvelopeReadUnder("`pragma protect encoding\n"),
                                f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Carries(read, "module sealed_m"));
}

TEST(ProtectEncodingSyntax, AnEmptyListIsNoValue) {
  PreprocFixture f;
  Preprocess("`pragma protect encoding=()\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectEncodingSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect encoding =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectEncodingSyntax, AListLeftUnclosedIsNoValue) {
  PreprocFixture f;
  Preprocess("`pragma protect encoding=(enctype=\"base64\"\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectEncodingSyntax, AnUnclosedSchemeNameIsNoString) {
  PreprocFixture f;
  Preprocess("`pragma protect encoding=(enctype=\"base64)\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma directive contains an illegal token", 1,
                            "22.11"));
}

TEST(ProtectEncodingSyntax, ABareWordAmongTheSubkeywordsQualifiesNothing) {
  std::string list =
      EncodingList(DefaultProtectEncoding().enctype, ", padded, bytes=1");
  PreprocFixture f;
  std::string src = EnvelopeReadUnder(StatesEncoding(list));
  Preprocess(src, f, HoldingTheKey());
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma value stands for a different number of bytes from the "
      "one the encoding in effect states",
      WhereTheEncodedBlockStands(src), "34.5.9.2"));
}

std::string StatedForARegionWriting(std::string_view list) {
  std::string envelope = EnvelopeAround(StatesEncoding(list));
  size_t at = envelope.find("`pragma protect encoding=");
  EXPECT_NE(at, std::string::npos) << envelope;
  size_t ends = envelope.find('\n', at);
  return envelope.substr(at, ends - at);
}

constexpr std::string_view kStatesNothingTaken =
    "`pragma protect encoding=(enctype=\"x-deltahdl-block\")";

TEST(ProtectEncodingSyntax, ARegionsListIsReadPastThePaddingAfterEachValue) {
  EXPECT_EQ(StatedForARegionWriting("(enctype=\"base64\" , line_length=8 )"),
            "`pragma protect encoding=(enctype=\"base64\", line_length=8)");
}

TEST(ProtectEncodingSyntax, ACommaInsideANestedListSeparatesNothing) {
  EXPECT_EQ(StatedForARegionWriting(
                "(enctype=\"base64\", x_acme=(1,2), line_length=8)"),
            "`pragma protect encoding=(enctype=\"base64\", line_length=8)");
}

TEST(ProtectEncodingSyntax, AnEscapedQuoteInsideTheSchemeNameEndsNothing) {
  std::string stated = StatedForARegionWriting(
      "(enctype=\"x-acme\\\",line_length=9\", line_length=8)");
  EXPECT_TRUE(Carries(stated, "line_length=8")) << stated;
  EXPECT_FALSE(Carries(stated, "line_length=9")) << stated;
}

TEST(ProtectEncodingSyntax, ALengthSpelledOtherThanInDigitsIsNoLength) {
  EXPECT_EQ(StatedForARegionWriting("(enctype=\"base64\", line_length=x8)"),
            "`pragma protect encoding=(enctype=\"base64\")");
}

TEST(ProtectEncodingSyntax, ARegionsListNamingNoSchemeIsNotTaken) {
  EXPECT_EQ(StatedForARegionWriting("(enctype=b, line_length=8)"),
            kStatesNothingTaken);
}

TEST(ProtectEncodingSyntax, AListTheGrammarRejectsStatesNothing) {
  for (std::string_view list : {
           "(enctype=\"base64\", line_length=)",
           "(enctype=\"base64\", line_length=8))",
           "(enctype=\"base64, line_length=8)",
           "(enctype=\"base64\\",
           "(enctype=\"base64\", line_length=8",
       }) {
    EXPECT_EQ(StatedForARegionWriting(list), kStatesNothingTaken) << list;
  }
}

TEST(ProtectEncodingSyntax, TheKeywordAsAnEscapedIdentifierIsRejected) {
  PreprocFixture f;
  Preprocess("`pragma protect \\encoding = (enctype = \"base64\")\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

}  // namespace
