#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
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

constexpr std::string_view kOwner = "acme-semiconductor";

constexpr std::string_view kOtherOwner = "globex-ip";

constexpr std::string_view kKeyName = "data-2026";

constexpr std::string_view kOwnerKey = "acme-region-exchange-key";
constexpr std::string_view kOtherOwnerKey = "globex-region-exchange-key";

constexpr std::string_view kExchangeKey = "one-key-of-the-authors-own";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

constexpr std::string_view kBlockDirective = "`pragma protect data_block\n";

bool Carries(std::string_view text, std::string_view written) {
  return text.find(written) != std::string_view::npos;
}

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

std::string NamesOwner(std::string_view value) {
  std::string directive = "`pragma protect data_keyowner=";
  directive.append(value).append("\n");
  return directive;
}

std::string NamesOwnerInAList(std::string_view owner) {
  std::string list = "(company=\"";
  list.append(owner).append("\")");
  return NamesOwner(list);
}

std::string Region(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

ProtectKeyList KeysOfBothParties() {
  ProtectKeyList keys;
  keys.Add(
      {std::string(kOwner), std::string(kKeyName), std::string(kOwnerKey)});
  keys.Add({std::string(kOtherOwner), std::string(kKeyName),
            std::string(kOtherOwnerKey)});
  return keys;
}

PreprocConfig KeysConfig() {
  PreprocConfig config;
  config.protect_keys = KeysOfBothParties();
  return config;
}

PreprocConfig HoldingTheKey() {
  PreprocConfig config;
  config.protect_key = std::string(kExchangeKey);
  return config;
}

struct ReadUnderKeys {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp;
  std::string text;

  explicit ReadUnderKeys(const std::string& src) : pp(mgr, diag, KeysConfig()) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  ProtectKeywordValue ValueOf(std::string_view keyword) const {
    return pp.ProtectKeywords().ValueOf(keyword);
  }
};

std::string EnvelopeUnderNames(const std::string& described) {
  std::string envelope =
      EncryptEnvelopes(Region(described), "", KeysOfBothParties());
  EXPECT_FALSE(Carries(envelope, kSealedDesign));
  return envelope;
}

std::string EnvelopeUnderOneKey(const std::string& described) {
  std::string envelope = EncryptEnvelopes(Region(described), kExchangeKey);
  EXPECT_FALSE(Carries(envelope, kSealedDesign));
  return envelope;
}

std::string EnvelopeReadUnder(const std::string& envelope,
                              const std::string& directive) {
  std::string text = envelope;
  size_t block = text.find(kBlockDirective);
  EXPECT_NE(block, std::string::npos);
  return text.insert(block, directive);
}

uint32_t WhereTheNamedBlockIsRead(std::string_view envelope) {
  return LineHolding(envelope, kBlockDirective) + 1;
}

TEST(ProtectDataKeyownerSyntax, TheStringAgainstTheKeywordNamesTheEntity) {
  ReadUnderKeys run(Writes("data_keyowner", kOwner));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, kOwner);
}

TEST(ProtectDataKeyownerSyntax, AnEntityNameHoldingACommaIsOneValue) {
  ReadUnderKeys run(Writes("data_keyowner", "Acme, Incorporated"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "Acme, Incorporated");
}

TEST(ProtectDataKeyownerSyntax,
     AnEntityNameInTheTripleQuotedSpellingIsOneValue) {
  std::string src = "`pragma protect data_keyowner=";
  src.append("\"\"\"Acme \"the\" Corp\"\"\"");
  src.append(", data_keyname=\"").append(kKeyName).append("\"\n");
  ReadUnderKeys run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyname").value, kKeyName);
}

TEST(ProtectDataKeyownerSyntax, AnEntityNameHoldingAnEscapedQuoteIsOneValue) {
  std::string src = "`pragma protect data_keyowner=\"Acme \\\"the\\\" Corp\"";
  src.append(", data_keyname=\"").append(kKeyName).append("\"\n");
  ReadUnderKeys run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "Acme \\\"the\\\" Corp");
  EXPECT_EQ(run.ValueOf("data_keyname").value, kKeyName);
}

TEST(ProtectDataKeyownerSyntax, AnEmptyEntityNameIsAString) {
  ReadUnderKeys run(Writes("data_keyowner", ""));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "");
}

TEST(ProtectDataKeyownerSyntax, ABareIdentifierIsOneWrittenThingToo) {
  ReadUnderKeys run(NamesOwner("acme_semiconductor"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "acme_semiconductor");
}

TEST(ProtectDataKeyownerSyntax, ANumberIsOneWrittenThingToo) {
  ReadUnderKeys run(NamesOwner("1997"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "1997");
}

TEST(ProtectDataKeyownerSyntax, AnEscapedIdentifierIsOneWrittenThingToo) {
  ReadUnderKeys run(NamesOwner("\\acme-semiconductor "));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "\\acme-semiconductor");
}

TEST(ProtectDataKeyownerSyntax, PaddingAroundThePunctuationLeavesTheValue) {
  ReadUnderKeys run("`pragma protect data_keyowner = \"acme-semiconductor\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyowner").value, kOwner);
}

TEST(ProtectDataKeyownerSyntax, TheExpressionFirstInADirectiveListIsRead) {
  std::string src = "`pragma protect data_keyowner=\"";
  src.append(kOwner).append("\", data_keyname=\"").append(kKeyName);
  src.append("\"\n");
  ReadUnderKeys run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyowner").value, kOwner);
  EXPECT_EQ(run.ValueOf("data_keyname").value, kKeyName);
}

TEST(ProtectDataKeyownerSyntax, TheExpressionLastInADirectiveListIsRead) {
  std::string src = "`pragma protect data_keyname=\"";
  src.append(kKeyName).append("\", data_keyowner=\"").append(kOwner);
  src.append("\"\n");
  ReadUnderKeys run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyowner").value, kOwner);
}

TEST(ProtectDataKeyownerSyntax, AMacroExpandingToTheWholeExpressionIsRead) {
  std::string src = "`define WHOSE_KEYS data_keyowner=\"";
  src.append(kOwner).append("\"\n`pragma protect `WHOSE_KEYS\n");
  ReadUnderKeys run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyowner").value, kOwner);
}

TEST(ProtectDataKeyownerSyntax, TheEntityARegionNamesReachesItsEnvelope) {
  std::string described = Writes("data_keyowner", kOwner);
  described += Writes("data_keyname", kKeyName);
  std::string envelope = EnvelopeUnderNames(described);
  EXPECT_TRUE(Carries(envelope, Writes("data_keyowner", kOwner)));
}

TEST(ProtectDataKeyownerSyntax, TheEntityAnEnvelopeStatesOpensItsBlock) {
  std::string described = Writes("data_keyowner", kOwner);
  described += Writes("data_keyname", kKeyName);
  PreprocFixture f;
  std::string read = Preprocess(EnvelopeUnderNames(described), f, KeysConfig());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Carries(read, "module sealed_m"));
}

TEST(ProtectDataKeyownerSyntax,
     AnEntityNamedAheadOfABlockIsTheOneItIsReadUnder) {
  std::string described = Writes("data_keyowner", kOwner);
  described += Writes("data_keyname", kKeyName);
  std::string envelope = EnvelopeReadUnder(
      EnvelopeUnderNames(described), Writes("data_keyowner", kOtherOwner));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, KeysConfig());
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      WhereTheNamedBlockIsRead(envelope), "34.3.2"));
  EXPECT_FALSE(Carries(read, "module sealed_m"));
}

TEST(ProtectDataKeyownerSyntax, AListLeavesTheEntityAlreadyNamedStanding) {
  std::string src = Writes("data_keyowner", kOwner);
  src += NamesOwnerInAList(kOtherOwner);
  ReadUnderKeys run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyowner").value, kOwner);
}

TEST(ProtectDataKeyownerSyntax, AListAheadOfABlockLeavesTheEnvelopesOwnEntity) {
  std::string described = Writes("data_keyowner", kOwner);
  described += Writes("data_keyname", kKeyName);
  std::string envelope = EnvelopeReadUnder(EnvelopeUnderNames(described),
                                           NamesOwnerInAList(kOtherOwner));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, KeysConfig());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Carries(read, "module sealed_m"));
}

TEST(ProtectDataKeyownerSyntax, AnEnvelopeStatesNoEntityAListWrote) {
  std::string envelope = EnvelopeUnderOneKey(NamesOwnerInAList(kOtherOwner));
  EXPECT_FALSE(Carries(envelope, "data_keyowner"));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Carries(read, "module sealed_m"));
}

TEST(ProtectDataKeyownerSyntax, AnEntityNamedBeforeAListStillSelectsTheKey) {
  std::string described = Writes("data_keyowner", kOwner);
  described += Writes("data_keyname", kKeyName);
  described += NamesOwnerInAList(kOtherOwner);
  std::string envelope = EnvelopeUnderNames(described);
  EXPECT_TRUE(Carries(envelope, Writes("data_keyowner", kOwner)));
}

TEST(ProtectDataKeyownerSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect data_keyowner =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectDataKeyownerSyntax, AnUnclosedEntityNameIsNoString) {
  PreprocFixture f;
  Preprocess("`pragma protect data_keyowner=\"acme-semiconductor\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`pragma directive contains an illegal token", 1,
                            "22.11"));
}

TEST(ProtectDataKeyownerSyntax, AnEmptyListIsNoValue) {
  PreprocFixture f;
  Preprocess("`pragma protect data_keyowner=()\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectDataKeyownerSyntax, TheKeywordAsAnEscapedIdentifierIsRejected) {
  PreprocFixture f;
  Preprocess("`pragma protect \\data_keyowner = \"acme-semiconductor\"\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

}  // namespace
