#include <gtest/gtest.h>

#include <cstddef>
#include <filesystem>
#include <fstream>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"
#include "preprocessor/protect_viewport.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

struct DirectiveRun {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, {}};
  std::string text;

  explicit DirectiveRun(const std::string& src) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  DirectiveRun(const std::string& path, const std::string& src) {
    text = pp.Preprocess(mgr.AddFile(path, src));
  }

  void ReadNextFile(const std::string& path, const std::string& src) {
    text += pp.Preprocess(mgr.AddFile(path, src));
  }

  ProtectKeywordValue ValueOf(std::string_view keyword) const {
    return pp.ProtectKeywords().ValueOf(keyword);
  }

  const ProtectEnvelopeState& Envelopes() const {
    return pp.ProtectEnvelopes();
  }
};

struct IncludeTestDir {
  fs::path dir;

  explicit IncludeTestDir(const std::string& name) {
    dir = fs::temp_directory_path() / ("delta_protect_34_04_" + name);
    fs::create_directories(dir);
  }

  ~IncludeTestDir() { fs::remove_all(dir); }

  void WriteFile(const std::string& rel_path, const std::string& content) {
    std::ofstream ofs(dir / rel_path);
    ofs << content;
  }

  std::string TopPath() const { return (dir / "top.sv").string(); }
};

std::string TabulatedNames() {
  std::string names;
  for (const ProtectPragmaKeyword& keyword : ProtectPragmaKeywords()) {
    if (!names.empty()) names += ' ';
    names.append(keyword.name);
  }
  return names;
}

constexpr std::string_view kAuthorKey = "acme-exchange-key";

PreprocConfig KeyConfig(std::string_view key) {
  PreprocConfig config;
  config.protect_key = key;
  return config;
}

std::string Encrypted(const std::string& src) {
  return EncryptEnvelopes(src, kAuthorKey);
}

size_t Occurrences(std::string_view text, std::string_view needle) {
  size_t count = 0;
  size_t pos = text.find(needle);
  while (pos != std::string_view::npos) {
    ++count;
    pos = text.find(needle, pos + needle.size());
  }
  return count;
}

struct ReadBackWithKey {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp;
  std::string text;

  ReadBackWithKey(const std::string& src, std::string_view key)
      : pp(mgr, diag, KeyConfig(key)) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  ProtectKeywordValue ValueOf(std::string_view keyword) const {
    return pp.ProtectKeywords().ValueOf(keyword);
  }
};

TEST(ProtectPragmaDirectives, TheTabulatedNamesAreTheOnesTheTableLists) {
  EXPECT_EQ(TabulatedNames(),
            "begin end begin_protected end_protected author author_info "
            "encrypt_agent encrypt_agent_info encoding data_keyowner "
            "data_method data_keyname data_public_key data_decrypt_key "
            "data_block digest_keyowner digest_key_method digest_keyname "
            "digest_public_key digest_decrypt_key digest_method digest_block "
            "key_keyowner key_method key_keyname key_public_key key_block "
            "decrypt_license runtime_license comment reset viewport");
}

TEST(ProtectPragmaDirectives, EveryTabulatedNameCarriesWhatItDoes) {
  for (const ProtectPragmaKeyword& keyword : ProtectPragmaKeywords()) {
    EXPECT_TRUE(IsProtectPragmaKeyword(keyword.name)) << keyword.name;
    EXPECT_FALSE(ProtectPragmaKeywordDescription(keyword.name).empty())
        << keyword.name;
  }
}

bool WrittenWithAValue(std::string_view keyword) {
  return IsProtectStringValuedKeyword(keyword) || keyword == "encoding" ||
         keyword == "decrypt_license" || keyword == "runtime_license" ||
         keyword == kViewportKeyword;
}

std::string SourceWriting(std::string_view keyword) {
  if (IsProtectStringValuedKeyword(keyword)) {
    return "`pragma protect " + std::string(keyword) + "=\"acme\"\n";
  }
  if (keyword == "encoding") {
    return "`pragma protect encoding=(enctype=\"raw\")\n";
  }
  if (keyword == "decrypt_license" || keyword == "runtime_license") {
    return "`pragma protect " + std::string(keyword) +
           " = ( library = \"liblic.so\" , entry = \"check\" , feature = "
           "\"core\" )\n";
  }
  if (keyword != kViewportKeyword) {
    return "`pragma protect " + std::string(keyword) + "\n";
  }
  return "`pragma protect begin_protected\n"
         "`pragma protect viewport = ( object = \"top.dut.mem\" , "
         "access = \"read-only\" )\n"
         "`pragma protect end_protected\n";
}

TEST(ProtectPragmaDirectives, EveryTabulatedNameIsAppliedFromASource) {
  for (const ProtectPragmaKeyword& keyword : ProtectPragmaKeywords()) {
    DirectiveRun run(SourceWriting(keyword.name));
    EXPECT_FALSE(run.diag.HasErrors()) << keyword.name;
    EXPECT_EQ(run.ValueOf(keyword.name).defaulted,
              !WrittenWithAValue(keyword.name))
        << keyword.name;
  }
}

TEST(ProtectPragmaDirectives, ATabulatedKeywordIsPutInEffect) {
  DirectiveRun run("`pragma protect data_method=\"des-cbc\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_method").defaulted);
  EXPECT_EQ(run.ValueOf("data_method").value, "des-cbc");
}

TEST(ProtectPragmaDirectives, AKeywordWithAnIdentifierValueIsPutInEffect) {
  DirectiveRun run("`pragma protect data_method=des_cbc\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_method").defaulted);
  EXPECT_EQ(run.ValueOf("data_method").value, "des_cbc");
}

TEST(ProtectPragmaDirectives, AKeywordWithANumberValueIsPutInEffect) {
  DirectiveRun run("`pragma protect comment=1997\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("comment").defaulted);
  EXPECT_EQ(run.ValueOf("comment").value, "1997");
}

TEST(ProtectPragmaDirectives, AKeywordWithAnEscapedIdentifierValueIsInEffect) {
  DirectiveRun run("`pragma protect data_keyname=\\acme-key \n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyname").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyname").value, "\\acme-key");
}

TEST(ProtectPragmaDirectives, AnEscapedSpellingOfATabulatedNameIsNotOne) {
  DirectiveRun run("`pragma protect \\data_method\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.ValueOf("data_method").defaulted);
  EXPECT_TRUE(run.ValueOf("\\data_method").defaulted);
}

TEST(ProtectPragmaDirectives, AMisspeltKeywordIsNotTheNameItResembles) {
  DirectiveRun run("`pragma protect data_keyownr=\"acme\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_TRUE(run.ValueOf("data_keyownr").defaulted);
}

TEST(ProtectPragmaDirectives, ATabulatedNameUnderAnotherPragmaIsNotApplied) {
  DirectiveRun run("`pragma acme_tool data_method=\"des-cbc\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.ValueOf("data_method").defaulted);
}

TEST(ProtectPragmaDirectives, ATabulatedNameInsideAValueIsNotTheDirectives) {
  DirectiveRun run(
      "`pragma protect encoding=(enctype=\"raw\", data_method=\"des-cbc\")\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("encoding").defaulted);
  EXPECT_TRUE(run.ValueOf("data_method").defaulted);
}

TEST(ProtectPragmaDirectives, AnUntabulatedNameWrittenBareIsAppliedByNothing) {
  DirectiveRun run("`pragma protect acme_keyowner\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.ValueOf("acme_keyowner").defaulted);
}

TEST(ProtectPragmaDirectives, TheNamesInsideAValueAreNotTabulated) {
  EXPECT_FALSE(IsProtectPragmaKeyword("enctype"));
  EXPECT_FALSE(IsProtectPragmaKeyword("line_length"));
  EXPECT_FALSE(IsProtectPragmaKeyword("bytes"));
  EXPECT_FALSE(IsProtectPragmaKeyword("object"));
  EXPECT_FALSE(IsProtectPragmaKeyword("access"));
  EXPECT_FALSE(IsProtectPragmaKeyword("library"));
  EXPECT_FALSE(IsProtectPragmaKeyword("entry"));
  EXPECT_FALSE(IsProtectPragmaKeyword("feature"));
  EXPECT_FALSE(IsProtectPragmaKeyword("exit"));
  EXPECT_FALSE(IsProtectPragmaKeyword("match"));
}

TEST(ProtectPragmaDirectives, AValuesOwnNameIsNotAppliedAsAKeyword) {
  DirectiveRun run("`pragma protect enctype=\"raw\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.ValueOf("enctype").defaulted);
}

TEST(ProtectPragmaDirectives, ThePragmaNameIsNotOneOfTheKeywords) {
  EXPECT_FALSE(IsProtectPragmaKeyword("protect"));
  EXPECT_FALSE(IsProtectPragmaKeyword("pragma"));
  EXPECT_TRUE(ProtectPragmaKeywordDescription("protect").empty());
}

TEST(ProtectPragmaDirectives, OneNameWithTwoExpressionsDoesTwoThings) {
  DirectiveRun delimits("`pragma protect begin\n");
  DirectiveRun describes("`pragma protect data_method=\"des-cbc\"\n");
  EXPECT_EQ(delimits.Envelopes().OpenEnvelopes().size(), 1U);
  EXPECT_TRUE(delimits.ValueOf("data_method").defaulted);
  EXPECT_TRUE(describes.Envelopes().OpenEnvelopes().empty());
  EXPECT_FALSE(describes.ValueOf("data_method").defaulted);
}

TEST(ProtectPragmaDirectives, TheLaterExpressionOfAKeywordIsTheOneInEffect) {
  DirectiveRun run(
      "`pragma protect data_method=\"des-cbc\"\n"
      "`pragma protect data_method=\"aes128-cbc\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_method").value, "aes128-cbc");
}

TEST(ProtectPragmaDirectives, AKeywordWrittenInsideAModuleOutlivesIt) {
  DirectiveRun run(
      "module m;\n"
      "  wire w;\n"
      "`pragma protect data_keyowner=\"acme\"\n"
      "endmodule\n"
      "module n;\n"
      "  wire x;\n"
      "endmodule\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "acme");
}

TEST(ProtectPragmaDirectives, AnEnvelopeSpansTheDeclarationsBetweenItsEnds) {
  DirectiveRun run(
      "module m;\n"
      "`pragma protect begin\n"
      "  wire w;\n"
      "endmodule\n"
      "module n;\n"
      "  wire x;\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Envelopes().OpenEnvelopes().empty());
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
}

TEST(ProtectPragmaDirectives, AKeywordWrittenInsideAPackageOutlivesIt) {
  DirectiveRun run(
      "package p;\n"
      "  parameter int W = 8;\n"
      "`pragma protect data_keyowner=\"acme\"\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "acme");
}

TEST(ProtectPragmaDirectives, AKeywordWrittenInsideAClassOutlivesIt) {
  DirectiveRun run(
      "class c;\n"
      "  int x;\n"
      "`pragma protect data_method=\"des-cbc\"\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_method").defaulted);
  EXPECT_EQ(run.ValueOf("data_method").value, "des-cbc");
}

TEST(ProtectPragmaDirectives, AKeywordWrittenInsideANamedBlockOutlivesIt) {
  DirectiveRun run(
      "module m;\n"
      "  initial begin : blk\n"
      "`pragma protect key_keyname=\"acme-key\"\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("key_keyname").defaulted);
  EXPECT_EQ(run.ValueOf("key_keyname").value, "acme-key");
}

TEST(ProtectPragmaDirectives, AnEnvelopeSpansAPackageAndAModule) {
  DirectiveRun run(
      "package p;\n"
      "`pragma protect begin\n"
      "  parameter int W = 8;\n"
      "endpackage\n"
      "module m;\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Envelopes().OpenEnvelopes().empty());
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
}

TEST(ProtectPragmaDirectives, AKeywordFromAnIncludedFileSurvivesTheInclude) {
  IncludeTestDir tmp("keyword_from_include");
  tmp.WriteFile("keys.svh", "`pragma protect data_keyowner=\"acme\"\n");
  std::string src =
      "`include \"keys.svh\"\n"
      "module m;\n"
      "endmodule\n";

  DirectiveRun run(tmp.TopPath(), src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "acme");
  EXPECT_NE(run.text.find("module m;"), std::string::npos);
}

TEST(ProtectPragmaDirectives, AKeywordReachesIntoTheFileItIncludes) {
  IncludeTestDir tmp("keyword_into_include");
  tmp.WriteFile("keys.svh", "`pragma protect data_method=\"des-cbc\"\n");
  std::string src =
      "`pragma protect data_keyowner=\"acme\"\n"
      "`include \"keys.svh\"\n";

  DirectiveRun run(tmp.TopPath(), src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "acme");
  EXPECT_EQ(run.ValueOf("data_method").value, "des-cbc");
}

TEST(ProtectPragmaDirectives, AnEnvelopeOpenedBeforeAnIncludeClosesInsideIt) {
  IncludeTestDir tmp("envelope_into_include");
  std::string body =
      "  wire w;\n"
      "`pragma protect end\n";
  tmp.WriteFile("body.svh", body);
  std::string src =
      "`pragma protect begin\n"
      "`include \"body.svh\"\n";

  DirectiveRun run(tmp.TopPath(), src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Envelopes().OpenEnvelopes().empty());
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
}

TEST(ProtectPragmaDirectives, AnEnvelopeOpenedInsideAnIncludeClosesAfterIt) {
  IncludeTestDir tmp("envelope_out_of_include");
  std::string body =
      "`pragma protect begin\n"
      "  wire w;\n";
  tmp.WriteFile("body.svh", body);
  std::string src =
      "`include \"body.svh\"\n"
      "`pragma protect end\n";

  DirectiveRun run(tmp.TopPath(), src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Envelopes().OpenEnvelopes().empty());
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
}

TEST(ProtectPragmaDirectives, AKeywordFromAFileIncludedTwoDeepSurvives) {
  IncludeTestDir tmp("keyword_two_deep");
  tmp.WriteFile("leaf.svh", "`pragma protect data_keyowner=\"acme\"\n");
  tmp.WriteFile("mid.svh", "`include \"leaf.svh\"\n");
  std::string src =
      "`include \"mid.svh\"\n"
      "module m;\n"
      "endmodule\n";

  DirectiveRun run(tmp.TopPath(), src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "acme");
}

TEST(ProtectPragmaDirectives, AKeywordFromOneInputFileIsInEffectInTheNext) {
  std::string src = "`pragma protect data_keyowner=\"acme\"\n";

  DirectiveRun run("first.sv", src);
  run.ReadNextFile("second.sv", "module m;\nendmodule\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "acme");
}

TEST(ProtectPragmaDirectives, AKeywordDoesNotReachASecondCompilationInput) {
  DirectiveRun first("`pragma protect data_keyowner=\"acme\"\n");
  DirectiveRun second("module m;\nendmodule\n");
  EXPECT_FALSE(first.ValueOf("data_keyowner").defaulted);
  EXPECT_TRUE(second.ValueOf("data_keyowner").defaulted);
}

TEST(ProtectPragmaDirectives, AnEnvelopeMissingAKeywordTakesItsDefault) {
  DirectiveRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect data_method=\"des-cbc\"\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_method").defaulted);
  EXPECT_TRUE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "");
}

TEST(ProtectPragmaDirectives, EveryKeywordNeverWrittenHasItsDefault) {
  DirectiveRun run(
      "`pragma protect begin_protected\n"
      "  wire w;\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  for (const ProtectPragmaKeyword& keyword : ProtectPragmaKeywords()) {
    if (keyword.name == "begin_protected" || keyword.name == "end_protected") {
      continue;
    }
    EXPECT_TRUE(run.ValueOf(keyword.name).defaulted) << keyword.name;
    EXPECT_EQ(run.ValueOf(keyword.name).value, "") << keyword.name;
  }
}

TEST(ProtectPragmaDirectives, AKeywordWrittenAheadOfAnEnvelopeDescribesIt) {
  DirectiveRun run(
      "`pragma protect data_keyowner=\"acme\", begin_protected\n"
      "  wire w;\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "acme");
}

TEST(ProtectPragmaDirectives, AKeywordOfOneEnvelopeIsInEffectForTheNext) {
  DirectiveRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect data_keyowner=\"acme\"\n"
      "`pragma protect end_protected\n"
      "`pragma protect begin_protected\n"
      "  wire w;\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes().size(), 2U);
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "acme");
}

TEST(ProtectPragmaDirectives, AKeywordWrittenBetweenEnvelopesIsInEffect) {
  DirectiveRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect end_protected\n"
      "`pragma protect data_keyowner=\"acme\"\n"
      "`pragma protect begin_protected\n"
      "  wire w;\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes().size(), 2U);
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "acme");
}

TEST(ProtectPragmaDirectives, ADefaultedKeywordAndAnUnlistedNameDiffer) {
  DirectiveRun run("`pragma protect acme_method=\"des-cbc\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.ValueOf("data_method").defaulted);
  EXPECT_TRUE(run.ValueOf("acme_method").defaulted);
  EXPECT_TRUE(IsProtectPragmaKeyword("data_method"));
  EXPECT_FALSE(IsProtectPragmaKeyword("acme_method"));
}

TEST(ProtectPragmaDirectives, ABareKeywordStatesNoValueForItsName) {
  DirectiveRun run("`pragma protect data_public_key\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.ValueOf("data_public_key").defaulted);
  EXPECT_EQ(run.ValueOf("data_public_key").value, "");
}

TEST(ProtectPragmaDirectives, AnEmptyStringWrittenAgainstAKeywordIsAValue) {
  DirectiveRun run("`pragma protect data_keyowner=\"\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "");
}

TEST(ProtectPragmaDirectives, ABareEnvelopeDelimiterStatesNoValue) {
  DirectiveRun run(
      "`pragma protect begin_protected\n"
      "  wire w;\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_TRUE(run.ValueOf("begin_protected").defaulted);
  EXPECT_TRUE(run.ValueOf("end_protected").defaulted);
}

TEST(ProtectPragmaDirectives, AParenthesizedListIsRecordedAsTheValue) {
  constexpr std::string_view kEncodingList = "(enctype=\"raw\")";
  DirectiveRun run("`pragma protect encoding=(enctype=\"raw\")\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("encoding").defaulted);
  EXPECT_EQ(run.ValueOf("encoding").value, kEncodingList);
}

TEST(ProtectPragmaDirectives, AWrittenEnvelopeCarriesItsOwnDescription) {
  constexpr std::string_view kBlockAnnouncement =
      "`pragma protect data_block\n";
  std::string written = Encrypted(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  size_t opening = written.find("`pragma protect begin_protected");
  size_t agent = written.find("`pragma protect encrypt_agent=");
  size_t method = written.find("`pragma protect data_method=");
  size_t encoding = written.find("`pragma protect encoding=");
  size_t block = written.find(kBlockAnnouncement);
  EXPECT_NE(opening, std::string::npos);
  EXPECT_NE(agent, std::string::npos);
  EXPECT_NE(method, std::string::npos);
  EXPECT_NE(encoding, std::string::npos);
  EXPECT_NE(block, std::string::npos);
  EXPECT_LT(opening, agent);
  EXPECT_LT(agent, block);
  EXPECT_LT(method, block);
  EXPECT_LT(encoding, block);
}

TEST(ProtectPragmaDirectives, AResetFollowsAWrittenEnvelope) {
  std::string written = Encrypted(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  size_t closing = written.find("`pragma protect end_protected");
  size_t reset = written.find("`pragma protect reset");
  EXPECT_NE(closing, std::string::npos);
  EXPECT_NE(reset, std::string::npos);
  EXPECT_LT(closing, reset);
}

TEST(ProtectPragmaDirectives, EveryWrittenEnvelopeCarriesItsOwn) {
  std::string written = Encrypted(
      "`pragma protect begin\n"
      "  initial first = 1;\n"
      "`pragma protect end\n"
      "`pragma protect begin\n"
      "  initial second = 2;\n"
      "`pragma protect end\n");
  EXPECT_EQ(Occurrences(written, "`pragma protect encrypt_agent="), 2U);
  EXPECT_EQ(Occurrences(written, "`pragma protect data_method="), 2U);
  EXPECT_EQ(Occurrences(written, "`pragma protect reset"), 2U);
}

TEST(ProtectPragmaDirectives, AWrittenEnvelopeOutweighsWhatPrecedesIt) {
  std::string written = Encrypted(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  std::string src = "`pragma protect data_method=\"acme-cipher\"\n" + written;

  ReadBackWithKey run(src, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_NE(run.text.find("initial result = 42;"), std::string::npos);
}

}  // namespace
