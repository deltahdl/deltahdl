#include <gtest/gtest.h>

#include <string>

#include "fixture_preprocessor.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/standard_pragmas.h"

using namespace delta;

namespace {

std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                             Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

TEST(Preprocessor, Pragma_Reset_NoError) {
  PreprocFixture f;
  Preprocess("`pragma reset my_pragma\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Pragma_Resetall_NoError) {
  PreprocFixture f;
  Preprocess("`pragma resetall\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Pragma_Reset_NoOutput) {
  PreprocFixture f;
  auto out = Preprocess("`pragma reset my_pragma\n", f);
  auto trimmed = out;
  trimmed.erase(0, trimmed.find_first_not_of(" \t\n\r"));
  trimmed.erase(trimmed.find_last_not_of(" \t\n\r") + 1);
  EXPECT_TRUE(trimmed.empty());
}

TEST(Preprocessor, Pragma_Resetall_NoOutput) {
  PreprocFixture f;
  auto out = Preprocess("`pragma resetall\n", f);
  auto trimmed = out;
  trimmed.erase(0, trimmed.find_first_not_of(" \t\n\r"));
  trimmed.erase(trimmed.find_last_not_of(" \t\n\r") + 1);
  EXPECT_TRUE(trimmed.empty());
}

TEST(Preprocessor, Pragma_Reset_SurroundingCodePreserved) {
  PreprocFixture f;
  auto out = Preprocess(
      "wire a;\n"
      "`pragma reset my_pragma\n"
      "wire b;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("wire a;"), std::string::npos);
  EXPECT_NE(out.find("wire b;"), std::string::npos);
}

TEST(Preprocessor, Pragma_Resetall_SurroundingCodePreserved) {
  PreprocFixture f;
  auto out = Preprocess(
      "wire a;\n"
      "`pragma resetall\n"
      "wire b;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("wire a;"), std::string::npos);
  EXPECT_NE(out.find("wire b;"), std::string::npos);
}

TEST(StandardPragmas, KeywordValueStandsWhenNothingResetsIt) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`pragma protect author=\"ada\"\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  ProtectKeywordValue author = pp.ProtectKeywords().ValueOf("author");
  EXPECT_FALSE(author.defaulted);
  EXPECT_EQ(author.value, "ada");
}

TEST(StandardPragmas, ResetRestoresTheNamedPragmasKeywordDefaults) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`pragma protect author=\"ada\"\n"
      "`pragma reset protect\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.ProtectKeywords().ValueOf("author").defaulted);
}

TEST(StandardPragmas, ResetallRestoresEveryRecognizedPragma) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`pragma protect author=\"ada\"\n"
      "`pragma resetall\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.ProtectKeywords().ValueOf("author").defaulted);
}

TEST(StandardPragmas, ResetNamingAnUnrecognizedPragmaRestoresNothing) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`pragma protect author=\"ada\"\n"
      "`pragma reset my_pragma\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.ProtectKeywords().ValueOf("author").value, "ada");
}

TEST(StandardPragmas, ResetNamingNoPragmaRestoresNothing) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`pragma protect author=\"ada\"\n"
      "`pragma reset\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.ProtectKeywords().ValueOf("author").value, "ada");
}

TEST(StandardPragmas, KeywordWrittenAfterAResetTakesEffectAgain) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`pragma protect author=\"ada\"\n"
      "`pragma resetall\n"
      "`pragma protect author=\"grace\"\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.ProtectKeywords().ValueOf("author").value, "grace");
}

TEST(StandardPragmas, RecognizedPragmaNamesAreWhatResetallReaches) {
  EXPECT_TRUE(IsRecognizedPragmaName("protect"));
  EXPECT_FALSE(IsRecognizedPragmaName("my_pragma"));
  EXPECT_FALSE(IsRecognizedPragmaName(kResetPragmaName));
  EXPECT_FALSE(IsRecognizedPragmaName(kResetallPragmaName));
}

}  // namespace
