

#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(Preprocessor, Pragma_Reset_NoError) {
  PreprocFixture f;
  Preprocess("`pragma reset my_pragma\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Pragma_Reset_MultipleNames_NoError) {
  PreprocFixture f;
  Preprocess("`pragma reset name1, name2, name3\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Pragma_Resetall_NoError) {
  PreprocFixture f;
  Preprocess("`pragma resetall\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Pragma_Reset_NoNames_NoError) {
  PreprocFixture f;
  Preprocess("`pragma reset\n", f);
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

TEST(Preprocessor, Pragma_Reset_InsideModule_NoError) {
  PreprocFixture f;
  Preprocess("module m;\n`pragma reset my_pragma\nendmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Pragma_Resetall_InsideModule_NoError) {
  PreprocFixture f;
  Preprocess("module m;\n`pragma resetall\nendmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Pragma_Reset_MultipleInSequence_NoError) {
  PreprocFixture f;
  Preprocess(
      "`pragma reset name1\n"
      "`pragma reset name2\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Pragma_ResetFollowedByResetall_NoError) {
  PreprocFixture f;
  Preprocess(
      "`pragma reset my_pragma\n"
      "`pragma resetall\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
