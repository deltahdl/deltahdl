#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct PreprocFixture {
  SourceManager mgr;
  DiagEngine diag{mgr};
};

static std::string Preprocess(const std::string &src, PreprocFixture &f,
                              PreprocConfig config = {}) {
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor pp(f.mgr, f.diag, std::move(config));
  return pp.Preprocess(fid);
}

TEST(Preprocessor, ElsifTakesSecondBranch) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"B", "1"}};
  auto result = Preprocess("`ifdef A\n"
                           "line_a\n"
                           "`elsif B\n"
                           "line_b\n"
                           "`endif\n",
                           f, std::move(cfg));
  EXPECT_NE(result.find("line_b"), std::string::npos);
  EXPECT_EQ(result.find("line_a"), std::string::npos);
}

TEST(Preprocessor, ElsifSkippedWhenFirstTaken) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}, {"B", "1"}};
  auto result = Preprocess("`ifdef A\n"
                           "line_a\n"
                           "`elsif B\n"
                           "line_b\n"
                           "`endif\n",
                           f, std::move(cfg));
  EXPECT_NE(result.find("line_a"), std::string::npos);
  EXPECT_EQ(result.find("line_b"), std::string::npos);
}

TEST(Preprocessor, ElsifElseFallthrough) {
  PreprocFixture f;
  auto result = Preprocess("`ifdef A\n"
                           "line_a\n"
                           "`elsif B\n"
                           "line_b\n"
                           "`else\n"
                           "line_else\n"
                           "`endif\n",
                           f);
  EXPECT_EQ(result.find("line_a"), std::string::npos);
  EXPECT_EQ(result.find("line_b"), std::string::npos);
  EXPECT_NE(result.find("line_else"), std::string::npos);
}

TEST(Preprocessor, MultipleElsif) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"C", "1"}};
  auto result = Preprocess("`ifdef A\n"
                           "line_a\n"
                           "`elsif B\n"
                           "line_b\n"
                           "`elsif C\n"
                           "line_c\n"
                           "`else\n"
                           "line_else\n"
                           "`endif\n",
                           f, std::move(cfg));
  EXPECT_EQ(result.find("line_a"), std::string::npos);
  EXPECT_EQ(result.find("line_b"), std::string::npos);
  EXPECT_NE(result.find("line_c"), std::string::npos);
  EXPECT_EQ(result.find("line_else"), std::string::npos);
}

TEST(Preprocessor, NestedIfdefInsideElsif) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"B", "1"}, {"INNER", "1"}};
  auto result = Preprocess("`ifdef A\n"
                           "line_a\n"
                           "`elsif B\n"
                           "`ifdef INNER\n"
                           "line_inner\n"
                           "`endif\n"
                           "`endif\n",
                           f, std::move(cfg));
  EXPECT_NE(result.find("line_inner"), std::string::npos);
  EXPECT_EQ(result.find("line_a"), std::string::npos);
}

TEST(Preprocessor, IfdefElseRegression) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess("`ifdef A\n"
                           "line_a\n"
                           "`else\n"
                           "line_else\n"
                           "`endif\n",
                           f, std::move(cfg));
  EXPECT_NE(result.find("line_a"), std::string::npos);
  EXPECT_EQ(result.find("line_else"), std::string::npos);
}

// --- Ifdef expression tests (IEEE 1800-2023 §22.6) ---

TEST(Preprocessor, IfdefExprAnd) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}, {"B", "1"}};
  auto result = Preprocess("`ifdef (A && B)\n"
                           "both_defined\n"
                           "`endif\n",
                           f, std::move(cfg));
  EXPECT_NE(result.find("both_defined"), std::string::npos);
}

TEST(Preprocessor, IfdefExprAndFalse) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess("`ifdef (A && B)\n"
                           "both_defined\n"
                           "`endif\n",
                           f, std::move(cfg));
  EXPECT_EQ(result.find("both_defined"), std::string::npos);
}

TEST(Preprocessor, IfdefExprOr) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess("`ifdef (A || B)\n"
                           "either_defined\n"
                           "`endif\n",
                           f, std::move(cfg));
  EXPECT_NE(result.find("either_defined"), std::string::npos);
}

TEST(Preprocessor, IfdefExprNot) {
  PreprocFixture f;
  auto result = Preprocess("`ifdef (!A)\n"
                           "not_defined\n"
                           "`endif\n",
                           f);
  EXPECT_NE(result.find("not_defined"), std::string::npos);
}

TEST(Preprocessor, IfdefExprComplex) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess("`ifdef (A && (B || !C))\n"
                           "complex_true\n"
                           "`endif\n",
                           f, std::move(cfg));
  EXPECT_NE(result.find("complex_true"), std::string::npos);
}
