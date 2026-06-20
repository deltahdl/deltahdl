#include <gtest/gtest.h>

#include <string>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(IdentifierPreprocessor, SimpleIdentifierPassesThrough) {
  PreprocFixture f;
  Preprocess(
      "module t;\n"
      "  logic [7:0] abc_123;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierPreprocessor, IdentifierWithDollarPassesThrough) {
  PreprocFixture f;
  Preprocess(
      "module t;\n"
      "  logic [7:0] n$657;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierPreprocessor, IdentifierStartingWithUnderscorePassesThrough) {
  PreprocFixture f;
  Preprocess(
      "module t;\n"
      "  logic [7:0] _bus3;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierPreprocessor, CaseSensitiveIdentifiersPassThrough) {
  PreprocFixture f;
  Preprocess(
      "module t;\n"
      "  logic [7:0] data, Data, DATA;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierPreprocessor, MaxLengthIdentifierPassesThrough) {
  PreprocFixture f;
  std::string long_id(1024, 'a');
  Preprocess(
      "module t;\n"
      "  logic [7:0] " +
          long_id +
          ";\n"
          "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierPreprocessor, IdentifierInMacroExpansion) {
  PreprocFixture f;
  Preprocess(
      "`define DECL(name) logic [7:0] name\n"
      "module t;\n"
      "  `DECL(my_var_99);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
