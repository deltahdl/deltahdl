// Non-LRM tests

#include "fixture_preprocessor.h"

namespace {

TEST(DesignElementPreprocessing, MultipleMacrosExpandInSameDesignElement) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define A 4\n"
      "`define B 8\n"
      "module m;\n"
      "  logic [`A-1:0] x;\n"
      "  logic [`B-1:0] y;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("4"), std::string::npos);
  EXPECT_NE(result.find("8"), std::string::npos);
}

}  // namespace
