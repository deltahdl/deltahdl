#include <gtest/gtest.h>

#include <string>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

// §5.9: a quoted string continues onto the next line when a backslash stands
// before the newline, so the `"` on the next line closes it. Taken to open a
// string instead, it kept the macro usage after it from expanding.
TEST(StringLiteralPreprocessor, MacroAfterAContinuedStringExpands) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define W 8\n"
      "module t;\n"
      "  initial $display(\"abc\\\n"
      "\", `W);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("\", 8);"), std::string::npos);
}

// And text on the continuation line before the closing `"` is still inside
// the string, so a macro usage written there is left as it stands.
TEST(StringLiteralPreprocessor, MacroInsideAContinuedStringStaysText) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define W 8\n"
      "module t;\n"
      "  initial $display(\"abc\\\n"
      "`W\");\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("`W\");"), std::string::npos);
}

}  // namespace
