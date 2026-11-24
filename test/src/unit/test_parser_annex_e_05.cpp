#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_parser.h"
#include "helpers_delay_mode_directives.h"

using namespace delta;

namespace {

TEST(OptionalDirectiveExtendedParsing, DelayModePath) {
  auto r = ParseWithPreprocessor(
      "`delay_mode_path\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->delay_mode_directive, DelayModeDirective::kPath);
}

TEST(OptionalDirectiveExtendedParsing,
     DISABLED_DelayModePath_TrailingTextStaysSourceText) {
  ExpectTrailingTextStaysSourceText(kPathDirective);
}

TEST(OptionalDirectiveExtendedParsing,
     DISABLED_DelayModePath_DeclarationAfterItStaysSourceText) {
  ExpectDeclarationAfterItStaysSourceText(kPathDirective);
}

TEST(OptionalDirectiveExtendedParsing,
     DISABLED_DelayModePath_ModuleAfterItOnItsLineIsDeclared) {
  ExpectModuleAfterItOnItsLineIsDeclared(kPathDirective);
}

}  // namespace
