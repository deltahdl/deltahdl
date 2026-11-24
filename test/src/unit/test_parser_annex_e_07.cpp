#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_parser.h"
#include "helpers_delay_mode_directives.h"

using namespace delta;

namespace {

TEST(OptionalDirectiveParsing, DelayModeZero) {
  auto r = ParseWithPreprocessor("`delay_mode_zero\nmodule m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->delay_mode_directive, DelayModeDirective::kZero);
}

TEST(OptionalDirectiveParsing,
     DISABLED_DelayModeZero_TrailingTextStaysSourceText) {
  ExpectTrailingTextStaysSourceText(kZeroDirective);
}

TEST(OptionalDirectiveParsing,
     DISABLED_DelayModeZero_DeclarationAfterItStaysSourceText) {
  ExpectDeclarationAfterItStaysSourceText(kZeroDirective);
}

TEST(OptionalDirectiveParsing,
     DISABLED_DelayModeZero_ModuleAfterItOnItsLineIsDeclared) {
  ExpectModuleAfterItOnItsLineIsDeclared(kZeroDirective);
}

}  // namespace
