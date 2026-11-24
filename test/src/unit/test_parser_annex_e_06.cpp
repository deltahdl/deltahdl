#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_parser.h"
#include "helpers_delay_mode_directives.h"

using namespace delta;

namespace {

TEST(OptionalDirectiveExtendedParsing, DelayModeUnit) {
  auto r = ParseWithPreprocessor(
      "`delay_mode_unit\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->delay_mode_directive, DelayModeDirective::kUnit);
}

TEST(OptionalDirectiveExtendedParsing,
     DISABLED_DelayModeUnit_TrailingTextStaysSourceText) {
  ExpectTrailingTextStaysSourceText(kUnitDirective);
}

TEST(OptionalDirectiveExtendedParsing,
     DISABLED_DelayModeUnit_DeclarationAfterItStaysSourceText) {
  ExpectDeclarationAfterItStaysSourceText(kUnitDirective);
}

TEST(OptionalDirectiveExtendedParsing,
     DISABLED_DelayModeUnit_ModuleAfterItOnItsLineIsDeclared) {
  ExpectModuleAfterItOnItsLineIsDeclared(kUnitDirective);
}

}  // namespace
