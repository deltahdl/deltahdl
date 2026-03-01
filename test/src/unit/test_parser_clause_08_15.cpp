// §8.15: Super

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// § implicit_class_handle — super
TEST(ParserA84, ImplicitClassHandleSuper) {
  auto r = Parse("module m; initial x = super; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
