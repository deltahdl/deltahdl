// §6.9.2: Vector net accessibility

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA213, NetDeclVectored) {
  auto r = Parse("module m; wire vectored [7:0] bus; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA213, NetDeclScalared) {
  auto r = Parse("module m; wire scalared [7:0] bus; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
