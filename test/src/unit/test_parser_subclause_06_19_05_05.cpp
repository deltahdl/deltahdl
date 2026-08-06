#include "fixture_parser.h"

using namespace delta;

namespace {

// §6.19.5.5 owns no parser rule of its own (its normative claims are the
// simulator-stage member-count and int-width behavior). This is a single
// acceptance smoke test that a num() method call is grammatical; varying the
// syntactic position of the call would only re-exercise method-call grammar
// owned elsewhere, so no additional parser cases are kept here.
TEST(EnumMethods, NumCallParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef enum {RED, GREEN, BLUE} color_e;\n"
              "  color_e c;\n"
              "  int n;\n"
              "  initial n = c.num();\n"
              "endmodule\n"));
}

}  // namespace
