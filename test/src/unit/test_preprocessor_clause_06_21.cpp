// §6.21: Scope and lifetime

#include "elaborator/type_eval.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection6, ProgramLifetimeAutomatic) {
  // §6.21: program blocks may be declared automatic.
  auto r = ParseWithPreprocessor("program automatic test_prog; endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "test_prog");
}

}  // namespace
