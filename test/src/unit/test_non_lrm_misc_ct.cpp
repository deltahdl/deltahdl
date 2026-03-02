// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Form 2: bind hierarchical_instance instantiation
TEST(SourceText, BindDirectiveHierarchical) {
  auto r = ParseWithPreprocessor("bind top.dut.u1 checker_mod chk(.a(sig));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "top.dut.u1");
}

}  // namespace
