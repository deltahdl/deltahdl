// §8.26.3: Type access

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// §8.26.3 — Interface class with typedef member
TEST(ParserSection8, InterfaceClassWithTypedef) {
  auto r = Parse("interface class ihello;\n"
                 "  typedef int int_t;\n"
                 "  pure virtual function void hello(int_t val);\n"
                 "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "ihello");
}

} // namespace
