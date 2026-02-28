// §19.4: Using covergroups in classes

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA211, CovergroupDecl_InClass) {
  EXPECT_TRUE(
      ParseOk("class c;\n"
              "  covergroup cg;\n"
              "  endgroup\n"
              "endclass\n"));
}

}  // namespace
