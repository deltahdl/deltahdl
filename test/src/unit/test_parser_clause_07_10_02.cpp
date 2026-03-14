#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(DynamicArrayAndQueueParsing, QueueInsertAndDelete) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    q.push_back(1);\n"
      "    q.push_back(3);\n"
      "    q.insert(1, 2);\n"
      "    q.delete(0);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
