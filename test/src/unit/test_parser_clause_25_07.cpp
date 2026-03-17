#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(TaskDeclParsing, TaskBodyInterfaceScope) {
  auto r = Parse(
      "interface intf;\n"
      "  extern task my_task();\n"
      "endinterface\n"
      "task intf.my_task();\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
