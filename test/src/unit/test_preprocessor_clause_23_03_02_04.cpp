#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(WildcardPortConnectionPreprocessing, WildcardSurvivesPreprocessing) {
  auto r = ParseWithPreprocessor(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic a, b;\n"
      "  child u0(.*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindItemByKind(r, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_TRUE(inst->inst_wildcard);
  EXPECT_TRUE(inst->inst_ports.empty());
}

}
