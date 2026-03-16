#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(StaticMethodParsing, StaticMethodClassScopeCall) {
  ParseOk(
      "class id;\n"
      "  static function int next_id();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "    x = id::next_id();\n"
      "  end\n"
      "endmodule\n");
}

TEST(StaticMethodParsing, StaticMethodInstanceDotCall) {
  ParseOk(
      "class C;\n"
      "  static function int helper();\n"
      "    return 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "    x = c.helper();\n"
      "  end\n"
      "endmodule\n");
}

}  // namespace
