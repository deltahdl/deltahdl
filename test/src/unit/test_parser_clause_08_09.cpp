#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ClassObjectParsing, StaticPropertyAccessViaInstance) {
  ParseOk(
      "class Packet;\n"
      "  static int fileID;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  initial begin\n"
      "    automatic int c;\n"
      "    c = p.fileID;\n"
      "  end\n"
      "endmodule\n");
}

TEST(ClassObjectParsing, StaticPropertyAccessViaScope) {
  ParseOk(
      "class Packet;\n"
      "  static int fileID;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    automatic int c;\n"
      "    c = Packet::fileID;\n"
      "  end\n"
      "endmodule\n");
}

}  // namespace
