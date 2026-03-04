#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA210, PropertyFormalType_Property) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(property q);\n"
              "    q;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyFormalType_Sequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(sequence s);\n"
              "    s |-> 1;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyFormalType_Implicit) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(x);\n"
              "    x;\n"
              "  endproperty\n"
              "endmodule\n"));
}

}
